import Leader.L3.Width.DigitQuietStepGlue
import Leader.L3.Width.DigitQuietStepArith
import Leader.L3.Width.DigitQuietStepScan

/-!
# The digit writes are idempotent on the quiet class

The three writes of the top machine (BASE, LAUNCH, ADVANCE; see `WidthDigitQuietStepDigitsRows`)
store the digit already there, on the quiet class:

* `scanTargetW_local`, `pairQuiet_local`: what the target scan of a pair says about one position
  (a settled input `S val tail` at position `p` has `val = Dp p`; a live carry has an empty input
  and carry bit `carryInto Dp (p + 1)`);
* `digits_complete_block`: a delimiter followed by a whole block is a complete value block;
* `digits_base_value`, `digits_launch_value`, `digits_advance_value`: the three writes.

Consumer: `WidthDigitQuietStepDigits` (`digits_kept`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- **A position of a window read by the target scan.**  A live carry at `p` has an empty input and
the carry bit `carryInto Dp (p + 1)`; a settled input `S val tail` at `p` without carry has
`val = Dp p` and `tail = decide (p = 0)`.  Consumer: `pairQuiet_local`. -/
theorem scanTargetW_local (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) :
    ∀ (k nxt : Nat) (sawP seen : Bool), ScanTargetW R v Dp lo K k nxt sawP seen →
      ∀ p, lo ≤ p → p < k + lo →
        ((v p).carryLive = true → (v p).input = .E ∧ (v p).carryBit = carryInto Dp (p + 1)) ∧
        ((v p).carryLive = false → ∀ (val : Fin c.topA) (tail : Bool),
          (v p).input = .S val tail → val = Dp p ∧ tail = decide (p = 0)) := by
  intro k
  induction k with
  | zero => intro nxt sawP seen _ p h1 hp; omega
  | succ k ih =>
    intro nxt sawP seen hs p h1 hp
    simp only [ScanTargetW] at hs
    by_cases hl : (v (k + lo)).carryLive = true
    · rw [if_pos hl] at hs
      obtain ⟨-, -, hE, hb, -, hrest⟩ := hs
      by_cases hpk : p = k + lo
      · subst hpk
        exact ⟨fun _ => ⟨hE, hb⟩, fun h => absurd hl (by rw [h]; exact Bool.false_ne_true)⟩
      · exact ih _ _ _ hrest p h1 (by omega)
    · rw [if_neg hl] at hs
      by_cases hpk : p = k + lo
      · subst hpk
        refine ⟨fun h => absurd h hl, fun _ val tail hin => ?_⟩
        simp only [hin] at hs
        exact ⟨hs.2.2.1, hs.2.2.2.1⟩
      · have hlt : p < k + lo := by omega
        revert hs
        cases hin : (v (k + lo)).input with
        | E => intro hs; exact ih _ _ _ hs p h1 hlt
        | X => intro hs; exact hs.elim
        | S val tail => intro hs; exact ih _ _ _ hs.2.2.2.2 p h1 hlt
        | P val tail =>
          intro hs
          rcases hs with hs | hs
          · exact ih _ _ _ hs.2.2.2.2 p h1 hlt
          · exact ih _ _ _ hs.2.2.2 p h1 hlt

/-- **A position of a quiet pair's target block.**  Consumer: `digits_launch_value`,
`digits_advance_value`. -/
theorem pairQuiet_local (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (lane : DigitLane) (source target : Nat) (h : PairQuiet ring root S lane source target)
    (p : Nat) (hp : p < digitSpan c) :
    ((view ring root S lane (target + p)).carryLive = true →
      (view ring root S lane (target + p)).input = .E ∧
      (view ring root S lane (target + p)).carryBit =
        carryInto (fun i => (S (digitSite ring root (source + i))).top.d) (p + 1)) ∧
    ((view ring root S lane (target + p)).carryLive = false → ∀ (val : Fin c.topA) (tail : Bool),
      (view ring root S lane (target + p)).input = .S val tail →
        val = (S (digitSite ring root (source + p))).top.d ∧ tail = decide (p = 0)) :=
  scanTargetW_local _ _ _ _ _ _ _ _ _ ((pairQuiet_iff_W ring root S lane source target).mp h) p
    (Nat.zero_le _) (by omega)

/-- **A delimiter followed by a whole block is a complete value block.**  Consumer:
`digits_launch_value`, `digits_advance_value`. -/
theorem digits_complete_block (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (j : Nat)
    (hj : first + j * digitSpan c + digitSpan c < n) :
    completeValueBlock ring root (digitValueView S) (first + j * digitSpan c) := by
  obtain ⟨hf2, hfn, hlay⟩ := hQ.layout
  have hjR : (j * digitSpan c) % digitSpan c = 0 := Nat.mul_mod_left j _
  refine ⟨⟨⟨by omega, by omega, ?_⟩, by omega, by omega, ?_, ?_⟩, hj⟩
  · show (S (digitSite ring root (first + j * digitSpan c))).word.beta = true
    refine (hlay _ (by omega) (by omega)).mpr ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact hjR
  · intro hlt
    show (S (digitSite ring root (first + j * digitSpan c + digitSpan c))).word.beta = true
    refine (hlay _ (by omega) hlt).mpr ⟨by omega, ?_⟩
    have e : first + j * digitSpan c + digitSpan c - first = j * digitSpan c + digitSpan c := by
      omega
    rw [e, Nat.add_mod_right]
    exact hjR
  · intro k hk1 hk2
    show (S (digitSite ring root k)).word.beta = false
    cases hb : (S (digitSite ring root k)).word.beta
    · rfl
    · exfalso
      obtain ⟨-, hm⟩ := (hlay k (by omega) (by omega)).mp hb
      have e : k - first = (k - (first + j * digitSpan c)) + j * digitSpan c := by omega
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hm
      omega

/-- The first delimiter and the block after it, as the data of `firstValueWritable`.  Consumer:
`digits_base_value`. -/
theorem digits_first_block (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) :
    firstValueDelimiter ring root (digitValueView S) first ∧
    nextValueDelimiter ring root (digitValueView S) first (min (first + digitSpan c) n) := by
  obtain ⟨hf2, hfn, hlay⟩ := hQ.layout
  have hbf : (S (digitSite ring root first)).word.beta = true :=
    (hlay first (by omega) hfn).mpr ⟨Nat.le_refl _, by rw [Nat.sub_self]; exact Nat.zero_mod _⟩
  have hvd : valueDelimiter ring root (digitValueView S) first := ⟨by omega, hfn, hbf⟩
  refine ⟨⟨hvd, ?_⟩, hvd, by omega, by omega, ?_, ?_⟩
  · intro k hk0 hk1
    show (S (digitSite ring root k)).word.beta = false
    cases hb : (S (digitSite ring root k)).word.beta
    · rfl
    · exfalso
      have := ((hlay k hk0 (by omega)).mp hb).1
      omega
  · intro hs
    show (S (digitSite ring root (min (first + digitSpan c) n))).word.beta = true
    have e : min (first + digitSpan c) n = first + digitSpan c := by omega
    rw [e]
    refine (hlay _ (by omega) (by omega)).mpr ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact Nat.mod_self _
  · intro k hk1 hk2
    show (S (digitSite ring root k)).word.beta = false
    cases hb : (S (digitSite ring root k)).word.beta
    · rfl
    · exfalso
      obtain ⟨-, hm⟩ := (hlay k (by omega) (by omega)).mp hb
      rw [Nat.mod_eq_of_lt (by omega)] at hm
      omega

/-- **BASE writes the digit already there**: a non-leader pair with `wBase = ZERO` at the left
site is inside the first segment, whose digits are `zero`.  Consumer: `digits_kept`. -/
theorem digits_base_value (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (k : Nat)
    (hk0 : 0 < k) (hk1 : k + 1 < n)
    (hz : (S (digitSite ring root k)).top.wBase = .ZERO) :
    (S (digitSite ring root k)).top.d = c.zeroDigit := by
  obtain ⟨hfirst, hlt⟩ := (hQ.base k hk0 (by omega)).2 hz
  obtain ⟨hfd, hnd⟩ := digits_first_block hR ring root first S hQ
  exact hQ.values.1 (digitSite ring root k)
    ⟨first, min (first + digitSpan c) n, k, hfd, hnd, hfirst, by omega, hk1, rfl⟩

/-- **LAUNCH writes the digit already there**: a delimiter holding a settled input `S v _` without
carry, followed by a site, has the digit `v + 1`.  Consumer: `digits_kept`. -/
theorem digits_launch_value (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (k : Nat)
    (hk0 : 0 < k) (hk1 : k + 1 < n)
    (hb : (S (digitSite ring root k)).word.beta = true)
    (hcar : (S (digitSite ring root k)).top.wCarry = .OFF) (v : Fin c.topA) (t : Bool)
    (hin : (S (digitSite ring root k)).top.wIn = .S v t) :
    (S (digitSite ring root k)).top.d = c.digitMod (v.val + 1) := by
  obtain ⟨hf2, hfn, hlay⟩ := hQ.layout
  obtain ⟨hge, hmod⟩ := (hlay k hk0 (by omega)).mp hb
  have hinv : (view ring root S DigitLane.writer k).input = .S v t := hin
  have hlive : (view ring root S DigitLane.writer k).carryLive = false := by
    show (S (digitSite ring root k)).top.wCarry.isW = false
    rw [hcar]; rfl
  obtain ⟨q, hq⟩ : ∃ q, k - first = digitSpan c * q :=
    ⟨(k - first) / digitSpan c, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm⟩
  have hqR : digitSpan c * q = q * digitSpan c := Nat.mul_comm _ _
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0
    have hkf : k = first := by rw [Nat.mul_zero] at hq; omega
    rcases hQ.firstSegment DigitLane.writer k (by omega) (by omega) (by omega) with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · rw [if_pos hkf, hinv] at h2
      cases h2
  · obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    have e1 : (j + 1) * digitSpan c = j * digitSpan c + digitSpan c := Nat.succ_mul j _
    have e2 : (j + 2) * digitSpan c = (j + 1) * digitSpan c + digitSpan c := Nat.succ_mul (j + 1) _
    have hkt : k = first + (j + 1) * digitSpan c := by omega
    by_cases hp : first + (j + 2) * digitSpan c < n
    · have hpair := hQ.pairs DigitLane.writer j hp
      have hloc := (pairQuiet_local ring root S DigitLane.writer _ _ hpair 0 hR).2
      subst hkt
      have hval := (hloc hlive v t hinv).1
      have hsrc := digits_complete_block hR ring root first S hQ j (by omega)
      have hT := digits_complete_block hR ring root first S hQ (j + 1) (by omega)
      have h := values_digitwise ring root S hQ.values (first + j * digitSpan c)
        (first + (j + 1) * digitSpan c) hsrc (by omega) hT 0 hR
      have hc : carryInto (fun i => (S (digitSite ring root (first + j * digitSpan c + i))).top.d) 0
          = true := rfl
      rw [hc, if_pos rfl, ← hval] at h
      exact Fin.ext h
    · exfalso
      have hlast : lastDelimiter first (digitSpan c) n ≤ k := by
        unfold lastDelimiter
        have hd : (n - 1 - first) / digitSpan c < j + 2 :=
          (Nat.div_lt_iff_lt_mul hR).mpr (by omega)
        have hm := Nat.mul_le_mul_left (digitSpan c) (Nat.le_of_lt_succ hd)
        omega
      rcases hQ.fragment (by omega) DigitLane.writer k hlast (by omega) v t with h1 | h1
      · exact h1 hinv
      · exact absurd h1.1 (by omega)

/-- **ADVANCE writes the digit already there**: a site without carry holding a settled input
`S v _` that is not a delimiter, behind a live carry `W cc`, has the digit `v + cc`.  Consumer:
`digits_kept`. -/
theorem digits_advance_value (hR : 0 < digitSpan c) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (k : Nat)
    (hk0 : 0 < k) (hk1 : k + 1 < n)
    (hb : (S (digitSite ring root (k + 1))).word.beta = false) (cc : Bool)
    (hcx : (S (digitSite ring root k)).top.wCarry = .W cc)
    (hcy : (S (digitSite ring root (k + 1))).top.wCarry = .OFF) (v : Fin c.topA) (t : Bool)
    (hin : (S (digitSite ring root (k + 1))).top.wIn = .S v t) :
    (S (digitSite ring root (k + 1))).top.d =
      c.digitMod (v.val + (if cc = true then 1 else 0)) := by
  obtain ⟨hf2, hfn, hlay⟩ := hQ.layout
  have hviewX : (view ring root S DigitLane.writer k).carryLive = true := by
    show (S (digitSite ring root k)).top.wCarry.isW = true
    rw [hcx]; rfl
  have hviewY : (view ring root S DigitLane.writer (k + 1)).carryLive = false := by
    show (S (digitSite ring root (k + 1))).top.wCarry.isW = false
    rw [hcy]; rfl
  have hinY : (view ring root S DigitLane.writer (k + 1)).input = .S v t := hin
  by_cases hkf : k < first
  · have := (hQ.leading DigitLane.writer k hk0 hkf).2.2
    rw [hviewX] at this
    cases this
  · by_cases hseg : k < first + digitSpan c
    · rcases hQ.firstSegment DigitLane.writer k (by omega) hseg (by omega) with ⟨h1, -⟩ | ⟨h1, -⟩
      · omega
      · rw [hviewX] at h1
        cases h1
    · obtain ⟨q, h, hh, hkq⟩ : ∃ q h, h < digitSpan c ∧ k - first = digitSpan c * q + h :=
        ⟨(k - first) / digitSpan c, (k - first) % digitSpan c, Nat.mod_lt _ hR,
          (Nat.div_add_mod _ _).symm⟩
      have hh1 : h + 1 < digitSpan c := by
        by_cases hh2 : h + 1 = digitSpan c
        · exfalso
          have e : k + 1 - first = digitSpan c * (q + 1) := by rw [Nat.mul_succ]; omega
          have hb' := (hlay (k + 1) (by omega) hk1).mpr ⟨by omega, by
            rw [e]; exact Nat.mul_mod_right _ _⟩
          rw [hb] at hb'
          cases hb'
        · omega
      rcases q with _ | j
      · rw [Nat.mul_zero] at hkq
        omega
      · have e1 : (j + 1) * digitSpan c = j * digitSpan c + digitSpan c := Nat.succ_mul j _
        have e2 : (j + 2) * digitSpan c = (j + 1) * digitSpan c + digitSpan c :=
          Nat.succ_mul (j + 1) _
        have hqR : digitSpan c * (j + 1) = (j + 1) * digitSpan c := Nat.mul_comm _ _
        have hkt : k = first + (j + 1) * digitSpan c + h := by omega
        by_cases hp : first + (j + 2) * digitSpan c < n
        · have hpair := hQ.pairs DigitLane.writer j hp
          have hloc1 := (pairQuiet_local ring root S DigitLane.writer _ _ hpair h hh).1
          have hloc2 := (pairQuiet_local ring root S DigitLane.writer _ _ hpair (h + 1) hh1).2
          subst hkt
          have hlx := hloc1 hviewX
          have hcb : cc = carryInto
              (fun i => (S (digitSite ring root (first + j * digitSpan c + i))).top.d) (h + 1) := by
            have h3 := hlx.2
            have h4 : wcC (S (digitSite ring root (first + (j + 1) * digitSpan c + h))).top.wCarry
                = _ := h3
            rw [hcx] at h4
            exact h4
          have hval := (hloc2 hviewY v t hinY).1
          have hsrc := digits_complete_block hR ring root first S hQ j (by omega)
          have hT := digits_complete_block hR ring root first S hQ (j + 1) (by omega)
          have h5 := values_digitwise ring root S hQ.values (first + j * digitSpan c)
            (first + (j + 1) * digitSpan c) hsrc (by omega) hT (h + 1) hh1
          rw [← hval, ← hcb] at h5
          exact Fin.ext h5
        · exfalso
          have hlast : lastDelimiter first (digitSpan c) n ≤ k + 1 := by
            unfold lastDelimiter
            have hd : (n - 1 - first) / digitSpan c < j + 2 :=
              (Nat.div_lt_iff_lt_mul hR).mpr (by omega)
            have hm := Nat.mul_le_mul_left (digitSpan c) (Nat.le_of_lt_succ hd)
            omega
          rcases hQ.fragment (by omega) DigitLane.writer (k + 1) hlast hk1 v t with h1 | h1
          · exact h1 hinY
          · rw [hviewY] at h1
            exact absurd h1.2 (by decide)

end L3.DigitQuiet

#print axioms L3.DigitQuiet.scanTargetW_local
#print axioms L3.DigitQuiet.digits_complete_block
#print axioms L3.DigitQuiet.digits_base_value
#print axioms L3.DigitQuiet.digits_launch_value
#print axioms L3.DigitQuiet.digits_advance_value
