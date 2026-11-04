import Leader.L3.Small.DigitTables
import Leader.L3.Width.DigitPairMomentPremise

/-!
# The SMALL writer-lane certificate `40 ⌊n/r⌋ (N-1)^t ≤ N^t`

Exact Jensen (`L3.PairMoment.costOfMoment`, through `simultaneousOfMoments`) turns the per-pair
moments `E[z^T] ≤ 40` (`z = N/(N-1)`, `N = n k`, `k = 2 C_r + 1`) of the `⌊n/r⌋` complete writer
pairs into the expected cost `t` once `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t`.  On SMALL the slot is
`t = ⌊c n² / 2⌋` with `c = smallDigitWriterTable q`; this module proves the inequality on every
SMALL ring (`smallWriterCertificate`).  The exponent is of order `n² ≤ 2^64`, so the inequality
is not checked numerically; it is reduced to small exact checks:

* `unitBlock`: a run of `n` letters multiplies `z^t` by at least `(k+1)/k`
  (Bernoulli, `tangentAbove`): `(k+1) (N-1)^n ≤ k N^n`.
* `chunkOne`: `a` such runs give at least `num_a / (2 k²)`,
  `num_a = 2k² + 2ak + a² - a` (second-order Bernoulli, `secondOrder`).
* `pieceBound`: with chunks `a₁ = ⌈k/64⌉`, `a₂ = ⌈k/4096⌉` and counts `j₁, j₂`, the exact check
  `40 K (2k²)^{j₁+j₂} ≤ num_{a₁}^{j₁} num_{a₂}^{j₂}` gives the inequality at
  `t = n (a₁ j₁ + a₂ j₂)`, and `certMono` lifts it to every larger `t`.
* `coverOk`, `coverSound`: a list of pieces `(lo, hi, j₁, j₂)` covering the slice
  `2^{q-1} < n ≤ 2^q`, each with `2 (a₁ j₁ + a₂ j₂) ≤ c lo`.
* `smallWriterCoverFinite`: `decide` on `3 ≤ q ≤ 32` over the piece lists
  `smallWriterPieces` (at most four pieces per slice, numbers below `10^{20000}`).
* `smallWriterCertLarge`: on `33 ≤ q ≤ 79` (`t ∈ {6, 7}`, `c = 3`) by blocks of `N` letters
  (`momentBlocks`, factor `5/2`) with `j = q + 6`.
-/

namespace L3.PairMomentCert

open L3
open L3.RenewalReferenceClock
open L3.PairMoment
open L3.PairMomentPremise
open L3.WidthDigit

set_option autoImplicit false
set_option exponentiation.threshold 100000

/-- `k = 2 C_r + 1` of slice `q`.  Consumer: `smallWriterCoverFinite`, `smallWriterCertificate`. -/
def sliceK (q : Nat) : Nat :=
  2 * bankRepairDigitPairClock (bankRepairDigitRadius (compileAdvice q).t) + 1

/-- `r = 2^t - 1` of slice `q` (`valueSpan n` on the slice).  Consumer: as `sliceK`. -/
def sliceR (q : Nat) : Nat := digitSpan (compileAdvice q)

/-- The large chunk `⌈k / 64⌉`.  Consumer: `pieceOk`. -/
def chunkLarge (k : Nat) : Nat := (k + 63) / 64

/-- The small chunk `⌈k / 4096⌉`.  Consumer: `pieceOk`. -/
def chunkSmall (k : Nat) : Nat := (k + 4095) / 4096

/-- `num_a = 2k² + 2ak + a² - a`: `(1 + 1/k)^a ≥ num_a / (2k²)`.  Consumer: `chunkOne`,
`pieceOk`. -/
def chunkNum (k a : Nat) : Nat := 2 * k * k + 2 * a * k + a * a - a

/-! ### The exact lower bounds -/

/-- A run of `n` letters: `(k+1) (N-1)^n ≤ k N^n`, `N = n k`.  Consumer: `unitBlocks`. -/
theorem unitBlock (n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (k + 1) * (n * k - 1) ^ n ≤ k * (n * k) ^ n := by
  obtain ⟨M, hM⟩ : ∃ M, n * k = M + 1 := ⟨n * k - 1, by have := Nat.mul_le_mul hn hk; omega⟩
  rw [hM, Nat.add_sub_cancel]
  have h := tangentAbove M n
  generalize hA : (M + 1) ^ n = A at h ⊢
  rw [← hM] at h
  have e1 : (n * k + n) * M ^ n = n * ((k + 1) * M ^ n) := by grind
  have e2 : n * k * A = n * (k * A) := by grind
  rw [e1, e2] at h
  exact Nat.le_of_mul_le_mul_left h (by omega)

/-- `s` runs of `n` letters. Consumer: `pieceBound`. -/
theorem unitBlocks (n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) (s : Nat) :
    (k + 1) ^ s * (n * k - 1) ^ (n * s) ≤ k ^ s * (n * k) ^ (n * s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hb := unitBlock n k hn hk
    rw [Nat.mul_succ, Nat.pow_add (n * k - 1), Nat.pow_add (n * k), Nat.pow_succ, Nat.pow_succ]
    calc (k + 1) ^ s * (k + 1) * ((n * k - 1) ^ (n * s) * (n * k - 1) ^ n)
        = ((k + 1) ^ s * (n * k - 1) ^ (n * s)) * ((k + 1) * (n * k - 1) ^ n) := by grind
      _ ≤ (k ^ s * (n * k) ^ (n * s)) * (k * (n * k) ^ n) := Nat.mul_le_mul ih hb
      _ = k ^ s * k * ((n * k) ^ (n * s) * (n * k) ^ n) := by grind

/-- `a` runs: `num_a k^a ≤ 2k² (k+1)^a`. Consumer: `chunkPow`. -/
theorem chunkOne (k a : Nat) : chunkNum k a * k ^ a ≤ 2 * k * k * (k + 1) ^ a := by
  have h := secondOrder k a
  have haa : a ≤ a * a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; exact Nat.le_refl _
    · exact Nat.le_mul_of_pos_left a hpos
  unfold chunkNum
  rw [Nat.sub_mul]
  have e : (2 * k * k + 2 * a * k + a * a) * k ^ a = k ^ a * (2 * k * k + 2 * a * k + a * a) :=
    Nat.mul_comm _ _
  rw [e]
  omega

/-- `j` chunks of `a` runs. Consumer: `pieceBound`. -/
theorem chunkPow (k a j : Nat) :
    chunkNum k a ^ j * k ^ (a * j) ≤ (2 * k * k) ^ j * (k + 1) ^ (a * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hb := chunkOne k a
    rw [Nat.mul_succ, Nat.pow_add k, Nat.pow_add (k + 1), Nat.pow_succ, Nat.pow_succ]
    calc chunkNum k a ^ j * chunkNum k a * (k ^ (a * j) * k ^ a)
        = (chunkNum k a ^ j * k ^ (a * j)) * (chunkNum k a * k ^ a) := by grind
      _ ≤ ((2 * k * k) ^ j * (k + 1) ^ (a * j)) * (2 * k * k * (k + 1) ^ a) :=
          Nat.mul_le_mul ih hb
      _ = (2 * k * k) ^ j * (2 * k * k) * ((k + 1) ^ (a * j) * (k + 1) ^ a) := by grind

/-- **One exact check gives the certificate at `t = n (a₁ j₁ + a₂ j₂)`**. Consumer:
`pieceSound`. -/
theorem pieceBound (n k a1 a2 j1 j2 K : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hcheck : 40 * K * (2 * k * k) ^ (j1 + j2) ≤ chunkNum k a1 ^ j1 * chunkNum k a2 ^ j2) :
    K * 40 * (n * k - 1) ^ (n * (a1 * j1 + a2 * j2)) ≤ (n * k) ^ (n * (a1 * j1 + a2 * j2)) := by
  have hU := unitBlocks n k hn hk (a1 * j1 + a2 * j2)
  have hC1 := chunkPow k a1 j1
  have hC2 := chunkPow k a2 j2
  have hD : 0 < (2 * k * k) ^ (j1 + j2) * k ^ (a1 * j1 + a2 * j2) :=
    Nat.mul_pos (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by decide) hk) hk)) (Nat.pow_pos (by omega))
  rw [Nat.pow_add (2 * k * k)] at hcheck hD
  rw [Nat.pow_add (k + 1), Nat.pow_add k] at hU
  rw [Nat.pow_add k] at hD
  generalize (n * k - 1) ^ (n * (a1 * j1 + a2 * j2)) = X at hU ⊢
  generalize (n * k) ^ (n * (a1 * j1 + a2 * j2)) = Y at hU ⊢
  generalize (2 * k * k) ^ j1 = D1 at hcheck hC1 hD
  generalize (2 * k * k) ^ j2 = D2 at hcheck hC2 hD
  generalize k ^ (a1 * j1) = p1 at hU hC1 hD
  generalize k ^ (a2 * j2) = p2 at hU hC2 hD
  generalize (k + 1) ^ (a1 * j1) = u1 at hU hC1
  generalize (k + 1) ^ (a2 * j2) = u2 at hU hC2
  generalize chunkNum k a1 ^ j1 = m1 at hcheck hC1
  generalize chunkNum k a2 ^ j2 = m2 at hcheck hC2
  have h1 : (D1 * D2 * (p1 * p2)) * (K * 40 * X) = (40 * K * (D1 * D2)) * (X * (p1 * p2)) := by
    grind
  have h2 : (40 * K * (D1 * D2)) * (X * (p1 * p2)) ≤ (m1 * m2) * (X * (p1 * p2)) :=
    Nat.mul_le_mul_right _ hcheck
  have h3 : (m1 * m2) * (X * (p1 * p2)) = ((m1 * p1) * (m2 * p2)) * X := by grind
  have h4 : ((m1 * p1) * (m2 * p2)) * X ≤ ((D1 * u1) * (D2 * u2)) * X :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hC1 hC2)
  have h5 : ((D1 * u1) * (D2 * u2)) * X = (D1 * D2) * ((u1 * u2) * X) := by grind
  have h6 : (D1 * D2) * ((u1 * u2) * X) ≤ (D1 * D2) * ((p1 * p2) * Y) :=
    Nat.mul_le_mul_left _ hU
  have h7 : (D1 * D2) * ((p1 * p2) * Y) = (D1 * D2 * (p1 * p2)) * Y := by grind
  have hfin : (D1 * D2 * (p1 * p2)) * (K * 40 * X) ≤ (D1 * D2 * (p1 * p2)) * Y := by
    rw [h1]; rw [← h7]; exact Nat.le_trans h2 (by rw [h3]; exact Nat.le_trans h4 (by rw [h5]; exact h6))
  exact Nat.le_of_mul_le_mul_left hfin hD

/-- The certificate is monotone in `t`. Consumer: `pieceSound`, `smallWriterCertLarge`. -/
theorem certMono (N A s t : Nat) (hst : s ≤ t) (h : A * (N - 1) ^ s ≤ N ^ s) :
    A * (N - 1) ^ t ≤ N ^ t := by
  obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
  rw [Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul h (Nat.pow_le_pow_left (Nat.sub_le N 1) d)

/-! ### Pieces and covers -/

/-- A piece `(lo, hi, j₁, j₂)` is valid for `k, r, c`: the exact check at the largest ring
`hi`, the exponent fits `⌊c n² / 2⌋` from `lo` on, and `lo ≥ 1`.  Consumer: `coverOk`. -/
def pieceOk (k r c : Nat) (p : Nat × Nat × Nat × Nat) : Bool :=
  Nat.ble (40 * (p.2.1 / r) * (2 * k * k) ^ (p.2.2.1 + p.2.2.2))
      (chunkNum k (chunkLarge k) ^ p.2.2.1 * chunkNum k (chunkSmall k) ^ p.2.2.2) &&
    Nat.ble (2 * (chunkLarge k * p.2.2.1 + chunkSmall k * p.2.2.2)) (c * p.1) &&
    Nat.ble 1 p.1

/-- The pieces cover `[s, e]` in order. Consumer: `coverSound`, `smallWriterCoverFinite`. -/
def coverOk (k r c : Nat) : Nat → Nat → List (Nat × Nat × Nat × Nat) → Bool
  | s, e, [] => Nat.blt e s
  | s, e, p :: ps => Nat.ble p.1 s && pieceOk k r c p && coverOk k r c (p.2.1 + 1) e ps

/-- A valid piece gives the certificate on `[lo, hi]`. Consumer: `coverSound`. -/
theorem pieceSound (k r c : Nat) (hk : 1 ≤ k) (p : Nat × Nat × Nat × Nat)
    (h : pieceOk k r c p = true) (n : Nat) (hlo : p.1 ≤ n) (hhi : n ≤ p.2.1) :
    n / r * 40 * (n * k - 1) ^ (c * n ^ 2 / 2) ≤ (n * k) ^ (c * n ^ 2 / 2) := by
  obtain ⟨lo, hi, j1, j2⟩ := p
  simp only [pieceOk, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only at hlo hhi
  have hK : n / r ≤ hi / r := Nat.div_le_div_right hhi
  have hcheck : 40 * (n / r) * (2 * k * k) ^ (j1 + j2) ≤
      chunkNum k (chunkLarge k) ^ j1 * chunkNum k (chunkSmall k) ^ j2 :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 40 hK)) h1
  have hb := pieceBound n k (chunkLarge k) (chunkSmall k) j1 j2 (n / r) (by omega) hk hcheck
  apply certMono _ _ _ _ _ hb
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  have hn2 : n ^ 2 = n * n := Nat.pow_two n
  have h4 : n * (2 * (chunkLarge k * j1 + chunkSmall k * j2)) ≤ n * (c * n) :=
    Nat.mul_le_mul_left n (Nat.le_trans h2 (Nat.mul_le_mul_left c hlo))
  have e1 : n * (chunkLarge k * j1 + chunkSmall k * j2) * 2 =
      n * (2 * (chunkLarge k * j1 + chunkSmall k * j2)) := by grind
  have e2 : c * n ^ 2 = n * (c * n) := by rw [hn2]; grind
  rw [e1, e2]
  exact h4

/-- A cover gives the certificate on `[s, e]`. Consumer: `smallWriterCertificate`. -/
theorem coverSound (k r c : Nat) (hk : 1 ≤ k) :
    ∀ (ps : List (Nat × Nat × Nat × Nat)) (s e : Nat), coverOk k r c s e ps = true →
      ∀ n, s ≤ n → n ≤ e →
        n / r * 40 * (n * k - 1) ^ (c * n ^ 2 / 2) ≤ (n * k) ^ (c * n ^ 2 / 2) := by
  intro ps
  induction ps with
  | nil =>
    intro s e h n hs he
    simp only [coverOk, Nat.blt_eq] at h
    omega
  | cons p ps ih =>
    intro s e h n hs he
    simp only [coverOk, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨hps, hp⟩, hrest⟩ := h
    by_cases hn : n ≤ p.2.1
    · exact pieceSound k r c hk p hp n (by omega) hn
    · exact ih (p.2.1 + 1) e hrest n (by omega) he

/-! ### The slices -/

/-- The piece lists of the finite slices `3 ≤ q ≤ 32`, computed exactly (scratch generator
cert3.py of this round).  Consumer: `smallWriterCoverFinite`. -/
def smallWriterPieces : Nat → List (Nat × Nat × Nat × Nat)
  | 3 => [(5, 5, 263, 5), (6, 8, 278, 0)]
  | 4 => [(9, 11, 303, 1), (12, 16, 336, 0)]
  | 5 => [(17, 20, 292, 26), (21, 32, 325, 0)]
  | 6 => [(33, 34, 334, 29), (35, 48, 354, 45), (49, 64, 377, 0)]
  | 7 => [(65, 69, 377, 9), (70, 104, 406, 10), (105, 128, 422, 0)]
  | 8 => [(129, 132, 421, 14), (133, 160, 434, 18), (161, 256, 466, 0)]
  | 9 => [(257, 258, 465, 53), (259, 272, 469, 30), (273, 405, 494, 53), (406, 512, 511, 0)]
  | 10 => [(513, 517, 510, 54), (518, 559, 515, 52), (560, 1024, 555, 0)]
  | 11 => [(1025, 1056, 556, 48), (1057, 1385, 574, 10), (1386, 2048, 600, 0)]
  | 12 => [(2049, 2162, 602, 54), (2163, 3653, 636, 26), (3654, 4096, 644, 0)]
  | 13 => [(4097, 4451, 649, 6), (4452, 8192, 689, 0)]
  | 14 => [(8193, 8588, 691, 10), (8589, 14475, 724, 35), (14476, 16384, 733, 0)]
  | 15 => [(16385, 18913, 741, 43), (18914, 32768, 777, 0)]
  | 16 => [(32769, 54221, 809, 6), (54222, 65536, 822, 0)]
  | 17 => [(65537, 65905, 726, 30), (65906, 70245, 730, 35), (70246, 131072, 771, 0)]
  | 18 => [(131073, 132431, 771, 9), (132432, 150070, 779, 9), (150071, 262144, 815, 0)]
  | 19 => [(262145, 264057, 815, 20), (264058, 289818, 821, 17), (289819, 524288, 860, 0)]
  | 20 => [(524289, 526689, 859, 32), (526690, 560107, 863, 28), (560108, 1048576, 904, 0)]
  | 21 => [(1048577, 1118200, 907, 44), (1118201, 2097152, 948, 0)]
  | 22 => [(2097153, 2692163, 963, 59), (2692164, 4194304, 993, 0)]
  | 23 => [(4194305, 4447197, 996, 3), (4447198, 8388608, 1037, 0)]
  | 24 => [(8388609, 16777216, 1082, 0)]
  | 25 => [(16777217, 33554432, 1126, 0)]
  | 26 => [(33554433, 67108864, 1170, 0)]
  | 27 => [(67108865, 134217728, 1215, 0)]
  | 28 => [(134217729, 268435456, 1259, 0)]
  | 29 => [(268435457, 536870912, 1303, 0)]
  | 30 => [(536870913, 1073741824, 1348, 0)]
  | 31 => [(1073741825, 2147483648, 1392, 0)]
  | 32 => [(2147483649, 4294967296, 1436, 0)]
  | _ => []

/-- **The finite slices are covered**: `decide` over `3 ≤ q ≤ 32`.  Consumer:
`smallWriterCertificate`. -/
theorem smallWriterCoverFinite :
    ∀ i : Fin 33, 3 ≤ i.val →
      coverOk (sliceK i.val) (sliceR i.val) (smallDigitWriterFinite i.val)
        (2 ^ (i.val - 1) + 1) (2 ^ i.val) (smallWriterPieces i.val) = true := by
  decide

/-- The large slices `33 ≤ q ≤ 79` by blocks of `N` letters, `j = q + 6`, `c = 3`.
Consumer: `smallWriterCertificate`. -/
theorem smallWriterCertLarge {n : Nat} (hn : 5 ≤ n) (h33 : 33 ≤ ceilLogTwo n)
    (h79 : ceilLogTwo n < 80) :
    n / sliceR (ceilLogTwo n) * 40 * (n * sliceK (ceilLogTwo n) - 1) ^ (3 * n ^ 2 / 2) ≤
      (n * sliceK (ceilLogTwo n)) ^ (3 * n ^ 2 / 2) := by
  have hspec := ceilLogTwo_spec n (by omega)
  generalize hq : ceilLogTwo n = q at h33 h79 hspec
  have ht : (compileAdvice q).t = ceilLogTwo q := compileAdvice_t_large q h33
  have hc := ceilLogTwo_spec q (by omega)
  have hc67 : ceilLogTwo q = 6 ∨ ceilLogTwo q = 7 := by
    have hlo : 6 ≤ ceilLogTwo q := by
      by_cases h : 6 ≤ ceilLogTwo q
      · exact h
      · have : 2 ^ ceilLogTwo q ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
        have e5 : (2 : Nat) ^ 5 = 32 := by decide
        omega
    have hhi : ceilLogTwo q ≤ 7 := by
      by_cases h : ceilLogTwo q ≤ 7
      · exact h
      · have : 2 ^ 7 ≤ 2 ^ (ceilLogTwo q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have e7 : (2 : Nat) ^ 7 = 128 := by decide
        omega
    omega
  -- `2 k (q + 6) ≤ 3 n`
  have hk3 : 2 * sliceK q * (q + 6) ≤ 3 * n := by
    unfold sliceK
    rw [ht]
    rcases hc67 with hc6 | hc7
    · have eC : 2 * bankRepairDigitPairClock (bankRepairDigitRadius 6) + 1 = 67037805 := by decide
      rw [hc6, eC]
      have e6 : (2 : Nat) ^ 6 = 64 := by decide
      have hq64 : q ≤ 64 := by
        rw [hc6] at hc
        omega
      have h32 : 2 ^ 32 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
      omega
    · have eC : 2 * bankRepairDigitPairClock (bankRepairDigitRadius 7) + 1 = 1073452269 := by
        decide
      rw [hc7, eC]
      have e6 : (2 : Nat) ^ 6 = 64 := by decide
      have hq65 : 65 ≤ q := by
        rw [hc7] at hc
        omega
      have h64 : 2 ^ 64 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
      omega
  have hk : 1 ≤ sliceK q := by unfold sliceK; omega
  have hN : 2 ≤ n * sliceK q := by
    have := Nat.mul_le_mul_left n hk; omega
  -- `K 40 2^j ≤ 5^j`, `K = n / r ≤ 2^q`
  have hKj : n / sliceR q * 40 * 2 ^ (q + 6) ≤ 5 ^ (q + 6) := by
    have hK : n / sliceR q ≤ 2 ^ q := Nat.le_trans (Nat.div_le_self _ _) hspec.2
    have h4 : 4 ^ q ≤ 5 ^ q := Nat.pow_le_pow_left (by omega) q
    have h22 : 2 ^ q * 2 ^ q = 4 ^ q := by rw [← Nat.mul_pow]
    have e1 : 2 ^ q * 40 * 2 ^ (q + 6) = 2560 * (2 ^ q * 2 ^ q) := by rw [Nat.pow_add]; grind
    have e2 : 5 ^ (q + 6) = 15625 * 5 ^ q := by rw [Nat.pow_add]; grind
    have h1 := Nat.mul_le_mul_right (2 ^ (q + 6)) (Nat.mul_le_mul_right 40 hK)
    omega
  have hb := momentBlocks (n * sliceK q) hN (q + 6)
  have hblock : n / sliceR q * 40 * (n * sliceK q - 1) ^ (n * sliceK q * (q + 6)) ≤
      (n * sliceK q) ^ (n * sliceK q * (q + 6)) := by
    have h1 : n / sliceR q * 40 * (n * sliceK q - 1) ^ (n * sliceK q * (q + 6)) * 2 ^ (q + 6) ≤
        5 ^ (q + 6) * (n * sliceK q - 1) ^ (n * sliceK q * (q + 6)) := by
      rw [Nat.mul_right_comm]
      exact Nat.mul_le_mul_right _ hKj
    have h2 : 2 ^ (q + 6) * (n / sliceR q * 40 * (n * sliceK q - 1) ^ (n * sliceK q * (q + 6))) ≤
        2 ^ (q + 6) * (n * sliceK q) ^ (n * sliceK q * (q + 6)) := by
      rw [Nat.mul_comm (2 ^ (q + 6))]
      exact Nat.le_trans h1 hb
    exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos (by omega))
  apply certMono _ _ _ _ _ hblock
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  have hn2 : n ^ 2 = n * n := Nat.pow_two n
  have h5 : n * (2 * sliceK q * (q + 6)) ≤ n * (3 * n) := Nat.mul_le_mul_left n hk3
  have e1 : n * sliceK q * (q + 6) * 2 = n * (2 * sliceK q * (q + 6)) := by grind
  have e2 : 3 * n ^ 2 = n * (3 * n) := by rw [hn2]; grind
  rw [e1, e2]
  exact h5

/-- **The SMALL writer-lane certificate**: on every SMALL ring,
`⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` with `N = widthPairMomentWidth n`, `r = valueSpan n` and
`t = ⌊smallDigitWriterTable q · n² / 2⌋`.  Consumer: `L3.WriterStage.smallWaveClockOfWriter`. -/
theorem smallWriterCertificate {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    n / L3.ValueWaveClose.valueSpan n * 40 *
        (widthPairMomentWidth n - 1) ^ (smallDigitWriterTable (ceilLogTwo n) * n ^ 2 / 2) ≤
      widthPairMomentWidth n ^ (smallDigitWriterTable (ceilLogTwo n) * n ^ 2 / 2) := by
  obtain ⟨hlo, hhi⟩ := L3.SmallFinishClean.smallDigitSliceBounds hn hsmall
  have hW : widthPairMomentWidth n = n * sliceK (ceilLogTwo n) := rfl
  have hR : L3.ValueWaveClose.valueSpan n = sliceR (ceilLogTwo n) := rfl
  rw [hW, hR]
  unfold smallDigitWriterTable
  by_cases h32 : ceilLogTwo n ≤ 32
  · rw [if_pos h32]
    have hspec := ceilLogTwo_spec n (by omega)
    have hk : 1 ≤ sliceK (ceilLogTwo n) := by unfold sliceK; omega
    have hcov : coverOk (sliceK (ceilLogTwo n)) (sliceR (ceilLogTwo n))
        (smallDigitWriterFinite (ceilLogTwo n)) (2 ^ (ceilLogTwo n - 1) + 1) (2 ^ ceilLogTwo n)
        (smallWriterPieces (ceilLogTwo n)) = true :=
      smallWriterCoverFinite ⟨ceilLogTwo n, by omega⟩ hlo
    exact coverSound _ _ _ hk _ _ _ hcov n (by omega) hspec.2
  · rw [if_neg h32]
    exact smallWriterCertLarge hn (by omega) hhi

end L3.PairMomentCert

#print axioms L3.PairMomentCert.pieceBound
#print axioms L3.PairMomentCert.smallWriterCoverFinite
#print axioms L3.PairMomentCert.smallWriterCertLarge
#print axioms L3.PairMomentCert.smallWriterCertificate
