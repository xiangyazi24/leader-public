import Leader.L4.Compiler.Digits

/-!
Word-level facts for the remaining digit primitives (MUX, MAX, SMALL, P, B-1, MASK,
CMP, SCAN5), on top of `L4.Compiler.Digits`. Digits are little-endian:
digit `j` has weight `16 ^ j`.
-/

namespace L4
namespace Compiler
namespace Digits

theorem pow16_pos (j : Nat) : 1 ≤ 16 ^ j := by
  have h := Nat.pow_le_pow_right (show 0 < 16 by decide) (Nat.zero_le j)
  rwa [Nat.pow_zero] at h

/-- Every `j`-digit prefix is below `16 ^ j`. -/
theorem valJ_lt {r : Nat} (w : Word r) : ∀ j (h : j ≤ r), valJ w j h < 16 ^ j := by
  intro j
  induction j with
  | zero => intro h; exact Nat.lt_of_lt_of_le (Nat.zero_lt_one) (pow16_pos 0)
  | succ j ih =>
      intro h
      rw [val_succ, Nat.pow_succ]
      have hv := ih (Nat.le_of_succ_le h)
      have hd : (w ⟨j, Nat.lt_of_succ_le h⟩).val ≤ 15 :=
        Nat.le_of_lt_succ (w ⟨j, Nat.lt_of_succ_le h⟩).isLt
      have hdm := Nat.mul_le_mul_left (16 ^ j) hd
      omega

/-- Prefix values depend only on the digits inside the prefix. -/
theorem valJ_congr {r : Nat} (w w' : Word r) : ∀ j (h : j ≤ r),
    (∀ i (hi : i < r), i < j → (w ⟨i, hi⟩).val = (w' ⟨i, hi⟩).val) →
    valJ w j h = valJ w' j h := by
  intro j
  induction j with
  | zero => intro h _; rfl
  | succ j ih =>
      intro h hd
      rw [val_succ, val_succ, ih (Nat.le_of_succ_le h) (fun i hi hij => hd i hi (by omega)),
        hd j (Nat.lt_of_succ_le h) (by omega)]

/-- Digits that are zero from position `k` on do not change the prefix value. -/
theorem valJ_stable {r : Nat} (w : Word r) (k : Nat) : ∀ d (h : k + d ≤ r),
    (∀ i (hi : i < r), k ≤ i → i < k + d → (w ⟨i, hi⟩).val = 0) →
    valJ w (k + d) h = valJ w k (Nat.le_trans (Nat.le_add_right k d) h) := by
  intro d
  induction d with
  | zero => intro h _; rfl
  | succ d ih =>
      intro h hz
      show valJ w (k + d + 1) h = _
      rw [val_succ, ih (by omega) (fun i hi h1 h2 => hz i hi h1 (by omega)),
        hz (k + d) (by omega) (by omega) (by omega), Nat.mul_zero, Nat.add_zero]

/-- A prefix whose digits are all zero has value zero. -/
theorem valJ_zero_digits {r : Nat} (w : Word r) (j : Nat) (h : j ≤ r)
    (hz : ∀ i (hi : i < r), i < j → (w ⟨i, hi⟩).val = 0) : valJ w j h = 0 := by
  have := valJ_stable w 0 j (by omega) (fun i hi _ h2 => hz i hi (by omega))
  simp only [Nat.zero_add] at this
  rw [this]; rfl

/-- The constant-15 prefix. -/
theorem valJ_allF {r : Nat} : ∀ j (h : j ≤ r),
    valJ (fun _ : Fin r => (15 : Nib)) j h = 16 ^ j - 1 := by
  intro j
  induction j with
  | zero => intro h; rfl
  | succ j ih =>
      intro h
      rw [val_succ, ih (Nat.le_of_succ_le h), Nat.pow_succ]
      have hp := pow16_pos j
      show 16 ^ j - 1 + 16 ^ j * 15 = 16 ^ j * 16 - 1
      omega

/-- The high part of a word above position `j` is a multiple of `16 ^ j`. -/
theorem valJ_mod {r : Nat} (w : Word r) (j : Nat) (hj : j ≤ r) : ∀ d (h : j + d ≤ r),
    valJ w (j + d) h % 16 ^ j = valJ w j hj := by
  intro d
  induction d with
  | zero => intro h; exact Nat.mod_eq_of_lt (valJ_lt w j hj)
  | succ d ih =>
      intro h
      show valJ w (j + d + 1) h % 16 ^ j = _
      rw [val_succ]
      have hp : 16 ^ (j + d) = 16 ^ j * 16 ^ d := Nat.pow_add 16 j d
      rw [hp, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      exact ih (by omega)

theorem mux_word {r : Nat} (q : Bool) (a b : Word r) :
    val (fun i => muxStep q (a i) (b i)) = if q then val a else val b := by
  cases q <;> rfl

theorem max_word {r : Nat} : val (fun _ : Fin r => constMaxStep) = 16 ^ r - 1 :=
  valJ_allF r (Nat.le_refl r)

theorem small_word {r : Nat} (hr : 1 ≤ r) (q : Nib) :
    val (fun i : Fin r => constSmallStep q (positionAt r i.val)) = q.val := by
  unfold val
  have hs := valJ_stable (fun i : Fin r => constSmallStep q (positionAt r i.val)) 1 (r - 1)
    (by omega) (by
      intro i hi h1 _
      have : i ≠ 0 := by omega
      simp [constSmallStep, positionAt, this])
  have e : 1 + (r - 1) = r := by omega
  have key : valJ (fun i : Fin r => constSmallStep q (positionAt r i.val)) r (Nat.le_refl r) =
      valJ (fun i : Fin r => constSmallStep q (positionAt r i.val)) (1 + (r - 1)) (by omega) := by
    congr 1 <;> omega
  rw [key, hs, val_succ]
  simp [constSmallStep, positionAt]
  rfl

theorem p_word {r : Nat} (hr : 1 ≤ r) :
    val (fun i : Fin r => constPStep (positionAt r i.val)) = 16 ^ r / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  unfold val
  rw [val_succ]
  have hz := valJ_zero_digits (fun i : Fin (k + 1) => constPStep (positionAt (k + 1) i.val)) k
    (Nat.le_succ k) (by
      intro i hi hik
      have : ¬ i = k := by omega
      simp [constPStep, positionAt, this])
  rw [hz]
  simp [constPStep, positionAt]
  rw [Nat.pow_succ]
  have hp := pow16_pos k
  show 16 ^ k * 8 = 16 ^ k * 16 / 2
  omega

theorem bm1_word {r : Nat} (hr : 2 ≤ r) :
    val (fun i : Fin r => constBM1Step (positionAt r i.val)) = 16 ^ (r - 2) - 1 := by
  let w := fun i : Fin r => constBM1Step (positionAt r i.val)
  have hs := valJ_stable w (r - 2) 2 (by omega) (by
      intro i hi h1 _
      have : r ≤ i + 2 := by omega
      simp [w, constBM1Step, positionAt, this])
  have hc := valJ_congr w (fun _ : Fin r => (15 : Nib)) (r - 2) (by omega) (by
      intro i hi h1
      have : ¬ (r ≤ i + 2) := by omega
      simp [w, constBM1Step, positionAt, this])
  have key : val w = valJ w (r - 2 + 2) (by omega) := by
    unfold val; congr 1 <;> omega
  rw [key, hs, hc, valJ_allF]

theorem mask_word {r : Nat} (hr : 2 ≤ r) (a : Word r) :
    val (fun i => maskStep (a i) (positionAt r i.val)) = val a % 16 ^ (r - 2) := by
  let w := fun i => maskStep (a i) (positionAt r i.val)
  have hs := valJ_stable w (r - 2) 2 (by omega) (by
      intro i hi h1 _
      have : r ≤ i + 2 := by omega
      simp [w, maskStep, positionAt, this])
  have hc := valJ_congr w a (r - 2) (by omega) (by
      intro i hi h1
      have : ¬ (r ≤ i + 2) := by omega
      simp [w, maskStep, positionAt, this])
  have hm := valJ_mod a (r - 2) (by omega) 2 (by omega)
  have key : val w = valJ w (r - 2 + 2) (by omega) := by
    unfold val; congr 1 <;> omega
  have key' : val a = valJ a (r - 2 + 2) (by omega) := by
    unfold val; congr 1 <;> omega
  rw [key, hs, hc, key', hm]

/-- Restricting a word to its first `r` digits does not change those prefixes. -/
theorem valJ_castSucc {r : Nat} (a : Word (r + 1)) : ∀ j (h : j ≤ r),
    valJ (fun i : Fin r => a i.castSucc) j h = valJ a j (Nat.le_succ_of_le h) := by
  intro j
  induction j with
  | zero => intro h; rfl
  | succ j ih =>
      intro h
      rw [val_succ, val_succ, ih (Nat.le_of_succ_le h)]
      rfl

theorem val_last {r : Nat} (a : Word (r + 1)) :
    val a = val (fun i : Fin r => a i.castSucc) + 16 ^ r * (a (Fin.last r)).val := by
  unfold val
  rw [val_succ, valJ_castSucc a r (Nat.le_refl r)]
  rfl

theorem cmp_word {r : Nat} (a b : Word r) :
    (List.finRange r).foldl (fun z i => cmpStep z.1 z.2 (a i) (b i)) (true, false) =
      (decide (val a = val b), decide (val a < val b)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [List.finRange_succ_last, List.foldl_append, List.foldl_map,
        ih (fun i => a i.castSucc) (fun i => b i.castSucc)]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [val_last a, val_last b]
      have ha : val (fun i : Fin r => a i.castSucc) < 16 ^ r :=
        valJ_lt (fun i : Fin r => a i.castSucc) r (Nat.le_refl r)
      have hb : val (fun i : Fin r => b i.castSucc) < 16 ^ r :=
        valJ_lt (fun i : Fin r => b i.castSucc) r (Nat.le_refl r)
      unfold cmpStep
      generalize val (fun i : Fin r => a i.castSucc) = x at ha ⊢
      generalize val (fun i : Fin r => b i.castSucc) = y at hb ⊢
      generalize (a (Fin.last r)).val = u
      generalize (b (Fin.last r)).val = v
      by_cases huv : u = v
      · subst huv
        simp
      · have hne : x + 16 ^ r * u ≠ y + 16 ^ r * v := by
          intro heq
          rcases Nat.lt_or_gt_of_ne huv with hlt | hlt
          · have := Nat.mul_le_mul_left (16 ^ r) (show u + 1 ≤ v by omega)
            rw [Nat.mul_add, Nat.mul_one] at this
            omega
          · have := Nat.mul_le_mul_left (16 ^ r) (show v + 1 ≤ u by omega)
            rw [Nat.mul_add, Nat.mul_one] at this
            omega
        have hlt : (x + 16 ^ r * u < y + 16 ^ r * v) ↔ u < v := by
          constructor
          · intro h
            rcases Nat.lt_or_ge u v with h1 | h1
            · exact h1
            · have := Nat.mul_le_mul_left (16 ^ r) (show v + 1 ≤ u by omega)
              rw [Nat.mul_add, Nat.mul_one] at this
              omega
          · intro h
            have := Nat.mul_le_mul_left (16 ^ r) (show u + 1 ≤ v by omega)
            rw [Nat.mul_add, Nat.mul_one] at this
            omega
        rw [if_neg huv, decide_eq_false huv, Bool.and_false, decide_eq_false hne]
        exact congrArg (Prod.mk false) ((decide_eq_decide).2 hlt.symm)

/-- Folding SCAN5 over positions that are all at least 2 leaves the accumulator alone. -/
theorem scan_tail {n : Nat} (a : Fin n → Nib) (l : List (Fin n)) (z : Fin 32)
    (hl : ∀ i ∈ l, 2 ≤ i.val) :
    l.foldl (fun z i => scan5Step i.val z (a i)) z = z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldl_cons]
      have hi := hl i (List.mem_cons_self ..)
      have h0 : i.val ≠ 0 := by omega
      have h1 : i.val ≠ 1 := by omega
      have : scan5Step i.val z (a i) = z := by simp [scan5Step, h0, h1]
      rw [this]
      exact ih z (fun j hj => hl j (List.mem_cons_of_mem _ hj))

theorem scan_word {r : Nat} (hr : 2 ≤ r) (a : Word r) :
    ((List.finRange r).foldl (fun z i => scan5Step i.val z (a i)) (0 : Fin 32)).val =
      val a % 32 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [List.finRange_succ, List.foldl_cons, List.finRange_succ, List.map_cons,
    List.foldl_cons, List.map_map]
  rw [scan_tail]
  · have hm := valJ_mod a 2 (by omega) k (by omega)
    have key : val a = valJ a (2 + k) (by omega) := by
      unfold val; congr 1 <;> omega
    rw [key, ← Nat.mod_mod_of_dvd _ (show 32 ∣ 16 ^ 2 by decide), hm]
    rw [val_succ, val_succ]
    show _ = (0 + 16 ^ 0 * (a ⟨0, _⟩).val + 16 ^ 1 * (a ⟨1, _⟩).val) % 32
    simp only [scan5Step]
    simp
    have h0 := (a ⟨0, by omega⟩).isLt
    omega
  · intro i hi
    simp only [List.mem_map, List.mem_finRange, true_and] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [Fin.succ]

end Digits
end Compiler
end L4

#print axioms L4.Compiler.Digits.valJ_lt
#print axioms L4.Compiler.Digits.valJ_congr
#print axioms L4.Compiler.Digits.valJ_stable
#print axioms L4.Compiler.Digits.valJ_mod
#print axioms L4.Compiler.Digits.mux_word
#print axioms L4.Compiler.Digits.max_word
#print axioms L4.Compiler.Digits.small_word
#print axioms L4.Compiler.Digits.p_word
#print axioms L4.Compiler.Digits.bm1_word
#print axioms L4.Compiler.Digits.mask_word
#print axioms L4.Compiler.Digits.cmp_word
#print axioms L4.Compiler.Digits.scan_word
