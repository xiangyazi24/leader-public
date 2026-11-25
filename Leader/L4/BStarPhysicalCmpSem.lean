import Leader.L4.BStarPhysicalWordSem

/-! The packed CMP sweep preserves every cell and returns the two exact
comparison flags, conditional on its chronological significant visits. -/
namespace L4.BStarPhysicalCmpSem
open AllSizeProtocol BStarTrace BStarLongToken BStarLongArithmetic
open BStarPhysicalDigitSem BStarPhysicalWordSem L4.Compiler.Digits
open L4.Compiler.Native

private theorem prefix_lt_pow {r : Nat} (w : Word r) (j : Nat) (hj : j ≤ r) :
    valJ w j hj < 16^j := by
  induction j with
  | zero => simp [valJ]
  | succ j ih =>
    have h := ih (by omega)
    have b := (w ⟨j, Nat.lt_of_succ_le hj⟩).isLt
    have m := Nat.mul_le_mul_left (16^j) (show (w ⟨j,Nat.lt_of_succ_le hj⟩).val+1≤16 by omega)
    rw [Nat.mul_add, Nat.mul_one] at m
    rw [val_succ, Nat.pow_succ]
    omega

private theorem less_high (x y W a b : Nat) (hx : x < W) (hab : a < b) :
    x + W*a < y + W*b := by
  have m := Nat.mul_le_mul_left W (show a+1≤b by omega)
  rw [Nat.mul_add, Nat.mul_one] at m
  omega

private theorem cmp_extend (x y W : Nat) (u v : Nib) (hx : x < W) (hy : y < W) :
    cmpStep (decide (x=y)) (decide (x<y)) u v =
      (decide (x+W*u.val=y+W*v.val), decide (x+W*u.val<y+W*v.val)) := by
  by_cases e : u.val=v.val
  · simp [cmpStep,e]
  · by_cases h : u.val<v.val
    · have H := less_high x y W u.val v.val hx h
      have N : x+W*u.val ≠ y+W*v.val := by omega
      simp [cmpStep,e,h,H,N]
    · have H := less_high y x W v.val u.val hy (by omega)
      have N : x+W*u.val ≠ y+W*v.val := by omega
      have NL : ¬ x+W*u.val<y+W*v.val := by omega
      simp [cmpStep,e,h,NL,N]

/-- An initialized physical CMP returns exact prefix equality and less-than
flags at each cursor, and writes no cell, including idempotent proposals. -/
theorem physical_cmp_prefix {r : Nat} {geom : Fin r → LongGeometry}
    {old updated : Fin r → BitVec LW} {i a b : Nat} {tokens : Nat → Payload}
    (H : DigitSweep geom old updated i (.cmp a b) tokens)
    (ha : WordSlot a) (hb : WordSlot b) (h0 : arg tokens 0 = cmpPack true false) :
    (∀ j (hj : j≤r), arg tokens j = cmpPack
      (decide (valJ (readWord old a ha) j hj = valJ (readWord old b hb) j hj))
      (decide (valJ (readWord old a ha) j hj < valJ (readWord old b hb) j hj))) ∧
    updated = old := by
  let A := readWord old a ha
  let B := readWord old b hb
  have make (j : Fin r) (he hl : Bool) (h : arg tokens j.val = cmpPack he hl) :
      let c := cmpStep he hl (A j) (B j)
      updated j = old j ∧ arg tokens (j.val+1) = cmpPack c.1 c.2 := by
    dsimp only
    have E := H.step j
    dsimp only at E
    rw [compare_row (geom j) (old j) i a b (tokens j.val) ha hb he hl h] at E
    have Ew := congrArg Prod.fst E
    have Et := congrArg Prod.snd E
    change withAcc (tokens j.val) (cmpPack (cmpStep he hl (A j) (B j)).1
      (cmpStep he hl (A j) (B j)).2) = tokens (j.val+1) at Et
    constructor
    · simpa [Patch.empty, Patch.apply] using Ew.symm
    · unfold arg
      rw [←Et]
      apply acc_read
      unfold cmpPack
      let p := (cmpStep he hl (A j) (B j)).1
      let q := (cmpStep he hl (A j) (B j)).2
      change 2*p.toNat+q.toNat<2^34
      cases p <;> cases q <;> decide
  have pref : ∀ j (hj : j≤r), arg tokens j = cmpPack
      (decide (valJ A j hj = valJ B j hj))
      (decide (valJ A j hj < valJ B j hj)) := by
    intro j
    induction j with
    | zero => intro _; simpa [valJ] using h0
    | succ j ih =>
      intro hj
      let k : Fin r := ⟨j, by omega⟩
      have hk : j ≤ r := by omega
      let x := valJ A j hk
      let y := valJ B j hk
      have next := (make k (decide (x=y)) (decide (x<y)) (ih hk)).2
      rw [cmp_extend x y (16^j) (A k) (B k) (prefix_lt_pow A j hk) (prefix_lt_pow B j hk)] at next
      exact next
  refine ⟨pref,?_⟩
  funext j
  exact (make j _ _ (pref j.val (Nat.le_of_lt j.isLt))).1

/-- At the return cursor of a complete chronological CMP sweep, the packed
flags are equality and strict order of the full old register words. -/
theorem physical_cmp_word {r : Nat} {geom : Fin r → LongGeometry}
    {old updated : Fin r → BitVec LW} {i a b : Nat} {tokens : Nat → Payload}
    (H : DigitSweep geom old updated i (.cmp a b) tokens)
    (ha : WordSlot a) (hb : WordSlot b) (h0 : arg tokens 0 = cmpPack true false) :
    arg tokens r = cmpPack (decide (val (readWord old a ha) = val (readWord old b hb)))
      (decide (val (readWord old a ha) < val (readWord old b hb))) ∧ updated = old := by
  obtain ⟨h,hu⟩ := physical_cmp_prefix H ha hb h0
  exact ⟨h r (Nat.le_refl r),hu⟩

end L4.BStarPhysicalCmpSem
