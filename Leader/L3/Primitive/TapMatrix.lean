import Leader.L3.Primitive.TapCert
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.List.Range
import Init.Data.Fin.Fold
import Init.Omega

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
# GF(2) tap matrices and their semantics

The vector space is Fin t -> Bool, not Nat. vcode / vdecode
provide a separate, bounded Nat-mask interface.
All matrix composition and binary-power semantics below are proved
for the literal TapCert definitions without changing them.
-/

/-- Little-endian encoding of t Boolean coordinates. -/
def vcode : (t : Nat) → (Fin t → Bool) → Nat
  | 0, _ => 0
  | t + 1, u =>
      2 * vcode t (fun j => u j.succ) + (u 0).toNat

/-- Extract coordinates 0 through t-1 from the Nat bitmask. -/
def vdecode (t : Nat) (x : Nat) : Fin t → Bool :=
  fun i => x.testBit i.val

private theorem double_add_bit_div (a : Nat) (b : Bool) :
    (2 * a + b.toNat) / 2 = a := by
  cases b <;> simp <;> omega

private theorem double_add_bit_testBit_zero (a : Nat) (b : Bool) :
    (2 * a + b.toNat).testBit 0 = b := by
  cases b <;> simp [Nat.testBit_zero, Nat.add_mod] <;> omega

theorem vcode_lt : ∀ (t : Nat) (u : Fin t → Bool),
    vcode t u < 2 ^ t := by
  intro t
  induction t with
  | zero =>
      intro u
      simp [vcode]
  | succ t ih =>
      intro u
      have ht := ih (fun j : Fin t => u j.succ)
      change 2 * vcode t (fun j : Fin t => u j.succ) +
        (u 0).toNat < 2 ^ (t + 1)
      rw [Nat.pow_succ]
      cases hb : u 0 <;> simp [hb] <;> omega

theorem vdecode_vcode (t : Nat) (u : Fin t → Bool) :
    vdecode t (vcode t u) = u := by
  induction t with
  | zero =>
      funext i
      exact i.elim0
  | succ t ih =>
      funext i
      cases i using Fin.cases with
      | zero =>
          change (2 * vcode t (fun j : Fin t => u j.succ) +
            (u 0).toNat).testBit 0 = u 0
          exact double_add_bit_testBit_zero _ _
      | succ j =>
          change (2 * vcode t (fun k : Fin t => u k.succ) +
            (u 0).toNat).testBit (j.val + 1) = u j.succ
          rw [Nat.testBit_add_one, double_add_bit_div]
          exact congrFun (ih (fun k : Fin t => u k.succ)) j

theorem vcode_vdecode (t : Nat) (x : Nat) (hx : x < 2 ^ t) :
    vcode t (vdecode t x) = x := by
  induction t generalizing x with
  | zero =>
      have h : x = 0 := by
        have h' : x < 1 := by simpa using hx
        omega
      subst x
      rfl
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by
        rw [Nat.pow_succ]
        omega
      have hhalf : x / 2 < 2 ^ t := by
        rw [hpow] at hx
        omega
      change 2 * vcode t
        (fun j : Fin t => x.testBit j.succ.val) +
          (x.testBit 0).toNat = x
      have htail :
          (fun j : Fin t => x.testBit j.succ.val) =
            vdecode t (x / 2) := by
        funext j
        change x.testBit (j.val + 1) = (x / 2).testBit j.val
        exact Nat.testBit_add_one x j.val
      rw [htail, ih (x / 2) hhalf, Nat.toNat_testBit]
      simp only [Nat.pow_zero, Nat.div_one]
      omega

private theorem testBit_vcode (t : Nat) (u : Fin t → Bool)
    (j : Nat) :
    (vcode t u).testBit j =
      if h : j < t then u ⟨j, h⟩ else false := by
  by_cases h : j < t
  · simpa [h, vdecode] using
      (congrFun (vdecode_vcode t u) ⟨j, h⟩)
  · have hj : t ≤ j := by omega
    have hp : 2 ^ t ≤ 2 ^ j :=
      Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat)) hj
    have hv : vcode t u < 2 ^ j :=
      Nat.lt_of_lt_of_le (vcode_lt t u) hp
    simp [h, Nat.testBit_lt_two_pow hv]

theorem vcode_xor (t : Nat) (u v : Fin t → Bool) :
    vcode t (fun i => (u i) ^^ (v i)) =
      ((vcode t u) ^^^ (vcode t v)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  rw [testBit_vcode, testBit_vcode, testBit_vcode]
  by_cases h : j < t <;> simp [h]

/-- Every matrix row has length t and fits in t bits. -/
def RowsWF (t : Nat) (A : List Nat) : Prop :=
  A.length = t ∧
    ∀ i : Nat, i < t → A.getD i 0 < 2 ^ t

private theorem range_map_getD (t i : Nat) (f : Nat → Nat)
    (hi : i < t) :
    ((List.range t).map f).getD i 0 = f i := by
  have hm : i < ((List.range t).map f).length := by simpa using hi
  rw [← List.getElem_eq_getD
    (l := (List.range t).map f) (i := i) (h := hm) 0]
  simp

private theorem foldSelectedXor_lt {α : Type}
    (t : Nat) (xs : List α)
    (selected : α → Bool) (value : α → Nat) :
    (∀ a ∈ xs, value a < 2 ^ t) →
    ∀ z : Nat, z < 2 ^ t →
      xs.foldl
        (fun acc a =>
          if selected a then Nat.xor acc (value a) else acc) z
        < 2 ^ t := by
  induction xs with
  | nil =>
      intro h z hz
      simpa using hz
  | cons a xs ih =>
      intro h z hz
      simp only [List.foldl_cons]
      apply ih
      · intro b hb
        exact h b (by simp [hb])
      · cases hs : selected a with
        | false => simpa [hs] using hz
        | true =>
            simpa [hs] using
              (Nat.xor_lt_two_pow hz (h a (by simp)))

theorem rowsId_wf (t : Nat) : RowsWF t (rowsId t) := by
  constructor
  · simp [rowsId]
  · intro i hi
    change ((List.range t).map (fun j => 2 ^ j)).getD i 0 <
      2 ^ t
    rw [range_map_getD t i (fun j => 2 ^ j) hi]
    exact Nat.pow_lt_pow_of_lt (by decide : 1 < (2 : Nat)) hi

theorem feedbackMask_lt (t : Nat) (taps : Nat → Bool) :
    feedbackMask t taps < 2 ^ t := by
  unfold feedbackMask
  exact foldSelectedXor_lt t (List.range t) taps
    (fun j => 2 ^ j)
    (by
      intro j hj
      exact Nat.pow_lt_pow_of_lt
        (by decide : 1 < (2 : Nat)) (List.mem_range.mp hj))
    0 (Nat.two_pow_pos t)

theorem recRows_wf (t : Nat) (taps : Nat → Bool) :
    RowsWF t (recRows t taps) := by
  constructor
  · simp [recRows]
  · intro i hi
    change ((List.range t).map
      (fun j =>
        if j + 1 < t then 2 ^ (j + 1)
        else feedbackMask t taps)).getD i 0 < 2 ^ t
    rw [range_map_getD t i _ hi]
    by_cases h : i + 1 < t
    · simp only [if_pos h]
      exact Nat.pow_lt_pow_of_lt
        (by decide : 1 < (2 : Nat)) h
    · simpa [h] using feedbackMask_lt t taps

theorem rowsXor_wf (t : Nat) (A B : List Nat)
    (hA : RowsWF t A) (hB : RowsWF t B) :
    RowsWF t (rowsXor t A B) := by
  constructor
  · simp [rowsXor]
  · intro i hi
    change ((List.range t).map
      (fun j => Nat.xor (A.getD j 0) (B.getD j 0))).getD i 0 <
      2 ^ t
    rw [range_map_getD t i _ hi]
    exact Nat.xor_lt_two_pow (hA.2 i hi) (hB.2 i hi)

theorem rowsMul_wf (t : Nat) (A B : List Nat)
    (_hA : RowsWF t A) (hB : RowsWF t B) :
    RowsWF t (rowsMul t A B) := by
  constructor
  · simp [rowsMul]
  · intro i hi
    change ((List.range t).map
      (fun r =>
        (List.range t).foldl
          (fun acc j =>
            if Nat.testBit (A.getD r 0) j
            then Nat.xor acc (B.getD j 0) else acc) 0)).getD i 0
      < 2 ^ t
    rw [range_map_getD t i _ hi]
    exact foldSelectedXor_lt t (List.range t)
      (fun j => Nat.testBit (A.getD i 0) j)
      (fun j => B.getD j 0)
      (by
        intro j hj
        exact hB.2 j (List.mem_range.mp hj))
      0 (Nat.two_pow_pos t)

private theorem rowsPowAux_wf (t : Nat) :
    ∀ fuel exponent (base acc : List Nat),
      RowsWF t base → RowsWF t acc →
      RowsWF t (rowsPowAux t fuel exponent base acc) := by
  intro fuel
  induction fuel with
  | zero =>
      intro exponent base acc hb ha
      simpa [rowsPowAux] using ha
  | succ fuel ih =>
      intro exponent base acc hb ha
      cases he : (exponent == 0) with
      | true =>
          simpa [rowsPowAux, he] using ha
      | false =>
          have hs : RowsWF t (rowsMul t base base) :=
            rowsMul_wf t base base hb hb
          have hc : RowsWF t
              (if exponent % 2 == 1
               then rowsMul t acc base else acc) := by
            cases hp : (exponent % 2 == 1) with
            | true =>
                simpa [hp] using
                  (rowsMul_wf t acc base ha hb)
            | false =>
                simpa [hp] using ha
          simpa [rowsPowAux, he] using
            (ih (exponent / 2) (rowsMul t base base)
              (if exponent % 2 == 1
               then rowsMul t acc base else acc) hs hc)

theorem rowsPowFast_wf (t : Nat) (A : List Nat) (k : Nat)
    (hA : RowsWF t A) :
    RowsWF t (rowsPowFast t A k) := by
  exact rowsPowAux_wf t (k + 1) k A (rowsId t)
    hA (rowsId_wf t)

/-! ## Finite Boolean XOR folds -/

/-- A truly constant Fin.foldl, needed in the zero branch of foldPick. -/
private theorem fold_id :
    ∀ (t : Nat) (b : Bool),
      Fin.foldl t (fun x _ => x) b = b := by
  intro t
  induction t with
  | zero =>
      intro b
      rfl
  | succ t ih =>
      intro b
      simpa only [Fin.foldl_succ] using ih b

private theorem foldFalse :
    ∀ (t : Nat) (b : Bool),
      Fin.foldl t (fun acc _ => acc ^^ false) b = b := by
  intro t
  induction t with
  | zero =>
      intro b
      rfl
  | succ t ih =>
      intro b
      simpa [Fin.foldl_succ, Bool.xor_false] using ih b

private theorem foldPick :
    ∀ (t : Nat) (u : Fin t → Bool) (i : Fin t),
      Fin.foldl t
        (fun acc j => acc ^^ ((decide (i.val = j.val)) && u j))
        false = u i := by
  intro t
  induction t with
  | zero =>
      intro u i
      exact i.elim0
  | succ t ih =>
      intro u i
      cases i using Fin.cases with
      | zero =>
          simpa [Fin.foldl_succ] using fold_id t (u 0)
      | succ j =>
          simpa [Fin.foldl_succ, Bool.false_xor] using
            (ih (fun k : Fin t => u k.succ) j)

/-- The parentheses on the RHS are essential: this is a Bool equality,
not a decide-equation (equality binds more tightly than Bool XOR). -/
private theorem foldXorAdd :
    ∀ (t : Nat) (f g : Fin t → Bool) (a b : Bool),
      Fin.foldl t
        (fun z j => z ^^ (f j ^^ g j)) (a ^^ b) =
        ((Fin.foldl t (fun z j => z ^^ f j) a) ^^
         (Fin.foldl t (fun z j => z ^^ g j) b)) := by
  intro t
  induction t with
  | zero =>
      intro f g a b
      rfl
  | succ t ih =>
      intro f g a b
      simp only [Fin.foldl_succ]
      have hstart :
          ((a ^^ b) ^^ (f 0 ^^ g 0)) =
          ((a ^^ f 0) ^^ (b ^^ g 0)) := by
        cases a <;> cases b <;>
          cases f 0 <;> cases g 0 <;> decide
      rw [hstart]
      exact ih (fun j : Fin t => f j.succ)
        (fun j : Fin t => g j.succ)
        (a ^^ f 0) (b ^^ g 0)

/-! ## A scalar GF(2) dot product and its algebra -/

private def dot (t : Nat) (row : Nat) (u : Fin t → Bool) : Bool :=
  Fin.foldl t (fun acc j => acc ^^ (row.testBit j.val && u j)) false

private theorem dot_zero (t : Nat) (u : Fin t → Bool) :
    dot t 0 u = false := by
  unfold dot
  simp only [Nat.zero_testBit, Bool.false_and, Bool.xor_false]
  exact fold_id t false

private theorem dot_two_pow (t : Nat) (u : Fin t → Bool)
    (i : Fin t) :
    dot t (2 ^ i.val) u = u i := by
  unfold dot
  simp only [Nat.testBit_two_pow]
  exact foldPick t u i

private theorem dot_xor (t : Nat) (a b : Nat)
    (u : Fin t → Bool) :
    dot t (Nat.xor a b) u = ((dot t a u) ^^ (dot t b u)) := by
  rw [show Nat.xor a b = a ^^^ b from rfl]
  unfold dot
  simp only [Nat.testBit_xor]
  simp only [Bool.and_xor_distrib_right]
  simpa only [Bool.false_xor] using
    (foldXorAdd t
      (fun j => a.testBit j.val && u j)
      (fun j => b.testBit j.val && u j)
      false false)

/-- Applying dot after a selected XOR of rows is the corresponding
selected XOR of dot values. This also handles unbounded source masks. -/
private theorem dotFoldXor (t : Nat) (xs : List Nat)
    (selected : Nat → Bool) (value : Nat → Nat)
    (u : Fin t → Bool) :
    ∀ z : Nat,
      dot t
        (xs.foldl
          (fun acc j => if selected j then Nat.xor acc (value j) else acc)
          z) u =
      xs.foldl
        (fun acc j => acc ^^ (selected j && dot t (value j) u))
        (dot t z u) := by
  induction xs with
  | nil =>
      intro z
      rfl
  | cons j xs ih =>
      intro z
      cases hj : selected j with
      | false =>
          simpa [List.foldl_cons, hj] using ih z
      | true =>
          have h := ih (Nat.xor z (value j))
          rw [dot_xor t z (value j) u] at h
          simpa [List.foldl_cons, hj] using h

/-- Explicit List.range/Fin.foldl bridge, proved from the leading-element
recurrences, rather than assuming a Fin/list-fold correspondence. -/
private theorem rangePrimeFold {α : Type} (n : Nat) :
    ∀ (start : Nat) (f : α → Nat → α) (a : α),
      (List.range' start n).foldl f a =
        Fin.foldl n (fun z i => f z (start + i.val)) a := by
  induction n with
  | zero =>
      intro start f a
      rfl
  | succ n ih =>
      intro start f a
      rw [List.range'_succ, List.foldl_cons, Fin.foldl_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (start + 1) f (f a start))

private theorem rangeFoldFin {α : Type} (n : Nat)
    (f : α → Nat → α) (a : α) :
    (List.range n).foldl f a =
      Fin.foldl n (fun z i => f z i.val) a := by
  rw [List.range_eq_range']
  simpa only [Nat.zero_add] using rangePrimeFold n 0 f a

/-! ## Matrix identity, sum, and product -/

theorem rowsApply_id (t : Nat) (u : Fin t → Bool) :
    rowsApply t (rowsId t) u = u := by
  funext i
  change dot t ((rowsId t).getD i.val 0) u = u i
  rw [show rowsId t = (List.range t).map (fun j => 2 ^ j) from rfl]
  rw [range_map_getD t i.val (fun j => 2 ^ j) i.isLt]
  exact dot_two_pow t u i

theorem rowsApply_xor (t : Nat) (A B : List Nat)
    (u : Fin t → Bool) :
    rowsApply t (rowsXor t A B) u =
      (fun i =>
        ((rowsApply t A u) i) ^^ ((rowsApply t B u) i)) := by
  funext i
  change dot t ((rowsXor t A B).getD i.val 0) u =
    ((dot t (A.getD i.val 0) u) ^^ (dot t (B.getD i.val 0) u))
  rw [show rowsXor t A B =
      (List.range t).map (fun j => Nat.xor (A.getD j 0) (B.getD j 0)) from rfl]
  rw [range_map_getD t i.val
    (fun j => Nat.xor (A.getD j 0) (B.getD j 0)) i.isLt]
  exact dot_xor t (A.getD i.val 0) (B.getD i.val 0) u

/-- Composition holds for arbitrary row lists. Only the first t bits of
each row are read; malformed extra rows or high bits have no effect. -/
private theorem rowsApply_mul_any (t : Nat) (A B : List Nat)
    (u : Fin t → Bool) :
    rowsApply t (rowsMul t A B) u =
      rowsApply t A (rowsApply t B u) := by
  funext i
  change dot t ((rowsMul t A B).getD i.val 0) u =
    dot t (A.getD i.val 0) (rowsApply t B u)
  change dot t
      (((List.range t).map (fun r =>
        (List.range t).foldl
          (fun acc j =>
            if Nat.testBit (A.getD r 0) j
            then Nat.xor acc (B.getD j 0) else acc) 0)).getD i.val 0) u =
    dot t (A.getD i.val 0) (rowsApply t B u)
  rw [range_map_getD t i.val _ i.isLt]
  rw [dotFoldXor t (List.range t)
    (fun j => Nat.testBit (A.getD i.val 0) j)
    (fun j => B.getD j 0) u 0]
  rw [dot_zero]
  rw [rangeFoldFin]
  rfl

/-- The requested RowsWF-qualified multiplication law. -/
theorem rowsApply_mul (t : Nat) (A B : List Nat)
    (_hA : RowsWF t A) (_hB : RowsWF t B)
    (u : Fin t → Bool) :
    rowsApply t (rowsMul t A B) u =
      rowsApply t A (rowsApply t B u) :=
  rowsApply_mul_any t A B u

/-- The feedback mask is exactly the GF(2) dot product of taps and u. -/
private theorem feedbackMask_dot (t : Nat) (taps : Nat → Bool)
    (u : Fin t → Bool) :
    dot t (feedbackMask t taps) u =
      Fin.foldl t
        (fun acc j => acc ^^ (taps j.val && u j)) false := by
  change dot t
      ((List.range t).foldl
        (fun acc j => if taps j then Nat.xor acc (2 ^ j) else acc) 0) u =
    Fin.foldl t (fun acc j => acc ^^ (taps j.val && u j)) false
  rw [dotFoldXor t (List.range t) taps (fun j => 2 ^ j) u 0]
  rw [dot_zero]
  rw [rangeFoldFin]
  simpa only [dot_two_pow]

/-- Literal companion-matrix semantics for all widths, including t = 0. -/
theorem recStep_rowsApply (t : Nat) (taps : Nat → Bool)
    (u : Fin t → Bool) :
    recStep t taps u = rowsApply t (recRows t taps) u := by
  funext i
  change
    (if h : i.val + 1 < t then u ⟨i.val + 1, h⟩
     else Fin.foldl t
       (fun acc j => Bool.xor acc (Bool.and (taps j.val) (u j)))
       false) =
    dot t ((recRows t taps).getD i.val 0) u
  change
    (if h : i.val + 1 < t then u ⟨i.val + 1, h⟩
     else Fin.foldl t
       (fun acc j => Bool.xor acc (Bool.and (taps j.val) (u j)))
       false) =
    dot t
      (((List.range t).map
        (fun j => if j + 1 < t then 2 ^ (j + 1)
                  else feedbackMask t taps)).getD i.val 0) u
  rw [range_map_getD t i.val _ i.isLt]
  by_cases h : i.val + 1 < t
  · simp only [dif_pos h, if_pos h]
    exact (dot_two_pow t u ⟨i.val + 1, h⟩).symm
  · simp only [dif_neg h, if_neg h]
    exact (feedbackMask_dot t taps u).symm

/-! ## Squaring semantics, including the finite fuel cutoff -/

/-- Local forward iterator, equivalent pointwise to recIter when f = recStep.
It is kept under a distinct name to avoid colliding with PeriodLemma.iterate. -/
def tapMatrixIterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (tapMatrixIterate f k x)

private theorem tapMatrixIterate_double {α : Type}
    (f : α → α) (k : Nat) (x : α) :
    tapMatrixIterate f (2 * k) x =
      tapMatrixIterate (fun y => f (f y)) k x := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      have he : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [he]
      change
        f (f (tapMatrixIterate f (2 * k) x)) =
        f (f (tapMatrixIterate (fun y => f (f y)) k x))
      rw [ih]

private theorem tapMatrixIterate_even {α : Type}
    (f : α → α) (exponent : Nat) (x : α)
    (he : exponent % 2 = 0) :
    tapMatrixIterate f exponent x =
      tapMatrixIterate (fun y => f (f y)) (exponent / 2) x := by
  have hn : exponent = 2 * (exponent / 2) := by omega
  calc
    tapMatrixIterate f exponent x =
        tapMatrixIterate f (2 * (exponent / 2)) x :=
      congrArg (fun j => tapMatrixIterate f j x) hn
    _ = tapMatrixIterate (fun y => f (f y)) (exponent / 2) x :=
      tapMatrixIterate_double f (exponent / 2) x

private theorem tapMatrixIterate_odd {α : Type}
    (f : α → α) (exponent : Nat) (x : α)
    (ho : exponent % 2 = 1) :
    tapMatrixIterate f exponent x =
      f (tapMatrixIterate (fun y => f (f y)) (exponent / 2) x) := by
  have hn : exponent = 2 * (exponent / 2) + 1 := by omega
  calc
    tapMatrixIterate f exponent x =
        tapMatrixIterate f (2 * (exponent / 2) + 1) x :=
      congrArg (fun j => tapMatrixIterate f j x) hn
    _ = f (tapMatrixIterate f (2 * (exponent / 2)) x) := rfl
    _ = f (tapMatrixIterate (fun y => f (f y)) (exponent / 2) x) := by
      rw [tapMatrixIterate_double]

/-- The complete semantic loop invariant for rowsPowAux.
The fuel may be any number at least the exponent; this conservative
bound suffices because every nonzero iteration replaces exponent by
exponent / 2. No matrix well-formedness is required by rowsApply. -/
theorem rowsPowAux_apply (t : Nat) :
    ∀ fuel exponent (base acc : List Nat) (u : Fin t → Bool),
      exponent ≤ fuel →
      rowsApply t (rowsPowAux t fuel exponent base acc) u =
        rowsApply t acc
          (tapMatrixIterate (rowsApply t base) exponent u) := by
  intro fuel
  induction fuel with
  | zero =>
      intro exponent base acc u h
      have hz : exponent = 0 := by omega
      subst exponent
      rfl
  | succ fuel ih =>
      intro exponent base acc u h
      by_cases he : exponent = 0
      · subst exponent
        simp [rowsPowAux, tapMatrixIterate]
      · have hrec :
            rowsPowAux t (fuel + 1) exponent base acc =
              rowsPowAux t fuel (exponent / 2)
                (rowsMul t base base)
                (if exponent % 2 == 1 then rowsMul t acc base else acc) := by
          simp [rowsPowAux, he]
        have hd : exponent / 2 ≤ fuel := by omega
        rw [hrec]
        rw [ih (exponent / 2) (rowsMul t base base)
          (if exponent % 2 == 1 then rowsMul t acc base else acc)
          u hd]
        have hf :
            rowsApply t (rowsMul t base base) =
              (fun v => rowsApply t base (rowsApply t base v)) := by
          funext v
          exact rowsApply_mul_any t base base v
        rw [hf]
        by_cases ho : exponent % 2 = 1
        · calc
            rowsApply t
                (if exponent % 2 == 1 then rowsMul t acc base else acc)
                (tapMatrixIterate
                  (fun v => rowsApply t base (rowsApply t base v))
                  (exponent / 2) u) =
                rowsApply t (rowsMul t acc base)
                  (tapMatrixIterate
                    (fun v => rowsApply t base (rowsApply t base v))
                    (exponent / 2) u) := by simp [ho]
            _ = rowsApply t acc
                  (rowsApply t base
                    (tapMatrixIterate
                      (fun v => rowsApply t base (rowsApply t base v))
                      (exponent / 2) u)) :=
                rowsApply_mul_any t acc base _
            _ = rowsApply t acc
                  (tapMatrixIterate (rowsApply t base) exponent u) := by
                rw [tapMatrixIterate_odd (rowsApply t base) exponent u ho]
        · have hz : exponent % 2 = 0 := by
            have hm : exponent % 2 < 2 :=
              Nat.mod_lt _ (by decide : 0 < (2 : Nat))
            omega
          calc
            rowsApply t
                (if exponent % 2 == 1 then rowsMul t acc base else acc)
                (tapMatrixIterate
                  (fun v => rowsApply t base (rowsApply t base v))
                  (exponent / 2) u) =
                rowsApply t acc
                  (tapMatrixIterate
                    (fun v => rowsApply t base (rowsApply t base v))
                    (exponent / 2) u) := by simp [ho]
            _ = rowsApply t acc
                  (tapMatrixIterate (rowsApply t base) exponent u) := by
                rw [tapMatrixIterate_even (rowsApply t base) exponent u hz]

/-- Fast binary matrix power acts as the corresponding ordinary k-fold
application, for every t, A, k, and Boolean vector u. -/
theorem rowsPowFast_apply (t : Nat) (A : List Nat)
    (k : Nat) (u : Fin t → Bool) :
    rowsApply t (rowsPowFast t A k) u =
      tapMatrixIterate (rowsApply t A) k u := by
  have h := rowsPowAux_apply t (k + 1) k A (rowsId t) u (by omega)
  simpa only [rowsPowFast, rowsApply_id] using h

/-- Recurrence k-fold iteration is exactly fast companion-matrix powering.
No orbit enumeration or primitivity assumption is involved. -/
theorem recIter_rowsPowFast (t : Nat) (taps : Nat → Bool)
    (k : Nat) (u : Fin t → Bool) :
    recIter t taps k u =
      rowsApply t (rowsPowFast t (recRows t taps) k) u := by
  have hfun :
      recStep t taps = rowsApply t (recRows t taps) := by
    funext v
    exact recStep_rowsApply t taps v
  have hit :
      recIter t taps k u =
        tapMatrixIterate (recStep t taps) k u := by
    induction k with
    | zero =>
        rfl
    | succ k ih =>
        change recStep t taps (recIter t taps k u) =
          recStep t taps (tapMatrixIterate (recStep t taps) k u)
        rw [ih]
  calc
    recIter t taps k u =
        tapMatrixIterate (recStep t taps) k u := hit
    _ = tapMatrixIterate (rowsApply t (recRows t taps)) k u := by
      rw [hfun]
    _ = rowsApply t (rowsPowFast t (recRows t taps) k) u :=
      (rowsPowFast_apply t (recRows t taps) k u).symm

/-- The existing TapCert.matrixIter is the semantic recIter. -/
theorem matrixIter_eq_recIter (t : Nat) (taps : Nat → Bool)
    (k : Nat) (u : Fin t → Bool) :
    matrixIter t taps k u = recIter t taps k u := by
  exact (recIter_rowsPowFast t taps k u).symm

/-! ## Nat-mask wrappers (no change to TapCert.rowsApply) -/

def rowsApplyCode (t : Nat) (A : List Nat) (x : Nat) : Nat :=
  vcode t (rowsApply t A (vdecode t x))

theorem rowsApplyCode_lt (t : Nat) (A : List Nat) (x : Nat) :
    rowsApplyCode t A x < 2 ^ t :=
  vcode_lt t (rowsApply t A (vdecode t x))

theorem rowsApplyCode_id (t : Nat) (x : Nat)
    (hx : x < 2 ^ t) :
    rowsApplyCode t (rowsId t) x = x := by
  unfold rowsApplyCode
  rw [rowsApply_id]
  exact vcode_vdecode t x hx

theorem rowsApplyCode_xor (t : Nat) (A B : List Nat)
    (x : Nat) :
    rowsApplyCode t (rowsXor t A B) x =
      ((rowsApplyCode t A x) ^^^ (rowsApplyCode t B x)) := by
  unfold rowsApplyCode
  rw [rowsApply_xor]
  exact vcode_xor t
    (rowsApply t A (vdecode t x))
    (rowsApply t B (vdecode t x))

/-- Orientation sanity checks, now accompanied by general theorems. -/
theorem companion_t2_example :
    vcode 2 (recStep 2 (fun j => j == 0) (vdecode 2 1)) = 2 := by
  decide

theorem matrix_t2_example :
    rowsApplyCode 2 (recRows 2 (fun j => j == 0)) 1 = 2 := by
  decide

end L3
