import Lean

namespace L4.ReportDigitArithmetic

def compareCode (a b : Nat) : Nat :=
  if a < b then 1 else if b < a then 2 else 0

def cmp (a b prior : Nat) : Nat :=
  if a < b then 1 else if b < a then 2 else prior

def digit (beta j x : Nat) : Nat := (x / beta^j) % beta

def cmpFold (beta r x : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => cmp (digit beta j x) (digit beta j r) (cmpFold beta r x j)

private theorem radix_lt {p a b c d : Nat} (A : a<p) (C : c<p) :
    a+p*b < c+p*d ↔ b<d ∨ (b=d ∧ a<c) := by
  rcases Nat.lt_trichotomy b d with H|H|H
  · have M := Nat.mul_le_mul_left p (show b+1 ≤ d by omega)
    rw [Nat.mul_add, Nat.mul_one] at M
    have F : a+p*b < c+p*d := by omega
    simp [F,H]
  · subst d
    simp
  · have M := Nat.mul_le_mul_left p (show d+1 ≤ b by omega)
    rw [Nat.mul_add, Nat.mul_one] at M
    have F : ¬ a+p*b < c+p*d := by omega
    simp [F,show ¬ b<d by omega,show ¬ b=d by omega]

theorem split_prefix (beta x j : Nat) :
    x % beta^(j+1) = x % beta^j + beta^j * digit beta j x := by
  rw [Nat.pow_succ, Nat.mod_mul, digit]

theorem cmp_prefix (beta r x j : Nat) (B : 2≤beta) :
    cmpFold beta r x j = compareCode (x%beta^j) (r%beta^j) := by
  induction j with
  | zero => simp [cmpFold,compareCode,Nat.mod_one]
  | succ j IH =>
    rw [cmpFold, IH, split_prefix beta x j, split_prefix beta r j]
    have P : 0 < beta^j := Nat.pow_pos (by omega)
    unfold cmp compareCode
    simp only [radix_lt (Nat.mod_lt _ P) (Nat.mod_lt _ P)]
    repeat (first | split | omega)

def updateDist (r : Nat) (a : Bool) (x : Nat) : Nat :=
  if a then 0 else min r (x+1)

def nextDigit (beta r x : Nat) (a : Bool) (c j carry : Nat) : Nat × Nat :=
  if a then (0,carry)
  else if c ≠ 1 then (digit beta j r,carry)
  else ((digit beta j x + carry)%beta,(digit beta j x + carry)/beta)

structure Prefix where
  value : Nat
  outCmp : Nat
  carry : Nat

def readWriteFold (beta r x : Nat) (a : Bool) (c : Nat) : Nat → Prefix
  | 0 => ⟨0,0,1⟩
  | j+1 =>
    let z := readWriteFold beta r x a c j
    let (v,k) := nextDigit beta r x a c j z.carry
    ⟨z.value + beta^j*v, cmp v (digit beta j r) z.outCmp,k⟩

private theorem div_succ (x p : Nat) (P : 0<p) :
    (x+1)/p = x/p + (x%p+1)/p := by
  have H : x+1 = x%p+1+p*(x/p) := by
    have := Nat.mod_add_div x p
    omega
  rw [H, Nat.add_mul_div_left _ _ P, Nat.add_comm]

private theorem increment_step (beta x j : Nat) (B : 2≤beta) :
    let carry := (x%beta^j+1)/beta^j
    (digit beta j x + carry)%beta = digit beta j (x+1) ∧
    (digit beta j x + carry)/beta = (x%beta^(j+1)+1)/beta^(j+1) := by
  dsimp
  have P : 0 < beta^j := Nat.pow_pos (by omega)
  unfold digit
  rw [div_succ x _ P, Nat.mod_add_mod]
  constructor
  · rfl
  · rw [split_prefix, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    simp only [digit]
    rw [show x%beta^j+beta^j*(x/beta^j%beta)+1 =
        x%beta^j+1+beta^j*(x/beta^j%beta) by omega,
      Nat.add_mul_div_left _ _ P, Nat.add_comm ((x%beta^j+1)/beta^j)]

theorem emitted_prefix (beta r x : Nat) (a : Bool) (j : Nat) (B : 2≤beta) :
    let c := compareCode x r
    let s := readWriteFold beta r x a c j
    let y := updateDist r a x
    s.value = y%beta^j ∧
    s.outCmp = compareCode (y%beta^j) (r%beta^j) ∧
    (a=false → x<r → s.carry = (x%beta^j+1)/beta^j) := by
  dsimp
  induction j with
  | zero => simp [readWriteFold, compareCode, Nat.mod_one]
  | succ j IH =>
    let c := compareCode x r
    let s := readWriteFold beta r x a c j
    let y := updateDist r a x
    change s.value = y%beta^j ∧ s.outCmp = compareCode (y%beta^j) (r%beta^j) ∧
      (a=false → x<r → s.carry = (x%beta^j+1)/beta^j) at IH
    have DC : (nextDigit beta r x a c j s.carry).1 = digit beta j y ∧
        (a=false → x<r →
          (nextDigit beta r x a c j s.carry).2 = (x%beta^(j+1)+1)/beta^(j+1)) := by
      cases E : a with
      | true => simp [nextDigit, y, updateDist, E, digit]
      | false =>
        by_cases H : x<r
        · have R : x+1≤r := by omega
          have C : c=1 := by simp [c,compareCode,H]
          have K := IH.2.2 E H
          simp only [nextDigit,E,Bool.false_eq_true,if_false,C,ne_eq, not_true_eq_false,
            y,updateDist,Nat.min_eq_right R,K]
          exact ⟨(increment_step beta x j B).1,
            fun _ _ => (increment_step beta x j B).2⟩
        · have R : r≤x+1 := by omega
          have C : c≠1 := by unfold c compareCode; rw [if_neg H]; split <;> decide
          simp [nextDigit,E,C,y,updateDist,Nat.min_eq_left R,H]
    rw [readWriteFold]
    change s.value + beta^j * (nextDigit beta r x a c j s.carry).1 = y % beta^(j+1) ∧
      cmp (nextDigit beta r x a c j s.carry).1 (digit beta j r) s.outCmp =
        compareCode (y%beta^(j+1)) (r%beta^(j+1)) ∧ _
    rw [IH.1, IH.2.1, DC.1]
    exact ⟨(split_prefix beta y j).symm, by
      rw [← cmp_prefix beta r y j B, ← cmp_prefix beta r y (j+1) B]; rfl, DC.2⟩

theorem threshold_step (r j x : Nat) (a : Bool) (J : 1≤j) (R : j≤r) :
    updateDist r a x < j ↔ (a=true ∨ (1<j ∧ x<j-1)) := by
  cases a <;> simp [updateDist] <;> omega

theorem carry_bit (beta x j : Nat) (B : 2≤beta) :
    (x%beta^j+1)/beta^j ≤ 1 := by
  have P : 0 < beta^j := Nat.pow_pos (by omega)
  exact Nat.div_le_of_le_mul (by have := Nat.mod_lt x P; omega)

theorem emitted_complete (beta t r x : Nat) (a : Bool) (B : 2≤beta)
    (R : r<beta^t) :
    let y := updateDist r a x
    let s := readWriteFold beta r x a (compareCode x r) t
    s.value = y ∧ (s.outCmp=1 ↔ y<r) := by
  let y := updateDist r a x
  let s := readWriteFold beta r x a (compareCode x r) t
  have Y : y<beta^t := by
    cases a with
    | true => simpa [y,updateDist] using (Nat.pow_pos (by omega) : 0 < beta^t)
    | false =>
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) R
  have H := emitted_prefix beta r x a t B
  change s.value = y%beta^t ∧ s.outCmp = compareCode (y%beta^t) (r%beta^t) ∧ _ at H
  rw [Nat.mod_eq_of_lt Y,Nat.mod_eq_of_lt R] at H
  refine ⟨H.1, ?_⟩
  change s.outCmp=1 ↔ y<r
  rw [H.2.1]
  unfold compareCode
  by_cases C : y<r
  · simp [C]
  · by_cases D : r<y <;> simp [C,D]

theorem full_cmp (beta t r x : Nat) (B : 2≤beta) (X : x<beta^t) (R : r<beta^t) :
    cmpFold beta r x t = compareCode x r := by
  rw [cmp_prefix beta r x t B,Nat.mod_eq_of_lt X,Nat.mod_eq_of_lt R]

/-- Same positional sum as the selected report word, with any supplied digit file. -/
def word (beta : Nat) (f : Nat → Nat) (t : Nat) : Nat :=
  ((List.range t).map (fun j => f j * beta^j)).sum

theorem word_succ (beta : Nat) (f : Nat → Nat) (j : Nat) :
    word beta f (j+1) = word beta f j + beta^j*f j := by
  simp [word,List.range_succ,List.sum_append,Nat.mul_comm]

theorem word_lt (beta : Nat) (f : Nat → Nat) (t : Nat)
    (H : ∀ j, j<t → f j < beta) : word beta f t < beta^t := by
  induction t with
  | zero => simp [word]
  | succ t IH =>
    have L : word beta f t < beta^t := IH (fun j J => H j (by omega))
    have M := Nat.mul_le_mul_left (beta^t) (show f t+1 ≤ beta by
      have := H t (by omega)
      omega)
    rw [word_succ,Nat.pow_succ]
    rw [Nat.mul_add,Nat.mul_one] at M
    omega

theorem word_mod_prefix (beta : Nat) (f : Nat → Nat) (t k : Nat) (K : k≤t) :
    word beta f t % beta^k = word beta f k % beta^k := by
  induction t with
  | zero => have : k=0 := by omega
            subst k
            rfl
  | succ t IH =>
    by_cases E : k=t+1
    · subst k; rfl
    have K' : k≤t := by omega
    rw [word_succ]
    obtain ⟨q,Q⟩ := Nat.pow_dvd_pow beta K'
    rw [Q,Nat.mul_assoc,Nat.add_mul_mod_self_left,IH K']

theorem word_digit (beta : Nat) (f : Nat → Nat) (t j : Nat) (J : j<t)
    (B : 2≤beta) (H : ∀ k, k<t → f k<beta) :
    digit beta j (word beta f t) = f j := by
  have P : 0 < beta^j := Nat.pow_pos (by omega)
  have W : word beta f j < beta^j := word_lt beta f j (fun k K => H k (by omega))
  have L : word beta f (j+1) < beta^(j+1) := word_lt beta f (j+1) (fun k K => H k (by omega))
  have M := word_mod_prefix beta f t (j+1) (by omega)
  rw [Nat.mod_eq_of_lt L,split_prefix,word_succ] at M
  have MD : word beta f t % beta^j = word beta f j := by
    rw [word_mod_prefix beta f t j (by omega),Nat.mod_eq_of_lt W]
  rw [MD] at M
  exact Nat.eq_of_mul_eq_mul_left P (by omega)

theorem word_of_digits (beta x t : Nat) :
    word beta (fun j => digit beta j x) t = x % beta^t := by
  induction t with
  | zero => simp [word,Nat.mod_one]
  | succ t IH => rw [word_succ,IH,split_prefix]

#print axioms word_lt
#print axioms word_digit
#print axioms word_of_digits
#print axioms full_cmp
#print axioms emitted_complete
#print axioms carry_bit
#print axioms cmp_prefix
#print axioms emitted_prefix
#print axioms threshold_step
end L4.ReportDigitArithmetic
