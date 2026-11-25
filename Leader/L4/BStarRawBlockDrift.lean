import Leader.L4.Height.Trial

namespace L4.BStarRawBlockDrift
open L4.Height
open Classical

noncomputable def massInd {n : Nat} (A : List (Fin n) → Prop) (w : List (Fin n)) : Nat :=
  if A w then 1 else 0

/-- Exact finite drift on raw marks, conditional uniformly on their entire old prefix.
The event on a block can use every old state along that block. -/
theorem miss_bound {n : Nat} (D : List (Fin n) → Nat) (S : List (Fin n) → List (Fin n) → Prop)
    (B q : Nat)
    (mono : ∀ a b, D (a++b) ≤ D a)
    (spend : ∀ a b, b.length=B → S a b → 0<D a → D (a++b)+1≤D a)
    (service : ∀ a, 0<D a → n^B≤q*wordSum (massInd (S a)) B)
    (j extra : Nat) :
    j*wordSum (massInd (fun w=>0<D w)) (j*B+extra) ≤
      q*D []*n^(j*B+extra) := by
  let bad := massInd (fun w=>0<D w)
  have hb (a b : List (Fin n)) : bad (a++b) ≤ bad a := by
    by_cases h : 0<D a
    · simp only [bad,massInd,if_pos h]
      split <;> omega
    · have hz : ¬0<D (a++b) := by have := mono a b; omega
      simp [bad,massInd,h,hz]
  have loss (a : List (Fin n)) :
      q*wordSum (fun b=>D (a++b)) B + bad a*n^B ≤ q*D a*n^B := by
    by_cases h : 0<D a
    · have pt := wordSum_mono_on_length (fun b=>D (a++b)+massInd (S a) b)
        (fun _=>D a) B (fun b len=>by
          by_cases yes : S a b
          · simpa [massInd,yes] using spend a b len yes h
          · simpa [massInd,yes] using mono a b)
      rw [wordSum_add_fun,wordSum_const] at pt
      have scaled := Nat.mul_le_mul_left q pt
      rw [Nat.mul_add] at scaled
      have serviced := service a h
      simp only [bad,massInd,if_pos h,Nat.one_mul]
      rw [Nat.mul_comm (n^B) (D a),←Nat.mul_assoc] at scaled
      omega
    · have h' : D a = 0 := by omega
      have pt := wordSum_mono (fun b=>D (a++b)) (fun _=>D a) (mono a) B
      rw [wordSum_const,h',Nat.mul_zero] at pt
      have hz := Nat.eq_zero_of_le_zero pt
      simp [bad,massInd,h',hz]
  let f := fun (i : Nat) w=>q*D w+i*bad w
  have advance (i : Nat) (a : List (Fin n)) :
      wordSum (fun b=>f (i+1) (a++b)) B ≤ n^B*f i a := by
    have ht := wordSum_mono (fun b=>bad (a++b)) (fun _=>bad a) (hb a) B
    rw [wordSum_const] at ht
    have scaled := Nat.mul_le_mul_left (i+1) ht
    unfold f
    rw [wordSum_add_fun,wordSum_mul_left,wordSum_mul_left]
    apply Nat.le_trans (Nat.add_le_add_left scaled _)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_left_comm i]
    have L := loss a
    rw [Nat.mul_comm (bad a) (n^B)] at L
    calc
      q*wordSum (fun b=>D (a++b)) B + (n^B*(i*bad a) + n^B*bad a)
          = (q*wordSum (fun b=>D (a++b)) B + n^B*bad a) + n^B*(i*bad a) := by ac_rfl
      _ ≤ (q*D a*n^B)+n^B*(i*bad a) := Nat.add_le_add_right L _
      _ = n^B*(q*D a+i*bad a) := by rw [Nat.mul_add,Nat.mul_comm (q*D a)]
  have loop (i : Nat) : wordSum (f i) (i*B) ≤ q*D []*n^(i*B) := by
    induction i with
    | zero => simp [f,wordSum]
    | succ i ih =>
      rw [Nat.succ_mul,wordSum_add]
      apply Nat.le_trans (wordSum_mono _ _ (advance i) _)
      rw [wordSum_mul_left,Nat.pow_add]
      exact Nat.le_trans (Nat.mul_le_mul_left _ ih) (by apply Nat.le_of_eq; ac_rfl)
  have final : wordSum bad (j*B+extra) ≤ n^extra*wordSum bad (j*B) := by
    rw [wordSum_add]
    apply Nat.le_trans (wordSum_mono _ (fun a=>n^extra*bad a) (fun a=>by
      simpa only [wordSum_const] using
        wordSum_mono (fun b=>bad (a++b)) (fun _=>bad a) (hb a) extra) _)
    rw [wordSum_mul_left]
    exact Nat.le_refl _
  have J := loop j
  unfold f at J
  rw [wordSum_add_fun,wordSum_mul_left,wordSum_mul_left] at J
  have drop : j*wordSum bad (j*B) ≤ q*D []*n^(j*B) := by omega
  calc
    j*wordSum bad (j*B+extra) ≤ j*(n^extra*wordSum bad (j*B)) := Nat.mul_le_mul_left _ final
    _ = n^extra*(j*wordSum bad (j*B)) := by ac_rfl
    _ ≤ n^extra*(q*D []*n^(j*B)) := Nat.mul_le_mul_left _ drop
    _ = q*D []*n^(j*B+extra) := by rw [Nat.pow_add]; ac_rfl

end L4.BStarRawBlockDrift
