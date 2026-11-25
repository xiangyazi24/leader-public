import Leader.L4.FastExp

/-! Theorem S: cut off the finite-word first-hit cost at a power-of-two
gain horizon, then integrate its remaining geometric tail exactly. -/
namespace L4.FastExpMean
open TaggedTail FastExp Classical

/-- One rate-sized block contracts the tail factor by at least a half. -/
theorem rate_pow_half (r : Nat) (hr : 0<r) : 2*(r-1)^r≤r^r := by
  have hr' : r-1+1=r := by omega
  have hb (t : Nat) : (r-1)*(r+t+1)≤r*(r+t) := by
    have a : (r-1)*(r+t+1)=(r-1)*(r+t)+(r-1) := by rw [Nat.mul_add,Nat.mul_one]
    have b : r*(r+t)=(r-1)*(r+t)+(r+t) := by
      calc
        _ = (r-1+1)*(r+t) := congrArg (fun z => z*(r+t)) hr'.symm
        _ = _ := by rw [Nat.add_mul,Nat.one_mul]
    omega
  have H (t : Nat) : (r-1)^t*(r+t)≤r^(t+1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      calc
        _ = (r-1)^t*((r-1)*(r+t+1)) := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ (r-1)^t*(r*(r+t)) := Nat.mul_le_mul_left _ (hb t)
        _ = r*((r-1)^t*(r+t)) := by ac_rfl
        _ ≤ r*r^(t+1) := Nat.mul_le_mul_left _ ih
        _ = _ := (show r^(t+1+1)=r*r^(t+1) from Nat.pow_succ').symm
  have ht := H r
  rw [show r+r=2*r by omega,Nat.pow_succ] at ht
  apply Nat.le_of_mul_le_mul_left _ hr
  calc
    _ = (r-1)^r*(2*r) := by ac_rfl
    _ ≤ r^r*r := ht
    _ = _ := Nat.mul_comm ..

/-- After r*c marks the gain is absorbed. This conclusion also holds
at c=0 (where the premise forces gain≤1) and at r=1. -/
theorem cutoff_factor {r gain c : Nat} (hr : 0<r) (hg : gain≤2^c) :
    gain*(r-1)^(r*c)≤r^(r*c) := by
  calc
    _ ≤ 2^c*(r-1)^(r*c) := Nat.mul_le_mul_right _ hg
    _ = (2*(r-1)^r)^c := by rw [Nat.mul_pow,←Nat.pow_mul]
    _ ≤ (r^r)^c := Nat.pow_le_pow_left (rate_pow_half r hr) _
    _ = _ := (Nat.pow_mul ..).symm

/-- Sharp geometric integration from the finite-word comparison.
The cutoff allowance is r*c and the remaining mean allowance is r,
instead of applying another doubled Markov block. -/
theorem mean_of_tail {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : α → Prop) (x : α) (r gain c : Nat) (hr : 0<r) (hg : gain≤2^c)
    (tail : ∀ t, r^t*survival next (fun y => ¬D y) t x≤gain*(n*(r-1))^t) :
    IIDExpectedHittingTimeAtMost next D x (r*(c+1)) := by
  let A := r*c
  let q := n*(r-1)
  have hh : r*n*1+r*q≤r*n*r := by
    have h : 1+(r-1)=r := by omega
    calc
      _ = (r*n)*(1+(r-1)) := by rw [Nat.mul_add,Nat.mul_one]; dsimp [q]; ac_rfl
      _ ≤ _ := by rw [h]; exact Nat.le_refl _
  have post (u : Nat) :
      r^u*survival next (fun y => ¬D y) (A+u) x≤1*n^A*q^u := by
    have ha : 0<r^A := Nat.pow_pos hr
    refine Nat.le_of_mul_le_mul_left ?_ ha
    calc
      _ = r^(A+u)*survival next (fun y => ¬D y) (A+u) x := by rw [Nat.pow_add,Nat.mul_assoc]
      _ ≤ gain*q^(A+u) := tail _
      _ = (gain*(r-1)^A)*(n^A*q^u) := by
        rw [Nat.pow_add,show q^A=n^A*(r-1)^A from Nat.mul_pow ..]
        ac_rfl
      _ ≤ r^A*(n^A*q^u) := Nat.mul_le_mul_right _ (cutoff_factor hr hg)
      _ = _ := by rw [Nat.one_mul]
  have h := expected_of_cutoff_tail next D x r q 1 A r hr hh post
  simpa only [A,Nat.mul_succ] using h

/-- Theorem S for the scaled terminal-one certificate. -/
theorem mean {α : Type} {n : Nat} {next : α → Fin n → α}
    {I D : α → Prop} {rate gain : Nat} (C : ExpCert next I D rate gain)
    (hn : 0<n) (keep : ∀ x e, I x → I (next x e))
    (c : Nat) (hg : gain≤2^c) (x : α) (hx : I x) :
    IIDExpectedHittingTimeAtMost next D x (rate*(c+1)) :=
  mean_of_tail next D x rate gain c C.ratePositive hg (fun t => FastExp.tail C hn keep t x hx)

/-- Same sharp integration for a family of closed certificate
targets, with the gains added rather than the means. -/
theorem union_mean {α : Type} {n K : Nat} {next : α → Fin n → α}
    {I : α → Prop} {D : Fin K → α → Prop} {rate : Nat} (hr : 0<rate)
    (gain : Fin K → Nat) (C : ∀ i, ExpCert next I (D i) rate (gain i))
    (hn : 0<n) (keep : ∀ x e, I x → I (next x e))
    (sticky : ∀ i x e, D i x → D i (next x e))
    (c : Nat) (hg : sumEdge gain≤2^c) (x : α) (hx : I x) :
    IIDExpectedHittingTimeAtMost next (fun y => ∀ i, D i y) x (rate*(c+1)) := by
  apply mean_of_tail next _ x rate (sumEdge gain) c hr hg
  intro t
  have eq : (fun y => ¬ ∀ i, D i y) = (fun y => ∃ i, ¬D i y) :=
    funext (fun _ => propext not_forall)
  rw [eq]
  exact FastExp.union_tail gain C hn keep sticky t x hx

end L4.FastExpMean

#print axioms L4.FastExpMean.cutoff_factor
#print axioms L4.FastExpMean.mean_of_tail
#print axioms L4.FastExpMean.mean
#print axioms L4.FastExpMean.union_mean
