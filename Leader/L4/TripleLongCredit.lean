import Leader.L4.TripleRenewal
import Leader.L4.TripleLongRace

/-! G6 long attempt: exact common-denominator credits for a
predictable two-label race, and finite-word first-terminal failure. -/
namespace L4.TripleLongCredit
open Classical TaggedTail RankRenewal

/-- Number of binary words with first quota finished first by the
horizon. The suffix after a winner merely pads the numerator. -/
def quotaCredit : Nat → Nat → Nat → Nat
  | h, 0, _ => 2^h
  | _, _+1, 0 => 0
  | 0, _+1, _+1 => 0
  | h+1, i+1, j+1 => quotaCredit h i (j+1)+quotaCredit h (i+1) j

theorem credit_le (H i j : Nat) : quotaCredit H i j≤2^H := by
  induction H generalizing i j with
  | zero => cases i <;> cases j <;> simp [quotaCredit]
  | succ H ih =>
    cases i <;> cases j <;> simp only [quotaCredit]
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.zero_le _
    · rw [Nat.pow_succ,Nat.mul_two]
      exact Nat.add_le_add (ih _ _) (ih _ _)

/-- Improvement of either quota can only improve the first candidate's
binary score, even before its terminal horizon. -/
theorem credit_mono (H : Nat) {i j i' j' : Nat} (hi : i'≤i) (hj : j≤j') :
    quotaCredit H i j≤quotaCredit H i' j' := by
  induction H generalizing i j i' j' with
  | zero =>
    cases i <;> cases i' <;> cases j <;> cases j' <;> simp_all [quotaCredit] <;> omega
  | succ H ih =>
    cases i with
    | zero =>
      have he : i'=0 := by omega
      simp [quotaCredit,he]
    | succ i =>
      cases i' with
      | zero => exact credit_le _ _ _
      | succ i' =>
        cases j with
        | zero => exact Nat.zero_le _
        | succ j =>
          cases j' with
          | zero => omega
          | succ j' =>
            simp only [quotaCredit]
            exact Nat.add_le_add (ih (by omega) (by omega)) (ih (by omega) (by omega))

/-- Padding one additional binary mark doubles a score after enough
marks to decide this race. -/
theorem credit_pad (H i j : Nat) (hb : i+j≤H) :
    quotaCredit (H+1) i j=2*quotaCredit H i j := by
  induction H generalizing i j with
  | zero =>
    have hi : i=0 := by omega
    subst i
    simp [quotaCredit]
  | succ H ih =>
    cases i with
    | zero => simp [quotaCredit,Nat.pow_succ']
    | succ i =>
      cases j with
      | zero => simp [quotaCredit]
      | succ j =>
        simp only [quotaCredit]
        rw [ih i (j+1) (by omega),ih (i+1) j (by omega),Nat.mul_add]

/-- The same common horizon can be used for both children. -/
theorem credit_average (H i j : Nat) (hb : i+j+2≤H) :
    2*quotaCredit H (i+1) (j+1)=
      quotaCredit H i (j+1)+quotaCredit H (i+1) j := by
  cases H with
  | zero => omega
  | succ H =>
    rw [credit_pad H i (j+1) (by omega),credit_pad H (i+1) j (by omega)]
    simp only [quotaCredit,Nat.mul_add]

/-- Exchanging the two positive-total contestants complements the
decided credit. No 0/0 race is assigned a symmetry claim. -/
theorem credit_complement (H i j : Nat) (hpos : 0<i+j) (hb : i+j≤H) :
    quotaCredit H i j+quotaCredit H j i=2^H := by
  induction H generalizing i j with
  | zero => omega
  | succ H ih =>
    cases i with
    | zero =>
      have hj : j≠0 := by omega
      cases j <;> simp_all [quotaCredit]
    | succ i =>
      cases j with
      | zero => simp [quotaCredit]
      | succ j =>
        simp only [quotaCredit]
        have h₁ := ih i (j+1) (by omega) (by omega)
        have h₂ := ih (i+1) j (by omega) (by omega)
        rw [Nat.pow_succ,Nat.mul_two]
        omega

theorem credit_half (H : Nat) {i j : Nat} (hi : 0<i) (hle : i≤j) (hb : i+j≤H) :
    2^H≤2*quotaCredit H i j := by
  have hf := credit_complement H i i (by omega) (by omega)
  have h := credit_mono H (Nat.le_refl i) hle
  omega

/-- If the favored contestant needs at most one extra hit, force its
first competing label and then use the fair-or-better race. -/
theorem credit_quarter (H : Nat) {i j : Nat} (hi : 0<i) (hj : 0<j)
    (hle : i≤j+1) (hb : i+j≤H) :
    2^H≤4*quotaCredit H i j := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have hA := credit_average H i j (by omega)
  have hh : 2^H≤2*quotaCredit H i (j+1) := by
    by_cases hz : i=0
    · simp [hz,quotaCredit]; omega
    · exact credit_half H (by omega) (by omega) (by omega)
  change 2^H≤4*quotaCredit H (i+1) (j+1)
  omega

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f=f 0+sumEdge (fun i : Fin n => f i.succ) := by simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i,f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih fun i => h i.succ)

private theorem sScale {n : Nat} (k : Nat) (f : Fin n → Nat) :
    sumEdge (fun i => k*f i)=k*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

/-- Use either two-label event or race at a raw node. The third branch
contains all other labels. Actual extra successes may only increase the
continuation credit required here. -/
theorem raw_two_children {n : Nat} (a b : Fin n) (hne : a≠b)
    (W L R : Nat) (f : Fin n → Nat) (balance : 2*W≤L+R)
    (lower : ∀ e, (if e=a then L else if e=b then R else W)≤f e) :
    n*W≤sumEdge f := by
  have hn : 2≤n := by
    by_cases h : 2≤n
    · exact h
    · exact (hne (Fin.ext (by omega))).elim
  have hm := sMono lower
  rw [TripleLongRace.two_labels a b hne] at hm
  have he : n*W=(n-2)*W+2*W := by
    have h : n=n-2+2 := by omega
    calc
      _ = (n-2+2)*W := congrArg (fun k => k*W) h
      _ = _ := Nat.add_mul ..
  omega

/-- Centered credit of a predictable quota race. Either explicitly
nominated children have their decremented credit or better; every
other mark retains credit or improves it. -/
theorem raw_quota_children {n : Nat} (a b : Fin n) (hne : a≠b)
    (H i j k : Nat) (hb : i+j+2≤H) (f : Fin n → Nat)
    (lower : ∀ e, k*(if e=a then quotaCredit H i (j+1)
      else if e=b then quotaCredit H (i+1) j else quotaCredit H (i+1) (j+1))≤f e) :
    n*(k*quotaCredit H (i+1) (j+1))≤sumEdge f := by
  apply raw_two_children a b hne _ (k*quotaCredit H i (j+1)) (k*quotaCredit H (i+1) j) f
  · have hh := congrArg (fun z => k*z) (credit_average H i j hb)
    rw [Nat.mul_add] at hh
    rw [←hh]
    exact Nat.le_of_eq (by ac_rfl)
  · intro e
    by_cases ha : e=a <;> by_cases hb' : e=b <;> simpa [ha,hb',hne,Ne.symm hne] using lower e

/-- Global finite-word accounting with first terminal decisions. At
unfinished leaves the remaining credit is kept; a terminal failure
has no credit. No tail or deadline is needed for this calculation. -/
theorem terminal_credit {α : Type} {n : Nat} (next : α → Fin n → α)
    (I done failure : α → Prop) (q : Nat) (score : α → Nat)
    (keep : ∀ x e,I x→I (next x e))
    (cap : ∀ x,I x→score x≤q)
    (zero : ∀ x,I x→done x→failure x→score x=0)
    (step : ∀ x,I x→¬done x→n*score x≤sumEdge (fun e => score (next x e)))
    (t : Nat) (x : α) (hx : I x) :
    q*TripleRenewal.terminalMass next done failure t x+score x*n^t≤q*n^t := by
  induction t generalizing x with
  | zero =>
    by_cases hd : done x <;> by_cases hf : failure x <;>
      simp [TripleRenewal.terminalMass,hd,hf,cap x hx,zero x hx]
  | succ t ih =>
    by_cases hd : done x
    · by_cases hf : failure x
      · simp [TripleRenewal.terminalMass,hd,hf,zero x hx hd hf]
      · simp [TripleRenewal.terminalMass,hd,hf,Nat.mul_le_mul_right _ (cap x hx)]
    · have h := sMono (g := fun _ : Fin n => q*n^t)
        (fun e => ih (next x e) (keep x e hx))
      simp only [sAdd,sScale,sConst] at h
      have hr := Nat.mul_le_mul_right (n^t) (step x hx hd)
      simp only [TripleRenewal.terminalMass,hd,if_false,Nat.pow_succ']
      rw [show score x*(n*n^t)=(n*score x)*n^t by ac_rfl]
      have hmul : sumEdge (fun e => score (next x e)*n^t)=
          (sumEdge (fun e => score (next x e)))*n^t := by
        simp only [Nat.mul_comm (_ : Nat) (n^t),sScale]
      rw [hmul] at h
      omega

/-- A 1/32 live reserve gives the exact mandated D=256 interface,
with the stronger right-hand side 248 maintained. -/
theorem failure_248 {α : Type} {n : Nat} (next : α → Fin n → α)
    (I done failure : α → Prop) (q : Nat) (hq : 0<q) (score : α → Nat)
    (keep : ∀ x e,I x→I (next x e))
    (cap : ∀ x,I x→score x≤q)
    (zero : ∀ x,I x→done x→failure x→score x=0)
    (step : ∀ x,I x→¬done x→n*score x≤sumEdge (fun e => score (next x e)))
    (t : Nat) (x : α) (hx : I x) (start : q≤32*score x) :
    256*TripleRenewal.terminalMass next done failure t x≤248*n^t := by
  let F := TripleRenewal.terminalMass next done failure t x
  have h := Nat.mul_le_mul_left 256 (terminal_credit next I done failure q score keep cap zero step t x hx)
  have he := Nat.mul_le_mul_right (n^t) (Nat.mul_le_mul_left 8 start)
  have eight : 8*(32*score x)=256*score x := (Nat.mul_assoc ..).symm
  rw [eight] at he
  apply Nat.le_of_mul_le_mul_left _ hq
  change _ ≤ q*(248*n^t)
  rw [show q*(256*F)=256*(q*F) by ac_rfl]
  rw [Nat.mul_add,←Nat.mul_assoc 256 (score x) (n^t)] at h
  have total : q*(248*n^t)+8*q*n^t=256*(q*n^t) := by
    calc
      _ = 248*(q*n^t)+8*(q*n^t) := by ac_rfl
      _ = (248+8)*(q*n^t) := (Nat.add_mul ..).symm
      _ = _ := rfl
  dsimp only [F]
  omega

end L4.TripleLongCredit

