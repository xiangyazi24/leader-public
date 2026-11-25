import Leader.L4.TripleRenewal

namespace L4.AdaptiveDoorCredit
open TaggedTail TripleRenewal
open Classical

private theorem sum_succ {m : Nat} (f : Fin (m+1) → Nat) :
    sumEdge f = f 0+sumEdge (fun i : Fin m => f i.succ) := by simp [sumEdge,List.ofFn_succ]

private theorem sum_const (m a : Nat) : sumEdge (fun _ : Fin m => a)=m*a := by
  induction m with
  | zero => simp [sumEdge]
  | succ m ih => rw [sum_succ,ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_add {m : Nat} (f g : Fin m → Nat) :
    sumEdge (fun i=>f i+g i)=sumEdge f+sumEdge g := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sum_succ,sum_succ f,sum_succ g,ih]; omega

private theorem sum_single {m : Nat} (e : Fin m) (a : Nat) : sumEdge (fun i => if i=e then a else 0)=a := by
  induction m with
  | zero => exact Fin.elim0 e
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) e
    · rw [sum_succ]
      simp [show (fun i : Fin m => if i.succ=(0 : Fin (m+1)) then a else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sum_const]
    · rw [sum_succ,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    rw [sum_succ,sum_succ]
    exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e) = a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ,sum_succ f,ih,Nat.mul_add]

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
      simp only [sum_add,sScale,sum_const] at h
      have hr := Nat.mul_le_mul_right (n^t) (step x hx hd)
      simp only [TripleRenewal.terminalMass,hd,if_false,Nat.pow_succ']
      rw [show score x*(n*n^t)=(n*score x)*n^t by ac_rfl]
      have hmul : sumEdge (fun e => score (next x e)*n^t)=
          (sumEdge (fun e => score (next x e)))*n^t := by
        simp only [Nat.mul_comm (_ : Nat) (n^t),sScale]
      rw [hmul] at h
      omega

/-- One designated winner pays exactly for the two possible losses;
every other raw label maintains the current credit. -/
theorem triple_drift {n : Nat} (f : Fin n→Nat) (c : Nat) (win loss₁ loss₂ : Fin n)
    (A : win≠loss₁) (B : win≠loss₂) (C : loss₁≠loss₂)
    (paid : 3*c≤f win)
    (other : ∀ e,e≠win→e≠loss₁→e≠loss₂→c≤f e) :
    n*c≤sumEdge f := by
  let charge := fun i : Fin n=>if i=win then 2*c else 0
  let one := fun i : Fin n=>if i=loss₁ then c else 0
  let two := fun i : Fin n=>if i=loss₂ then c else 0
  have P : ∀ i, c+charge i≤f i+one i+two i := by
    intro i
    by_cases w : i=win
    · subst i; simp [charge,one,two,A,B]; omega
    by_cases l : i=loss₁
    · subst i; simp [charge,one,two,Ne.symm A,C]
    by_cases r : i=loss₂
    · subst i; simp [charge,one,two,Ne.symm B,Ne.symm C]
    · simpa [charge,one,two,w,l,r] using other i w l r
  have H := sMono P
  rw [sum_add,sum_const,sum_add _ two,sum_add _ one,
    show sumEdge charge=2*c from sum_single win _,
    show sumEdge one=c from sum_single loss₁ _,
    show sumEdge two=c from sum_single loss₂ _] at H
  omega

/-- At each actual old state, a race may nominate three labels or the
physical phase may instead preserve credit on every label. -/
def LocalLaw {α : Type} {n : Nat} (next : α → Fin n → α) (score : α → Nat) (x : α) : Prop :=
  (∀ e,score x≤score (next x e)) ∨
    ∃ win loss₁ loss₂ : Fin n, win≠loss₁ ∧ win≠loss₂ ∧ loss₁≠loss₂ ∧
      3*score x≤score (next x win) ∧
      ∀ e,e≠win→e≠loss₁→e≠loss₂→score x≤score (next x e)

/-- Six one-in-three races reserve one unit out of 729. Finite-horizon
terminal failure is bounded without independence or any completion
premise on the interleaved physical phases. -/
theorem six_race_failure {α : Type} {n : Nat} (next : α → Fin n → α)
    (I done failure : α → Prop) (score : α → Nat)
    (keep : ∀ x e,I x→I (next x e))
    (cap : ∀ x,I x→score x≤729)
    (zero : ∀ x,I x→done x→failure x→score x=0)
    (localLaw : ∀ x,I x→¬done x→LocalLaw next score x)
    (t : Nat) (x : α) (hx : I x) (positive : 0<score x) :
    729*terminalMass next done failure t x≤728*n^t := by
  have drift (y : α) (hy : I y) (live : ¬done y) :
      n*score y≤sumEdge (fun e=>score (next y e)) := by
    rcases localLaw y hy live with slow|⟨win,l₁,l₂,A,B,C,paid,other⟩
    · have H := sMono slow
      rwa [sum_const] at H
    · exact triple_drift _ _ win l₁ l₂ A B C paid other
  have E := terminal_credit next I done failure 729 score keep cap zero drift t x hx
  have H := Nat.mul_le_mul_right (n^t) (show 1≤score x from positive)
  rw [Nat.one_mul] at H
  have exactD : 729*n^t=728*n^t+n^t := by
    exact (Nat.add_mul 728 1 (n^t)).trans (by rw [Nat.one_mul])
  rw [exactD] at E
  omega

/-- A live stage records how many accepted races it still owes. -/
inductive Progress where
  | live (remaining : Nat)
  | success
  | failure

def score : Progress → Nat
  | .live k => 3^(6-k)
  | .success => 729
  | .failure => 0

theorem score_cap (p : Progress) : score p≤729 := by
  cases p with
  | live k =>
    exact Nat.pow_le_pow_right (by decide : 0<3) (Nat.sub_le 6 k)
  | success => exact Nat.le_refl _
  | failure => exact Nat.zero_le _

/-- Paying one race multiplies the reserve by exactly three, including
the last race when there need be no residual random choice. -/
theorem pay_one {k : Nat} (pos : 0<k) (bound : k≤6) :
    score (.live (k-1))=3*score (.live k) := by
  have E : 6-(k-1)=6-k+1 := by omega
  simp only [score,E,Nat.pow_succ,Nat.mul_comm]

theorem physical_progress {i j : Nat} (keep : j≤i) :
    score (.live i)≤score (.live j) :=
  Nat.pow_le_pow_right (by decide : 0<3) (by omega)

end L4.AdaptiveDoorCredit
