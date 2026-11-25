import Leader.L4.Height.Trial

namespace L4.ReportAdaptiveFibre
open Height

variable {X : Type} {n : Nat}

/-- Predictable relabeling driven by uniform letters; all states advance
on the actual relabeled letter, not on the hidden driver letter. -/
def mapWord (step : X→Fin n→X) (steer : X→Fin n→Fin n) :
    X→List (Fin n)→List (Fin n)
  | _, [] => []
  | x, e::tail => let a:=steer x e; a::mapWord step steer (step x a) tail

def fibre (steer : X→Fin n→Fin n) (x : X) (a : Fin n) : Nat :=
  (List.ofFn (fun e => if steer x e=a then 1 else 0)).sum

def weight (step : X→Fin n→X) (steer : X→Fin n→Fin n) :
    X→List (Fin n)→Nat
  | _, [] => 1
  | x, a::tail => fibre steer x a * weight step steer (step x a) tail

theorem sum_delta {m : Nat} (a : Fin m) (f : Fin m→Nat) :
    (List.ofFn (fun i => if a=i then f i else 0)).sum=f a := by
  induction m with
  | zero => exact Fin.elim0 a
  | succ m ih =>
    refine Fin.cases ?_ (fun b=>?_) a
    · rw [List.ofFn_succ,List.sum_cons]
      have H : (List.ofFn (fun i : Fin m =>
          if (0 : Fin (m+1))=i.succ then f i.succ else 0)).sum=0 := by
        rw [sum_ofFn_eq _ (fun _=>0) (fun i=>by simp [Ne.symm (Fin.succ_ne_zero i)]),sum_ofFn_const,Nat.mul_zero]
      simp [H]
    · rw [List.ofFn_succ,List.sum_cons]
      simp only [Fin.succ_ne_zero,if_false,Nat.zero_add,Fin.succ_inj]
      exact ih b (fun i => f i.succ)

theorem sum_swap {m k : Nat} (f : Fin m→Fin k→Nat) :
    (List.ofFn (fun i => (List.ofFn (f i)).sum)).sum =
      (List.ofFn (fun j => (List.ofFn (fun i=>f i j)).sum)).sum := by
  induction m with
  | zero => simp [sum_ofFn_const]
  | succ m ih =>
    rw [List.ofFn_succ,List.sum_cons,ih (fun i=>f i.succ)]
    symm
    calc
      _ = (List.ofFn (fun j=>f 0 j+(List.ofFn (fun i : Fin m=>f i.succ j)).sum)).sum :=
        sum_ofFn_eq _ _ (fun j=>by rw [List.ofFn_succ,List.sum_cons])
      _ = _ := sum_ofFn_add _ _

theorem sum_group (steer : X→Fin n→Fin n) (x : X) (f : Fin n→Nat) :
    (List.ofFn (fun e=>f (steer x e))).sum =
      (List.ofFn (fun a=>fibre steer x a*f a)).sum := by
  calc
    _ = (List.ofFn (fun e => (List.ofFn (fun a=>if steer x e=a then f a else 0)).sum)).sum :=
      sum_ofFn_eq _ _ (fun e=>(sum_delta (steer x e) f).symm)
    _ = (List.ofFn (fun a => (List.ofFn (fun e=>if steer x e=a then f a else 0)).sum)).sum :=
      sum_swap _
    _ = _ := by
      apply sum_ofFn_eq
      intro a
      unfold fibre
      rw [Nat.mul_comm,←sum_ofFn_mul_left]
      apply sum_ofFn_eq
      intro e
      split <;> simp_all

/-- Exact adaptive finite-word pushforward, as an identity for every payoff. -/
theorem wordSum_pushforward (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (B : Nat) (x : X) (pay : List (Fin n)→Nat) :
    wordSum (fun w=>pay (mapWord step steer x w)) B =
      wordSum (fun w=>weight step steer x w*pay w) B := by
  induction B generalizing x pay with
  | zero => simp [wordSum,mapWord,weight]
  | succ k ih =>
    rw [wordSum,wordSum]
    calc
      _ = (List.ofFn (fun a=>wordSum (fun w=>
          weight step steer (step x (steer x a)) w * pay (steer x a::w)) k)).sum := by
        apply sum_ofFn_eq
        intro a
        simp only [mapWord]
        exact ih (step x (steer x a)) (fun w=>pay (steer x a::w))
      _ = _ := by
        rw [sum_group steer x (fun a=>wordSum (fun w=>weight step steer (step x a) w * pay (a::w)) k)]
        apply sum_ofFn_eq
        intro a
        rw [←wordSum_mul_left]
        apply wordSum_congr_fun
        intro w
        simp only [weight,Nat.mul_assoc]

def choices (step : X→Fin n→X) (steer : X→Fin n→Fin n) :
    X→List (Fin n)→Nat
  | _, [] => 0
  | x,a::tail => (if fibre steer x a=2 then 1 else 0) + choices step steer (step x a) tail

/-- The likelihood is at most 2^N, even for impossible actual words. -/
theorem weight_le_pow (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (Q : X→Prop) (stay : ∀ x e, Q x → Q (step x e))
    (two : ∀ x e, Q x → fibre steer x e ≤ 2)
    (x : X) (G : Q x) (w : List (Fin n)) :
    weight step steer x w ≤ 2^choices step steer x w := by
  induction w generalizing x with
  | nil => exact Nat.le_refl _
  | cons a w ih =>
    have I := ih (step x a) (stay x a G)
    simp only [weight,choices,Nat.pow_add]
    apply Nat.mul_le_mul _ I
    have F := two x a G
    split <;> omega

/-- A qualifying successful driver set transfers back to ordinary words;
no conditioning or fresh resampling of their actual tape is involved. -/
theorem capped_transfer (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (Q : X→Prop) (stay : ∀ x e, Q x → Q (step x e))
    (two : ∀ x e, Q x → fibre steer x e ≤ 2)
    (x : X) (G : Q x) (B cap : Nat) (ok : List (Fin n)→Bool)
    (bound : ∀ w, w.length=B → ok w=true → choices step steer x w≤cap) :
    wordSum (fun w=>(ok (mapWord step steer x w)).toNat) B ≤
      2^cap * wordSum (fun w=>(ok w).toNat) B := by
  rw [wordSum_pushforward step steer B x (fun w=>(ok w).toNat),←wordSum_mul_left]
  apply wordSum_mono_on_length
  intro w W
  cases O : ok w with
  | false => simp
  | true =>
    simp only [Bool.toNat_true,Nat.mul_one]
    exact Nat.le_trans (weight_le_pow step steer Q stay two x G w)
      (Nat.pow_le_pow_right (by decide) (bound w W O))

#print axioms wordSum_pushforward
#print axioms weight_le_pow
#print axioms capped_transfer
end L4.ReportAdaptiveFibre
