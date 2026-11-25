import Leader.L4.ReportAdaptiveFibre

namespace L4.ReportAdaptiveFibre
open Height

variable {X : Type} {n : Nat}

def driverStep (step : X→Fin n→X) (steer : X→Fin n→Fin n) (x : X) (e : Fin n) : X :=
  step x (steer x e)

theorem map_length (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (x : X) (w : List (Fin n)) :
    (mapWord step steer x w).length=w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => simp [mapWord,ih]

theorem run_map (step : X→Fin n→X) (steer : X→Fin n→Fin n) (x : X) (w : List (Fin n)) :
    runWord step x (mapWord step steer x w)=runWord (driverStep step steer) x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (step x (steer x e))

/-- A reward supported on at most a specified original sum can receive
at most twice its original mass in the auxiliary law. -/
theorem one_reward (steer : X→Fin n→Fin n) (x : X) (R : Fin n→Nat)
    (two : ∀ a, fibre steer x a≤2) (K : Nat) (bound : (List.ofFn R).sum≤K) :
    (List.ofFn (fun e=>R (steer x e))).sum≤2*K := by
  rw [sum_group steer x R]
  exact Nat.le_trans (sum_ofFn_le _ _ (fun a=>Nat.mul_le_mul_right (R a) (two a)))
    (by rw [sum_ofFn_mul_left]; exact Nat.mul_le_mul_left 2 bound)

def reward (step : X→Fin n→X) (mark : X→Fin n→Nat) :
    X→List (Fin n)→Nat
  | _,[] => 0
  | x,e::w => mark x e + reward step mark (step x e) w

private theorem reward_driver (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (mark : X→Fin n→Nat) (x : X) (w : List (Fin n)) :
    reward step mark x (mapWord step steer x w)=
      reward (driverStep step steer) (fun x e=>mark x (steer x e)) x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    simp [reward,mapWord,driverStep,ih]

/-- Multiplying by n avoids a truncated exponent at horizon zero. -/
theorem total_reward {step : X→Fin n→X} (mark : X→Fin n→Nat)
    (Q : X→Prop) (stay : ∀ x e,Q x→Q (step x e))
    (K : Nat) (bound : ∀ x,Q x→(List.ofFn (mark x)).sum≤K)
    (H : Nat) (x : X) (G : Q x) :
    n * wordSum (reward step mark x) H ≤ K*H*n^H := by
  induction H generalizing x with
  | zero => simp [wordSum,reward]
  | succ h ih =>
    rw [wordSum,←sum_ofFn_mul_left]
    have S : (List.ofFn
        (fun e : Fin n => n * wordSum (fun w=>reward step mark x (e::w)) h)).sum ≤
        (List.ofFn (fun e=>n^h*(n*mark x e)+K*h*n^h)).sum := by
      apply sum_ofFn_le
      intro e
      change n*wordSum (fun w=>mark x e + reward step mark (step x e) w) h≤_
      rw [wordSum_add_fun,wordSum_const,Nat.mul_add]
      calc
        _ = n^h*(n*mark x e)+n*wordSum (reward step mark (step x e)) h := by ac_rfl
        _ ≤ _ := Nat.add_le_add_left (ih (step x e) (stay x e G)) _
    refine Nat.le_trans S ?_
    rw [sum_ofFn_add,sum_ofFn_mul_left,sum_ofFn_mul_left,sum_ofFn_const]
    calc
      _ ≤ n^h*(n*K)+n*(K*h*n^h) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (bound x G))) _
      _ = K*(h+1)*n^(h+1) := by rw [Nat.pow_succ,Nat.mul_add,Nat.mul_one,Nat.add_mul]; ac_rfl

/-- Combined old progress rewards for a list of owners. Overlapping
advances are added, not assumed independent or mutually exclusive. -/
theorem total_driver_reward (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (mark : X→Fin n→Nat) (Q : X→Prop) (stay : ∀ x e,Q x→Q (step x e))
    (two : ∀ x a,Q x → fibre steer x a≤2)
    (K : Nat) (bound : ∀ x,Q x→(List.ofFn (mark x)).sum≤K)
    (H : Nat) (x : X) (G : Q x) :
    n*wordSum (fun w=>reward step mark x (mapWord step steer x w)) H≤2*K*H*n^H := by
  rw [wordSum_congr_fun _ (reward (driverStep step steer) (fun x e=>mark x (steer x e)) x)
    _ (reward_driver step steer mark x)]
  exact total_reward _ Q (fun x e hx=>stay x (steer x e) hx)
    (2*K) (fun x hx=>one_reward steer x (mark x) (fun e=>two x e hx) K (bound x hx)) H x G

/-- Accumulate a pathwise spacing certificate, then count cap overflow
by Markov without a division by either the spacing or horizon. -/
theorem cap_overflow_count (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (mark : X→Fin n→Nat) (x : X) (H spacing start cap K : Nat)
    (sep : ∀ w, w.length=H →
      let u:=mapWord step steer x w
      spacing*choices step steer x u≤spacing*start+reward step mark x u)
    (progress : n*wordSum (fun w=>reward step mark x (mapWord step steer x w)) H≤K*H*n^H) :
    n*(spacing*(cap+1)) *
      wordSum (fun w=>if cap<choices step steer x (mapWord step steer x w) then 1 else 0) H
    ≤ (n*(spacing*start)+K*H)*n^H := by
  rw [←wordSum_mul_left]
  have S : wordSum (fun w=>n*(spacing*(cap+1)) *
      (if cap<choices step steer x (mapWord step steer x w) then 1 else 0)) H ≤
      wordSum (fun w=>n*(spacing*start+reward step mark x (mapWord step steer x w))) H := by
    apply wordSum_mono_on_length
    intro w W
    let u := mapWord step steer x w
    change n*(spacing*(cap+1))*(if cap<choices step steer x u then 1 else 0)≤_
    split
    · rename_i C
      rw [Nat.mul_one]
      exact Nat.mul_le_mul_left _
        (Nat.le_trans (Nat.mul_le_mul_left _ (by omega : cap+1≤choices step steer x u)) (sep w W))
    · simp
  refine Nat.le_trans S ?_
  rw [wordSum_mul_left,wordSum_add_fun,wordSum_const,Nat.mul_add]
  calc
    _ ≤ n*(n^H*(spacing*start))+K*H*n^H := Nat.add_le_add_left progress _
    _ = (n*(spacing*start)+K*H)*n^H := by rw [Nat.add_mul]; ac_rfl

/-- Specialized paper arithmetic: spacing 3tw, initial allowance 5,
tilted one-mark mass 20, and horizon 8192tw_upper n. -/
theorem paper_cap_quarter {t w W n : Nat}
    (T : 0<t) (wpos : 0<w) (N : 0<n) (R : W≤11*w)
    (B : List (Fin n)→Nat)
    (bound : n*(3*t*w*(2^22+1))*wordSum B (8192*t*W*n) ≤
        (n*(3*t*w*5)+20*(8192*t*W*n))*n^(8192*t*W*n)) :
    4*wordSum B (8192*t*W*n)≤n^(8192*t*W*n) := by
  let b := wordSum B (8192*t*W*n)
  let M := n^(8192*t*W*n)
  let f := n*(t*w)
  have F : 0<f := Nat.mul_pos N (Nat.mul_pos T wpos)
  have R1 : 20*(8192*t*W*n) ≤ f*(20*8192*11) := by
    calc
      _ = (20*8192*t*n)*W := by ac_rfl
      _ ≤ (20*8192*t*n)*(11*w) := Nat.mul_le_mul_left _ R
      _ = _ := by unfold f; ac_rfl
  have R2 : n*(3*t*w*5) = f*15 := by unfold f; change n*(3*t*w*5)=n*(t*w)*(3*5); ac_rfl
  have R3 : n*(3*t*w*(2^22+1))=f*(3*(2^22+1)) := by unfold f; ac_rfl
  rw [R2,R3] at bound
  have L : (3*(2^22+1))*b ≤ (15+20*8192*11)*M := by
    apply Nat.le_of_mul_le_mul_left _ F
    calc
      f*((3*(2^22+1))*b) = (f*(3*(2^22+1)))*b := by ac_rfl
      _ ≤ (f*15+20*(8192*t*W*n))*M := bound
      _ ≤ (f*15+f*(20*8192*11))*M := Nat.mul_le_mul_right _ (Nat.add_le_add_left R1 _)
      _ = _ := by rw [←Nat.mul_add,Nat.mul_assoc]
  omega

#print axioms one_reward
#print axioms total_driver_reward
#print axioms cap_overflow_count
#print axioms paper_cap_quarter
end L4.ReportAdaptiveFibre
