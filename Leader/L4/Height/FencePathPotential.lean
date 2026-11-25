import Leader.L4.Height.Window

/-! Finite integer potential for parallel paths served by the same alphabet. -/
namespace L4.Height.FencePathPotential

abbrev total {n : Nat} (f : Fin n → Nat) := (List.ofFn f).sum

private theorem component_le_total {n : Nat} (f : Fin n → Nat) (e : Fin n) : f e ≤ total f := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    rw [total, List.ofFn_succ, List.sum_cons]
    refine Fin.cases (by omega) (fun j => ?_) e
    exact Nat.le_trans (ih (fun i => f i.succ) j) (Nat.le_add_left _ _)

def weight (debt : Nat) : Nat := if debt=0 then 0 else 2^debt

def mass {S : Type} (paths : List (S → Nat)) (y : S) :=
  (paths.map (fun p => weight (p y))).sum

private theorem weight_le {a b : Nat} (h : a ≤ b) : weight a ≤ weight b := by
  by_cases ha : a=0
  · simp [weight,ha]
  · have hb : b≠0 := by omega
    simpa [weight,ha,hb] using Nat.pow_le_pow_right (n:=2) (by decide) h

private theorem weight_halves {a b : Nat} (h : a < b) : 2*weight a ≤ weight b := by
  have hb : b≠0 := by omega
  by_cases ha : a=0
  · simp [weight,ha]
  · have z := Nat.pow_le_pow_right (n:=2) (by decide) (show a+1≤b by omega)
    simpa [weight,ha,hb,Nat.pow_succ,Nat.mul_comm] using z

theorem mass_step {S : Type} {n : Nat} (paths : List (S → Nat)) (y : S) (z : Fin n → S)
    (weak : ∀ p ∈ paths, ∀ e, p (z e) ≤ p y)
    (strict : ∀ p ∈ paths, 0 < p y → ∃ e, p (z e) < p y) :
    (∀ e, mass paths (z e) ≤ mass paths y) ∧
    mass paths y ≤ 2 * total (fun e => mass paths y - mass paths (z e)) := by
  induction paths with
  | nil => simp [mass]
  | cons p ps ih =>
    have hp (e : Fin n) := weight_le (weak p List.mem_cons_self e)
    obtain ⟨wm,dm⟩ := ih (fun q h => weak q (List.mem_cons_of_mem _ h))
      (fun q h => strict q (List.mem_cons_of_mem _ h))
    have dp : weight (p y) ≤ 2 * total (fun e => weight (p y) - weight (p (z e))) := by
      by_cases hy : 0 < p y
      · obtain ⟨e,h⟩ := strict p List.mem_cons_self hy
        have hstep := weight_halves h
        have hsum := component_le_total (fun e => weight (p y) - weight (p (z e))) e
        omega
      · simp [weight,show p y = 0 by omega]
    have M (v : S) : mass (p::ps) v = weight (p v) + mass ps v := rfl
    refine ⟨fun e => by rw [M,M]; exact Nat.add_le_add (hp e) (wm e), ?_⟩
    have diff (e : Fin n) : mass (p::ps) y - mass (p::ps) (z e) =
        (weight (p y) - weight (p (z e))) + (mass ps y - mass ps (z e)) := by
      rw [M,M]
      have := hp e
      have := wm e
      omega
    simp only [diff,total,sum_ofFn_add] at dm dp ⊢
    rw [M]
    omega

def band (n k m : Nat) := min (8*n) (8*n*m / 2^k)

def reserve (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | b+1,m => reserve n b m + band n b m

theorem reserve_cap (n b m : Nat) : reserve n b m ≤ b*(8*n) := by
  induction b with
  | zero => simp [reserve]
  | succ b ih =>
    rw [reserve,Nat.succ_mul]
    exact Nat.add_le_add ih (Nat.min_le_left _ _)

private theorem band_mono (n k : Nat) {m t : Nat} (h : m ≤ t) : band n k m ≤ band n k t := by
  have d := Nat.div_le_div_right (c:=2^k) (Nat.mul_le_mul_left (8*n) h)
  unfold band
  omega

private theorem reserve_mono (n : Nat) {m t : Nat} (h : m ≤ t) (b : Nat) :
    reserve n b m ≤ reserve n b t := by
  induction b with
  | zero => exact Nat.le_refl _
  | succ b ih => exact Nat.add_le_add ih (band_mono n b h)

private theorem band_within {n k m : Nat} (h : m ≤ 2^k) :
    band n k m = 8*n*m / 2^k := by
  unfold band
  apply Nat.min_eq_right
  exact Nat.le_trans (Nat.div_le_div_right (c:=2^k) (Nat.mul_le_mul_left (8*n) h))
    (Nat.le_of_eq (Nat.mul_div_cancel _ (Nat.two_pow_pos k)))

private theorem band_drift {n k m : Nat} (z : Fin n → Nat) (pos : 0 < m)
    (lo : m ≤ 2^k) (hi : 2^k ≤ 2*m) (weak : ∀ e, z e ≤ m)
    (progress : m ≤ 2 * total (fun e => m - z e)) :
    n + total (fun e => band n k (z e)) ≤ n * band n k m := by
  let K := 2^k
  let cost := 8*n
  let dec (e : Fin n) := band n k m - band n k (z e)
  have child (e : Fin n) : cost * (m - z e) ≤ K * (dec e + 1) := by
    have a := Nat.lt_mul_div_succ (cost*m) (Nat.two_pow_pos k)
    have b := Nat.div_mul_le_self (cost*z e) K
    have D := Nat.div_le_div_right (c:=K) (Nat.mul_le_mul_left cost (weak e))
    have hsplit : K*((cost*m/K - cost*z e/K)+1) + K*(cost*z e/K) =
        K*(cost*m/K+1) := by
      rw [←Nat.mul_add]
      congr 1
      omega
    have splitEq : cost*(m-z e) + cost*z e = cost*m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (weak e)]
    change cost * (m-z e) ≤ K*(band n k m - band n k (z e) + 1)
    rw [band_within lo,band_within (Nat.le_trans (weak e) lo)]
    change cost*(m-z e) ≤ K*((cost*m/K - cost*z e/K)+1)
    change cost*m < K*(cost*m/K+1) at a
    rw [Nat.mul_comm (cost*z e/K) K] at b
    omega
  have S := sum_ofFn_le _ _ child
  rw [sum_ofFn_mul_left,sum_ofFn_mul_left,sum_ofFn_add,sum_ofFn_const] at S
  have cap := Nat.mul_le_mul_right (total dec+n) hi
  have hcharge : (2*m)*(2*n) ≤ (2*m)*(total dec+n) := by
    calc
      _ = (4*n)*m := by
        calc
          _ = (2*2)*(n*m) := by ac_rfl
          _ = _ := by simp [Nat.mul_assoc]
      _ ≤ (4*n)*(2*total (fun e => m-z e)) := Nat.mul_le_mul_left _ progress
      _ = cost*total (fun e => m-z e) := by
        dsimp only [cost]
        calc
          _ = (4*2)*n*total (fun e => m-z e) := by ac_rfl
          _ = _ := rfl
      _ ≤ K*(total dec+n) := by simpa [total] using S
      _ ≤ _ := cap
  have dif := Nat.le_of_mul_le_mul_left hcharge (show 0 < 2*m from Nat.mul_pos (by decide) pos)
  have cancel := sum_ofFn_eq (fun e => dec e + band n k (z e)) (fun _ : Fin n => band n k m)
    (fun e => Nat.sub_add_cancel (band_mono n k (weak e)))
  rw [sum_ofFn_add,sum_ofFn_const] at cancel
  change total dec + total (fun e => band n k (z e)) = n * band n k m at cancel
  omega

private theorem band_paid {n m k b : Nat} (z : Fin n → Nat) (weak : ∀ e, z e ≤ m)
    (hit : k < b) (good : n + total (fun e => band n k (z e)) ≤ n * band n k m) :
    n + total (fun e => reserve n b (z e)) ≤ n * reserve n b m := by
  induction b with
  | zero => omega
  | succ b ih =>
    have sumRes : total (fun e => reserve n b (z e)) ≤ n*reserve n b m := by
      simpa [total,sum_ofFn_const] using sum_ofFn_le _ _ (fun e => reserve_mono n (weak e) b)
    have sumBand : total (fun e => band n b (z e)) ≤ n*band n b m := by
      simpa [total,sum_ofFn_const] using sum_ofFn_le _ _ (fun e => band_mono n b (weak e))
    change n + (List.ofFn (fun e => reserve n b (z e) + band n b (z e))).sum ≤
      n * (reserve n b m + band n b m)
    rw [sum_ofFn_add,Nat.mul_add]
    by_cases eq : k=b
    · subst k
      unfold total at good sumRes
      omega
    · have pay := ih (by omega)
      unfold total at pay sumBand
      omega

theorem reserve_drift {n b m : Nat} (z : Fin n → Nat) (pos : 0<m)
    (extra : m < 2^(b-1)) (weak : ∀ e, z e ≤ m)
    (progress : m ≤ 2 * total (fun e => m-z e)) :
    n + total (fun e => reserve n b (z e)) ≤ n * reserve n b m := by
  have log := (Nat.log2_lt (Nat.ne_of_gt pos)).2 extra
  have top := Nat.lt_log2_self (n:=m)
  have low := Nat.log2_self_le (Nat.ne_of_gt pos)
  apply band_paid z weak (show m.log2+1 < b by omega)
  apply band_drift z pos (Nat.le_of_lt top) _ weak progress
  rw [Nat.pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 low

#print axioms reserve_drift
end L4.Height.FencePathPotential
