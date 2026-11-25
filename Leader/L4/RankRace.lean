import Leader.L4.RankRenewal
import Leader.L4.GGTiming

/-! Exact finite-word bounds for adaptive nominated-edge races. -/
namespace L4.RankRace
open TaggedTail RankRenewal

private theorem sum_succ {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sum_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    rw [sum_succ, sum_succ]
    exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

private theorem sum_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun i => f i+g i) = sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_succ,sum_succ f,sum_succ g,ih]; omega

private theorem sum_mul {n : Nat} (k : Nat) (f : Fin n → Nat) :
    sumEdge (fun i => k*f i) = k*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ,sum_succ f,ih,Nat.mul_add]

private theorem sum_single {n : Nat} (e : Fin n) (a : Nat) :
    sumEdge (fun i => if i=e then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) e
    · rw [sum_succ]
      simp [show (fun i : Fin n => if i.succ=(0 : Fin (n+1)) then a else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sum_const]
    · rw [sum_succ,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

private theorem endpoint_estimate {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (C : Nat) (hs : ∀ x, sumEdge (fun e => f (next x e)) ≤ C*f x)
    (t : Nat) (x : α) :
    endpointSum next f t x ≤ C^t*f x := by
  induction t generalizing x with
  | zero => simp [endpointSum]
  | succ t ih =>
    calc
      _ ≤ sumEdge (fun e => C^t*f (next x e)) := sum_mono (fun e => ih _)
      _ ≤ C^t*(C*f x) := by rw [sum_mul]; exact Nat.mul_le_mul_left _ (hs x)
      _ = _ := by rw [Nat.pow_succ,Nat.mul_assoc]

private theorem endpoint_le_scaled {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (K : Nat) (t : Nat) (x : α)
    (h : ∀ y, K*f y ≤ g y) :
    K*endpointSum next f t x ≤ endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h _
  | succ t ih =>
    simp only [endpointSum,←sum_mul]
    exact sum_mono (fun e => ih _)

/-- A mark selects at most one productive timer edge. For an ordered
payment clock use a total nomination, padding after completion. -/
def countStep {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α × Nat × Nat) (e : Fin n) :
    α × Nat × Nat :=
  if nom x.1 = some e then (next x.1 e,x.2.1+1,x.2.2)
  else (next x.1 e,x.2.1,x.2.2+1)

private theorem timer_weight {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α × Nat × Nat) :
    sumEdge (fun e =>
      let y := countStep next nom x e
      (5 : Nat)^y.2.1 * 4^y.2.2) ≤
    (4*n+1)*(5^x.2.1*4^x.2.2) := by
  let w := (5 : Nat)^x.2.1*4^x.2.2
  have h (e : Fin n) :
      (let y := countStep next nom x e; (5 : Nat)^y.2.1 * 4^y.2.2) =
        4*w + if nom x.1 = some e then w else 0 := by
    by_cases he : nom x.1 = some e
    · simp only [countStep,he,if_true,Nat.pow_succ]
      rw [show (5 : Nat)^x.2.1*5 = 5^x.2.1*4+5^x.2.1 from by omega]
      -- keep the base unchanged: factor only the terminal multiplicative 5
      change (5^x.2.1*4+5^x.2.1)*4^x.2.2 = 4*w+w
      rw [Nat.add_mul]
      dsimp [w]
      ac_rfl
    · simp only [countStep,he,if_false,Nat.pow_succ,Nat.add_zero]
      dsimp [w]
      ac_rfl
  simp only [h,sum_add,sum_const]
  have hh : sumEdge (fun e => if nom x.1 = some e then w else 0) ≤ w := by
    cases hm : nom x.1 with
    | none => simp [sum_const]
    | some i =>
      simpa only [hm,Option.some.injEq,eq_comm] using
        (show sumEdge (fun e => if e=i then w else 0) ≤ w from (by rw [sum_single]; exact Nat.le_refl _))
  have hm : (4*n+1)*w = n*(4*w)+w := by rw [Nat.add_mul,Nat.one_mul]; congr 1; ac_rfl
  change _ ≤ (4*n+1)*w
  omega

private theorem count_total {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α × Nat × Nat) (e : Fin n) :
    (countStep next nom x e).2.1+(countStep next nom x e).2.2 = x.2.1+x.2.2+1 := by
  unfold countStep
  split <;> simp <;> omega

private theorem endpoint_scoped {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (K : Nat) (level : α → Nat)
    (step : ∀ x e, level (next x e) = level x+1)
    (T : Nat) (h : ∀ x, level x=T → K*f x ≤ g x)
    (t : Nat) (x : α) (hx : level x+t=T) :
    K*endpointSum next f t x ≤ endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h _ (by omega)
  | succ t ih =>
    simp only [endpointSum,←sum_mul]
    exact sum_mono (fun e => ih _ (by rw [step]; omega))

/-- Number of fixed-length raw words having at least K productive
nominations. The one possible edge can depend on all previous marks. -/
noncomputable def timerMass {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α) (T K : Nat) : Nat :=
  endpointSum (countStep next nom) (fun y => if K≤y.2.1 then 1 else 0) T (x,0,0)

/-- A 5/4 exponential-moment estimate, with all denominators cleared. -/
theorem timer_moment {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α) (T K : Nat) :
    (5^K*4^(T-K))*timerMass next nom x T K ≤ (4*n+1)^T := by
  have h := endpoint_scoped (countStep next nom) (fun y => if K≤y.2.1 then 1 else 0)
    (fun y => 5^y.2.1*4^y.2.2) (5^K*4^(T-K)) (fun y => y.2.1+y.2.2)
    (count_total next nom) T (by
      intro y hy
      by_cases hh : K ≤ y.2.1
      · simp only [hh,if_true,Nat.mul_one]
        have h1 : y.2.1 = K+(y.2.1-K) := by omega
        have h2 : T-K = y.2.2+(y.2.1-K) := by omega
        have ha : 4^(y.2.1-K) ≤ 5^(y.2.1-K) := Nat.pow_le_pow_left (by decide) _
        rw [h2,Nat.pow_add]
        have hpow : 5^y.2.1 = 5^K*5^(y.2.1-K) := by
          exact (congrArg (fun a => (5 : Nat)^a) h1).trans (Nat.pow_add ..)
        calc
          _ = (5^K*4^y.2.2)*4^(y.2.1-K) := by ac_rfl
          _ ≤ (5^K*4^y.2.2)*5^(y.2.1-K) := Nat.mul_le_mul_left _ ha
          _ = _ := by rw [hpow]; ac_rfl
      · simp [hh]) T (x,0,0) (by simp)
  refine Nat.le_trans h ?_
  simpa using endpoint_estimate (countStep next nom) (fun y => 5^y.2.1*4^y.2.2)
    (4*n+1) (timer_weight next nom) T (x,0,0)

private theorem power_linear_upper (a k : Nat) (hk : k≤a) :
    (a+1)^k*(a-k) ≤ a^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := ih (by omega)
    let u := a-k
    have hu : 0 < u := by dsimp [u]; omega
    have hu' : u ≤ a+1 := by dsimp [u]; omega
    have he : a-(k+1)=u-1 := by dsimp [u]; omega
    have step : (a+1)*(u-1) ≤ a*u := by
      have hmul : (a+1)*(u-1)+(a+1) = a*u+u := by
        rw [← Nat.mul_succ,show (u-1).succ = u by omega,Nat.add_mul,Nat.one_mul]
      omega
    calc
      _ = (a+1)^k*((a+1)*(u-1)) := by rw [he,Nat.pow_succ,Nat.mul_assoc]
      _ ≤ (a+1)^k*(a*u) := Nat.mul_le_mul_left _ step
      _ = ((a+1)^k*u)*a := by ac_rfl
      _ ≤ a^(k+1)*a := Nat.mul_le_mul_right _ h
      _ = _ := (Nat.pow_succ ..).symm

private theorem timer_block (n : Nat) (hn : 0<n) :
    3*(4*n+1)^n ≤ 4*(4*n)^n := by
  have h := power_linear_upper (4*n) n (by omega)
  rw [show 4*n-n=3*n by omega,Nat.pow_succ] at h
  apply Nat.le_of_mul_le_mul_right _ hn
  exact (show (3*(4*n+1)^n)*n ≤ (4*(4*n)^n)*n by
    calc
      _ = (4*n+1)^n*(3*n) := by ac_rfl
      _ ≤ (4*n)^n*(4*n) := h
      _ = _ := by ac_rfl)

private theorem timer_coeff (c h : Nat) (hc : 12≤c) :
    16^h * 4096^(c*h) ≤ 5625^(c*h) := by
  have hbase : 2 * 4096^3 ≤ (5625 : Nat)^3 := by decide
  have hh := Nat.pow_le_pow_left hbase (4*h)
  rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul] at hh
  have hh' : 16^h * 4096^(12*h) ≤ 5625^(12*h) := by
    have hpow : (2 : Nat)^(4*h) = 16^h := by rw [Nat.pow_mul]
    rw [hpow,show 3*(4*h)=12*h by omega] at hh
    exact hh
  have hm : 12*h≤c*h := Nat.mul_le_mul_right h hc
  have he : c*h = 12*h + (c*h-12*h) := by omega
  have ha (a : Nat) : a^(c*h) = a^(12*h)*a^(c*h-12*h) :=
    (congrArg (fun e => a^e) he).trans (Nat.pow_add ..)
  rw [ha 4096,ha 5625,←Nat.mul_assoc]
  exact Nat.mul_le_mul hh' (Nat.pow_le_pow_left (by decide) _)

/-- Across 2*c*n*h marks, at most one nominated productive timer edge
per mark gives a tail of at most 16^(-h) for 4*c*h hits, when c≥12.
This is uniform over the nomination strategy and physical start. -/
theorem timer_gap_tail {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α) (c h : Nat) (hn : 2≤n) (hc : 12≤c) :
    16^h * timerMass next nom x (2*n*(c*h)) (4*(c*h)) ≤ n^(2*n*(c*h)) := by
  let m := c*h
  let T := 2*n*m
  let K := 4*m
  let Z := timerMass next nom x T K
  change 16^h*Z ≤ n^T
  have hKT : K≤T := by
    dsimp [K,T]
    exact Nat.mul_le_mul_right _ (by omega)
  have hBlock := Nat.pow_le_pow_left (timer_block n (by omega)) (2*m)
  rw [Nat.mul_pow,Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul,
    show n*(2*m)=T by dsimp [T]; ac_rfl] at hBlock
  have hM : (5^K*4^(T-K))*Z ≤ (4*n+1)^T := timer_moment next nom x T K
  have hQ := Nat.le_trans (Nat.mul_le_mul_left (3^(2*m)) hM) hBlock
  have ex (a b : Nat) : (a^b)^m = a^(b*m) := (Nat.pow_mul ..).symm
  have cLeft : 3^(2*m)*5^K = 5625^m := by
    dsimp [K]
    rw [←ex 3 2,←ex 5 4,←Nat.mul_pow]
  have cRight : 4^(2*m)*4^K = 4096^m := by
    dsimp [K]
    rw [←ex 4 2,←ex 4 4,←Nat.mul_pow]
  have hPower : 4^T = 4^K*4^(T-K) := by rw [←Nat.pow_add,show K+(T-K)=T by omega]
  have hCancel : 5625^m * Z ≤ 4096^m * n^T := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < 4^(T-K) from Nat.pow_pos (by decide))
    calc
      _ = 3^(2*m)*((5^K*4^(T-K))*Z) := by rw [←cLeft]; ac_rfl
      _ ≤ 4^(2*m)*(4*n)^T := hQ
      _ = _ := by
        rw [Nat.mul_pow,hPower,←cRight]
        ac_rfl
  apply Nat.le_of_mul_le_mul_left _ (show 0 < 4096^m from Nat.pow_pos (by decide))
  calc
    _ = (16^h*4096^m)*Z := by ac_rfl
    _ ≤ 5625^m*Z := Nat.mul_le_mul_right _ (timer_coeff c h hc)
    _ ≤ _ := hCancel

/-- Number of exact-length raw words with at most K hits of the
predictable payment edge. Its edge can change after every mark. -/
noncomputable def slowMass {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Fin n) (x : α) (T K : Nat) : Nat :=
  endpointSum (countStep next (fun y => some (nom y)))
    (fun y => if y.2.1≤K then 1 else 0) T (x,0,0)

private theorem slow_weight {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Fin n) (x : α × Nat × Nat) :
    sumEdge (fun e => (2:Nat)^(countStep next (fun y => some (nom y)) x e).2.2) ≤
      (2*n-1)*2^x.2.2 := by
  let w := (2:Nat)^x.2.2
  have hz : 0<n := (nom x.1).isLt |> Nat.zero_lt_of_lt
  have he (e : Fin n) :
      (2:Nat)^(countStep next (fun y => some (nom y)) x e).2.2+
        (if e=nom x.1 then w else 0) = 2*w := by
    by_cases h : e=nom x.1
    · simp [countStep,h,w,Nat.two_mul]
    · simp [countStep,h,Ne.symm h,Nat.pow_succ,w,Nat.mul_comm]
  have hh := congrArg sumEdge (funext he)
  rw [sum_add,sum_single,sum_const] at hh
  have hm : (2*n-1)*w+w = n*(2*w) := by
    rw [←Nat.succ_mul,show (2*n-1).succ=2*n by omega]; ac_rfl
  change _ ≤ (2*n-1)*w
  omega

/-- Exact lower-tail moment for an always nominated payment edge. -/
theorem slow_moment {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Fin n) (x : α) (T K : Nat) :
    2^(T-K)*slowMass next nom x T K ≤ (2*n-1)^T := by
  let f := countStep next (fun y => some (nom y))
  have h := endpoint_scoped f (fun y => if y.2.1≤K then 1 else 0)
    (fun y => 2^y.2.2) (2^(T-K)) (fun y => y.2.1+y.2.2)
    (count_total next _) T (by
      intro y hy
      by_cases hh : y.2.1≤K
      · simp only [hh,if_true,Nat.mul_one]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      · simp [hh]) T (x,0,0) (by simp)
  refine Nat.le_trans h ?_
  simpa [f] using endpoint_estimate f (fun y => 2^y.2.2)
    (2*n-1) (slow_weight next nom) T (x,0,0)

private theorem neighboring_power (d k : Nat) :
    d^(k+1) + (k+1)*d^k ≤ (d+1)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (k+1)*d^(k+1) = ((k+1)*d^k)*d := by rw [Nat.pow_succ,Nat.mul_assoc]
    calc
      _ = (d^(k+1)*d+d^(k+1))+(k+1)*d^(k+1) := by
        rw [Nat.pow_succ d (k+1),show k.succ+1=(k+1)+1 from rfl,Nat.add_mul,Nat.one_mul]
        ac_rfl
      _ ≤ (d^(k+1)*d+d^(k+1))+((k+1)*d^(k+1)+(k+1)*d^k) :=
        Nat.add_le_add_left (Nat.le_add_right ..) _
      _ = (d^(k+1)+(k+1)*d^k)*(d+1) := by
        rw [he]; simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]; ac_rfl
      _ ≤ (d+1)^(k+1)*(d+1) := Nat.mul_le_mul_right _ ih
      _ = _ := (Nat.pow_succ ..).symm

private theorem slow_block (n : Nat) (hn : 0<n) :
    2*(2*n-1)^(2*n) ≤ (2*n)^(2*n) := by
  let d := 2*n-1
  have hd : d+1=2*n := by dsimp [d]; omega
  have h := neighboring_power d d
  have hmono : d*d^d ≤ (d+1)*d^d := Nat.mul_le_mul_right _ (by omega)
  have h' : 2*d^(d+1) ≤ d^(d+1)+(d+1)*d^d := by
    rw [Nat.pow_succ,Nat.mul_comm (d^d) d]; omega
  exact hd ▸ Nat.le_trans h' h

/-- The chance of having no more than 2h successful ordered nominations
by 2*c*n*h marks is at most 16^(-h), even with predictable selection. -/
theorem slow_gap_tail {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Fin n) (x : α) (c h : Nat) (hn : 2≤n) (hc : 12≤c) :
    16^h * slowMass next nom x (2*n*(c*h)) (2*h) ≤ n^(2*n*(c*h)) := by
  let m := c*h
  let T := 2*n*m
  let Z := slowMass next nom x T (2*h)
  change 16^h*Z ≤ n^T
  have hT : 2*h ≤ T := by
    have hm : h ≤ m := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.le_trans (Nat.mul_le_mul_left _ hm) (Nat.mul_le_mul_right _ (by omega))
  have hm : 6*h≤m := Nat.mul_le_mul_right _ (by omega)
  have hBlock := Nat.pow_le_pow_left (slow_block n (by omega)) m
  rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul] at hBlock
  change 2^m*(2*n-1)^T ≤ (2*n)^T at hBlock
  have hM : 2^(T-2*h)*Z ≤ (2*n-1)^T := slow_moment next nom x T (2*h)
  have hQ := Nat.le_trans (Nat.mul_le_mul_left (2^m) hM) hBlock
  have hc' : 2^T * 16^h ≤ 2^m * 2^(T-2*h) := by
    rw [show (16:Nat)^h = 2^(4*h) from (Nat.pow_mul 2 4 h).symm,←Nat.pow_add,←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply Nat.le_of_mul_le_mul_left _ (show 0<2^T from Nat.pow_pos (by decide))
  calc
    _ = (2^T*16^h)*Z := by ac_rfl
    _ ≤ (2^m*2^(T-2*h))*Z := Nat.mul_le_mul_right _ hc'
    _ ≤ (2*n)^T := by rw [Nat.mul_assoc]; exact hQ
    _ = _ := Nat.mul_pow ..

/-- Sum contributions of distinct positive gap lengths, filling absent
lengths by zero. Use one slot per length, not one per monitored leader. -/
def gapSum (mass : Nat → Nat) (first : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => mass first + gapSum mass (first+1) k

private theorem geometric_gap_sum (M : Nat) (mass : Nat → Nat)
    (h : ∀ i, 0<i → 16^i * mass i ≤ M)
    (first k : Nat) (hf : 0<first) :
    15*16^first*gapSum mass first k ≤ 16*M := by
  induction k generalizing first with
  | zero => simp [gapSum]
  | succ k ih =>
    have hh := ih (first+1) (by omega)
    have hrest : 15*16^first*gapSum mass (first+1) k ≤ M := by
      apply Nat.le_of_mul_le_mul_left _ (by decide : 0<16)
      calc
        _ = 15*16^(first+1)*gapSum mass (first+1) k := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ _ := hh
    have hhead := Nat.mul_le_mul_left 15 (h first hf)
    simp only [gapSum,Nat.mul_add,Nat.mul_assoc]
    have hh' : 15*(16^first*gapSum mass (first+1) k) ≤ M := by
      simpa only [Nat.mul_assoc] using hrest
    omega

/-- Apply the geometric union estimate on any common denominator M.
Two event families each bounded by 16^(-h) at distinct positive h have
combined probability at most 1/4 (in fact at most 2/15). -/
theorem quarter_of_distinct_gap_masses (M K : Nat) (a b : Nat → Nat)
    (ha : ∀ i, 0<i → 16^i*a i ≤ M)
    (hb : ∀ i, 0<i → 16^i*b i ≤ M) :
    4*gapSum (fun h => a h+b h) 1 K ≤ M := by
  let f := fun h => a h+b h
  have hf (i : Nat) (hi : 0<i) : 16^i*f i ≤ 2*M := by
    dsimp [f]
    rw [Nat.mul_add]
    have hh := Nat.add_le_add (ha i hi) (hb i hi)
    simpa [Nat.two_mul] using hh
  have h1 := geometric_gap_sum (2*M) f hf 1 K (by decide)
  have h2 : 15*gapSum f 1 K ≤ 2*M := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0<16)
    calc
      _ = 15*16^1*gapSum f 1 K := by rw [Nat.pow_one]; ac_rfl
      _ ≤ _ := h1
  change 4*gapSum f 1 K ≤ M
  omega

/-- Padding a prefix event by arbitrary raw suffix marks gives a common
word denominator, even when the individual prefix horizons differ. -/
theorem rescale_prefix_mass (n a T U K : Nat) (hTU : T≤U)
    (h : K*a ≤ n^T) : K*(n^(U-T)*a) ≤ n^U := by
  calc
    _ = n^(U-T)*(K*a) := by ac_rfl
    _ ≤ n^(U-T)*n^T := Nat.mul_le_mul_left _ h
    _ = _ := by rw [←Nat.pow_add,show U-T+T=U by omega]

private theorem sharp_timer_weight {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α × Nat × Nat) :
    sumEdge (fun e =>
      let y := countStep next nom x e
      (3 : Nat)^y.2.1 * 2^y.2.2) ≤
    (2*n+1)*(3^x.2.1*2^x.2.2) := by
  let w := (3 : Nat)^x.2.1*2^x.2.2
  have h (e : Fin n) :
      (let y := countStep next nom x e; (3 : Nat)^y.2.1 * 2^y.2.2) =
        2*w + if nom x.1 = some e then w else 0 := by
    by_cases he : nom x.1 = some e
    · simp only [countStep,he,if_true,Nat.pow_succ]
      rw [show (3 : Nat)^x.2.1*3 = 3^x.2.1*2+3^x.2.1 from by omega]
      -- keep the base unchanged: factor only the terminal multiplicative 5
      change (3^x.2.1*2+3^x.2.1)*2^x.2.2 = 2*w+w
      rw [Nat.add_mul]
      dsimp [w]
      ac_rfl
    · simp only [countStep,he,if_false,Nat.pow_succ,Nat.add_zero]
      dsimp [w]
      ac_rfl
  simp only [h,sum_add,sum_const]
  have hh : sumEdge (fun e => if nom x.1 = some e then w else 0) ≤ w := by
    cases hm : nom x.1 with
    | none => simp [sum_const]
    | some i =>
      simpa only [hm,Option.some.injEq,eq_comm] using
        (show sumEdge (fun e => if e=i then w else 0) ≤ w from (by rw [sum_single]; exact Nat.le_refl _))
  have hm : (2*n+1)*w = n*(2*w)+w := by rw [Nat.add_mul,Nat.one_mul]; congr 1; ac_rfl
  change _ ≤ (2*n+1)*w
  omega

/-- A 3/2 exponential-moment estimate, with all denominators cleared. -/
theorem sharp_timer_moment {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α) (T K : Nat) :
    (3^K*2^(T-K))*timerMass next nom x T K ≤ (2*n+1)^T := by
  have h := endpoint_scoped (countStep next nom) (fun y => if K≤y.2.1 then 1 else 0)
    (fun y => 3^y.2.1*2^y.2.2) (3^K*2^(T-K)) (fun y => y.2.1+y.2.2)
    (count_total next nom) T (by
      intro y hy
      by_cases hh : K ≤ y.2.1
      · simp only [hh,if_true,Nat.mul_one]
        have h1 : y.2.1 = K+(y.2.1-K) := by omega
        have h2 : T-K = y.2.2+(y.2.1-K) := by omega
        have ha : 2^(y.2.1-K) ≤ 3^(y.2.1-K) := Nat.pow_le_pow_left (by decide) _
        rw [h2,Nat.pow_add]
        have hpow : 3^y.2.1 = 3^K*3^(y.2.1-K) := by
          exact (congrArg (fun a => (3 : Nat)^a) h1).trans (Nat.pow_add ..)
        calc
          _ = (3^K*2^y.2.2)*2^(y.2.1-K) := by ac_rfl
          _ ≤ (3^K*2^y.2.2)*3^(y.2.1-K) := Nat.mul_le_mul_left _ ha
          _ = _ := by rw [hpow]; ac_rfl
      · simp [hh]) T (x,0,0) (by simp)
  refine Nat.le_trans h ?_
  simpa using endpoint_estimate (countStep next nom) (fun y => 3^y.2.1*2^y.2.2)
    (2*n+1) (sharp_timer_weight next nom) T (x,0,0)

private theorem sharp_timer_block (n : Nat) (hn : 0<n) :
    9*(2*n+1)^n ≤ 16*(2*n)^n := by
  have hbase : (8*n)*(2*n+1) ≤ (4*n+1)^2 := by
    simp only [Nat.pow_two,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    have he : 8*n*(2*n)=(4*n)*(4*n) := by ac_rfl
    rw [he]
    omega
  have h1 := Nat.pow_le_pow_left hbase n
  rw [Nat.mul_pow,←Nat.pow_mul,Nat.mul_comm 2 n,Nat.pow_mul] at h1
  rw [show n*2+1=2*n+1 by omega] at h1
  have h2 := Nat.pow_le_pow_left (timer_block n hn) 2
  rw [Nat.mul_pow,Nat.mul_pow] at h2
  change 9*((4*n+1)^n)^2 ≤16*((4*n)^n)^2 at h2
  have he : ((4*n)^n)^2 = (8*n)^n*(2*n)^n := by
    rw [Nat.pow_two,←Nat.mul_pow,←Nat.mul_pow]
    have he' : 4*n*(4*n)=8*n*(2*n) := by ac_rfl
    rw [he']
  apply Nat.le_of_mul_le_mul_left _ (show 0 < (8*n)^n from Nat.pow_pos (by omega))
  calc
    _ = 9*((8*n)^n*(2*n+1)^n) := by ac_rfl
    _ ≤ 9*((4*n+1)^n)^2 := Nat.mul_le_mul_left 9 h1
    _ ≤ 16*((4*n)^n)^2 := h2
    _ = _ := by rw [he]; ac_rfl

private theorem sharp_timer_coeff (c h : Nat) (hc : 12≤c) :
    256^h * 4096^(c*h) ≤ 6561^(c*h) := by
  have hbase : 256 * 4096^12 ≤ (6561 : Nat)^12 := by decide
  have hh := Nat.pow_le_pow_left hbase h
  rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul] at hh
  have hh' : 256^h * 4096^(12*h) ≤ 6561^(12*h) := hh
  have hm : 12*h≤c*h := Nat.mul_le_mul_right h hc
  have he : c*h = 12*h + (c*h-12*h) := by omega
  have ha (a : Nat) : a^(c*h) = a^(12*h)*a^(c*h-12*h) :=
    (congrArg (fun e => a^e) he).trans (Nat.pow_add ..)
  rw [ha 4096,ha 6561,←Nat.mul_assoc]
  exact Nat.mul_le_mul hh' (Nat.pow_le_pow_left (by decide) _)

/-- Across 2*c*n*h marks, at most one nominated productive timer edge
per mark gives a tail of at most 256^(-h) for 4*c*h hits, when c≥12.
This is uniform over the nomination strategy and physical start. -/
theorem sharp_timer_gap_tail {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Option (Fin n)) (x : α) (c h : Nat) (hn : 2≤n) (hc : 12≤c) :
    256^h * timerMass next nom x (2*n*(c*h)) (4*(c*h)) ≤ n^(2*n*(c*h)) := by
  let m := c*h
  let T := 2*n*m
  let K := 4*m
  let Z := timerMass next nom x T K
  change 256^h*Z ≤ n^T
  have hKT : K≤T := by
    dsimp [K,T]
    exact Nat.mul_le_mul_right _ (by omega)
  have hBlock := Nat.pow_le_pow_left (sharp_timer_block n (by omega)) (2*m)
  rw [Nat.mul_pow,Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul,
    show n*(2*m)=T by dsimp [T]; ac_rfl] at hBlock
  have hM : (3^K*2^(T-K))*Z ≤ (2*n+1)^T := sharp_timer_moment next nom x T K
  have hQ := Nat.le_trans (Nat.mul_le_mul_left (9^(2*m)) hM) hBlock
  have ex (a b : Nat) : (a^b)^m = a^(b*m) := (Nat.pow_mul ..).symm
  have cLeft : 9^(2*m)*3^K = 6561^m := by
    dsimp [K]
    rw [←ex 9 2,←ex 3 4,←Nat.mul_pow]
  have cRight : 16^(2*m)*2^K = 4096^m := by
    dsimp [K]
    rw [←ex 16 2,←ex 2 4,←Nat.mul_pow]
  have hPower : 2^T = 2^K*2^(T-K) := by rw [←Nat.pow_add,show K+(T-K)=T by omega]
  have hCancel : 6561^m * Z ≤ 4096^m * n^T := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < 2^(T-K) from Nat.pow_pos (by decide))
    calc
      _ = 9^(2*m)*((3^K*2^(T-K))*Z) := by rw [←cLeft]; ac_rfl
      _ ≤ 16^(2*m)*(2*n)^T := hQ
      _ = _ := by
        rw [Nat.mul_pow,hPower,←cRight]
        ac_rfl
  apply Nat.le_of_mul_le_mul_left _ (show 0 < 4096^m from Nat.pow_pos (by decide))
  calc
    _ = (256^h*4096^m)*Z := by ac_rfl
    _ ≤ 6561^m*Z := Nat.mul_le_mul_right _ (sharp_timer_coeff c h hc)
    _ ≤ _ := hCancel

/-- The chance of having no more than h successful ordered nominations
by 2*c*n*h marks is at most 2048^(-h), even with predictable selection. -/
theorem sharp_slow_gap_tail {α : Type} {n : Nat} (next : α → Fin n → α)
    (nom : α → Fin n) (x : α) (c h : Nat) (hn : 2≤n) (hc : 12≤c) :
    2048^h * slowMass next nom x (2*n*(c*h)) (h) ≤ n^(2*n*(c*h)) := by
  let m := c*h
  let T := 2*n*m
  let Z := slowMass next nom x T (h)
  change 2048^h*Z ≤ n^T
  have hT : h ≤ T := by
    have hm : h ≤ m := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.le_trans hm (Nat.le_mul_of_pos_left _ (by omega))
  have hm : 12*h≤m := Nat.mul_le_mul_right _ (by omega)
  have hBlock := Nat.pow_le_pow_left (slow_block n (by omega)) m
  rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul] at hBlock
  change 2^m*(2*n-1)^T ≤ (2*n)^T at hBlock
  have hM : 2^(T-h)*Z ≤ (2*n-1)^T := slow_moment next nom x T (h)
  have hQ := Nat.le_trans (Nat.mul_le_mul_left (2^m) hM) hBlock
  have hc' : 2^T * 2048^h ≤ 2^m * 2^(T-h) := by
    rw [show (2048:Nat)^h = 2^(11*h) from (Nat.pow_mul 2 11 h).symm,←Nat.pow_add,←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply Nat.le_of_mul_le_mul_left _ (show 0<2^T from Nat.pow_pos (by decide))
  calc
    _ = (2^T*2048^h)*Z := by ac_rfl
    _ ≤ (2^m*2^(T-h))*Z := Nat.mul_le_mul_right _ hc'
    _ ≤ (2*n)^T := by rw [Nat.mul_assoc]; exact hQ
    _ = _ := Nat.mul_pow ..

private theorem sharp_geometric_gap_sum (M : Nat) (mass : Nat → Nat)
    (h : ∀ i, 0<i → 256^i * mass i ≤ M)
    (first k : Nat) (hf : 0<first) :
    255*256^first*gapSum mass first k ≤ 256*M := by
  induction k generalizing first with
  | zero => simp [gapSum]
  | succ k ih =>
    have hh := ih (first+1) (by omega)
    have hrest : 255*256^first*gapSum mass (first+1) k ≤ M := by
      apply Nat.le_of_mul_le_mul_left _ (by decide : 0<256)
      calc
        _ = 255*256^(first+1)*gapSum mass (first+1) k := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ _ := hh
    have hhead := Nat.mul_le_mul_left 255 (h first hf)
    simp only [gapSum,Nat.mul_add,Nat.mul_assoc]
    have hh' : 255*(256^first*gapSum mass (first+1) k) ≤ M := by
      simpa only [Nat.mul_assoc] using hrest
    omega

/-- Apply the geometric union estimate on any common denominator M.
Two event families each bounded by 256^(-h) at distinct positive h have
combined probability at most 11/1000 (in fact at most 2/255). -/
theorem elevenPerThousand_of_distinct_gap_masses (M K : Nat) (a b : Nat → Nat)
    (ha : ∀ i, 0<i → 256^i*a i ≤ M)
    (hb : ∀ i, 0<i → 256^i*b i ≤ M) :
    1000*gapSum (fun h => a h+b h) 1 K ≤ 11*M := by
  let f := fun h => a h+b h
  have hf (i : Nat) (hi : 0<i) : 256^i*f i ≤ 2*M := by
    dsimp [f]
    rw [Nat.mul_add]
    have hh := Nat.add_le_add (ha i hi) (hb i hi)
    simpa [Nat.two_mul] using hh
  have h1 := sharp_geometric_gap_sum (2*M) f hf 1 K (by decide)
  have h2 : 255*gapSum f 1 K ≤ 2*M := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0<256)
    calc
      _ = 255*256^1*gapSum f 1 K := by rw [Nat.pow_one]; ac_rfl
      _ ≤ _ := h1
  change 1000*gapSum f 1 K ≤ 11*M
  omega

/-- The next ordered payment request, with a harmless fixed label after
all requests have been served. -/
def payNomination {n : Nat} (fallback : Fin n) (pending : List (Fin n)) : Fin n :=
  pending.headD fallback

/-- Enough favorable marks of the predictable path cursor certify that
the entire original payment path appears as an ordered subsequence.
Padding the nomination after completion never gives a false certificate. -/
theorem paySublist_of_hits {n : Nat} (fallback : Fin n) (path w : List (Fin n))
    (b miss : Nat)
    (h : path.length+b ≤
      (GGTiming.runMarks (countStep GGTiming.pathStep (fun p => some (payNomination fallback p)))
        (path,b,miss) w).2.1) :
    path.Sublist w := by
  induction w generalizing path b miss with
  | nil =>
    change path.length+b ≤ b at h
    have hl : path.length=0 := by omega
    rw [List.length_eq_zero_iff.mp hl]
    exact .slnil
  | cons e w ih =>
    cases path with
    | nil => exact List.nil_sublist _
    | cons a p =>
      by_cases he : e=a
      · subst e
        apply List.Sublist.cons_cons
        apply ih p (b+1) miss
        simp only [GGTiming.runMarks,countStep,payNomination,List.headD_cons,
          GGTiming.pathStep,List.length_cons] at h
        rw [show p.length+(b+1)=p.length+1+b by omega]
        exact h
      · have hn : (some (payNomination fallback (a::p)) : Option (Fin n)) ≠ some e :=
          fun hm => he (Option.some.inj hm).symm
        apply List.Sublist.cons
        apply ih (a::p) b (miss+1)
        simpa only [GGTiming.runMarks,countStep,if_neg hn,GGTiming.pathStep,if_neg he] using h

/-- Exact comparison of finite raw-word numerators on two different
observers from the same initial physical cut. Only a deterministic
pointwise comparison on common words is needed. -/
theorem endpointSum_le_of_common_words {α β : Type} {n : Nat}
    (next : α → Fin n → α) (other : β → Fin n → β)
    (f : α → Nat) (g : β → Nat) (x : α) (y : β)
    (h : ∀ w, f (GGTiming.runMarks next x w) ≤ g (GGTiming.runMarks other y w))
    (t : Nat) :
    endpointSum next f t x ≤ endpointSum other g t y := by
  induction t generalizing x y with
  | zero => exact h []
  | succ t ih =>
    exact sum_mono (fun e => ih (next x e) (other y e) (fun w => h (e::w)))

end L4.RankRace

