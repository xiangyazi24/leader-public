import Leader.L4.RankRenewal
import Leader.L4.RankAttempt
import Leader.L4.TripleControlled

/-! Adaptive raw-label races for the long sealed triple attempt. -/
namespace L4.TripleLongRace
open TaggedTail RankRenewal

private theorem ss {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sconst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [ss,ih,Nat.succ_mul,Nat.add_comm]

private theorem sadd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun i => f i+g i) = sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ss,ss f,ss g,ih]; omega

private theorem sone {n : Nat} (e : Fin n) (a : Nat) :
    sumEdge (fun i => if i=e then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) e
    · rw [ss]
      simp [show (fun i : Fin n => if i.succ=(0 : Fin (n+1)) then a else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sconst]
    · rw [ss,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

/-- Two distinct observable labels each occur once, whatever the state
that supplied the nominations. -/
theorem two_labels {n : Nat} (a b : Fin n) (h : a ≠ b) (L R U : Nat) :
    sumEdge (fun e => if e=a then L else if e=b then R else U) = L+R+(n-2)*U := by
  have hn : 2 ≤ n := by
    by_cases hn : 2 ≤ n
    · exact hn
    · exact False.elim (h (Fin.ext (by omega)))
  have hh (e : Fin n) :
      (if e=a then L else if e=b then R else U) +
          ((if e=a then U else 0)+(if e=b then U else 0)) =
      (if e=a then L else 0) + ((if e=b then R else 0) + U) := by
    by_cases ha : e=a <;> by_cases hb : e=b
    · exact (h (ha.symm.trans hb)).elim
    all_goals simp [ha,hb,h,Ne.symm h,Nat.add_comm]
  have he := congrArg sumEdge (funext hh)
  rw [sadd,sadd,sadd,sadd,sone,sone,sone,sone,sconst] at he
  have hmul : n*U=(n-2)*U+U+U := by
    calc
      n*U = (n-2+1+1)*U := congrArg (fun k => k*U) (by omega)
      _ = _ := by simp [Nat.add_mul]
  omega

/-- Arbitrary physical history evolves on every raw mark. The two shadow
branches update only at the two predictable nominated labels. -/
def step {α σ : Type} {n : Nat} (next : α → Fin n → α)
    (a b : α × σ → Fin n) (left right : σ → σ) (x : α × σ) (e : Fin n) : α × σ :=
  (next x.1 e, if e=a x then left x.2 else if e=b x then right x.2 else x.2)

def clock {σ : Type} (n : Nat) (left right : σ → σ) (f : σ → Nat) :
    Nat → σ → Nat
  | 0,x => f x
  | t+1,x => clock n left right f t (left x) + clock n left right f t (right x) +
    (n-2)*clock n left right f t x

/-- Exact shadow marginal at any deterministic raw horizon. In particular
one may extend nominations past a physical stop by any distinct pair,
without conditioning on survival or future winners. -/
theorem exact_marginal {α σ : Type} {n : Nat} (next : α → Fin n → α)
    (a b : α × σ → Fin n) (h : ∀ x, a x ≠ b x) (left right : σ → σ)
    (f : σ → Nat) (t : Nat) (x : α × σ) :
    endpointSum (step next a b left right) (fun y => f y.2) t x =
      clock n left right f t x.2 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [endpointSum]
    calc
      _ = sumEdge (fun e => clock n left right f t (step next a b left right x e).2) :=
        congrArg sumEdge (funext fun e => ih (step next a b left right x e))
      _ = sumEdge (fun e => if e=a x then clock n left right f t (left x.2)
          else if e=b x then clock n left right f t (right x.2) else clock n left right f t x.2) := by
        apply congrArg sumEdge
        funext e
        by_cases ha : e=a x <;> by_cases hb : e=b x <;> simp [step,ha,hb,Ne.symm (h x)]
      _ = _ := two_labels (a x) (b x) (h x) _ _ _

/-- Remaining forward hits of the two competing fronts. Both shadow
credits freeze on the first zero. -/
def left : Nat × Nat → Nat × Nat
  | (a,b) => if a=0 ∨ b=0 then (a,b) else (a-1,b)

def right : Nat × Nat → Nat × Nat
  | (a,b) => if a=0 ∨ b=0 then (a,b) else (a,b-1)

def won (x : Nat × Nat) : Nat := if x.1>0 ∧ x.2=0 then 1 else 0

def lost (x : Nat × Nat) : Nat := won x.swap

def live (x : Nat × Nat) : Nat := if x.1>0 ∧ x.2>0 then 1 else 0

private theorem swap_left (x : Nat × Nat) : (left x).swap = right x.swap := by
  rcases x with ⟨a,b⟩
  by_cases h : a=0 ∨ b=0 <;> simp [left,right,Or.comm,h]

private theorem swap_right (x : Nat × Nat) : (right x).swap = left x.swap := by
  rcases x with ⟨a,b⟩
  by_cases h : a=0 ∨ b=0 <;> simp [left,right,Or.comm,h]

private theorem symmetry (n t : Nat) (x : Nat × Nat) :
    clock n left right won t x.swap = clock n left right lost t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [clock,←swap_right,←swap_left,ih]
    omega

private theorem total (n t : Nat) (hn : 2≤n) (x : Nat × Nat)
    (hx : x.1+x.2>0) :
    clock n left right won t x + clock n left right lost t x +
    clock n left right live t x = n^t := by
  induction t generalizing x with
  | zero =>
    rcases x with ⟨a,b⟩
    by_cases ha : a=0 <;> by_cases hb : b=0
    all_goals simp_all [clock,won,lost,live]
  | succ t ih =>
    have hL : (left x).1+(left x).2>0 := by
      rcases x with ⟨a,b⟩
      by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp_all [left] <;> omega
    have hR : (right x).1+(right x).2>0 := by
      rcases x with ⟨a,b⟩
      by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp_all [right] <;> omega
    have h₁ := ih _ hL
    have h₂ := ih _ hR
    have h₀ := congrArg (fun z => (n-2)*z) (ih x hx)
    simp only [clock]
    rw [Nat.pow_succ]
    simp only [Nat.mul_add] at h₀
    have key : n^t*n=(n-2)*n^t+n^t+n^t := by
      conv => lhs; rhs; rw [show n=n-2+1+1 from by omega]
      simp [Nat.mul_add,Nat.mul_comm]
    omega

/-- The padded equal-quota race has exact symmetry at *every* bounded
raw horizon: twice its winning mass plus its unfinished mass is the
entire raw-word mass.  Earlier genuine target readiness and actual
physical deletion can subsequently be counted as additional wins. -/
theorem fair_race {α : Type} {n : Nat} (next : α → Fin n → α)
    (a b : α × (Nat × Nat) → Fin n) (h : ∀ x, a x ≠ b x)
    (hn : 2≤n) (t k : Nat) (hk : 0<k) (x : α) :
    2*endpointSum (step next a b left right) (fun y => won y.2) t (x,(k,k)) +
      endpointSum (step next a b left right) (fun y => live y.2) t (x,(k,k)) = n^t := by
  rw [exact_marginal next a b h,exact_marginal next a b h]
  change 2*clock n left right won t (k,k) + clock n left right live t (k,k) = n^t
  have hs : clock n left right won t (k,k) = clock n left right lost t (k,k) :=
    symmetry n t (k,k)
  have ht := total n t hn (k,k) (by omega)
  omega

/-- The shadow race ends in at most one attacker counter's worth of
nominated hits in expectation. No timing independence of the nomination
choices is needed. -/
theorem race_mean {α : Type} {n : Nat} (next : α → Fin n → α)
    (a b : α × (Nat × Nat) → Fin n) (x : α × (Nat × Nat)) :
    IIDExpectedHittingTimeAtMost (step next a b left right)
      (fun y => y.2.1=0 ∨ y.2.2=0) x (n*x.2.1) := by
  refine TripleControlled.mean_of_potential (step next a b left right)
    (fun y => y.2.1=0 ∨ y.2.2=0) (fun _ => True) (fun y => y.2.1)
    (by simp) ?_ x trivial
  intro y _ hy
  rcases y with ⟨ctx,A,B⟩
  change ¬ (A=0 ∨ B=0) at hy
  have hA : 0<A := by omega
  apply TripleControlled.progress_raw_drift _ (a (ctx,A,B))
  · simpa [step,left,hy] using (show A-1+1≤A by omega)
  · intro i
    change (if i=a (ctx,A,B) then left (A,B)
      else if i=b (ctx,A,B) then right (A,B) else (A,B)).1 ≤ A
    split
    · simp [left,hy]
    · split <;> simp [right,hy]

private theorem survival_eq_live {α : Type} {n : Nat} (next : α → Fin n → α)
    (a b : α × (Nat × Nat) → Fin n) (t : Nat) (x : α × (Nat × Nat)) :
    survival (step next a b left right) (fun y => ¬ (y.2.1=0 ∨ y.2.2=0)) t x =
    endpointSum (step next a b left right) (fun y => live y.2) t x := by
  classical
  have inert (z : α × (Nat × Nat)) (hz : z.2.1=0 ∨ z.2.2=0) (e : Fin n) :
      (step next a b left right z e).2=z.2 := by
    by_cases h₁ : e=a z <;> by_cases h₂ : e=b z <;> simp [step,h₁,h₂,left,right,hz]
  have zero : ∀ t (z : α × (Nat × Nat)), z.2.1=0 ∨ z.2.2=0 →
      endpointSum (step next a b left right) (fun y => live y.2) t z=0 := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rcases hz with h|h <;> simp [endpointSum,live,h]
    | succ m ih =>
      intro z hz
      rw [endpointSum,show (fun e => endpointSum (step next a b left right)
        (fun y => live y.2) m (step next a b left right z e)) = (fun _ => 0) from
          funext fun e => ih _ (by rw [inert z hz e]; exact hz),sconst]
      omega
  induction t generalizing x with
  | zero =>
    by_cases hx : x.2.1=0 ∨ x.2.2=0
    · simp [survival,weightedSurvival,hx,zero 0 x hx]
    · have h₀ : 0<x.2.1 := by omega
      have h₁ : 0<x.2.2 := by omega
      simp [survival,weightedSurvival,endpointSum,live,hx,h₀,h₁]
  | succ t ih =>
    by_cases hx : x.2.1=0 ∨ x.2.2=0
    · simp [survival,weightedSurvival,hx,zero (t+1) x hx]
    · simp only [survival,weightedSurvival,hx,not_false_eq_true,if_true,endpointSum]
      exact congrArg sumEdge (funext fun e => ih _)

/-- Explicit finite-horizon cut, equivalent to a padded-race success
probability at least (1−nk/t)/2 when t>0. -/
theorem fair_race_deadline {α : Type} {n : Nat} (next : α → Fin n → α)
    (a b : α × (Nat × Nat) → Fin n) (h : ∀ x, a x ≠ b x)
    (hn : 2≤n) (t k : Nat) (hk : 0<k) (x : α) :
    t*n^t ≤ 2*t*endpointSum (step next a b left right) (fun y => won y.2) t (x,(k,k)) +
      (n*k)*n^t := by
  have H := fair_race next a b h hn t k hk x
  have M := race_mean next a b (x,(k,k)) t
  have E := RankPhysical.horizon_mul_survival_le_cost (step next a b left right)
    (fun y => y.2.1=0 ∨ y.2.2=0) t (x,(k,k))
  rw [survival_eq_live] at E
  change iidHitCost (step next a b left right)
    (fun y => y.2.1=0 ∨ y.2.2=0) t (x,(k,k)) ≤ n*k*n^t at M
  have J := Nat.le_trans E M
  have HH := congrArg (fun i => t*i) H
  simp only [Nat.mul_add,← Nat.mul_assoc] at HH
  rw [Nat.mul_comm t 2] at HH
  omega

/-- Literal directed edge indices from the two ambient sectors cannot
alias, even when the third endpoint is the first after a whole lap. -/
theorem disjoint_sector_bonds {n : Nat} (i : Fin n) {a b u v : Nat}
    (hab : a+b≤n) (hu : u<a) (hv : v<b) :
    liftedSite i u ≠ liftedSite (liftedSite i a) v := by
  have hfold : liftedSite (liftedSite i a) v = liftedSite i (a+v) := by
    apply Fin.ext
    change ((i.val+a)%n+v)%n = (i.val+(a+v))%n
    simp [Nat.add_assoc]
  rw [hfold]
  intro h
  have he := liftedSite_inj i (by omega : u<n) (by omega : a+v<n) h
  omega

end L4.TripleLongRace

#print axioms L4.TripleLongRace.exact_marginal
#print axioms L4.TripleLongRace.fair_race

#print axioms L4.TripleLongRace.race_mean
#print axioms L4.TripleLongRace.fair_race_deadline

#print axioms L4.TripleLongRace.disjoint_sector_bonds
