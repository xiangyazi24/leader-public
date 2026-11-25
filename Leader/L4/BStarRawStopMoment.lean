import Leader.L4.Height.Window

namespace L4.BStarRawStopMoment
open Height

/-- Evaluate at the first old-prefix stop or the finite horizon.
The remainder at a stop is the original untouched raw suffix. -/
def atStop {n : Nat} (stop : List (Fin n)→Bool)
    (pay : List (Fin n)→Nat→List (Fin n)→Nat) :
    List (Fin n)→Nat→List (Fin n)→Nat
  | h,t,[] => pay h t []
  | h,t,e::w => if stop h then pay h t (e::w)
    else atStop stop pay (h++[e]) (t+1) w

private theorem stop_true {n : Nat} (stop : List (Fin n)→Bool)
    (pay : List (Fin n)→Nat→List (Fin n)→Nat)
    (h : List (Fin n)) (t : Nat) (w : List (Fin n)) (H : stop h=true) :
    atStop stop pay h t w=pay h t w := by
  cases w <;> simp [atStop,H]

/-- Per-slice continuation bounds survive an adapted stopped prefix. -/
theorem compare_at_stop {n : Nat} (stop : List (Fin n)→Bool)
    (pay : List (Fin n)→Nat→List (Fin n)→Nat)
    (base : List (Fin n)→Nat→Nat) (C : Nat)
    (slice : ∀ h t K, (stop h=true ∨ K=0) →
      wordSum (pay h t) K ≤ C*base h t*n^K) :
    ∀ K h t, wordSum (atStop stop pay h t) K≤
      C*wordSum (atStop stop (fun h' t' _=>base h' t') h t) K := by
  intro K
  induction K with
  | zero =>
    intro h t
    have S := slice h t 0 (.inr rfl)
    simpa [atStop,wordSum] using S
  | succ K ih =>
    intro h t
    by_cases S : stop h=true
    · have P := wordSum_congr _ _ (fun w=>stop_true stop pay h t w S) (K+1)
      have T := wordSum_congr _ _
        (fun w=>stop_true stop (fun h' t' _=>base h' t') h t w S) (K+1)
      rw [P,T,wordSum_const]
      exact Nat.le_trans (slice h t (K+1) (.inl S)) (Nat.le_of_eq (by ac_rfl))
    · simp only [wordSum]
      rw [←sum_ofFn_mul_left]
      apply sum_ofFn_le
      intro e
      simpa [atStop,S] using ih (h++[e]) (t+1)

private theorem floor_add_le (L t w : Nat) (pos : 0<L) :
    (t+w)/L≤t/L+w/L+1 := by
  rw [Nat.add_div pos]
  split <;> omega

/-- A bounded stopping time and a predictable target can be followed
by suffix service at a factor-four cost in the floor moment, without
an independent-time or independent-target assumption. -/
theorem stopped_service_moment {n : Nat} (stop : List (Fin n)→Bool)
    (wait : List (Fin n)→List (Fin n)→Nat) (L : Nat) (pos : 0<L)
    (slice : ∀ h K, stop h=true →
      wordSum (fun w=>2^(wait h w/L)) K ≤ 2*n^K)
    (empty : ∀ h, wait h []=0) (D : Nat) (h : List (Fin n)) (t : Nat) :
    wordSum (atStop stop (fun h' t' w=>2^((t'+wait h' w)/L)) h t) D ≤
      4*wordSum (atStop stop (fun _ t' _=>2^(t'/L)) h t) D := by
  apply compare_at_stop stop (fun h' t' w=>2^((t'+wait h' w)/L)) (fun _ t'=>2^(t'/L)) 4
  intro old a K H
  rcases H with stopNow|zero
  · have point (w : List (Fin n)) :
        2^((a+wait old w)/L)≤(2*2^(a/L))*2^(wait old w/L) := by
      have E := Nat.pow_le_pow_right (by decide : 0 < 2) (floor_add_le L a (wait old w) pos)
      rw [Nat.pow_succ,Nat.pow_add] at E
      exact Nat.le_trans E (Nat.le_of_eq (by ac_rfl))
    apply Nat.le_trans (wordSum_mono _ _ point K)
    rw [wordSum_mul_left]
    exact Nat.le_trans (Nat.mul_le_mul_left _ (slice old K stopNow)) (Nat.le_of_eq (by
      change (2*2^(a/L))*(2*n^K)=4*2^(a/L)*n^K
      calc
        _ = (2*2)*2^(a/L)*n^K := by ac_rfl
        _ = _ := rfl))
  · subst K
    simp only [wordSum,empty,Nat.add_zero,Nat.pow_zero,Nat.mul_one]
    exact Nat.le_mul_of_pos_left _ (by decide)

#print axioms compare_at_stop
#print axioms stopped_service_moment
end L4.BStarRawStopMoment
