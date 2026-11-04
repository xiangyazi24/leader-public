import Leader.Core.ThreePortSerialCount
import Leader.Wu.Splice.GarbageDrainTable

set_option autoImplicit false

/-! # Ordered window matcher: a fixed request sequence hit in order before any other window symbol

A window is a set of `t ≥ 1` touching scheduler symbols (`touch`).  The matcher of a request list `req` of touching
symbols waits on non-touching symbols, advances when the next requested symbol comes, and fails on any other touching
symbol.  One stage has the exact count identity `t * S(T) + (n - t)^T = n^T` (`stage_identity`), hence
`3 n^(2n) ≤ 4 t S(2n)` (`stage_mass`), and a request list of length `k` succeeds on at least a `(3 / (4 t))^k` fraction of
the words of length `2 n k` (`ordered_mass`).  The four-hit matcher `B9SpliceQuadHitCount` is the case of one repeated
request with window size three. -/

namespace B9OrderedWindowMatcher

open FiniteUniformStoppingTree ThreePortSerialCount

variable {n : Nat}

def touchCount (touch : Fin n → Bool) : Nat :=
  (List.ofFn (fun e : Fin n => if touch e = true then 1 else 0)).sum

theorem ofFn_spike' (a : Fin n) (c : Nat) : (List.ofFn (fun i : Fin n => if i = a then c else 0)).sum = c := by
  have h1 := B9SpliceTableV10d.ofFn_sum_split (fun _ : Fin n => 0) (fun i : Fin n => if i = a then c else 0) a
    (fun _ _ => Nat.zero_le _)
  have h2 := B9SpliceTableV10d.ofFn_sum_split (fun i : Fin n => if i = a then c else 0) (fun _ : Fin n => 0) a
    (fun i hi => by simp [hi])
  rw [ofFn_sum_const] at h1 h2
  simp at h1 h2
  omega

theorem touchCount_le (touch : Fin n → Bool) : touchCount touch ≤ n := by
  unfold touchCount
  have h := ofFn_sum_le (fun e : Fin n => if touch e = true then 1 else 0) (fun _ => 1)
    (fun e => by split <;> omega)
  rw [ofFn_sum_const] at h
  omega

/-- Child sum of a stage: the requested symbol, the other touching symbols, the waiting symbols. -/
theorem sum_stage (touch : Fin n → Bool) (a : Fin n) (ha : touch a = true) (X Y : Nat) (f : Fin n → Nat)
    (hf : ∀ e, f e = if e = a then X else if touch e = true then 0 else Y) :
    (List.ofFn f).sum = X + (n - touchCount touch) * Y := by
  have hp : ∀ e : Fin n, f e + Y * (if touch e = true then 1 else 0) = (if e = a then X else 0) + Y := by
    intro e
    rw [hf e]
    by_cases hea : e = a
    · subst hea; simp [ha]
    · by_cases ht : touch e = true
      · simp [hea, ht]
      · simp [hea, ht]
  have hs := ofFn_sum_eq _ _ hp
  rw [ofFn_sum_add, ofFn_sum_add, ofFn_sum_mul_left, ofFn_spike', ofFn_sum_const] at hs
  have ht := touchCount_le touch
  have hsub : (n - touchCount touch) * Y + touchCount touch * Y = n * Y := by
    rw [← Nat.add_mul, Nat.sub_add_cancel ht]
  rw [show (List.ofFn fun i : Fin n => if touch i = true then 1 else 0).sum = touchCount touch from rfl] at hs
  rw [Nat.mul_comm Y] at hs
  omega

/-! ## One stage -/

/-- Good symbol `a` succeeds, other touching symbols fail, the rest wait. -/
def oneStep (touch : Fin n → Bool) (a : Fin n) (_ : Unit) (e : Fin n) : StopNode Unit :=
  if e = a then .success else if touch e = true then .failure else .active ()

/-- The stage count, by its recursion. -/
def stageCount (n t : Nat) : Nat → Nat
  | 0 => 0
  | T + 1 => n ^ T + (n - t) * stageCount n t T

theorem oneStep_count (touch : Fin n → Bool) (a : Fin n) (ha : touch a = true) :
    ∀ T, successCount (oneStep touch a) (.active ()) T = stageCount n (touchCount touch) T
  | 0 => rfl
  | T + 1 => by
      change (List.ofFn (fun e : Fin n =>
        treeWeight (oneStep touch a) successWeight (oneStep touch a () e) T)).sum = _
      rw [sum_stage touch a ha (n ^ T) (stageCount n (touchCount touch) T) _ (fun e => by
        unfold oneStep
        by_cases hea : e = a
        · rw [if_pos hea, if_pos hea, treeWeight_success]; simp [successWeight]
        · rw [if_neg hea, if_neg hea]
          by_cases ht : touch e = true
          · rw [if_pos ht, if_pos ht, treeWeight_failure]; simp [successWeight]
          · rw [if_neg ht, if_neg ht]
            exact oneStep_count touch a ha T)]
      rfl

theorem stage_identity (t : Nat) (ht : t ≤ n) :
    ∀ T, t * stageCount n t T + (n - t) ^ T = n ^ T
  | 0 => by simp [stageCount]
  | T + 1 => by
      have ih := stage_identity t ht T
      obtain ⟨m, rfl⟩ : ∃ m, n = m + t := ⟨n - t, by omega⟩
      have hm : m + t - t = m := by omega
      rw [hm] at ih
      rw [stageCount, hm, Nat.pow_succ, Nat.pow_succ, Nat.mul_add]
      have e1 : t * (m * stageCount (m + t) t T) + m ^ T * m = m * (t * stageCount (m + t) t T + m ^ T) := by
        rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm (m ^ T) m]
      calc t * (m + t) ^ T + t * (m * stageCount (m + t) t T) + m ^ T * m
          = t * (m + t) ^ T + (t * (m * stageCount (m + t) t T) + m ^ T * m) := by rw [Nat.add_assoc]
        _ = t * (m + t) ^ T + m * (m + t) ^ T := by rw [e1, ih]
        _ = (m + t) ^ T * (m + t) := by rw [← Nat.add_mul, Nat.mul_comm, Nat.add_comm t m]

/-- Bernoulli: `a^(k+1) + (k+1) a^k ≤ (a+1)^(k+1)`. -/
theorem bernoulli (a : Nat) : ∀ k, a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
      have ih := bernoulli a k
      have h1 : (a + 1) * (a ^ (k + 1) + (k + 1) * a ^ k) ≤ (a + 1) * (a + 1) ^ (k + 1) :=
        Nat.mul_le_mul_left _ ih
      have e2 : (a + 1) * (a ^ (k + 1) + (k + 1) * a ^ k) =
          a ^ (k + 1 + 1) + (k + 1) * a ^ (k + 1) + a ^ (k + 1) + (k + 1) * a ^ k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.pow_succ a (k + 1)]
        have : a * ((k + 1) * a ^ k) = (k + 1) * a ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm (a ^ k) a]
        rw [this, Nat.mul_comm a (a ^ (k + 1))]
        omega
      have e3 : (a + 1) * (a + 1) ^ (k + 1) = (a + 1) ^ (k + 1 + 1) := by
        rw [Nat.pow_succ (a + 1) (k + 1), Nat.mul_comm]
      rw [e2, e3] at h1
      have e4 : (k + 1 + 1) * a ^ (k + 1) = (k + 1) * a ^ (k + 1) + a ^ (k + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e4]
      omega

theorem two_mul_pow_le (n : Nat) (hn : 1 ≤ n) : 2 * (n - 1) ^ n ≤ n ^ n := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  have hb := bernoulli a a
  have h2 : a ^ (a + 1) ≤ (a + 1) * a ^ a := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.le_succ a)
  simp only [Nat.add_sub_cancel]
  omega

theorem stage_mass (touch : Fin n → Bool) (a : Fin n) (ha : touch a = true) :
    3 * n ^ (2 * n) ≤ 4 * (touchCount touch * successCount (oneStep touch a) (.active ()) (2 * n)) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact Fin.elim0 a)
  have ht1 : 1 ≤ touchCount touch := by
    unfold touchCount
    have h := B9SpliceTableV10d.ofFn_sum_split (fun _ : Fin n => 0)
      (fun e : Fin n => if touch e = true then 1 else 0) a (fun _ _ => Nat.zero_le _)
    rw [ofFn_sum_const] at h
    simp [ha] at h
    omega
  have htn := touchCount_le touch
  have hid := stage_identity (n := n) (touchCount touch) htn (2 * n)
  rw [← oneStep_count touch a ha] at hid
  have hpow : (n - touchCount touch) ^ (2 * n) ≤ (n - 1) ^ (2 * n) := Nat.pow_le_pow_left (by omega) _
  have hb := two_mul_pow_le n hn
  have hsq : 4 * (n - 1) ^ (2 * n) ≤ n ^ (2 * n) := by
    have h1 : (2 * (n - 1) ^ n) * (2 * (n - 1) ^ n) ≤ n ^ n * n ^ n := Nat.mul_le_mul hb hb
    have e1 : (2 * (n - 1) ^ n) * (2 * (n - 1) ^ n) = 4 * (n - 1) ^ (2 * n) := by
      rw [show 2 * n = n + n by omega, Nat.pow_add, show (4 : Nat) = 2 * 2 from rfl]; ac_rfl
    have e2 : n ^ n * n ^ n = n ^ (2 * n) := by rw [show 2 * n = n + n by omega, Nat.pow_add]
    rw [e1, e2] at h1; exact h1
  omega

/-! ## Ordered requests -/

/-- State = the remaining requests. -/
def ordStep (touch : Fin n → Bool) : List (Fin n) → Fin n → StopNode (List (Fin n))
  | [], _ => .success
  | a :: rest, e =>
      if e = a then (match rest with | [] => .success | _ :: _ => .active rest)
      else if touch e = true then .failure else .active (a :: rest)

theorem ordStep_single (touch : Fin n → Bool) (a e : Fin n) :
    ordStep touch [a] e = if e = a then .success else if touch e = true then .failure else .active [a] := by
  unfold ordStep; rfl

theorem ordStep_cons2 (touch : Fin n → Bool) (a b e : Fin n) (rest : List (Fin n)) :
    ordStep touch (a :: b :: rest) e =
      if e = a then .active (b :: rest) else if touch e = true then .failure else .active (a :: b :: rest) := by
  unfold ordStep; rfl

theorem ord_last_count (touch : Fin n → Bool) (a : Fin n) :
    ∀ T, successCount (ordStep touch) (.active [a]) T = successCount (oneStep touch a) (.active ()) T
  | 0 => rfl
  | T + 1 => by
      change (List.ofFn (fun e : Fin n => treeWeight (ordStep touch) successWeight (ordStep touch [a] e) T)).sum =
        (List.ofFn (fun e : Fin n => treeWeight (oneStep touch a) successWeight (oneStep touch a () e) T)).sum
      apply ofFn_sum_eq
      intro e
      rw [ordStep_single]
      unfold oneStep
      by_cases hea : e = a
      · rw [if_pos hea, if_pos hea, treeWeight_success, treeWeight_success]; rfl
      · rw [if_neg hea, if_neg hea]
        by_cases ht : touch e = true
        · rw [if_pos ht, if_pos ht, treeWeight_failure, treeWeight_failure]; rfl
        · rw [if_neg ht, if_neg ht]; exact ord_last_count touch a T

theorem ord_cons_succ (touch : Fin n → Bool) (a b : Fin n) (rest : List (Fin n)) (ha : touch a = true) (T : Nat) :
    successCount (ordStep touch) (.active (a :: b :: rest)) (T + 1) =
      successCount (ordStep touch) (.active (b :: rest)) T +
        (n - touchCount touch) * successCount (ordStep touch) (.active (a :: b :: rest)) T := by
  change (List.ofFn (fun e : Fin n =>
    treeWeight (ordStep touch) successWeight (ordStep touch (a :: b :: rest) e) T)).sum = _
  exact sum_stage touch a ha _ _ _ (fun e => by
    rw [ordStep_cons2]
    by_cases hea : e = a
    · rw [if_pos hea, if_pos hea]; rfl
    · rw [if_neg hea, if_neg hea]
      by_cases ht : touch e = true
      · rw [if_pos ht, if_pos ht, treeWeight_failure]; simp [successWeight]
      · rw [if_neg ht, if_neg ht]; rfl)

/-- A stage of `u` letters followed by the remaining requests within `v` letters. -/
theorem ord_concat (touch : Fin n → Bool) (a b : Fin n) (rest : List (Fin n)) (ha : touch a = true) (v : Nat) :
    ∀ u, successCount (oneStep touch a) (.active ()) u * successCount (ordStep touch) (.active (b :: rest)) v ≤
      successCount (ordStep touch) (.active (a :: b :: rest)) (u + v)
  | 0 => by simp [successCount, treeWeight, successWeight]
  | u + 1 => by
      have ih := ord_concat touch a b rest ha v u
      have hpad : n ^ u * successCount (ordStep touch) (.active (b :: rest)) v ≤
          successCount (ordStep touch) (.active (b :: rest)) (u + v) := by
        simpa only [Nat.add_comm] using success_padding (ordStep touch) (.active (b :: rest)) v u
      rw [oneStep_count touch a ha (u + 1)] at *
      rw [oneStep_count touch a ha u] at ih
      show (n ^ u + (n - touchCount touch) * stageCount n (touchCount touch) u) *
          successCount (ordStep touch) (.active (b :: rest)) v ≤ _
      rw [show u + 1 + v = (u + v) + 1 by omega, ord_cons_succ touch a b rest ha (u + v), Nat.add_mul, Nat.mul_assoc]
      exact Nat.add_le_add hpad (Nat.mul_le_mul_left _ ih)

theorem ordered_mass (touch : Fin n → Bool) :
    ∀ (req : List (Fin n)), req ≠ [] → (∀ a ∈ req, touch a = true) →
      3 ^ req.length * n ^ (2 * n * req.length) ≤
        (4 * touchCount touch) ^ req.length * successCount (ordStep touch) (.active req) (2 * n * req.length)
  | [], h, _ => absurd rfl h
  | [a], _, hall => by
      have ha := hall a (List.mem_singleton_self a)
      rw [ord_last_count touch a]
      simp only [List.length_singleton, Nat.pow_one, Nat.mul_one]
      have := stage_mass touch a ha
      calc 3 * n ^ (2 * n) ≤ 4 * (touchCount touch * successCount (oneStep touch a) (.active ()) (2 * n)) := this
        _ = 4 * touchCount touch * successCount (oneStep touch a) (.active ()) (2 * n) := by rw [Nat.mul_assoc]
  | a :: b :: rest, _, hall => by
      have ha := hall a List.mem_cons_self
      have hrest : ∀ x ∈ b :: rest, touch x = true := fun x hx => hall x (List.mem_cons_of_mem a hx)
      have ih := ordered_mass touch (b :: rest) (by simp) hrest
      have hs := stage_mass touch a ha
      have hcat := ord_concat touch a b rest ha (2 * n * (b :: rest).length) (2 * n)
      have hlen : (a :: b :: rest).length = (b :: rest).length + 1 := rfl
      rw [hlen]
      have hT : 2 * n * ((b :: rest).length + 1) = 2 * n + 2 * n * (b :: rest).length := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [hT]
      generalize hS : successCount (oneStep touch a) (.active ()) (2 * n) = S at hs hcat
      generalize hR : successCount (ordStep touch) (.active (b :: rest)) (2 * n * (b :: rest).length) = R at ih hcat
      generalize hQ : successCount (ordStep touch) (.active (a :: b :: rest)) (2 * n + 2 * n * (b :: rest).length) = Q at hcat ⊢
      generalize (b :: rest).length = k at ih hcat ⊢
      generalize touchCount touch = t at hs ih ⊢
      -- 3^(k+1) n^(2n + 2nk) = (3 n^(2n)) (3^k n^(2nk)) ≤ (4 t S) ((4t)^k R) = (4t)^(k+1) (S R) ≤ (4t)^(k+1) Q
      calc 3 ^ (k + 1) * n ^ (2 * n + 2 * n * k)
          = (3 * n ^ (2 * n)) * (3 ^ k * n ^ (2 * n * k)) := by rw [Nat.pow_succ, Nat.pow_add]; ac_rfl
        _ ≤ (4 * (t * S)) * ((4 * t) ^ k * R) := Nat.mul_le_mul hs ih
        _ = (4 * t) ^ (k + 1) * (S * R) := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ (4 * t) ^ (k + 1) * Q := Nat.mul_le_mul_left _ hcat

end B9OrderedWindowMatcher
