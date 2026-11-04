import Leader.Wu.Entrance.PairLocalLightCone

set_option autoImplicit false

/-! # Ordered requests complete within O(k n) letters with probability 7/8

`pending rs w` is the part of the ordered request list `rs` that greedy matching along the word `w` has not served:
a letter equal to the first pending request serves it, every other letter is skipped.  The words of length `T` that
leave a request pending satisfy `2^T * count ≤ 2^k * (2n-1)^T` for `k = rs.length` (`pending_count`, an exponential
moment bound proved by the first-letter recurrence), and with `(2n-1)^(2n) * 2 ≤ (2n)^(2n)` this gives: among the
words of length `2 n m` with `m ≥ k + 3`, at most one eighth leave a request pending (`pending_mass`).  For the
stage-4 chain of `psi - 1` ordered requests this is the completion probability that the ordered window matcher
(`BirthCheckChainR1Mass.train_escape_mass_explicit`, factor exp(-O(psi log psi))) does not give; interleaved letters
still have to be shown harmless separately.
-/

namespace B6OrderedCompletion

open FixedSpanRenewalPayload FiniteUniformStoppingTree

variable {n : Nat}

/-- Requests still pending after greedy matching along a word. -/
def pending : List (Fin n) → List (Fin n) → List (Fin n)
  | [], _ => []
  | r :: rs, [] => r :: rs
  | r :: rs, e :: w => if e = r then pending rs w else pending (r :: rs) w

theorem pending_nil (w : List (Fin n)) : pending [] w = [] := by
  cases w <;> rfl

theorem wordSum_zero : ∀ T : Nat, wordSum n T (fun _ => 0) = 0
  | 0 => by unfold wordSum; simp [allSchedules]
  | T + 1 => by
      rw [wordSum_succ]
      have h : (fun e : Fin n => wordSum n T (fun _ => 0)) = (fun _ => 0) := by
        funext e; exact wordSum_zero T
      simp only [h]
      rw [FiniteUniformStoppingTree.ofFn_sum_const]
      simp

/-- The pending indicator. -/
def pendingBit (rs : List (Fin n)) (w : List (Fin n)) : Nat := if pending rs w = [] then 0 else 1

theorem pending_count : ∀ (T : Nat) (rs : List (Fin n)),
    2 ^ T * wordSum n T (pendingBit rs) ≤ 2 ^ rs.length * (2 * n - 1) ^ T
  | T, [] => by
      have h : pendingBit ([] : List (Fin n)) = fun _ => 0 := by
        funext w; simp [pendingBit, pending_nil]
      rw [h, wordSum_zero]
      simp
  | 0, r :: rs => by
      unfold wordSum
      simp [allSchedules, pendingBit, pending] <;>
        first | exact Nat.one_le_two_pow | exact Nat.two_pow_pos _ | omega
  | T + 1, r :: rs => by
      have hn : 1 ≤ n := by have := r.isLt; omega
      rw [wordSum_succ]
      have hfun : (fun e : Fin n => wordSum n T (fun u => pendingBit (r :: rs) (e :: u))) =
          (fun e : Fin n => if e = r then wordSum n T (pendingBit rs) else wordSum n T (pendingBit (r :: rs))) := by
        funext e
        by_cases he : e = r
        · rw [if_pos he]
          have hu : (fun u => pendingBit (r :: rs) (e :: u)) = pendingBit rs := by
            funext u; simp [pendingBit, pending, he]
          rw [hu]
        · rw [if_neg he]
          have hu : (fun u => pendingBit (r :: rs) (e :: u)) = pendingBit (r :: rs) := by
            funext u; simp [pendingBit, pending, he]
          rw [hu]
      rw [hfun]
      have ih1 := pending_count T rs
      have ih2 := pending_count T (r :: rs)
      simp only [List.length_cons] at ih2 ⊢
      generalize wordSum n T (pendingBit rs) = A at ih1 ⊢
      generalize wordSum n T (pendingBit (r :: rs)) = B at ih2 ⊢
      have hsplit := B9SpliceTableV10d.ofFn_sum_split (fun e : Fin n => if e = r then A else B) (fun _ => B) r
        (by intro i hi; simp [hi])
      rw [if_pos rfl, FiniteUniformStoppingTree.ofFn_sum_const] at hsplit
      have hnB : (n - 1) * B + B = n * B := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      have hsum : (List.ofFn (fun e : Fin n => if e = r then A else B)).sum ≤ A + (n - 1) * B := by omega
      have hP1 : (2 * n - 1) ^ (T + 1) = (2 * n - 1) ^ T * (2 * n - 1) := Nat.pow_succ _ _
      have hK1 : 2 ^ (rs.length + 1) = 2 * 2 ^ rs.length := by rw [Nat.pow_succ, Nat.mul_comm]
      have hT1 : 2 ^ (T + 1) = 2 * 2 ^ T := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hK1, hP1, hT1]
      rw [hK1] at ih2
      generalize (2 * n - 1) ^ T = P at ih1 ih2 ⊢
      generalize 2 ^ rs.length = K at ih1 ih2 ⊢
      generalize 2 ^ T = Q at ih1 ih2 ⊢
      have step1 : 2 * Q * (List.ofFn (fun e : Fin n => if e = r then A else B)).sum ≤ 2 * Q * (A + (n - 1) * B) :=
        Nat.mul_le_mul_left _ hsum
      have e1 : 2 * Q * (A + (n - 1) * B) = 2 * (Q * A) + (2 * (n - 1)) * (Q * B) := by
        rw [Nat.mul_add]
        congr 1 <;> simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have step2 : 2 * (Q * A) + (2 * (n - 1)) * (Q * B) ≤ 2 * (K * P) + (2 * (n - 1)) * (2 * K * P) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ih1) (Nat.mul_le_mul_left _ ih2)
      have e2 : 2 * (K * P) + (2 * (n - 1)) * (2 * K * P) = (2 * K * P) * (1 + 2 * (n - 1)) := by
        simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e3 : 1 + 2 * (n - 1) = 2 * n - 1 := by omega
      have e4 : 2 * K * (P * (2 * n - 1)) = (2 * K * P) * (2 * n - 1) := by
        simp only [Nat.mul_assoc]
      rw [e4, ← e3, ← e2]
      exact Nat.le_trans step1 (by rw [e1]; exact step2)

theorem pending_mass (rs : List (Fin n)) (m : Nat) (hn : 1 ≤ n) (hm : rs.length + 3 ≤ m) :
    8 * wordSum n (2 * n * m) (pendingBit rs) ≤ n ^ (2 * n * m) := by
  have hc := pending_count (2 * n * m) rs
  generalize wordSum n (2 * n * m) (pendingBit rs) = F at hc ⊢
  have hb := B9OrderedWindowMatcher.two_mul_pow_le (2 * n) (by omega)
  have hbm : 2 ^ m * (2 * n - 1) ^ (2 * n * m) ≤ 2 ^ (2 * n * m) * n ^ (2 * n * m) := by
    have e1 : (2 * (2 * n - 1) ^ (2 * n)) ^ m = 2 ^ m * (2 * n - 1) ^ (2 * n * m) := by
      rw [Nat.mul_pow, ← Nat.pow_mul]
    have e2 : ((2 * n) ^ (2 * n)) ^ m = 2 ^ (2 * n * m) * n ^ (2 * n * m) := by
      rw [← Nat.pow_mul, Nat.mul_pow]
    rw [← e1, ← e2]
    exact Nat.pow_le_pow_left hb m
  have hk : 2 ^ m = 2 ^ rs.length * 2 ^ (m - rs.length) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h8 : 8 ≤ 2 ^ (m - rs.length) := by
    have : 2 ^ 3 ≤ 2 ^ (m - rs.length) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hKpos : 0 < 2 ^ rs.length := Nat.two_pow_pos _
  have hQpos : 0 < 2 ^ (2 * n * m) := Nat.two_pow_pos _
  rw [hk] at hbm
  generalize 2 * n * m = T at hc hbm hQpos ⊢
  generalize (2 * n - 1) ^ T = P at hc hbm
  generalize n ^ T = N at hbm ⊢
  generalize 2 ^ T = Q at hc hbm hQpos
  generalize 2 ^ rs.length = K at hc hbm hKpos
  generalize 2 ^ (m - rs.length) = R at hbm h8
  have s1 : (K * R) * (Q * F) ≤ (K * R) * (K * P) := Nat.mul_le_mul_left _ hc
  have s2 : K * ((K * R) * P) ≤ K * (Q * N) := Nat.mul_le_mul_left _ hbm
  have e1 : (K * R) * (K * P) = K * ((K * R) * P) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e2 : (K * R) * (Q * F) = (K * Q) * (R * F) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e3 : K * (Q * N) = (K * Q) * N := by rw [Nat.mul_assoc]
  have s3 : (K * Q) * (R * F) ≤ (K * Q) * N := by
    rw [← e2, ← e3]; rw [e1] at s1; exact Nat.le_trans s1 s2
  have s4 := Nat.le_of_mul_le_mul_left s3 (Nat.mul_pos hKpos hQpos)
  exact Nat.le_trans (Nat.mul_le_mul_right F h8) s4

end B6OrderedCompletion
