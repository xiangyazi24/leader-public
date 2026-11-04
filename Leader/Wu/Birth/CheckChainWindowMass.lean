import Leader.Wu.Birth.CheckChainRing
import Leader.Wu.Splice.MatcherMass

set_option autoImplicit false

/-! # Escape mass of a ready train window under the R1 step

The window of a train starting at `s` is the set of its `psi` cells (`window`).  Every success word of the ordered
window matcher for the train requests (each request hit before any other letter touching the window) has a prefix
whose run agrees on the window with the request run (`B6WindowLocality.success_prefix_agrees`), and the request run
creates a leader on a window cell (`train_requests_leader`); so no success word stays leaderless along all its
prefixes (`success_not_alive`).  With `ordered_mass`, at least a `(3 / (4 t))^(psi-1)` fraction of the words of length
`2 n (psi - 1)` leave the leaderless class, `t` the number of letters touching the window (`train_escape_mass`). -/

namespace BirthCheckChainR1Mass

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open FiniteUniformStoppingTree FixedSpanRenewalPayload B9OrderedWindowMatcher B6WindowLocality B9SpliceTripleHitWords
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring BirthLeaderlessBirthMassRenewal

set_option Elab.async false

variable {n ψ κ τ : Nat}

/-- The cells of the train window. -/
def window (ring : DirectedRing n) (s : Fin n) (ψ : Nat) (i : Fin n) : Bool :=
  (List.range ψ).any (fun k => decide (i = cell ring s k))

theorem window_cell (ring : DirectedRing n) (s : Fin n) {k : Nat} (hk : k < ψ) :
    window ring s ψ (cell ring s k) = true := by
  unfold window
  rw [List.any_eq_true]
  exact ⟨k, List.mem_range.2 hk, by simp⟩

theorem requests_internal (ring : DirectedRing n) (s : Fin n) :
    ∀ a ∈ trainRequests ring s ψ, internalOf ring (window ring s ψ) a = true := by
  intro a ha
  unfold trainRequests at ha
  rw [List.mem_map] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  rw [List.mem_range'_1] at hk
  unfold internalOf
  rw [right_cell, window_cell ring s (by omega), window_cell ring s (by omega)]
  rfl

theorem requests_length (ring : DirectedRing n) (s : Fin n) : (trainRequests ring s ψ).length = ψ - 1 := by
  unfold trainRequests
  rw [List.length_map, List.length_range']

theorem requests_ne_nil (ring : DirectedRing n) (s : Fin n) (h3 : 2 < ψ) : trainRequests ring s ψ ≠ [] := by
  intro h
  have := requests_length (ψ := ψ) ring s
  rw [h] at this
  simp at this
  omega

/-- A success word of the train matcher leaves the leaderless class at some prefix. -/
theorem success_not_alive (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ)
    (s : Fin n) (hready : ∀ k, k < ψ → ReadyCell k (C (cell ring s k))) (u : List (Fin n))
    (hs : runNode (ordStep (touchOf ring (window ring s ψ))) (.active (trainRequests ring s ψ)) u = StopNode.success) :
    aliveBit (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C u = 0 := by
  classical
  obtain ⟨p, hp, hagree⟩ := success_prefix_agrees (step1_pairLocal (kappa := κ) (tau := τ) hψ (by omega) ring)
    (window ring s ψ) (trainRequests ring s ψ) (requests_ne_nil ring s h3) (requests_internal ring s) u hs C
  obtain ⟨k, hk, hlead⟩ := train_requests_leader hψ h3 ring hψn C s hready
  have hpk : (p.foldl (step1 hψ (by omega) ring) C (cell ring s k)).core.core.leader = true := by
    rw [hagree _ (window_cell ring s hk)]; exact hlead
  unfold aliveBit
  rw [if_neg]
  intro halive
  obtain ⟨v, rfl⟩ := hp
  have hsplit := (aliveAlong_append (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C p v).1 halive
  have hgood := aliveAlong_good hsplit.2
  have hf := hgood (cell ring s k)
  rw [hpk] at hf
  exact Bool.noConfusion hf

theorem wordSum_pair_le (T : Nat) (f g : List (Fin n) → Nat) (h : ∀ u, f u + g u ≤ 1) :
    wordSum n T f + wordSum n T g ≤ n ^ T := by
  rw [← rawWord_sum n T f, ← rawWord_sum n T g, ← ofFn_sum_add]
  have hle := ofFn_sum_le (fun i : Fin (n ^ T) => f (rawWord n T i) + g (rawWord n T i)) (fun _ => 1)
    (fun i => h _)
  rw [ofFn_sum_const, Nat.mul_one] at hle
  exact hle

/-- Escape mass of a ready train window: with `t` letters touching the window, the words of length
`2 n (psi - 1)` that stay leaderless along every prefix are at most a `1 - (3 / (4 t))^(psi-1)` fraction. -/
theorem train_escape_mass (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ)
    (s : Fin n) (hready : ∀ k, k < ψ → ReadyCell k (C (cell ring s k))) :
    3 ^ (ψ - 1) * n ^ (2 * n * (ψ - 1)) +
        (4 * touchCount (touchOf ring (window ring s ψ))) ^ (ψ - 1) *
          aliveCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C (2 * n * (ψ - 1)) ≤
      (4 * touchCount (touchOf ring (window ring s ψ))) ^ (ψ - 1) * n ^ (2 * n * (ψ - 1)) := by
  classical
  have hmass := ordered_mass (touchOf ring (window ring s ψ)) (trainRequests ring s ψ) (requests_ne_nil ring s h3)
    (fun a ha => by
      have hi := requests_internal ring s a ha
      simp only [internalOf, Bool.and_eq_true] at hi
      simp [touchOf, hi.1])
  rw [requests_length, ← B9SpliceMatcherMass.wordSum_success_eq_successCount] at hmass
  have hpair := wordSum_pair_le (2 * n * (ψ - 1))
    (aliveBit (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C)
    (fun u => successWeight (runStopped (ordStep (touchOf ring (window ring s ψ)))
      (.active (trainRequests ring s ψ)) u))
    (by
      intro u
      by_cases hsu : runStopped (ordStep (touchOf ring (window ring s ψ))) (.active (trainRequests ring s ψ)) u =
          .success
      · rw [success_not_alive hψ h3 ring hψn C s hready u
          (by rw [B9SpliceMatcherMass.runNode_eq_runStopped]; exact hsu), hsu]
        show 0 + 1 ≤ 1
        exact Nat.le_refl 1
      · have h0 : successWeight (runStopped (ordStep (touchOf ring (window ring s ψ)))
            (.active (trainRequests ring s ψ)) u) = 0 := by
          cases hr : runStopped (ordStep (touchOf ring (window ring s ψ))) (.active (trainRequests ring s ψ)) u with
          | active x => rfl
          | success => exact absurd hr hsu
          | failure => rfl
        rw [h0, Nat.add_zero]
        exact aliveBit_le_one _ _ _ _)
  unfold aliveCount
  generalize wordSum n (2 * n * (ψ - 1)) (aliveBit (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C) = A
    at hpair ⊢
  generalize wordSum n (2 * n * (ψ - 1)) (fun u => successWeight (runStopped (ordStep (touchOf ring (window ring s ψ)))
    (.active (trainRequests ring s ψ)) u)) = B at hpair hmass
  generalize (4 * touchCount (touchOf ring (window ring s ψ))) ^ (ψ - 1) = M at hmass ⊢
  have h1 : M * A + M * B ≤ M * n ^ (2 * n * (ψ - 1)) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hpair
  omega

/-! ## The number of letters touching the window -/

theorem sum_indicator_list (l : List (Fin n)) :
    (List.ofFn (fun e : Fin n => (l.map (fun x => if e = x then 1 else 0)).sum)).sum = l.length := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.sum_nil, List.length_nil]
      rw [ofFn_sum_const, Nat.mul_zero]
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ofFn_sum_add, ofFn_spike' x 1, ih]
      omega

theorem mem_indicator_pos (e : Fin n) : ∀ (l : List (Fin n)), e ∈ l →
    1 ≤ (l.map (fun x => if e = x then 1 else 0)).sum
  | [], h => absurd h List.not_mem_nil
  | x :: l, h => by
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 h with h | h
      · rw [if_pos h]; omega
      · have := mem_indicator_pos e l h; omega

theorem touchCount_le_of_mem (P : Fin n → Bool) (l : List (Fin n)) (h : ∀ e, P e = true → e ∈ l) :
    touchCount P ≤ l.length := by
  unfold touchCount
  rw [← sum_indicator_list l]
  apply ofFn_sum_le
  intro e
  split
  · exact mem_indicator_pos e l (h e ‹_›)
  · exact Nat.zero_le _

theorem right_injective (ring : DirectedRing n) {e x : Fin n} (h : ring.rightNeighbor e = ring.rightNeighbor x) :
    e = x := by
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt; have hx := x.isLt
  rw [mod_two_range _ (by omega), mod_two_range _ (by omega)] at hv
  apply Fin.ext
  split at hv <;> split at hv <;> omega

/-- The window start moved one cell to the left. -/
def leftStart (ring : DirectedRing n) (s : Fin n) : Fin n := ⟨(s.val + n - 1) % n, Nat.mod_lt _ ring.hn⟩

theorem cell_leftStart (ring : DirectedRing n) (s : Fin n) (k : Nat) :
    cell ring (leftStart ring s) (k + 1) = cell ring s k := by
  apply Fin.ext
  simp only [cell, leftStart]
  have hn := ring.hn
  rw [Nat.mod_add_mod, show s.val + n - 1 + (k + 1) = (s.val + k) + n by omega, Nat.add_mod_right]

theorem touchCount_window_le (ring : DirectedRing n) (s : Fin n) :
    touchCount (touchOf ring (window ring s ψ)) ≤ ψ + 1 := by
  have hl : ((List.range (ψ + 1)).map (cell ring (leftStart ring s))).length = ψ + 1 := by
    rw [List.length_map, List.length_range]
  rw [← hl]
  apply touchCount_le_of_mem
  intro e he
  rw [List.mem_map]
  simp only [touchOf, Bool.or_eq_true] at he
  rcases he with he | he
  · unfold window at he
    rw [List.any_eq_true] at he
    obtain ⟨k, hk, hek⟩ := he
    rw [List.mem_range] at hk
    have hek' : e = cell ring s k := of_decide_eq_true hek
    exact ⟨k + 1, List.mem_range.2 (by omega), by rw [cell_leftStart, hek']⟩
  · unfold window at he
    rw [List.any_eq_true] at he
    obtain ⟨k, hk, hek⟩ := he
    rw [List.mem_range] at hk
    have hek' : ring.rightNeighbor e = cell ring s k := of_decide_eq_true hek
    refine ⟨k, List.mem_range.2 (by omega), ?_⟩
    apply right_injective ring
    rw [right_cell, cell_leftStart, hek']

theorem aliveCount_le (step : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Fin n → BirthCheckPermitRepairLeaf.FC n ψ κ τ)
    (Good : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop) (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) (T : Nat) :
    aliveCount step Good C T ≤ n ^ T := by
  have h := wordSum_pair_le T (aliveBit step Good C) (fun _ => 0) (fun u => by
    have := aliveBit_le_one step Good C u; omega)
  unfold aliveCount
  omega

/-- Escape mass of a ready train window with the explicit window constant: at most a
`1 - (3 / (4 (psi + 1)))^(psi-1)` fraction of the words of length `2 n (psi - 1)` stay leaderless. -/
theorem train_escape_mass_explicit (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n)
    (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) (s : Fin n)
    (hready : ∀ k, k < ψ → ReadyCell k (C (cell ring s k))) :
    3 ^ (ψ - 1) * n ^ (2 * n * (ψ - 1)) +
        (4 * (ψ + 1)) ^ (ψ - 1) *
          aliveCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C (2 * n * (ψ - 1)) ≤
      (4 * (ψ + 1)) ^ (ψ - 1) * n ^ (2 * n * (ψ - 1)) := by
  have hm := train_escape_mass hψ h3 ring hψn C s hready
  have hA := aliveCount_le (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C (2 * n * (ψ - 1))
  have ht := touchCount_window_le (ψ := ψ) ring s
  have hM : (4 * touchCount (touchOf ring (window ring s ψ))) ^ (ψ - 1) ≤ (4 * (ψ + 1)) ^ (ψ - 1) :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left 4 ht) _
  generalize aliveCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C (2 * n * (ψ - 1)) = A
    at hm hA ⊢
  generalize n ^ (2 * n * (ψ - 1)) = N at hm hA ⊢
  generalize (4 * touchCount (touchOf ring (window ring s ψ))) ^ (ψ - 1) = M at hm hM
  generalize (4 * (ψ + 1)) ^ (ψ - 1) = M' at hM ⊢
  obtain ⟨d, rfl⟩ : ∃ d, M' = M + d := ⟨M' - M, by omega⟩
  have hdA : d * A ≤ d * N := Nat.mul_le_mul_left d hA
  rw [Nat.add_mul, Nat.add_mul]
  omega

end BirthCheckChainR1Mass
