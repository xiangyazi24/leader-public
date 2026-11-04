import Leader.PPL.Elim.LiteralInterface
import Leader.PPL.Probability.FixedWord
import Init.Omega

/-!
# Lemma 17 with a short explicit word: the Algorithm-5 deletion macro

For every literal Algorithm-5 configuration `D` (four-field row E) satisfying
`PPL.Elim.PB`, some scheduler word of length at most `5 * n * n` drives the
literal process to exactly one leader (`literalPB_oneLeader_exists_short`).
At `n = 8` the bound is `320`.

Route: "Deterministic Algorithm-5 deletion
macro"), checked line by line against `PPL.Elim.rowE` (Algorithm 5,
lines 51--62).  For consecutive leaders `A`, `B = A + d2`,
`C = B + d1` (no leaders strictly inside either arc):

1. `arm(B, C)`: forward sweep of the edges `B, B+1, ..., C-1` (this clears
   every initiator bullet on the arc and, by line 62, sets
   `signalB` at `C-1` if `C` survives); if `B.signalB` is still false, a
   backward sweep `C-2, ..., B` carries `signalB` to `B` (no bullet can eat it,
   no cell fires).
2. Edge `B-1`: `B` is the responder with `signalB`, so lines 53--54 make it
   fire a dummy and become unshielded (`shield = false`, `signalB = false`).
3. `arm(A, B)`: same sweeps on the arc `A..B`; `B` is touched only as a
   responder without `signalB`, so it stays unshielded.
4. Chase: edges `A, A+1, ..., B-1`.  `A` fires live (line 52), the live
   bullet moves over the cleared arc, and at `B` line 57 deletes `B`.

Any leader deletion during steps 1--3 is already progress.  Each deletion
costs at most `2 d1 + 1 + 3 d2 ≤ 5 n` letters.

Correction to the text: step 1 of its `arm(X, Y)` says "if
`X.signalB = true`, do nothing".  In that branch the arc is not cleared, so in
step 3 the live bullet can be dropped on a collision (e.g. `A.signalB = true`,
`A+1` holding a dummy, `B = A+2`: the live bullet is discarded by line 58,
the dummy reaches `B`, and `B` survives).  Here the forward sweep is always
performed; the early stop is taken only after the forward sweep.

Leader count is monotone and drops by at most one per step, so a shortest
prefix of a count-decreasing word decreases the count by exactly one; hence
the process stops at exactly one leader and PB is used only for "at least
one leader".
-/

namespace PPL.Convergence.L17Macro

set_option autoImplicit false
set_option Elab.async false

open PPL.Elim
open PPL.Convergence.LDLocal (advance advance_zero)

/-! ## Row-E facts (Algorithm 5, lines 51--62) -/

private theorem fin3_cases (b : Fin 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
  rcases b with ⟨v, hv⟩
  have : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp

/-- A cell carrying a live bullet, or a leader about to fire one. -/
def Armed (c : Cell4) : Prop :=
  (c.leader = true ∧ c.signalB = true) ∨ c.bullet = 2

/-- Line 61: the initiator always ends with no bullet. -/
theorem rowE_left_bullet (l r : Cell4) : (rowE l r).1.bullet = 0 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;>
  rfl

/-- Line 62: a responder that is a leader after the step gives the initiator
`signalB`. -/
theorem rowE_signal_or (l r : Cell4) :
    (rowE l r).2.leader = false ∨ (rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;>
  first | exact Or.inl rfl | exact Or.inr rfl

/-- Backward propagation: a non-firing, bullet-free initiator next to a
non-leader responder carrying `signalB` only acquires `signalB`. -/
theorem rowE_backward (l r : Cell4)
    (hnf : l.leader = true → l.signalB = false) (hb : l.bullet = 0)
    (hrl : r.leader = false) (hrs : r.signalB = true) :
    rowE l r = ({ l with signalB := true }, r) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  simp only at hnf hb hrl hrs
  subst hb hrl hrs
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rsh <;>
  first | rfl | exact absurd (hnf rfl) (by simp)

/-- Lines 53--54: a leader responder with `signalB` fires a dummy and ends
unshielded with `signalB = false` (whether or not it survives). -/
theorem rowE_dummy (l r : Cell4) (hr : r.leader = true) (hs : r.signalB = true) :
    (rowE l r).2.shield = false ∧ (rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  simp only at hr hs
  subst hr hs
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rsh <;>
  exact ⟨rfl, rfl⟩

/-- A leader responder without `signalB` keeps its shield and `signalB`. -/
theorem rowE_leader_frame (l r : Cell4) (hr : r.leader = true) (hs : r.signalB = false) :
    (rowE l r).2.shield = r.shield ∧ (rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  simp only at hr hs
  subst hr hs
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rsh <;>
  exact ⟨rfl, rfl⟩

/-- Lines 52, 58--59: an armed initiator hands a live bullet to an empty
non-leader responder. -/
theorem rowE_carry (l r : Cell4) (hrl : r.leader = false) (hrb : r.bullet = 0)
    (harm : Armed l) : (rowE l r).2.bullet = 2 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  unfold Armed at harm
  simp only at hrl hrb harm
  subst hrl hrb
  rcases harm with ⟨rfl, rfl⟩ | rfl
  · rcases fin3_cases lb with rfl | rfl | rfl <;>
    cases lsh <;> cases rsb <;> cases rsh <;> rfl
  · cases ll <;> cases lsb <;> cases lsh <;> cases rsb <;> cases rsh <;> rfl

/-- Line 57: an armed initiator deletes an unshielded leader responder
without `signalB`. -/
theorem rowE_kill (l r : Cell4) (hr : r.leader = true) (hs : r.signalB = false)
    (hsh : r.shield = false) (harm : Armed l) :
    (rowE l r).2.leader = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  unfold Armed at harm
  simp only at hr hs hsh harm
  subst hr hs hsh
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;>
  simp_all [rowE]

/-! ## Steps, runs, frames -/

variable {n : Nat}

/-- One literal row-E interaction on edge `e`. -/
def stE (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n) : Fin n → Cell4 :=
  PopulationProtocol.step protocolE ring C e

/-- The literal run of a scheduler word (the project's `runPopulationSchedule`). -/
def runW (ring : DirectedRing n) (C : Fin n → Cell4) (w : List (Fin n)) :
    Fin n → Cell4 :=
  PPL.Probability.runPopulationSchedule protocolE ring C w

theorem stE_apply (ring : DirectedRing n) (C : Fin n → Cell4) (e k : Fin n) :
    stE ring C e k =
      if k = e then (rowE (C e) (C (ring.rightNeighbor e))).1
      else if k = ring.rightNeighbor e then (rowE (C e) (C (ring.rightNeighbor e))).2
      else C k := rfl

theorem stE_left (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n) :
    stE ring C e e = (rowE (C e) (C (ring.rightNeighbor e))).1 := by
  rw [stE_apply, if_pos rfl]

theorem stE_right (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n)
    (h : ring.rightNeighbor e ≠ e) :
    stE ring C e (ring.rightNeighbor e) = (rowE (C e) (C (ring.rightNeighbor e))).2 := by
  rw [stE_apply, if_neg h, if_pos rfl]

theorem stE_frame (ring : DirectedRing n) (C : Fin n → Cell4) (e k : Fin n)
    (h1 : k ≠ e) (h2 : k ≠ ring.rightNeighbor e) : stE ring C e k = C k := by
  rw [stE_apply, if_neg h1, if_neg h2]

theorem stE_setSig (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n)
    (h : rowE (C e) (C (ring.rightNeighbor e)) =
      ({ C e with signalB := true }, C (ring.rightNeighbor e))) (k : Fin n) :
    stE ring C e k = if k = e then { C e with signalB := true } else C k := by
  rw [stE_apply, h]
  by_cases hk : k = e
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    by_cases hk2 : k = ring.rightNeighbor e
    · rw [if_pos hk2, hk2]
    · rw [if_neg hk2]

theorem runW_nil (ring : DirectedRing n) (C : Fin n → Cell4) : runW ring C [] = C := rfl

theorem runW_cons (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n) (w : List (Fin n)) :
    runW ring C (e :: w) = runW ring (stE ring C e) w := rfl

theorem runW_append (ring : DirectedRing n) :
    ∀ (w1 w2 : List (Fin n)) (C : Fin n → Cell4),
      runW ring C (w1 ++ w2) = runW ring (runW ring C w1) w2
  | [], _, _ => rfl
  | e :: w1, w2, C => by
      show runW ring (stE ring C e) (w1 ++ w2) = runW ring (runW ring (stE ring C e) w1) w2
      exact runW_append ring w1 w2 (stE ring C e)

theorem runW_frame (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : Fin n → Cell4) (k : Fin n),
      (∀ e ∈ w, k ≠ e ∧ k ≠ ring.rightNeighbor e) → runW ring C w k = C k
  | [], _, _, _ => rfl
  | e :: w, C, k, h => by
      rw [runW_cons, runW_frame ring w (stE ring C e) k
        (fun e' he' => h e' (List.mem_cons.mpr (Or.inr he')))]
      have he := h e (List.mem_cons.mpr (Or.inl rfl))
      exact stE_frame ring C e k he.1 he.2

theorem stE_leader_mono (ring : DirectedRing n) (C : Fin n → Cell4) (e k : Fin n)
    (h : (stE ring C e k).leader = true) : (C k).leader = true := by
  cases hk : (C k).leader with
  | true => rfl
  | false =>
      have h2 : (stE ring C e k).leader = false :=
        PPL.Convergence.LDLocal.stepE_leader_false_of_false ring C e k hk
      rw [h2] at h
      cases h

theorem runW_leader_mono (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : Fin n → Cell4) (k : Fin n),
      (runW ring C w k).leader = true → (C k).leader = true
  | [], _, _, h => h
  | e :: w, C, k, h =>
      stE_leader_mono ring C e k (runW_leader_mono ring w (stE ring C e) k h)

theorem runW_leader_false (ring : DirectedRing n) (C : Fin n → Cell4)
    (w : List (Fin n)) (k : Fin n) (h : (C k).leader = false) :
    (runW ring C w k).leader = false := by
  cases hr : (runW ring C w k).leader with
  | false => rfl
  | true =>
      have := runW_leader_mono ring w C k hr
      rw [h] at this
      cases this

/-! ## Leader-count facts -/

theorem ofFn_sum_lt (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) (j : Fin n)
    (hj : f j < g j) : (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      have hrest := FiniteUniformStoppingTree.ofFn_sum_le
        (fun i : Fin n => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
      have h0 := h 0
      revert hj
      refine Fin.cases ?_ (fun i => ?_) j
      · intro hj
        omega
      · intro hi
        have := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ) i hi
        omega

theorem ofFn_sum_le_one (f : Fin n → Nat) (hle : ∀ i, f i ≤ 1) (X : Fin n)
    (hz : ∀ i, i ≠ X → f i = 0) : (List.ofFn f).sum ≤ 1 := by
  induction n with
  | zero => exact Fin.elim0 X
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons]
      revert hz
      refine Fin.cases ?_ (fun x => ?_) X
      · intro hz
        have htail : (List.ofFn fun i : Fin n => f i.succ).sum ≤
            (List.ofFn fun _ : Fin n => 0).sum :=
          FiniteUniformStoppingTree.ofFn_sum_le _ _
            (fun i => by rw [hz i.succ (Fin.succ_ne_zero i)]; exact Nat.le_refl 0)
        rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] at htail
        have := hle 0
        omega
      · intro hz
        have h0 : f 0 = 0 := hz 0 (fun h => Fin.succ_ne_zero x h.symm)
        have htail := ih (fun i => f i.succ) (fun i => hle i.succ) x
          (fun i hi => hz i.succ (fun h => hi (Fin.succ_inj.mp h)))
        omega

theorem lc_eq (C : Fin n → Cell4) :
    leaderCount C = (List.ofFn fun i => if (C i).leader = true then 1 else 0).sum := rfl

theorem lc_lt_of_kill (C' C : Fin n → Cell4)
    (hmono : ∀ k, (C' k).leader = true → (C k).leader = true)
    (j : Fin n) (hj : (C j).leader = true) (hj' : (C' j).leader = false) :
    leaderCount C' < leaderCount C := by
  rw [lc_eq, lc_eq]
  refine ofFn_sum_lt _ _ (fun i => ?_) j ?_
  · by_cases h1 : (C' i).leader = true
    · rw [if_pos h1, if_pos (hmono i h1)]
      exact Nat.le_refl _
    · rw [if_neg h1]
      exact Nat.zero_le _
  · rw [if_neg (by rw [hj']; exact Bool.false_ne_true), if_pos hj]
    exact Nat.zero_lt_one

theorem lc_pos (C : Fin n → Cell4) (j : Fin n) (hj : (C j).leader = true) :
    0 < leaderCount C := by
  have h := ofFn_sum_lt (fun _ : Fin n => 0)
    (fun i => if (C i).leader = true then 1 else 0)
    (fun _ => Nat.zero_le _) j (by rw [if_pos hj]; exact Nat.zero_lt_one)
  rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] at h
  rw [lc_eq]
  exact h

theorem lc_zero_of_none (C : Fin n → Cell4) (h : ∀ i, (C i).leader = false) :
    leaderCount C = 0 := by
  rw [lc_eq]
  have hle := FiniteUniformStoppingTree.ofFn_sum_le
    (fun i => if (C i).leader = true then 1 else 0) (fun _ : Fin n => 0)
    (fun i => by rw [h i]; exact Nat.le_refl _)
  rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] at hle
  omega

theorem lc_le_n (C : Fin n → Cell4) : leaderCount C ≤ n := by
  rw [lc_eq]
  have hle := FiniteUniformStoppingTree.ofFn_sum_le
    (fun i => if (C i).leader = true then 1 else 0) (fun _ : Fin n => 1)
    (fun i => by split <;> omega)
  rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_one] at hle
  exact hle

theorem lc_le_one_of_unique (C : Fin n → Cell4) (X : Fin n)
    (h : ∀ i, (C i).leader = true → i = X) : leaderCount C ≤ 1 := by
  rw [lc_eq]
  refine ofFn_sum_le_one _ (fun i => by split <;> omega) X (fun i hne => ?_)
  by_cases hi : (C i).leader = true
  · exact absurd (h i hi) hne
  · rw [if_neg hi]

theorem lc_runW_le (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : Fin n → Cell4), leaderCount (runW ring C w) ≤ leaderCount C
  | [], _ => Nat.le_refl _
  | e :: w, C => by
      rw [runW_cons]
      have h1 : leaderCount (stE ring C e) ≤ leaderCount C := leaderCount_step_le ring C e
      exact Nat.le_trans (lc_runW_le ring w (stE ring C e)) h1

theorem alive_of_not_lt (ring : DirectedRing n) (C : Fin n → Cell4) (w : List (Fin n))
    (h : ¬ leaderCount (runW ring C w) < leaderCount C) (k : Fin n)
    (hk : (C k).leader = true) : (runW ring C w k).leader = true := by
  cases hr : (runW ring C w k).leader with
  | true => rfl
  | false =>
      exact absurd (lc_lt_of_kill (runW ring C w) C
        (fun j hj => runW_leader_mono ring w C j hj) k hk hr) h

/-! ## Ring positions -/

theorem rn_adv (ring : DirectedRing n) (i : Fin n) (q : Nat) :
    ring.rightNeighbor (advance ring i q) = advance ring i (q + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor advance
  dsimp only
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem adv_inj (ring : DirectedRing n) (i : Fin n) {a b : Nat} (ha : a < n) (hb : b < n)
    (h : advance ring i a = advance ring i b) : a = b := by
  have hv := congrArg Fin.val h
  unfold advance at hv
  dsimp only at hv
  by_cases hia : i.val + a < n
  · rw [Nat.mod_eq_of_lt hia] at hv
    by_cases hib : i.val + b < n
    · rw [Nat.mod_eq_of_lt hib] at hv
      omega
    · have hge : n ≤ i.val + b := by omega
      have hlt : i.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at hv
      omega
  · have hgea : n ≤ i.val + a := by omega
    have hlta : i.val + a - n < n := by omega
    rw [Nat.mod_eq_sub_mod hgea, Nat.mod_eq_of_lt hlta] at hv
    by_cases hib : i.val + b < n
    · rw [Nat.mod_eq_of_lt hib] at hv
      omega
    · have hgeb : n ≤ i.val + b := by omega
      have hltb : i.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hgeb, Nat.mod_eq_of_lt hltb] at hv
      omega

theorem adv_ne (ring : DirectedRing n) (i : Fin n) {a b : Nat} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : advance ring i a ≠ advance ring i b :=
  fun h => hab (adv_inj ring i ha hb h)

theorem exists_adv_eq (ring : DirectedRing n) (X Z : Fin n) :
    ∃ t, t < n ∧ advance ring X t = Z := by
  refine ⟨(Z.val + n - X.val) % n, Nat.mod_lt _ ring.hn, ?_⟩
  apply Fin.ext
  unfold advance
  dsimp only
  rw [Nat.add_mod_mod]
  have h : X.val + (Z.val + n - X.val) = Z.val + n := by
    have := X.isLt
    omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt Z.isLt]

theorem exists_min (P : Nat → Prop) :
    ∀ t, (∃ s, 1 ≤ s ∧ s ≤ t ∧ P s) →
      ∃ d, 1 ≤ d ∧ d ≤ t ∧ P d ∧ ∀ s, 1 ≤ s → s < d → ¬ P s
  | 0, ⟨s, h1, h2, _⟩ => absurd h2 (by omega)
  | t + 1, h => by
      rcases Classical.em (∃ s, 1 ≤ s ∧ s ≤ t ∧ P s) with hlow | hlow
      · obtain ⟨d, h1, h2, h3, h4⟩ := exists_min P t hlow
        exact ⟨d, h1, by omega, h3, h4⟩
      · obtain ⟨s, h1, h2, h3⟩ := h
        have hs : s = t + 1 :=
          Classical.byContradiction fun hne => hlow ⟨s, h1, by omega, h3⟩
        rw [hs] at h3 h1
        exact ⟨t + 1, h1, Nat.le_refl _, h3,
          fun s' h1' h2' hp => hlow ⟨s', h1', by omega, hp⟩⟩

/-- The next leader clockwise after `X`, given some other leader `Z`. -/
theorem exists_next_leader (ring : DirectedRing n) (C : Fin n → Cell4) (X Z : Fin n)
    (hZ : (C Z).leader = true) (hne : Z ≠ X) :
    ∃ d, 1 ≤ d ∧ d < n ∧ (C (advance ring X d)).leader = true ∧
      ∀ s, 1 ≤ s → s < d → (C (advance ring X s)).leader = false := by
  obtain ⟨t, ht, hZt⟩ := exists_adv_eq ring X Z
  have ht1 : 1 ≤ t := by
    refine Nat.pos_of_ne_zero fun h0 => hne ?_
    rw [← hZt, h0, advance_zero]
  obtain ⟨d, h1, h2, h3, h4⟩ :=
    exists_min (fun s => (C (advance ring X s)).leader = true) t
      ⟨t, ht1, Nat.le_refl _, by rw [hZt]; exact hZ⟩
  exact ⟨d, h1, by omega, h3, fun s hs1 hs2 => by simpa using h4 s hs1 hs2⟩

/-! ## Forward sweep `X, X+1, ..., X+t-1` -/

/-- Forward sweep word: edges `X+0, ..., X+(t-1)` in clockwise order. -/
def fwd (ring : DirectedRing n) (X : Fin n) : Nat → List (Fin n)
  | 0 => []
  | t + 1 => fwd ring X t ++ [advance ring X t]

/-- Backward sweep word: edges `X+(m-1), ..., X+0`. -/
def bwd (ring : DirectedRing n) (X : Fin n) : Nat → List (Fin n)
  | 0 => []
  | m + 1 => advance ring X m :: bwd ring X m

theorem fwd_length (ring : DirectedRing n) (X : Fin n) : ∀ t, (fwd ring X t).length = t
  | 0 => rfl
  | t + 1 => by simp [fwd, fwd_length ring X t]

theorem bwd_length (ring : DirectedRing n) (X : Fin n) : ∀ m, (bwd ring X m).length = m
  | 0 => rfl
  | m + 1 => by simp [bwd, bwd_length ring X m]

theorem fwd_mem (ring : DirectedRing n) (X : Fin n) :
    ∀ t e, e ∈ fwd ring X t → ∃ s, s < t ∧ e = advance ring X s
  | 0, e, h => by simp [fwd] at h
  | t + 1, e, h => by
      simp only [fwd, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨s, hs, he⟩ := fwd_mem ring X t e h
        exact ⟨s, by omega, he⟩
      · exact ⟨t, by omega, h⟩

theorem runW_fwd_succ (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) (t : Nat) :
    runW ring C (fwd ring X (t + 1)) =
      stE ring (runW ring C (fwd ring X t)) (advance ring X t) := by
  show runW ring C (fwd ring X t ++ [advance ring X t]) = _
  rw [runW_append]
  rfl

theorem fwd_frame (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) (t : Nat)
    (k : Fin n) (hk : ∀ s, s < t → k ≠ advance ring X s ∧ k ≠ advance ring X (s + 1)) :
    runW ring C (fwd ring X t) k = C k := by
  apply runW_frame
  intro e he
  obtain ⟨s, hs, rfl⟩ := fwd_mem ring X t e he
  rw [rn_adv]
  exact hk s hs

/-- After the forward sweep of length `t < n`, every swept initiator site is
bullet-free (line 61). -/
theorem fwd_bullets (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) :
    ∀ t, t < n → ∀ s, s < t → (runW ring C (fwd ring X t) (advance ring X s)).bullet = 0 := by
  intro t
  induction t with
  | zero => intro _ s hs; exact absurd hs (Nat.not_lt_zero s)
  | succ t ih =>
      intro ht s hs
      rw [runW_fwd_succ]
      by_cases hst : s = t
      · rw [hst, stE_left]
        exact rowE_left_bullet _ _
      · have h1 : advance ring X s ≠ advance ring X t := adv_ne ring X (by omega) (by omega) hst
        have h2 : advance ring X s ≠ ring.rightNeighbor (advance ring X t) := by
          rw [rn_adv]; exact adv_ne ring X (by omega) ht (by omega)
        rw [stE_frame _ _ _ _ h1 h2]
        exact ih (by omega) s (by omega)

/-- Last forward edge: either the target leader died, or line 62 put
`signalB` on its predecessor. -/
theorem fwd_signal (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) (m : Nat)
    (hm : m + 1 < n) :
    (runW ring C (fwd ring X (m + 1)) (advance ring X (m + 1))).leader = false ∨
      (runW ring C (fwd ring X (m + 1)) (advance ring X m)).signalB = true := by
  have hne : ring.rightNeighbor (advance ring X m) ≠ advance ring X m := by
    rw [rn_adv]; exact adv_ne ring X hm (by omega) (by omega)
  rw [runW_fwd_succ, ← rn_adv ring X m, stE_left, stE_right _ _ _ hne]
  exact rowE_signal_or _ _

/-- The target leader of a forward sweep, if it has no `signalB`, keeps its
shield and `signalB = false`. -/
theorem fwd_target (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) (m : Nat)
    (hm : m + 1 < n) (hY : (C (advance ring X (m + 1))).leader = true)
    (hYs : (C (advance ring X (m + 1))).signalB = false) :
    (runW ring C (fwd ring X (m + 1)) (advance ring X (m + 1))).shield =
        (C (advance ring X (m + 1))).shield ∧
      (runW ring C (fwd ring X (m + 1)) (advance ring X (m + 1))).signalB = false := by
  have hne : ring.rightNeighbor (advance ring X m) ≠ advance ring X m := by
    rw [rn_adv]; exact adv_ne ring X hm (by omega) (by omega)
  have hfr : runW ring C (fwd ring X m) (advance ring X (m + 1)) = C (advance ring X (m + 1)) :=
    fwd_frame ring X C m _ (fun s hs =>
      ⟨adv_ne ring X hm (by omega) (by omega), adv_ne ring X hm (by omega) (by omega)⟩)
  rw [runW_fwd_succ, ← rn_adv ring X m, stE_right _ _ _ hne, rn_adv, hfr]
  rw [rn_adv] at hne
  exact rowE_leader_frame _ _ hY hYs

/-! ## Backward sweep -/

/-- Backward sweep `X+(m-1), ..., X+0`: with `signalB` at `X+m`, no leader in
`X+1..X+m`, no bullets on `X..X+(m-1)` and `X` not about to fire, each step
only sets `signalB` on its initiator. -/
theorem bwd_run (ring : DirectedRing n) (X : Fin n) :
    ∀ m, m < n → ∀ C : Fin n → Cell4,
      (∀ s, 1 ≤ s → s ≤ m → (C (advance ring X s)).leader = false) →
      (∀ s, s < m → (C (advance ring X s)).bullet = 0) →
      (0 < m → (C X).leader = true → (C X).signalB = false) →
      (C (advance ring X m)).signalB = true →
      (∀ s, s < m → runW ring C (bwd ring X m) (advance ring X s) =
          { C (advance ring X s) with signalB := true }) ∧
      (∀ k, (∀ s, s < m → k ≠ advance ring X s) → runW ring C (bwd ring X m) k = C k) := by
  intro m
  induction m with
  | zero =>
      intro _ C _ _ _ _
      exact ⟨fun s hs => absurd hs (Nat.not_lt_zero s), fun _ _ => rfl⟩
  | succ m ih =>
      intro hm C hlead hbul hX hsig
      have hne : ring.rightNeighbor (advance ring X m) ≠ advance ring X m := by
        rw [rn_adv]; exact adv_ne ring X hm (by omega) (by omega)
      have hrow : rowE (C (advance ring X m)) (C (ring.rightNeighbor (advance ring X m))) =
          ({ C (advance ring X m) with signalB := true },
            C (ring.rightNeighbor (advance ring X m))) := by
        apply rowE_backward
        · intro hl
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · rw [h0, advance_zero] at hl ⊢
            exact hX (by omega) hl
          · have := hlead m hpos (by omega)
            rw [this] at hl
            cases hl
        · exact hbul m (by omega)
        · rw [rn_adv]; exact hlead (m + 1) (by omega) (Nat.le_refl _)
        · rw [rn_adv]; exact hsig
      have hC1 := stE_setSig ring C (advance ring X m) hrow
      have hC1pm : stE ring C (advance ring X m) (advance ring X m) =
          { C (advance ring X m) with signalB := true } := by
        rw [hC1, if_pos rfl]
      have hC1o : ∀ k, k ≠ advance ring X m → stE ring C (advance ring X m) k = C k := by
        intro k hk
        rw [hC1, if_neg hk]
      have hC1l : ∀ k, (stE ring C (advance ring X m) k).leader = (C k).leader := by
        intro k
        by_cases hk : k = advance ring X m
        · rw [hk, hC1pm]
        · rw [hC1o k hk]
      have hC1b : ∀ k, (stE ring C (advance ring X m) k).bullet = (C k).bullet := by
        intro k
        by_cases hk : k = advance ring X m
        · rw [hk, hC1pm]
        · rw [hC1o k hk]
      obtain ⟨ha, hb⟩ := ih (by omega) (stE ring C (advance ring X m))
        (fun s h1 h2 => by rw [hC1l]; exact hlead s h1 (by omega))
        (fun s hs => by rw [hC1b]; exact hbul s (by omega))
        (fun hpos => by
          have hXne : X ≠ advance ring X m := by
            intro h
            have := adv_inj ring X (a := 0) (b := m) (by omega) (by omega)
              (by rw [advance_zero]; exact h)
            omega
          rw [hC1o X hXne]
          exact hX (by omega))
        (by rw [hC1pm])
      have hrun : runW ring C (bwd ring X (m + 1)) =
          runW ring (stE ring C (advance ring X m)) (bwd ring X m) := rfl
      rw [hrun]
      constructor
      · intro s hs
        rcases Nat.lt_or_ge s m with hsm | hsm
        · rw [ha s hsm, hC1o _ (adv_ne ring X (by omega) (by omega) (by omega))]
        · have hs' : s = m := by omega
          rw [hs', hb _ (fun s' hs' => adv_ne ring X (by omega) (by omega) (by omega)), hC1pm]
      · intro k hk
        rw [hb k (fun s hs => hk s (by omega)), hC1o k (hk m (by omega))]

/-! ## arm(X, Y) -/

/--
`arm(X, Y)` for a cell `X` (in use, a leader) and the next leader `Y = X + d` (no leaders
strictly between).  Some word of length at most `2 d` either lowers the
leader count, or leaves `X.signalB = true`, the arc `X..Y-1` bullet-free, and
(if `Y` had no `signalB`) `Y`'s shield unchanged and `Y.signalB = false`.
-/
theorem arm (ring : DirectedRing n) (C : Fin n → Cell4) (X : Fin n) (d : Nat)
    (hd1 : 1 ≤ d) (hdn : d < n)
    (hY : (C (advance ring X d)).leader = true)
    (hmid : ∀ s, 1 ≤ s → s < d → (C (advance ring X s)).leader = false) :
    ∃ w : List (Fin n), w.length ≤ 2 * d ∧
      (leaderCount (runW ring C w) < leaderCount C ∨
        ((runW ring C w X).signalB = true ∧
          (∀ s, s < d → (runW ring C w (advance ring X s)).bullet = 0) ∧
          ((C (advance ring X d)).signalB = false →
            (runW ring C w (advance ring X d)).shield = (C (advance ring X d)).shield ∧
            (runW ring C w (advance ring X d)).signalB = false))) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  by_cases hprog : leaderCount (runW ring C (fwd ring X (m + 1))) < leaderCount C
  · exact ⟨fwd ring X (m + 1), by rw [fwd_length]; omega, Or.inl hprog⟩
  have hsig : (runW ring C (fwd ring X (m + 1)) (advance ring X m)).signalB = true := by
    rcases fwd_signal ring X C m hdn with h | h
    · have := alive_of_not_lt ring C _ hprog _ hY
      rw [h] at this
      cases this
    · exact h
  have hYpost := fwd_target ring X C m hdn hY
  have hbul := fwd_bullets ring X C (m + 1) hdn
  by_cases hXs : (runW ring C (fwd ring X (m + 1)) X).signalB = true
  · exact ⟨fwd ring X (m + 1), by rw [fwd_length]; omega, Or.inr ⟨hXs, hbul, hYpost⟩⟩
  · have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · have hX1 : (runW ring C (fwd ring X (m + 1)) X).signalB = true := by
          rw [h0] at hsig ⊢
          rw [advance_zero] at hsig
          exact hsig
        exact absurd hX1 hXs
      · exact h0
    obtain ⟨ha, hb⟩ := bwd_run ring X m (by omega) (runW ring C (fwd ring X (m + 1)))
      (fun s h1 h2 => runW_leader_false ring C _ _ (hmid s h1 (by omega)))
      (fun s hs => hbul s (by omega))
      (fun _ _ => by simpa using hXs)
      hsig
    refine ⟨fwd ring X (m + 1) ++ bwd ring X m,
      by rw [List.length_append, fwd_length, bwd_length]; omega, Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [runW_append]
      have h0 := ha 0 hm
      rw [advance_zero] at h0
      rw [h0]
    · intro s hs
      rw [runW_append]
      rcases Nat.lt_or_ge s m with hsm | hsm
      · rw [ha s hsm]
        exact hbul s (by omega)
      · have hs' : s = m := by omega
        rw [hs', hb _ (fun s' hs' => adv_ne ring X (by omega) (by omega) (by omega))]
        exact hbul m (by omega)
    · intro hYs
      rw [runW_append, hb _ (fun s' hs' => adv_ne ring X (by omega) (by omega) (by omega))]
      exact hYpost hYs

/-! ## Chase -/

theorem chase_inv (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) (d : Nat)
    (hdn : d < n)
    (harm : (C X).leader = true ∧ (C X).signalB = true)
    (hmid : ∀ s, 1 ≤ s → s < d → (C (advance ring X s)).leader = false)
    (hbul : ∀ s, 1 ≤ s → s < d → (C (advance ring X s)).bullet = 0) :
    ∀ t, t < d →
      Armed (runW ring C (fwd ring X t) (advance ring X t)) ∧
      (∀ s, t < s → s < d → (runW ring C (fwd ring X t) (advance ring X s)).bullet = 0) ∧
      runW ring C (fwd ring X t) (advance ring X d) = C (advance ring X d) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨?_, fun s h1 h2 => hbul s (by omega) h2, rfl⟩
      show Armed (C (advance ring X 0))
      rw [advance_zero]
      exact Or.inl harm
  | succ t ih =>
      intro ht
      obtain ⟨ha, hb, hf⟩ := ih (by omega)
      have hne : ring.rightNeighbor (advance ring X t) ≠ advance ring X t := by
        rw [rn_adv]; exact adv_ne ring X (by omega) (by omega) (by omega)
      rw [runW_fwd_succ]
      refine ⟨?_, ?_, ?_⟩
      · rw [← rn_adv ring X t, stE_right _ _ _ hne]
        apply Or.inr
        apply rowE_carry
        · rw [rn_adv]
          exact runW_leader_false ring C _ _ (hmid (t + 1) (by omega) ht)
        · rw [rn_adv]
          exact hb (t + 1) (by omega) ht
        · exact ha
      · intro s h1 h2
        rw [stE_frame _ _ _ _ (adv_ne ring X (by omega) (by omega) (by omega))
          (by rw [rn_adv]; exact adv_ne ring X (by omega) (by omega) (by omega))]
        exact hb s (by omega) h2
      · rw [stE_frame _ _ _ _ (adv_ne ring X hdn (by omega) (by omega))
          (by rw [rn_adv]; exact adv_ne ring X hdn (by omega) (by omega))]
        exact hf

/-- The chase: an armed leader `X`, a cleared leader-free arc, and an
unshielded leader `Y = X + d` without `signalB`; the forward sweep deletes `Y`. -/
theorem chase (ring : DirectedRing n) (X : Fin n) (C : Fin n → Cell4) (d : Nat)
    (hd1 : 1 ≤ d) (hdn : d < n)
    (harm : (C X).leader = true ∧ (C X).signalB = true)
    (hmid : ∀ s, 1 ≤ s → s < d → (C (advance ring X s)).leader = false)
    (hbul : ∀ s, 1 ≤ s → s < d → (C (advance ring X s)).bullet = 0)
    (hY : (C (advance ring X d)).leader = true)
    (hYs : (C (advance ring X d)).signalB = false)
    (hYsh : (C (advance ring X d)).shield = false) :
    (runW ring C (fwd ring X d) (advance ring X d)).leader = false := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ha, _, hf⟩ := chase_inv ring X C (m + 1) hdn harm hmid hbul m (by omega)
  have hne : ring.rightNeighbor (advance ring X m) ≠ advance ring X m := by
    rw [rn_adv]; exact adv_ne ring X hdn (by omega) (by omega)
  rw [runW_fwd_succ, ← rn_adv ring X m, stE_right _ _ _ hne]
  rw [rn_adv] at hne ⊢
  rw [hf]
  exact rowE_kill _ _ hY hYs hYsh ha

/-! ## One deletion -/

/--
One deletion of the macro.  `A` a leader, `A + d2` the next leader, and
`(A + d2) + d1` the leader after that.  A word of length at most `5 n`
strictly lowers the leader count.
-/
theorem kill_step (ring : DirectedRing n) (C : Fin n → Cell4) (A : Fin n) (d1 d2 : Nat)
    (h21 : 1 ≤ d2) (h2n : d2 < n) (h11 : 1 ≤ d1) (h1n : d1 < n)
    (hA : (C A).leader = true)
    (hB : (C (advance ring A d2)).leader = true)
    (hmidA : ∀ s, 1 ≤ s → s < d2 → (C (advance ring A s)).leader = false)
    (hCc : (C (advance ring (advance ring A d2) d1)).leader = true)
    (hmidB : ∀ s, 1 ≤ s → s < d1 →
      (C (advance ring (advance ring A d2) s)).leader = false) :
    ∃ w : List (Fin n), w.length ≤ 5 * n ∧ leaderCount (runW ring C w) < leaderCount C := by
  -- Phase 1: arm(B, C).
  obtain ⟨w1, hw1, h1⟩ := arm ring C (advance ring A d2) d1 h11 h1n hCc hmidB
  rcases h1 with hp | ⟨hBsig, -, -⟩
  · exact ⟨w1, by omega, hp⟩
  by_cases hnp1 : leaderCount (runW ring C w1) < leaderCount C
  · exact ⟨w1, by omega, hnp1⟩
  -- Phase 2: B's incoming edge, B fires a dummy.
  have he0 : ring.rightNeighbor (advance ring A (d2 - 1)) = advance ring A d2 := by
    rw [rn_adv, Nat.sub_add_cancel h21]
  have hne0 : ring.rightNeighbor (advance ring A (d2 - 1)) ≠ advance ring A (d2 - 1) := by
    rw [he0]; exact adv_ne ring A h2n (by omega) (by omega)
  have hrun2 : runW ring C (w1 ++ [advance ring A (d2 - 1)]) =
      stE ring (runW ring C w1) (advance ring A (d2 - 1)) := by
    rw [runW_append]; rfl
  by_cases hnp2 : leaderCount (runW ring C (w1 ++ [advance ring A (d2 - 1)])) < leaderCount C
  · exact ⟨w1 ++ [advance ring A (d2 - 1)],
      by rw [List.length_append, List.length_singleton]; omega, hnp2⟩
  have hB2 : (runW ring C (w1 ++ [advance ring A (d2 - 1)]) (advance ring A d2)).shield = false ∧
      (runW ring C (w1 ++ [advance ring A (d2 - 1)]) (advance ring A d2)).signalB = false := by
    rw [hrun2, ← he0, stE_right _ _ _ hne0]
    apply rowE_dummy
    · rw [he0]; exact alive_of_not_lt ring C w1 hnp1 _ hB
    · rw [he0]; exact hBsig
  -- Phase 3: arm(A, B).
  obtain ⟨w3, hw3, h3⟩ := arm ring (runW ring C (w1 ++ [advance ring A (d2 - 1)])) A d2 h21 h2n
    (alive_of_not_lt ring C _ hnp2 _ hB)
    (fun s hs1 hs2 => runW_leader_false ring C _ _ (hmidA s hs1 hs2))
  have hle2 := lc_runW_le ring (w1 ++ [advance ring A (d2 - 1)]) C
  have hlen13 : (w1 ++ [advance ring A (d2 - 1)] ++ w3).length ≤ 5 * n := by
    rw [List.length_append, List.length_append, List.length_singleton]; omega
  rcases h3 with hp | ⟨hAsig, hbul3, hY3⟩
  · refine ⟨w1 ++ [advance ring A (d2 - 1)] ++ w3, hlen13, ?_⟩
    rw [runW_append]
    omega
  by_cases hnp3 : leaderCount (runW ring (runW ring C (w1 ++ [advance ring A (d2 - 1)])) w3) <
      leaderCount (runW ring C (w1 ++ [advance ring A (d2 - 1)]))
  · refine ⟨w1 ++ [advance ring A (d2 - 1)] ++ w3, hlen13, ?_⟩
    rw [runW_append]
    omega
  -- Phase 4: chase from A to B.
  have hY3' := hY3 hB2.2
  have hA3 := alive_of_not_lt ring _ w3 hnp3 A (alive_of_not_lt ring C _ hnp2 A hA)
  have hB3 := alive_of_not_lt ring _ w3 hnp3 _ (alive_of_not_lt ring C _ hnp2 _ hB)
  have hdead := chase ring A (runW ring (runW ring C (w1 ++ [advance ring A (d2 - 1)])) w3) d2
    h21 h2n ⟨hA3, hAsig⟩
    (fun s hs1 hs2 => runW_leader_false ring _ _ _
      (runW_leader_false ring C _ _ (hmidA s hs1 hs2)))
    (fun s _ hs2 => hbul3 s hs2) hB3 hY3'.2 (by rw [hY3'.1]; exact hB2.1)
  have hlt4 := lc_lt_of_kill _ _ (fun j hj => runW_leader_mono ring _ _ j hj) _ hB3 hdead
  have hle3 := lc_runW_le ring w3 (runW ring C (w1 ++ [advance ring A (d2 - 1)]))
  refine ⟨w1 ++ [advance ring A (d2 - 1)] ++ w3 ++ fwd ring A d2, ?_, ?_⟩
  · rw [List.length_append, List.length_append, List.length_append, List.length_singleton,
      fwd_length]
    omega
  · rw [runW_append, runW_append]
    exact Nat.lt_of_lt_of_le hlt4 (Nat.le_trans hle3 hle2)

/-- With at least two leaders, a word of length at most `5 n` lowers the
leader count. -/
theorem decrease (ring : DirectedRing n) (C : Fin n → Cell4) (h2 : 2 ≤ leaderCount C) :
    ∃ w : List (Fin n), w.length ≤ 5 * n ∧ leaderCount (runW ring C w) < leaderCount C := by
  obtain ⟨A, hA⟩ : ∃ A, (C A).leader = true := by
    refine Classical.byContradiction fun hno => ?_
    have h0 := lc_zero_of_none C (fun i => by
      cases h : (C i).leader with
      | false => rfl
      | true => exact absurd ⟨i, h⟩ hno)
    omega
  obtain ⟨Z, hZ, hZA⟩ : ∃ Z, (C Z).leader = true ∧ Z ≠ A := by
    refine Classical.byContradiction fun hno => ?_
    have h1 := lc_le_one_of_unique C A
      (fun i hi => Classical.byContradiction fun hne => hno ⟨i, hi, hne⟩)
    omega
  obtain ⟨d2, h21, h2n, hB, hmidA⟩ := exists_next_leader ring C A Z hZ hZA
  have hAB : A ≠ advance ring A d2 := by
    intro h
    have := adv_inj ring A (a := 0) (b := d2) (by omega) h2n (by rw [advance_zero]; exact h)
    omega
  obtain ⟨d1, h11, h1n, hCc, hmidB⟩ := exists_next_leader ring C (advance ring A d2) A hA hAB
  exact kill_step ring C A d1 d2 h21 h2n h11 h1n hA hB hmidA hCc hmidB

/-- Since one step deletes at most one leader, a count-lowering word has a
prefix lowering the count by exactly one. -/
theorem exact_drop (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : Fin n → Cell4),
      leaderCount (runW ring C w) < leaderCount C →
      ∃ w' : List (Fin n), w'.length ≤ w.length ∧
        leaderCount (runW ring C w') + 1 = leaderCount C
  | [], _, h => absurd h (Nat.lt_irrefl _)
  | e :: w, C, h => by
      have hle : leaderCount (stE ring C e) ≤ leaderCount C := leaderCount_step_le ring C e
      have hge : leaderCount C ≤ leaderCount (stE ring C e) + 1 :=
        leaderCount_le_step_add_one ring C e
      by_cases hs : leaderCount (stE ring C e) < leaderCount C
      · refine ⟨[e], by simp, ?_⟩
        show leaderCount (stE ring C e) + 1 = leaderCount C
        omega
      · rw [runW_cons] at h
        obtain ⟨w', hw', hdrop⟩ := exact_drop ring w (stE ring C e) (by omega)
        refine ⟨e :: w', by simp; omega, ?_⟩
        rw [runW_cons]
        omega

/-- From `m + 1` leaders, a word of length at most `m * (5 n)` reaches exactly
one leader. -/
theorem reach_one (ring : DirectedRing n) :
    ∀ (m : Nat) (C : Fin n → Cell4), leaderCount C = m + 1 →
      ∃ w : List (Fin n), w.length ≤ m * (5 * n) ∧ leaderCount (runW ring C w) = 1
  | 0, C, h => ⟨[], by simp, by rw [runW_nil]; omega⟩
  | m + 1, C, h => by
      obtain ⟨w0, hw0, hlt⟩ := decrease ring C (by omega)
      obtain ⟨w1, hw1, hdrop⟩ := exact_drop ring w0 C hlt
      obtain ⟨w2, hw2, hone⟩ := reach_one ring m (runW ring C w1) (by omega)
      refine ⟨w1 ++ w2, ?_, by rw [runW_append]; exact hone⟩
      rw [List.length_append, Nat.add_mul, Nat.one_mul]
      omega

/-! ## Headline -/

/--
**Deterministic Lemma 17 with a short word.**  Every literal Algorithm-5
configuration `D` with `PPL.Elim.PB ring D` admits a scheduler word of length
at most `5 * n * n` (320 at `n = 8`) whose literal row-E run ends with exactly
one leader.  More precisely the word has length at most
`(leaderCount D - 1) * 5 n`.

No lower bound on `n` is needed; PB is used only for the existence of a
leader.
-/
theorem literalPB_oneLeader_exists_short
    {n : Nat}
    (ring : DirectedRing n)
    (D : PPL.LiteralElimConfig n)
    (hPB : PPL.Elim.PB ring D) :
    ∃ w : DetSchedule n,
      w.length ≤ 5 * n * n ∧
      PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule PPL.Elim.protocolE ring D w) := by
  obtain ⟨i, hi⟩ := hPB.1
  have hpos := lc_pos D i hi
  have hle := lc_le_n D
  obtain ⟨w, hw, h1⟩ := reach_one ring (leaderCount D - 1) D (by omega)
  refine ⟨w, ?_, h1⟩
  have hmul : (leaderCount D - 1) * (5 * n) ≤ n * (5 * n) :=
    Nat.mul_le_mul_right (5 * n) (by omega)
  have hcomm : n * (5 * n) = 5 * n * n := Nat.mul_comm n (5 * n)
  omega

end PPL.Convergence.L17Macro

#print axioms PPL.Convergence.L17Macro.arm
#print axioms PPL.Convergence.L17Macro.chase
#print axioms PPL.Convergence.L17Macro.kill_step
#print axioms PPL.Convergence.L17Macro.literalPB_oneLeader_exists_short
