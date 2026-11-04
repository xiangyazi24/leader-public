import Init.Data.List.OfFn
import Init.Data.List.MinMax
import Init.Data.List.Nat.Sum
import Init.Data.Nat.Div.Lemmas
import Init.Data.Nat.Lemmas
import Lean.Elab.Tactic

set_option autoImplicit false

/-!
# Harmonic accounting for proof-chosen elimination episodes

This file contains only finite `Nat` accounting.

There are three interfaces.

* `cyclic_adjacent_pigeonhole` chooses a short adjacent pair from a cyclic
  family of gaps whose total mass is at most the ring size.
* `harmonicBudget` bounds the accumulated floor-division charges by bit length.
* `ChosenTripleTrace` records a finite sequence of completed successful
  episodes.  Its constructor requires the averaging charge condition at every
  step, rather than only at the initial state.

The stopping-tree/Bellman proof is outside this file.  Its per-episode output is
represented here only by the natural number `episodeCost`.
-/

namespace HarmonicEpisodeCharge

/-! ## 1. Cyclic adjacent-pair averaging -/

/-- Clockwise cyclic successor on a nonempty finite index type. -/
def cyclicSucc {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

/-- Finite uniform sums distribute over pointwise addition. -/
theorem ofFn_sum_add {m : Nat} (f g : Fin m → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

/-- Away from the final index, cyclic successor is ordinary successor. -/
theorem cyclicSucc_castSucc {k : Nat}
    (hm : 0 < k + 1) (i : Fin k) :
    cyclicSucc hm i.castSucc = i.succ := by
  apply Fin.ext
  simp [cyclicSucc,
    Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]

/-- The final finite index wraps to zero. -/
theorem cyclicSucc_last {k : Nat} (hm : 0 < k + 1) :
    cyclicSucc hm (Fin.last k) = 0 := by
  apply Fin.ext
  simp [cyclicSucc]

/-- Cyclic successor is a reindexing of a finite sum. -/
theorem cyclic_reindex_sum {m : Nat} (hm : 0 < m)
    (d : Fin m → Nat) :
    (List.ofFn (fun i => d (cyclicSucc hm i))).sum =
      (List.ofFn d).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hm)
  subst m
  rw [show
    List.ofFn (fun i : Fin (k + 1) => d (cyclicSucc hm i)) =
      (List.ofFn (fun i : Fin k => d (cyclicSucc hm i.castSucc))) ++
        [d (cyclicSucc hm (Fin.last k))]
    from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : cyclicSucc hm (Fin.last k) = 0 :=
    cyclicSucc_last hm
  rw [hlast]
  have hfun :
      (fun i : Fin k => d (cyclicSucc hm i.castSucc)) =
        (fun i : Fin k => d i.succ) := by
    funext i
    rw [cyclicSucc_castSucc hm i]
  rw [hfun]
  omega

/-- The sum of all cyclic adjacent-pair masses is exactly twice total mass. -/
theorem cyclic_adjacent_sum {m : Nat} (hm : 0 < m)
    (d : Fin m → Nat) :
    (List.ofFn (fun i => d i + d (cyclicSucc hm i))).sum =
      2 * (List.ofFn d).sum := by
  calc
    (List.ofFn (fun i => d i + d (cyclicSucc hm i))).sum =
        (List.ofFn d).sum +
          (List.ofFn (fun i => d (cyclicSucc hm i))).sum :=
      ofFn_sum_add d (fun i => d (cyclicSucc hm i))
    _ = (List.ofFn d).sum + (List.ofFn d).sum := by
      rw [cyclic_reindex_sum hm d]
    _ = 2 * (List.ofFn d).sum := by omega

/-- Division-free averaging on a cyclic gap family.

If `m > 0` gaps have total mass at most `n`, one cyclic-adjacent pair has
`m * pairMass <= 2*n`.  The proof takes the minimum pair term and uses
`min * length <= sum`; no division is needed. -/
theorem cyclic_adjacent_pigeonhole
    {m n : Nat} (hm : 0 < m) (d : Fin m → Nat)
    (mass : (List.ofFn d).sum ≤ n) :
    ∃ i : Fin m,
      m * (d i + d (cyclicSucc hm i)) ≤ 2 * n := by
  let xs : List Nat :=
    List.ofFn (fun i : Fin m => d i + d (cyclicSucc hm i))
  have hlen : xs.length = m := by
    simp [xs]
  have hne : xs ≠ [] := by
    intro hx
    have hzero : xs.length = 0 := by simp [hx]
    rw [hlen] at hzero
    omega
  have hmin := List.min_mul_length_le_sum_nat hne
  have hmem : xs.min hne ∈ xs := List.min_mem hne
  have hidx :
      ∃ i : Fin m,
        d i + d (cyclicSucc hm i) = xs.min hne := by
    simpa [xs] using hmem
  obtain ⟨i, hi⟩ := hidx
  have havg0 : xs.min hne * m ≤ xs.sum := by
    rw [hlen] at hmin
    exact hmin
  have havg : m * xs.min hne ≤ xs.sum := by
    calc
      m * xs.min hne = xs.min hne * m := Nat.mul_comm _ _
      _ ≤ xs.sum := havg0
  have hpairs : xs.sum = 2 * (List.ofFn d).sum := by
    simpa [xs] using cyclic_adjacent_sum hm d
  have hsum : xs.sum ≤ 2 * n := by
    calc
      xs.sum = 2 * (List.ofFn d).sum := hpairs
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 mass
  refine ⟨i, ?_⟩
  rw [hi]
  exact Nat.le_trans havg hsum

/-! ## 2. A division-free harmonic budget -/

/-- `sum_{k=1}^m floor(N/k)`, represented recursively. -/
def divisionBudget (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => divisionBudget N k + N / (k + 1)

/-- Unfold one denominator. -/
theorem divisionBudget_succ (N k : Nat) :
    divisionBudget N (k + 1) =
      divisionBudget N k + N / (k + 1) := rfl

/-- Adding one denominator cannot lower the budget. -/
theorem divisionBudget_step_le (N k : Nat) :
    divisionBudget N k ≤ divisionBudget N (k + 1) := by
  change divisionBudget N k ≤ divisionBudget N k + N / (k + 1)
  exact Nat.le_add_right _ _

/-- The prefix budget is monotone in its endpoint. -/
theorem divisionBudget_mono (N : Nat) {a b : Nat} (hab : a ≤ b) :
    divisionBudget N a ≤ divisionBudget N b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases htop : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a ≤ b := by omega
        exact Nat.le_trans (ih hab') (divisionBudget_step_le N b)

/-- Unfold two consecutive denominators. -/
theorem divisionBudget_add_two (N k : Nat) :
    divisionBudget N (k + 2) =
      divisionBudget N k + N / (k + 1) + N / (k + 2) := by
  rw [show k + 2 = (k + 1) + 1 by omega,
    divisionBudget_succ N (k + 1), divisionBudget_succ N k]

/-- The part of the harmonic sum after denominator one, grouped as
`(2,3), (4,5), ..., (2k,2k+1)`. -/
def pairedTailBudget (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      pairedTailBudget N k +
        (N / (2 * (k + 1)) + N / (2 * (k + 1) + 1))

/-- Unfold one dyadic denominator pair. -/
theorem pairedTailBudget_succ (N k : Nat) :
    pairedTailBudget N (k + 1) =
      pairedTailBudget N k +
        (N / (2 * (k + 1)) + N / (2 * (k + 1) + 1)) := rfl

/-- One dyadic pair contracts to one denominator in the next coarser layer.

No linear-arithmetic step reasons about division.  The two division facts are
`Nat.div_le_div_left`, for denominator monotonicity, and
`Nat.div_mul_le_self`, after `Nat.le_div_iff_mul_le` removes the outer quotient. -/
theorem dyadic_pair_le (N r : Nat) (hr : 0 < r) :
    N / (2 * r) + N / (2 * r + 1) ≤ N / r := by
  have htwo : 0 < 2 * r := by omega
  have hright : N / (2 * r + 1) ≤ N / (2 * r) := by
    exact Nat.div_le_div_left (a := N) (by omega) htwo
  have hdouble : 2 * (N / (2 * r)) ≤ N / r := by
    apply (Nat.le_div_iff_mul_le hr).2
    have hbase : (N / (2 * r)) * (2 * r) ≤ N :=
      Nat.div_mul_le_self N (2 * r)
    calc
      (2 * (N / (2 * r))) * r =
          (N / (2 * r)) * (2 * r) := by ac_rfl
      _ ≤ N := hbase
  calc
    N / (2 * r) + N / (2 * r + 1) ≤
        N / (2 * r) + N / (2 * r) :=
      Nat.add_le_add (Nat.le_refl _) hright
    _ = 2 * (N / (2 * r)) := by omega
    _ ≤ N / r := hdouble

/-- Every complete pair in one dyadic layer is paid by the corresponding
coarser denominator. -/
theorem pairedTailBudget_le (N k : Nat) :
    pairedTailBudget N k ≤ divisionBudget N k := by
  induction k with
  | zero =>
      exact Nat.le_refl _
  | succ k ih =>
      change
        pairedTailBudget N k +
            (N / (2 * (k + 1)) + N / (2 * (k + 1) + 1)) ≤
          divisionBudget N k + N / (k + 1)
      exact Nat.add_le_add ih (dyadic_pair_le N (k + 1) (by omega))

/-- Exact decomposition of an odd prefix into denominator one plus dyadic
pairs. -/
theorem divisionBudget_odd_eq (N k : Nat) :
    divisionBudget N (2 * k + 1) = N + pairedTailBudget N k := by
  induction k with
  | zero =>
      simp [divisionBudget, pairedTailBudget]
  | succ k ih =>
      have hindex :
          2 * (k + 1) + 1 = (2 * k + 1) + 2 := by
        omega
      calc
        divisionBudget N (2 * (k + 1) + 1) =
            divisionBudget N ((2 * k + 1) + 2) :=
          congrArg (divisionBudget N) hindex
        _ = divisionBudget N (2 * k + 1) +
              N / ((2 * k + 1) + 1) +
              N / ((2 * k + 1) + 2) :=
          divisionBudget_add_two N (2 * k + 1)
        _ = (N + pairedTailBudget N k) +
              N / ((2 * k + 1) + 1) +
              N / ((2 * k + 1) + 2) := by
          rw [ih]
        _ = N +
              (pairedTailBudget N k +
                (N / (2 * (k + 1)) +
                  N / (2 * (k + 1) + 1))) := by
          have hden0 : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
          have hden1 : (2 * k + 1) + 2 = 2 * (k + 1) + 1 := by omega
          rw [hden0, hden1]
          omega
        _ = N + pairedTailBudget N (k + 1) := by
          rw [pairedTailBudget_succ]

/-- An odd prefix costs at most one fresh `N` plus its halved prefix. -/
theorem divisionBudget_odd_le (N k : Nat) :
    divisionBudget N (2 * k + 1) ≤ N + divisionBudget N k := by
  calc
    divisionBudget N (2 * k + 1) =
        N + pairedTailBudget N k := divisionBudget_odd_eq N k
    _ ≤ N + divisionBudget N k :=
      Nat.add_le_add (Nat.le_refl _) (pairedTailBudget_le N k)

/-- An even prefix obeys the same one-layer bound. -/
theorem divisionBudget_even_le (N k : Nat) :
    divisionBudget N (2 * k) ≤ N + divisionBudget N k := by
  exact Nat.le_trans
    (divisionBudget_step_le N (2 * k))
    (divisionBudget_odd_le N k)

/-- **Dyadic block lemma.** Removing one binary layer costs at most `N`.

This is the division-free replacement for explicitly summing the intervals
`[2^j, 2^(j+1))`: even and odd prefixes are reduced to their quotient by two. -/
theorem divisionBudget_halve (N m : Nat) :
    divisionBudget N m ≤ N + divisionBudget N (m / 2) := by
  have hdecomp := Nat.mod_add_div m 2
  rcases Nat.mod_two_eq_zero_or_one m with hmod | hmod
  · have hm : m = 2 * (m / 2) := by omega
    calc
      divisionBudget N m = divisionBudget N (2 * (m / 2)) :=
        congrArg (divisionBudget N) hm
      _ ≤ N + divisionBudget N (m / 2) :=
        divisionBudget_even_le N (m / 2)
  · have hm : m = 2 * (m / 2) + 1 := by omega
    calc
      divisionBudget N m = divisionBudget N (2 * (m / 2) + 1) :=
        congrArg (divisionBudget N) hm
      _ ≤ N + divisionBudget N (m / 2) :=
        divisionBudget_odd_le N (m / 2)

/-- Binary length, defined exactly by repeated halving. -/
def numBits (m : Nat) : Nat :=
  if h : m = 0 then 0
  else
    have : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
    numBits (m / 2) + 1
termination_by m

/-- Recurrence for positive binary length. -/
theorem numBits_rec (m : Nat) (hm : 0 < m) :
    numBits m = numBits (m / 2) + 1 := by
  conv => lhs; unfold numBits
  simp [show m ≠ 0 from Nat.ne_of_gt hm]

/-- Iterating the dyadic block lemma: each bit layer costs at most `N`. -/
theorem divisionBudget_le_numBits (N m : Nat) :
    divisionBudget N m ≤ N * numBits m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      by_cases hm : m = 0
      · subst m
        simp [divisionBudget, numBits]
      · have hpos : 0 < m := Nat.pos_of_ne_zero hm
        have hhalf : m / 2 < m :=
          Nat.div_lt_self hpos (by omega)
        have hih :
            divisionBudget N (m / 2) ≤ N * numBits (m / 2) :=
          ih (m / 2) hhalf
        calc
          divisionBudget N m ≤ N + divisionBudget N (m / 2) :=
            divisionBudget_halve N m
          _ ≤ N + N * numBits (m / 2) :=
            Nat.add_le_add (Nat.le_refl _) hih
          _ = N * (numBits (m / 2) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          _ = N * numBits m :=
            congrArg (fun q => N * q) (numBits_rec m hpos).symm

/-- The requested harmonic charge: `sum_{k=1}^m floor((2*n)/k)`. -/
def harmonicBudget (n : Nat) : Nat → Nat :=
  divisionBudget (2 * n)

/-- The requested recursive equation. -/
theorem harmonicBudget_succ (n k : Nat) :
    harmonicBudget n (k + 1) =
      harmonicBudget n k + (2 * n) / (k + 1) := by
  change
    divisionBudget (2 * n) (k + 1) =
      divisionBudget (2 * n) k + (2 * n) / (k + 1)
  exact divisionBudget_succ (2 * n) k

/-- Harmonic budget is monotone in the number of denominators. -/
theorem harmonicBudget_mono (n : Nat) {a b : Nat} (hab : a ≤ b) :
    harmonicBudget n a ≤ harmonicBudget n b := by
  change divisionBudget (2 * n) a ≤ divisionBudget (2 * n) b
  exact divisionBudget_mono (2 * n) hab

/-- Stronger bit-length form of the harmonic bound. -/
theorem harmonicBudget_le_numBits (n m : Nat) :
    harmonicBudget n m ≤ (2 * n) * numBits m := by
  change divisionBudget (2 * n) m ≤ (2 * n) * numBits m
  exact divisionBudget_le_numBits (2 * n) m

/-- Requested looser form `2*n*(numBits m + 1)`. -/
theorem harmonicBudget_le_bits (n m : Nat) :
    harmonicBudget n m ≤ (2 * n) * (numBits m + 1) := by
  exact Nat.le_trans (harmonicBudget_le_numBits n m)
    (Nat.mul_le_mul_left (2 * n) (Nat.le_add_right (numBits m) 1))

/-! ## 3. Composition across proof-chosen triples -/

/--
Protocol boundary for the harmonic argument.

At each completed success, `remaining` is the current number of live gaps /
leaders and `span` is the adjacent-pair span selected by the proof.  The field
`chosen` is required at **every** constructor, so the averaging hypothesis is
state-uniform across the whole trace.

The only protocol-level obligation left outside this file is that the existing
episode theorem can be instantiated with every proof-chosen valid consecutive
triple of the current configuration.  If that theorem has an ordinary
parameter `F : TwoGapFrame ...`, this is a weak proof-interface requirement:
Lean quantifies over `F`, so the caller may choose a new `F` after each renewal;
the protocol itself need not locate the minimizing triple.  What must still be
checked is that all side hypotheses of the episode theorem hold for every such
current frame, rather than only for one distinguished frame.
-/
inductive ChosenTripleTrace (C n : Nat) :
    Nat → Nat → Nat → Prop where
  | stop (remaining : Nat) :
      ChosenTripleTrace C n remaining 0 0
  | step
      {remaining nextRemaining span episodeCost tailSpan tailCost : Nat}
      (remaining_pos : 0 < remaining)
      (decrease : nextRemaining < remaining)
      (chosen : remaining * span ≤ 2 * n)
      (episode_cost : episodeCost ≤ (C * n) * span)
      (tail : ChosenTripleTrace C n nextRemaining tailSpan tailCost) :
      ChosenTripleTrace C n remaining
        (span + tailSpan) (episodeCost + tailCost)

namespace ChosenTripleTrace

/-- The sum of all proof-chosen adjacent spans is harmonic in the initial
number of remaining leaders.  Strict decrease allows an episode to delete more
than one leader; skipped denominator values only improve the estimate. -/
theorem totalSpan_le_harmonic
    {C n remaining totalSpan totalCost : Nat}
    (trace : ChosenTripleTrace C n remaining totalSpan totalCost) :
    totalSpan ≤ harmonicBudget n remaining := by
  induction trace with
  | stop remaining =>
      simp [harmonicBudget, divisionBudget]
  | @step remaining nextRemaining span episodeCost tailSpan tailCost
      hpos hdec hchosen hcost tail ih =>
      have hspanDiv : span ≤ (2 * n) / remaining := by
        apply (Nat.le_div_iff_mul_le hpos).2
        calc
          span * remaining = remaining * span := Nat.mul_comm _ _
          _ ≤ 2 * n := hchosen
      have hnext : nextRemaining ≤ remaining - 1 := by omega
      have htail : tailSpan ≤ harmonicBudget n (remaining - 1) :=
        Nat.le_trans ih (harmonicBudget_mono n hnext)
      have hrem : remaining = (remaining - 1) + 1 := by omega
      calc
        span + tailSpan ≤
            (2 * n) / remaining + harmonicBudget n (remaining - 1) :=
          Nat.add_le_add hspanDiv htail
        _ = harmonicBudget n (remaining - 1) +
              (2 * n) / remaining := by omega
        _ = harmonicBudget n remaining := by
          have hs := harmonicBudget_succ n (remaining - 1)
          rw [← hrem] at hs
          exact hs.symm

/-- Per-episode bounds `episodeCost <= C*n*span` add linearly. -/
theorem totalCost_le_span
    {C n remaining totalSpan totalCost : Nat}
    (trace : ChosenTripleTrace C n remaining totalSpan totalCost) :
    totalCost ≤ (C * n) * totalSpan := by
  induction trace with
  | stop remaining =>
      simp
  | @step remaining nextRemaining span episodeCost tailSpan tailCost
      hpos hdec hchosen hcost tail ih =>
      calc
        episodeCost + tailCost ≤
            (C * n) * span + (C * n) * tailSpan :=
          Nat.add_le_add hcost ih
        _ = (C * n) * (span + tailSpan) :=
          (Nat.mul_add (C * n) span tailSpan).symm

/-- Composition theorem in the exact harmonic-budget form. -/
theorem totalCost_le_harmonic
    {C n remaining totalSpan totalCost : Nat}
    (trace : ChosenTripleTrace C n remaining totalSpan totalCost) :
    totalCost ≤ (C * n) * harmonicBudget n remaining := by
  exact Nat.le_trans trace.totalCost_le_span
    (Nat.mul_le_mul_left (C * n) trace.totalSpan_le_harmonic)

/-- Final `O(n^2 log n)` natural-number cap.

For an initial count `m0`, instantiate `remaining := m0`.  If exactly one leader
is deleted per episode then the constructor's current `remaining` is exactly
`m0-j`; if an episode deletes more, the strict-decrease trace skips terms and
the same bound remains valid. -/
theorem totalCost_le_bits
    {C n remaining totalSpan totalCost : Nat}
    (trace : ChosenTripleTrace C n remaining totalSpan totalCost) :
    totalCost ≤ 2 * C * n * n * (numBits remaining + 1) := by
  calc
    totalCost ≤ (C * n) * harmonicBudget n remaining :=
      trace.totalCost_le_harmonic
    _ ≤ (C * n) * ((2 * n) * (numBits remaining + 1)) :=
      Nat.mul_le_mul_left (C * n) (harmonicBudget_le_bits n remaining)
    _ = 2 * C * n * n * (numBits remaining + 1) := by
      ac_rfl

end ChosenTripleTrace
end HarmonicEpisodeCharge

#print axioms HarmonicEpisodeCharge.ofFn_sum_add
#print axioms HarmonicEpisodeCharge.cyclicSucc_castSucc
#print axioms HarmonicEpisodeCharge.cyclicSucc_last
#print axioms HarmonicEpisodeCharge.cyclic_reindex_sum
#print axioms HarmonicEpisodeCharge.cyclic_adjacent_sum
#print axioms HarmonicEpisodeCharge.cyclic_adjacent_pigeonhole
#print axioms HarmonicEpisodeCharge.divisionBudget_succ
#print axioms HarmonicEpisodeCharge.divisionBudget_step_le
#print axioms HarmonicEpisodeCharge.divisionBudget_mono
#print axioms HarmonicEpisodeCharge.divisionBudget_add_two
#print axioms HarmonicEpisodeCharge.pairedTailBudget_succ
#print axioms HarmonicEpisodeCharge.dyadic_pair_le
#print axioms HarmonicEpisodeCharge.pairedTailBudget_le
#print axioms HarmonicEpisodeCharge.divisionBudget_odd_eq
#print axioms HarmonicEpisodeCharge.divisionBudget_odd_le
#print axioms HarmonicEpisodeCharge.divisionBudget_even_le
#print axioms HarmonicEpisodeCharge.divisionBudget_halve
#print axioms HarmonicEpisodeCharge.numBits_rec
#print axioms HarmonicEpisodeCharge.divisionBudget_le_numBits
#print axioms HarmonicEpisodeCharge.harmonicBudget_succ
#print axioms HarmonicEpisodeCharge.harmonicBudget_mono
#print axioms HarmonicEpisodeCharge.harmonicBudget_le_numBits
#print axioms HarmonicEpisodeCharge.harmonicBudget_le_bits
#print axioms HarmonicEpisodeCharge.ChosenTripleTrace.totalSpan_le_harmonic
#print axioms HarmonicEpisodeCharge.ChosenTripleTrace.totalCost_le_span
#print axioms HarmonicEpisodeCharge.ChosenTripleTrace.totalCost_le_harmonic
#print axioms HarmonicEpisodeCharge.ChosenTripleTrace.totalCost_le_bits
