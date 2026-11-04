import Leader.Wu.Elimination.LeaderCountProgress
import Leader.Wu.RaceEntrance.UniformAll

/-!
# Short physical pairs and adaptive leader-count blocks

The actual sorted leader enumeration selects two adjacent gaps of total
span at most `floor(2*n/k)`.  The proved all-ratio pair mass is transferred
on the same raw scheduler words to a strict drop of the finite-cell leader
count, then padded to `floor(60*n*n/k)` interactions.

The closed signal domain supplies every adaptive restart state.  The
dyadic conclusion concerns the event that more than two leaders remain;
it does not assert positive count, output safety, or a final two-to-one
estimate.  The physical transition and all existing cell fields are
unchanged.
-/

namespace K2GlobalShortPairMass

open StateBoundUnifiedCell LDSinkBoundedKernel LDTwoGapFrame
  LDSinkTwoGapNoResetKernel LDSinkTwoGapReachInvariant LDSinkGapCleanup
  FiniteUniformStoppingTree LabelFreeElimination K2FiniteProgress
  LeaderCountDyadicTail LDSinkTwoGapRaceEntranceUniformAll

set_option autoImplicit false

variable {n ψ κ : Nat}

/-- A deterministic physical horizon for the actual current leader count. -/
def countBlock (n k : Nat) : Nat := 60 * n * n / k

/-- The bin consumer retains its one explicit rounding interaction. -/
def binBlock (n m : Nat) : Nat := levelBlock n 60 0 m

/-- Counting the actual stored leader bits never exceeds the ring size. -/
theorem count_le_ring_size (C : Fin n → UCell ψ κ) : count C ≤ n := by
  rw [count_eq_sum]
  have h := ofFn_sum_le
    (fun i : Fin n => if (C i).legacy.leader then 1 else 0)
    (fun _ : Fin n => 1) (by intro i; cases (C i).legacy.leader <;> decide)
  simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_one] using h

/-- This is the actual short adjacent pair constructor, applied to the
label-free observation of the physical cells. No layout is an input. -/
theorem signalGlobal_short_pair (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (hk : 3 ≤ count C) :
    ∃ F : TwoGapFrame n,
      F.recovery.d + F.attack.d ≤ (2 * n) / count C ∧
      ∀ phase : APhase, GapPair (by decide) F ⟨observe C, phase⟩ := by
  have hG : K2GlobalGapClosure.GlobalClass (by decide) ring (count C) (observe C) :=
    ⟨by omega, (count_eq_observe C).symm, hC⟩
  exact K2CyclicLayout.short_pair_of_globalClass (by decide) ring (observe C) hk hG

/-- Integer division already covers the complete pair clock. There is no
omitted recovery term and no extra rounding needed at the count level. -/
theorem span_clock_le_countBlock (n k span : Nat) (hk : 0 < k)
    (hspan : span ≤ (2 * n) / k) : 30 * n * span ≤ countBlock n k := by
  apply (Nat.le_div_iff_mul_le hk).mpr
  calc
    30 * n * span * k = (30 * n) * (span * k) := Nat.mul_assoc _ _ _
    _ ≤ (30 * n) * (2 * n) :=
      Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le hk).mp hspan)
    _ = 60 * n * n := by
      have h60 : 60 = 30 * 2 := by decide
      rw [h60]
      ac_rfl

noncomputable section

/-- All-ratio physical deletion mass becomes strict count-drop mass in the
same finite carrier at the same physical endpoint, including padding after
the tagged stopping time. Only the actual GapPair is assumed. -/
theorem pair_count_drop_at_span (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hg : GapPair (by decide) F ⟨observe C, .transit⟩) :
    n ^ (30 * n * (F.recovery.d + F.attack.d)) ≤ deletionDenominator *
      wordSum (step hψ F.attack.ring)
        (fun D => if count D < count C then 1 else 0) C
        (30 * n * (F.recovery.d + F.attack.d)) := by
  have hm := gapPair_uniform_deletion_mass (by decide) F ⟨observe C, .transit⟩ hg
  rw [← successCount_eq hψ F C .transit] at hm
  exact Nat.le_trans hm (Nat.mul_le_mul_left _
    (successCount_le_physical_count_drop hψ F C
      (pairPresent_of_gapPair F C .transit hg) _))

/-- Every actual state in the closed signal domain with `k >= 3` has a
strict physical count drop with constant original-word mass by `60*n*n/k`.
The short pair, its physical invariants, and its mass are all produced. -/
theorem signalGlobal_count_drop_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (hk : 3 ≤ count C) :
    n ^ countBlock n (count C) ≤ deletionDenominator *
      wordSum (step hψ ring) (fun D => if count D < count C then 1 else 0)
        C (countBlock n (count C)) := by
  obtain ⟨F, hspan, hg⟩ := signalGlobal_short_pair ring C hC hk
  exact pad_deletion_mass (step hψ F.attack.ring) count
    (step_count_nonincrease hψ F.attack.ring) C deletionDenominator
    (30 * n * (F.recovery.d + F.attack.d)) (countBlock n (count C))
    (span_clock_le_countBlock n (count C) _ (by omega) hspan)
    (pair_count_drop_at_span hψ F C (hg .transit))

/-- Enlarging the count-level block to the lower endpoint of a bin keeps
the same success mass. This is valid for each actual adaptive endpoint. -/
theorem signalGlobal_bin_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C)
    (m : Nat) (hm : 2 ≤ m) (hk : m < count C) :
    n ^ binBlock n m ≤ deletionDenominator *
      wordSum (step hψ ring) (fun D => if count D < count C then 1 else 0)
        C (binBlock n m) := by
  have hdiv : 60 * n * n / count C ≤ 60 * n * n / m :=
    Nat.div_le_div_left (by omega) (by omega)
  have htime : countBlock n (count C) ≤ binBlock n m := by
    unfold countBlock binBlock levelBlock
    omega
  exact pad_deletion_mass (step hψ ring) count (step_count_nonincrease hψ ring)
    C deletionDenominator (countBlock n (count C)) (binBlock n m) htime
    (signalGlobal_count_drop_mass hψ ring C hC (by omega))

/-- The real physical domain remains closed under every original edge. -/
private theorem closed (hψ : 0 < ψ) (ring : DirectedRing n) :
    ∀ (C : Fin n → UCell ψ κ) (e : Fin n),
      SignalGlobal ring C → SignalGlobal ring (step hψ ring C e) :=
  fun C e hC => signalGlobal_step hψ ring C hC e

/-- Exact finite-word tail for a single bin, with the derived inverse-count
clock. The subtype is erased before the conclusion is stated. -/
theorem signalGlobal_bin_tail (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C)
    (m s : Nat) (hm : 2 ≤ m) (hk : count C ≤ 2 * m) :
    2 ^ s * wordSum (step hψ ring) (fun D => binMiss m (count D)) C
      ((m + s) * (2 * deletionDenominator * binBlock n m)) ≤
      n ^ ((m + s) * (2 * deletionDenominator * binBlock n m)) := by
  let stepP := restrictedStep (step hψ ring) (SignalGlobal ring) (closed (κ := κ) hψ ring)
  have hmass : ∀ D : {D : Fin n → UCell ψ κ // SignalGlobal ring D},
      m < count D.val → count D.val ≤ 2 * m →
      n ^ binBlock n m ≤ deletionDenominator * wordSum stepP
        (fun E => if count E.val < count D.val then 1 else 0) D (binBlock n m) := by
    intro D hD _
    rw [wordSum_restrict (step hψ ring) (SignalGlobal ring) (closed hψ ring)
      (fun E : Fin n → UCell ψ κ => if count E < count D.val then 1 else 0)
      (binBlock n m) D]
    exact signalGlobal_bin_mass hψ ring D.val D.property m hm hD
  have ht := bin_tail stepP (fun D => count D.val) m (binBlock n m)
    deletionDenominator s deletion_denominator_pos
    (fun D e => step_count_nonincrease hψ ring D.val e) hmass ⟨C, hC⟩ hk
  rw [wordSum_restrict (step hψ ring) (SignalGlobal ring) (closed hψ ring)
    (fun D : Fin n → UCell ψ κ => binMiss m (count D))
    ((m + s) * (2 * deletionDenominator * binBlock n m)) ⟨C, hC⟩] at ht
  exact ht

/-- Descending bins are composed on their own actual physical endpoints.
The only bad event is that the final physical count still exceeds two. -/
theorem signalGlobal_dyadic_tail (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C)
    (L s : Nat) (hk : count C ≤ 2 ^ (L + 1)) :
    2 ^ s * wordSum (step hψ ring) (fun D => binMiss 2 (count D)) C
      (dyadicTime (binBlock n) deletionDenominator s L) ≤
      L * n ^ (dyadicTime (binBlock n) deletionDenominator s L) := by
  let stepP := restrictedStep (step hψ ring) (SignalGlobal ring) (closed (κ := κ) hψ ring)
  have hmass : ∀ m, 2 ≤ m →
      ∀ D : {D : Fin n → UCell ψ κ // SignalGlobal ring D},
      m < count D.val → count D.val ≤ 2 * m →
      n ^ binBlock n m ≤ deletionDenominator * wordSum stepP
        (fun E => if count E.val < count D.val then 1 else 0) D (binBlock n m) := by
    intro m hm D hD _
    rw [wordSum_restrict (step hψ ring) (SignalGlobal ring) (closed hψ ring)
      (fun E : Fin n → UCell ψ κ => if count E < count D.val then 1 else 0)
      (binBlock n m) D]
    exact signalGlobal_bin_mass hψ ring D.val D.property m hm hD
  have ht := dyadic_tail stepP (fun D => count D.val) (binBlock n)
    deletionDenominator s deletion_denominator_pos
    (fun D e => step_count_nonincrease hψ ring D.val e) hmass L ⟨C, hC⟩ hk
  rw [wordSum_restrict (step hψ ring) (SignalGlobal ring) (closed hψ ring)
    (fun D : Fin n → UCell ψ κ => binMiss 2 (count D))
    (dyadicTime (binBlock n) deletionDenominator s L) ⟨C, hC⟩] at ht
  exact ht

/-- A deterministic original-scheduler horizon for reducing to at most two
leaders. It is a proof clock; no protocol state or row contains this value. -/
def twoLeaderTime (n : Nat) : Nat :=
  dyadicTime (binBlock n) deletionDenominator (logSlack n) (Nat.log2 n)

/-- A finite-word `1/n` tail at a proved `O(n^2 log n)` physical horizon on
the actual closed signal domain. This does not identify count zero or one
with a legitimate output; the conclusion is explicitly `count <= 2`. -/
theorem signalGlobal_two_leader_whp (hψ : 0 < ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) :
    n * wordSum (step hψ ring) (fun D => binMiss 2 (count D)) C (twoLeaderTime n) ≤
      n ^ twoLeaderTime n ∧
    twoLeaderTime n ≤ 12 * deletionDenominator * (60 + 0 + 1) * n * n * Nat.log2 n := by
  have hstart : count C ≤ 2 ^ (Nat.log2 n + 1) :=
    Nat.le_trans (count_le_ring_size C) (log_parameters n hn).2.2.2
  have ht := signalGlobal_dyadic_tail hψ ring C hC (Nat.log2 n) (logSlack n) hstart
  have hslack : n * Nat.log2 n ≤ 2 ^ logSlack n :=
    Nat.le_trans (Nat.mul_le_mul_left n (Nat.le_succ (Nat.log2 n)))
      (logSlack_union_bound n hn)
  have hscaled : 2 ^ logSlack n *
      (n * wordSum (step hψ ring) (fun D => binMiss 2 (count D)) C (twoLeaderTime n)) ≤
      2 ^ logSlack n * n ^ twoLeaderTime n := by
    calc
      _ = n * (2 ^ logSlack n *
          wordSum (step hψ ring) (fun D => binMiss 2 (count D)) C (twoLeaderTime n)) :=
        Nat.mul_left_comm _ _ _
      _ ≤ n * (Nat.log2 n * n ^ twoLeaderTime n) := Nat.mul_le_mul_left n ht
      _ = (n * Nat.log2 n) * n ^ twoLeaderTime n := (Nat.mul_assoc _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hslack
  refine ⟨Nat.le_of_mul_le_mul_left hscaled (Nat.two_pow_pos _), ?_⟩
  exact dyadicTime_log_bound n 60 0 deletionDenominator hn

/-- The physical three-leader witness consumes the complete global block,
with arbitrary stored label modulus and no initial ready-shot premise. -/
theorem threeLeaderSeed_mass :
    count threeLeaderSeed = 3 ∧
    7 ^ countBlock 7 (count threeLeaderSeed) ≤ deletionDenominator *
      wordSum (step (by decide) NondivisibleExample.frame7.attack.ring)
        (fun D => if count D < count threeLeaderSeed then 1 else 0)
        threeLeaderSeed (countBlock 7 (count threeLeaderSeed)) :=
  ⟨by decide, signalGlobal_count_drop_mass (by decide)
    NondivisibleExample.frame7.attack.ring threeLeaderSeed threeLeaderSeed_global (by decide)⟩

end

end K2GlobalShortPairMass

#print axioms K2GlobalShortPairMass.count_le_ring_size
#print axioms K2GlobalShortPairMass.signalGlobal_short_pair
#print axioms K2GlobalShortPairMass.span_clock_le_countBlock
#print axioms K2GlobalShortPairMass.pair_count_drop_at_span
#print axioms K2GlobalShortPairMass.signalGlobal_count_drop_mass
#print axioms K2GlobalShortPairMass.signalGlobal_bin_mass
#print axioms K2GlobalShortPairMass.signalGlobal_bin_tail
#print axioms K2GlobalShortPairMass.signalGlobal_dyadic_tail
#print axioms K2GlobalShortPairMass.signalGlobal_two_leader_whp
#print axioms K2GlobalShortPairMass.threeLeaderSeed_mass
