import Leader.Wu.Scheduler.LeaderCountExpectedCost
import Leader.Wu.Scheduler.FixedSpanRenewalPayload
import Leader.Core.UniformBlockRenewal
import Leader.Core.BellmanGeometricTail


namespace BirthPhaseGenericRenewal


open FiniteUniformStoppingTree


set_option autoImplicit false
set_option pp.structureInstances false


/-- The renewal domain.  `Reacquire` is the explicit B1 side state; if B1 is
folded into the block, instantiate it by `fun _ => False`. -/
def RenewalAllowed {S : Type} (Carrier Reacquire : S → Prop) (x : S) : Prop :=
  Carrier x ∨ Reacquire x


/-- The active stopped-tree state contains the actual full configuration. -/
abbrev RenewalState {S : Type} (Carrier Reacquire : S → Prop) :=
  {x : S // RenewalAllowed Carrier Reacquire x}


/-- Execute one literal raw scheduler word. -/
def rawEndpoint {S : Type} {n : Nat}
    (step : S → Fin n → S) (x : S) (u : List (Fin n)) : S :=
  u.foldl step x


/-- Indicator used in the B4 `wordSum` mass hypothesis. -/
def goodWeight {S : Type} {n : Nat}
    (good : S → List (Fin n) → Bool) (x : S) (u : List (Fin n)) : Nat :=
  if good x u = true then 1 else 0


private theorem bool_eq_false_of_ne_true (b : Bool) (h : ¬ b = true) :
    b = false := by
  cases b <;> simp_all


/-- One macro trial, indexed by the repository's exact enumeration of
length-`L` raw words.  It stops on the target or on B4's good event. -/
def trialStep {S : Type} {n L : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u)) :
    RenewalState Carrier Reacquire → Fin (n ^ L) →
      StopNode (RenewalState Carrier Reacquire) :=
  fun x i =>
    let u := FixedSpanRenewalPayload.rawWord n L i
    if ht : target x.1 u = true then
      .success
    else if hg : good x.1 u = true then
      .success
    else
      .active ⟨rawEndpoint step x.1 u,
        hclosed x.1 x.2 u
          (by
            simpa [u] using
              FixedSpanRenewalPayload.rawWord_length n L i)
          (bool_eq_false_of_ne_true _ ht)⟩


/-- The target-only macro process.  Strict rank drops remain active at their
actual physical endpoint and therefore contribute their smaller potential to
the next block. -/
def targetStep {S : Type} {n L : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    (target : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u)) :
    RenewalState Carrier Reacquire → Fin (n ^ L) →
      StopNode (RenewalState Carrier Reacquire) :=
  fun x i =>
    let u := FixedSpanRenewalPayload.rawWord n L i
    if ht : target x.1 u = true then
      .success
    else
      .active ⟨rawEndpoint step x.1 u,
        hclosed x.1 x.2 u
          (by
            simpa [u] using
              FixedSpanRenewalPayload.rawWord_length n L i)
          (bool_eq_false_of_ne_true _ ht)⟩


/-- Natural Bellman potential for rank composition. -/
def rankPotential {S : Type}
    (Carrier Reacquire : S → Prop) (rank : S → Nat) (Q : Nat) :
    StopNode (RenewalState Carrier Reacquire) → Nat
  | .active x => Q * rank x.1
  | .success => 0
  | .failure => 0


/-- Number of macro words that have not yet hit the target.  Its raw scheduler
denominator after `b` blocks is `(n^L)^b = n^(L*b)`. -/
def targetFailureNumerator {S : Type} {n L : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    (target : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u))
    (x : RenewalState Carrier Reacquire) (blocks : Nat) : Nat :=
  activeCount (targetStep step Carrier Reacquire target hclosed)
    (.active x) blocks


private theorem trial_successCount_ge_goodWordSum
    {S : Type} {n L : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u))
    (x : RenewalState Carrier Reacquire) :
    FixedSpanRenewalPayload.wordSum n L (goodWeight good x.1) ≤
      successCount
        (trialStep step Carrier Reacquire target good hclosed)
        (.active x) 1 := by
  rw [← FixedSpanRenewalPayload.rawWord_sum n L (goodWeight good x.1)]
  change
    (List.ofFn (fun i : Fin (n ^ L) =>
      goodWeight good x.1 (FixedSpanRenewalPayload.rawWord n L i))).sum ≤
    (List.ofFn (fun i : Fin (n ^ L) =>
      successWeight
        (trialStep step Carrier Reacquire target good hclosed x i))).sum
  apply ofFn_sum_le
  intro i
  let u := FixedSpanRenewalPayload.rawWord n L i
  by_cases ht : target x.1 u = true
  · simp [trialStep, goodWeight, successWeight, u, ht]
    split <;> omega
  · by_cases hg : good x.1 u = true
    · simp [trialStep, goodWeight, successWeight, u, ht, hg]
    · simp [trialStep, goodWeight, successWeight, u, ht, hg]


private theorem trialStep_ne_failure
    {S : Type} {n L : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u)) :
    ∀ x i,
      trialStep step Carrier Reacquire target good hclosed x i ≠ .failure := by
  intro x i
  let u := FixedSpanRenewalPayload.rawWord n L i
  by_cases ht : target x.1 u = true
  · simp [trialStep, u, ht]
  · by_cases hg : good x.1 u = true
    · simp [trialStep, u, ht, hg]
    · simp [trialStep, u, ht, hg]


/-- Exact `(1-1/Q)^k`-style contraction for avoiding both the target and B4's
good event.  Every macro symbol is one literal length-`L` raw scheduler word. -/
theorem good_or_target_avoidance_geometric
    {S : Type} {n L Q : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    [DecidablePred Carrier] [DecidablePred Reacquire]
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u))
    (hQ : 0 < Q)
    (hmass : ∀ x, RenewalAllowed Carrier Reacquire x →
      n ^ L ≤ Q *
        FixedSpanRenewalPayload.wordSum n L (goodWeight good x))
    (x : S) (hx : Carrier x) (k : Nat) :
    Q ^ k *
        activeCount
          (trialStep step Carrier Reacquire target good hclosed)
          (.active (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)) k ≤
      (Q - 1) ^ k * n ^ (L * k) := by
  let z : RenewalState Carrier Reacquire := ⟨x, Or.inl hx⟩
  have hblock : ∀ y : RenewalState Carrier Reacquire,
      (n ^ L) ^ (1 * 1) ≤
        Q * successCount
          (trialStep step Carrier Reacquire target good hclosed)
          (.active y) (1 * 1) := by
    intro y
    have hm := hmass y.1 y.2
    have hs := trial_successCount_ge_goodWordSum
      step Carrier Reacquire target good hclosed y
    have hscaled := Nat.mul_le_mul_left Q hs
    simpa using Nat.le_trans hm hscaled
  have ht := UniformBlockRenewal.block_tail
    (step := trialStep step Carrier Reacquire target good hclosed)
    (K := 1) (q := 1) (q' := Q)
    hQ
    (trialStep_ne_failure step Carrier Reacquire target good hclosed)
    hblock z k
  have ht' :
      Q ^ k *
          activeCount
            (trialStep step Carrier Reacquire target good hclosed)
            (.active z) k ≤
        (Q - 1) ^ k * (n ^ L) ^ k := by
    simpa [UniformBlockRenewal.retry] using ht
  calc
    Q ^ k *
        activeCount
          (trialStep step Carrier Reacquire target good hclosed)
          (.active (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)) k ≤
      (Q - 1) ^ k * (n ^ L) ^ k := by
        simpa [z] using ht'
    _ = (Q - 1) ^ k * n ^ (L * k) := by
      rw [Nat.pow_mul]


private theorem rankPotential_super
    {S : Type} {n L Q : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    (rank : S → Nat)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u))
    (hpos : ∀ x, RenewalAllowed Carrier Reacquire x → 1 ≤ rank x)
    (hmono : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        rank (rawEndpoint step x u) ≤ rank x)
    (hgood : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → good x u = true →
        target x u = true ∨ rank (rawEndpoint step x u) < rank x)
    (hmass : ∀ x, RenewalAllowed Carrier Reacquire x →
      n ^ L ≤ Q *
        FixedSpanRenewalPayload.wordSum n L (goodWeight good x)) :
    NatBellmanSuperSolution
      (targetStep step Carrier Reacquire target hclosed) 1
      (rankPotential Carrier Reacquire rank Q) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  rw [Nat.one_mul]
  rw [show
    rankPotential Carrier Reacquire rank Q (.active x) =
      Q * rank x.1 by rfl]
  have hpoint : ∀ i : Fin (n ^ L),
      rankPotential Carrier Reacquire rank Q
          (targetStep step Carrier Reacquire target hclosed x i) +
          Q * goodWeight good x.1
            (FixedSpanRenewalPayload.rawWord n L i) ≤
        Q * rank x.1 := by
    intro i
    let u := FixedSpanRenewalPayload.rawWord n L i
    have hlen : u.length = L := by
      simpa [u] using FixedSpanRenewalPayload.rawWord_length n L i
    by_cases ht : target x.1 u = true
    · by_cases hg : good x.1 u = true
      · have hq : Q ≤ Q * rank x.1 := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left Q (hpos x.1 x.2)
        simpa [targetStep, rankPotential, goodWeight, u, ht, hg] using hq
      · simpa [targetStep, rankPotential, goodWeight, u, ht, hg] using
          (Nat.zero_le (Q * rank x.1))
    · have htf : target x.1 u = false :=
        bool_eq_false_of_ne_true _ ht
      by_cases hg : good x.1 u = true
      · have hs := hgood x.1 x.2 u hlen hg
        have hd : rank (rawEndpoint step x.1 u) < rank x.1 := by
          rcases hs with hs | hs
          · exact (ht hs).elim
          · exact hs
        have hsucc : rank (rawEndpoint step x.1 u) + 1 ≤ rank x.1 := by
          omega
        have hq :
            Q * rank (rawEndpoint step x.1 u) + Q ≤ Q * rank x.1 := by
          calc
            Q * rank (rawEndpoint step x.1 u) + Q =
                Q * (rank (rawEndpoint step x.1 u) + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
            _ ≤ Q * rank x.1 := Nat.mul_le_mul_left Q hsucc
        simpa [targetStep, rankPotential, goodWeight, u, ht, hg] using hq
      · have hm := Nat.mul_le_mul_left Q
          (hmono x.1 x.2 u hlen htf)
        simpa [targetStep, rankPotential, goodWeight, u, ht, hg] using hm
  have hsum := ofFn_sum_le
    (fun i : Fin (n ^ L) =>
      rankPotential Carrier Reacquire rank Q
          (targetStep step Carrier Reacquire target hclosed x i) +
        Q * goodWeight good x.1 (FixedSpanRenewalPayload.rawWord n L i))
    (fun _ : Fin (n ^ L) => Q * rank x.1) hpoint
  rw [ofFn_sum_add, ofFn_sum_mul_left,
    FixedSpanRenewalPayload.rawWord_sum n L (goodWeight good x.1),
    ofFn_sum_const] at hsum
  have hm := hmass x.1 x.2
  calc
    n ^ L +
        (List.ofFn (fun i : Fin (n ^ L) =>
          rankPotential Carrier Reacquire rank Q
            (targetStep step Carrier Reacquire target hclosed x i))).sum ≤
      Q * FixedSpanRenewalPayload.wordSum n L (goodWeight good x.1) +
        (List.ofFn (fun i : Fin (n ^ L) =>
          rankPotential Carrier Reacquire rank Q
            (targetStep step Carrier Reacquire target hclosed x i))).sum :=
      Nat.add_le_add_right hm _
    _ =
      (List.ofFn (fun i : Fin (n ^ L) =>
          rankPotential Carrier Reacquire rank Q
            (targetStep step Carrier Reacquire target hclosed x i))).sum +
        Q * FixedSpanRenewalPayload.wordSum n L (goodWeight good x.1) := by
      ac_rfl
    _ ≤ n ^ L * (Q * rank x.1) := hsum


private theorem rankPotential_bound
    {S : Type} {Q R : Nat}
    (Carrier Reacquire : S → Prop) (rank : S → Nat)
    (hbound : ∀ x, RenewalAllowed Carrier Reacquire x → rank x ≤ R) :
    ∀ z, rankPotential Carrier Reacquire rank Q z ≤ Q * R := by
  intro z
  cases z with
  | success => simp [rankPotential]
  | failure => simp [rankPotential]
  | active x =>
      simpa [rankPotential] using Nat.mul_le_mul_left Q (hbound x.1 x.2)


/-- Number of Bellman half-life blocks per rank budget. -/
def renewalK (Q s : Nat) : Nat := 2 * Q * s


/-- Explicit coefficient used for the `1/n` corollary. -/
def oneOverNK (n Q : Nat) : Nat :=
  renewalK Q (Nat.log2 n + 1)


/-- Rank-composed target tail.  There are `renewalK Q s * R` literal
length-`L` blocks, hence raw horizon `renewalK Q s * L * R`. -/
theorem target_failure_geometric
    {S : Type} {n L Q R : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    [DecidablePred Carrier] [DecidablePred Reacquire]
    (rank : S → Nat)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u))
    (hpos : ∀ x, RenewalAllowed Carrier Reacquire x → 1 ≤ rank x)
    (hbound : ∀ x, RenewalAllowed Carrier Reacquire x → rank x ≤ R)
    (hmono : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        rank (rawEndpoint step x u) ≤ rank x)
    (hgood : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → good x u = true →
        target x u = true ∨ rank (rawEndpoint step x u) < rank x)
    (hmass : ∀ x, RenewalAllowed Carrier Reacquire x →
      n ^ L ≤ Q *
        FixedSpanRenewalPayload.wordSum n L (goodWeight good x))
    (hn : 0 < n) (hQ : 0 < Q)
    (x : S) (hx : Carrier x) (s : Nat) :
    2 ^ s *
        targetFailureNumerator step Carrier Reacquire target hclosed
          (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)
          (renewalK Q s * R) ≤
      n ^ (renewalK Q s * L * R) := by
  have hbell := rankPotential_super
    step Carrier Reacquire rank target good hclosed hpos hmono hgood hmass
  have hB := rankPotential_bound (Q := Q)
    Carrier Reacquire rank hbound
  have ht := BellmanGeometricTail.geometric_tail
    (step := targetStep step Carrier Reacquire target hclosed)
    (potential := rankPotential Carrier Reacquire rank Q)
    hbell hB (Nat.pow_pos hn)
    (.active (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)) s
  have hk :
      s * (2 * (Q * R)) = renewalK Q s * R := by
    unfold renewalK
    ac_rfl
  rw [hk] at ht
  have ht' :
      2 ^ s *
          targetFailureNumerator step Carrier Reacquire target hclosed
            (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)
            (renewalK Q s * R) ≤
        (n ^ L) ^ (renewalK Q s * R) := by
    simpa [targetFailureNumerator] using ht
  calc
    2 ^ s *
        targetFailureNumerator step Carrier Reacquire target hclosed
          (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)
          (renewalK Q s * R) ≤
      (n ^ L) ^ (renewalK Q s * R) := ht'
    _ = n ^ (L * (renewalK Q s * R)) := by
      rw [← Nat.pow_mul]
    _ = n ^ (renewalK Q s * L * R) := by
      congr 1
      ac_rfl


/-- Explicit original-scheduler `1/n` failure numerator.  The coefficient is
`k(n)=2*Q*(log2 n+1)` and the raw horizon is `k(n)*L*R`. -/
theorem target_failure_le_one_over_n
    {S : Type} {n L Q R : Nat}
    (step : S → Fin n → S)
    (Carrier Reacquire : S → Prop)
    [DecidablePred Carrier] [DecidablePred Reacquire]
    (rank : S → Nat)
    (target good : S → List (Fin n) → Bool)
    (hclosed : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        RenewalAllowed Carrier Reacquire (rawEndpoint step x u))
    (hpos : ∀ x, RenewalAllowed Carrier Reacquire x → 1 ≤ rank x)
    (hbound : ∀ x, RenewalAllowed Carrier Reacquire x → rank x ≤ R)
    (hmono : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → target x u = false →
        rank (rawEndpoint step x u) ≤ rank x)
    (hgood : ∀ x, RenewalAllowed Carrier Reacquire x →
      ∀ u, u.length = L → good x u = true →
        target x u = true ∨ rank (rawEndpoint step x u) < rank x)
    (hmass : ∀ x, RenewalAllowed Carrier Reacquire x →
      n ^ L ≤ Q *
        FixedSpanRenewalPayload.wordSum n L (goodWeight good x))
    (hn : 2 ≤ n) (hQ : 0 < Q)
    (x : S) (hx : Carrier x) :
    n *
        targetFailureNumerator step Carrier Reacquire target hclosed
          (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)
          (oneOverNK n Q * R) ≤
      n ^ (oneOverNK n Q * L * R) := by
  let s := Nat.log2 n + 1
  have ht := target_failure_geometric
    step Carrier Reacquire rank target good
    hclosed hpos hbound hmono hgood hmass (by omega) hQ x hx s
  have ht' :
      2 ^ s *
          targetFailureNumerator step Carrier Reacquire target hclosed
            (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)
            (oneOverNK n Q * R) ≤
        n ^ (oneOverNK n Q * L * R) := by
    simpa [s, oneOverNK] using ht
  have hpow : n ≤ 2 ^ s := by
    simpa [s] using
      (LeaderCountDyadicTail.log_parameters n hn).2.2.2
  have hscaled := Nat.mul_le_mul_right
    (targetFailureNumerator step Carrier Reacquire target hclosed
      (⟨x, Or.inl hx⟩ : RenewalState Carrier Reacquire)
      (oneOverNK n Q * R)) hpow
  exact Nat.le_trans hscaled ht'


end BirthPhaseGenericRenewal


#print axioms BirthPhaseGenericRenewal.good_or_target_avoidance_geometric
#print axioms BirthPhaseGenericRenewal.target_failure_geometric
#print axioms BirthPhaseGenericRenewal.target_failure_le_one_over_n
