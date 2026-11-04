import Leader.L3.Grant.ShortValid
import Leader.L3.ProbStages

/-!
# G17: the cover phase (coupon collector) of the finite counter

Before the valid-phase bound applies, every site must have been a responder
once (and so hold `RUN 0`) or a success must have been reported.  The number
of invalid sites falls at least by one on each edge whose responder is
invalid, so the harmonic potential
`H(u) = sum_{k<u} ceil(n/(k+1))`, `u` the number of invalid sites, drifts by
`-1` per step.  This is the paper's `E C = n H_n`, with each term rounded up.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The harmonic potential `sum_{k<u} ceil(n/(k+1))`.

Consumer: `shortCoverCost`. -/
def shortHarm (n u : Nat) : Nat :=
  ((List.range u).map (fun k => (n + k) / (k + 1))).sum

/-- The harmonic step `H(u+1) = H(u) + ceil(n/(u+1))`.

Consumer: `shortCoverDrift`. -/
theorem shortHarmSucc (n u : Nat) :
    shortHarm n (u + 1) = shortHarm n u + (n + u) / (u + 1) := by
  unfold shortHarm
  rw [List.range_succ, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]

/-- The harmonic potential is monotone.

Consumer: `shortCoverDrift`. -/
theorem shortHarmMono (n : Nat) {u v : Nat} (h : u ≤ v) :
    shortHarm n u ≤ shortHarm n v := by
  induction v with
  | zero =>
      have : u = 0 := by omega
      subst this
      exact Nat.le_refl _
  | succ v ih =>
      by_cases huv : u ≤ v
      · have := ih huv
        rw [shortHarmSucc]
        exact Nat.le_trans this (Nat.le_add_right _ _)
      · have : u = v + 1 := by omega
        subst this
        exact Nat.le_refl _

/-- The step `ceil(n/u)` covers `n`: `n ≤ u * ((n + u - 1)/u)`.

Consumer: `shortCoverDrift`. -/
theorem shortCeilCovers (n u : Nat) (hu : 0 < u) :
    n ≤ u * ((n + (u - 1)) / u) := by
  have h1 := Nat.div_add_mod (n + (u - 1)) u
  have h2 := Nat.mod_lt (n + (u - 1)) hu
  omega


/-- A site is invalid unless it holds `RUN j` with `j < K`.

Consumer: `shortCoverDrift`. -/
def shortInv {n : Nat} (K : Nat) (s : Fin n → Small) (i : Fin n) : Nat :=
  match s i with
  | Small.RUN j => if j.val < K then 0 else 1
  | _ => 1

/-- A member of a list is at most the list sum.

Consumer: `shortCoverDrift`. -/
theorem shortSumGeMem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons y L ih =>
      intro x hx
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst h
        omega
      · have := ih x h
        omega

/-- The sum of zeros.

Consumer: `shortSumSpike`. -/
theorem shortSumZero {α : Type} :
    ∀ l : List α, (l.map (fun _ => (0 : Nat))).sum = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons x L ih => simp [ih]

/-- The sum of a single spike.

Consumer: `shortCoverDrift`. -/
theorem shortSumSpike {α : Type} [DecidableEq α] (r : α) (c : Nat) :
    ∀ l : List α, l.Nodup → r ∈ l →
      (l.map (fun i => if i = r then c else 0)).sum = c := by
  intro l
  induction l with
  | nil => intro _ hr; cases hr
  | cons x L ih =>
      intro hnd hr
      have hnd' := List.nodup_cons.mp hnd
      simp only [List.map_cons, List.sum_cons]
      by_cases hxr : x = r
      · subst hxr
        have : (L.map (fun i => if i = x then c else 0)).sum = 0 := by
          have hz : L.map (fun i => if i = x then c else 0) =
              L.map (fun _ => 0) := by
            apply List.map_congr_left
            intro i hi
            have : i ≠ x := fun h => hnd'.1 (h ▸ hi)
            simp [this]
          rw [hz]
          exact shortSumZero L
        rw [this, if_pos rfl]
        omega
      · have hrL : r ∈ L := by
          rcases List.mem_cons.mp hr with h | h
          · exact absurd h.symm hxr
          · exact h
        rw [if_neg hxr, ih hnd'.2 hrL]
        omega


/-- The responder output of the finite counter row is always `RUN 0`.

Consumer: `shortInvNext`. -/
theorem shortStepSnd (k : Nat) (sx sy : Small) :
    (shortStep k sx sy).2.1 = smallRunZero := by
  unfold shortStep
  rcases sx with _ | _ | j
  · rfl
  · rfl
  · by_cases h1 : k ≤ j.val
    · simp [h1]
    · by_cases h2 : j.val + 1 < k <;> simp [h1, h2]

/-- `RUN 0` is valid when `K > 0`.

Consumer: `shortInvNext`. -/
theorem shortInvRunZero {n : Nat} (K : Nat) (hK0 : 0 < K)
    (s : Fin n → Small) (i : Fin n) (h : s i = smallRunZero) :
    shortInv K s i = 0 := by
  unfold shortInv
  rw [h]
  simp [smallRunZero, hK0]

/-- **Invalid sites do not appear; the responder becomes valid.**  Without a
success report, `inv(next, i) + [i = responder] inv(s, responder) ≤ inv(s, i)`.

Consumer: `shortCoverDrift`. -/
theorem shortInvNext {n : Nat} (ring : DirectedRing n) (K : Nat)
    (hk : K < kStar) (hK0 : 0 < K) (s : Fin n → Small)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (e : Fin n) (hsucc : shortSucc ring K s e = false) (i : Fin n) :
    shortInv K (shortNext ring K s e) i +
        (if i = ring.rightNeighbor e then
          shortInv K s (ring.rightNeighbor e) else 0) ≤ shortInv K s i := by
  by_cases hie : i = e
  · subst hie
    have hir : i ≠ ring.rightNeighbor i := fun h => hne i h.symm
    rw [if_neg hir]
    unfold shortInv
    rw [shortNextSelf]
    rcases hse : s i with _ | _ | j
    · simp [shortStep]
    · simp [shortStep]
    · by_cases h1 : K ≤ j.val
      · have : shortStep K (Small.RUN j) (s (ring.rightNeighbor i)) =
            (smallRunZero, smallRunZero, false) := by
          unfold shortStep
          simp [h1]
        rw [this]
        simp [smallRunZero, hK0]
      · have hjK : j.val < K := by omega
        have hrow := shortStepRun K j hjK hk (s (ring.rightNeighbor i))
        by_cases h2 : j.val + 1 < K
        · rw [hrow]
          simp [h2]
        · exfalso
          unfold shortSucc at hsucc
          rw [hse, hrow] at hsucc
          simp [h2] at hsucc
  · by_cases hir : i = ring.rightNeighbor e
    · rw [if_pos hir]
      have h0 : shortInv K (shortNext ring K s e) i = 0 := by
        apply shortInvRunZero K hK0
        rw [hir, shortNextResp ring K s e (hne e), shortStepSnd]
      rw [h0, hir]
      omega
    · rw [if_neg hir]
      unfold shortInv
      rw [shortNextOther ring K s e i hie hir]
      omega

/-- The number of invalid sites.

Consumer: `shortCoverDrift`. -/
def shortInvCount {n : Nat} (K : Nat) (s : Fin n → Small) : Nat :=
  shortSumFin (shortInv K s)

/-- The invalid count drops by the responder's invalidity.

Consumer: `shortCoverDrift`. -/
theorem shortInvCountNext {n : Nat} (ring : DirectedRing n) (K : Nat)
    (hk : K < kStar) (hK0 : 0 < K) (s : Fin n → Small)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (e : Fin n) (hsucc : shortSucc ring K s e = false) :
    shortInvCount K (shortNext ring K s e) +
        shortInv K s (ring.rightNeighbor e) ≤ shortInvCount K s := by
  unfold shortInvCount shortSumFin
  have h1 := shortSumMono
    (fun i => shortInv K (shortNext ring K s e) i +
      (if i = ring.rightNeighbor e then
        shortInv K s (ring.rightNeighbor e) else 0))
    (shortInv K s) (List.finRange n)
    (fun i _ => shortInvNext ring K hk hK0 s hne e hsucc i)
  rw [shortSumAdd, shortSumSpike (ring.rightNeighbor e) _
    (List.finRange n) (List.nodup_finRange n) (List.mem_finRange _)] at h1
  exact h1

/-- Each site contributes at most one.

Consumer: `shortCoverDrift`. -/
theorem shortInvLeOne {n : Nat} (K : Nat) (s : Fin n → Small) (i : Fin n) :
    shortInv K s i ≤ 1 := by
  unfold shortInv
  rcases s i with _ | _ | j
  · simp
  · simp
  · by_cases h : j.val < K <;> simp [h]


/-- Zero invalid count means valid.

Consumer: `shortCoverDrift`. -/
theorem shortValidOfInv {n : Nat} (K : Nat) (s : Fin n → Small)
    (h : ∀ i, shortInv K s i = 0) : ShortValid K s := by
  intro i
  have := h i
  unfold shortInv at this
  rcases hs : s i with _ | _ | j
  · rw [hs] at this
    simp at this
  · rw [hs] at this
    simp at this
  · rw [hs] at this
    by_cases hj : j.val < K
    · exact ⟨j, rfl, hj⟩
    · simp [hj] at this

/-- The potential of the cover phase: the harmonic number of the invalid
count, zero once a success has been reported.

Consumer: `shortCoverCost`. -/
def shortCoverPot {n : Nat} (K : Nat) (z : (Fin n → Small) × Bool) : Nat :=
  if z.2 = true then 0 else shortHarm n (shortInvCount K z.1)

/-- **The harmonic drift.**  Off the cover target the potential drifts by
`-1` per step: `n + sum_e pot(next) ≤ n pot`.

Consumer: `shortCoverCost`. -/
theorem shortCoverDrift {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (K : Nat) (hk : K < kStar) (hK0 : 0 < K) :
    ∀ z : (Fin n → Small) × Bool,
      ¬ (z.2 = true ∨ ShortValid K z.1) →
      n + (List.ofFn (fun e : Fin n =>
          shortCoverPot K (shortAbsNext ring K z e))).sum ≤
        n * shortCoverPot K z := by
  have hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e :=
    fun e => EWord.rightNeighborDifferent ring (by omega) e
  intro z hz
  obtain ⟨s, d⟩ := z
  have hd : d = false := by
    cases d with
    | false => rfl
    | true => exact absurd (Or.inl rfl) hz
  subst hd
  have hnv : ¬ ShortValid K s := fun h => hz (Or.inr h)
  have hpot : shortCoverPot K ((s, false) : (Fin n → Small) × Bool) =
      shortHarm n (shortInvCount K s) := by
    unfold shortCoverPot
    simp
  rw [hpot]
  -- the invalid count is between 1 and n
  have hu1 : 1 ≤ shortInvCount K s := by
    have : ∃ i, shortInv K s i ≠ 0 := by
      by_cases hall : ∀ i, shortInv K s i = 0
      · exact absurd (shortValidOfInv K s hall) hnv
      · exact by
          have := hall
          simpa using this
    obtain ⟨i, hi⟩ := this
    have hi1 : 1 ≤ shortInv K s i := by omega
    have := shortSumGeMem (shortInv K s) (List.finRange n) i
      (List.mem_finRange i)
    unfold shortInvCount shortSumFin
    omega
  have hun : shortInvCount K s ≤ n := by
    have h1 := shortSumMono (shortInv K s) (fun _ => 1) (List.finRange n)
      (fun i _ => shortInvLeOne K s i)
    rw [shortSumConst, List.length_finRange] at h1
    unfold shortInvCount shortSumFin
    omega
  obtain ⟨u', hu'⟩ : ∃ u', shortInvCount K s = u' + 1 := ⟨shortInvCount K s - 1, by omega⟩
  rw [hu'] at hun
  rw [hu', shortHarmSucc]
  -- per edge bound
  have hedge : ∀ e : Fin n,
      shortCoverPot K (shortAbsNext ring K (s, false) e) ≤
        shortHarm n (u' + 1 - shortInv K s (ring.rightNeighbor e)) := by
    intro e
    by_cases hsucc : shortSucc ring K s e = true
    · have : (shortAbsNext ring K (s, false) e).2 = true := by
        show (false || shortSucc ring K s e) = true
        simp [hsucc]
      unfold shortCoverPot
      rw [if_pos this]
      exact Nat.zero_le _
    · have hsf : shortSucc ring K s e = false := by
        cases h : shortSucc ring K s e with
        | false => rfl
        | true => exact absurd h hsucc
      have hnd : (shortAbsNext ring K (s, false) e).2 = false := by
        show (false || shortSucc ring K s e) = false
        simp [hsf]
      unfold shortCoverPot
      rw [if_neg (by simp [hnd])]
      have hc := shortInvCountNext ring K hk hK0 s hne e hsf
      rw [hu'] at hc
      apply shortHarmMono
      show shortInvCount K (shortNext ring K s e) ≤ _
      omega
  -- sum over the edges
  have hsum1 : (List.ofFn (fun e : Fin n =>
      shortCoverPot K (shortAbsNext ring K (s, false) e))).sum ≤
      ((List.finRange n).map (fun i =>
        shortHarm n (u' + 1 - shortInv K s i))).sum := by
    rw [shortOfFnEqMap, ← shortRingShift ring
      (fun i => shortHarm n (u' + 1 - shortInv K s i))]
    exact shortSumMono _ _ _ (fun e _ => hedge e)
  -- H(u - inv_i) + inv_i * delta = H(u)
  have hpt : ∀ i : Fin n,
      shortHarm n (u' + 1 - shortInv K s i) +
        shortInv K s i * ((n + u') / (u' + 1)) =
      shortHarm n u' + (n + u') / (u' + 1) := by
    intro i
    have h1 := shortInvLeOne K s i
    by_cases h0 : shortInv K s i = 0
    · rw [h0]
      simp only [Nat.sub_zero, Nat.zero_mul, Nat.add_zero]
      rw [shortHarmSucc]
    · have h2 : shortInv K s i = 1 := by omega
      rw [h2]
      simp only [Nat.add_sub_cancel, Nat.one_mul]
  have hsum2 : ((List.finRange n).map (fun i =>
        shortHarm n (u' + 1 - shortInv K s i))).sum +
      (u' + 1) * ((n + u') / (u' + 1)) =
      n * (shortHarm n u' + (n + u') / (u' + 1)) := by
    have e1 := shortSumAdd
      (fun i => shortHarm n (u' + 1 - shortInv K s i))
      (fun i => shortInv K s i * ((n + u') / (u' + 1))) (List.finRange n)
    have e2 : ((List.finRange n).map (fun i =>
        shortHarm n (u' + 1 - shortInv K s i) +
          shortInv K s i * ((n + u') / (u' + 1)))).sum =
        ((List.finRange n).map (fun _ =>
          shortHarm n u' + (n + u') / (u' + 1))).sum := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact hpt i
    rw [e1, shortSumConst, List.length_finRange] at e2
    have e3 := shortSumMulRight ((n + u') / (u' + 1)) (shortInv K s)
      (List.finRange n)
    have e4 : ((List.finRange n).map (shortInv K s)).sum = u' + 1 := by
      have := hu'
      unfold shortInvCount shortSumFin at this
      exact this
    rw [e3, e4] at e2
    exact e2
  have hcov := shortCeilCovers n (u' + 1) (by omega)
  have hu1' : u' + 1 - 1 = u' := by omega
  rw [hu1'] at hcov
  calc
    n + (List.ofFn (fun e : Fin n =>
        shortCoverPot K (shortAbsNext ring K (s, false) e))).sum ≤
        n + ((List.finRange n).map (fun i =>
          shortHarm n (u' + 1 - shortInv K s i))).sum :=
      Nat.add_le_add_left hsum1 _
    _ ≤ n * (shortHarm n u' + (n + u') / (u' + 1)) := by omega


/-- The invalid count is at most `n`.

Consumer: `shortCoverCost`. -/
theorem shortInvCountLe {n : Nat} (K : Nat) (s : Fin n → Small) :
    shortInvCount K s ≤ n := by
  have h1 := shortSumMono (shortInv K s) (fun _ => 1) (List.finRange n)
    (fun i _ => shortInvLeOne K s i)
  rw [shortSumConst, List.length_finRange] at h1
  unfold shortInvCount shortSumFin
  omega

/-- **The cover cost.**  From any vector of `small` fields the expected time
to a valid vector or a success report is at most `H(n) = sum_{k<n}
ceil(n/(k+1))`.

Consumer: `shortAbsCost`. -/
theorem shortCoverCost {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (K : Nat) (hk : K < kStar) (hK0 : 0 < K) (s : Fin n → Small) :
    ∀ T, costNumerator (shortAbsNext ring K)
        (fun z => z.2 = true ∨ ShortValid K z.1) (s, false) T ≤
      n ^ T * shortHarm n n := by
  intro T
  have h := Prob.costNumerator_le_of_potential (shortAbsNext ring K)
    (fun z => z.2 = true ∨ ShortValid K z.1) (shortCoverPot K)
    (shortCoverDrift ring hn K hk hK0) (s, false) T
  have hpot : shortCoverPot K ((s, false) : (Fin n → Small) × Bool) ≤
      shortHarm n n := by
    unfold shortCoverPot
    simp only [Bool.false_eq_true, if_false]
    exact shortHarmMono n (shortInvCountLe K s)
  exact Nat.le_trans h (Nat.mul_le_mul_left _ hpot)

/-- **The abstract finite-counter cost (C.22 with the cover).**  From any
vector of `small` fields, the expected number of steps to the first success
is at most `H(n) + (2 (2^K + 1) + n (K-1) + 1) / 2`.

Consumer: `grantShortCostBound` (GrantShortBound.lean). -/
theorem shortAbsCost {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (K : Nat) (hk : K < kStar) (hK0 : 0 < K) (s : Fin n → Small) :
    ∀ T, costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T ≤
      n ^ T * (shortHarm n n +
        (2 * (2 ^ K + 1) + n * (K - 1) + 1) / 2) := by
  have h := Prob.costNumerator_stage_le (shortAbsNext ring K) (s, false)
    (fun z => ShortValid K z.1 ∧ z.2 = false) (fun z => z.2 = true)
    (shortHarm n n) ((2 * (2 ^ K + 1) + n * (K - 1) + 1) / 2)
    (by
      intro T
      have h1 := Prob.costNumerator_target_mono (shortAbsNext ring K)
        (fun z => z.2 = true ∨ ShortValid K z.1)
        (fun z => (ShortValid K z.1 ∧ z.2 = false) ∨ z.2 = true)
        (by
          intro z hz
          rcases hz with h | h
          · exact Or.inr h
          · cases hd : z.2 with
            | true => exact Or.inr rfl
            | false => exact Or.inl ⟨h, rfl⟩)
        (s, false) T
      exact Nat.le_trans h1 (shortCoverCost ring hn K hk hK0 s T))
    (by
      intro y hy T
      obtain ⟨hv, hd⟩ := hy
      have : y = (y.1, false) := by
        cases y with
        | mk a b =>
            simp only at hd
            rw [hd]
      rw [this]
      exact shortValidCost ring hn K hK0 hk y.1 hv T)
  exact h

end L3

#print axioms L3.shortCoverDrift
#print axioms L3.shortCoverCost
#print axioms L3.shortAbsCost
