import Leader.L3.Grant.ShortProduct
import Leader.L3.Small.RunFacts

/-!
# G17: the valid-phase cost of the abstract finite counter

On vectors of `small` fields in which every site holds a valid run value
`RUN j`, `j < K`, the abstract chain `shortAbsNext` is the tick/reset chain of
the paper's finite assertion.  The survival count of the first success is
bounded by the product of the one-site profiles (the discrete C.25, from
`shortCyclicStep`), and the profile sums give the expected time
`2^K + 1 + n (K-1) / 2` (C.22) with the sum invariant of `GrantShortProfile`.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The run value of a site (dead sites have value `K`). -/
def shortVal {n : Nat} (K : Nat) (s : Fin n → Small) (i : Fin n) : Nat :=
  match s i with
  | Small.RUN j => j.val
  | _ => K

/-- Every site holds a valid run value `RUN j`, `j < K`. -/
def ShortValid {n : Nat} (K : Nat) (s : Fin n → Small) : Prop :=
  ∀ i, ∃ j : Fin kStar, s i = Small.RUN j ∧ j.val < K

/-- The finite counter row at a valid initiator.

Consumer: `shortNextVal`. -/
theorem shortStepRun (k : Nat) (j : Fin kStar) (hj : j.val < k)
    (hk : k < kStar) (sy : Small) :
    shortStep k (Small.RUN j) sy =
      (if j.val + 1 < k then
        (Small.RUN ⟨j.val + 1, by omega⟩, smallRunZero, false)
      else (Small.SPENT, smallRunZero, true)) := by
  unfold shortStep
  have h1 : ¬ k ≤ j.val := by omega
  simp only [h1, if_false]
  by_cases h2 : j.val + 1 < k
  · simp only [h2, if_true]
    rw [smallRun_of_lt (j.val + 1) (by omega)]
  · simp only [h2, if_false]

/-- The abstract step at the initiator.

Consumer: `shortNextVal`. -/
theorem shortNextSelf {n : Nat} (ring : DirectedRing n) (K : Nat)
    (s : Fin n → Small) (e : Fin n) :
    shortNext ring K s e e = (shortStep K (s e) (s (ring.rightNeighbor e))).1 := by
  unfold shortNext
  rw [if_pos rfl]

/-- The abstract step at the responder.

Consumer: `shortNextVal`. -/
theorem shortNextResp {n : Nat} (ring : DirectedRing n) (K : Nat)
    (s : Fin n → Small) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    shortNext ring K s e (ring.rightNeighbor e) =
      (shortStep K (s e) (s (ring.rightNeighbor e))).2.1 := by
  unfold shortNext
  rw [if_neg hne, if_pos rfl]

/-- The abstract step away from the edge.

Consumer: `shortNextVal`. -/
theorem shortNextOther {n : Nat} (ring : DirectedRing n) (K : Nat)
    (s : Fin n → Small) (e i : Fin n) (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    shortNext ring K s e i = s i := by
  unfold shortNext
  rw [if_neg hie, if_neg hir]

/-- **The valid-phase update of the run values.**

Consumer: `shortProductInduction`. -/
theorem shortNextVal {n : Nat} (ring : DirectedRing n) (K : Nat)
    (hk : K < kStar) (s : Fin n → Small) (hs : ShortValid K s)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e) (e i : Fin n) :
    shortVal K (shortNext ring K s e) i =
      (if i = e then shortVal K s e + 1
       else if i = ring.rightNeighbor e then 0 else shortVal K s i) := by
  obtain ⟨j, hje, hjK⟩ := hs e
  have hrow := shortStepRun K j hjK hk (s (ring.rightNeighbor e))
  by_cases hie : i = e
  · subst hie
    rw [if_pos rfl]
    unfold shortVal
    rw [shortNextSelf, hje, hrow]
    by_cases h2 : j.val + 1 < K
    · simp [h2]
    · have : j.val + 1 = K := by omega
      simp [h2, this]
  · by_cases hir : i = ring.rightNeighbor e
    · rw [if_neg hie, if_pos hir]
      unfold shortVal
      rw [hir, shortNextResp ring K s e (hne e), hje, hrow]
      by_cases h2 : j.val + 1 < K <;> simp [h2, smallRunZero]
    · rw [if_neg hie, if_neg hir]
      unfold shortVal
      rw [shortNextOther ring K s e i hie hir]

/-- A step without success keeps the vector valid.

Consumer: `shortProductInduction`. -/
theorem shortNextValid {n : Nat} (ring : DirectedRing n) (K : Nat)
    (hk : K < kStar) (hK0 : 0 < K) (s : Fin n → Small) (hs : ShortValid K s)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (e : Fin n) (hsucc : shortSucc ring K s e = false) :
    ShortValid K (shortNext ring K s e) := by
  obtain ⟨j, hje, hjK⟩ := hs e
  have hrow := shortStepRun K j hjK hk (s (ring.rightNeighbor e))
  have h2 : j.val + 1 < K := by
    by_cases hh : j.val + 1 < K
    · exact hh
    · exfalso
      unfold shortSucc at hsucc
      rw [hje, hrow] at hsucc
      simp [hh] at hsucc
  intro i
  by_cases hie : i = e
  · subst hie
    rw [shortNextSelf, hje, hrow]
    simp only [h2, if_true]
    exact ⟨⟨j.val + 1, by omega⟩, rfl, h2⟩
  · by_cases hir : i = ring.rightNeighbor e
    · rw [hir, shortNextResp ring K s e (hne e), hje, hrow]
      simp only [h2, if_true]
      exact ⟨⟨0, by decide⟩, rfl, hK0⟩
    · rw [shortNextOther ring K s e i hie hir]
      exact hs i

/-- A step reports success exactly when the initiator is at `K-1`.

Consumer: `shortProductInduction`. -/
theorem shortSuccTrue {n : Nat} (ring : DirectedRing n) (K : Nat)
    (hk : K < kStar) (s : Fin n → Small) (hs : ShortValid K s) (e : Fin n)
    (hsucc : shortSucc ring K s e = true) :
    shortVal K s e + 1 = K := by
  obtain ⟨j, hje, hjK⟩ := hs e
  have hrow := shortStepRun K j hjK hk (s (ring.rightNeighbor e))
  unfold shortSucc at hsucc
  rw [hje, hrow] at hsucc
  have hv : shortVal K s e = j.val := by
    unfold shortVal
    rw [hje]
  rw [hv]
  show j.val + 1 = K
  by_cases hh : j.val + 1 < K
  · simp [hh] at hsucc
  · omega


/-- `List.ofFn` is the map over `finRange`.

Consumer: `shortProductInduction`. -/
theorem shortOfFnEqMap {n : Nat} (f : Fin n → Nat) :
    List.ofFn f = (List.finRange n).map f := by
  unfold List.finRange
  rw [List.map_ofFn]
  rfl

/-- A product of ones.

Consumer: `shortProductInduction`. -/
theorem shortProdOnes {α : Type} (l : List α) :
    (l.map (fun _ => 1)).prod = 1 := by
  induction l with
  | nil => simp
  | cons x L ih => simp [ih]

/-- A product of constants.

Consumer: `shortProductBound`. -/
theorem shortProdConst {α : Type} (c : Nat) (l : List α) :
    (l.map (fun _ => c)).prod = c ^ l.length := by
  induction l with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.prod_cons, ih, List.length_cons,
        Nat.pow_succ]
      rw [Nat.mul_comm]

/-- Products are monotone pointwise.

Consumer: `shortProductBound`. -/
theorem shortProdMono {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ x, x ∈ l → f x ≤ g x) →
      (l.map f).prod ≤ (l.map g).prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x L ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- A common factor pulls out of a list sum (on the right).

Consumer: `shortProductInduction`. -/
theorem shortSumMulRight {α : Type} (c : Nat) (g : α → Nat) :
    ∀ l : List α, (l.map (fun i => g i * c)).sum = (l.map g).sum * c := by
  intro l
  induction l with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-- **The discrete product comparison (C.25).**  For a valid vector the
number of words of length `t` without a success satisfies
`F_t n^(n t) ≤ n^t prod_i V_t(j_i)`.

Consumer: `shortProductBound`. -/
theorem shortProductInduction {n : Nat} (ring : DirectedRing n)
    (hn : 3 ≤ n) (K : Nat) (hK0 : 0 < K) (hk : K < kStar) :
    ∀ t (s : Fin n → Small), ShortValid K s →
      UniformFirstHit.survivalNumerator (shortAbsNext ring K)
          (fun z => z.2 = true) (s, false) t * n ^ (n * t) ≤
        n ^ t * shortProdFin (fun i => shortV n K t (shortVal K s i)) := by
  have hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e :=
    fun e => EWord.rightNeighborDifferent ring (by omega) e
  have hn2 : 2 ≤ n := by omega
  intro t
  induction t with
  | zero =>
      intro s hs
      rw [UniformFirstHit.survivalNumerator_zero_of_not _ _ _
        (by simp)]
      have h1 : shortProdFin (fun i => shortV n K 0 (shortVal K s i)) = 1 := by
        unfold shortProdFin
        have : ((List.finRange n).map (fun i => shortV n K 0 (shortVal K s i)))
            = (List.finRange n).map (fun _ => 1) := by
          apply List.map_congr_left
          intro i _
          obtain ⟨j, hje, hjK⟩ := hs i
          have hv : shortVal K s i = j.val := by
            unfold shortVal
            rw [hje]
          rw [hv]
          simp [shortV, hjK]
        rw [this, shortProdOnes]
      rw [h1]
      simp
  | succ t ih =>
      intro s hs
      rw [UniformFirstHit.survivalNumerator_succ_of_not _ _ _ (by simp)]
      have hmono : ∀ i, shortV n K t (shortVal K s i + 1) ≤
            shortV n K t (shortVal K s i) ∧
          shortV n K t (shortVal K s i) ≤ shortV n K t 0 :=
        fun i => ⟨shortVMonoJ n K hn2 hK0 t _, shortVLeZero n K hn2 hK0 t _⟩
      have hvalK : ∀ i, shortVal K s i < K := by
        intro i
        obtain ⟨j, hje, hjK⟩ := hs i
        have hv : shortVal K s i = j.val := by
          unfold shortVal
          rw [hje]
        rw [hv]
        exact hjK
      have hnext : ∀ i, shortV n K (t + 1) (shortVal K s i) =
          (n - 2) * shortV n K t (shortVal K s i) +
            shortV n K t (shortVal K s i + 1) + shortV n K t 0 := by
        intro i
        have := hvalK i
        simp [shortV, this]
      have htime : ∀ i, shortV n K t (shortVal K s i + 1) + shortV n K t 0 ≤
          2 * shortV n K t (shortVal K s i) := by
        intro i
        have h1 := shortVTimeMono n K hn2 hK0 t (shortVal K s i)
        rw [hnext i] at h1
        have hn' : n * shortV n K t (shortVal K s i) =
            (n - 2) * shortV n K t (shortVal K s i) +
              2 * shortV n K t (shortVal K s i) := by
          have hn3 : n = (n - 2) + 2 := by omega
          calc
            n * shortV n K t (shortVal K s i) =
                ((n - 2) + 2) * shortV n K t (shortVal K s i) := by
              rw [← hn3]
            _ = _ := Nat.add_mul _ _ _
        omega
      have hcyc := shortCyclicStep ring hn
        (fun i => shortV n K t (shortVal K s i))
        (fun i => shortV n K t (shortVal K s i + 1))
        (shortV n K t 0) hmono htime
      -- the term of each edge
      have hterm : ∀ e : Fin n,
          UniformFirstHit.survivalNumerator (shortAbsNext ring K)
            (fun z => z.2 = true)
            (shortAbsNext ring K (s, false) e) t * n ^ (n * t) ≤
          n ^ t * shortMoveProd ring
            (fun i => shortV n K t (shortVal K s i))
            (fun i => shortV n K t (shortVal K s i + 1))
            (shortV n K t 0) e := by
        intro e
        by_cases hsucc : shortSucc ring K s e = true
        · have htgt : (shortAbsNext ring K (s, false) e).2 = true := by
            show (false || shortSucc ring K s e) = true
            simp [hsucc]
          rw [UniformFirstHit.survivalNumerator_of_target
            (shortAbsNext ring K) (fun z => z.2 = true)
            (shortAbsNext ring K (s, false) e) htgt t]
          simp
        · have hsf : shortSucc ring K s e = false := by
            cases h : shortSucc ring K s e with
            | false => rfl
            | true => exact absurd h hsucc
          have hnx : shortAbsNext ring K (s, false) e =
              (shortNext ring K s e, false) := by
            unfold shortAbsNext
            simp [hsf]
          rw [hnx]
          have hv' := shortNextValid ring K hk hK0 s hs hne e hsf
          have h1 := ih (shortNext ring K s e) hv'
          have h2 : shortProdFin (fun i =>
              shortV n K t (shortVal K (shortNext ring K s e) i)) =
              shortMoveProd ring (fun i => shortV n K t (shortVal K s i))
                (fun i => shortV n K t (shortVal K s i + 1))
                (shortV n K t 0) e := by
            unfold shortProdFin shortMoveProd shortProdFin
            congr 1
            apply List.map_congr_left
            intro i _
            rw [shortNextVal ring K hk s hs hne e i]
            by_cases hie : i = e
            · subst hie
              simp
            · by_cases hir : i = ring.rightNeighbor e
              · subst hir
                simp [hne e]
              · simp [hie, hir]
          rw [h2] at h1
          exact h1
      -- sum over the edges
      have hsum :
          (List.ofFn (fun e => UniformFirstHit.survivalNumerator
            (shortAbsNext ring K) (fun z => z.2 = true)
            (shortAbsNext ring K (s, false) e) t)).sum * n ^ (n * t) ≤
          n ^ t * shortSumFin (shortMoveProd ring
            (fun i => shortV n K t (shortVal K s i))
            (fun i => shortV n K t (shortVal K s i + 1))
            (shortV n K t 0)) := by
        rw [shortOfFnEqMap, ← shortSumMulRight]
        unfold shortSumFin
        rw [← shortSumMulLeft]
        exact shortSumMono _ _ _ (fun e _ => hterm e)
      have hprod' : shortProdFin (fun i => shortV n K (t + 1) (shortVal K s i))
          = shortProdFin (fun i => (n - 2) * shortV n K t (shortVal K s i) +
            shortV n K t (shortVal K s i + 1) + shortV n K t 0) := by
        unfold shortProdFin
        congr 1
        apply List.map_congr_left
        intro i _
        exact hnext i
      rw [hprod']
      have hpw : n ^ n = n * n ^ (n - 1) := by
        have hn1 : n = (n - 1) + 1 := by omega
        calc
          n ^ n = n ^ ((n - 1) + 1) := by rw [← hn1]
          _ = n ^ (n - 1) * n := Nat.pow_succ _ _
          _ = n * n ^ (n - 1) := Nat.mul_comm _ _
      have hnt : n ^ (n * (t + 1)) = n ^ (n * t) * (n * n ^ (n - 1)) := by
        rw [Nat.mul_succ, Nat.pow_add, hpw]
      rw [hnt, Nat.pow_succ n t]
      generalize (List.ofFn (fun e => UniformFirstHit.survivalNumerator
        (shortAbsNext ring K) (fun z => z.2 = true)
        (shortAbsNext ring K (s, false) e) t)).sum = A at hsum ⊢
      generalize shortSumFin (shortMoveProd ring
        (fun i => shortV n K t (shortVal K s i))
        (fun i => shortV n K t (shortVal K s i + 1))
        (shortV n K t 0)) = M at hsum hcyc
      generalize shortProdFin (fun i => (n - 2) * shortV n K t (shortVal K s i)
        + shortV n K t (shortVal K s i + 1) + shortV n K t 0) = Q at hcyc ⊢
      generalize n ^ (n - 1) = a at hcyc ⊢
      generalize n ^ (n * t) = N at hsum ⊢
      generalize n ^ t = m at hsum ⊢
      calc
        A * (N * (n * a)) = n * a * (A * N) := by ac_rfl
        _ ≤ n * a * (m * M) := Nat.mul_le_mul_left _ hsum
        _ = n * m * (a * M) := by ac_rfl
        _ ≤ n * m * Q := Nat.mul_le_mul_left _ hcyc
        _ = m * n * Q := by ac_rfl


/-- The survival count against the profile power.

Consumer: `shortValidCost`. -/
theorem shortProductBound {n : Nat} (ring : DirectedRing n)
    (hn : 3 ≤ n) (K : Nat) (hK0 : 0 < K) (hk : K < kStar)
    (s : Fin n → Small) (hs : ShortValid K s) (t : Nat) :
    UniformFirstHit.survivalNumerator (shortAbsNext ring K)
        (fun z => z.2 = true) (s, false) t * n ^ ((n - 1) * t) ≤
      shortX n K t := by
  have hn2 : 2 ≤ n := by omega
  have h1 := shortProductInduction ring hn K hK0 hk t s hs
  have h2 : shortProdFin (fun i => shortV n K t (shortVal K s i)) ≤
      shortV n K t 0 ^ n := by
    unfold shortProdFin
    have := shortProdMono (fun i => shortV n K t (shortVal K s i))
      (fun _ => shortV n K t 0) (List.finRange n)
      (fun i _ => shortVLeZero n K hn2 hK0 t _)
    rw [shortProdConst, List.length_finRange] at this
    exact this
  have hpos : 0 < n ^ t := Nat.pow_pos (by omega)
  have hpw : n ^ (n * t) = n ^ ((n - 1) * t) * n ^ t := by
    rw [← Nat.pow_add]
    congr 1
    have hn1 : n = (n - 1) + 1 := by omega
    calc
      n * t = ((n - 1) + 1) * t := by rw [← hn1]
      _ = (n - 1) * t + t := by rw [Nat.add_mul, Nat.one_mul]
  rw [hpw] at h1
  have h3 : (UniformFirstHit.survivalNumerator (shortAbsNext ring K)
      (fun z => z.2 = true) (s, false) t * n ^ ((n - 1) * t)) * n ^ t ≤
      shortX n K t * n ^ t := by
    calc
      _ = UniformFirstHit.survivalNumerator (shortAbsNext ring K)
          (fun z => z.2 = true) (s, false) t *
          (n ^ ((n - 1) * t) * n ^ t) := Nat.mul_assoc _ _ _
      _ ≤ _ := h1
      _ ≤ n ^ t * shortV n K t 0 ^ n := Nat.mul_le_mul_left _ h2
      _ = shortX n K t * n ^ t := by
        unfold shortX
        exact Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h3 hpos

/-- The cost against the cumulative sum.

Consumer: `shortValidCost`. -/
theorem shortCostOfSurvival {S : Type} {n : Nat} (next : S → Fin n → S)
    (P : S → Prop) (x : S) (K : Nat) (hn : 1 ≤ n)
    (hF : ∀ t, UniformFirstHit.survivalNumerator next P x t *
        n ^ ((n - 1) * t) ≤ shortX n K t) :
    ∀ T, n ^ ((n - 1) * T) * costNumerator next P x T ≤ shortL n K T := by
  intro T
  induction T with
  | zero => simp [shortL]
  | succ T ih =>
      rw [UniformFirstHit.costNumerator_succ_eq]
      have hF' := hF T
      have e1 : n ^ ((n - 1) * (T + 1)) * n =
          n ^ ((n - 1) * T) * n ^ n := by
        have hn1 : n = (n - 1) + 1 := by omega
        calc
          n ^ ((n - 1) * (T + 1)) * n =
              n ^ ((n - 1) * T) * n ^ (n - 1) * n := by
            rw [Nat.mul_succ, Nat.pow_add]
          _ = n ^ ((n - 1) * T) * (n ^ (n - 1) * n) := Nat.mul_assoc _ _ _
          _ = n ^ ((n - 1) * T) * n ^ n := by
            have : (n - 1) + 1 = n := by omega
            rw [← Nat.pow_succ, Nat.succ_eq_add_one, this]
      simp only [shortL]
      calc
        n ^ ((n - 1) * (T + 1)) * (n * (costNumerator next P x T +
            UniformFirstHit.survivalNumerator next P x T)) =
            (n ^ ((n - 1) * (T + 1)) * n) * (costNumerator next P x T +
              UniformFirstHit.survivalNumerator next P x T) := by
          rw [Nat.mul_assoc]
        _ = n ^ n * (n ^ ((n - 1) * T) * costNumerator next P x T +
            UniformFirstHit.survivalNumerator next P x T *
              n ^ ((n - 1) * T)) := by
          rw [e1]
          simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
        _ ≤ n ^ n * (shortL n K T + shortX n K T) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add ih hF')

/-- **The valid-phase cost (C.22).**  From a valid vector the expected
number of steps to the first success of the finite counter is at most
`(2 (2^K + 1) + n (K-1) + 1) / 2`, that is `2^K + 1 + n(K-1)/2` rounded up.

Consumer: `grantShortCostBound` (GrantShortBound.lean). -/
theorem shortValidCost {n : Nat} (ring : DirectedRing n)
    (hn : 3 ≤ n) (K : Nat) (hK0 : 0 < K) (hk : K < kStar)
    (s : Fin n → Small) (hs : ShortValid K s) :
    ∀ T, costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T ≤
      n ^ T * ((2 * (2 ^ K + 1) + n * (K - 1) + 1) / 2) := by
  intro T
  have hn2 : 2 ≤ n := by omega
  have hcost := shortCostOfSurvival (shortAbsNext ring K)
    (fun z => z.2 = true) (s, false) K (by omega)
    (fun t => shortProductBound ring hn K hK0 hk s hs t) T
  have hsum := shortSumBound n K hn2 hK0 T
  have hGpos : 0 < n ^ ((n - 1) * T) := Nat.pow_pos (by omega)
  have hpw : n ^ (n * T) = n ^ ((n - 1) * T) * n ^ T := by
    rw [← Nat.pow_add]
    congr 1
    have hn1 : n = (n - 1) + 1 := by omega
    calc
      n * T = ((n - 1) + 1) * T := by rw [← hn1]
      _ = (n - 1) * T + T := by rw [Nat.add_mul, Nat.one_mul]
  have hK1 : n * K = n * (K - 1) + n := by
    have : K = (K - 1) + 1 := by omega
    calc
      n * K = n * ((K - 1) + 1) := by rw [← this]
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  rw [hpw, hK1] at hsum
  have hX : 2 * shortL n K T ≤
      (2 * (2 ^ K + 1) + n * (K - 1)) * (n ^ ((n - 1) * T) * n ^ T) := by
    have e : (2 * (2 ^ K + 1) + (n * (K - 1) + n)) *
        (n ^ ((n - 1) * T) * n ^ T) =
        (2 * (2 ^ K + 1) + n * (K - 1)) * (n ^ ((n - 1) * T) * n ^ T) +
          n * (n ^ ((n - 1) * T) * n ^ T) := by
      rw [← Nat.add_assoc, Nat.add_mul]
    rw [e] at hsum
    omega
  have h2 : 2 * costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T * n ^ ((n - 1) * T) ≤
      (2 * (2 ^ K + 1) + n * (K - 1)) * (n ^ ((n - 1) * T) * n ^ T) := by
    have e2 : 2 * costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T * n ^ ((n - 1) * T) =
        2 * (n ^ ((n - 1) * T) * costNumerator (shortAbsNext ring K)
          (fun z => z.2 = true) (s, false) T) := by ac_rfl
    rw [e2]
    omega
  have h3 : 2 * costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T ≤
      (2 * (2 ^ K + 1) + n * (K - 1)) * n ^ T := by
    have h4 : (2 * costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T) * n ^ ((n - 1) * T) ≤
        ((2 * (2 ^ K + 1) + n * (K - 1)) * n ^ T) * n ^ ((n - 1) * T) := by
      calc
        _ = 2 * costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
            (s, false) T * n ^ ((n - 1) * T) := rfl
        _ ≤ _ := h2
        _ = _ := by ac_rfl
    exact Nat.le_of_mul_le_mul_right h4 hGpos
  have h5 : (2 * (2 ^ K + 1) + n * (K - 1)) ≤
      2 * ((2 * (2 ^ K + 1) + n * (K - 1) + 1) / 2) := by omega
  have h6 := Nat.mul_le_mul_right (n ^ T) h5
  have h7 : 2 * costNumerator (shortAbsNext ring K) (fun z => z.2 = true)
        (s, false) T ≤
      2 * (n ^ T * ((2 * (2 ^ K + 1) + n * (K - 1) + 1) / 2)) := by
    calc
      _ ≤ _ := h3
      _ ≤ 2 * ((2 * (2 ^ K + 1) + n * (K - 1) + 1) / 2) * n ^ T := h6
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left h7 (by omega)

end L3

#print axioms L3.shortProductInduction
#print axioms L3.shortProductBound
#print axioms L3.shortValidCost
