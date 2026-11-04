import Leader.L3.Grant.ShortProfile

/-!
# G17: the product comparison on the ring

The paper's comparison (C.23)--(C.25) bounds the survival of the whole ring by
the product of the isolated-site survivals.  In discrete time the one-step
comparison is
`n^(n-1) * sum_e prod_i g_e(i) <= prod_i V'(i)`: the scheduler move at the edge
`e` ticks the initiator `e` and resets the responder `e+1`, and the product of
the one-site updates dominates the average of these moves because the tick
lowers and the reset raises a monotone factor, and the one-site updates are
nonincreasing in time (the factors `V'(i)` are at most `n h(i)`).
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-! ### Products over a list of distinct indices -/

/-- Pulling one factor out of a product over a duplicate-free list.

Consumer: `shortReplaceProd`. -/
theorem shortEraseProd {α : Type} [DecidableEq α] (f : α → Nat) :
    ∀ (l : List α), l.Nodup → ∀ i, i ∈ l →
      (l.map f).prod = f i * ((l.erase i).map f).prod := by
  intro l
  induction l with
  | nil => intro _ i hi; cases hi
  | cons x L ih =>
      intro hnd i hi
      by_cases hxi : x = i
      · subst hxi
        simp
      · have hiL : i ∈ L := by
          rcases List.mem_cons.mp hi with h | h
          · exact absurd h.symm hxi
          · exact h
        have hnd' := (List.nodup_cons.mp hnd).2
        rw [List.erase_cons_tail (by simpa using hxi)]
        simp only [List.map_cons, List.prod_cons]
        rw [ih hnd' i hiL]
        ac_rfl

/-- Replacing one factor of a product over a duplicate-free list.

Consumer: `shortReplacePairProd`. -/
theorem shortReplaceProd {α : Type} [DecidableEq α] (f : α → Nat) (a : Nat) :
    ∀ (l : List α), l.Nodup → ∀ i, i ∈ l →
      (l.map (fun k => if k = i then a else f k)).prod =
        a * ((l.erase i).map f).prod := by
  intro l
  induction l with
  | nil => intro _ i hi; cases hi
  | cons x L ih =>
      intro hnd i hi
      have hnd' := List.nodup_cons.mp hnd
      by_cases hxi : x = i
      · subst hxi
        rw [List.erase_cons_head]
        simp only [List.map_cons, List.prod_cons, if_pos rfl]
        congr 1
        congr 1
        apply List.map_congr_left
        intro k hk
        have : k ≠ x := fun h => hnd'.1 (h ▸ hk)
        simp [this]
      · have hiL : i ∈ L := by
          rcases List.mem_cons.mp hi with h | h
          · exact absurd h.symm hxi
          · exact h
        rw [List.erase_cons_tail (by simpa using hxi)]
        simp only [List.map_cons, List.prod_cons, if_neg hxi]
        rw [ih hnd'.2 i hiL]
        ac_rfl

/-- Replacing two factors of a product over a duplicate-free list.

Consumer: `shortCyclicStep`. -/
theorem shortReplacePairProd {α : Type} [DecidableEq α] (f : α → Nat)
    (x y : Nat) (l : List α) (hnd : l.Nodup) (a b : α) (ha : a ∈ l)
    (hb : b ∈ l) (hab : a ≠ b) :
    (l.map (fun k => if k = a then x else if k = b then y else f k)).prod =
      x * y * (((l.erase a).erase b).map f).prod := by
  have h1 := shortReplaceProd (fun k => if k = b then y else f k) x l hnd a ha
  have hnd2 : (l.erase a).Nodup := hnd.erase a
  have hb2 : b ∈ l.erase a := (List.mem_erase_of_ne (Ne.symm hab)).mpr hb
  have h2 := shortReplaceProd f y (l.erase a) hnd2 b hb2
  rw [h1, h2, Nat.mul_assoc]

/-- A constant factor pulls out of a list sum.

Consumer: `shortMultiBernoulli`. -/
theorem shortSumMulLeft {α : Type} (c : Nat) (g : α → Nat) :
    ∀ l : List α, (l.map (fun i => c * g i)).sum = c * (l.map g).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- The multilinear Bernoulli inequality over a duplicate-free list: if
`V k + d k = N h k` then
`N^(|l|+1) prod h ≤ N prod V + N^|l| sum_i d_i prod_{k ≠ i} h_k`.

Consumer: `shortCyclicStep`. -/
theorem shortMultiBernoulli {α : Type} [DecidableEq α] (N : Nat)
    (h d V : α → Nat) :
    ∀ l : List α, l.Nodup → (∀ k, k ∈ l → V k + d k = N * h k) →
      N ^ (l.length + 1) * (l.map h).prod ≤
        N * (l.map V).prod + N ^ l.length *
          (l.map (fun i => d i * ((l.erase i).map h).prod)).sum := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x L ih =>
      intro hnd hk
      have hnd' := List.nodup_cons.mp hnd
      have hL := ih hnd'.2 (fun k hk' => hk k (List.mem_cons_of_mem x hk'))
      have hx := hk x List.mem_cons_self
      have hsum : ((x :: L).map
          (fun i => d i * (((x :: L).erase i).map h).prod)).sum =
          d x * (L.map h).prod + h x *
            (L.map (fun i => d i * ((L.erase i).map h).prod)).sum := by
        rw [List.map_cons, List.sum_cons, List.erase_cons_head]
        congr 1
        rw [← shortSumMulLeft]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hxi : x ≠ i := fun h' => hnd'.1 (h' ▸ hi)
        rw [List.erase_cons_tail (by simpa using hxi)]
        simp only [List.map_cons, List.prod_cons]
        ac_rfl
      rw [hsum]
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      have hVle : V x ≤ N * h x := by omega
      have g1 := Nat.mul_le_mul_left (V x) hL
      have g2 := Nat.mul_le_mul_right
        (N ^ L.length * (L.map (fun i => d i * ((L.erase i).map h).prod)).sum)
        hVle
      have hpow : N ^ (L.length + 1) = N * N ^ L.length := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hpow2 : N ^ (L.length + 1 + 1) = N * (N * N ^ L.length) := by
        rw [Nat.pow_succ, hpow, Nat.mul_comm]
      rw [hpow2, hpow]
      rw [hpow] at g1 hL
      generalize (L.map h).prod = p at *
      generalize (L.map V).prod = q at *
      generalize (L.map (fun i => d i * ((L.erase i).map h).prod)).sum = sS
        at *
      generalize N ^ L.length = a at *
      have e1 : N * (N * a) * (h x * p) = (V x + d x) * (N * a * p) := by
        have : N * h x = V x + d x := hx.symm
        calc
          N * (N * a) * (h x * p) = (N * h x) * (N * a * p) := by ac_rfl
          _ = _ := by rw [this]
      rw [e1]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at g1 g2 ⊢
      omega


/-- List sums are monotone pointwise.

Consumer: `shortCyclicStep`. -/
theorem shortSumMono {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ x, x ∈ l → f x ≤ g x) →
      (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x L ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- List sums are additive.

Consumer: `shortCyclicStep`. -/
theorem shortSumAdd {α : Type} (f g : α → Nat) :
    ∀ l : List α,
      (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

/-- The sum of a constant over a list.

Consumer: `shortCyclicStep`. -/
theorem shortSumConst {α : Type} (c : Nat) :
    ∀ l : List α, (l.map (fun _ => c)).sum = l.length * c := by
  intro l
  induction l with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons,
        Nat.succ_mul]
      omega

/-- The clockwise successor is injective.

Consumer: `shortRingShift`. -/
theorem shortRightInjective {n : Nat} (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

/-- The clockwise successor is surjective.

Consumer: `shortRingShift`. -/
theorem shortRightSurjective {n : Nat} (ring : DirectedRing n)
    (x : Fin n) : ∃ y : Fin n, ring.rightNeighbor y = x := by
  have hn := ring.hn
  refine ⟨⟨(x.val + n - 1) % n, Nat.mod_lt _ hn⟩, ?_⟩
  apply Fin.ext
  show ((x.val + n - 1) % n + 1) % n = x.val
  have hx := x.isLt
  by_cases h0 : x.val = 0
  · have : (x.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self]
    omega
  · have : (x.val + n - 1) % n = x.val - 1 := by
      have : x.val + n - 1 = (x.val - 1) + n := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    have : x.val - 1 + 1 = x.val := by omega
    rw [this]
    exact Nat.mod_eq_of_lt hx

/-- Injective images of duplicate-free lists are duplicate-free.

Consumer: `shortRingShift`. -/
theorem shortNodupMap {α β : Type} (f : α → β) (hf : Function.Injective f) :
    ∀ l : List α, l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x L ih =>
      intro h
      have h' := List.nodup_cons.mp h
      simp only [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, ih h'.2⟩
      intro hm
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
      exact h'.1 ((hf hxy) ▸ hy)

/-- Reindexing a sum along the clockwise successor.

Consumer: `shortCyclicStep`. -/
theorem shortRingShift {n : Nat} (ring : DirectedRing n) (G : Fin n → Nat) :
    ((List.finRange n).map (fun e => G (ring.rightNeighbor e))).sum =
      ((List.finRange n).map G).sum := by
  have hperm : ((List.finRange n).map ring.rightNeighbor).Perm
      (List.finRange n) := by
    rw [List.perm_ext_iff_of_nodup
      (shortNodupMap _ (shortRightInjective ring) _ (List.nodup_finRange n))
      (List.nodup_finRange n)]
    intro a
    constructor
    · intro _
      exact List.mem_finRange a
    · intro _
      obtain ⟨y, hy⟩ := shortRightSurjective ring a
      exact List.mem_map.mpr ⟨y, List.mem_finRange y, hy⟩
  have h2 := (hperm.map G).sum_nat
  rw [List.map_map] at h2
  exact h2


/-- The product over the ring.

Consumer: `shortCyclicStep`. -/
def shortProdFin {n : Nat} (f : Fin n → Nat) : Nat :=
  ((List.finRange n).map f).prod

/-- The sum over the ring.

Consumer: `shortCyclicStep`. -/
def shortSumFin {n : Nat} (f : Fin n → Nat) : Nat :=
  ((List.finRange n).map f).sum

/-- The product with one factor removed.

Consumer: `shortCyclicStep`. -/
def shortProdOff {n : Nat} (h : Fin n → Nat) (i : Fin n) : Nat :=
  (((List.finRange n).erase i).map h).prod

/-- The one-step move of the scheduler at the edge `e`: the initiator takes
the lower factor `hp e`, the responder the upper factor `h0`, the other sites
keep `h`.

Consumer: `shortCyclicStep`. -/
def shortMoveProd {n : Nat} (ring : DirectedRing n) (h hp : Fin n → Nat)
    (h0 : Nat) (e : Fin n) : Nat :=
  shortProdFin (fun k =>
    if k = e then hp e else if k = ring.rightNeighbor e then h0 else h k)

/-- **The cyclic one-step comparison.**  For monotone factors
`hp ≤ h ≤ h0` that are nonincreasing in time (`hp + h0 ≤ 2 h`),
`n^(n-1) * sum_e prod_i g_e(i) ≤ prod_i ((n-2) h_i + hp_i + h0)`.

Consumer: `shortProductInduction`. -/
theorem shortCyclicStep {n : Nat} (ring : DirectedRing n) (hn : 3 ≤ n)
    (h hp : Fin n → Nat) (h0 : Nat)
    (hmono : ∀ i, hp i ≤ h i ∧ h i ≤ h0)
    (htime : ∀ i, hp i + h0 ≤ 2 * h i) :
    n ^ (n - 1) * shortSumFin (shortMoveProd ring h hp h0) ≤
      shortProdFin (fun i => (n - 2) * h i + hp i + h0) := by
  have hnd : (List.finRange n).Nodup := List.nodup_finRange n
  obtain ⟨F, hF⟩ : ∃ F, F = shortProdFin h := ⟨_, rfl⟩
  have hFi : ∀ i, F = h i * shortProdOff h i := by
    intro i
    rw [hF]
    exact shortEraseProd h (List.finRange n) hnd i (List.mem_finRange i)
  have hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e := by
    intro e
    exact EWord.rightNeighborDifferent ring (by omega) e
  have hRR1 : ∀ e : Fin n, shortProdOff h e =
      h (ring.rightNeighbor e) *
        ((((List.finRange n).erase e).erase (ring.rightNeighbor e)).map h).prod := by
    intro e
    exact shortEraseProd h ((List.finRange n).erase e) (hnd.erase e) _
      ((List.mem_erase_of_ne (hne e)).mpr (List.mem_finRange _))
  have hRR2 : ∀ e : Fin n, shortProdOff h (ring.rightNeighbor e) =
      h e * ((((List.finRange n).erase e).erase
        (ring.rightNeighbor e)).map h).prod := by
    intro e
    unfold shortProdOff
    have := shortEraseProd h ((List.finRange n).erase (ring.rightNeighbor e))
      (hnd.erase _) e
      ((List.mem_erase_of_ne (Ne.symm (hne e))).mpr (List.mem_finRange _))
    rw [this, List.erase_comm]
  have hMove : ∀ e : Fin n, shortMoveProd ring h hp h0 e =
      hp e * h0 * ((((List.finRange n).erase e).erase
        (ring.rightNeighbor e)).map h).prod := by
    intro e
    exact shortReplacePairProd h (hp e) h0 (List.finRange n) hnd e
      (ring.rightNeighbor e)
      (List.mem_finRange _) (List.mem_finRange _) (Ne.symm (hne e))
  have hpoint : ∀ e : Fin n, shortMoveProd ring h hp h0 e + F ≤
      hp e * shortProdOff h e + h0 * shortProdOff h (ring.rightNeighbor e) := by
    intro e
    obtain ⟨R, hR⟩ : ∃ R, R = ((((List.finRange n).erase e).erase
        (ring.rightNeighbor e)).map h).prod := ⟨_, rfl⟩
    rw [hMove e, hFi e, hRR1 e, hRR2 e, ← hR]
    have m1 := hmono e
    have m2 := hmono (ring.rightNeighbor e)
    obtain ⟨u, hu⟩ : ∃ u, h e = hp e + u := ⟨h e - hp e, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, h0 = h (ring.rightNeighbor e) + v :=
      ⟨h0 - h (ring.rightNeighbor e), by omega⟩
    have key : hp e * h0 + h e * h (ring.rightNeighbor e) ≤
        hp e * h (ring.rightNeighbor e) + h0 * h e := by
      rw [hu, hv]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
      omega
    have := Nat.mul_le_mul_right R key
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] at this ⊢
    omega
  -- sums
  have hL0 : (List.finRange n).length = n := List.length_finRange
  have hS1 : shortSumFin (shortMoveProd ring h hp h0) + n * F ≤
      shortSumFin (fun i => hp i * shortProdOff h i) +
      shortSumFin (fun i => h0 * shortProdOff h i) := by
    have h1 : ((List.finRange n).map
        (fun e => shortMoveProd ring h hp h0 e + F)).sum ≤
        ((List.finRange n).map (fun e =>
          hp e * shortProdOff h e +
            h0 * shortProdOff h (ring.rightNeighbor e))).sum :=
      shortSumMono _ _ _ (fun e _ => hpoint e)
    rw [shortSumAdd, shortSumAdd, shortRingShift ring
      (fun i => h0 * shortProdOff h i), shortSumConst, hL0] at h1
    unfold shortSumFin
    exact h1
  obtain ⟨d, hd⟩ : ∃ d : Fin n → Nat, d = fun i => 2 * h i - hp i - h0 :=
    ⟨_, rfl⟩
  have hD : ∀ i, hp i * shortProdOff h i + h0 * shortProdOff h i +
      d i * shortProdOff h i = 2 * F := by
    intro i
    have := htime i
    rw [hd]
    simp only []
    have e : hp i + h0 + (2 * h i - hp i - h0) = 2 * h i := by omega
    calc
      hp i * shortProdOff h i + h0 * shortProdOff h i +
          (2 * h i - hp i - h0) * shortProdOff h i =
          (hp i + h0 + (2 * h i - hp i - h0)) * shortProdOff h i := by
        simp only [Nat.add_mul]
      _ = 2 * h i * shortProdOff h i := by rw [e]
      _ = 2 * F := by rw [hFi i, Nat.mul_assoc]
  have hS2 : shortSumFin (fun i => hp i * shortProdOff h i) +
      shortSumFin (fun i => h0 * shortProdOff h i) +
      shortSumFin (fun i => d i * shortProdOff h i) = n * (2 * F) := by
    unfold shortSumFin
    rw [← shortSumAdd, ← shortSumAdd]
    have : ((List.finRange n).map (fun i =>
        hp i * shortProdOff h i + h0 * shortProdOff h i +
          d i * shortProdOff h i)).sum =
        ((List.finRange n).map (fun _ => 2 * F)).sum := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact hD i
    rw [this, shortSumConst, hL0]
  have hV : ∀ k, k ∈ List.finRange n →
      ((n - 2) * h k + hp k + h0) + d k = n * h k := by
    intro k _
    have := htime k
    rw [hd]
    simp only []
    have hn2 : n = (n - 2) + 2 := by omega
    have e : n * h k = (n - 2) * h k + 2 * h k := by
      calc
        n * h k = ((n - 2) + 2) * h k := by rw [← hn2]
        _ = _ := Nat.add_mul _ _ _
    rw [e]
    omega
  have hB := shortMultiBernoulli n h d (fun i => (n - 2) * h i + hp i + h0)
    (List.finRange n) hnd hV
  rw [hL0] at hB
  have hProdh : (((List.finRange n).map h).prod) = F := hF.symm
  rw [hProdh] at hB
  have hSdef : shortSumFin (fun i => d i * shortProdOff h i) =
      ((List.finRange n).map
        (fun i => d i * (((List.finRange n).erase i).map h).prod)).sum := rfl
  rw [← hSdef] at hB
  have e2 : n * (2 * F) = 2 * (n * F) := Nat.mul_left_comm _ _ _
  have hc1 : shortSumFin (shortMoveProd ring h hp h0) +
      shortSumFin (fun i => d i * shortProdOff h i) ≤ n * F := by
    omega
  have h3 := Nat.mul_le_mul_left (n ^ n) hc1
  have h4 : n ^ n * (n * F) = n ^ (n + 1) * F := by
    rw [Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h5 : n ^ n * shortSumFin (shortMoveProd ring h hp h0) ≤
      n * shortProdFin (fun i => (n - 2) * h i + hp i + h0) := by
    have hPf : shortProdFin (fun i => (n - 2) * h i + hp i + h0) =
        ((List.finRange n).map (fun i => (n - 2) * h i + hp i + h0)).prod := rfl
    rw [hPf]
    rw [Nat.mul_add] at h3
    omega
  have h6 : n * (n ^ (n - 1) * shortSumFin (shortMoveProd ring h hp h0)) ≤
      n * shortProdFin (fun i => (n - 2) * h i + hp i + h0) := by
    have hpw : n ^ n = n * n ^ (n - 1) := by
      have hn1 : n = (n - 1) + 1 := by omega
      calc
        n ^ n = n ^ ((n - 1) + 1) := by rw [← hn1]
        _ = n ^ (n - 1) * n := Nat.pow_succ _ _
        _ = n * n ^ (n - 1) := Nat.mul_comm _ _
    rw [← Nat.mul_assoc, ← hpw]
    exact h5
  exact Nat.le_of_mul_le_mul_left h6 (by omega)

end L3

#print axioms L3.shortCyclicStep
