import Leader.Wu.ZeroDivisible.TrafficLand
import Leader.Wu.ZeroDivisible.ResetDrain

/-! Physical-ring and finite-sum interfaces for the shared traffic rank.
Only the actual two-cell update is used. No service-row contract is assumed
by the geometry or selection results; the scalar update accepts a numerical
pair inequality for the literal R5 transition. -/
namespace PPLLAstraR5GlobalTraffic
open PPLL PPLLAstraR5TrafficMove PPLLAstraR5ResetDrain
set_option autoImplicit false

/-- Three times token weight plus the zero-position reader indicator. -/
def cellRank {ψ : Nat} (u : AgentState ψ) : Nat :=
  3 * PPLLAstraR5TrafficLand.P u + PPLLAstraR5TrafficLand.Z u

/-- The finite sum of the existing holder weights on the physical ring. -/
def globalRank {n ψ : Nat} (C : Fin n → AgentState ψ) : Nat :=
  (List.ofFn fun i => cellRank (C i)).sum

private theorem sum_one {n : Nat} (f g : Fin n → Nat) (i : Fin n)
    (hoff : ∀ k, k ≠ i → g k = f k) :
    (List.ofFn g).sum + f i = (List.ofFn f).sum + g i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      have hs : (fun k : Fin n => g k.succ) = fun k => f k.succ := by
        funext k
        exact hoff k.succ (by intro h; have := congrArg Fin.val h; simp at this)
      simp only [List.ofFn_succ, List.sum_cons]
      rw [hs]
      omega
    | succ i =>
      have hz := hoff 0 (by intro h; have := congrArg Fin.val h; simp at this)
      have hs := ih (fun k => f k.succ) (fun k => g k.succ) i
        (fun k h => hoff k.succ (by simpa using h))
      simp only [List.ofFn_succ, List.sum_cons]
      omega

/-- Cancellation-form exchange for exactly two changed physical cells. -/
theorem sum_two {n : Nat} (f g : Fin n → Nat) (i j : Fin n) (hne : i ≠ j)
    (hoff : ∀ k, k ≠ i → k ≠ j → g k = f k) :
    (List.ofFn g).sum + (f i + f j) =
      (List.ofFn f).sum + (g i + g j) := by
  let h : Fin n → Nat := fun k => if k = i then g k else f k
  have h1 := sum_one f h i (fun k hk => by simp [h, hk])
  have h2 := sum_one h g j (fun k hk => by
    by_cases hi : k = i
    · simp [h, hi]
    · simp [h, hi, hoff k hi hk])
  have hi : h i = g i := by simp [h]
  have hj : h j = f j := by simp [h, Ne.symm hne]
  rw [hi] at h1
  rw [hj] at h2
  omega

/-- Distinct interacting cells when the ring has at least two vertices. -/
theorem rightNeighbor_ne {n : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have he := e.isLt
  have hv := congrArg Fin.val h
  change (e.val+1)%n=e.val at hv
  by_cases hs : e.val+1<n
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have ht : e.val+1=n := by omega
    rw [ht, Nat.mod_self] at hv
    omega

/-- The incoming physical edge ends at the chosen holder, including vertex zero. -/
theorem right_left {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  change (((i.val+n-1)%n)+1)%n=i.val
  by_cases hz : i.val=0
  · have hn := ring.hn
    have hl : n-1<n := by omega
    simp only [hz, Nat.zero_add, Nat.mod_eq_of_lt hl]
    rw [show n-1+1=n by omega, Nat.mod_self]
  · have hi := i.isLt
    have he : i.val+n-1=(i.val-1)+n := by omega
    have hm : (i.val-1+n)%n=i.val-1 := by
      simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt (show i.val-1<n by omega)]
    rw [he, hm]
    rw [show i.val-1+1=i.val by omega, Nat.mod_eq_of_lt hi]

/-- Correct physical successor roles on a ring containing whole psi-groups. -/
theorem physical_adj {q ψ : Nat} (_hp : 0 < ψ) (ring : DirectedRing (q*ψ))
    (C : Fin (q*ψ) → AgentState ψ)
    (labels : ∀ i, (C i).label.val = i.val % ψ) (e : Fin (q*ψ)) :
    Adj (C e) (C (ring.rightNeighbor e)) := by
  unfold Adj
  rw [labels, labels, mod_succ_eq]
  change ((e.val+1)%(q*ψ))%ψ=(e.val+1)%ψ
  by_cases he : e.val+1<q*ψ
  · rw [Nat.mod_eq_of_lt he]
  · have ht : e.val+1=q*ψ := by have := e.isLt; omega
    rw [ht, Nat.mod_self]
    simp

/-- Every present allowed token supplies an indicated physical edge, even
when its MOVE guard is frozen or its reader position is zero. -/
theorem exists_selected {n ψ : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (ok : ∀ i, OkSlot (C i).path2)
    (present : ∃ i, (C i).path2 ≠ none) :
    ∃ e, Selected (C e) (C (ring.rightNeighbor e)) := by
  obtain ⟨i, hi⟩ := present
  cases ht : (C i).path2 with
  | none => exact False.elim (hi ht)
  | some t =>
    have ha := ok i t ht
    have hf : t.action=1 ∨ t.action=2 ∨ t.action=3 ∨ t.action=4 := by
      unfold Ok at ha
      omega
    rcases hf with h | h | h | h
    · exact ⟨i, Or.inl ⟨t, ht, Or.inl h⟩⟩
    · refine ⟨ring.leftNeighbor i, Or.inr ?_⟩
      rw [right_left]
      exact ⟨t, ht, Or.inl h⟩
    · refine ⟨ring.leftNeighbor i, Or.inr ?_⟩
      rw [right_left]
      exact ⟨t, ht, Or.inr h⟩
    · exact ⟨i, Or.inl ⟨t, ht, Or.inr h⟩⟩

private theorem Z_le_one {ψ : Nat} (u : AgentState ψ) :
    PPLLAstraR5TrafficLand.Z u ≤ 1 := by
  unfold PPLLAstraR5TrafficLand.Z
  split
  · omega
  · split <;> omega

private theorem pair_scalar {ψ : Nat} (l r : AgentState ψ) :
    cellRank l + cellRank r = 3*P l r+Z l r := by
  have h := PPLLAstraR5TrafficLand.pair_coordinates l r
  simp only [P, Z, h, cellRank, Nat.mul_add]
  omega

/-- An actual R5 pair lexicographic decrease strictly decreases the whole
ring sum. The two-cell indicator bound, rather than the ring size, sets 3. -/
theorem globalRank_step_lt {n ψ : Nat} (hn : 1 < n) (hp : 0 < ψ)
    (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (drop : let z := PPLLAstraR5Repair.pipeline hp κ c (C e) (C (ring.rightNeighbor e))
      P z.1 z.2 < P (C e) (C (ring.rightNeighbor e)) ∨
        (P z.1 z.2 = P (C e) (C (ring.rightNeighbor e)) ∧
          Z z.1 z.2 < Z (C e) (C (ring.rightNeighbor e)))) :
    globalRank ((PPLLAstraR5ResetDrain.protocol hp κ c).step ring C e) < globalRank C := by
  let j := ring.rightNeighbor e
  let z := PPLLAstraR5Repair.pipeline hp κ c (C e) (C j)
  let D := (PPLLAstraR5ResetDrain.protocol hp κ c).step ring C e
  have hne : j ≠ e := rightNeighbor_ne ring hn e
  have he : D e=z.1 := by simp [D, PopulationProtocol.step, PPLLAstraR5ResetDrain.protocol, z, j]
  have hj : D j=z.2 := by simp [D, PopulationProtocol.step, PPLLAstraR5ResetDrain.protocol, z, j, hne]
  have hs := sum_two (fun k => cellRank (C k)) (fun k => cellRank (D k)) e j
    (Ne.symm hne) (fun k hi hj => by
      simp [D, PopulationProtocol.step, PPLLAstraR5ResetDrain.protocol, hi,
        show k≠ring.rightNeighbor e from hj])
  have hz : Z z.1 z.2 ≤ 2 := by
    have hb := PPLLAstraR5TrafficLand.pair_coordinates z.1 z.2
    have h1 := Z_le_one z.1
    have h2 := Z_le_one z.2
    simp only [Z, hb]
    omega
  have hlt := PPLLAstraR5TrafficArithmetic.scalar_of_lex 2
    (P (C e) (C j)) (Z (C e) (C j)) (P z.1 z.2) (Z z.1 z.2) drop hz
  rw [he, hj, pair_scalar, pair_scalar] at hs
  change (List.ofFn fun k => cellRank (D k)).sum <
    (List.ofFn fun k => cellRank (C k)).sum
  omega

#print axioms sum_two
#print axioms rightNeighbor_ne
#print axioms right_left
#print axioms physical_adj
#print axioms exists_selected
#print axioms globalRank_step_lt
end PPLLAstraR5GlobalTraffic
