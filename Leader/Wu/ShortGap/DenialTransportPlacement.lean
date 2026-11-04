import Leader.Wu.ShortGap.DenialTransport

/-!
# Denial transport on placement-derived gaps of variable length

`Leader/Wu/ShortGap/DenialTransport.lean` ran the stop-and-wait denial token walk
on `m` gaps of one common length `h` whose edge sets were supplied abstractly.
This file removes both restrictions.

**Variable-length layouts.**  `VarGapLayout n m` assigns every gap `g` its own
length `len g ≥ 1` and its own clockwise edge list `edgeAt g : Fin (len g) → Fin
n`, injective across gaps and positions.  The token walk, its potential
`n * (total remaining hops)`, the Bellman certificate, the absence of bad
terminals, and the `CandidateRearmSpec` composition are all re-established in
this dependent setting.  The rearm start has potential `n * (2 * Σ_g len g)`,
so repeated candidate rounds cost at most `2*(n*m) + 2*n*Σ_g len g`; when the
gaps tile the ring (`Σ_g len g = n`) this is `2*n*(m+n)`, and uniform lengths
`h` give back `2*(n*m)*(1+h)`.

**Placement-derived gaps.**  Given `P : Placement n m` and a ring `ring` of
roots, gap `g` runs clockwise on the physical ring from vertex `P.root g` to
vertex `P.root (ring.rightNeighbor g)`.  Its length is the clockwise distance
`cwDist (P.root g) (P.root (ring.rightNeighbor g)) = (b + n - a) % n`, and its
`k`-th edge is the physical edge with tail `(P.root g + k) % n`.  Under the
ordering hypothesis `RootsOrdered ring P` (no root lies strictly inside any
gap, i.e. the cyclic order of the placed roots is the ring order), the edges of
one gap are pairwise distinct and edges of different gaps are disjoint
(`gapEdge_injective`), which yields the layout `placementLayout`.  Gap lengths
are positive as soon as `1 < m`, by injectivity of the placement.

**Abstraction boundary.**  As in the companion file: only the uniform
(all-denial) outcome is modelled; the token is a single message carrier with
no forgery, staleness, or interference from unrelated rows; the shared endpoint
root between adjacent gaps enters only through disjoint edge sets, not through
a shared-root two-receipt join (that join lives in
`Leader/Wu/ShortGap/TwoDenialRearm.lean`, not imported).  `RootsOrdered` is taken
as a hypothesis on the placement, not derived; the tiling identity
`Σ_g gapLen g = n` is likewise taken as a hypothesis where the `2*n*(m+n)`
form is stated.  Nothing here claims complete leader stabilization or a final
complexity bound.
-/

namespace ShortGapDenialTransportPlacement

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport

set_option autoImplicit false

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-! ## Variable-length layouts -/

/-- `m` gaps of individual lengths on `n` scheduler edges.  Gap `g` owns the
edges `edgeAt g 0, …, edgeAt g (len g - 1)` in clockwise order; the assignment
is injective in the pair (gap, position), so one physical edge advances at
most one carrier.

That injectivity means a `VarGapLayout n m` presupposes `Σ_g len g ≤ n`, and
for `Σ_g len g > n` no layout exists, so every statement below quantified over
one is vacuous.  The placement-derived layout below meets this with equality
under `RootsOrdered` (`gapLen_sum_eq` of
`Leader/Wu/ShortGap/GapTiling.lean`). -/
structure VarGapLayout (n m : Nat) where
  len : Fin m → Nat
  len_pos : ∀ g, 0 < len g
  edgeAt : (g : Fin m) → Fin (len g) → Fin n
  edgeAt_injective : ∀ g a g' a',
    edgeAt g a = edgeAt g' a' → g = g' ∧ a.val = a'.val

/-- Total physical length of all gaps. -/
def VarGapLayout.totalLength {n m : Nat} (L : VarGapLayout n m) : Nat :=
  (List.ofFn (fun g => L.len g)).sum

/-- A uniform-length layout is a variable-length layout. -/
def VarGapLayout.ofUniform {n h m : Nat} (L : GapLayout n h m) :
    VarGapLayout n m where
  len := fun _ => h
  len_pos := fun _ => L.hpos
  edgeAt := L.edgeAt
  edgeAt_injective := fun g a g' a' heq =>
    ⟨(L.edgeAt_injective g a g' a' heq).1,
      congrArg Fin.val (L.edgeAt_injective g a g' a' heq).2⟩

theorem VarGapLayout.totalLength_ofUniform {n h m : Nat}
    (L : GapLayout n h m) : (VarGapLayout.ofUniform L).totalLength = m * h := by
  simp [VarGapLayout.totalLength, VarGapLayout.ofUniform, ofFn_sum_const]

/-- Joint carrier state with at least one gap still in transit. -/
structure VarMultiGapState {n m : Nat} (L : VarGapLayout n m) where
  gap : (g : Fin m) → GapDenialState (L.len g)
  hasActive : ∃ g, 0 < (gap g).hops

/-- Total remaining carrier hops over all gaps. -/
def varTotalHops {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) : Nat :=
  (List.ofFn (fun g => (gap g).hops)).sum

/-- One scheduler edge acting on every gap through its own edge set. -/
def varLocalStep {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (e : Fin n) :
    (g : Fin m) → GapDenialState (L.len g) :=
  fun g => GapDenialState.localStep (L.edgeAt g) (gap g) e

theorem varTotalHops_localStep_le {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (e : Fin n) :
    varTotalHops L (varLocalStep L gap e) ≤ varTotalHops L gap :=
  ofFn_sum_le _ _
    (fun g => GapDenialState.hops_localStep_le (L.edgeAt g) (gap g) e)

/-- The advancing edge of any in-transit gap strictly lowers the total. -/
theorem varTotalHops_localStep_lt {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (g : Fin m)
    (a : Fin (L.len g)) (ha : (gap g).advanceEdge = some a) :
    varTotalHops L (varLocalStep L gap (L.edgeAt g a)) < varTotalHops L gap := by
  apply ofFn_sum_lt_of_single_lt _ _ g
  · intro g'
    exact GapDenialState.hops_localStep_le (L.edgeAt g') (gap g') _
  · have := GapDenialState.hops_localStep_advance (L.edgeAt g) (gap g) a ha
    show (varLocalStep L gap (L.edgeAt g a) g).hops < (gap g).hops
    simp only [varLocalStep]
    omega

/-- A gap's advancing edge leaves every other gap unchanged. -/
theorem varLocalStep_other {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (g g' : Fin m)
    (hne : g' ≠ g) (a : Fin (L.len g)) :
    varLocalStep L gap (L.edgeAt g a) g' = gap g' := by
  apply GapDenialState.localStep_eq_of_ne
  intro a' _ heq
  exact hne (L.edgeAt_injective g' a' g a heq).1

/-- The variable-length token-walk rearm service. -/
noncomputable def varMultiGapStep {n m : Nat} (L : VarGapLayout n m) :
    VarMultiGapState L → Fin n → StopNode (VarMultiGapState L) :=
  fun state edge =>
    let next := varLocalStep L state.gap edge
    if hnext : ∃ g, 0 < (next g).hops then
      .active ⟨next, hnext⟩
    else .success

def varMultiGapPotential {n m : Nat} (L : VarGapLayout n m) :
    StopNode (VarMultiGapState L) → Nat
  | .active state => n * varTotalHops L state.gap
  | .success => 0
  | .failure => 0

private theorem varMultiGapPotential_step_le
    {n m : Nat} (L : VarGapLayout n m)
    (state : VarMultiGapState L) (edge : Fin n) :
    varMultiGapPotential L (varMultiGapStep L state edge) ≤
      n * varTotalHops L (varLocalStep L state.gap edge) := by
  classical
  simp only [varMultiGapStep]
  split <;> simp [varMultiGapPotential]

/-- The exact child-sum inequality for remaining carrier hops. -/
theorem varTotalHops_childSum {n m : Nat} (L : VarGapLayout n m)
    (state : VarMultiGapState L) :
    1 + (List.ofFn (fun edge : Fin n =>
      varTotalHops L (varLocalStep L state.gap edge))).sum ≤
        n * varTotalHops L state.gap := by
  obtain ⟨g, hg⟩ := state.hasActive
  obtain ⟨a, ha⟩ := GapDenialState.advanceEdge_of_hops_pos _ hg
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n => varTotalHops L (varLocalStep L state.gap edge))
    (fun _ : Fin n => varTotalHops L state.gap) (L.edgeAt g a)
    (fun edge => varTotalHops_localStep_le L state.gap edge)
    (varTotalHops_localStep_lt L state.gap g a ha)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- Expected work is at most `n` times the initial total number of hops. -/
theorem varMultiGap_natBellmanSuperSolution
    {n m : Nat} (L : VarGapLayout n m) :
    NatBellmanSuperSolution (varMultiGapStep L) 1 (varMultiGapPotential L) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := varTotalHops_childSum L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        varMultiGapPotential L (varMultiGapStep L state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.gap edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          varMultiGapPotential L (varMultiGapStep L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          n * varTotalHops L (varLocalStep L state.gap edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact varMultiGapPotential_step_le L state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.gap edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        varMultiGapPotential L (varMultiGapStep L state edge))).sum ≤
      n + n * (List.ofFn (fun edge : Fin n =>
        varTotalHops L (varLocalStep L state.gap edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
        varTotalHops L (varLocalStep L state.gap edge))).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * varTotalHops L state.gap) := hscaled
    _ = n * varMultiGapPotential L (.active state) := rfl

theorem varMultiGapStep_ne_failure {n m : Nat} (L : VarGapLayout n m) :
    ∀ state edge, varMultiGapStep L state edge ≠ .failure := by
  classical
  intro state edge
  simp only [varMultiGapStep]
  split <;> simp

/-- Every gap starts with its left root's declaration at position `0`. -/
def varAllDeclareStart {n m : Nat} (L : VarGapLayout n m) (hm : 0 < m) :
    VarMultiGapState L :=
  ⟨fun g => .declareRight 0 (L.len_pos g),
    ⟨⟨0, hm⟩, by
      have := L.len_pos ⟨0, hm⟩
      simp only [GapDenialState.hops]
      omega⟩⟩

@[simp] theorem varTotalHops_allDeclare {n m : Nat} (L : VarGapLayout n m) :
    varTotalHops L (fun g => GapDenialState.declareRight 0 (L.len_pos g)) =
      2 * L.totalLength := by
  simp only [varTotalHops, GapDenialState.hops, Nat.sub_zero,
    VarGapLayout.totalLength, ← Nat.two_mul]
  exact ofFn_sum_mul_left 2 _

@[simp] theorem varMultiGapPotential_allDeclare
    {n m : Nat} (L : VarGapLayout n m) (hm : 0 < m) :
    varMultiGapPotential L (.active (varAllDeclareStart L hm)) =
      n * (2 * L.totalLength) := by
  simp [varMultiGapPotential, varAllDeclareStart]

/-- Token-walk implementation of the candidate rearm interface for `m` gaps
of individual lengths on disjoint edge sets. -/
noncomputable def varGapDenialRearmSpec
    {n m : Nat} (L : VarGapLayout n m) (hm : 0 < m) :
    CandidateRearmSpec n where
  State := VarMultiGapState L
  step := varMultiGapStep L
  start := varAllDeclareStart L hm
  potential := varMultiGapPotential L
  bellman := varMultiGap_natBellmanSuperSolution L
  noFailure := varMultiGapStep_ne_failure L

/-- Complete candidate process with variable-length token-walk rearm. -/
noncomputable def varGapCandidateRestartStep
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (L : VarGapLayout n m) (hm : 0 < m) :=
  (varGapDenialRearmSpec L hm).restartStep ring P hm

private theorem budget_eq (n m t : Nat) :
    2 * (n * m) + 2 * n * t = 2 * (n * m) + n * (2 * t) := by
  have hswap : n * (2 * t) = 2 * n * t := by ac_rfl
  rw [hswap]

/-- Repeated candidate rounds with variable-length token-walk rearm have
expected work at most `2*n*m + 2*n*Σ_g len g`. -/
theorem varGapCandidateRestart_truncatedCost_le
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : VarGapLayout n m) (T : Nat) :
    truncatedActiveCostNumerator
        (varGapCandidateRestartStep ring P L (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) + 2 * n * L.totalLength) := by
  have hcost :=
    (varGapDenialRearmSpec L (by omega)).allRace_truncatedCost_le
      ring hm P hn T
  simp only [varGapCandidateRestartStep, varGapDenialRearmSpec,
    varMultiGapPotential_allDeclare] at hcost ⊢
  rw [budget_eq]
  exact hcost

/-- Exact reciprocal success tail for the variable-length process. -/
theorem varGapCandidateRestart_success_one_minus_inv_factor
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : VarGapLayout n m) :
    (factor - 1) * n ^ (factor * (2 * (n * m) + 2 * n * L.totalLength)) ≤
      factor * successCount
        (varGapCandidateRestartStep ring P L (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) + 2 * n * L.totalLength)) := by
  have hsuccess :=
    CandidateRearmSpec.allRace_success_one_minus_inv_factor
      (varGapDenialRearmSpec L (by omega)) ring hm P hn
      (factor := factor)
  simp only [varGapCandidateRestartStep, varGapDenialRearmSpec,
    varMultiGapPotential_allDeclare] at hsuccess ⊢
  rw [budget_eq]
  exact hsuccess

/-- When the gaps tile the physical ring, the bound reads `2*n*(m+n)`. -/
theorem varGapCandidateRestart_truncatedCost_le_of_tiling
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : VarGapLayout n m)
    (htotal : L.totalLength = n) (T : Nat) :
    truncatedActiveCostNumerator
        (varGapCandidateRestartStep ring P L (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * n * (m + n)) := by
  have hcost := varGapCandidateRestart_truncatedCost_le ring hm P hn L T
  rw [htotal] at hcost
  have hbudget : 2 * (n * m) + 2 * n * n = 2 * n * (m + n) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [← hbudget]
  exact hcost

/-- Uniform gap length `h` recovers the bound `2*(n*m)*(1+h)` of
`Leader/Wu/ShortGap/DenialTransport.lean`. -/
theorem varGapCandidateRestart_truncatedCost_le_of_uniform
    {n m h : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : VarGapLayout n m)
    (hlen : ∀ g, L.len g = h) (T : Nat) :
    truncatedActiveCostNumerator
        (varGapCandidateRestartStep ring P L (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) := by
  have hcost := varGapCandidateRestart_truncatedCost_le ring hm P hn L T
  have htotal : L.totalLength = m * h := by
    simp [VarGapLayout.totalLength, hlen, ofFn_sum_const]
  rw [htotal] at hcost
  have hbudget : 2 * (n * m) + 2 * n * (m * h) = 2 * (n * m) * (1 + h) := by
    rw [Nat.mul_add, Nat.mul_one]
    have hswap : 2 * n * (m * h) = 2 * (n * m) * h := by ac_rfl
    rw [hswap]
  rw [← hbudget]
  exact hcost

/-- Consistency of the two special forms: uniform gaps tiling the ring have
`m * h = n`, and then `2*n*(m+n) = 2*(n*m)*(1+h)`. -/
theorem tiling_budget_eq_uniform_budget (n m h : Nat) (hmh : m * h = n) :
    2 * n * (m + n) = 2 * (n * m) * (1 + h) := by
  subst hmh
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  ac_rfl

/-! ## Clockwise distance on the physical ring -/

/-- Clockwise distance from vertex `a` to vertex `b` on the physical ring. -/
def cwDist {n : Nat} (a b : Fin n) : Nat := (b.val + n - a.val) % n

theorem cwDist_eq {n : Nat} (a b : Fin n) :
    cwDist a b =
      if a.val ≤ b.val then b.val - a.val else b.val + n - a.val := by
  have ha := a.isLt
  have hb := b.isLt
  unfold cwDist
  split
  · have hshift : b.val + n - a.val = (b.val - a.val) + n := by omega
    rw [hshift, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.mod_eq_of_lt (by omega)

theorem cwDist_lt {n : Nat} (a b : Fin n) : cwDist a b < n :=
  Nat.mod_lt _ (by have := a.isLt; omega)

theorem cwDist_pos_of_ne {n : Nat} (a b : Fin n) (hab : a ≠ b) :
    0 < cwDist a b := by
  have ha := a.isLt
  have hb := b.isLt
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rw [cwDist_eq]
  split <;> omega

/-- The vertex `k` steps clockwise from `a`. -/
def stepFrom {n : Nat} (a : Fin n) (k : Nat) : Fin n :=
  ⟨(a.val + k) % n, Nat.mod_lt _ (by have := a.isLt; omega)⟩

theorem stepFrom_val {n : Nat} (a : Fin n) (k : Nat) (hk : k < n) :
    (stepFrom a k).val =
      if a.val + k < n then a.val + k else a.val + k - n := by
  have ha := a.isLt
  simp only [stepFrom]
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

/-- Walking `k < n` steps clockwise lands at clockwise distance `k`. -/
theorem cwDist_stepFrom {n : Nat} (a : Fin n) (k : Nat) (hk : k < n) :
    cwDist a (stepFrom a k) = k := by
  have ha := a.isLt
  rw [cwDist_eq, stepFrom_val a k hk]
  by_cases hc : a.val + k < n
  · rw [if_pos hc]
    split <;> omega
  · rw [if_neg hc]
    split <;> omega

/-- Cyclic covering: a vertex `v` seen from two roots `r`, `r'` lies beyond
`r'` as seen from `r`, or beyond `r` as seen from `r'`. -/
theorem cwDist_cover {n : Nat} (r r' v : Fin n) :
    cwDist r r' ≤ cwDist r v ∨ cwDist r' r ≤ cwDist r' v := by
  have hr := r.isLt
  have hr' := r'.isLt
  have hv := v.isLt
  simp only [cwDist_eq]
  split <;> split <;> split <;> split <;> omega

/-! ## Placement-derived gaps -/

/-- Physical length of the gap from root `g` clockwise to its ring successor. -/
def gapLen {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (g : Fin m) : Nat :=
  cwDist (P.root g) (P.root (ring.rightNeighbor g))

/-- The `k`-th physical edge of gap `g`: its tail is `k` steps clockwise from
`P.root g`. -/
def gapEdge {n m : Nat} (P : Placement n m) (g : Fin m) (k : Nat) : Fin n :=
  stepFrom (P.root g) k

/-- The placed roots occur in ring order: no root lies strictly inside the
gap from any root to its ring successor. -/
def RootsOrdered {n m : Nat} (ring : DirectedRing m) (P : Placement n m) :
    Prop :=
  ∀ g g' : Fin m, cwDist (P.root g) (P.root g') < gapLen ring P g → g' = g

theorem gapLen_pos {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (hm : 1 < m) (g : Fin m) : 0 < gapLen ring P g :=
  cwDist_pos_of_ne _ _
    (fun h => rightNeighbor_ne ring hm g (P.root_injective h).symm)

theorem gapLen_lt {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (g : Fin m) : gapLen ring P g < n :=
  cwDist_lt _ _

theorem cwDist_gapEdge {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (g : Fin m) (k : Nat) (hk : k < gapLen ring P g) :
    cwDist (P.root g) (gapEdge P g k) = k :=
  cwDist_stepFrom _ _ (Nat.lt_trans hk (gapLen_lt ring P g))

/-- Under ring order, gap edges are pairwise distinct within one gap and
disjoint across different gaps. -/
theorem gapEdge_injective {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P)
    (g g' : Fin m) (k k' : Nat)
    (hk : k < gapLen ring P g) (hk' : k' < gapLen ring P g')
    (heq : gapEdge P g k = gapEdge P g' k') : g = g' ∧ k = k' := by
  have h1 := cwDist_gapEdge ring P g k hk
  have h2 := cwDist_gapEdge ring P g' k' hk'
  by_cases hg : g = g'
  · subst hg
    refine ⟨rfl, ?_⟩
    rw [← h1, ← h2, heq]
  · exfalso
    rcases cwDist_cover (P.root g) (P.root g') (gapEdge P g k) with hcov | hcov
    · exact hg (hord g g' (by omega)).symm
    · rw [heq] at hcov
      exact hg (hord g' g (by omega))

/-- The variable-length layout derived from an ordered placement. -/
def placementLayout {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (hord : RootsOrdered ring P) (hm : 1 < m) : VarGapLayout n m where
  len := gapLen ring P
  len_pos := gapLen_pos ring P hm
  edgeAt := fun g a => gapEdge P g a.val
  edgeAt_injective := fun g a g' a' heq =>
    gapEdge_injective ring P hord g g' a.val a'.val a.isLt a'.isLt heq

@[simp] theorem placementLayout_totalLength {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m)
    (hord : RootsOrdered ring P) (hm : 1 < m) :
    (placementLayout ring P hord hm).totalLength =
      (List.ofFn (fun g => gapLen ring P g)).sum := rfl

/-- Complete candidate process whose rearm walks denial tokens across the
placement-derived gaps. -/
noncomputable def placementCandidateRestartStep
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (hord : RootsOrdered ring P) (hm : 1 < m) :=
  varGapCandidateRestartStep ring P (placementLayout ring P hord hm)
    (by omega)

/-- Placement-derived bound: `2*n*m + 2*n*Σ_g gapLen g`. -/
theorem placementCandidateRestart_truncatedCost_le
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (hord : RootsOrdered ring P)
    (T : Nat) :
    truncatedActiveCostNumerator
        (placementCandidateRestartStep ring P hord hm)
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) +
        2 * n * (List.ofFn (fun g => gapLen ring P g)).sum) := by
  have hcost := varGapCandidateRestart_truncatedCost_le ring hm P hn
    (placementLayout ring P hord hm) T
  simpa [placementCandidateRestartStep] using hcost

/-- Placement-derived bound when the gaps tile the physical ring. -/
theorem placementCandidateRestart_truncatedCost_le_of_tiling
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (hord : RootsOrdered ring P)
    (htotal : (List.ofFn (fun g => gapLen ring P g)).sum = n) (T : Nat) :
    truncatedActiveCostNumerator
        (placementCandidateRestartStep ring P hord hm)
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * n * (m + n)) := by
  have hcost := varGapCandidateRestart_truncatedCost_le_of_tiling ring hm P hn
    (placementLayout ring P hord hm) htotal T
  simpa [placementCandidateRestartStep] using hcost

/-- Placement-derived reciprocal success tail. -/
theorem placementCandidateRestart_success_one_minus_inv_factor
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (hord : RootsOrdered ring P) :
    (factor - 1) * n ^ (factor * (2 * (n * m) +
        2 * n * (List.ofFn (fun g => gapLen ring P g)).sum)) ≤
      factor * successCount
        (placementCandidateRestartStep ring P hord hm)
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) +
          2 * n * (List.ofFn (fun g => gapLen ring P g)).sum)) := by
  have hsuccess := varGapCandidateRestart_success_one_minus_inv_factor
    ring hm P hn (placementLayout ring P hord hm) (factor := factor)
  simpa [placementCandidateRestartStep] using hsuccess

#print axioms varMultiGap_natBellmanSuperSolution
#print axioms varGapCandidateRestart_truncatedCost_le
#print axioms varGapCandidateRestart_truncatedCost_le_of_tiling
#print axioms varGapCandidateRestart_truncatedCost_le_of_uniform
#print axioms gapEdge_injective
#print axioms placementCandidateRestart_truncatedCost_le
#print axioms placementCandidateRestart_truncatedCost_le_of_tiling
#print axioms placementCandidateRestart_success_one_minus_inv_factor

end ShortGapDenialTransportPlacement
