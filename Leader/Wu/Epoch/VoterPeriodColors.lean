import Leader.Wu.Epoch.VoterSumTools
import Leader.Wu.Epoch.VoterColorDrift
import Leader.Wu.Epoch.VoterActionTree
import Leader.Wu.Epoch.FilterProtectedPotential
import Leader.Wu.Epoch.FilterProtectedActionTree
import Leader.Wu.Epoch.FilterCubicBlock

/-!
# A `Fin h` color layer for the directed voter bound

The polynomial epoch-voter theorem is stated for colors in `Fin n`, although
its transition only copies colors.  This module embeds `Fin h` into `Fin n`
when `h <= n`, transfers the exact finite scheduler tree, and connects that
process to the period-`h` successor repair through offset colors.

No second `Fin h` is part of the protocol state.  The offset color and the
physical coordinate below are proof-level projections of the one stored
position field.
-/

namespace PPLLPeriodHColorVoter

open PPLLResearchFormulation PPLLEpochVoterReduction
  PPLLEpochVoterFiniteTree PPLLEpochVoterPolynomialUpper

set_option autoImplicit false
set_option warningAsError true

private theorem mod_add_mod_left (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod (a % m) b m, Nat.mod_mod]
  exact (Nat.add_mod a b m).symm

/-! ## Finite-color voter as a restriction of the checked `Fin n` voter -/

/-- One clockwise update on an arbitrary `Fin h` color word. -/
def finiteColorStep {n h : Nat} (ring : DirectedRing n)
    (D : Fin n -> Fin h) (e : Fin n) : Fin n -> Fin h :=
  fun i => if i = e then D e
    else if i = ring.rightNeighbor e then D e else D i

/-- Inject the smaller color alphabet into the already-checked `Fin n` voter. -/
def liftColors {n h : Nat} (hle : h <= n)
    (D : Fin n -> Fin h) : Fin n -> Fin n :=
  fun i => Fin.castLE hle (D i)

theorem liftColors_injective {n h : Nat} (hle : h <= n) :
    Function.Injective (liftColors hle : (Fin n -> Fin h) -> (Fin n -> Fin n)) := by
  intro D E hDE
  funext i
  apply Fin.ext
  have hv := congrArg Fin.val (congrFun hDE i)
  exact hv

/-- The embedding commutes exactly with every local voter action. -/
theorem liftColors_finiteColorStep {n h : Nat} (hle : h <= n)
    (ring : DirectedRing n) (D : Fin n -> Fin h) (e : Fin n) :
    liftColors hle (finiteColorStep ring D e) =
      directedVoterStep ring (liftColors hle D) e := by
  funext i
  simp only [liftColors, finiteColorStep, directedVoterStep]
  by_cases hie : i = e
  · simp [hie]
  · by_cases hir : i = ring.rightNeighbor e
    · simp [hir]
    · simp [hie, hir]

/-- Consensus over the actual `Fin h` color alphabet. -/
def FiniteColorConsensus {n h : Nat} (D : Fin n -> Fin h) : Prop :=
  exists color : Fin h, forall i, D i = color

/-- Restricting colors preserves and reflects consensus. -/
theorem voterConsensus_liftColors_iff {n h : Nat} (hle : h <= n)
    (hn : 0 < n) (D : Fin n -> Fin h) :
    VoterConsensus (liftColors hle D) <-> FiniteColorConsensus D := by
  constructor
  · rintro ⟨_color, hcolor⟩
    let zero : Fin n := ⟨0, hn⟩
    refine ⟨D zero, ?_⟩
    intro i
    apply Fin.ext
    have hv := congrArg Fin.val ((hcolor i).trans (hcolor zero).symm)
    exact hv
  · rintro ⟨color, hcolor⟩
    exact ⟨Fin.castLE hle color, fun i => by
      simp only [liftColors]
      rw [hcolor i]⟩

/-- Exact miss count, defined by the injective restriction of the existing
action tree. -/
noncomputable def finiteColorMissTree {n h : Nat} (hle : h <= n)
    (ring : DirectedRing n) (D : Fin n -> Fin h) (t : Nat) : Nat :=
  voterMissTree ring (liftColors hle D) t

@[simp] theorem finiteColorMissTree_zero {n h : Nat} (hle : h <= n)
    (ring : DirectedRing n) (D : Fin n -> Fin h) :
    finiteColorMissTree hle ring D 0 =
      @ite Nat (FiniteColorConsensus D) (Classical.propDecidable _) 0 1 := by
  simp only [finiteColorMissTree, voterMissTree]
  rw [show VoterConsensus (liftColors hle D) = FiniteColorConsensus D from
    propext (voterConsensus_liftColors_iff hle ring.hn D)]

@[simp] theorem finiteColorMissTree_succ {n h : Nat} (hle : h <= n)
    (ring : DirectedRing n) (D : Fin n -> Fin h) (t : Nat) :
    finiteColorMissTree hle ring D (t + 1) =
      @ite Nat (FiniteColorConsensus D) (Classical.propDecidable _) 0
        ((List.ofFn (fun e : Fin n =>
          finiteColorMissTree hle ring (finiteColorStep ring D e) t)).sum) := by
  simp only [finiteColorMissTree, voterMissTree]
  rw [show VoterConsensus (liftColors hle D) = FiniteColorConsensus D from
    propext (voterConsensus_liftColors_iff hle ring.hn D)]
  have hfun :
      (fun e : Fin n => voterMissTree ring
        (directedVoterStep ring (liftColors hle D) e) t) =
      (fun e : Fin n => voterMissTree ring
        (liftColors hle (finiteColorStep ring D e)) t) := by
    funext e
    rw [liftColors_finiteColorStep]
  rw [hfun]

/-- Exact finite-horizon tail inequality for `Fin h` colors. -/
theorem finiteColorMissTree_tail_moment {n h : Nat} (hle : h <= n)
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n -> Fin h) (t : Nat) :
    2 * (t + 1) * finiteColorMissTree hle ring D t <= n ^ t * n ^ 3 := by
  exact voterMissTree_tail_moment hn2 ring (liftColors hle D) t

/-- Weighted survival count.  Dividing `n * value` by `n^t` gives the exact
truncated expected consensus time through depth `t-1`. -/
noncomputable def finiteColorWeightedMissTotal {n h : Nat} (hle : h <= n)
    (ring : DirectedRing n) (D : Fin n -> Fin h) (t : Nat) : Nat :=
  voterWeightedMissTotal ring (liftColors hle D) t

/-- Division-free form of the uniform-scheduler expectation bound
`E[min(T,t)] <= n^3 / 2`. -/
theorem finiteColor_truncated_expectation_le_half_cube
    {n h : Nat} (hle : h <= n) (hn2 : 1 < n)
    (ring : DirectedRing n) (D : Fin n -> Fin h) (t : Nat) :
    2 * (n * finiteColorWeightedMissTotal hle ring D t) <= n ^ t * n ^ 3 := by
  have hbudget := voterWeightedMissTotal_budget hn2 ring (liftColors hle D) t
  have hscaled := Nat.mul_le_mul_left n hbudget
  change 2 * (n * voterWeightedMissTotal ring (liftColors hle D) t) <=
    n ^ t * n ^ 3
  calc
    2 * (n * voterWeightedMissTotal ring (liftColors hle D) t) =
        n * (2 * voterWeightedMissTotal ring (liftColors hle D) t) := by
          exact Nat.mul_left_comm 2 n _
    _ <= n * (n ^ t * n ^ 2) := hscaled
    _ = n ^ t * n ^ 3 := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]

/-! ## Period repair and offset-color conjugacy -/

def successorH {h : Nat} (hh : 0 < h) (p : Fin h) : Fin h :=
  ⟨(p.val + 1) % h, Nat.mod_lt _ hh⟩

/-- Advancing both arguments preserves their modular difference. -/
theorem successorH_sub_successorH {h : Nat} (hh : 0 < h)
    (p c : Fin h) : successorH hh p - successorH hh c = p - c := by
  apply Fin.ext
  simp only [Fin.sub_def, successorH]
  by_cases hc : c.val + 1 < h
  · rw [Nat.mod_eq_of_lt hc]
    by_cases hp : p.val + 1 < h
    · rw [Nat.mod_eq_of_lt hp]
      have hsame : h - (c.val + 1) + (p.val + 1) =
          h - c.val + p.val := by omega
      rw [hsame]
    · have hpe : p.val + 1 = h := by omega
      rw [hpe, Nat.mod_self]
      have hleft : h - (c.val + 1) + 0 = h - c.val - 1 := by omega
      have hright : h - c.val + p.val = h + (h - c.val - 1) := by omega
      rw [hleft, hright, Nat.add_mod_left]
  · have hce : c.val + 1 = h := by omega
    rw [hce, Nat.mod_self]
    by_cases hp : p.val + 1 < h
    · rw [Nat.mod_eq_of_lt hp]
      have hleft : h - 0 + (p.val + 1) = h + (p.val + 1) := by omega
      have hright : h - c.val + p.val = p.val + 1 := by omega
      rw [hleft, hright, Nat.add_mod_left]
    · have hpe : p.val + 1 = h := by omega
      rw [hpe, Nat.mod_self]
      have hleft : h - 0 + 0 = h := by omega
      have hright : h - c.val + p.val = h := by omega
      rw [hleft, hright, Nat.mod_self]

/-- Cancellation for the concrete modular subtraction on `Fin h`. -/
theorem eq_of_sub_right_eq {h : Nat} (a b c : Fin h)
    (hab : a - c = b - c) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [Fin.sub_def] at hv
  have hv2 := congrArg (fun x : Nat => (x + c.val) % h) hv
  rw [mod_add_mod_left, mod_add_mod_left] at hv2
  have ha : h - c.val + a.val + c.val = h + a.val := by omega
  have hb : h - c.val + b.val + c.val = h + b.val := by omega
  rw [ha, hb, Nat.add_mod_left, Nat.add_mod_left,
    Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hv2
  exact hv2

/-- A proof-level cyclic coordinate; it is not stored alongside `pos`. -/
def CyclicCoordinate {n h : Nat} (hh : 0 < h) (ring : DirectedRing n)
    (coord : Fin n -> Fin h) : Prop :=
  forall e, coord (ring.rightNeighbor e) = successorH hh (coord e)

def offsetColors {n h : Nat} (coord : Fin n -> Fin h)
    (P : Fin n -> Fin h) : Fin n -> Fin h :=
  fun i => P i - coord i

/-- Priority position repair, written without the redundant defect test. -/
def periodRepairStep {n h : Nat} (hh : 0 < h) (ring : DirectedRing n)
    (P : Fin n -> Fin h) (e : Fin n) : Fin n -> Fin h :=
  fun i => if i = e then P e
    else if i = ring.rightNeighbor e then successorH hh (P e) else P i

/-- Offset colors conjugate period repair to the finite-color voter action. -/
theorem offsetColors_periodRepairStep {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (coord : Fin n -> Fin h)
    (hcoord : CyclicCoordinate hh ring coord)
    (P : Fin n -> Fin h) (e : Fin n) :
    offsetColors coord (periodRepairStep hh ring P e) =
      finiteColorStep ring (offsetColors coord P) e := by
  funext i
  simp only [offsetColors, periodRepairStep, finiteColorStep]
  by_cases hie : i = e
  · simp [hie]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp only [hie, if_false, if_pos]
      rw [hcoord e, successorH_sub_successorH]
    · simp [hie, hir]

/-- Edge equality forces consensus for the smaller color alphabet. -/
theorem finiteColorConsensus_of_forall_edge_eq {n h : Nat} (hle : h <= n)
    (ring : DirectedRing n) (D : Fin n -> Fin h)
    (hall : forall e, D e = D (ring.rightNeighbor e)) :
    FiniteColorConsensus D := by
  apply (voterConsensus_liftColors_iff hle ring.hn D).mp
  apply voterConsensus_of_forall_edge_eq ring (liftColors hle D)
  intro e
  exact congrArg (Fin.castLE hle) (hall e)

/-- The target closed set for the period repair. -/
def SuccessorGrid {n h : Nat} (hh : 0 < h) (ring : DirectedRing n)
    (P : Fin n -> Fin h) : Prop :=
  forall e, P (ring.rightNeighbor e) = successorH hh (P e)

/-- Successor grids are exactly consensus words in offset coordinates. -/
theorem successorGrid_iff_offset_consensus {n h : Nat} (hh : 0 < h)
    (hle : h <= n) (ring : DirectedRing n) (coord : Fin n -> Fin h)
    (hcoord : CyclicCoordinate hh ring coord) (P : Fin n -> Fin h) :
    SuccessorGrid hh ring P <->
      FiniteColorConsensus (offsetColors coord P) := by
  constructor
  · intro hgrid
    apply finiteColorConsensus_of_forall_edge_eq hle ring
    intro e
    simp only [offsetColors]
    rw [hgrid e, hcoord e, successorH_sub_successorH]
  · rintro ⟨color, hcolor⟩
    intro e
    apply eq_of_sub_right_eq _ _ (coord (ring.rightNeighbor e))
    rw [hcoord e]
    calc
      P (ring.rightNeighbor e) - successorH hh (coord e) = color :=
        by simpa [offsetColors, hcoord e] using hcolor (ring.rightNeighbor e)
      _ = P e - coord e := (hcolor e).symm
      _ = successorH hh (P e) - successorH hh (coord e) :=
        (successorH_sub_successorH hh (P e) (coord e)).symm

/-- A successor grid has no effective repair action. -/
theorem periodRepairStep_eq_self_of_grid {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (P : Fin n -> Fin h)
    (hgrid : SuccessorGrid hh ring P) (e : Fin n) :
    periodRepairStep hh ring P e = P := by
  funext i
  simp only [periodRepairStep]
  by_cases hie : i = e
  · simp [hie]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp [hie, hgrid e]
    · simp [hie, hir]

/-- There are no non-grid fixed points once the physical ring is nontrivial. -/
theorem periodRepairStep_fixed_iff_grid {n h : Nat} (hh : 0 < h)
    (hn2 : 1 < n) (ring : DirectedRing n) (P : Fin n -> Fin h) :
    (forall e, periodRepairStep hh ring P e = P) <->
      SuccessorGrid hh ring P := by
  constructor
  · intro hfixed e
    have hne := rightNeighbor_ne hn2 ring e
    have hv := congrFun (hfixed e) (ring.rightNeighbor e)
    have hv' : successorH hh (P e) = P (ring.rightNeighbor e) := by
      simpa [periodRepairStep, hne] using hv
    exact hv'.symm
  · intro hgrid e
    exact periodRepairStep_eq_self_of_grid hh ring P hgrid e

/-! ## The concrete proof-level coordinate supplied by `h | n` -/

def periodCoordinate {n h : Nat} (hh : 0 < h) (i : Fin n) : Fin h :=
  ⟨i.val % h, Nat.mod_lt _ hh⟩

theorem periodCoordinate_cyclic {n h : Nat} (hh : 0 < h)
    (hdvd : h ∣ n) (ring : DirectedRing n) :
    CyclicCoordinate hh ring (periodCoordinate hh) := by
  intro e
  apply Fin.ext
  simp only [periodCoordinate, DirectedRing.rightNeighbor, successorH]
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact (mod_add_mod_left e.val 1 h).symm

noncomputable def periodGridMissTree {n h : Nat} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (P : Fin n -> Fin h) (t : Nat) : Nat :=
  finiteColorMissTree (Nat.le_of_dvd ring.hn hdvd) ring
    (offsetColors (periodCoordinate hh) P) t

noncomputable def periodGridWeightedMissTotal {n h : Nat}
    (hh : 0 < h) (hdvd : h ∣ n) (ring : DirectedRing n)
    (P : Fin n -> Fin h) (t : Nat) : Nat :=
  finiteColorWeightedMissTotal (Nat.le_of_dvd ring.hn hdvd) ring
    (offsetColors (periodCoordinate hh) P) t

/-- Exact iid tail for the actual priority position-repair process.  By the
conjugacy and grid/consensus equivalence above, this counts words that have not
yet entered the closed successor-grid set. -/
theorem periodGridMissTree_tail_moment {n h : Nat} (hh : 0 < h)
    (hdvd : h ∣ n) (hn2 : 1 < n) (ring : DirectedRing n)
    (P : Fin n -> Fin h) (t : Nat) :
    2 * (t + 1) * periodGridMissTree hh hdvd ring P t <=
      n ^ t * n ^ 3 := by
  exact finiteColorMissTree_tail_moment
    (Nat.le_of_dvd ring.hn hdvd) hn2 ring
    (offsetColors (periodCoordinate hh) P) t

/-- Division-free exact form of
`E[min(T_grid,t)] <= n^3 / 2` under the uniform directed-edge scheduler. -/
theorem periodGrid_truncated_expectation_le_half_cube
    {n h : Nat} (hh : 0 < h) (hdvd : h ∣ n)
    (hn2 : 1 < n) (ring : DirectedRing n)
    (P : Fin n -> Fin h) (t : Nat) :
    2 * (n * periodGridWeightedMissTotal hh hdvd ring P t) <=
      n ^ t * n ^ 3 := by
  exact finiteColor_truncated_expectation_le_half_cube
    (Nat.le_of_dvd ring.hn hdvd) hn2 ring
    (offsetColors (periodCoordinate hh) P) t

end PPLLPeriodHColorVoter
