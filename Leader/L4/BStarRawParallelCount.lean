import Leader.L4.BStarRawCausalCrossing
import Leader.L4.BStarRawDisplayBudget

/-! Publication-depth bounds on the literal original-epoch trace. -/
namespace L4.BStarRawParallelCount
open BStarRawCausalCrossing BStarRawDisplayBudget BStarRawBlockDrift Height
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarLongFixedRouting BStarCycleGeometry
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarPhysicalLiftAlignment
open BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarGrantWriterHistory
open BStarNativePointwise BStarNativePortGeometry BStarNativeNeedLift Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "run" => BStarResetSchedule.run (AllSizeS1Geometry.step B)

noncomputable def traceCrossing {base : X} (initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n → Nat) (history : List (Fin n)) (level : Nat)
    (i : Header (oldH6 B base)) (w : List (Fin n)) : Nat :=
  firstCrossing w.length (fun t =>
    traceCount hp base initial hh start (history++w.take t) i.val) level

theorem traceCrossing_initial {base : X} (initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n → Nat) (history : List (Fin n)) (level : Nat)
    (i : Header (oldH6 B base))
    (ready : level ≤ traceCount hp base initial hh start history i.val)
    (w : List (Fin n)) : traceCrossing hp initial hh start history level i w = 0 := by
  apply firstCrossing_initial
  simpa only [List.take_zero, List.append_nil] using ready

theorem traceCrossing_at_horizon_of_miss {base : X} (initial : X)
    (hh : ∃ i,oldH6 B base i=true) (start : Fin n → Nat) (history : List (Fin n))
    (level : Nat) (i : Header (oldH6 B base)) (w : List (Fin n))
    (miss : traceCount hp base initial hh start (history++w) i.val < level) :
    traceCrossing hp initial hh start history level i w = w.length := by
  let t := traceCrossing hp initial hh start history level i w
  have bound : t ≤ w.length := firstCrossing_le _ _ _
  apply Nat.le_antisymm bound
  apply Nat.le_of_not_gt
  intro early
  have meet : level ≤ traceCount hp base initial hh start (history++w.take t) i.val :=
    firstCrossing_reached _ _ _ early
  have dec : ((history++w.take t)++w.drop t) = history++w := by
    rw [List.append_assoc, List.take_append_drop]
  have mono :
      traceCount hp base initial hh start (history++w.take t) i.val ≤
        traceCount hp base initial hh start ((history++w.take t)++w.drop t) i.val := by
    rw [count_concat hp base initial hh start (history++w.take t) (w.drop t)]
    unfold traceCount
    exact count_monotone (traceCount hp base initial hh start (history++w.take t))
      (tapeInc hp base hh (run initial (history++w.take t)) (w.drop t)) i.val
      (Nat.zero_le _)
  rw [dec] at mono
  exact Nat.not_le_of_gt miss (Nat.le_trans meet mono)

/-- The original ledger gives the horizon witness on every missed
word. This is independent of the induction proving its moments. -/
theorem raw_quarter_miss_of_moments {base : X} (initial : X)
    (hh : ∃ i,oldH6 B base i=true) (start : Fin n → Nat)
    (history : List (Fin n)) (L lo cap : Nat) (Lpos : 0<L)
    (depth : cap+1-lo ≤ 2^25*total (oldH6 B base))
    (moment : ∀ i : Header (oldH6 B base),
      let D := 2^29*L*total (oldH6 B base)
      wordSum (fun w => 2^(traceCrossing hp initial hh start history
        (lo+(cap+1-lo)) i w/L)) D ≤ 12^(cap+1-lo)*n^D) :
    let D := 2^29*L*total (oldH6 B base)
    let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 B base),
      traceCount hp base initial hh start (history++w) i.val ≤ cap
    4*wordSum (massInd miss) D ≤ n^D := by
  dsimp only
  let m := total (oldH6 B base)
  let D := 2^29*L*m
  let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 B base),
    traceCount hp base initial hh start (history++w) i.val ≤ cap
  let T := fun (j : Fin m) w =>
    traceCrossing hp initial hh start history (lo+(cap+1-lo)) (atIndex hh j) w
  refine quarter_missed_at_display_deadline L (cap+1-lo) Lpos
    (total_pos (oldH6 B base) hh) depth T miss ?_ (fun j => moment (atIndex hh j))
  intro w len hm
  obtain ⟨i,bad⟩ := hm
  refine ⟨index hh i,?_⟩
  change traceCrossing hp initial hh start history (lo+(cap+1-lo))
    (atIndex hh (index hh i)) w = D
  rw [atIndex_index, traceCrossing_at_horizon_of_miss hp initial hh start history _ i w (by omega)]
  exact len

/-- The conditional per-level stopped bound suffices for the quarter
miss loss without an extra factor of the number of owners in time. -/
theorem raw_quarter_miss_of_child {base : X} (initial : X)
    (hh : ∃ i,oldH6 B base i=true) (start : Fin n → Nat)
    (history : List (Fin n)) (L lo cap : Nat) (Lpos : 0<L)
    (lower : ∀ i : Header (oldH6 B base),
      lo ≤ traceCount hp base initial hh start history i.val)
    (depth : cap+1-lo ≤ 2^25*total (oldH6 B base))
    (child : ∀ (k : Nat) (i : Header (oldH6 B base)),
      let D := 2^29*L*total (oldH6 B base)
      let T := fun l j w => traceCrossing hp initial hh start history (lo+l) j w
      wordSum (fun w => 2^(T (k+1) i w/L)) D ≤ 4*wordSum (fun w =>
        2^(max (T k (neighborHeader hh i 0) w)
          (max (T k (neighborHeader hh i 1) w) (T k (neighborHeader hh i 2) w))/L)) D) :
    let D := 2^29*L*total (oldH6 B base)
    let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 B base),
      traceCount hp base initial hh start (history++w) i.val ≤ cap
    4*wordSum (massInd miss) D ≤ n^D := by
  apply raw_quarter_miss_of_moments hp initial hh start history L lo cap Lpos depth
  intro i
  let m := total (oldH6 B base)
  let D := 2^29*L*m
  let U := fun k (j : Fin m) w =>
    traceCrossing hp initial hh start history (lo+k) (atIndex hh j) w
  let left : Fin m → Fin m := fun j => index hh (neighborHeader hh (atIndex hh j) 0)
  let right : Fin m → Fin m := fun j => index hh (neighborHeader hh (atIndex hh j) 2)
  have Z (j : Fin m) (w : List (Fin n)) (_ : w.length = D) : U 0 j w = 0 := by
    dsimp only [U,Nat.add_zero]
    exact traceCrossing_initial hp initial hh start history lo _ (lower _) w
  have S (k : Nat) (j : Fin m) := child k (atIndex hh j)
  have H : ∀ k j, wordSum (fun w => 2^(U (k+1) j w/L)) D ≤ 4*wordSum
      (fun w => 2^(max (U k j w) (max (U k (left j) w) (U k (right j) w))/L)) D := by
    intro k j
    dsimp [U,left,right]
    simpa only [atIndex_index,self_port,Nat.max_left_comm] using S k j
  have A := level_moments L D U left right Z H (cap+1-lo) (index hh i)
  simpa only [U, atIndex_index] using A

end L4.BStarRawParallelCount
