import Leader.Wu.Seal.TasepVarianceDrop
import Leader.Wu.Seal.JohnsonPoincareStatements
import Leader.Wu.Seal.TasepFiniteTime
import Leader.Wu.Scheduler.Probability
import Leader.Wu.Seal.ABGate

namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepAdjoint
open PPLL PPLLResearchFormulation PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonPoincareA2a SealTasepL2Contraction
open PPartialSealSweepABGateBreakthroughSol
set_option autoImplicit false
set_option Elab.async false

abbrev SealObs (n : Nat) := (Fin n -> Bool) -> Int
def sealPNumerator {n : Nat} (ring : DirectedRing n) (f : SealObs n)
    (F : Fin n -> Bool) : Int :=
  (List.ofFn fun e : Fin n => f (localStep ring clockwiseTasepPair F e)).sum
def sealPNumeratorIter {n : Nat} (ring : DirectedRing n)
    (f : SealObs n) : Nat -> SealObs n
  | 0 => f
  | t + 1 => sealPNumeratorIter ring (sealPNumerator ring f) t
private noncomputable def eqb {a : Type} (x y : a) : Bool :=
  @ite Bool (x = y) (Classical.propDecidable _) true false

private theorem isumMapAdd {a : Type} (xs : List a) (f g : a -> Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with | nil => simp | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega
private theorem isumMapConst {a : Type} (xs : List a) (c : Int) :
    (xs.map (fun _ => c)).sum = (xs.length : Int) * c := by
  induction xs with | nil => simp | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_succ, ih, Int.add_mul, Int.one_mul]; omega
private theorem isumMapComm {a b : Type} (xs : List a) (ys : List b) (f : a -> b -> Int) :
    (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil]; simpa using (isumMapConst ys 0).symm
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; simpa using (isumMapAdd ys (fun y => f x y) (fun y => (xs.map (fun z => f z y)).sum)).symm
private theorem isumFilter {a : Type} (xs : List a) (p : a -> Bool) (f : a -> Int) :
    ((xs.filter p).map f).sum = (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with | nil => rfl | cons x xs ih => cases h : p x <;> simp [h, ih]
private theorem isumMapMulRight {a : Type} (xs : List a) (f : a -> Int) (c : Int) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with | nil => simp | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Int.add_mul]
private theorem isumFlatMap {a b : Type} (xs : List a) (ys : a -> List b) (f : b -> Int) :
    ((xs.flatMap ys).map f).sum = (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with | nil => rfl | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]
private theorem isumOfFnMulLeft {m : Nat} (c : Int) (f : Fin m -> Int) :
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  induction m with | zero => simp | succ m ih => rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons, ih (fun i => f i.succ), Int.mul_add]
private theorem isumEqFiber {b : Type} (ys : List b) (hys : ys.Nodup) (y : b) (c : Int) :
    (ys.map (fun z => if eqb y z then c else 0)).sum =
      @ite Int (y ∈ ys) (Classical.propDecidable _) c 0 := by
  classical
  induction ys with
  | nil => simp
  | cons z ys ih =>
      rw [List.nodup_cons] at hys
      have h2 := ih hys.2
      simp only [eqb, decide_eq_true_eq] at h2
      by_cases h : y = z
      · subst h
        simp [hys.1] at h2
        simp [eqb, h2]
      · simp [eqb, h]
        simp at h2
        rw [h2]
        by_cases hm : y ∈ ys <;> simp [hm]
private theorem fiberWeighted {a b : Type} (xs : List a) (ys : List b)
    (out : a -> b) (u : a -> Int) (v : b -> Int) (hys : ys.Nodup)
    (hout : ∀ x, x ∈ xs -> out x ∈ ys) :
    (ys.map (fun y => ((xs.filter (fun x => eqb (out x) y)).map u).sum * v y)).sum =
      (xs.map (fun x => u x * v (out x))).sum := by
  classical
  calc
    _ = (ys.map (fun y => ((xs.filter (fun x => eqb (out x) y)).map (fun x => u x * v y)).sum)).sum := by
      apply congrArg List.sum; apply List.map_congr_left; intro y _; rw [isumMapMulRight]
    _ = (ys.map (fun y => (xs.map (fun x => if eqb (out x) y then u x * v y else 0)).sum)).sum := by
      apply congrArg List.sum; apply List.map_congr_left; intro y _; exact isumFilter _ _ _
    _ = (xs.map (fun x => (ys.map (fun y => if eqb (out x) y then u x * v y else 0)).sum)).sum := isumMapComm ys xs _
    _ = _ := by
      apply congrArg List.sum; apply List.map_congr_left; intro x hx
      calc
        _ = (ys.map (fun y => if eqb (out x) y then u x * v (out x) else 0)).sum := by
          apply congrArg List.sum; apply List.map_congr_left; intro y _; by_cases h : out x = y <;> simp [eqb, h]
        _ = u x * v (out x) := by rw [isumEqFiber ys hys]; simp [hout x hx]
private theorem incomingEqFilter {n : Nat} (ring : DirectedRing n) (k : Nat) (G : Fin n -> Bool) :
    tasepSliceIncomingPairs ring k G =
      (tasepSliceSchedulerPairs n k).filter (fun p => eqb (localStep ring clockwiseTasepPair p.1 p.2) G) := by
  classical
  unfold tasepSliceIncomingPairs
  apply congrArg (fun q : (((Fin n -> Bool) × Fin n) -> Bool) => (tasepSliceSchedulerPairs n k).filter q)
  funext p; by_cases h : localStep ring clockwiseTasepPair p.1 p.2 = G <;> simp [eqb, h]
private theorem schedulerEndpointMem {n k : Nat} (ring : DirectedRing n)
    (p : (Fin n -> Bool) × Fin n) (hp : p ∈ tasepSliceSchedulerPairs n k) :
    localStep ring clockwiseTasepPair p.1 p.2 ∈ tasepFrontConfigSlice n k := by
  have hF := (mem_tasepSliceSchedulerPairs_iff p.1 p.2).mp hp
  by_cases hn : 1 < n
  · rw [mem_tasepFrontConfigSlice_iff] at hF ⊢
    exact (frontConfigMass_clockwiseTasep_localStep ring hn p.1 p.2).trans hF
  · have hone : n = 1 := by have hp' := p.2.isLt; omega
    subst n
    have hs : localStep ring clockwiseTasepPair p.1 p.2 = p.1 := by
      funext i
      have hi : i = p.2 := Subsingleton.elim _ _
      have hj : ring.rightNeighbor p.2 = p.2 := Subsingleton.elim _ _
      subst i
      cases hb : p.1 p.2 <;> simp [localStep, hj, clockwiseTasepPair, hb]
    rw [hs]; exact hF

theorem sealPStar_adjoint {n : Nat} (ring : DirectedRing n) (k : Nat) (f h : SealObs n) :
    sealSliceIntDot k (sealPStarNumerator ring k f) h = sealSliceIntDot k f (sealPNumerator ring h) := by
  classical
  let xs := tasepSliceSchedulerPairs n k
  let ys := tasepFrontConfigSlice n k
  let out := fun p : (Fin n -> Bool) × Fin n => localStep ring clockwiseTasepPair p.1 p.2
  have hp := fiberWeighted xs ys out (fun p => f p.1) h (tasepFrontConfigSlice_nodup n k) (schedulerEndpointMem ring)
  calc
    _ = (ys.map (fun G => (((xs.filter (fun p => eqb (out p) G)).map (fun p => f p.1)).sum) * h G)).sum := by
      unfold sealSliceIntDot sealPStarNumerator; apply congrArg List.sum; apply List.map_congr_left; intro G _; rw [incomingEqFilter]
    _ = (xs.map (fun p => f p.1 * h (out p))).sum := hp
    _ = _ := by
      simp only [xs, ys, out]
      unfold tasepSliceSchedulerPairs sealSliceIntDot sealPNumerator
      rw [isumFlatMap]
      apply congrArg List.sum; apply List.map_congr_left; intro F _
      simpa [List.map_ofFn, Function.comp_def] using isumOfFnMulLeft (f F) (fun e : Fin n => h (localStep ring clockwiseTasepPair F e))
theorem sealPStarIter_adjoint {n : Nat} (ring : DirectedRing n) (k t : Nat) (f h : SealObs n) :
    sealSliceIntDot k (sealPStarNumeratorIter ring k f t) h = sealSliceIntDot k f (sealPNumeratorIter ring h t) := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih => rw [sealPStarNumeratorIter, sealPStar_adjoint]; exact ih (sealPNumerator ring h)
private theorem run_append_single {n : Nat} (ring : DirectedRing n) (F : Fin n -> Bool)
    (w : DetSchedule n) (e : Fin n) :
    runLocalSchedule ring clockwiseTasepPair F (w ++ [e]) =
      localStep ring clockwiseTasepPair (runLocalSchedule ring clockwiseTasepPair F w) e := by
  induction w generalizing F with
  | nil => rfl
  | cons a w ih => simp only [List.cons_append, runLocalSchedule]; exact ih (localStep ring clockwiseTasepPair F a)
theorem sealPNumeratorIter_eq_scheduleSum {n : Nat} (ring : DirectedRing n)
    (h : SealObs n) (t : Nat) (F : Fin n -> Bool) :
    sealPNumeratorIter ring h t F =
      ((allSchedules n t).map fun w => h (runLocalSchedule ring clockwiseTasepPair F w)).sum := by
  induction t generalizing h F with
  | zero => simp [sealPNumeratorIter, allSchedules, runLocalSchedule]
  | succ t ih =>
      rw [sealPNumeratorIter, ih]
      simp only [allSchedules]
      unfold sealPNumerator
      rw [isumFlatMap]
      apply congrArg List.sum; apply List.map_congr_left; intro s _
      simp only [List.map_ofFn, Function.comp_def]
      apply congrArg List.sum; apply congrArg List.ofFn; funext e
      rw [run_append_single]

end SealTasepAdjoint
end PPLLCompleteMultiLeaderCleanup
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepAdjoint.sealPStar_adjoint
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepAdjoint.sealPStarIter_adjoint
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepAdjoint.sealPNumeratorIter_eq_scheduleSum
