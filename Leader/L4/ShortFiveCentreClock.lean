import Leader.L4.ShortFiveParked
import Leader.L4.ShortReadCaptureGeometry

namespace L4.ShortFiveCentreClock
open PhysicalCustody ShortResetMIS1Ring ShortResetCycle ShortResetChart
open ShortSimultaneousOrder ShortFiveParked ShortInheritedRank ShortResetWatch
open ShortSimulLocal

theorem chart_center_is_right {s n : Nat} (x : Raw s n) (A : H2Ready x)
    (N : 9<n) (C : Chart (header x)) :
    nextAt C.root C.a =
      (PhysicalH1Neighbors.right A.1 ⟨C.root,C.rootHeader⟩).val := by
  obtain ⟨a,b,L,H,_,_,_⟩ := ShortReadCaptureGeometry.capture_chart_fields x A.1 C N
  have P := (H C.a (by omega)).mpr (.inr (.inl rfl))
  have D := PhysicalH1Neighbors.rightDist_eq_gap a P (by
    intro k K B
    apply Bool.eq_false_iff.mpr
    intro R
    have V := (H k (by omega)).mp R
    omega)
  change nextAt C.root C.a=nextAt C.root (PhysicalH1Neighbors.rightDist (header x) C.root)
  rw [D]

/-- Choose the nominal *publication site* first. The stopped clock
cleans the previous selected site as its central *source* and exports
the exact clockwise witness needed by the fenced physical word. -/
theorem fixed_five_for_centre {s n : Nat} (N : 21<n) (x : Raw s n) (A : H2Ready x)
    (i : PhysicalH1Neighbors.Sites (header x)) :
    let owner := PhysicalH1Neighbors.left A.1 i
    let left := PhysicalH1Neighbors.left A.1
    let start := left (left owner)
    ∃ cs : Fin 5 → Chart (header x),
      (∀ j, (cs j).root=nextAt start.val (offset (header x) start.val j.val)) ∧
      (cs 2).root=owner.val ∧
      nextAt (cs 2).root (cs 2).a=i.val ∧
      (cs 3).root=i.val ∧
      (∀ j, (cs j).L≤9) ∧
      (∀ j, ∃ g : Nat, 0<g ∧ g+1<(cs j).L ∧
        ∀ (y : Raw s n), H2Ready y → (∀ q,header y q=header x q) →
          ∀ k, k<(cs j).L → (ShortGateChart.slotGate (cs j) y k=true ↔ k=g)) ∧
      (∀ j k : Fin 5, j≠k → (cs j).root≠(cs k).root) ∧
      ∀ y : Raw s n, Fiber (header x) y →
        L4.IIDExpectedHittingTimeAtMost (rawNext s) (FiveParked cs) y (n*50^40575) := by
  let owner := PhysicalH1Neighbors.left A.1 i
  let left := PhysicalH1Neighbors.left A.1
  let start := left (left owner)
  obtain ⟨cs,coords,small,gates,order,distinct⟩ :=
    clockwise_five x A.1 start.val start.property N
  have p := offset_two_on_double_left A.1 owner
  change nextAt start.val (offset (header x) start.val 2)=owner.val at p
  have mid : (cs 2).root=owner.val := (coords 2).trans p
  have rootEq : (⟨(cs 2).root,(cs 2).rootHeader⟩ : PhysicalH1Neighbors.Sites (header x)) = owner :=
    Subtype.ext mid
  have R : (PhysicalH1Neighbors.right A.1 owner).val=i.val :=
    congrArg Subtype.val (PhysicalH1Neighbors.right_left A.1 i)
  have center : nextAt (cs 2).root (cs 2).a=i.val := by
    exact (chart_center_is_right x A (by omega) (cs 2)).trans
      ((congrArg (fun t => (PhysicalH1Neighbors.right A.1 t).val) rootEq).trans R)
  have next : (cs 3).root=i.val := by
    rw [coords 3]
    change nextAt start.val (offset (header x) start.val 2 +
      PhysicalH1Neighbors.rightDist (header x)
        (nextAt start.val (offset (header x) start.val 2))) = i.val
    rw [nextAt_add,p]
    exact R
  have n5 : 5≤n := by omega
  have nom (j : Fin 5) : ForwardNomination (s:=s) (cs j) := by
    obtain ⟨g,P,L,G⟩ := gates j
    intro y Y heads none
    exact ShortLeastForward.nominate_forward (cs j) n5 y Y heads g P L G none
  exact ⟨cs,coords,mid,center,next,small,gates,distinct,
    fun y Y => fixed_five_parked_expected n5 cs small nom order y Y⟩

end L4.ShortFiveCentreClock
