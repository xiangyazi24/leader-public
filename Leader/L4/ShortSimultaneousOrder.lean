import Leader.L4.ShortGateChart
import Leader.L4.ShortResetWatch
import Leader.L4.PhysicalH1Neighbors

namespace L4.ShortSimultaneousOrder
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1
open ShortResetChart ShortResetCycle ShortResetWatch ShortResetMIS1Ring

/-- Take clockwise coordinates relative to an arbitrary physical anchor.
The entire right chart, including its terminal endpoint, must fit inside
one traversal from the anchor. Its watched marks then omit the earlier
chart's incoming door, even across the physical seam. -/
theorem earlier_door_omitted {n : Nat} {h : Fin n → Bool}
    (C D : Chart h) (root : Fin n) (a b : Nat)
    (Croot : C.root=nextAt root a) (Droot : D.root=nextAt root b)
    (lt : a<b) (fit : b+D.L<n) :
    RearTrace.predecessor C.root ∉ watch D := by
  intro E
  have A : rightNeighbor (RearTrace.predecessor C.root)=nextAt root a :=
    (RearTrace.right_predecessor C.root).trans Croot
  rcases (mem_watch D _).mp E with E|⟨k,K,E⟩
  · have B : rightNeighbor (RearTrace.predecessor C.root)=nextAt root b := by
      rw [E,incoming_spec,Droot]
    have Eq := nextAt_injective_under root a b (by omega) (by omega) (A.symm.trans B)
    omega
  · have B : rightNeighbor (RearTrace.predecessor C.root)=nextAt root (b+k+1) := by
      rw [E,Droot,←nextAt_add]
      rfl
    have Eq := nextAt_injective_under root a (b+k+1) (by omega) (by omega) (A.symm.trans B)
    omega

/-- Lift the consecutive selected physical H1 roots into clockwise
coordinates without assuming that the physical zero is outside the arc. -/
def offset {n : Nat} (h : Fin n → Bool) (r : Fin n) : Nat → Nat
  | 0 => 0
  | k+1 => let a := offset h r k; a + PhysicalH1Neighbors.rightDist h (nextAt r a)

theorem offset_strict {n : Nat} (h : Fin n → Bool) (r : Fin n) (k : Nat) :
    offset h r k < offset h r (k+1) := by
  change _ < _ + PhysicalH1Neighbors.rightDist h (nextAt r (offset h r k))
  unfold PhysicalH1Neighbors.rightDist
  split <;> omega

theorem offset_monotone {n : Nat} (h : Fin n → Bool) (r : Fin n) {i j : Nat} (lt : i<j) :
    offset h r i < offset h r j := by
  induction j with
  | zero => omega
  | succ j IH =>
    by_cases H : i=j
    · subst i
      exact offset_strict h r j
    · exact Nat.lt_trans (IH (by omega)) (offset_strict h r j)

theorem offset_bound {n : Nat} (h : Fin n → Bool) (r : Fin n) (k : Nat) :
    offset h r k ≤ 3*k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k IH =>
    change _ + PhysicalH1Neighbors.rightDist h (nextAt r (offset h r k)) ≤ _
    unfold PhysicalH1Neighbors.rightDist
    split <;> omega

theorem offset_at_header {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (r : Fin n) (R : header x r=true) (k : Nat) :
    header x (nextAt r (offset (header x) r k))=true := by
  induction k with
  | zero => exact R
  | succ k IH =>
    change header x (nextAt r
      (offset (header x) r k +
        PhysicalH1Neighbors.rightDist (header x) (nextAt r (offset (header x) r k))))=true
    rw [nextAt_add]
    exact PhysicalH1Neighbors.rightDist_header M ⟨_,IH⟩

/-- A concrete clockwise census. Each of the five charts comes with the
unique admission gate already used by the checked single-chart mean.
Starting from the leftmost root, offset at most 12 plus chart length at
most 9 fits before the next occurrence of the leftmost root. -/
theorem clockwise_five {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (r : Fin n) (R : header x r=true) (N : 21<n) :
    ∃ C : Fin 5 → Chart (header x),
      (∀ i, (C i).root=nextAt r (offset (header x) r i.val)) ∧
      (∀ i, (C i).L≤9) ∧
      (∀ i, ∃ g : Nat, 0<g ∧ g+1<(C i).L ∧
        ∀ (y : Raw s n), H2Ready y → (∀ q, header y q=header x q) →
          ∀ k, k<(C i).L → (ShortGateChart.slotGate (C i) y k=true ↔ k=g)) ∧
      (∀ i j : Fin 5, i.val<j.val →
        RearTrace.predecessor (C i).root ∉ watch (C j)) ∧
      (∀ i j : Fin 5, i≠j → (C i).root≠(C j).root) := by
  have pts (i : Fin 5) :=
    ShortGateChart.chart_exists_gate x M (nextAt r (offset (header x) r i.val))
      (offset_at_header x M r R i.val) (by omega)
  let C := fun i : Fin 5 => Classical.choose (pts i)
  have Cspec (i : Fin 5) := Classical.choose_spec (pts i)
  refine ⟨C,fun i=>(Cspec i).1,fun i=>(Cspec i).2.1,fun i=>(Cspec i).2.2,?_,?_⟩
  · intro i j L
    have B := offset_bound (header x) r j.val
    have J := j.isLt
    have Lc : (C j).L≤9 := (Cspec j).2.1
    exact earlier_door_omitted (C i) (C j) r _ _ (Cspec i).1 (Cspec j).1
      (offset_monotone _ _ L) (by omega)
  · intro i j H eq
    have I := i.isLt
    have J := j.isLt
    have B := offset_bound (header x) r i.val
    have D := offset_bound (header x) r j.val
    have E : nextAt r (offset (header x) r i.val)=nextAt r (offset (header x) r j.val) :=
      ((Cspec i).1).symm.trans (eq.trans (Cspec j).1)
    have F := nextAt_injective_under r _ _ (by omega) (by omega) E
    rcases Nat.lt_trichotomy i.val j.val with lt|e|gt
    · have G := offset_monotone (header x) r lt
      omega
    · exact H (Fin.ext e)
    · have G := offset_monotone (header x) r gt
      omega

/-- Center the five-root order on a designated target. Start the
clockwise census at the target's second selected-H1 predecessor. -/
theorem offset_two_on_double_left {s n : Nat} {x : Raw s n} (M : rawMaximal x)
    (target : PhysicalH1Neighbors.Sites (header x)) :
    let start := PhysicalH1Neighbors.left M (PhysicalH1Neighbors.left M target)
    nextAt start.val (offset (header x) start.val 2)=target.val := by
  let left := PhysicalH1Neighbors.left M target
  let start := PhysicalH1Neighbors.left M left
  let d := PhysicalH1Neighbors.rightDist (header x) start.val
  have one : nextAt start.val d=left.val :=
    congrArg Subtype.val (PhysicalH1Neighbors.right_left M left)
  dsimp only [offset]
  simp only [Nat.zero_add, nextAt]
  change nextAt start.val (d + PhysicalH1Neighbors.rightDist (header x) (nextAt start.val d))=target.val
  rw [nextAt_add,one]
  exact congrArg Subtype.val (PhysicalH1Neighbors.right_left M target)

end L4.ShortSimultaneousOrder
