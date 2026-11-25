import Leader.L4.ReportStaticSpacing
import Leader.L4.ShortNORCover

namespace L4.SelectedRingGeometry
open AllSizeProtocol BStarH6Ordinal ShortResetChart ShortLayerGeometry
open ShortHopSpacing ReportStaticSpacing WidthOrdinalSpan

/-- The actual selected predecessor is the root of the word ending
immediately before this header; the modular ordinal handles wrap. -/
noncomputable def predecessor {n : Nat} {h : Fin n→Bool}
    (hh : ∃ i,h i=true) (i : Lower h) : Lower h :=
  let u := RearTrace.predecessor i.val
  let H : h (rightNeighbor u)=true :=
    (RearTrace.right_predecessor i.val).symm ▸ i.property
  ⟨back u (ordinal h hh u),(last_gap h hh u H).1⟩

theorem successor_predecessor {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (i : Lower h) :
    successor G (predecessor hh i) = i := by
  let u := RearTrace.predecessor i.val
  let d := ordinal h hh u
  have H : h (rightNeighbor u)=true :=
    (RearTrace.right_predecessor i.val).symm ▸ i.property
  have F := (last_gap h hh u H).2
  have E := gap_unique (successorWidth_spec G (predecessor hh i).val
    (predecessor hh i).property).2.2 F
  apply Subtype.ext
  change nextAt (back u d) (successorWidth G (predecessor hh i).val)=i.val
  rw [E]
  change rightNeighbor (nextAt (back u d) d)=i.val
  rw [nextAt_back]
  exact RearTrace.right_predecessor i.val

private theorem back_end {n : Nat} (q : Fin n) (d : Nat) :
    back (nextAt q d) d=q := by
  have E := back_nextAt_add q 0 d
  rw [Nat.zero_add] at E
  exact E.trans rfl

private theorem backward_interior {n : Nat} {h : Fin n→Bool} {q : Fin n} {d : Nat}
    (F : Gap h q d) {a : Nat} (P : 0<a) (A : a<d) :
    h (back (nextAt q d) a)=false := by
  have E := back_nextAt_add q (d-a) a
  rw [show d-a+a=d by omega] at E
  rw [E]
  exact F.interior _ (by omega) (by omega)

/-- Two forward gaps with the same selected endpoint have the same
selected start, including gaps crossing the ring seam. -/
theorem gap_source_unique {n : Nat} {h : Fin n→Bool} {q r : Fin n} {a b : Nat}
    (Q : h q=true) (R : h r=true) (F : Gap h q a) (G : Gap h r b)
    (E : nextAt q a=nextAt r b) : q=r := by
  have A := F.positive
  have B := G.positive
  have D : a=b := by
    rcases Nat.lt_trichotomy a b with X|X|X
    · have Y := backward_interior G A X
      rw [←E,back_end,Q] at Y
      contradiction
    · exact X
    · have Y := backward_interior F B X
      rw [E,back_end,R] at Y
      contradiction
  have P := congrArg (fun x=>back x a) E
  simpa only [back_end,D] using P

theorem successor_injective {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) {i j : Lower h} (E : successor G i=successor G j) : i=j := by
  apply Subtype.ext
  exact gap_source_unique i.property j.property (successorWidth_spec G i.val i.property).2.2
    (successorWidth_spec G j.val j.property).2.2 (congrArg Subtype.val E)

theorem predecessor_successor {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (i : Lower h) :
    predecessor hh (successor G i)=i :=
  successor_injective G (successor_predecessor G hh (successor G i))

private theorem cycle {n : Nat} (i : Fin n) : nextAt i n=i := by
  apply Fin.ext
  rw [nextAt_val,Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]

private theorem reaches_other {n : Nat} {i j : Fin n} (D : i≠j) :
    ∃ k, 0<k ∧ k<n ∧ nextAt i k=j := by
  obtain ⟨a,A,E⟩ := back_hits j i
  have P : 0<a := by
    by_cases T : a=0
    · rw [T,back_zero] at E
      exact False.elim (D E.symm)
    · omega
  refine ⟨a,P,A,?_⟩
  rw [←E,nextAt_back]

/-- The exact premise for noLoop is a second selected node. A mask
with a unique selected node still has mutual inverses but cannot
provide the noLoop field of ShortNORCover.Ring. -/
theorem successor_noLoop {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (i : Lower h) (other : ∃ j : Lower h, j≠i) :
    successor G i ≠ i := by
  obtain ⟨j,J⟩ := other
  have D : i.val≠j.val := fun E=>J (Subtype.ext E.symm)
  obtain ⟨k,K,N,E⟩ := reaches_other D
  let a := successorWidth G i.val
  have F : Gap h i.val a := (successorWidth_spec G i.val i.property).2.2
  have upper : a≤k := by
    by_cases T : k<a
    · have bad := F.interior k K T
      rw [E,j.property] at bad
      contradiction
    · omega
  intro O
  have P : nextAt i.val a=nextAt i.val 0 := congrArg Subtype.val O
  have Z := nextAt_injective_under i.val a 0 (by omega) (by omega) P
  have pos := F.positive
  omega

theorem successor_noLoop_of_upper {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (room : U<n) (i : Lower h) : successor G i≠i := by
  let a := successorWidth G i.val
  obtain ⟨_,U,F⟩ := successorWidth_spec G i.val i.property
  intro E
  have V : nextAt i.val a=nextAt i.val 0 := congrArg Subtype.val E
  have Z := nextAt_injective_under i.val a 0 (by exact Nat.lt_of_le_of_lt U room)
    (Nat.zero_lt_of_lt room) V
  exact Nat.ne_of_gt F.positive Z

noncomputable def ring {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (room : U<n) :
    ShortNORCover.Ring (Lower h) where
  left := predecessor hh
  right := successor G
  lr := predecessor_successor G hh
  rl := successor_predecessor G hh
  noLoop := successor_noLoop_of_upper G room

theorem singleton_wrap {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (i : Lower h) (one : ∀ j : Lower h, j=i) :
    successor G i=i ∧ successorWidth G i.val=n := by
  have O := one (successor G i)
  refine ⟨O,gap_unique (successorWidth_spec G i.val i.property).2.2 ⟨?_,?_,?_⟩⟩
  · exact Nat.zero_lt_of_lt i.val.isLt
  · rw [cycle]
    exact i.property
  · intro k K N
    apply Bool.eq_false_iff.mpr
    intro H
    have J := congrArg Subtype.val (one ⟨nextAt i.val k,H⟩)
    change nextAt i.val k=nextAt i.val 0 at J
    have Z := nextAt_injective_under i.val k 0 N (Nat.zero_lt_of_lt N) J
    omega

#print axioms successor_predecessor
#print axioms gap_source_unique
#print axioms successor_injective
#print axioms predecessor_successor
#print axioms successor_noLoop
#print axioms successor_noLoop_of_upper
#print axioms ring
#print axioms singleton_wrap
end L4.SelectedRingGeometry
