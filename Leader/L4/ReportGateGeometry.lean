import Leader.L4.ReportChartPartition

namespace L4.ReportGateGeometry
open ShortResetChart ShortLayerGeometry BStarH6Ordinal WidthOrdinalSpan ReportChartPartition

/-- An ADMIT gate has the incident labels with offsets 1 (incoming)
and 2 (outgoing) from the center word's header. -/
def label {n : Nat} (r : Fin n) (outgoing : Bool) : Fin n :=
  nextAt r (if outgoing then 2 else 1)

theorem label_incoming {n : Nat} (r : Fin n) :
    rightNeighbor (label r false)=label r true := rfl

theorem disjoint_center_incidence {n : Nat} {h : Fin n → Bool}
    (hh : ∃ r,h r=true) {r u : Fin n} {a b : Nat}
    (R : h r=true) (U : h u=true) (F : Gap h r a) (G : Gap h u b)
    (A : 2<a) (B : 2<b) {s t : Bool} (H : label r s=label u t) :
    r=u ∧ s=t := by
  let i := if s then 2 else 1
  let j := if t then 2 else 1
  change nextAt r i=nextAt u j at H
  have I : i<a := by cases s <;> simp [i] <;> omega
  have J : j<b := by cases t <;> simp [j] <;> omega
  have E : i=j := calc
    i = ordinal h hh (nextAt r i) := (ordinal_at_offset hh R F i I).symm
    _ = ordinal h hh (nextAt u j) := congrArg (ordinal h hh) H
    _ = j := ordinal_at_offset hh U G j J
  have S : s=t := by cases s <;> cases t <;> simp_all [i,j]
  have L := back_nextAt_add r 0 j
  have M := back_nextAt_add u 0 j
  rw [Nat.zero_add] at L M
  rw [E] at H
  rw [H,M] at L
  exact ⟨L.symm,S⟩

theorem chart_gate_incidence {n : Nat} {h : Fin n → Bool} {r : Fin n}
    {a b c : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (I : Gap h (nextAt (nextAt r a) b) c) (room : a+b+c<n) (s : Bool) :
    let C := chart_of_three R F G I room
    nextAt C.root (a+(if s then 2 else 1)) = label (nextAt r a) s := by
  change nextAt r (a+(if s then 2 else 1)) = label (nextAt r a) s
  rw [nextAt_add]
  rfl

end L4.ReportGateGeometry
