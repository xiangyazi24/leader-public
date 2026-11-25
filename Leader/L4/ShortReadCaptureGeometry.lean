import Leader.L4.ShortResetCycle

namespace L4.ShortReadCaptureGeometry
open AllSizeProtocol PhysicalCustody ShortResetChart ShortResetCycle ShortResetMIS1Ring

/-- Two charts of a common owner on the same layout traverse the same
lanes and stop at the same cell. -/
theorem chart_unique {n : Nat} {h : Fin n → Bool} (C D : Chart h)
    (R : C.root = D.root) :
    C.L = D.L ∧ ∀ k, k < C.L → lane C.a C.b k = lane D.a D.b k := by
  have agree : ∀ k, k < C.L → k < D.L → lane C.a C.b k = lane D.a D.b k := by
    intro k
    induction k with
    | zero => intro _ _; exact C.rootPort.trans D.rootPort.symm
    | succ k ih =>
      intro I J
      have HC := C.dst k (by omega)
      have HD := D.dst k (by omega)
      rw [if_pos I, R, ih (by omega) (by omega)] at HC
      rw [if_pos J] at HD
      exact Option.some.inj (HC.symm.trans HD)
  have aux (C D : Chart h) (R : C.root = D.root)
      (A : ∀ k, k < C.L → k < D.L → lane C.a C.b k = lane D.a D.b k) :
      ¬ C.L < D.L := by
    intro B
    have P := C.positive
    have E : C.L - 1 + 1 = C.L := by omega
    have HC := C.dst (C.L - 1) (by omega)
    have HD := D.dst (C.L - 1) (by omega)
    rw [if_neg (by omega), R, A _ (by omega) (by omega)] at HC
    rw [if_pos (by omega)] at HD
    cases HC.symm.trans HD
  have E : C.L = D.L := by
    have A := aux C D R agree
    have B := aux D C R.symm (fun k J I => (agree k I J).symm)
    omega
  exact ⟨E, fun k I => agree k I (E ▸ I)⟩

private theorem destination_of_gaps {s n : Nat} {x : Raw s n} (r : Fin n) (N : 9<n)
    (a b c : Nat) (Aa : a=2 ∨ a=3) (Bb : b=2 ∨ b=3) (Cc : c=2 ∨ c=3)
    (H : ∀ k : Nat, 0<k → k≤a+b+c → (AllSizeS1Geometry.header (x (nextAt r k))=true ↔ k=a ∨ k=a+b ∨ k=a+b+c)) :
        lane a b 0=0 ∧ lane a b (a+b+c-1)=2 ∧
      (∀ k : Nat, k+1<a+b+c →
        ShortResetRow.destination (AllSizeS1Geometry.header (x (rightNeighbor (nextAt r k)))) (lane a b k)
          =some (lane a b (k+1))) ∧
      ShortResetRow.destination (AllSizeS1Geometry.header (x (rightNeighbor (nextAt r (a+b+c-1)))))
        (lane a b (a+b+c-1))=none ∧
      ∀ i j : Nat, i≤a+b+c → j≤a+b+c → nextAt r i=nextAt r j → i=j := by
  have Ap : 0<a := by omega
  have Bp : 0<b := by omega
  have Cp : 0<c := by omega
  have L : a+b+c<n := by omega
  have fin : lane a b (a+b+c-1)=2 := by
    unfold lane
    rw [if_neg (by omega),if_neg (by omega)]
  refine ⟨by simp [lane,Ap],fin,?_,?_,?_⟩
  · intro k K
    change ShortResetRow.destination (AllSizeS1Geometry.header (x (nextAt r (k+1)))) (lane a b k)=some (lane a b (k+1))
    by_cases P : k+1=a
    · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inl P)
      have u : k<a := by omega
      have v : k+1<a+b := by omega
      have w : ¬ k+1<a := by omega
      simp [ShortResetRow.destination,T,lane,u,v,w]
    by_cases Q : k+1=a+b
    · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inr (Or.inl Q))
      have u : ¬ k<a := by omega
      have v : k<a+b := by omega
      have w : ¬ k+1<a := by omega
      have z : ¬ k+1<a+b := by omega
      simp [ShortResetRow.destination,T,lane,u,v,w,z]
    have T : AllSizeS1Geometry.header (x (nextAt r (k+1)))=false :=
      Bool.eq_false_iff.mpr (fun h => by have F := (H (k+1) (by omega) (by omega)).mp h; omega)
    have I : (k<a)=(k+1<a) := propext (by omega)
    have J : (k<a+b)=(k+1<a+b) := propext (by omega)
    simp [ShortResetRow.destination,T,lane]
    split <;> rename_i e
    · simp [←I,e]
    · simp [←I,e,←J]
  · have e : a+b+c-1+1=a+b+c := by omega
    change ShortResetRow.destination (AllSizeS1Geometry.header (x (nextAt r (a+b+c-1+1)))) (lane a b (a+b+c-1))=none
    rw [e,fin,(H _ (by omega) (by omega)).mpr (Or.inr (Or.inr rfl))]
    rfl
  · intro i j I J E
    exact nextAt_injective_under r i j (by omega) (by omega) E

/-- Exact H1 departure indices for an arbitrary chart of a frozen maximal
layout. The turn endpoint is an H1, but is outside the departure interval;
the last forward departure itself is not an H1. -/
theorem capture_indices {s n : Nat} (x : Raw s n) (M : H1.rawMaximal x)
    (C : Chart (header x)) (N : 9 < n) :
    ∃ a b c : Nat, (a=2 ∨ a=3) ∧ (b=2 ∨ b=3) ∧ (c=2 ∨ c=3) ∧
      C.L = a+b+c ∧ a+b<C.L ∧
      (∀ k, k<C.L → (header x (nextAt C.root k)=true ↔ k=0 ∨ k=a ∨ k=a+b)) ∧
      lane C.a C.b 0=0 ∧ lane C.a C.b a=1 ∧ lane C.a C.b (a+b)=2 ∧
      header x (nextAt C.root (C.L-1))=false ∧
      header x (nextAt C.root C.L)=true := by
  obtain ⟨a,b,c,A,B,F,geom⟩ := three_gaps M C.root C.rootHeader
  obtain ⟨Z,_,live,turn,_⟩ := destination_of_gaps C.root N a b c A B F geom
  let D : Chart (header x) :=
    ⟨C.root,a,b,a+b+c,by omega,by omega,Z,C.rootHeader,by
      intro k K
      split
      · exact live k (by assumption)
      · have E : k=a+b+c-1 := by omega
        subst k
        exact turn⟩
  obtain ⟨len,lanes⟩ := chart_unique C D rfl
  change C.L = a+b+c at len
  refine ⟨a,b,c,A,B,F,len,by omega,?_,C.rootPort,?_,?_,?_,?_⟩
  · intro k K
    by_cases Q : k=0
    · subst k
      simpa [nextAt] using C.rootHeader
    · have G := geom k (by omega) (by omega)
      change (header x (nextAt C.root k)=true ↔ _) at G
      rw [G]
      omega
  · have E := lanes a (by omega)
    change lane C.a C.b a = lane a b a at E
    simpa [lane, show a<a+b by omega] using E
  · have E := lanes (a+b) (by omega)
    change lane C.a C.b (a+b) = lane a b (a+b) at E
    simpa [lane, show ¬a+b<a by omega] using E
  · apply Bool.eq_false_iff.mpr
    intro H
    have G := (geom (C.L-1) (by omega) (by omega)).mp H
    omega
  · exact (geom C.L (by omega) (by omega)).mpr (Or.inr (Or.inr len))

/-- Chart fields are the actual first two distances as well as lane cutoffs.
This version uses the original chart offsets directly. -/
theorem capture_chart_fields {s n : Nat} (x : Raw s n) (M : H1.rawMaximal x)
    (C : Chart (header x)) (N : 9 < n) :
    (C.a=2 ∨ C.a=3) ∧ (C.b=2 ∨ C.b=3) ∧ C.a+C.b<C.L ∧
      (∀ k, k<C.L → (header x (nextAt C.root k)=true ↔
        k=0 ∨ k=C.a ∨ k=C.a+C.b)) ∧
      lane C.a C.b 0=0 ∧ lane C.a C.b C.a=1 ∧ lane C.a C.b (C.a+C.b)=2 ∧
      header x (nextAt C.root (C.L-1))=false ∧
      header x (nextAt C.root C.L)=true := by
  obtain ⟨a,b,c,A,B,F,len,_,geom,zero,one,two,last,turn⟩ := capture_indices x M C N
  have aex : C.a=a := by
    have p : ¬a<C.a := by
      intro P
      simp [lane,P] at one
    by_cases Q : C.a=a
    · exact Q
    have W : C.a<a := by omega
    have P : 0<C.a := by
      by_cases H : 0<C.a
      · exact H
      simp [lane, H] at zero
      split at zero <;> contradiction
    have H := C.dst (C.a-1) (by omega)
    have h : header x (nextAt C.root C.a)=false := by
      apply Bool.eq_false_iff.mpr
      intro U
      have V := (geom C.a (by omega)).mp U
      omega
    have E : C.a-1+1=C.a := by omega
    change ShortResetRow.destination (header x (nextAt C.root (C.a-1+1)))
      (lane C.a C.b (C.a-1)) = _ at H
    rw [E,if_pos (by omega),h] at H
    simp [ShortResetRow.destination,lane,show C.a-1<C.a by omega] at H
    split at H <;> contradiction
  have bex : C.b=b := by
    have A1 : a<C.a+C.b := by
      by_cases H : a<C.a+C.b
      · exact H
      have H' : ¬a<a+C.b := by omega
      simp [lane, aex, H'] at one
    have p : ¬a+b<C.a+C.b := by
      intro P
      simp [lane,show ¬a+b<C.a by omega,P] at two
    by_cases Q : C.b=b
    · exact Q
    have W : C.a+C.b<a+b := by omega
    have H := C.dst (C.a+C.b-1) (by omega)
    have h : header x (nextAt C.root (C.a+C.b))=false := by
      apply Bool.eq_false_iff.mpr
      intro U
      have V := (geom (C.a+C.b) (by omega)).mp U
      omega
    have E : C.a+C.b-1+1=C.a+C.b := by omega
    change ShortResetRow.destination (header x (nextAt C.root (C.a+C.b-1+1)))
      (lane C.a C.b (C.a+C.b-1)) = _ at H
    rw [E,if_pos (by omega),h] at H
    simp [ShortResetRow.destination,lane,show ¬C.a+C.b-1<C.a by omega,
      show C.a+C.b-1<C.a+C.b by omega,show ¬C.a+C.b<C.a by omega] at H
  refine ⟨?_,?_,by omega,?_,zero,?_,?_,last,turn⟩
  · simpa only [aex] using A
  · simpa only [bex] using B
  · simpa only [aex,bex] using geom
  · simpa only [aex] using one
  · simpa only [aex,bex] using two

#print axioms chart_unique
#print axioms capture_indices
#print axioms capture_chart_fields
end L4.ShortReadCaptureGeometry
