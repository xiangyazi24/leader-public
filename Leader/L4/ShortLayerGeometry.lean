import Leader.L4.ShortResetCycle

namespace L4.ShortLayerGeometry
open AllSizeProtocol ShortResetChart ShortResetCycle ShortResetRow

/-- A successor in a frozen header mask, measured in physical sites.
Marks continue to use physical edges, not the compressed subring. -/
structure Gap {n : Nat} (h : Fin n → Bool) (r : Fin n) (d : Nat) : Prop where
  positive : 0<d
  atEnd : h (nextAt r d)=true
  interior : ∀ k, 0<k → k<d → h (nextAt r k)=false

theorem gap_to_submask {n : Nat} {h sel : Fin n → Bool} {r : Fin n} {d : Nat}
    (subset : ∀ q, sel q=true → h q=true)
    (F : Gap h r d) (H : sel (nextAt r d)=true) : Gap sel r d := by
  refine ⟨F.positive,H,?_⟩
  intro k K L
  apply Bool.eq_false_iff.mpr
  intro S
  have P := subset _ S
  rw [F.interior k K L] at P
  contradiction

/-- Skip a rejected old header without altering the physical distance. -/
theorem join_rejected {n : Nat} {h sel : Fin n → Bool} {r : Fin n} {a b : Nat}
    (subset : ∀ q, sel q=true → h q=true)
    (F : Gap h r a) (H : sel (nextAt r a)=false)
    (G : Gap sel (nextAt r a) b) : Gap sel r (a+b) := by
  refine ⟨by have := F.positive; omega,by rw [nextAt_add]; exact G.atEnd,?_⟩
  intro k K L
  by_cases u : k<a
  · apply Bool.eq_false_iff.mpr
    intro B
    have X := subset _ B
    rw [F.interior k K u] at X
    contradiction
  · by_cases v : k=a
    · simpa only [v] using H
    · have A : k=a+(k-a) := by omega
      rw [show nextAt r k=nextAt (nextAt r a) (k-a) by rw [←nextAt_add,←A]]
      exact G.interior (k-a) (by omega) (by omega)

/-- The two-step outcome of a maximal independent selection on the
previous header subring. The paper must separately establish that this
is the selected mask and that it stays selected. -/
theorem select_after_two {n : Nat} {h sel : Fin n → Bool} {r : Fin n} {a b B : Nat}
    (subset : ∀ q, sel q=true → h q=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (A : a≤B) (D : b≤B)
    (skip : sel (nextAt r a)=false)
    (keep : sel (nextAt (nextAt r a) b)=true) :
    Gap sel r (a+b) ∧ a+b≤3*B :=
  ⟨join_rejected subset F skip (gap_to_submask subset G keep),by omega⟩

theorem select_after_three {n : Nat} {h sel : Fin n → Bool} {r : Fin n} {a b c B : Nat}
    (subset : ∀ q, sel q=true → h q=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (H : Gap h (nextAt (nextAt r a) b) c)
    (A : a≤B) (D : b≤B) (E : c≤B)
    (skipA : sel (nextAt r a)=false)
    (skipB : sel (nextAt (nextAt r a) b)=false)
    (keep : sel (nextAt (nextAt (nextAt r a) b) c)=true) :
    Gap sel r (a+b+c) ∧ a+b+c≤3*B := by
  rw [Nat.add_assoc]
  exact ⟨join_rejected subset F skipA
    (join_rejected subset G skipB (gap_to_submask subset H keep)),by omega⟩

theorem three_gap_exact {n : Nat} {h : Fin n → Bool} {r : Fin n} {a b c : Nat}
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (H : Gap h (nextAt (nextAt r a) b) c) :
    ∀ k, 0<k → k≤a+b+c → (h (nextAt r k)=true ↔ k=a ∨ k=a+b ∨ k=a+b+c) := by
  have A := F.positive
  have B := G.positive
  have C := H.positive
  intro k K L
  by_cases ka : k<a
  · rw [F.interior k K ka]
    simp only [Bool.false_eq_true, false_iff]
    omega
  by_cases ea : k=a
  · subst k
    simp [F.atEnd]
  by_cases kb : k<a+b
  · have kx : k=a+(k-a) := by omega
    rw [show nextAt r k=nextAt (nextAt r a) (k-a) by rw [←nextAt_add,←kx]]
    rw [G.interior (k-a) (by omega) (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega
  by_cases eb : k=a+b
  · subst k
    rw [nextAt_add]
    simp [G.atEnd]
  by_cases kc : k<a+b+c
  · have kx : k=a+b+(k-(a+b)) := by omega
    rw [show nextAt r k=nextAt (nextAt (nextAt r a) b) (k-(a+b)) by
      rw [←nextAt_add,←nextAt_add,←Nat.add_assoc,←kx]]
    rw [H.interior (k-(a+b)) (by omega) (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega
  · have h : k=a+b+c := by omega
    subst k
    rw [nextAt_add,nextAt_add]
    simp [H.atEnd]

/-- Build the same routing chart from any three consecutive incidences
of the frozen mask. No MIS1-specific gap length or compressed clock. -/
def chart_of_three {n : Nat} {h : Fin n → Bool} {r : Fin n} {a b c : Nat}
    (root : h r=true) (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (I : Gap h (nextAt (nextAt r a) b) c) (fits : a+b+c<n) : Chart h := by
  have A := F.positive
  have B := G.positive
  have C := I.positive
  have H := three_gap_exact F G I
  have fin : lane a b (a+b+c-1)=2 := by
    unfold lane
    rw [if_neg (by omega),if_neg (by omega)]
  refine ⟨r,a,b,a+b+c,by omega,fits,by simp [lane,A],root,?_⟩
  intro i Q
  by_cases J : i+1<a+b+c
  · rw [if_pos J]
    suffices ∀ k, k+1<a+b+c →
      destination (h (rightNeighbor (nextAt r k))) (lane a b k)=some (lane a b (k+1)) by
      exact this i J
    intro k K
    change ShortResetRow.destination (h (nextAt r (k+1))) (lane a b k)=some (lane a b (k+1))
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
    have T : h (nextAt r (k+1))=false :=
      Bool.eq_false_iff.mpr (fun h => by have F := (H (k+1) (by omega) (by omega)).mp h; omega)
    have I : (k<a)=(k+1<a) := propext (by omega)
    have J : (k<a+b)=(k+1<a+b) := propext (by omega)
    simp [ShortResetRow.destination,T,lane]
    split <;> rename_i e
    · simp [←I,e]
    · simp [←I,e,←J]
  · rw [if_neg J]
    have p : i=a+b+c-1 := by omega
    subst i
    have e : a+b+c-1+1=a+b+c := by omega
    change destination (h (nextAt r (a+b+c-1+1))) (lane a b (a+b+c-1))=none
    rw [e,fin,(H _ (by omega) (by omega)).mpr (Or.inr (Or.inr rfl))]
    rfl

/-- The one theorem used for all sheets once the corresponding lower
selector supplies a successor law. The positional cap is independent
of the number of physical marks or storage width. -/
theorem chart_of_successor_law {n B : Nat} {h : Fin n → Bool}
    (N : 3*B<n)
    (next : ∀ r, h r=true → ∃ d≤B, Gap h r d)
    (r : Fin n) (root : h r=true) :
    ∃ C : Chart h, C.root=r ∧ C.L≤3*B := by
  obtain ⟨a,A,F⟩ := next r root
  obtain ⟨b,Bb,G⟩ := next (nextAt r a) F.atEnd
  obtain ⟨c,Cc,H⟩ := next (nextAt (nextAt r a) b) G.atEnd
  exact ⟨chart_of_three root F G H (by omega),rfl,by
    change a+b+c≤3*B
    omega⟩

/-- MIS1 is the first instance: H1-gaps 2/3 are already checked.
Higher-sheet instances must use the previous header subring instead. -/
theorem mis1_chart {s n : Nat} (x : PhysicalCustody.Raw s n)
    (M : PhysicalCustody.H1.rawMaximal x) (N : 9<n) (r : Fin n)
    (R : ShortResetMIS1Ring.header x r=true) :
    ∃ C : Chart (ShortResetMIS1Ring.header x), C.root=r ∧ C.L≤9 := by
  apply chart_of_successor_law (B:=3) N _ r R
  intro u U
  obtain ⟨d,P,E,I⟩ := ShortResetChart.gap M u U
  exact ⟨d,by omega,by exact ⟨by omega,E,I⟩⟩

end L4.ShortLayerGeometry
