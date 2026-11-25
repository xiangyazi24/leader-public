import Leader.L4.ShortResetCycle

namespace L4.ShortGateChart
open AllSizeProtocol MISByteCodec PhysicalCustody PhysicalCustody.H1
open ShortResetChart ShortResetCycle ShortResetMIS1Ring ShortResetForwardH2

def slotGate {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) (i : Nat) : Bool :=
  atGate (header x (nextAt C.root i)) (x (nextAt C.root i)).mis1 (C.route.port i)

theorem chart_exists_gate {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (r : Fin n) (R : header x r=true) (N : 9<n) :
    ∃ C : Chart (header x), C.root=r ∧ C.L≤9 ∧
      ∃ g : Nat, 0<g ∧ g+1<C.L ∧
        ∀ (y : Raw s n), H2Ready y → (∀ q, header y q=header x q) →
          ∀ k, k<C.L → (slotGate C y k=true ↔ k=g) := by
  let A := M
  obtain ⟨a,b,c,Aa,Bb,Cc,H⟩ := three_gaps A r R
  have Ap : 0<a := by omega
  have Bp : 0<b := by omega
  have Cp : 0<c := by omega
  have L : a+b+c<n := by omega
  have fin : ShortResetChart.lane a b (a+b+c-1)=2 := by
    unfold ShortResetChart.lane
    rw [if_neg (by omega),if_neg (by omega)]
  refine ⟨⟨r,a,b,a+b+c,by omega,L,by simp [ShortResetChart.lane,Ap],R,?_⟩,
    rfl,by change a+b+c≤9; omega, a,Ap,by change a+1<a+b+c; omega,?_⟩
  · intro k K
    by_cases J : k+1<a+b+c
    · rw [if_pos J]
      change ShortResetRow.destination (AllSizeS1Geometry.header (x (nextAt r (k+1)))) (ShortResetChart.lane a b k)=some (ShortResetChart.lane a b (k+1))
      by_cases P : k+1=a
      · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inl P)
        have u : k<a := by omega
        have v : k+1<a+b := by omega
        have w : ¬ k+1<a := by omega
        simp [ShortResetRow.destination,T,ShortResetChart.lane,u,v,w]
      by_cases Q : k+1=a+b
      · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inr (Or.inl Q))
        have u : ¬ k<a := by omega
        have v : k<a+b := by omega
        have w : ¬ k+1<a := by omega
        have z : ¬ k+1<a+b := by omega
        simp [ShortResetRow.destination,T,ShortResetChart.lane,u,v,w,z]
      have T : AllSizeS1Geometry.header (x (nextAt r (k+1)))=false :=
        Bool.eq_false_iff.mpr (fun h => by have F := (H (k+1) (by omega) (by omega)).mp h; omega)
      have I : (k<a)=(k+1<a) := propext (by omega)
      have J : (k<a+b)=(k+1<a+b) := propext (by omega)
      simp [ShortResetRow.destination,T,ShortResetChart.lane]
      split <;> rename_i e
      · simp [←I,e]
      · simp [←I,e,←J]
    · rw [if_neg J]
      have rk : k=a+b+c-1 := by omega
      subst k
      have e : a+b+c-1+1=a+b+c := by omega
      change ShortResetRow.destination (AllSizeS1Geometry.header (x (nextAt r (a+b+c-1+1)))) (ShortResetChart.lane a b (a+b+c-1))=none
      rw [e,fin,(H _ (by omega) (by omega)).mpr (Or.inr (Or.inr rfl))]
      rfl
  · change ∀ (y : Raw s n), H2Ready y → (∀ q, header y q=header x q) →
        ∀ k, k<a+b+c → (atGate (header y (nextAt r k)) (y (nextAt r k)).mis1 (ShortResetChart.lane a b k)=true ↔ k=a)
    intro y Hy headers k K
    change (atGate (AllSizeS1Geometry.header (y (nextAt r k))) (y (nextAt r k)).mis1 (ShortResetChart.lane a b k)=true ↔ k=a)
    change ∀ q, AllSizeS1Geometry.header (y q)=AllSizeS1Geometry.header (x q) at headers
    rw [h2_ready_gate Hy,headers]
    constructor
    · intro U
      have p : ¬k<a := by intro J; simpa [ShortResetChart.lane,J] using U.1
      have q : k<a+b := by
        by_cases J : k<a+b
        · exact J
        · simpa [ShortResetChart.lane,p,J] using U.1
      have Z := (H k (by omega) (by omega)).mp U.2
      omega
    · intro U
      subst k
      have p : a<a+b := by omega
      exact ⟨by simp [ShortResetChart.lane,p],(H a (by omega) (by omega)).mpr (Or.inl rfl)⟩

#print axioms chart_exists_gate
end L4.ShortGateChart
