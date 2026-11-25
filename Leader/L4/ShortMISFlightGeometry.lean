import Leader.L4.ShortMISLift
import Leader.L4.ShortWriteFlight
import Leader.L4.ShortCommitFlight

namespace L4.ShortMISFlightGeometry
open AllSizeProtocol PhysicalCustody ShortMISEngine ShortMISLift
open ShortResetChart ShortResetCycle ShortLayerGeometry

variable {s n : Nat}

theorem coordinates (G : Geometry s n) (C : Chart G.P.h) :
    ∃ a b c : Nat, G.A≤a ∧ G.A≤b ∧ G.A≤c ∧ C.a=a ∧ C.b=b ∧ C.L=a+b+c ∧
      (∀ k, k<C.L → (G.P.h (nextAt C.root k)=true ↔ k=0 ∨ k=a ∨ k=a+b)) := by
  obtain ⟨a,aa,aB,F⟩ := G.gaps C.root C.rootHeader
  obtain ⟨b,bb,bB,H⟩ := G.gaps (nextAt C.root a) F.atEnd
  obtain ⟨c,cc,cB,J⟩ := G.gaps (nextAt (nextAt C.root a) b) H.atEnd
  have ap := F.positive
  have bp := H.positive
  have cp := J.positive
  have room := G.seven
  let D : Chart G.P.h := chart_of_three C.rootHeader F H J (by omega)
  have U := ShortReadCaptureGeometry.chart_unique C D rfl
  have len : C.L=a+b+c := U.1
  have ports (k : Nat) (K : k<C.L) : lane C.a C.b k=lane a b k := U.2 k K
  have Z (k : Nat) (K : k<C.L) :
      G.P.h (nextAt C.root k)=true ↔ k=0 ∨ k=a ∨ k=a+b := by
    by_cases k0 : k=0
    · subst k
      simp; exact C.rootHeader
    · have W := three_gap_exact F H J k (by omega) (by omega)
      rw [W]
      omega
  have p0 := ports (a-1) (by omega)
  have p1 := ports a (by omega)
  have q0 := ports (a+b-1) (by omega)
  have q1 := ports (a+b) (by omega)
  have lane0 (r t k : Nat) : lane r t k=0 ↔ k<r := by
    unfold lane
    by_cases I : k<r
    · simp [I]
    · by_cases T : k<r+t <;> simp [I,T]
  have lane2 (r t k : Nat) : lane r t k=2 ↔ r+t≤k := by
    unfold lane
    by_cases I : k<r
    · simp [I]; omega
    · by_cases T : k<r+t
      · simp [I,T]
      · simp [I,T]; omega
  have A0 : a-1<C.a := (lane0 _ _ _).mp (p0.trans ((lane0 _ _ _).mpr (by omega)))
  have A1 : ¬ a<C.a := by
    intro F'
    exact (Nat.lt_irrefl a) ((lane0 _ _ _).mp (p1.symm.trans ((lane0 _ _ _).mpr F')))
  have B0 : ¬ C.a+C.b≤a+b-1 := by
    intro F'
    have L := (lane2 _ _ _).mp (q0.symm.trans ((lane2 _ _ _).mpr F'))
    omega
  have B1 : C.a+C.b≤a+b := (lane2 _ _ _).mp (q1.trans ((lane2 _ _ _).mpr (by omega)))
  exact ⟨a,b,c,aa,bb,cc,by omega,by omega,len,Z⟩

theorem flight_geometry (G : Geometry s n) (C : Chart G.P.h)
    (minGap : 2≤G.A)
    (x : Raw s n) (heads : ∀ q, ShortResetMIS1Ring.header x q=G.P.h q) :
    (C.a+1<C.L ∧ ∀ k, k<C.L →
      (ShortResetMIS1Ring.header x (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a)) ∧
    (C.a-1+1<C.L ∧ ∀ k, k+1<C.L →
      (ShortResetMIS1Ring.header x (rightNeighbor (nextAt C.root k))=true ∧
        C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1)) ∧
    ShortResetMIS1Ring.header x (nextAt C.root (C.a-1))=false ∧
    ShortResetMIS1Ring.header x (rightNeighbor (nextAt C.root C.a))=false := by
  obtain ⟨a,b,c,aa,bb,cc,ca,cb,L,H⟩ := coordinates G C
  have W (k : Nat) (K : k<C.L) :
      ShortResetMIS1Ring.header x (nextAt C.root k)=true ↔ k=0 ∨ k=a ∨ k=a+b := by
    rw [heads]
    exact H k K
  refine ⟨⟨by omega,?_⟩,⟨by omega,?_⟩,?_,?_⟩
  · intro k K
    rw [W k K]
    change ((k=0 ∨ k=a ∨ k=a+b) ∧ lane C.a C.b k=1 ↔ k=C.a)
    rw [ca,cb]
    constructor
    · rintro ⟨rfl|rfl|rfl,P⟩
      · simp [lane,show 0<a by omega] at P
      · rfl
      · simp [lane,show ¬a+b<a by omega] at P
    · rintro rfl
      exact ⟨.inr (.inl rfl),by simp [lane,show k<k+b by omega]⟩
  · intro k K
    change (ShortResetMIS1Ring.header x (nextAt C.root (k+1))=true ∧
      lane C.a C.b k=0 ∧ lane C.a C.b (k+1)=1 ↔ k=C.a-1)
    rw [W _ K,ca,cb]
    constructor
    · rintro ⟨I,_,P⟩
      rcases I with I|I|I
      · omega
      · omega
      · rw [I] at P
        simp [lane,show ¬a+b<a by omega] at P
    · intro J
      have A : k+1=a := by omega
      exact ⟨.inr (.inl A),by simp [lane,show k<a by omega],
        by rw [A]; simp [lane,show a<a+b by omega]⟩
  · apply Bool.eq_false_iff.mpr
    intro J
    have K := (W _ (by omega)).mp J
    omega
  · apply Bool.eq_false_iff.mpr
    intro J
    change ShortResetMIS1Ring.header x (nextAt C.root (C.a+1))=true at J
    have K := (W _ (by omega)).mp J
    omega

end L4.ShortMISFlightGeometry
