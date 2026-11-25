import Leader.L4.ShortReadCaptureGeometry
import Leader.L4.ShortGateChart

namespace L4.ShortPublishChart
open AllSizeProtocol PhysicalCustody ShortResetChart ShortResetCycle ShortResetMIS1Ring
open ShortReadCaptureGeometry ShortResetRow ShortGateChart

/-- STAGE4 and SEAL5 test the old grant at the unique outgoing header/K1
incidence. The next cell is a follower, so this crossing is K1 → K1. -/
theorem stage_seal_centre {s n : Nat} (x y : Raw s n) (X : H2Ready x) (Y : H2Ready y)
    (C : Chart (header x)) (N : 9<n) (frozen : ∀ i, header y i=header x i) :
    C.a+1<C.L ∧
    (∀ k, k<C.L → (header y (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a)) ∧
    (∀ k, k<C.L → (slotGate C y k=true ↔ k=C.a)) ∧
    header y (rightNeighbor (nextAt C.root C.a))=false ∧
    C.route.port (C.a+1)=1 ∧
    destination (header y (rightNeighbor (nextAt C.root C.a))) (C.route.port C.a) =
      some (C.route.port (C.a+1)) := by
  obtain ⟨A,B,L,H,zero,one,two,_,_⟩ := capture_chart_fields x X.1 C N
  have R : C.route.port C.a=1 := one
  have S : C.a+1<C.L := by omega
  have U : ∀ k, k<C.L →
      (header y (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a) := by
    intro k K
    rw [frozen, H k K]
    constructor
    · rintro ⟨rfl|rfl|rfl, P⟩
      · change lane C.a C.b 0=1 at P
        rw [zero] at P
        contradiction
      · rfl
      · change lane C.a C.b (C.a+C.b)=1 at P
        rw [two] at P
        contradiction
    · rintro rfl
      exact ⟨Or.inr (Or.inl rfl),R⟩
  have next : header y (rightNeighbor (nextAt C.root C.a))=false := by
    change header y (nextAt C.root (C.a+1))=false
    apply Bool.eq_false_iff.mpr
    intro P
    rw [frozen] at P
    have T := (H _ S).mp P
    omega
  have live := C.route.live C.a S
  rw [← frozen] at live
  refine ⟨S,U,?_,next,?_,live⟩
  · intro k K
    unfold slotGate
    change MISByteCodec.atGate (AllSizeS1Geometry.header (y (nextAt C.root k))) _ _ = true ↔ _
    rw [h2_ready_gate Y]
    constructor
    · intro ⟨P,Q⟩
      refine (U k K).mp ⟨Q,Fin.ext ?_⟩
      exact P
    · intro P
      obtain ⟨Q,T⟩ := (U k K).mpr P
      exact ⟨congrArg Fin.val T,Q⟩
  · change destination (header y (rightNeighbor (nextAt C.root C.a))) (C.route.port C.a) = _ at live
    rw [next, R] at live
    exact Option.some.inj live |>.symm

/-- COMMIT6 tests the destination header at the unique K0 → K1 crossing.
The preceding cell is a follower. -/
theorem commit_centre {s n : Nat} (x y : Raw s n) (X : H2Ready x)
    (C : Chart (header x)) (N : 9<n) (frozen : ∀ i, header y i=header x i) :
    C.a-1+1<C.L ∧
    header y (nextAt C.root (C.a-1))=false ∧
    (∀ k, k+1<C.L →
      (header y (rightNeighbor (nextAt C.root k))=true ∧ C.route.port k=0 ∧
        C.route.port (k+1)=1 ↔ k=C.a-1)) ∧
    destination (header y (rightNeighbor (nextAt C.root (C.a-1)))) (C.route.port (C.a-1)) =
      some (C.route.port C.a) := by
  obtain ⟨A,B,L,H,_,one,two,_,_⟩ := capture_chart_fields x X.1 C N
  have E : C.a-1+1=C.a := by omega
  have S : C.a-1+1<C.L := by omega
  have F : header y (nextAt C.root (C.a-1))=false := by
    apply Bool.eq_false_iff.mpr
    intro P
    rw [frozen] at P
    have T := (H (C.a-1) (by omega)).mp P
    omega
  have R : C.route.port (C.a-1)=0 := by
    change lane C.a C.b (C.a-1)=0
    simp [lane, show C.a-1<C.a by omega]
  have live := C.route.live (C.a-1) S
  rw [← frozen, E] at live
  refine ⟨S,F,?_,live⟩
  intro k K
  change (header y (nextAt C.root (k+1))=true ∧
    C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ _)
  rw [frozen, H _ K]
  constructor
  · rintro ⟨G,_,P⟩
    rcases G with G|G|G
    · omega
    · omega
    · rw [G] at P
      change lane C.a C.b (C.a+C.b)=1 at P
      rw [two] at P
      contradiction
  · rintro rfl
    rw [E]
    exact ⟨Or.inr (Or.inl rfl),R,one⟩

/-- The exact old pair at the COMMIT ingress, ready for the local row
lemma without a separate arithmetic or layout rewrite. -/
theorem commit_centre_pair {s n : Nat} (x y : Raw s n) (X : H2Ready x)
    (C : Chart (header x)) (N : 9<n) (frozen : ∀ i, header y i=header x i) :
    C.a-1+1=C.a ∧ C.a<C.L ∧ C.route.port (C.a-1)=0 ∧ C.route.port C.a=1 ∧
      header y (nextAt C.root (C.a-1))=false ∧
      header y (rightNeighbor (nextAt C.root (C.a-1)))=true := by
  obtain ⟨A,_,L,_,_,_,_,_,_⟩ := capture_chart_fields x X.1 C N
  obtain ⟨S,F,U,_⟩ := commit_centre x y X C N frozen
  have E : C.a-1+1=C.a := by omega
  obtain ⟨H,K0,K1⟩ := (U _ S).mpr rfl
  rw [E] at K1
  exact ⟨E,by omega,K0,K1,F,H⟩

end L4.ShortPublishChart
