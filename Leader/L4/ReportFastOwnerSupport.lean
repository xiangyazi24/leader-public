import Leader.L4.ReportWriteRailSupplier
import Leader.L4.ReportGateGeometry
import Leader.L4.ReportGatePairs

namespace L4.ReportFastOwnerSupport
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportPrelaunchClock ReportByteRows
open ReportGoodEightBank ReportGoodEightCut ReportPrelaunchAllOwners
open ReportAdaptiveFibre ReportGateGeometry

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem serial_from_bank (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : GoodEightBank d hh Q G x) (C : Chart h) (M : C∈ownerCharts G) :
    StrongSerial d C x := by
  obtain ⟨a,flight,post,B,R,_,E⟩ := second_owner_seed d N hh G F digit x A.1 C M
  have X : Cached d hh Q a := B.1.1.1
  have S := seed_receipt d C N hh F a X flight R
  have Y := cached_run d N hh F a X flight
  rw [E]
  exact (strong_run d C N hh G F digit _ Y S post).2.1
private theorem front_tag_iff (k i : Nat) : frontTag k i=2 ↔ i=k := by
  unfold frontTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_tag_iff (k i : Nat) : backTag k i=3 ↔ i=k := by
  unfold backTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_not_front (k i : Nat) : backTag k i≠2 := by
  unfold backTag
  by_cases A : i<k <;> by_cases B : i=k <;> simp [A,B]

private theorem fwd_unique (d : Sheet) (C : Chart h) (x : Raw s n)
    {i j : Nat} (A : ForwardWait d C x i) (B : ForwardWait d C x j) : i=j := by
  have E := A.2.2 i A.2.1
  have F0 := B.2.2 i A.2.1
  rw [(front_tag_iff i i).mpr rfl] at E
  exact (front_tag_iff j i).mp (F0.symm.trans E)

private theorem rev_unique (d : Sheet) (C : Chart h) (x : Raw s n)
    {i j : Nat} (A : ReverseWait d C x i) (B : ReverseWait d C x j) : i=j := by
  have E := A.2.2 i A.2.1
  have F0 := B.2.2 i A.2.1
  rw [(back_tag_iff i i).mpr rfl] at E
  exact (back_tag_iff j i).mp (F0.symm.trans E)

private theorem issue_not_fwd (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : LegalIssue d C x) {i : Nat} (B : ForwardWait d C x i) : False := by
  have E := A.2.1
  have D := B.1.1
  omega

private theorem issue_not_rev (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : LegalIssue d C x) {i : Nat} (B : ReverseWait d C x i) : False := by
  have E := A.2.1
  have D := B.1.1
  omega

private theorem fwd_not_rev (d : Sheet) (C : Chart h) (x : Raw s n)
    {i j : Nat} (A : ForwardWait d C x i) (B : ReverseWait d C x j) : False := by
  have E := A.2.2 i A.2.1
  rw [(front_tag_iff i i).mpr rfl] at E
  exact back_not_front j i ((B.2.2 i A.2.1).symm.trans E)
theorem gate_room (C : Chart h) (G : GapInput h) :
    C.a+3<C.L ∧ h (nextAt C.root C.a)=true ∧
    ∃ b,2<b ∧ Gap h (nextAt C.root C.a) b := by
  obtain ⟨a,A,A',F⟩ := G.gaps C.root C.rootHeader
  obtain ⟨b,B,B',H⟩ := G.gaps (nextAt C.root a) F.atEnd
  obtain ⟨c,D,D',J⟩ := G.gaps (nextAt (nextAt C.root a) b) H.atEnd
  have room : a+b+c<n := by have := G.room; omega
  let C' := chart_of_three C.rootHeader F H J room
  have U := ShortReadCaptureGeometry.chart_unique C C' rfl
  have L : C.L=a+b+c := U.1
  have ports (i : Nat) (K : i<C.L) :
      C.route.port i=ShortResetChart.lane a b i := U.2 i K
  have one : ShortResetChart.lane C.a C.b a=1 := by
    have E := ports a (by omega)
    exact E.trans (by simp [ShortResetChart.lane,show a<a+b by omega])
  have zero : ShortResetChart.lane C.a C.b (a-1)=0 := by
    have E := ports (a-1) (by omega)
    exact E.trans (by simp [ShortResetChart.lane,show a-1<a by omega])
  have O := (lane1 _ _ _).mp one
  have Z0 := (lane0 _ _ _).mp zero
  have ca : C.a=a := by omega
  rw [ca]
  exact ⟨by omega,F.atEnd,b,B,H⟩

def center (C : Chart h) : Fin n := nextAt C.root C.a

theorem physical_labels (C : Chart h) :
    out C (C.a+1)=ReportGateGeometry.label (center C) false ∧
    out C (C.a+2)=ReportGateGeometry.label (center C) true := by
  constructor <;> unfold center ReportGateGeometry.label <;> simp only [Bool.false_eq_true,if_false,if_true]
  · change nextAt C.root (C.a+1)=nextAt (nextAt C.root C.a) 1
    rw [nextAt_add]
  · change nextAt C.root (C.a+2)=nextAt (nextAt C.root C.a) 2
    rw [nextAt_add]

-- Five owners can be arbitrary distinct center words of the fixed
-- partition, not necessarily five disjoint entire charts.
theorem incidence_disjoint (hh : ∃ i,h i=true) (G : GapInput h)
    (C D : Chart h) (u v : Bool)
    (E : ReportGateGeometry.label (center C) u=
         ReportGateGeometry.label (center D) v) :
    center C=center D ∧ u=v := by
  obtain ⟨_,A,b,B,F⟩ := gate_room C G
  obtain ⟨_,A',c,B',F'⟩ := gate_room D G
  exact ReportGateGeometry.disjoint_center_incidence hh A A' F F' B B' E

-- Only the old state is used to choose the label.
def OwnerProgress (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  (LegalIssue d C x ∧ e=door C) ∨
  (∃ k,ForwardWait d C x k ∧
    ((e=out C k ∧ (readyAt d C x k=true ∨
       (chartGate d C x k=true ∧ healthyAdmit (params d s) (tok d C x k) ∧
         ((tok d C x k).race=1 ∨ (tok d C x k).race=2)))) ∨
     (0<k ∧ e=out C (k-1) ∧ chartGate d C x k=true ∧
       healthyAdmit (params d s) (tok d C x k) ∧
       ((tok d C x k).race=1 ∨ (tok d C x k).race=3)))) ∨
  (∃ k,ReverseWait d C x k ∧ e=inEdge C k)

noncomputable def ownerMark (d : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) : Bool := by
  classical
  exact if OwnerProgress d C x e then true else false

theorem owner_mark_iff (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) :
    ownerMark d C x e=true ↔ OwnerProgress d C x e := by
  classical
  unfold ownerMark
  split <;> simp_all

theorem two_labels (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) :
    ∃ a b,∀ e,ownerMark d C x e=true→e=a ∨ e=b := by
  rcases S with I|⟨k,I⟩|⟨k,I⟩
  · refine ⟨door C,door C,?_⟩
    intro e H
    rcases (owner_mark_iff d C x e).mp H with A|⟨j,A,_⟩|⟨j,A,_⟩
    · exact .inl A.2
    · exact False.elim (issue_not_fwd d C x I A)
    · exact False.elim (issue_not_rev d C x I A)
  · refine ⟨out C k,out C (k-1),?_⟩
    intro e H
    rcases (owner_mark_iff d C x e).mp H with A|⟨j,A,B⟩|⟨j,A,_⟩
    · exact False.elim (issue_not_fwd d C x A.1 I)
    · have E := fwd_unique d C x A I
      subst j
      rcases B with B|B
      · exact .inl B.1
      · exact .inr B.2.1
    · exact False.elim (fwd_not_rev d C x I A)
  · refine ⟨inEdge C k,inEdge C k,?_⟩
    intro e H
    rcases (owner_mark_iff d C x e).mp H with A|⟨j,A,_⟩|⟨j,A,B⟩
    · exact False.elim (issue_not_rev d C x A.1 I)
    · exact False.elim (fwd_not_rev d C x A I)
    · have E := rev_unique d C x A I
      subst j
      exact .inl B

theorem five_support (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (B : GoodEightBank d hh Q G x)
    (C : Fin 5→Chart h) (M : ∀ j,C j∈ownerCharts G) :
    (List.ofFn (fun e : Fin n =>
      (List.ofFn (fun j : Fin 5=>(ownerMark d (C j) x e).toNat)).sum)).sum≤10 := by
  apply ReportAdaptiveFibre.five_two_label_support
  intro j
  exact two_labels d (C j) x (serial_from_bank d N hh G F digit x B (C j) (M j)).1

#print axioms serial_from_bank
theorem pairs_from_centers (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (active desired : Fin 5→Bool) (ban : Fin n→Option (Fin n))
    (spec : ∀ e a,ban e=some a ↔
      ∃ j,active j=true ∧ e=label (center (C j)) (!desired j) ∧
        a=label (center (C j)) (desired j)) : DisjointPairs ban := by
  constructor
  · intro e a E
    obtain ⟨j,Aj,Ej,Dj⟩ := (spec e a).mp E
    cases B : ban a with
    | none => rfl
    | some b =>
      obtain ⟨k,Ak,Ek,Dk⟩ := (spec a b).mp B
      obtain ⟨R,S⟩ := incidence_disjoint hh G (C j) (C k) (desired j) (!desired k)
        (Dj.symm.trans Ek)
      have K := inj R
      subst k
      cases J : desired j <;> simp [J] at S
  · intro e e' a E E'
    obtain ⟨j,_,Ej,Dj⟩ := (spec e a).mp E
    obtain ⟨k,_,Ek,Dk⟩ := (spec e' a).mp E'
    have K := inj (incidence_disjoint hh G (C j) (C k) _ _ (Dj.symm.trans Dk)).1
    subst k
    exact Ej.trans Ek.symm

-- Exact old grant readback on either report sheet. This is NOT

#print axioms physical_labels
#print axioms incidence_disjoint
#print axioms two_labels
#print axioms five_support
#print axioms pairs_from_centers
end L4.ReportFastOwnerSupport

