import Leader.L4.ReportProtectedMark
import Leader.L4.ReportQuietCovers

namespace L4.ReportQuietRaw
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportGenerationAncestry ReportLeaseStep
open ReportCurrentCustodyCut ReportLeaseOwner ReportGoodEightCut ReportGoodEightBank
open ReportPrelaunchClock ReportIngressOwnership ReportFastRawEvent
open ReportProtectedMark ReportProtectedAB ReportProtectedWords ReportProtectedRebase
open ReportProtectedInterval ReportStickyRawCover ReportStaticSpacing
open ShortHopSpacing ReportRootBall ReportQuietCovers

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem guard_of_opportunity (p : Params) (hu : Bool) (u v : BitVec p.w)
    (K : ancestryCommitOpportunity p hu true u v) :
    CommitGuard p hu u v (oldReportToken p hu u 0).payload := by
  let t := publicationToken p hu u 0
  have Ready : rankReady p hu u 0=true := K.2.1
  have T : t.tag=2 := ((rankReady_iff ..).mp Ready).1
  have NS : t.fault=false := K.2.2.1
  have OP : t.opcode=commitOp p := K.2.2.2.1
  have S : SealCommitForward p t := by
    rw [show t=decode p (rankGate p hu u 0) (resetTokenRead p u 0) from rankToken_wire p hu u 0]
    refine seal_commit_decoded_shape p _ _ ?_ ?_ (.inr ?_) <;>
      rw [←rankToken_wire p hu u 0]
    · exact T
    · exact NS
    · exact OP
  have G : packetCommitGuard p v t=true := K.2.2.2.2
  change (!t.applied && reportOldGrant p v 1 &&
    (publicationSelector p v==t.payload/8) && (reportOldSeal p v==some t.payload))=true at G
  have GG : (((!t.applied)=true ∧ reportOldGrant p v 1=true) ∧
      publicationSelector p v=t.payload/8) ∧ reportOldSeal p v=some t.payload := by
    simpa only [Bool.and_eq_true_iff,beq_iff_eq] using G
  obtain ⟨⟨⟨A,B⟩,C⟩,D⟩ := GG
  have AP : t.applied=false := by simpa using A
  have Race := S.2.2.2.2.1
  have Outcome := S.2.2.2.2.2.1
  have Eq : t=({tag:=2, opcode:=commitOp p,payload:=t.payload} : Tok) := by
    generalize U : t=q at T OP NS Race Outcome AP ⊢
    cases q
    simp_all
  exact ⟨Eq,B,C,D⟩

theorem classify_iff_ingress (d : Sheet) (h : Fin n→Bool)
    (x : Raw s n) (e : Fin n) (i : Lower h)
    (Mask : ∀ k,lower d (oldHeaders (rows s) (x k))=h k) :
    classify d h x e=some i ↔ i.val=rightNeighbor e ∧ oldCommitAt d x e := by
  constructor
  · intro C
    obtain ⟨E,H,G⟩ := (classify_iff d h x e i).mp C
    refine ⟨E.symm,?_⟩
    unfold oldCommitAt
    rw [H]
    exact ReportFastClassifiedCustody.commit_guard_is_ancestry _ _ _ _ G
  · rintro ⟨E,C⟩
    have H : lower d (oldHeaders (rows s) (x (rightNeighbor e)))=true :=
      (Mask _).trans (E ▸ i.property)
    apply (classify_iff d h x e i).mpr
    unfold oldCommitAt at C
    rw [H] at C
    exact ⟨E.symm,H,guard_of_opportunity _ _ _ _ C⟩

private theorem update_clip (r v : Nat) (a : Bool) :
    ReportDigitArithmetic.updateDist r a v=updateDistance r a (min r v) := by
  cases a with
  | true => rfl
  | false =>
    unfold ReportDigitArithmetic.updateDist updateDistance
    simp only [Bool.false_eq_true,if_false]
    by_cases H : v≤r
    · rw [Nat.min_eq_right H]
    · rw [Nat.min_eq_left (by omega : r≤v), Nat.min_eq_left (by omega : r≤v+1),
        Nat.min_eq_left (by omega : r≤r+1)]

theorem labelled_raw_row (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h, let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
      (params d s).digits≤C.L-(C.a+C.b))
    (Fits : ∀ i : Lower h, ∃ len, Gap h i.val len ∧ (params d s).digits≤len)
    (neighbor : Bool→Lower h→Lower h) (Geom : NeighborLaw G neighbor)
    (x : Raw s n) (A : CurrentCustodyCut d hh Q G x) (e : Fin n)
    (i : Lower h) :
    (classify d h x e=some i →
      Publish (readout d h) (params d s).radius neighbor x (rawNext s x e) i) ∧
    (classify d h x e≠some i →
      Frame (readout d h) x (rawNext s x e) i) := by
  let p := params d s
  have X : Cached d hh Q x := A.1.1.2.1.1.1.1
  have Mask := (cached_fibre d N hh Q F).mask x X
  have Safe := A.1.1.2.2
  have Equiv := classify_iff_ingress d h x e i Mask
  constructor
  · intro E
    have K := Equiv.mp E
    obtain ⟨r,Eq⟩ := ReportFastClassifiedCustody.centre_covers_lower_header hh G e (K.1 ▸ i.property)
    obtain ⟨L,M,R⟩ := Width r
    have Centre : centre (charter G r)=i.val := Eq.symm.trans K.1.symm
    obtain ⟨HL,HR⟩ := Geom r i Centre
    have Pub := publication_now d N Spos hh G F r x A L M R e Eq K.2
    dsimp only at Pub
    rw [Centre,←HR,←HL] at Pub
    refine ⟨Pub.1,?_,?_⟩
    · intro dir
      change min p.radius (reportValue p (fun j=>selectBytes d (rawNext s x e j)) i.val dir)=
        updateDistance p.radius (selectedA d x (neighbor dir i).val)
          (min p.radius (reportValue p (fun j=>selectBytes d (x j)) (neighbor dir i).val dir))
      cases dir
      · rw [Pub.2.2.1,update_clip]
        apply Nat.min_eq_right
        unfold updateDistance
        split
        · omega
        · exact Nat.min_le_left _ _
      · rw [Pub.2.1,update_clip]
        apply Nat.min_eq_right
        unfold updateDistance
        split
        · omega
        · exact Nat.min_le_left _ _
    · change selectedB d (rawNext s x e) i.val=thresholds p.radius
        (min p.radius (reportValue p (fun j=>selectBytes d (rawNext s x e j)) i.val true))
        (min p.radius (reportValue p (fun j=>selectBytes d (rawNext s x e j)) i.val false))
      rw [Pub.2.2.2]
      unfold thresholds
      simp only [clipped_threshold_iff _ _ _ (Nat.le_refl _)]
      rfl
  · intro E
    have K := fun H=>E (Equiv.mpr H)
    have AB := raw_ab_without_ingress d N x e i.val K
    obtain ⟨len,Gap,Fits'⟩ := Fits i
    exact ⟨AB.1,AB.2,fun dir=>congrArg (min p.radius)
      (value_frame_without_ingress d N hh G x e i.val Mask i.property Gap Fits' Safe K dir)⟩

/-- Same-track no-paint on the literal marks yields a quiet interval
whose labels are exactly raw classifier results, not a chosen
MarkSemantics witness. Both boundary states are included in z_const. -/
theorem quiet_of_no_paint (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h, let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
      (params d s).digits≤C.L-(C.a+C.b))
    {L U : Nat} (Bounds : GapBounds h L U)
    (states : Nat→Raw s n) (marks : Nat→Fin n)
    (ball : Lower h→Prop) (a b : Nat)
    (Step : ∀ t,a≤t → t<b → states (t+1)=rawNext s (states t) (marks t))
    (Cut : ∀ t,a≤t → t≤b → CurrentCustodyCut d hh Q G (states t))
    (NoPaint : ∀ t i,a≤t → t<b → ball i → rawPaint d h (states t) (marks t) i=false) :
    Quiet (readout d h) (params d s).radius (rootNeighbor Bounds hh) ball
      ((readout d h).z (states a)) states
      (fun t i=>classify d h (states t) (marks t)=some i) a b := by
  have one (t : Nat) (i : Lower h) (A : a≤t) (B : t<b) :=
    labelled_raw_row d N Spos hh G F Width (width_supplies_gap d G Width)
      (rootNeighbor Bounds hh) (concrete_neighbors Bounds hh G) (states t)
      (Cut t A (by omega)) (marks t) i
  refine ⟨?_,?_,?_⟩
  · intro t i A B I
    have Z (k : Nat) (H : a+k≤b) :
        (readout d h).z (states (a+k)) i=(readout d h).z (states a) i := by
      induction k with
      | zero => rfl
      | succ k IH =>
        have A' : a≤a+k := by omega
        have B' : a+k<b := by omega
        have C : Cached d hh Q (states (a+k)) := (Cut (a+k) A' (by omega)).1.1.2.1.1.1.1
        have M := (cached_fibre d N hh Q F).mask _ C
        rw [show a+(k+1)=a+k+1 by omega,Step (a+k) A' B']
        rw [raw_pulse d h (states (a+k)) (marks (a+k)) i (edge_sep N _) M,
          NoPaint (a+k) i A' B' I]
        exact IH (by omega)
    have E : a+(t-a)=t := by omega
    exact E ▸ Z (t-a) (E.symm ▸ B)
  · intro t i A B _ K
    rw [Step t A B]
    exact (one t i A B).2 K
  · intro t i A B _ K
    rw [Step t A B]
    exact (one t i A B).1 K

end L4.ReportQuietRaw
