import Leader.L4.ReportQuietRaw
import Leader.L4.ReportLiteralPulse
import Leader.L4.ReportTrialCone

namespace L4.ReportRawTrialSticky
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportLeaseOwner ReportByteRows
open ReportCurrentCustodyCut ReportFastRawEvent ReportProtectedMark
open ReportProtectedInterval ReportStickyRawCover ReportStaticSpacing ShortHopSpacing
open ReportQuietCovers ReportQuietRaw ReportLiteralPulse ReportTrialToSticky ReportTrialCone

variable {s n L U : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private theorem quiet_sub {I X : Type} {R : Readout X I} {rho : Nat}
    {near : Bool→I→I} {ball : I→Prop} {z : I→Bool}
    {states : Nat→X} {pub : Nat→I→Prop} {a b lo hi : Nat}
    (S : Quiet R rho near ball z states pub a b) (L : a≤lo) (H : hi≤b) :
    Quiet R rho near ball z states pub lo hi :=
  ⟨fun t i A B C=>S.z_const t i (by omega) (by omega) C,
    fun t i A B C D=>S.frame t i (by omega) (by omega) C D,
    fun t i A B C D=>S.publish t i (by omega) (by omega) C D⟩

/-- A local quiet interval on the physical tape containing consecutive
complete publication cover windows. The interval and the endpoints are
literal natural mark coordinates. -/
structure Passed {I : Type} (rho : Nat) (ball : I→Prop) (pub : Nat→I→Prop)
    (a b : Nat) : Prop where
  cert : ∃ cut : Nat→Nat,
    a≤cut 0 ∧ cut (rho+1)≤b ∧
    (∀ k,k≤rho → cut k≤cut (k+1)) ∧
    (∀ k,k≤rho → Covers ball pub (cut k) (cut (k+1)))

private theorem cut_mono {r : Nat} {cut : Nat→Nat}
    (A : ∀ k,k≤r → cut k≤cut (k+1)) :
    ∀ k,k≤r+1 → cut 0≤cut k ∧ cut k≤cut (r+1) := by
  intro k K
  constructor
  · induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans (ih (by omega)) (A k (by omega))
  · have C : ∀ p,k+p≤r+1 → cut k≤cut (k+p) := by
      intro p
      induction p with
      | zero => simp
      | succ p ih =>
        intro H
        exact Nat.le_trans (ih (by omega)) (A (k+p) (by omega))
    have H := C (r+1-k) (by omega)
    rwa [show k+(r+1-k)=r+1 by omega] at H

theorem complete_quiet_interval {I X : Type} (R : Readout X I) (rho : Nat)
    (near : Bool→I→I) (ball : I→Prop) (z : I→Bool) (states : Nat→X)
    (pub : Nat→I→Prop) (a b : Nat) (S : Quiet R rho near ball z states pub a b)
    (W : Passed rho ball pub a b) :
    (∀ i,ball i→CorrectAt R rho near ball z rho (states b) i) ∧
    Visible R rho near ball z (states b) := by
  obtain ⟨cut,A,B,M,C⟩ := W.cert
  have AB : a≤b := Nat.le_trans A (Nat.le_trans (cut_mono M 0 (by omega)).2 B)
  have SQ (k : Nat) (K : k≤rho) :
      Quiet R rho near ball z states pub (cut k) (cut (k+1)) :=
    quiet_sub S (Nat.le_trans A (cut_mono M k (by omega)).1)
      (Nat.le_trans (cut_mono M (k+1) (by omega)).2 B)
  have Init := passes R rho near ball z states pub cut M SQ C rho (Nat.le_refl _)
  have Final := quiet_preserves_correct R rho near ball z states pub _ b rho B
    (Nat.le_refl _) (quiet_sub S (Nat.le_trans A (cut_mono M _ (by omega)).1) (Nat.le_refl _)) Init
  have Z (i : I) (H : ball i) : R.z (states b) i=z i := S.z_const b i AB (Nat.le_refl _) H
  refine ⟨Final,⟨Z,fun i H=>(Final i H).1.trans (Z i H).symm,?_,fun i H=>(Final i H).2.1⟩⟩
  intro i dir k K P
  have Here : ball i := (ReportRootBall.path_iff _ _ _ _ _).mp P 0 (by omega)
  exact (correct_rebase R rho near ball z _ (fun i I=>(Z i I).symm) rho _ i Here
    (Final i Here)).2.2 dir k K P

abbrev WidthOK (d : Sheet) (G : GapInput h) (s : Nat) :=
  ∀ r : Owner h, let C := charter G r
    (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
    (params d s).digits≤C.L-(C.a+C.b)

def Paint (d : Sheet) (states : Nat→Raw s n) (marks : Nat→Fin n)
    (t : Nat) (i : Lower h) : Prop :=
  rawPaint d h (states t) (marks t) i=true

def QuietPass (d : Sheet) (Bounds : GapBounds h L U) (hh : ∃ i,h i=true)
    (states : Nat→Raw s n) (marks : Nat→Fin n) (c : Lower h) (a b : Nat) : Prop :=
  (∀ t i,a≤t → t<b → ReportRootBall.ball Bounds hh (params d s).radius c i →
    ¬Paint d states marks t i) ∧
  Passed (params d s).radius (ReportRootBall.ball Bounds hh (params d s).radius c)
    (fun t i=>classify d h (states t) (marks t)=some i) a b

theorem quiet_pass_result (d : Sheet) (N : 1<n) (S : 0<s) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (W : WidthOK d G s) (Bounds : GapBounds h L U)
    (states : Nat→Raw s n) (marks : Nat→Fin n) (c : Lower h) (a b : Nat)
    (Step : ∀ t,a≤t → t<b → states (t+1)=rawNext s (states t) (marks t))
    (Cut : ∀ t,a≤t → t≤b → CurrentCustodyCut d hh Q G (states t))
    (P : QuietPass d Bounds hh states marks c a b) :
    let R := readout (s:=s) d h
    let near := ReportRootBall.rootNeighbor Bounds hh
    let ball := ReportRootBall.ball Bounds hh (params d s).radius c
    let z := R.z (states a)
    (∀ i,ball i → CorrectAt R (params d s).radius near ball z (params d s).radius (states b) i) ∧
    Visible R (params d s).radius near ball z (states b) := by
  let r := (params d s).radius
  let B := ReportRootBall.ball Bounds hh r c
  let R := readout (s:=s) d h
  have C := quiet_of_no_paint d N S hh G F W Bounds states marks B a b Step Cut
    (fun t i A B' H => Bool.eq_false_iff.mpr (P.1 t i A B' H))
  exact complete_quiet_interval R r _ B (R.z (states a)) states _ a b C P.2

/-- Deterministic soundness on an actual physical timeline, assuming
the three pulse events and the full mesh give the named interval
certificates. This conclusion is the existing raw Sticky predicate. -/
theorem physical_sticky_of_quiet_trials (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (W : WidthOK d G s) (Bounds : GapBounds h L U) (Lo : 1≤L)
    (Room : (params d s).radius*U<n) (states : Nat→Raw s n) (marks : Nat→Fin n)
    (i : Lower h) (lo test endTime : Nat)
    (Step : ∀ t,t<endTime → states (t+1)=rawNext s (states t) (marks t))
    (Cut : ∀ t,t≤endTime → CurrentCustodyCut d hh Q G (states t))
    (First : ∀ j,ReportRootBall.ball Bounds hh (params d s).radius i j → j≠i →
      ∃ t,lo≤t ∧ t<test ∧ Paint d states marks t j)
    (T : lo≤test) (End : test<endTime) (Second : Paint d states marks test i)
    (Before : ∀ t j,lo≤t → t≤test → t<endTime → ReportRootBall.ball Bounds hh (params d s).radius i j →
      Paint d states marks t j → ∃ a,QuietPass d Bounds hh states marks j a t)
    (After : ∀ t j,lo≤t → t≤test → t<endTime → ReportRootBall.ball Bounds hh (params d s).radius j i →
      Paint d states marks t j → ∃ b,b≤endTime ∧ QuietPass d Bounds hh states marks j (t+1) b) :
    Sticky (readout d h) (params d s).radius (ReportRootBall.rootNeighbor Bounds hh)
      (ReportRootBall.ball Bounds hh (params d s).radius) ReportRootBall.centerMask i (states endTime) := by
  let R := readout (s:=s) d h
  let rho := (params d s).radius
  let B := ReportRootBall.ball Bounds hh rho
  let geom := ReportRootBall.physical_ball_geometry Bounds hh Lo Room
  let near := ReportRootBall.rootNeighbor Bounds hh
  have Mask (t : Nat) (H : t≤endTime) :
      ∀ k,lower d (oldHeaders (rows s) (states t k))=h k :=
    (cached_fibre d N hh Q F).mask _ (Cut t H).1.1.2.1.1.1.1
  have Frame (t : Nat) (j : Lower h) (H : t<endTime) (P : ¬Paint d states marks t j) :
      R.z (states (t+1)) j=R.z (states t) j := by
    rw [Step t H]
    change _ = (readout d h).z (states t) j
    rw [raw_pulse d h (states t) (marks t) j (edge_sep N _) (Mask t (by omega))]
    rw [show rawPaint d h (states t) (marks t) j=false from Bool.eq_false_iff.mpr P]
    rfl
  have Decision (t : Nat) (j : Lower h) (LT : lo≤t) (TT : t≤test) (H : t<endTime) (B' : B i j)
      (P : Paint d states marks t j) :
      R.z (states (t+1)) j=true ↔ ∀ k,B j k → k≠j → R.z (states t) k=false := by
    obtain ⟨a,A⟩ := Before t j LT TT H B' P
    obtain ⟨_,V⟩ := quiet_pass_result d N S hh G F W Bounds states marks j a t
      (fun q _ Q=>Step q (by omega)) (fun q _ Q=>Cut q (by omega)) A
    have C : CorrectAt R rho near (B j) (R.z (states t)) rho (states t) j :=
      ⟨V.captured j (geom j).center_mem,V.pair j (geom j).center_mem,V.interior j⟩
    have D := certified_decision R Bounds hh Lo rho Room j (states t) C
    rw [Step t H]
    change (readout d h).z _ _=true ↔ _
    rw [raw_pulse d h (states t) (marks t) j (edge_sep N _) (Mask t (by omega)),
      show rawPaint d h (states t) (marks t) j=true from P]
    exact D
  have carry (b : Nat) (B' : b≤endTime)
      (Z : Sticky R rho near B ReportRootBall.centerMask i (states b)) :
      Sticky R rho near B ReportRootBall.centerMask i (states endTime) := by
    have go : ∀ k,b+k≤endTime → Sticky R rho near B ReportRootBall.centerMask i (states (b+k)) := by
      intro k
      induction k with
      | zero => simpa using fun (_ : b≤endTime)=>Z
      | succ k ih =>
        intro H
        have K : b+k<endTime := by omega
        obtain ⟨c,J,V⟩ := ih (by omega)
        rw [show b+(k+1)=b+k+1 by omega,Step _ K]
        have Sem := raw_mark_semantics d N S hh G F W Bounds (states (b+k))
          (Cut _ (by omega)) (marks (b+k)) (B c)
        exact ⟨c,J,(one_mark R rho near (B c) c _ (geom c)
          (states (b+k)) _ _ V Sem).1⟩
    have O := go (endTime-b) (by omega)
    rwa [show b+(endTime-b)=endTime by omega] at O
  apply sticky_of_two_windows B (Paint d states marks) (fun t=>R.z (states t))
    lo endTime i test _
    (fun j H=>ball_symm Bounds hh rho i j H) (geom i).center_mem First T End Second
    (fun t j _ H=>Frame t j H) Decision
  intro t j LT TT H J P On
  obtain ⟨b,Z,A⟩ := After t j LT TT H J P
  have Iso := isolated_after_test B (Paint d states marks) (fun t=>R.z (states t)) j t P On
    (Decision t j LT TT H (ball_symm Bounds hh rho j i J) P)
    (fun k _ K E => Bool.noConfusion
      ((distinct_gates_cannot_paint d N G (states t) (marks t) j k (Ne.symm K) P).symm.trans E))
    (fun k _=>Frame t k H)
  obtain ⟨_,V⟩ := quiet_pass_result d N S hh G F W Bounds states marks j (t+1) b
    (fun q _ Q=>Step q (by omega)) (fun q _ Q=>Cut q (by omega)) A
  have V' : Visible R rho near (B j) (ReportRootBall.centerMask j) (states b) :=
    ⟨fun k K=>(V.isolated k K).trans (Iso k K),V.captured,V.interior,V.pair⟩
  exact carry b Z ⟨j,J,V'⟩

end L4.ReportRawTrialSticky
