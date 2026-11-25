import Leader.L4.ReportByteRows
import Leader.L4.ShortHopSpacing
import Leader.L4.ReportRadiusSpacing
import Leader.L4.ProductionH6Count

namespace L4.ReportStaticSpacing
open AllSizeProtocol PhysicalCustody ShortHopSpacing ShortResetChart ShortLayerGeometry
open BStarH6WordChart BStarH6Ordinal

abbrev Lower {n : Nat} (h : Fin n→Bool) := {i : Fin n // h i=true}

noncomputable def successor {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (i : Lower h) : Lower h :=
  ⟨nextAt i.val (successorWidth G i.val),(successorWidth_spec G i.val i.property).2.2.atEnd⟩

theorem advance_val {n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (i : Lower h) (j : Nat) :
    (ReportRadiusSpacing.advance (successor G) i j).val=hop (successorWidth G) i.val j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change nextAt _ (successorWidth G _) = _
    rw [ih,hop_add]
    rfl

/-- An exact selected-bank digit, using the same field layout and clip
as CMP/READ in the work row. The high digit is the minus direction. -/
def selectedDigit (p : ReportByteRows.Params) (ix : Nat) (minus : Bool)
    (a : BitVec p.w) : Nat :=
  let off := ReportByteRows.sealBase p+5+(1-ix)*ReportByteRows.bankW p
  let off := off+(if minus then ReportByteRows.d p else 0)
  min (p.beta-1) (a.extractLsb' off (ReportByteRows.d p)).toNat

/-- Low digit first, starting at the lower header. The bank captured
at the header selects the same lane at each cell of the digit file. -/
def reportValue {n : Nat} (p : ReportByteRows.Params)
    (a : Fin n→BitVec p.w) (i : Fin n) (minus : Bool) : Nat :=
  let ix := ReportByteRows.publicationSelector p (a i)
  ((List.range p.digits).map
    (fun j=> selectedDigit p ix minus (a (nextAt i j))*p.beta^j)).sum

/-- Static common-cut premises on the actual report fields. A report
transaction computes from its captured snapshot; none of the equations
below is asserted to hold on arbitrary bytes or on an arbitrary COMMIT. -/
structure ReportCut {n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (p : ReportByteRows.Params) (a : Fin n→BitVec p.w) : Prop where
  own : ∀ i : Lower h, ReportByteRows.publicationA p (a i.val)
      (ReportByteRows.publicationSelector p (a i.val))=ReportByteRows.Z p (a i.val)
  minus_step : ∀ i : Lower h, reportValue p a (successor G i).val true =
    if ReportByteRows.publicationA p (a i.val) (ReportByteRows.publicationSelector p (a i.val))
    then 0 else min p.radius (reportValue p a i.val true+1)
  plus_step : ∀ i : Lower h, reportValue p a i.val false =
    let j := (successor G i).val
    if ReportByteRows.publicationA p (a j) (ReportByteRows.publicationSelector p (a j))
    then 0 else min p.radius (reportValue p a j false+1)
  clipped : ∀ i : Lower h, reportValue p a i.val true ≤ p.radius ∧
    reportValue p a i.val false ≤ p.radius
  threshold : ∀ i : Lower h, ReportByteRows.publicationPair p (a i.val)
      (ReportByteRows.publicationSelector p (a i.val)) =
      2*(decide (reportValue p a i.val true<p.radius)).toNat+
        (decide (reportValue p a i.val false<p.radius)).toNat
  paint : ∀ i : Lower h, ReportByteRows.Z p (a i.val)=
    (ReportByteRows.publicationPair p (a i.val)
      (ReportByteRows.publicationSelector p (a i.val))==0)

theorem settled_of_cut {n L U : Nat} {h : Fin n→Bool} {G : GapBounds h L U}
    {p : ReportByteRows.Params} {a : Fin n→BitVec p.w} (C : ReportCut G p a) :
    ReportRadiusSpacing.Settled (successor G) p.radius
      (fun i=>ReportByteRows.Z p (a i.val))
      (fun i=>reportValue p a i.val true) (fun i=>reportValue p a i.val false) := by
  constructor
  · intro i
    simpa only [C.own i] using C.minus_step i
  · intro i
    simpa only [C.own (successor G i)] using C.plus_step i
  · intro i
    change ReportByteRows.Z p (a i.val)=true ↔ _
    rw [C.paint i,C.threshold i]
    obtain ⟨A,B⟩ := C.clipped i
    by_cases L : reportValue p a i.val true<p.radius <;>
      by_cases R : reportValue p a i.val false<p.radius <;> simp [L,R] <;> omega

/-- The static report conclusion in the exact physical successor
representation, not an assumption about the scheduler. -/
theorem hop_bounds_of_cut {n L U : Nat} {h out : Fin n→Bool} {G : GapBounds h L U}
    {p : ReportByteRows.Params} {a : Fin n→BitVec p.w} (C : ReportCut G p a)
    (mask : ∀ i, out i=(h i && ReportByteRows.Z p (a i))) :
    HopBounds (successorWidth G) out (p.radius+1) (2*p.radius+1) := by
  have sub (i : Fin n) (H : out i=true) : h i=true := by
    rw [mask i,Bool.and_eq_true] at H
    exact H.1
  have val (i : Lower h) : out i.val=ReportByteRows.Z p (a i.val) := by
    rw [mask _,i.property,Bool.true_and]
  intro i H
  let root : Lower h := ⟨i,sub i H⟩
  have R : ReportByteRows.Z p (a root.val)=true := (val root).symm.trans H
  obtain ⟨d,D,U,A,I⟩ := ReportRadiusSpacing.next_selected_gap (settled_of_cut C) root R
  have E (j : Nat) :
      out (hop (successorWidth G) i j)=
      ReportByteRows.Z p (a (ReportRadiusSpacing.advance (successor G) root j).val) := by
    rw [←show (ReportRadiusSpacing.advance (successor G) root j).val=
      hop (successorWidth G) i j from advance_val G root j]
    exact val _
  refine ⟨d,D,U,⟨by omega,(E d).trans A,fun j K J=>(E j).trans (I j K J)⟩⟩

theorem nonempty_of_cut {n L U : Nat} {h out : Fin n→Bool} {G : GapBounds h L U}
    {p : ReportByteRows.Params} {a : Fin n→BitVec p.w} (C : ReportCut G p a)
    (mask : ∀ i, out i=(h i && ReportByteRows.Z p (a i))) (H : ∃ i,h i=true) :
    ∃ i,out i=true := by
  obtain ⟨i,I⟩ := H
  obtain ⟨j,J⟩ := ReportRadiusSpacing.selected_nonempty (settled_of_cut C) ⟨i,I⟩
  refine ⟨j.val,?_⟩
  rw [mask _,j.property,Bool.true_and]
  exact J

def h4 {s n : Nat} (z : Raw s n) : Fin n→Bool := fun i=>(oldHeaders (rows s) (z i)).h4
def h5 {s n : Nat} (z : Raw s n) : Fin n→Bool := fun i=>(oldHeaders (rows s) (z i)).h5

abbrev p1 (s : Nat) : ReportByteRows.Params := ⟨s+1,1,s,streak s⟩
abbrev p2 (s : Nat) : ReportByteRows.Params := ⟨2,ell (radiusTwo s+1),radiusTwo s,streak (radiusTwo s)⟩

private theorem pulse_is_Z (p : ReportByteRows.Params) (v : BitVec p.w) :
    ShortByteReadouts.reportPulse p.beta p.digits p.streak v = ReportByteRows.Z p v := by
  change (v.extractLsb' (ell p.streak+2) 1).getLsbD 0=v.getLsbD (ell p.streak+2)
  rw [BitVec.getLsbD_extractLsb']
  simp

theorem report1_mask {s n : Nat} (z : Raw s n) (i : Fin n) :
    h5 z i=(h4 z i && ReportByteRows.Z (p1 s) (z i).report1) := by
  exact congrArg (fun b=>h4 z i && b) (pulse_is_Z (p1 s) (z i).report1)

theorem report2_mask {s n : Nat} (z : Raw s n) (i : Fin n) :
    oldH6 (rows s) z i=(h5 z i && ReportByteRows.Z (p2 s) (z i).report2) := by
  exact congrArg (fun b=>h5 z i && b) (pulse_is_Z (p2 s) (z i).report2)

theorem h5_hops {s n : Nat} {z : Raw s n} {G : GapBounds (h4 z) 16 81}
    (R : ReportCut G (p1 s) (fun i=>(z i).report1)) :
    HopBounds (successorWidth G) (h5 z) (s+1) (2*s+1) :=
  hop_bounds_of_cut R (report1_mask z)

theorem h6_hops {s n : Nat} {z : Raw s n}
    {G : GapBounds (h5 z) (16*(s+1)) (81*(2*s+1))}
    (R : ReportCut G (p2 s) (fun i=>(z i).report2)) :
    HopBounds (successorWidth G) (oldH6 (rows s) z) (radiusTwo s+1) (2*radiusTwo s+1) :=
  hop_bounds_of_cut R (report2_mask z)

theorem h5_bounds {s n : Nat} {z : Raw s n} {G : GapBounds (h4 z) 16 81}
    (R : ReportCut G (p1 s) (fun i=>(z i).report1)) :
    GapBounds (h5 z) (16*(s+1)) (81*(2*s+1)) := by
  apply spacing_transfer_chosen G
  · intro i I
    rw [report1_mask z i,Bool.and_eq_true] at I
    exact I.1
  · exact hop_bounds_of_cut R (report1_mask z)

theorem h6_bounds {s n : Nat} {z : Raw s n}
    {G : GapBounds (h5 z) (16*(s+1)) (81*(2*s+1))}
    (R : ReportCut G (p2 s) (fun i=>(z i).report2)) :
    WidthPackedBridge.CertifiedSpacing z := by
  apply spacing_transfer_chosen G
  · intro i I
    rw [report2_mask z i,Bool.and_eq_true] at I
    exact I.1
  · exact hop_bounds_of_cut R (report2_mask z)

theorem raw_static_geometry {s n : Nat} (S : 6≤s) (advice : s=ell (ell n)) (z : Raw s n)
    (G : GapBounds (h4 z) 16 81) (H4 : ∃ i,h4 z i=true)
    (R1 : ReportCut G (p1 s) (fun i=>(z i).report1))
    (R2 : ReportCut (h5_bounds R1) (p2 s) (fun i=>(z i).report2)) :
    ∃ hh : ∃ i,oldH6 (rows s) z i=true,
      WidthPackedBridge.CertifiedSpacing z ∧
      4≤total (oldH6 (rows s) z) ∧
      total (oldH6 (rows s) z)*radWidth s≤n ∧
      (∀ e, oldH6 (rows s) z (rightNeighbor e)=true →
        radWidth s≤oldOrdinal (rows s) z hh e+1 ∧
        oldOrdinal (rows s) z hh e+1≤1024*radWidth s) ∧
      (∀ e f, oldH6 (rows s) z (rightNeighbor e)=true →
        oldH6 (rows s) z (rightNeighbor f)=true →
        4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1)) := by
  have H5 := nonempty_of_cut R1 (report1_mask z) H4
  have H6 := nonempty_of_cut R2 (report2_mask z) H5
  have G6 := h6_bounds R2
  obtain ⟨L,U⟩ := WidthRatioArithmetic.production_bounds S
  have E (e : Fin n) (H : oldH6 (rows s) z (rightNeighbor e)=true) :
      radWidth s≤oldOrdinal (rows s) z H6 e+1 ∧
      oldOrdinal (rows s) z H6 e+1≤1024*radWidth s :=
    let B := WidthPackedBridge.spacing_end_width z H6 G6 e H
    ⟨Nat.le_trans L B.1,Nat.le_trans B.2 U⟩
  exact ⟨H6,G6,ProductionH6Count.four_h6_of_advice S advice z H6 G6,
    PackedOrdinalCount.total_mul_width_le _ H6 _ (fun e H=>(E e H).1),
    E,WidthPackedBridge.spacing_ratio z H6 G6⟩

/-- The width writer's flag convergence is a separate premise; no
width token or temporal obligation is discharged by static spacing. -/
theorem custody_geometry_of_reports {s n : Nat} (S : 6≤s) (advice : s=ell (ell n)) (z : Raw s n)
    (G : GapBounds (h4 z) 16 81) (H4 : ∃ i,h4 z i=true)
    (R1 : ReportCut G (p1 s) (fun i=>(z i).report1))
    (R2 : ReportCut (h5_bounds R1) (p2 s) (fun i=>(z i).report2))
    (F : ∀ hh : ∃ i,oldH6 (rows s) z i=true, WidthPackedBridge.FlagsCorrect z hh) :
    CustodyGeometry z ∧ 4≤total (oldH6 (rows s) z) := by
  obtain ⟨hh,C,K,_⟩ := raw_static_geometry S advice z G H4 R1 R2
  exact ⟨WidthPackedBridge.geometry_of_certified_width S z hh C (F hh),K⟩

#print axioms advance_val
#print axioms settled_of_cut
#print axioms hop_bounds_of_cut
#print axioms nonempty_of_cut
#print axioms report1_mask
#print axioms report2_mask
#print axioms h5_hops
#print axioms h6_hops
#print axioms h5_bounds
#print axioms h6_bounds
#print axioms raw_static_geometry
#print axioms custody_geometry_of_reports
end L4.ReportStaticSpacing
