import Leader.L4.ReportSnapshotLease
import Leader.L4.ReportItemNineActualPublication

namespace L4.ReportProtectedRebase
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportOwnerSerial ReportSnapshotLease ReportIndexedSideLease
open ReportGoodEightBank ReportGoodEightCut ReportReaderSelectorLease ReportGenerationAncestry
open ReportDigitWord ReportStaticSpacing ReportLeaseGrants ReportWriterPayload
open ReportLeaseOwner ReportGrantTimeline ShortLayerGeometry ReportDigitArithmetic

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem selector_on_held_tape (d : Sheet) (N : 1<n) (i : Fin n) (j : Fin 3)
    (Side : j=0 ∨ j=2) (x : Raw s n) (w : List (Fin n))
    (C : Compatible (rawGrant d x i)) (Held : HeldAlong d i j x w) :
    rawSelector d (rawRun x w) i=rawSelector d x i := by
  induction w generalizing x with
  | nil => rfl
  | cons e w IH =>
    have S := reader_grant_protects_selector d x e i N j Side C Held.1
    have B := raw_compatible_step d x e i (edge_sep N e) C
    exact (IH _ B Held.2).trans S

/-- The arithmetic value of the genuinely held reader word is already
its value on the immediate old cut of the accepted publication. -/
theorem value_on_held_tape (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Dgt : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (x : Raw s n) (First : FirstCut d hh Q G x)
    (hdr : Fin n) (Hdr : h hdr=true) (len : Nat) (Gap : Gap h hdr len)
    (Width : (params d s).digits≤len)
    (side : Fin 3) (Side : side=0 ∨ side=2) (w : List (Fin n))
    (Held : HeldAlong d hdr side x w) :
    reportValue (params d s) (fun i=>selectBytes d (rawRun x w i)) hdr (side=0) =
    reportValue (params d s) (fun i=>selectBytes d (x i)) hdr (side=0) := by
  let p := params d s
  have S := selector_on_held_tape d N hdr side Side x w (First.1.2 hdr Hdr) Held
  unfold reportValue
  dsimp only
  apply congrArg List.sum
  apply List.map_congr_left
  intro j J
  have I := observed_word_digit d N hh G F Dgt Rail x First hdr Hdr Gap
    (Nat.lt_of_lt_of_le (List.mem_range.mp J) Width)
    side Side w Held (rawSelector d x hdr) rfl
  change publicationSelector p (selectBytes d (rawRun x w hdr)) =
    publicationSelector p (selectBytes d (x hdr)) at S
  have K : selectedFile p (fun i=>selectBytes d (rawRun x w i)) hdr (side=0) j =
      indexedSample p (selectBytes d (rawRun x w (nextAt hdr j))) (rawSelector d x hdr) side := by
    unfold selectedFile
    rw [S]
    rcases Side with rfl|rfl <;> rfl
  exact congrArg (fun z=>z*p.beta^j) (K.trans I)


theorem snapshot_numbers_now (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Dgt : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (r : Owner h) (x : Raw s n) (First : FirstCut d hh Q G x)
    (w : List (Fin n)) :
    let C := charter G r
    let p := params d s
    let right := nextAt C.root (C.a+C.b)
    let I := ReportItemNineTrace.snapshotInputs d C x
    p.digits≤C.a → p.digits≤C.L-(C.a+C.b) →
    HeldAlong d C.root 0 x w → HeldAlong d right 2 x w →
    reportValue p (fun i=>selectBytes d (rawRun x w i)) C.root true=I.left ∧
    reportValue p (fun i=>selectBytes d (rawRun x w i)) right false=I.right := by
  let a := Classical.choose (G.gaps r.val r.property)
  have A := Classical.choose_spec (G.gaps r.val r.property)
  let b := Classical.choose (G.gaps (nextAt r.val a) A.2.2.atEnd)
  have B := Classical.choose_spec (G.gaps (nextAt r.val a) A.2.2.atEnd)
  let c := Classical.choose (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  have C := Classical.choose_spec (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  dsimp only
  intro L R H0 H2
  change (params d s).digits≤a at L
  change (params d s).digits≤a+b+c-(a+b) at R
  have RR : (params d s).digits≤c := by omega
  have H2' : HeldAlong d (nextAt (nextAt r.val a) b) 2 x w := by
    change HeldAlong d (nextAt r.val (a+b)) 2 x w at H2
    rwa [nextAt_add] at H2
  have LL := value_on_held_tape d N hh G F Dgt Rail x First r.val r.property a A.2.2 L 0
    (.inl rfl) w H0
  have V := value_on_held_tape d N hh G F Dgt Rail x First
    (nextAt (nextAt r.val a) b) B.2.2.atEnd c C.2.2 RR 2 (.inr rfl) w H2'
  refine ⟨LL,?_⟩
  change reportValue (params d s) (fun i=>selectBytes d (rawRun x w i))
    (nextAt r.val (a+b)) false =
    reportValue (params d s) (fun i=>selectBytes d (x i)) (nextAt r.val (a+b)) false
  rw [nextAt_add]
  exact V

#print axioms snapshot_numbers_now
#print axioms selector_on_held_tape
#print axioms value_on_held_tape
end L4.ReportProtectedRebase
