import Leader.L4.ReportReaderWordLease
import Leader.L4.ReportIngressOwnership

namespace L4.ReportReaderWordOwner
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportByteRows
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners ReportLeaseOwner
open ReportGenerationAncestry ReportOwnerProvenanceTransport ReportReaderWordLease
open ShortChartOwnership ShortLayerGeometry WidthOrdinalSpan BStarH6Ordinal

variable {s n : Nat} {h : Fin n→Bool}

private theorem same_start {u v : Fin n} (m : Nat)
    (E : nextAt u m=nextAt v m) : u=v := by
  induction m with
  | zero => exact E
  | succ k ih => exact ih (ShortChartOwnership.right_injective E)

theorem canonical_middle_offset (hh : ∃ i,h i=true) (G : GapInput h)
    (r : Owner h) (k : Nat) (Lane : (charter G r).route.port k=1) :
    let C := charter G r
    let m := k-C.a
    m<C.b ∧ out C k=nextAt (centre C) m ∧ ordinal h hh (out C k)=m := by
  unfold charter ownerChart at Lane ⊢
  dsimp only
  let a := Classical.choose (G.gaps r.val r.property)
  have A := Classical.choose_spec (G.gaps r.val r.property)
  let b := Classical.choose (G.gaps (nextAt r.val a) A.2.2.atEnd)
  have B := Classical.choose_spec (G.gaps (nextAt r.val a) A.2.2.atEnd)
  change ShortResetChart.lane a b k=1 at Lane
  change k-a<b ∧ nextAt r.val k=nextAt (nextAt r.val a) (k-a) ∧
    ordinal h hh (nextAt r.val k)=k-a
  obtain ⟨L,R⟩ := (lane1 a b k).mp Lane
  have E : nextAt r.val k=nextAt (nextAt r.val a) (k-a) := by
    conv => lhs; rw [show k=a+(k-a) by omega]
    exact nextAt_add r.val a (k-a)
  have T : k-a<b := by omega
  exact ⟨T,E,E ▸ ReportChartPartition.ordinal_at_offset hh A.2.2.atEnd B.2.2 (k-a) T⟩

/-- The old lane 1 token at a reached word site belongs to a chart
whose centre is this word's header, including across physical wrap. -/
theorem lane1_owner_centre (hh : ∃ i,h i=true) (G : GapInput h)
    (r : Owner h) (k : Nat) (Lane : (charter G r).route.port k=1)
    {hdr : Fin n} (Hdr : h hdr=true) {len off : Nat} (Gap : Gap h hdr len)
    (Off : off<len) (Site : out (charter G r) k=nextAt hdr off) :
    centre (charter G r)=hdr := by
  obtain ⟨_,E,A⟩ := canonical_middle_offset hh G r k Lane
  have B := ReportChartPartition.ordinal_at_offset hh Hdr Gap off Off
  have sameOff : off=k-(charter G r).a := B.symm.trans (Site ▸ A)
  have L : nextAt (centre (charter G r)) off=nextAt hdr off := by
    rw [←Site]
    rw [sameOff]
    exact E.symm
  exact same_start off L

/-- Given per-owner epochs, the enabled-writer condition of the
reader's word lease is supplied by the unique actual writer's epoch.
It is not required as a separate field of the reader's epoch. -/
theorem nonheader_writer_safe_of_epochs (sheet : Sheet)
    (hh : ∃ i,h i=true) (G : GapInput h) {Q : Raw s n→Prop}
    (x : Raw s n) (e hdr : Fin n) (Hdr : h hdr=true)
    {len off : Nat} (Gap : Gap h hdr len) (Off : off<len)
    (H : h (nextAt hdr off)=false)
    (epochs : ∀ r : Owner h,∃ g,GenerationInv sheet (charter G r) hh Q x g) :
    NonheaderWriterSafe sheet x hdr (nextAt hdr off) e := by
  intro E
  subst e
  let i := nextAt hdr off
  let p := params sheet s
  let u := selectBytes sheet (x i)
  let t := publicationToken p false u 1
  change rankReady p false u 1=true → t.fault=false →
    writeOp p≤t.opcode → t.opcode<sealOp p → reportOldOffset p false u=t.opcode-writeOp p →
    ancestryWriteTarget p t≠rawSelector sheet x hdr
  intro Ready Live Lower Upper _
  obtain ⟨r,k,K,F,_⟩ := unique_cell hh G i 1
  have Pos : out (charter G r) k=i := congrArg Prod.fst F
  have Lane : (charter G r).route.port k=1 := congrArg Prod.snd F
  have Same := lane1_owner_centre hh G r k Lane Hdr Gap Off Pos
  obtain ⟨g,Epoch⟩ := epochs r
  have T : tok sheet (charter G r) x k=t := by
    rw [predecessor_projection,Pos,Lane,H]
    rfl
  have W : WriteCommand p (tok sheet (charter G r) x k) := by
    rw [T]
    exact ⟨((rankReady_iff p false u 1).mp Ready).1,Live,Lower,Upper⟩
  have D := (generated_write_inactive sheet _ hh Q x g Epoch k K W).2
  rw [T,Same] at D
  exact D

#print axioms canonical_middle_offset
#print axioms lane1_owner_centre
#print axioms nonheader_writer_safe_of_epochs
end L4.ReportReaderWordOwner
