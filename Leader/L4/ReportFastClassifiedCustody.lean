import Leader.L4.ReportFastRawEvent
import Leader.L4.ReportCurrentCustodyCut
import Leader.L4.ReportIngressOwnership
import Leader.L4.ReportItemNineActualPublication

namespace L4.ReportFastClassifiedCustody
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportGenerationAncestry ReportIngressOwnership ReportLeaseOwner
open ReportPrelaunchAllOwners ReportFastRawEvent WidthOrdinalSpan BStarH6Ordinal
open ReportGoodEightCut ReportCurrentCustodyCut

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem centre_covers_lower_header (hh : ∃ i,h i=true) (G : GapInput h)
    (i : Fin n) (H : h (rightNeighbor i)=true) :
    ∃ r : Owner h,rightNeighbor i=centre (charter G r) := by
  obtain ⟨B,D⟩ := last_gap h hh i H
  let r : Owner h := ⟨back i (ordinal h hh i),B⟩
  let a := Classical.choose (G.gaps r.val r.property)
  have A := Classical.choose_spec (G.gaps r.val r.property)
  have Len : a=ordinal h hh i+1 := gap_unique A.2.2 D
  refine ⟨r,?_⟩
  change rightNeighbor i=nextAt r.val a
  rw [Len]
  change rightNeighbor i=rightNeighbor (nextAt r.val (ordinal h hh i))
  rw [show nextAt r.val (ordinal h hh i)=i from nextAt_back i (ordinal h hh i)]

theorem commit_guard_is_ancestry (p : Params) (hu : Bool) (u v : BitVec p.w)
    (G : CommitGuard p hu u v (oldReportToken p hu u 0).payload) :
    ancestryCommitOpportunity p hu true u v := by
  let t := publicationToken p hu u 0
  let val := (oldReportToken p hu u 0).payload
  obtain ⟨T,A,B,C⟩ := G
  have Eq : t=({tag:=2,opcode:=commitOp p,payload:=val}:Tok) := T
  have Ready : rankReady p hu u 0=true := by
    apply (rankReady_iff p hu u 0).mpr
    rw [show publicationToken p hu u 0=t from rfl,Eq]
    refine ⟨rfl,?_⟩
    intro Bad
    have E := Bad.1.2.2
    change commitOp p=admitOp p at E
    unfold commitOp admitOp at E
    omega
  refine ⟨rfl,Ready,?_,?_,?_⟩
  · change t.fault=false
    rw [Eq]
  · change t.opcode=commitOp p
    rw [Eq]
  · change packetCommitGuard p v t=true
    rw [Eq]
    change ((!false) && reportOldGrant p v 1 && (publicationSelector p v==val/8) &&
      (reportOldSeal p v==some val))=true
    change reportOldGrant p v 1=true at A
    change publicationSelector p v=val/8 at B
    change reportOldSeal p v=some val at C
    simp [A,B,C]

/-- Rectifies a raw observer label to the unique owner layout and to
the exact semantic acceptance used by item 9. This step uses the
fixed lower cache, not a supposed published value or future liveness. -/
theorem classified_owner_guard (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (x : Raw s n)
    (A : CurrentCustodyCut d hh Q G x) (e : Fin n) (j : Owner h)
    (K : classify d h x e=some j) :
    ∃ r : Owner h, centre (charter G r)=j.val ∧
      rightNeighbor e=centre (charter G r) ∧
      ancestryCommitOpportunity (params d s) (h e) true (selectBytes d (x e))
        (selectBytes d (x (centre (charter G r)))) := by
  obtain ⟨J,_,Commit⟩ := (classify_iff d h x e j).mp K
  have H : h (rightNeighbor e)=true := J.symm ▸ j.property
  obtain ⟨r,E⟩ := centre_covers_lower_header hh G e H
  have X : Cached d hh Q x := A.1.1.2.1.1.1.1
  have Mask := (cached_fibre d N hh Q F).mask x X
  rw [Mask e] at Commit
  refine ⟨r,E.symm.trans J,E,?_⟩
  rw [←E]
  exact commit_guard_is_ancestry _ _ _ _ Commit

#print axioms centre_covers_lower_header
#print axioms commit_guard_is_ancestry
#print axioms classified_owner_guard
end L4.ReportFastClassifiedCustody

namespace L4.ReportFastClassifiedCustody
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportGenerationAncestry ReportIngressOwnership ReportLeaseOwner
open ReportFastRawEvent ReportGoodEightCut ReportCurrentCustodyCut
open ReportItemNineActualPublication ReportItemNineTrace ReportDigitArithmetic ReportStaticSpacing
open ReportOwnerIssueControl ReportPrelaunchClock ReportOwnerDoorProjection
open ReportOwnerAcquireReturn
open ReportOwnerAcquireProvenance (BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- A raw classified publication in the closed custody region has a
real own ACQ and the exact semantic write at the classified target.
This is the soundness of credit, not its probability or rate. -/
theorem classified_publication (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h,
      let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
        (params d s).digits≤C.L-(C.a+C.b))
    (x : Raw s n) (A : CurrentCustodyCut d hh Q G x)
    (e : Fin n) (j : Owner h) (Ev : classify d h x e=some j) :
    let p := params d s
    ∃ r : Owner h, ∃ issue : Raw s n, ∃ flight post : List (Fin n),
      let C := charter G r
      let start := rawNext s issue (door C)
      let old := rawRun start flight
      let b := rawNext s old (door C)
      let I := snapshotInputs d C b
      let y := fun i=>selectBytes d (rawNext s x e i)
      centre C=j.val ∧ FirstCut d hh Q G issue ∧
      LegalIssue d C issue ∧ readPC d C issue=(1,acqOp p) ∧
      BeforeConsume d C start flight ∧ (tok d C old 0).tag=3 ∧
      (tok d C old 0).outcome≠1 ∧
      x=rawRun b post ∧ NoRestartTape d C b post ∧
      publicationSelector p (y j.val)=1-I.prior ∧
      publicationSelector p (y j.val)≠publicationSelector p (selectBytes d (x j.val)) ∧
      reportValue p y j.val true=updateDist p.radius I.leftRoot I.left ∧
      reportValue p y j.val false=updateDist p.radius I.rightRoot I.right ∧
      publicationPair p (y j.val) (publicationSelector p (y j.val))=
        2*(decide (reportValue p y j.val true<p.radius)).toNat+
          (decide (reportValue p y j.val false<p.radius)).toNat ∧
      publicationA p (y j.val) (publicationSelector p (y j.val))=
        Z p (selectBytes d (x j.val)) := by
  dsimp only
  obtain ⟨r,J,Arr,Guard⟩ := classified_owner_guard d N hh G F x A e j Ev
  obtain ⟨L,M,R⟩ := Width r
  obtain ⟨issue,flight,post,B,I,PC,T,Tag,ND,W,NR,_,Rest⟩ :=
    publication_at_current_cut d N Spos hh G F r x A L M R e Arr Guard
  refine ⟨r,issue,flight,post,J,B,I,PC,T,Tag,ND,W,NR,?_⟩
  rw [←J]
  exact Rest

#print axioms classified_publication
end L4.ReportFastClassifiedCustody
