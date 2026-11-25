import Leader.L4.ReportGuardedTailSuccess
import Leader.L4.ReportSealReverse

namespace L4.ReportGuardedTailFrameTape
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportPrelaunchClock ReportOwnerForwardControl ReportOwnerForwardLocations
open ReportOwnerReverseControl ReportOwnerReverseShape ReportByteRows ReportLeaseOwner
open ReportGenerationAncestry ReportIngressOwnership ReportGuardedTailSuccess
open ReportOwnerAcquireProvenance (BeforeConsume)
open ReportSealReverse ReportSealCommitOrigin
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem writerfree_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (A : CentreWriterFree d C x w)
    (B : CentreWriterFree d C (rawRun x w) [e]) : CentreWriterFree d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact B
  | cons a w IH => exact ⟨A.1,A.2.1,IH _ A.2.2 B⟩

private theorem rev_notF (d : Sheet) (C : Chart h) (x : Raw s n)
    (k i : Nat) (R : ReverseWait d C x k) (I : i<C.L) :
    (tok d C x i).tag≠2 := by
  rw [R.2.2 i I]
  unfold backTag
  split <;> try decide
  split <;> decide

theorem seal_reverse_writerfree (d : Sheet) (N : 1<n) (G : GapInput h)
    (r : Owner h) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (R : SealD d (charter G r) x k) (w : List (Fin n))
    (B : BeforeConsume d (charter G r) x w) :
    CentreWriterFree d (charter G r) x w := by
  let C := charter G r
  obtain ⟨Pos,K,_,_,_⟩ := canonical_centre G r
  change C.a<C.L at K
  have K0 : C.a-1<C.L := by omega
  induction B with
  | nil => trivial
  | @snoc w e B NC IH =>
    obtain ⟨_,j,_,D⟩ := seal_reverse_run d C hh G F N x X k R digit w B
    exact writerfree_snoc d C x w e IH
      ⟨fun _=>.inr (rev_notF d C _ j C.a D.shape K),
       fun _=>.inr (rev_notF d C _ j (C.a-1) D.shape K0),trivial⟩

private theorem front_notF (d : Sheet) (C : Chart h) (x : Raw s n)
    (k i : Nat) (R : ForwardWait d C x k) (I : i<C.L) (H : k≠i) :
    (tok d C x i).tag≠2 := by
  rw [R.2.2 i I]
  unfold frontTag
  split
  · decide
  · rw [if_neg H.symm]
    decide

/-- The actual outward COMMIT prefix reaching its ingress cursor has
not yet fired its writer. This includes unrestricted other marks and
fault fronts, and makes no grant/selector claim by itself. -/
theorem commit_prefix_writerfree (d : Sheet) (N : 1<n) (G : GapInput h)
    (r : Owner h) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok)
    (R : Flight d (charter G r) x 0 t)
    (PC : readPC d (charter G r) x=(2,commitOp (params d s)))
    (O : t.opcode=commitOp (params d s))
    (w : List (Fin n)) (k : Nat)
    (B : BeforeLateIngress d (charter G r) (s:=s) t.opcode w k) :
    CentreWriterFree d (charter G r) x w := by
  let C := charter G r
  let p := params d s
  obtain ⟨Pos,K,_,_,_⟩ := canonical_centre G r
  change C.a<C.L at K
  have K0 : C.a-1<C.L := by omega
  have NotSeal : commitOp p≠sealOp p := by unfold commitOp sealOp; omega
  have witness (u : List (Fin n)) (j : Nat)
      (A : BeforeLateIngress d C (s:=s) t.opcode u j) :
      ForwardWait d C (rawRun x u) j ∧ (readPC d C (rawRun x u)).2=commitOp p := by
    have G0 := late_origin_run d C hh G F N x X t R u j A
    exact ⟨G0.2.1.shape,congrArg Prod.snd (G0.2.2.trans PC)⟩
  induction B with
  | nil => trivial
  | @hold u j e A NE IH =>
    obtain ⟨Old,Op⟩ := witness u j A
    apply writerfree_snoc d C x u e IH
    exact ⟨fun _=>.inl (fun Z => NotSeal (Op.symm.trans Z)), fun E=>.inr
      (front_notF d C _ j (C.a-1) Old K0 (fun EJ=>NE (E.trans (congrArg (out C) EJ).symm))),
      trivial⟩
  | @hop u j A J Guard IH =>
    obtain ⟨Old,Op⟩ := witness u j A
    apply writerfree_snoc d C x u (out C j) IH
    refine ⟨fun _=>.inl (fun Z => NotSeal (Op.symm.trans Z)), fun E=>.inr
      (front_notF d C _ j (C.a-1) Old K0 ?_),trivial⟩
    intro EJ
    subst j
    have Eq : C.a-1+1=C.a := by
      change 0<C.a at Pos
      omega
    apply Guard O
    change h (rightNeighbor (out C (C.a-1)))=true ∧ _ ∧ _
    rw [chart_succ,Eq]
    exact ⟨(canonical_centre G r).2.2.1,(canonical_centre G r).2.2.2.2,
      (canonical_centre G r).2.2.2.1⟩

theorem door_writerfree (d : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) : CentreWriterFree d (charter G r) x [door (charter G r)] := by
  let C := charter G r
  obtain ⟨_,K,_,_,_⟩ := canonical_centre G r
  change C.a<C.L at K
  have K0 : C.a-1<C.L := by omega
  refine ⟨?_,?_,trivial⟩
  · intro H
    exact False.elim (ReportChartPartition.door_not_outgoing C C.a K H)
  · intro H
    exact False.elim (ReportChartPartition.door_not_outgoing C (C.a-1) K0 H)

/-- One arbitrary selected mark after the outward SEAL cursor has
passed centre cannot rewrite the installed seal or selected bank. -/
theorem postcentre_seal_front_writerfree (d : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (k : Nat) (A : (charter G r).a<k)
    (F : ForwardWait d (charter G r) x k)
    (PC : (readPC d (charter G r) x).2=sealOp (params d s))
    (e : Fin n) : CentreWriterFree d (charter G r) x [e] := by
  let C := charter G r
  have I := F.2.1
  have J : C.a<C.L := Nat.lt_trans A I
  have Ne : k≠C.a := by
    change C.a<k at A
    omega
  refine ⟨fun _ => .inr (front_notF d C x k C.a F J Ne), ?_,trivial⟩
  intro _
  left
  rw [PC]
  unfold sealOp commitOp
  omega

end L4.ReportGuardedTailFrameTape
