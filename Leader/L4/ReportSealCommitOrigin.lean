import Leader.L4.ReportSealCommitLaunch
import Leader.L4.ReportWriteOrigin

namespace L4.ReportSealCommitOrigin
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ShortLayerGeometry ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportByteRows
open ReportRawProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerIssueControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportOwnerWriteTransport ReportSealDescriptor
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

structure Flight (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) (t : Tok) : Prop where
  shape : ForwardWait d C x k
  origin : SealCommitForward (params d s) t
  packet : tok d C x k=t ∨ tok d C x k=MISByteCodec.faultToken 2

/-- The sole payload-changing healthy COMMIT branch is the target
header's incoming lane 0→1. SEAL hops never need this exclusion. -/
def BeforeCommitIngress (C : Chart h) (op : Nat) (p : Params) (k : Nat) : Prop :=
  op=commitOp p → ¬(h (rightNeighbor (out C k))=true ∧ C.route.port k=0 ∧ C.route.port (k+1)=1)

private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

private theorem incoming_zero (C : Chart h) (e : Fin n)
    (E : rightNeighbor e=out C 0) : e=door C := by
  unfold door
  have R : out C 0=C.root := rfl
  rw [←R,←E,RearTrace.predecessor_right]

private theorem incoming_succ (C : Chart h) (e : Fin n) (j : Nat)
    (E : rightNeighbor e=out C (j+1)) : e=out C j :=
  ShortChartOwnership.right_injective (E.trans (chart_succ C j).symm)

theorem late_forward_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (t : Tok) (R : Flight d C x k t) (e : Fin n) (A : e≠out C k) :
    tok d C (rawNext s x e) k=tok d C x k := by
  let CF := cached_fibre d N hh Q F
  have I := R.shape.2.1
  have Y := CF.closed x e X
  by_cases H : rightNeighbor e=out C k
  · cases k with
    | zero =>
      have E := incoming_zero C e H
      subst e
      let p := params d s
      let v := selectBytes d (x C.root)
      let t0 := publicationToken p true v 0
      have T : t0.tag=2 := by
        change (publicationToken p true v 0).tag=2
        rw [←root_pub]
        exact (R.shape.2.2 0 C.positive).trans rfl
      have P : sourcePhase p v=2 := R.shape.1.1
      have O : sourceOpcode p v≤commitOp p := R.shape.1.2
      have W := (raw_door_final d C x N (CF.mask x X)).2
      change resetTokenRead p (selectBytes d (rawNext s x (door C) C.root)) 0 =
        (match (source p v t0).2 with
          | none => prelaunchDoorNormWire p v
          | some z => resetTokenWire p z) at W
      rw [prelaunch_wait_hold p v t0 P O (.inr T)] at W
      rw [root_tok,W,rank_root_norm_token,root_pub]
    | succ j =>
      have E := incoming_succ C e j H
      subst e
      let p := params d s
      let u := bytesL d x (out C j)
      let v := bytesR d x (out C j)
      let a := C.route.port j
      let b := C.route.port (j+1)
      have LT : (tok d C x j).tag=1 := by rw [R.shape.2.2 j (by omega)]; simp [frontTag]
      have RT : (tok d C x (j+1)).tag≠3 := by
        rw [R.shape.2.2 (j+1) I]
        simp [frontTag]
      rw [predecessor_projection] at LT
      rw [successor_projection] at RT
      have NR : rankReady p (h (out C j)) u a=false := by
        apply Bool.eq_false_iff.mpr
        intro H0
        have T0 := ((rankReady_iff p (h (out C j)) u a).mp H0).1
        change (publicationToken p (h (out C j)) u a).tag=1 at LT
        rw [LT] at T0
        contradiction
      have W := raw_pair_wire d C x N (CF.mask x X) j
      have E := rank_idle_right p (h (out C j)) (h (rightNeighbor (out C j))) u v a b
        (internal_dest C j I) NR (.inr RT)
      have RP : (publicationToken p (h (rightNeighbor (out C j))) v b).opcode≠admitOp p ∨
          (publicationToken p (h (rightNeighbor (out C j))) v b).fault=true := by
        rw [←successor_projection]
        rcases R.packet with H0|H0
        · left
          rw [H0]
          rcases R.origin.2.1 with O|O <;>
            rw [O] <;> simp only [sealOp, commitOp, admitOp, p] <;> omega
        · right
          rw [H0]
          rfl
      rw [rankToken_wire] at RP
      have Y' := CF.closed x (out C j) X
      have Gate : chartGate d C x (j+1)=rankGate p (h (rightNeighbor (out C j))) v b := by
        change rankGate p (h (out C (j+1))) (bytesL d x (out C (j+1))) b=_
        simp only [bytesL,bytesR,v,chart_succ]
      rw [tok_wire d C (rawNext s x (out C j)),gate_frame d C hh G x _ X Y' (j+1) I,Gate,W.2,workR,E,tok_wire,Gate]
      have NF := rank_nondadmit_norm_token p 2 _ _ (.inl rfl) RP
      simpa only [wire,bytesR,v,b,chart_succ] using NF
  · apply decoded_frame d C hh G x _ X Y k I
    unfold wire
    rw [raw_spectator x e _ (Ne.symm A) (Ne.symm H)]

theorem late_forward_hop (d : Sheet) (C : Chart h)
    (N : 1<n) (x : Raw s n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (J : k+1<C.L) (t : Tok) (R : Flight d C x k t)
    (Before : BeforeCommitIngress C t.opcode (params d s) k) :
    tok d C (rawNext s x (out C k)) (k+1)=t ∨
      tok d C (rawNext s x (out C k)) (k+1)=MISByteCodec.faultToken 2 := by
  rcases R.packet with E|E
  · let p := params d s
    let e := out C k
    let u := bytesL d x e
    let v := bytesR d x e
    let j := C.route.port k
    let l := C.route.port (k+1)
    have W := raw_pair_wire d C x N mask k
    rw [predecessor_projection] at E
    change publicationToken p (h e) u j=t at E
    rw [tok_wire,W.2,workR]
    have T := (seal_commit_hop_pair p (h e) (h (rightNeighbor e)) u v j l
      (internal_dest C k J) (E.symm ▸ R.origin) (chartGate d C (rawNext s x e) (k+1))).2.2
    rw [E] at T
    rw [T]
    rcases R.origin.2.1 with O|O
    · rw [seal_effect_token p _ _ u v j _ _ t O R.origin.2.2.2.2.2.2.1]
      split
      · exact .inr rfl
      · exact .inl rfl
    · rw [commit_effect_token p _ _ u v j l _ t O R.origin.2.2.2.2.2.2.1,
        if_neg (Before O)]
      exact .inl rfl
  · exact .inr (ReportWriteOrigin.fault_cannot_revive_on_hop d C N x mask k J E)

/-- The history counts all original marks, stopping before an
applied-bit-changing ingress (but allowing holds at that cursor). -/
inductive BeforeLateIngress (d : Sheet) (C : Chart h) (op : Nat) :
    List (Fin n) → Nat → Prop
  | nil : BeforeLateIngress d C op [] 0
  | hold {w : List (Fin n)} {k : Nat} (e : Fin n) :
      BeforeLateIngress d C op w k → e≠out C k →
      BeforeLateIngress d C op (w++[e]) k
  | hop {w : List (Fin n)} {k : Nat} :
      BeforeLateIngress d C op w k → k+1<C.L →
      BeforeCommitIngress C op (params d s) k →
      BeforeLateIngress d C op (w++[out C k]) (k+1)

theorem late_origin_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (R : Flight d C x 0 t)
    (w : List (Fin n)) (k : Nat) (H : BeforeLateIngress d C (s:=s) t.opcode w k) :
    Cached d hh Q (rawRun x w) ∧ Flight d C (rawRun x w) k t ∧
      readPC d C (rawRun x w)=readPC d C x := by
  let CF := cached_fibre d N hh Q F
  induction H with
  | nil => exact ⟨X,R,rfl⟩
  | @hold u j e H E IH =>
    rw [ShortOwnerEpochJS.raw_snoc]
    have S := ReportOwnerForwardControl.all_mark d C hh G F N _ IH.1 j IH.2.1.shape e
    rcases S with P|⟨M,_⟩
    · refine ⟨CF.closed _ e IH.1,⟨P,IH.2.1.origin,?_⟩,?_⟩
      · rw [late_forward_hold d C hh G F N _ IH.1 j t IH.2.1 e E]
        exact IH.2.1.packet
      · exact (ReportWriteOrigin.forward_pc_held d C _ e N (CF.mask _ IH.1) j IH.2.1.shape).trans IH.2.2
    · contradiction
  | @hop u j H E Before IH =>
    rw [ShortOwnerEpochJS.raw_snoc]
    have K := late_forward_hop d C N (rawRun x u) (CF.mask _ IH.1) j E t IH.2.1 Before
    have M := ReportOwnerForwardControl.all_mark d C hh G F N _ IH.1 j IH.2.1.shape (out C j)
    have PC := ReportWriteOrigin.forward_pc_held d C _ (out C j) N (CF.mask _ IH.1) j IH.2.1.shape
    rcases M with P|⟨_,P|⟨F0,_⟩⟩
    · have T := P.2.2 (j+1) E
      rcases K with K|K
      · rw [K,IH.2.1.origin.1] at T
        simp [frontTag,show ¬j+1<j by omega] at T
      · rw [K] at T
        simp [MISByteCodec.faultToken,frontTag,show ¬j+1<j by omega] at T
    · exact ⟨CF.closed _ (out C j) IH.1,⟨P,IH.2.1.origin,K⟩,PC.trans IH.2.2⟩
    · omega

/-- A healthy token at the final old cursor carries the exact issuing
descriptor. For COMMIT that token is still unapplied, even if the
current right guard is about to accept it. -/
theorem healthy_late_origin_from_issue (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (op : Nat) (Op : op=sealOp (params d s) ∨ op=commitOp (params d s))
    (P : readPC d C x=(1,op))
    (Good : comparisonFile (params d s) (selectBytes d (x C.root))/4≠3 ∧
      comparisonFile (params d s) (selectBytes d (x C.root))%4≠3)
    (w : List (Fin n)) (j : Nat) (H : BeforeLateIngress d C (s:=s) op w j)
    (Healthy : (tok d C (rawRun (rawNext s x (door C)) w) j).fault=false) :
    let y := rawRun (rawNext s x (door C)) w
    Cached d hh Q y ∧ ForwardWait d C y j ∧ readPC d C y=(2,op) ∧
      tok d C y j=({tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (x C.root))}:Tok) := by
  dsimp only
  let t : Tok := {tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (x C.root))}
  obtain ⟨Y,S,PC,Eq,_⟩ := ReportSealCommitLaunch.launch d C hh G F N x X I op Op P Good
  have Origins := late_origin_run d C hh G F N _ Y t ⟨S,ReportSealCommitLaunch.descriptor_forward _ _ op Op,.inl Eq⟩ w j H
  refine ⟨Origins.1,Origins.2.1.shape,Origins.2.2.trans PC,?_⟩
  rcases Origins.2.1.packet with K|K
  · exact K
  · rw [K] at Healthy
    contradiction

#print axioms late_origin_run
#print axioms healthy_late_origin_from_issue
#print axioms late_forward_hold
#print axioms late_forward_hop
end L4.ReportSealCommitOrigin
