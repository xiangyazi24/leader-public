import Leader.L4.ReportOwnerWriteTransport
import Leader.L4.ReportOwnerIssueControl
import Leader.L4.ReportWriterPayload

namespace L4.ReportWriteOrigin
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ShortLayerGeometry ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportByteRows
open ReportRawProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerIssueControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportOwnerWriteTransport
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def HealthyWrite (p : Params) (t : Tok) : Prop :=
  t.tag=2 ∧ t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p

structure WriteF (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) (t : Tok) : Prop where
  shape : ForwardWait d C x k
  origin : HealthyWrite (params d s) t
  packet : tok d C x k=t ∨ tok d C x k=MISByteCodec.faultToken 2

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

theorem write_forward_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (t : Tok) (R : WriteF d C x k t) (e : Fin n) (A : e≠out C k) :
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
          have L : writeOp p≤t.opcode := R.origin.2.2.1
          unfold writeOp admitOp at *
          omega
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

theorem write_forward_hop (d : Sheet) (C : Chart h)
    (N : 1<n) (x : Raw s n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (J : k+1<C.L) (t : Tok) (R : WriteF d C x k t) :
    tok d C (rawNext s x (out C k)) (k+1)=t ∨
      tok d C (rawNext s x (out C k)) (k+1)=MISByteCodec.faultToken 2 := by
  have RD : readyAt d C x k=true := by
    unfold readyAt
    rw [rankReady_iff,←predecessor_projection]
    rcases R.packet with E|E
    · rw [E]
      refine ⟨R.origin.1,?_⟩
      intro S
      have L := R.origin.2.2.1
      have K := S.1.2.2
      unfold healthyAdmit at S
      change t.opcode=admitOp (params d s) at K
      unfold writeOp admitOp at *
      omega
    · rw [E]
      simp [MISByteCodec.faultToken,healthyAdmit]
  rcases R.packet with E|E
  · have W := write_hop d C x N mask k J RD
      (by rw [E]; exact R.origin.2.1)
      (by rw [E]; exact R.origin.2.2.1)
      (by rw [E]; exact R.origin.2.2.2)
    rcases W with H|⟨_,H⟩
    · exact .inl (H.trans E)
    · exact .inr H
  · right
    have W := raw_pair_wire d C x N mask k
    rw [predecessor_projection] at E
    rw [tok_wire,W.2]
    exact rank_fault2_hop (params d s) (h (out C k)) (h (rightNeighbor (out C k)))
      (bytesL d x (out C k)) (bytesR d x (out C k)) _ _ (internal_dest C k J) E _

#print axioms write_forward_hold
#print axioms write_forward_hop

theorem write_launch (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (t : Tok) (P : sourcePhase (params d s) (selectBytes d (x C.root))=1)
    (L : writeOp (params d s)≤sourceOpcode (params d s) (selectBytes d (x C.root)))
    (U : sourceOpcode (params d s) (selectBytes d (x C.root))<sealOp (params d s))
    (S : (source (params d s) (selectBytes d (x C.root))
      (publicationToken (params d s) true (selectBytes d (x C.root)) 0)).2=some t)
    (T0 : t.tag=2) :
    WriteF d C (rawNext s x (door C)) 0 t := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let y := rawNext s x (door C)
  let old := publicationToken p true v 0
  let CF := cached_fibre d N hh Q F
  have W := (raw_door_final d C x N (CF.mask x X)).2
  change resetTokenRead p (selectBytes d (y C.root)) 0 =
    (match (source p v old).2 with
      | none => prelaunchDoorNormWire p v
      | some t => resetTokenWire p t) at W
  rw [S] at W
  have A : tok d C y 0=t := by
    rw [root_tok,W]
    exact rank_write_issue_roundtrip p v old t P L U S T0 false
  have O := ReportWriterPayload.issue_write_banks p v old t P L U S T0
  have Good : HealthyWrite p t := ⟨T0,O.2.2.1,by rwa [O.2.1],by rwa [O.2.1]⟩
  rcases ReportOwnerIssueControl.door_step d C hh G F N x X I with B|⟨B,J⟩
  · have Z := B.2.2 0 C.positive
    rw [A,T0] at Z
    contradiction
  · exact ⟨B,Good,.inl A⟩

theorem write_follows_forward (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (t : Tok) (R : WriteF d C x k t) (e : Fin n) :
    let y := rawNext s x e
    WriteF d C y k t ∨ (e=out C k ∧
      (WriteF d C y (k+1) t ∨ (k+1=C.L ∧ ReverseWait d C y k))) := by
  dsimp only
  have A := ReportOwnerForwardControl.all_mark d C hh G F N x X k R.shape e
  by_cases E : e=out C k
  · subst e
    rcases A with P|⟨E,P|⟨E0,P⟩⟩
    · -- An actual ready local WRITE or its fault never remains at k.
      have RD : readyAt d C x k=true := by
        unfold readyAt
        rw [rankReady_iff,←predecessor_projection]
        rcases R.packet with U|U
        · rw [U]
          refine ⟨R.origin.1,?_⟩
          intro H
          have L := R.origin.2.2.1
          have A := H.1.2.2
          change t.opcode=admitOp (params d s) at A
          unfold writeOp admitOp at *
          omega
        · rw [U]; simp [MISByteCodec.faultToken,healthyAdmit]
      have CF := cached_fibre d N hh Q F
      by_cases J : k+1<C.L
      · have K := (ready_locations d C x N (CF.mask x X) k J RD).1
        have V := P.2.2 k R.shape.2.1
        rw [K] at V
        simp [frontTag,MISByteCodec.T] at V
      · have K := ready_turn_tag d C x N (CF.mask x X) k (by have := R.shape.2.1; omega) RD
        have V := P.2.2 k R.shape.2.1
        rw [K] at V
        simp [frontTag] at V
    · exact .inr ⟨E,.inl ⟨P,R.origin,write_forward_hop d C N x
        ((cached_fibre d N hh Q F).mask x X) k P.2.1 t R⟩⟩
    · exact .inr ⟨E,.inr ⟨E0,P⟩⟩
  · rcases A with P|⟨B,_⟩
    · exact .inl ⟨P,R.origin,by rw [write_forward_hold d C hh G F N x X k t R e E]; exact R.packet⟩
    · contradiction

/-- Actual original-tape prefix before this WRITE's terminal turn.
Its cursor always steps along an old chart occurrence. No token/file
claim is supplied by the caller. -/
inductive BeforeWriteTurn (d : Sheet) (C : Chart h) (x : Raw s n) :
    List (Fin n) → Nat → Prop
  | nil : BeforeWriteTurn d C x [] 0
  | hold {w : List (Fin n)} {k : Nat} (e : Fin n) :
      BeforeWriteTurn d C x w k → e≠out C k → BeforeWriteTurn d C x (w++[e]) k
  | hop {w : List (Fin n)} {k : Nat} :
      BeforeWriteTurn d C x w k → k+1<C.L → BeforeWriteTurn d C x (w++[out C k]) (k+1)

theorem write_origin_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (R : WriteF d C x 0 t)
    (w : List (Fin n)) (k : Nat) (H : BeforeWriteTurn d C x w k) :
    Cached d hh Q (rawRun x w) ∧ WriteF d C (rawRun x w) k t := by
  let CF := cached_fibre d N hh Q F
  induction H with
  | nil => exact ⟨X,R⟩
  | @hold u j e H E IH =>
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨CF.closed _ e IH.1,?_⟩
    rcases write_follows_forward d C hh G F N _ IH.1 j t IH.2 e with P|⟨F0,_⟩
    · exact P
    · contradiction
  | @hop u j H E IH =>
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨CF.closed _ (out C j) IH.1,?_⟩
    rcases write_follows_forward d C hh G F N _ IH.1 j t IH.2 (out C j) with P|⟨_,P|⟨F0,_⟩⟩
    · have Q := write_forward_hop d C N (rawRun x u) (CF.mask _ IH.1) j E t IH.2
      have T := P.shape.2.2 (j+1) E
      rcases Q with Q|Q
      · rw [Q,IH.2.origin.1] at T
        simp [frontTag,show ¬j+1<j by omega] at T
      · rw [Q] at T
        simp [MISByteCodec.faultToken,frontTag,show ¬j+1<j by omega] at T
    · exact P
    · omega

theorem healthy_write_origin_of_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (R : WriteF d C x 0 t)
    (w : List (Fin n)) (k : Nat) (H : BeforeWriteTurn d C x w k)
    (Live : (tok d C (rawRun x w) k).fault=false) :
    tok d C (rawRun x w) k=t := by
  have O := (write_origin_run d C hh G F N x X t R w k H).2.packet
  rcases O with P|P
  · exact P
  · rw [P] at Live
    contradiction

#print axioms write_launch
#print axioms write_follows_forward
#print axioms write_origin_run
#print axioms healthy_write_origin_of_run

theorem forward_pc_held (d : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (R : ForwardWait d C x k) :
    readPC d C (rawNext s x e)=readPC d C x := by
  by_cases E : e=door C
  · subst e
    have Tag : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
      rw [R.2.2 0 C.positive]
      by_cases K : k=0
      · subst k; exact .inr rfl
      · exact .inl (by simp [frontTag,show 0<k by omega])
    rw [root_pub] at Tag
    exact (raw_door_final d C x N mask).1.trans
      (prelaunch_hold_controls (params d s) _ _ R.1.1 R.1.2 Tag)
  · exact raw_nondoor_control d C x e N mask E

/-- Cursor motion and holds on the genuine WRITE flight do not change
the original source opcode; failure remains represented by fault2. -/
theorem write_origin_pc (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (R : WriteF d C x 0 t)
    (w : List (Fin n)) (k : Nat) (H : BeforeWriteTurn d C x w k) :
    readPC d C (rawRun x w)=readPC d C x := by
  let CF := cached_fibre d N hh Q F
  induction H with
  | nil => rfl
  | @hold u j e H E IH =>
    have A := write_origin_run d C hh G F N x X t R u j H
    rw [ShortOwnerEpochJS.raw_snoc]
    exact (forward_pc_held d C _ e N (CF.mask _ A.1) j A.2.shape).trans IH
  | @hop u j H E IH =>
    have A := write_origin_run d C hh G F N x X t R u j H
    rw [ShortOwnerEpochJS.raw_snoc]
    exact (forward_pc_held d C _ (out C j) N (CF.mask _ A.1) j A.2.shape).trans IH

#print axioms forward_pc_held
#print axioms write_origin_pc

theorem fault_cannot_revive_on_hop (d : Sheet) (C : Chart h)
    (N : 1<n) (x : Raw s n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (J : k+1<C.L)
    (E : tok d C x k=MISByteCodec.faultToken 2) :
    tok d C (rawNext s x (out C k)) (k+1)=MISByteCodec.faultToken 2 := by
  have W := raw_pair_wire d C x N mask k
  rw [predecessor_projection] at E
  rw [tok_wire,W.2]
  exact rank_fault2_hop (params d s) (h (out C k)) (h (rightNeighbor (out C k)))
    (bytesL d x (out C k)) (bytesR d x (out C k)) _ _ (internal_dest C k J) E _

/-- A healthy endpoint on the actual forward flight refers to the exact
token emitted by the literal ISSUE. The source opcode is unchanged. -/
theorem healthy_origin_from_issue (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (t : Tok) (P : sourcePhase (params d s) (selectBytes d (x C.root))=1)
    (L : writeOp (params d s)≤sourceOpcode (params d s) (selectBytes d (x C.root)))
    (U : sourceOpcode (params d s) (selectBytes d (x C.root))<sealOp (params d s))
    (S : (source (params d s) (selectBytes d (x C.root))
      (publicationToken (params d s) true (selectBytes d (x C.root)) 0)).2=some t)
    (T0 : t.tag=2)
    (w : List (Fin n)) (k : Nat)
    (H : BeforeWriteTurn d C (rawNext s x (door C)) w k)
    (Live : (tok d C (rawRun (rawNext s x (door C)) w) k).fault=false) :
    let y := rawRun (rawNext s x (door C)) w
    tok d C y k=t ∧ (readPC d C y).2=(readPC d C x).2 := by
  let x' := rawNext s x (door C)
  have X' := (cached_fibre d N hh Q F).closed x (door C) X
  have A := write_launch d C hh G F N x X I t P L U S T0
  have PC : (readPC d C x').2=(readPC d C x).2 := by
    rcases ReportOwnerIssueControl.door_step d C hh G F N x X I with R|⟨_,R⟩
    · have Z := R.2.1
      have Y := A.shape.1.1
      rw [Y] at Z
      contradiction
    · exact R
  exact ⟨healthy_write_origin_of_run d C hh G F N x' X' t A w k H Live,
    (congrArg Prod.snd (write_origin_pc d C hh G F N x' X' t A w k H)).trans PC⟩

#print axioms fault_cannot_revive_on_hop
#print axioms healthy_origin_from_issue
end L4.ReportWriteOrigin
