import Leader.L4.ReportFastPreACQTrack
import Leader.L4.ReportFastAcqMapped
import Leader.L4.ReportFastNoRearm
import Leader.L4.ReportFastPrepMapping
import Leader.L4.ReportAdaptiveRank

namespace L4.ReportFastEarlyPacket
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl ReportOwnerReverseShape
open ReportOwnerReverseControl ReportOwnerIssueControl ReportOwnerSerial ReportOwnerCommandRail
open ReportByteRows ReportRawProjection ReportFastGateRaw ReportFastNoRearm
open ReportFastOwnerSupport ReportFastFreshReset ReportFastNominationBridge
open ReportFastPreACQTrack ReportAdaptiveFibre ReportFastKernel
open ReportFastPrepMapping ReportFastSteeringMap ReportFastDenySteering
open ReportFastRefractory ReportGateGeometry

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

def EarlyData (p : Params) (g a k q r : Nat) : Prop :=
  (a<admitOp p ∧ q=0 ∧ r=0) ∨
  (a=admitOp p ∧ k<g ∧ q=0 ∧ r=0) ∨
  (a=admitOp p ∧ k=g ∧ q=0 ∧ (r=1 ∨ r=3 ∨ r=5)) ∨
  (a=admitOp p ∧ g<k ∧ q=1 ∧ r=0)

inductive EarlyPacket (d : Sheet) (C : Chart h) (x : Raw s n) : Prop where
  | issue (a : Nat) (A : 0<a) (B : a≤admitOp (params d s))
      (PC : readPC d C x=(1,a))
  | fwd (a k q r : Nat) (A : 0<a) (B : a≤admitOp (params d s))
      (K : k<C.L) (PC : readPC d C x=(2,a))
      (D : EarlyData (params d s) (C.a+2) a k q r)
      (T : tok d C x k=earlyF a q r)
  | rev (a k : Nat) (A : 0<a) (B : a≤admitOp (params d s))
      (K : k<C.L) (PC : readPC d C x=(2,a))
      (T : tok d C x k=earlyD a (earlyQ (params d s) a))
  | acq (PC : AtACQIssue d C x)

def WinAllowed (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  healthyAdmit (params d s) (tok d C x (C.a+2)) →
    (tok d C x (C.a+2)).race=1 → e≠out C (C.a+1)

private theorem gate_off (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (K : k<C.L) (H : k≠C.a+2) : chartGate d C x k=false := by
  apply Bool.eq_false_iff.mpr
  intro E
  exact H (((gate_geometry d C hh G (Q:=Q)).2.2 x X k K).mp E)

private theorem root_pub_early (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true
      (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

private theorem fwd_shape (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (k : Nat) (K : k<C.L)
    (T : (tok d C x k).tag=2) : ForwardWait d C x k := by
  rcases S with A|⟨j,A⟩|⟨j,A⟩
  · have Z := A.2.2 k K
    rw [T] at Z
    contradiction
  · have Z := A.2.2 k K
    rw [T] at Z
    by_cases E : k=j
    · subst j
      exact A
    · by_cases L : k<j <;> simp [frontTag,L,E] at Z
  · have Z := A.2.2 k K
    rw [T] at Z
    by_cases E : k=j <;> by_cases L : k<j <;> simp [backTag,L,E] at Z

private theorem rev_shape (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (k : Nat) (K : k<C.L)
    (T : (tok d C x k).tag=3) : ReverseWait d C x k := by
  rcases S with A|⟨j,A⟩|⟨j,A⟩
  · have Z := A.2.2 k K
    rw [T] at Z
    contradiction
  · have Z := A.2.2 k K
    rw [T] at Z
    by_cases E : k=j <;> by_cases L : k<j <;> simp [frontTag,L,E] at Z
  · have Z := A.2.2 k K
    rw [T] at Z
    by_cases E : k=j
    · subst j
      exact A
    · by_cases L : k<j <;> simp [backTag,L,E] at Z

private theorem root_pc_hold (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (P : LegalWait d C x)
    (T : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2) :
    readPC d C (rawNext s x (door C))=readPC d C x := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have TE : tok d C x 0=t := root_pub_early d C x
  have R := prelaunch_hold_controls p v t P.1 P.2 (TE ▸ T)
  have W := raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)
  exact W.1.trans R

private theorem wait_pc_hold (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (P : LegalWait d C x) (e : Fin n)
    (H : e=door C → (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2) :
    readPC d C (rawNext s x e)=readPC d C x := by
  by_cases E : e=door C
  · subst e
    exact root_pc_hold d C N hh F x X P (H rfl)
  · exact raw_nondoor_control d C x e N
      ((cached_fibre d N hh Q F).mask x X) E

private theorem fwd_root_hold_tag (d : Sheet) (C : Chart h)
    (x : Raw s n) (k : Nat) (R : ForwardWait d C x k) :
    (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
  rw [R.2.2 0 C.positive]
  by_cases E : k=0
  · subst k
    exact .inr (by simp [frontTag])
  · exact .inl (by simp [frontTag,show 0<k by omega])

private theorem rev_root_hold_tag (d : Sheet) (C : Chart h)
    (x : Raw s n) (k : Nat) (R : ReverseWait d C x k) (K : 0<k) :
    (tok d C x 0).tag=1 := by
  rw [R.2.2 0 C.positive]
  simp [backTag,K]

private theorem root_spectator_early (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n)
    (A : e≠door C) (B : e≠out C 0) :
    tok d C (rawNext s x e) 0=tok d C x 0 := by
  have Y := (cached_fibre d N hh Q F).closed x e X
  apply decoded_frame d C hh G x _ X Y 0 C.positive
  unfold wire
  have R : out C 0≠rightNeighbor e := by
    intro E
    apply A
    unfold door
    have Z : out C 0=C.root := rfl
    rw [←Z,E,RearTrace.predecessor_right]
  rw [ReportRawProjection.raw_spectator x e _ (Ne.symm B) R]

private theorem raw_issue_early (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (a : Nat)
    (A : 0<a) (B : a≤admitOp (params d s))
    (PC : readPC d C x=(1,a)) :
    let y := rawNext s x (door C)
    readPC d C y=(2,a) ∧ tok d C y 0=earlyF a 0 0 := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have P : sourcePhase p v=1 := congrArg Prod.fst PC
  have O : sourceOpcode p v=a := congrArg Prod.snd PC
  have L : sourceOpcode p v≤commitOp p := by
    rw [O]
    change a≤admitOp p at B
    unfold admitOp at B
    unfold commitOp
    omega
  have E := early_issue_packet p v t a P O A B
  have J := source_issue_joint p v t P L
  have W := raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)
  dsimp only at W J
  constructor
  · rcases J with ⟨_,Z⟩|⟨Z,_,_,_,_⟩
    · rw [E] at Z
      have K := congrArg MISByteCodec.Token.tag (Option.some.inj Z)
      change 2=0 at K
      contradiction
    · exact W.1.trans (Z.trans (by rw [O]))
  · rw [root_tok,W.2,E]
    exact early_F_roundtrip p false a 0 A B (by decide) (fun _=>rfl) (fun _=>rfl)

private theorem raw_early_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (a : Nat)
    (A : 0<a) (B : a≤admitOp (params d s))
    (PC : readPC d C x=(2,a))
    (T : tok d C x 0=earlyD a (earlyQ (params d s) a)) :
    let y := rawNext s x (door C)
    readPC d C y=(1,a+1) ∧ wire d C y 0=resetTokenWire (params d s) MISByteCodec.E := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have TE : t=earlyD a (earlyQ p a) := (root_pub_early d C x).symm.trans T
  have R := early_consume_control p v a (congrArg Prod.fst PC)
    (congrArg Prod.snd PC) A B
  have TE' : publicationToken (params d s) true (selectBytes d (x C.root)) 0=earlyD a (earlyQ p a) := TE
  have W := raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)
  dsimp only at W R
  constructor
  · rw [TE'] at W
    exact W.1.trans R.1
  · unfold wire
    rw [show C.route.port 0=0 from C.rootPort]
    change resetTokenRead p (selectBytes d (rawNext s x (door C) C.root)) 0=_
    rw [W.2,TE',R.2]

private theorem raw_root_fwd_hold (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (P : LegalWait d C x) (a q r : Nat) (T : tok d C x 0=earlyF a q r) :
    tok d C (rawNext s x (door C)) 0=earlyF a q r := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have TE : t=earlyF a q r := (root_pub_early d C x).symm.trans T
  have H : t.tag=1 ∨ t.tag=2 := .inr (by rw [TE]; rfl)
  have FT : t.fault=false := by rw [TE]; rfl
  have W := raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)
  dsimp only at W
  rw [root_tok,W.2,prelaunch_wait_hold p v t P.1 P.2 H]
  change decode p false (prelaunchDoorNormWire p v)=_
  rw [early_root_norm_wire p v FT]
  exact (prelaunch_root_decode p v).symm.trans TE

-- CHECK: source_issue_joint (ReportByteRows:6776) has the exact
-- (PC ∧ ∃ packet, source result ∧ tag ∧ RankFits) second branch.
-- CHECK: raw_door_final (ReportOwnerDoorProjection:12), root_tok
-- (ReportPrelaunchDoorLift:73); if dsimp exposes the tuple, use
-- change to (source p v t).2 before rewriting E/TE/R.2.
-- CHECK: incoming-zero predecessor identity is the same as the
-- private incoming_zero, ReportOwnerCommandRail:42.

private theorem raw_fwd_in_fixed (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (P : (tok d C x i).tag≠2) (a q : Nat)
    (T : tok d C x (i+1)=earlyF a q 0) :
    tok d C (rawNext s x (out C i)) (i+1)=earlyF a q 0 := by
  let e := out C i
  let y := rawNext s x e
  let p := params d s
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have NR : readyAt d C x i=false :=
    Bool.eq_false_iff.mpr (fun R=>P ((ready_iff d C x i).mp R).1)
  have D : (publicationToken p (h (rightNeighbor e))
      (bytesR d x e) (C.route.port (i+1))).tag≠3 := by
    rw [←successor_projection d C x i,T]
    simp [earlyF]
  have E := rank_idle_right p (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ (internal_dest C i I) NR (.inr D)
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,W.2,workR,E]
  change decode p (chartGate d C x (i+1))
    (rankNormWire p 2 (chartGate d C x (i+1)) (wire d C x (i+1)))=_
  apply early_norm_fixed
  · exact (tok_wire d C x (i+1)).symm.trans T
  · simp [rankNormIntent,earlyF]

private theorem raw_regular_hop (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i a q : Nat) (I : i+1<C.L)
    (A : 0<a) (B : a≤admitOp (params d s)) (Q0 : q<2)
    (HQ : a≠admitOp (params d s) → q=0)
    (GA : a=admitOp (params d s) → chartGate d C x i=false)
    (GB : a=admitOp (params d s) → chartGate d C x (i+1)=false)
    (T : tok d C x i=earlyF a q 0) :
    tok d C (rawNext s x (out C i)) (i+1)=earlyF a q 0 := by
  let e := out C i
  let y := rawNext s x e
  let p := params d s
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have RD : readyAt d C x i=true := by
    apply (ready_iff d C x i).mpr
    refine ⟨by rw [T]; rfl,?_⟩
    intro K
    have E : a=admitOp p := by
      have Z := K.1
      rw [T] at Z
      exact Z.2.2
    rw [GA E] at K
    exact Bool.noConfusion K.2.1
  have V := ready_joined d C x N (CF.mask x X) i I RD
  dsimp only at V
  have T' := T
  rw [predecessor_projection] at T'
  have GB' : a=admitOp p → rankGate p (h (rightNeighbor e))
      (bytesR d x e) (C.route.port (i+1))=false := by
    intro H
    rw [chart_succ]
    exact GB H
  have E := early_regular_route p (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ a q A B T' GA GB'
  obtain ⟨t,H,W⟩ := V.2
  have TE := Option.some.inj (H.symm.trans E)
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,W,TE]
  exact early_F_roundtrip p _ a q A B Q0 HQ GB

private theorem raw_regular_turn (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (_G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i a : Nat)
    (_I : i<C.L) (End : i+1=C.L) (A : 0<a) (B : a≤admitOp (params d s))
    (GA : a=admitOp (params d s) → chartGate d C x i=false)
    (T : tok d C x i=earlyF a (earlyQ (params d s) a) 0) :
    tok d C (rawNext s x (out C i)) i=earlyD a (earlyQ (params d s) a) := by
  let e := out C i
  let p := params d s
  have CF := cached_fibre d N hh Q F
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have T' := T
  rw [predecessor_projection] at T'
  have E := early_terminal_wire p (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ a (earlyQ p a) A B
    (end_dest C i End) T' GA (fun H=>by simp [earlyQ,H])
  rw [tok_wire,W.1,workL,E]
  exact early_D_roundtrip p _ a A B

private theorem raw_reverse_hop_early (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i a : Nat) (I : i+1<C.L)
    (A : 0<a) (B : a≤admitOp (params d s))
    (P : (tok d C x i).tag≠2)
    (T : tok d C x (i+1)=earlyD a (earlyQ (params d s) a)) :
    tok d C (rawNext s x (out C i)) i=earlyD a (earlyQ (params d s) a) := by
  have W := reverse_joined d C x N ((cached_fibre d N hh Q F).mask x X)
    i I P (by rw [T]; rfl)
  dsimp only at W
  rw [tok_wire,W.1,T]
  exact early_D_roundtrip _ _ a A B

private theorem raw_reverse_out_hold (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i a : Nat) (I : i<C.L)
    (R : ReverseWait d C x i)
    (T : tok d C x i=earlyD a (earlyQ (params d s) a)) :
    tok d C (rawNext s x (out C i)) i=earlyD a (earlyQ (params d s) a) := by
  let e := out C i
  let y := rawNext s x e
  let p := params d s
  let u := bytesL d x e
  let v := bytesR d x e
  let j := C.route.port i
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have T' : publicationToken p (h e) u j=earlyD a (earlyQ p a) :=
    (predecessor_projection d C x i).symm.trans T
  have NR : readyAt d C x i=false := Bool.eq_false_iff.mpr
    (fun H=>by have K := ((ready_iff d C x i).mp H).1; rw [T] at K; simp [earlyD] at K)
  have ID :
      (publicationToken p (h e) u j).tag≠2 ∧
      (match reset0Destination (h (rightNeighbor e)) j with
       | none => (publicationToken p (h e) u j).tag≠1
       | some k => (publicationToken p (h (rightNeighbor e)) v k).tag≠3 ∧
           ¬((publicationToken p (h e) u j).tag=1 ∧
             (publicationToken p (h (rightNeighbor e)) v k).tag=0)) := by
    refine ⟨by rw [T']; simp [earlyD],?_⟩
    by_cases H : i+1<C.L
    · rw [internal_dest C i H]
      have E := R.2.2 (i+1) H
      have Z : (tok d C x (i+1)).tag=0 := by
        simpa [backTag,show ¬i+1<i by omega,show i+1≠i by omega] using E
      dsimp only [e,v,p,j,u]
      rw [←successor_projection d C x i,T',Z]
      simp [earlyD]
    · rw [end_dest C i (by omega),T']
      simp [earlyD]
  have E := rank_idle_left p (h e) (h (rightNeighbor e)) u v j NR (.inr ID)
  rw [tok_wire,gate_frame d C hh G x y X Y i I,W.1,workL,E]
  change decode p (chartGate d C x i)
    (rankNormWire p 3 (chartGate d C x i) (wire d C x i))=_
  apply early_norm_fixed
  · exact (tok_wire d C x i).symm.trans T
  · simp [rankNormIntent,earlyD]

-- CHECK: the let-bound e/u/v/j in rank_idle_left/right are reducible;
-- if rw does not find them, dsimp only [e,u,v,j] at E ID.
-- ReportByteRows:4786-4896; raw_pair_wire, ReportPrelaunchK1Geometry:171.
-- The match in rank_idle_left is exactly the checked router split,
-- with both tag tests on the OLD pair.

private theorem regular_forward_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (a k q : Nat)
    (A : 0<a) (B : a≤admitOp (params d s)) (K : k<C.L)
    (PC : readPC d C x=(2,a))
    (D : EarlyData (params d s) (C.a+2) a k q 0)
    (T : tok d C x k=earlyF a q 0) (R : ForwardWait d C x k)
    (e : Fin n) : EarlyPacket d C (rawNext s x e) := by
  let p := params d s
  change EarlyData p (C.a+2) a k q 0 at D
  have PP := (wait_pc_hold d C N hh F x X R.1 e
    (fun _=>fwd_root_hold_tag d C x k R)).trans PC
  have Room := (gate_room C G).1
  have Q0 : q<2 := by unfold EarlyData at D; omega
  have HQ : a≠admitOp p → q=0 := by
    intro H
    unfold EarlyData at D
    omega
  have GA : a=admitOp p → chartGate d C x k=false := by
    intro H
    apply gate_off d C hh G x X k K
    unfold EarlyData at D
    omega
  by_cases E : e=out C k
  · subst e
    by_cases I : k+1<C.L
    · by_cases H : a=admitOp p ∧ k+1=C.a+2
      · have QZ : q=0 := by unfold EarlyData at D; omega
        have GB : chartGate d C x (k+1)=true :=
          ((gate_geometry d C hh G (Q:=Q)).2.2 x X (k+1) I).mpr H.2
        have T' : tok d C x k=earlyF (admitOp p) q 0 := by rw [←H.1]; exact T
        have W := (raw_gate_arrival d C N hh G F x X k I (GA H.1) GB q Q0 T').2
        refine .fwd a (k+1) q 1 A B I PP ?_ ?_
        · exact .inr (.inr (.inl ⟨H.1,H.2,QZ,.inl rfl⟩))
        · rw [H.1]
          exact W
      · have GB : a=admitOp p → chartGate d C x (k+1)=false :=
          fun J=>gate_off d C hh G x X (k+1) I (fun L=>H ⟨J,L⟩)
        refine .fwd a (k+1) q 0 A B I PP ?_
          (raw_regular_hop d C N hh G F x X k a q I A B Q0 HQ GA GB T)
        change EarlyData p (C.a+2) a (k+1) q 0
        unfold EarlyData at D ⊢
        omega
    · have End : k+1=C.L := by omega
      have QZ : q=earlyQ p a := by
        by_cases H : a=admitOp p
        · simp [earlyQ,H]
          unfold EarlyData at D
          omega
        · simp [earlyQ,H,HQ H]
      have T' : tok d C x k=earlyF a (earlyQ p a) 0 := QZ ▸ T
      exact .rev a k A B K PP (raw_regular_turn d C N hh G F x X k a K End A B GA T')
  · refine .fwd a k q 0 A B K PP D ?_
    cases k with
    | zero =>
      by_cases J : e=door C
      · subst e
        exact raw_root_fwd_hold d C N hh F x X R.1 a q 0 T
      · exact (root_spectator_early d C N hh G F x X e J E).trans T
    | succ i =>
      by_cases J : e=out C i
      · subst e
        have P : (tok d C x i).tag≠2 := by
          rw [R.2.2 i (by omega)]
          simp [frontTag,show i<i+1 by omega]
        exact raw_fwd_in_fixed d C N hh G F x X i K P a q T
      · exact (raw_gate_spectator d C N hh G F x X i K e J E).trans T

private theorem gate_forward_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (S : StrongSerial d C x) (r : Nat) (RR : r=1 ∨ r=3 ∨ r=5)
    (PC : readPC d C x=(2,admitOp (params d s)))
    (T : tok d C x (C.a+2)=earlyF (admitOp (params d s)) 0 r)
    (e : Fin n) (Allowed : WinAllowed d C x e) :
    EarlyPacket d C (rawNext s x e) := by
  let p := params d s
  have K := (gate_geometry d C hh G (Q:=Q)).2.1
  have Room := (gate_room C G).1
  have GA := ((gate_geometry d C hh G (Q:=Q)).2.2 x X (C.a+2) K).mpr rfl
  have GB := gate_off d C hh G x X (C.a+3) Room (by omega)
  have H : healthyAdmit p (tok d C x (C.a+2)) := by
    rw [T]
    exact ⟨rfl,rfl,rfl⟩
  have R := fwd_shape d C x S.1 (C.a+2) K H.1
  have PP := (wait_pc_hold d C N hh F x X R.1 e
    (fun _=>fwd_root_hold_tag d C x _ R)).trans PC
  have P : (tok d C x (C.a+1)).tag≠2 := by
    rw [R.2.2 (C.a+1) (by omega)]
    simp [frontTag,show C.a+1<C.a+2 by omega]
  have A : 0<admitOp p := by unfold admitOp; omega
  have I : C.a+1+1<C.L := by omega
  have T5 : ∀ t : Nat, (t=1 ∨ t=3 ∨ t=5) →
      tok d C (rawNext s x e) (C.a+2)=earlyF (admitOp p) 0 t →
      EarlyPacket d C (rawNext s x e) := by
    intro t J Z
    exact .fwd (admitOp p) (C.a+2) 0 t A (Nat.le_refl _) K PP
      (.inr (.inr (.inl ⟨rfl,rfl,rfl,J⟩))) Z
  rcases RR with E|E|E
  · subst r
    have No := Allowed H (by rw [T]; rfl)
    by_cases J : e=out C (C.a+2)
    · subst e
      apply T5 3 (.inr (.inl rfl))
      have W := raw_outgoing_decisions d C N hh G F x X (C.a+2) K GA H
        (.inl (by rw [T]; rfl))
      simpa [T,earlyF,admitRaceAfter] using W
    · exact T5 1 (.inl rfl)
        ((raw_gate_spectator d C N hh G F x X (C.a+1) I e No J).trans T)
  · subst r
    by_cases J : e=out C (C.a+1)
    · subst e
      apply T5 5 (.inr (.inr rfl))
      have W := raw_incoming_decisions d C N hh G F x X (C.a+1) I GA P H
        (.inr (by rw [T]; rfl))
      simpa [T,earlyF,admitRaceAfter] using W
    · exact T5 3 (.inr (.inl rfl))
        ((raw_no_rearm_step d C N hh G F x X S.1 (C.a+1) I GA H true
          (by rw [T]; rfl) e J).trans T)
  · subst r
    by_cases J : e=out C (C.a+2)
    · subst e
      have W := (raw_ready_depart d C N hh G F x X (C.a+2) Room GA GB H
        (by rw [T]; simp [earlyF])).2
      refine .fwd (admitOp p) (C.a+3) 1 0 A (Nat.le_refl _) Room PP
        (.inr (.inr (.inr ⟨rfl,by omega,rfl,rfl⟩))) ?_
      simpa [T,earlyF] using W
    · by_cases L : e=out C (C.a+1)
      · subst e
        apply T5 5 (.inr (.inr rfl))
        rw [raw_in_norm d C N hh G F x X (C.a+1) I GA P H]
        apply early_norm_fixed
        · have Z := tok_wire d C x (C.a+2)
          rw [GA] at Z
          exact Z.symm.trans T
        · simp [rankNormIntent,earlyF]
      · exact T5 5 (.inr (.inr rfl))
          ((raw_gate_spectator d C N hh G F x X (C.a+1) I e L J).trans T)

-- CHECK: gate_room is ReportFastOwnerSupport:75, with first conjunct
-- C.a+3<C.L. All a+1+1 / a+2 and a+2+1 / a+3 coercions are Nat
-- definitional reductions. healthyAdmit is ReportByteRows:2570.
-- In the W rewrites, if simp does not use the exact token equation T
-- under structure update, rw [T] at W before simpa [earlyF,admitRaceAfter].

private theorem reverse_early_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (a k : Nat)
    (A : 0<a) (B : a≤admitOp (params d s)) (K : k<C.L)
    (PC : readPC d C x=(2,a))
    (T : tok d C x k=earlyD a (earlyQ (params d s) a))
    (R : ReverseWait d C x k) (e : Fin n) :
    EarlyPacket d C (rawNext s x e) := by
  let p := params d s
  by_cases Stop : k=0 ∧ e=door C
  · obtain ⟨E,J⟩ := Stop
    subst k
    subst e
    have W := raw_early_consume d C N hh F x X a A B PC T
    dsimp only at W
    by_cases AD : a=admitOp p
    · apply EarlyPacket.acq
      unfold AtACQIssue
      rw [W.1,AD]
      rfl
    · exact .issue (a+1) (by omega) (by change a+1≤admitOp p; change a≤admitOp p at B; omega) W.1
  · have PP := (wait_pc_hold d C N hh F x X R.1 e (fun J=>
        .inl (rev_root_hold_tag d C x k R (by
          have H : k≠0 := fun E=>Stop ⟨E,J⟩
          omega)))).trans PC
    by_cases Out : e=out C k
    · subst e
      exact .rev a k A B K PP (raw_reverse_out_hold d C N hh G F x X k a K R T)
    · cases k with
      | zero =>
        have H : e≠door C := fun J=>Stop ⟨rfl,J⟩
        exact .rev a 0 A B K PP
          ((root_spectator_early d C N hh G F x X e H Out).trans T)
      | succ i =>
        by_cases In : e=out C i
        · subst e
          have P : (tok d C x i).tag≠2 := by
            rw [R.2.2 i (by omega)]
            simp [backTag,show i<i+1 by omega]
          exact .rev a i A B (by omega) PP
            (raw_reverse_hop_early d C N hh F x X i a K A B P T)
        · exact .rev a (i+1) A B K PP
            ((raw_gate_spectator d C N hh G F x X i K e In Out).trans T)

theorem early_pose (d : Sheet) (C : Chart h) (x : Raw s n)
    (H : EarlyPacket d C x) : PreACQPose d C x := by
  cases H with
  | issue a A B PC =>
    unfold PreACQPose
    rw [PC]
    exact ⟨A,.inl (by unfold admitOp at B; unfold acqOp; omega)⟩
  | fwd a k q r A B K PC D T =>
    unfold PreACQPose
    rw [PC]
    exact ⟨A,.inl (by unfold admitOp at B; unfold acqOp; omega)⟩
  | rev a k A B K PC T =>
    unfold PreACQPose
    rw [PC]
    exact ⟨A,.inl (by unfold admitOp at B; unfold acqOp; omega)⟩
  | acq PC =>
    refine ⟨?_,.inr PC⟩
    unfold AtACQIssue at PC
    rw [PC]
    unfold acqOp
    omega

-- This is the one-mark preservation theorem. It invokes actual joined
-- rows, never an abstract packet-stage transition in place of rawNext.
theorem early_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d C x)
    (H : EarlyPacket d C x) (e : Fin n) (Allowed : WinAllowed d C x e)
    (NL : ¬(AtACQIssue d C x ∧ e=door C)) :
    EarlyPacket d C (rawNext s x e) := by
  let p := params d s
  cases H with
  | issue a A B PC =>
    by_cases E : e=door C
    · subst e
      have W := raw_issue_early d C N hh F x X a A B PC
      refine .fwd a 0 0 0 A B C.positive W.1 ?_ W.2
      by_cases J : a=admitOp p
      · exact .inr (.inl ⟨J,by omega,rfl,rfl⟩)
      · exact .inl ⟨by change a<admitOp p; change a≤admitOp p at B; omega,rfl,rfl⟩
    · exact .issue a A B
        ((raw_nondoor_control d C x e N
          ((cached_fibre d N hh Q F).mask x X) E).trans PC)
  | fwd a k q r A B K PC D T =>
    by_cases RZ : r=0
    · subst r
      have R := fwd_shape d C x S.1 k K (by rw [T]; rfl)
      exact regular_forward_step d C N hh G F x X a k q A B K PC D T R e
    · have J : a=admitOp p ∧ k=C.a+2 ∧ q=0 ∧ (r=1 ∨ r=3 ∨ r=5) := by
        change EarlyData p (C.a+2) a k q r at D
        unfold EarlyData at D
        omega
      obtain ⟨AE,KE,QE,RR⟩ := J
      subst a
      subst k
      subst q
      exact gate_forward_step d C N hh G F x X S r RR PC T e Allowed
  | rev a k A B K PC T =>
    have R := rev_shape d C x S.1 k K (by rw [T]; rfl)
    exact reverse_early_step d C N hh G F x X a k A B K PC T R e
  | acq PC =>
    have E : e≠door C := fun J=>NL ⟨PC,J⟩
    apply EarlyPacket.acq
    unfold AtACQIssue at PC ⊢
    exact (raw_nondoor_control d C x e N
      ((cached_fibre d N hh Q F).mask x X) E).trans PC

-- End-of-ADMIT is a separately usable literal receipt. This uses
-- the old grant-independent consume row and proves the exact E wire.
theorem winning_admit_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d C x)
    (PC : readPC d C x=(2,admitOp (params d s)))
    (T : tok d C x 0=earlyD (admitOp (params d s)) 1) :
    let y := rawNext s x (door C)
    AtACQIssue d C y ∧ LegalIssue d C y ∧
      wire d C y 0=resetTokenWire (params d s) MISByteCodec.E := by
  dsimp only
  have W := raw_admit_consume d C N x ((cached_fibre d N hh Q F).mask x X)
    PC (by rw [T]; rfl) (by rw [T]; rfl) (by rw [T]; rfl) (by rw [T]; rfl)
  have A : AtACQIssue d C (rawNext s x (door C)) := by
    unfold AtACQIssue
    simpa [T,earlyD] using W.1
  exact ⟨A,preACQ_legal_issue d C _ (strong_step d C N hh G F x X S digit _) A,W.2⟩

-- CHECK: preACQ_legal_issue; the fresh
-- reset receipt and all issue/WAIT shapes come from the pinned
-- ReportOwnerCommandRail. No positive opcode successor is assumed here.

def BasePacketGood (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) : Prop :=
  StrongSerial d C z.raw.val ∧ z.status≠.retry ∧
    (z.status=.live → EarlyPacket d C z.raw.val)

theorem base_packet_init (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (x : {x : Raw s n // Cached d hh Q x})
    (PC : readPC d C x.val=(1,1)) (S : StrongSerial d C x.val) :
    BasePacketGood d C hh (⟨x,.live⟩ : PreACQBase d hh Q) := by
  have NR : PreACQStatus.live≠PreACQStatus.retry := by decide
  refine ⟨S,NR,fun _=>.issue 1 (by decide) ?_ PC⟩
  unfold admitOp
  omega

theorem base_packet_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : PreACQBase d hh Q) (e : Fin n)
    (H : BasePacketGood d C hh z) (Allowed : WinAllowed d C z.raw.val e) :
    BasePacketGood d C hh (preACQStep d C N hh F z e) := by
  classical
  refine ⟨strong_step d C N hh G F z.raw.val z.raw.property H.1 digit e,?_⟩
  by_cases L : z.status=.live
  · by_cases J : AtACQIssue d C z.raw.val ∧ e=door C
    · have E : (preACQStep d C N hh F z e).status=.launched := by
        simp [preACQStep,L,J]
      rw [E]
      exact ⟨by decide,fun H=>by contradiction⟩
    · have P := early_step d C N hh G F z.raw.val z.raw.property H.1
        (H.2.2 L) e Allowed J
      have Pose := early_pose d C _ P
      have E : (preACQStep d C N hh F z e).status=.live := by
        simp [preACQStep,L,J,Pose]
      exact ⟨by rw [E]; decide,fun _=>P⟩
  · have E : (preACQStep d C N hh F z e).status=z.status := by
      simp [preACQStep,L]
    exact ⟨E ▸ H.2.1,fun J=>False.elim (L (E.symm.trans J))⟩

-- Ordinary raw marks can be included in a word without any relabeling
-- if (and only insofar as) they satisfy the old-race restriction.
-- This predicate recomputes the guard at EVERY old state.
def WinWord (d : Sheet) (C : Chart h) :
    Raw s n → List (Fin n) → Prop
  | _,[] => True
  | x,e::w => WinAllowed d C x e ∧ WinWord d C (rawNext s x e) w

theorem base_packet_word (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (w : List (Fin n))
    (z : PreACQBase d hh Q) (H : BasePacketGood d C hh z)
    (W : WinWord d C z.raw.val w) :
    BasePacketGood d C hh
      (SequentialMarkClock.run (preACQStep d C N hh F) z w) := by
  induction w generalizing z with
  | nil => exact H
  | cons e w ih =>
    change WinAllowed d C z.raw.val e ∧ WinWord d C (rawNext s z.raw.val e) w at W
    exact ih (preACQStep d C N hh F z e)
      (base_packet_step d C N hh G F digit z e H W.1) W.2

theorem base_packet_run_raw (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreACQBase d hh Q) (w : List (Fin n)) :
    (SequentialMarkClock.run (preACQStep d C N hh F) z w).raw.val=
      SequentialMarkClock.run (rawNext s) z.raw.val w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    exact ih (preACQStep d C N hh F z e)

-- CHECK: SequentialMarkClock.run: chronological cons recursion,
-- same direction as rawRun. ReportFastFreshReset: preACQStep_raw
-- is definitionally rfl.

theorem win_word_prefix (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (W : WinWord d C x (u++v)) :
    WinWord d C x u := by
  induction u generalizing x with
  | nil => trivial
  | cons e u ih =>
    exact ⟨W.1,ih _ W.2⟩

-- Strictly before the first ISSUE cut no ACQ opcode is present.
theorem early_nonacq (d : Sheet) (C : Chart h) (x : Raw s n)
    (H : EarlyPacket d C x) (J : ¬AtACQIssue d C x) :
    (readPC d C x).2≠acqOp (params d s) := by
  cases H with
  | issue a A B PC =>
    rw [PC]
    unfold admitOp at B
    unfold acqOp
    omega
  | fwd a k q r A B K PC D T =>
    rw [PC]
    unfold admitOp at B
    unfold acqOp
    omega
  | rev a k A B K PC T =>
    rw [PC]
    unfold admitOp at B
    unfold acqOp
    omega
  | acq PC => exact False.elim (J PC)

end L4.ReportFastEarlyPacket
namespace L4.ReportFastEarlyPacket
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportOwnerCommandRail ReportOwnerIssueControl
open ReportByteRows ReportFastOwnerSupport ReportFastFreshReset
open ReportFastNominationBridge ReportFastPreACQTrack
open ReportAdaptiveFibre ReportFastKernel ReportFastPrepMapping
open ReportFastSteeringMap ReportFastDenySteering ReportFastRefractory ReportGateGeometry

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

def WinTrackGood (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreTrack d hh Q) : Prop :=
  preTrackGood d C target hh z ∧ BasePacketGood d (C target) hh z.base

noncomputable def preWinDriver (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreTrack d hh Q) (e : Fin n) : PreTrack d hh Q :=
  preTrackStep d C target N hh F z (mergeSide (preBan d C target hh z.base) e)

theorem preTrack_base_early (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreTrack d hh Q) (e : Fin n) :
    (preTrackStep d C target N hh F z e).base=
      preACQStep d (C target) N hh F z.base e := by
  unfold preTrackStep
  rw [next_base]

theorem win_track_init (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (x : {x : Raw s n // Cached d hh Q x})
    (PC : readPC d (C target) x.val=(1,1))
    (S : ∀ j,StrongSerial d (C j) x.val) (q : Fin n) :
    WinTrackGood d C target hh
      (start (PreACQNom d (C target) hh) (⟨x,.live⟩ : PreACQBase d hh Q) q) := by
  refine ⟨preTrack_init d C target N hh G F digit inj x PC S q,?_⟩
  exact base_packet_init d (C target) hh x PC (S target)

theorem win_driver_allowed (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (e : Fin n) :
    WinAllowed d (C target) z.base.raw.val
      (mergeSide (preBan d C target hh z.base) e) := by
  intro H R
  exact target_first_not_incoming d C target hh G inj z.base H R e

theorem win_driver_step (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (e : Fin n) (H : WinTrackGood d C target hh z) :
    WinTrackGood d C target hh (preWinDriver d C target N hh F z e) := by
  let m := mergeSide (preBan d C target hh z.base) e
  refine ⟨preTrack_closed d C target N hh G F digit inj z m H.1,?_⟩
  change BasePacketGood d (C target) hh (preTrackStep d C target N hh F z m).base
  rw [preTrack_base_early]
  exact base_packet_step d (C target) N hh G F digit z.base m H.2
    (win_driver_allowed d C target hh G inj z e)

theorem win_driver_word (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (w : List (Fin n)) (z : PreTrack d hh Q)
    (H : WinTrackGood d C target hh z) :
    WinTrackGood d C target hh
      (SequentialMarkClock.run (preWinDriver d C target N hh F) z w) := by
  induction w generalizing z with
  | nil => exact H
  | cons e w ih =>
    exact ih (preWinDriver d C target N hh F z e)
      (win_driver_step d C target N hh G F digit inj z e H)

-- Compare the two already checked physical ban specifications. This
-- is the target-win version of the prep bridge, not a new scheduler.
theorem pre_merge_eq_steer (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreACQBase d hh Q) (e : Fin n) :
    mergeSide (preBan d C target hh z) e=
      steerRaw d C (targetDesired target) z.raw.val e := by
  have A : activeRaw d C z.raw.val=fun j=>armed d (C j) z.raw.val :=
    funext (active_eq_armed d C z.raw.val)
  unfold preBan steerRaw
  rw [A]
  generalize (fun j=>armed d (C j) z.raw.val)=active
  cases H : makeBan C active (targetDesired target) e with
  | none =>
    cases K : gateBan C active (targetDesired target) e with
    | none => simp [mergeSide,H,K]
    | some a =>
      have J := (gate_ban_spec hh G C inj active (targetDesired target) e a).mp K
      have D := (makeBan_spec hh G C inj active (targetDesired target) e a).mpr J
      rw [H] at D
      contradiction
  | some a =>
    have J := (makeBan_spec hh G C inj active (targetDesired target) e a).mp H
    have D := (gate_ban_spec hh G C inj active (targetDesired target) e a).mpr J
    simp [mergeSide,H,D]

-- CHECK: active_eq_armed and prep_merge_eq_steer in
-- ReportFastPrepMapping; the latter proof is copied with desired
-- profile substituted. gate_ban_spec in ReportFastSteeringMap.
-- mappedWord below has signature (d C policy t x w), where the
-- policy takes mark count and OLD raw state.

theorem win_mapped_projection (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (inj : Function.Injective (fun j=>center (C j)))
    (w : List (Fin n)) (t : Nat) (z : PreTrack d hh Q) :
    let policy : Nat→Raw s n→Fin 5→Bool := fun _ _=>targetDesired target
    (SequentialMarkClock.run (preWinDriver d C target N hh F) z w).base.raw.val=
      SequentialMarkClock.run (rawNext s) z.base.raw.val
        (mappedWord d C policy t z.base.raw.val w) := by
  induction w generalizing t z with
  | nil => rfl
  | cons e w ih =>
    dsimp only [SequentialMarkClock.run,mappedWord]
    let y := preWinDriver d C target N hh F z e
    have E : y.base.raw.val=rawNext s z.base.raw.val
        (steerRaw d C (targetDesired target) z.base.raw.val e) := by
      unfold y preWinDriver
      rw [preTrack_raw,pre_merge_eq_steer d C target hh G inj]
    rw [ih (t+1) y,E]

theorem win_mapped_allowed (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (inj : Function.Injective (fun j=>center (C j)))
    (w : List (Fin n)) (t : Nat) (z : PreTrack d hh Q) :
    WinWord d (C target) z.base.raw.val
      (mappedWord d C (fun _ _=>targetDesired target) t z.base.raw.val w) := by
  induction w generalizing t z with
  | nil => trivial
  | cons e w ih =>
    let y := preWinDriver d C target N hh F z e
    have E : y.base.raw.val=rawNext s z.base.raw.val
        (steerRaw d C (targetDesired target) z.base.raw.val e) := by
      unfold y preWinDriver
      rw [preTrack_raw,pre_merge_eq_steer d C target hh G inj]
    change WinAllowed d (C target) z.base.raw.val
        (steerRaw d C (targetDesired target) z.base.raw.val e) ∧
      WinWord d (C target) (rawNext s z.base.raw.val
        (steerRaw d C (targetDesired target) z.base.raw.val e))
        (mappedWord d C (fun _ _=>targetDesired target) (t+1)
          (rawNext s z.base.raw.val (steerRaw d C (targetDesired target) z.base.raw.val e)) w)
    constructor
    · rw [←pre_merge_eq_steer d C target hh G inj z.base e]
      exact win_driver_allowed d C target hh G inj z e
    · rw [←E]
      exact ih (t+1) y

-- In particular this gives the actual physical prefix invariant,
-- without identifying the observer's words with resampled words.
theorem win_mapped_physical_prefix (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (w u v : List (Fin n)) (t : Nat) (z : PreTrack d hh Q)
    (H : WinTrackGood d C target hh z)
    (E : mappedWord d C (fun _ _=>targetDesired target) t z.base.raw.val w=u++v) :
    BasePacketGood d (C target) hh
      (SequentialMarkClock.run (preACQStep d (C target) N hh F) z.base u) := by
  have W := win_mapped_allowed d C target N hh G F inj w t z
  rw [E] at W
  exact base_packet_word d (C target) N hh G F digit u z.base H.2
    (win_word_prefix d (C target) z.base.raw.val u v W)

theorem win_hit_is_launch (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreTrack d hh Q)
    (H : WinTrackGood d C target hh z) :
    preACQHit d hh z.base ↔ preACQSuccess d hh z.base := by
  have R := H.2.2.1
  unfold preACQHit preACQSuccess
  cases E : z.base.status <;> simp_all

-- The actual end-state assertion at every mapped prefix, including
-- a prefix ending in a nonpaying, unaltered physical mark.
theorem mapped_no_retry (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (w : List (Fin n)) (z : PreTrack d hh Q)
    (H : WinTrackGood d C target hh z) :
    (SequentialMarkClock.run (preWinDriver d C target N hh F) z w).base.status≠.retry :=
  (win_driver_word d C target N hh G F digit inj w z H).2.2.1

end L4.ReportFastEarlyPacket
namespace L4.ReportFastEarlyPacket
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportOwnerCommandRail ReportOwnerIssueControl
open ReportByteRows ReportFastOwnerSupport ReportFastFreshReset
open ReportFastNominationBridge ReportFastPreACQTrack ReportAdaptiveFibre ReportFastKernel
open Height

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

def preIssueHit (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) : Prop :=
  preACQHit d hh z ∨ AtACQIssue d C z.raw.val

theorem pre_issue_rise (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : PreACQBase d hh Q) (e : Fin n)
    (H : BasePacketGood d C hh z) (W : WinAllowed d C z.raw.val e)
    (L : ¬preIssueHit d C hh z)
    (J : preIssueHit d C hh (preACQStep d C N hh F z e)) :
    let y := preACQStep d C N hh F z e
    y.status=.live ∧ AtACQIssue d C y.raw.val ∧ LegalIssue d C y.raw.val := by
  classical
  dsimp only
  have Live : z.status=.live := by
    apply Classical.byContradiction
    intro E
    exact L (.inl E)
  have Not : ¬(AtACQIssue d C z.raw.val ∧ e=door C) :=
    fun E=>L (.inr E.1)
  have P := early_step d C N hh G F z.raw.val z.raw.property H.1
    (H.2.2 Live) e W Not
  have Pose := early_pose d C _ P
  have Live' : (preACQStep d C N hh F z e).status=.live := by
    simp [preACQStep,Live,Not,Pose]
  have A : AtACQIssue d C (preACQStep d C N hh F z e).raw.val := by
    rcases J with J|J
    · exact False.elim (J Live')
    · exact J
  exact ⟨Live',A,preACQ_legal_issue d C _
    (strong_step d C N hh G F z.raw.val z.raw.property H.1 digit e) A⟩

theorem pre_issue_sticky (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreACQBase d hh Q) (e : Fin n) (H : preIssueHit d C hh z) :
    preIssueHit d C hh (preACQStep d C N hh F z e) := by
  classical
  by_cases L : z.status=.live
  · have A : AtACQIssue d C z.raw.val := by
      rcases H with H|H
      · exact False.elim (H L)
      · exact H
    by_cases E : e=door C
    · left
      have J : (preACQStep d C N hh F z e).status=.launched := by
        simp [preACQStep,L,A,E]
      unfold preACQHit
      rw [J]
      decide
    · right
      unfold AtACQIssue at A ⊢
      exact (raw_nondoor_control d C z.raw.val e N
        ((cached_fibre d N hh Q F).mask z.raw.val z.raw.property) E).trans A
  · left
    unfold preACQHit
    simp [preACQStep,L]

-- Use nominated_mean on the driver itself. Calling driver_nominated_mean
-- with WinTrackGood as an ordinary-closed predicate would be WRONG:
-- the incoming race-1 counterexample refutes that premise.
theorem win_driver_issue_mean (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (H : WinTrackGood d C target hh z) :
    Height.IIDExpectedHittingTimeAtMost (preWinDriver d C target N hh F)
      (fun w=>preIssueHit d (C target) hh w.base) z
      (n*preTrackRank d C target hh z) := by
  apply nominated_mean (preWinDriver d C target N hh F)
    (WinTrackGood d C target hh)
    (fun w=>preIssueHit d (C target) hh w.base) (preTrackRank d C target hh) _ z H
  constructor
  · intro w e W
    exact win_driver_step d C target N hh G F digit inj w e W
  · intro w e W L
    exact preTrack_idle d C target N hh G F digit inj w
      (mergeSide (preBan d C target hh w.base) e) W.1 (fun K=>L (.inl K))
  · intro w W L
    obtain ⟨a,e,E,P⟩ := preTrack_nominate d C target N hh G F digit inj w W.1
      (fun K=>L (.inl K))
    refine ⟨e,?_⟩
    unfold preWinDriver
    rw [E]
    exact P

-- The original, later launch latch also has the same bound, now
-- using the genuine launch predicate rather than launch-or-retry.
theorem win_driver_launch_mean (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (H : WinTrackGood d C target hh z) :
    Height.IIDExpectedHittingTimeAtMost (preWinDriver d C target N hh F)
      (fun w=>preACQSuccess d hh w.base) z
      (n*preTrackRank d C target hh z) := by
  apply nominated_mean (preWinDriver d C target N hh F)
    (WinTrackGood d C target hh)
    (fun w=>preACQSuccess d hh w.base) (preTrackRank d C target hh) _ z H
  constructor
  · intro w e W
    exact win_driver_step d C target N hh G F digit inj w e W
  · intro w e W L
    exact preTrack_idle d C target N hh G F digit inj w
      (mergeSide (preBan d C target hh w.base) e) W.1
      (fun K=>L ((win_hit_is_launch d C target hh w W).mp K))
  · intro w W L
    obtain ⟨a,e,E,P⟩ := preTrack_nominate d C target N hh G F digit inj w W.1
      (fun K=>L ((win_hit_is_launch d C target hh w W).mp K))
    refine ⟨e,?_⟩
    unfold preWinDriver
    rw [E]
    exact P

-- CHECK: nominated_mean, ReportAdaptiveRank, uses a Nomination
-- structure with closed/idle/progress fields in this order.
-- The result is the exact repository's IIDExpectedHittingTimeAtMost,
-- not a new probabilistic axiom.

#print axioms early_step
#print axioms winning_admit_consume
#print axioms base_packet_step
#print axioms base_packet_word
#print axioms win_driver_word
#print axioms win_mapped_projection
#print axioms win_mapped_physical_prefix
#print axioms mapped_no_retry
#print axioms pre_issue_rise
#print axioms win_driver_issue_mean
#print axioms win_driver_launch_mean

end L4.ReportFastEarlyPacket
