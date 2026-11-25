import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportGateGeometry
import Leader.L4.ReportFastRawEvent

namespace L4.ReportFastGateRaw
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportOwnerDoorProjection
open ReportPrelaunchClock ReportByteRows ReportRawProjection ReportPrelaunchDoorLift

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem ready_iff (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) :
    readyAt d C x i=true ↔ (tok d C x i).tag=2 ∧
      ¬(healthyAdmit (params d s) (tok d C x i) ∧
        chartGate d C x i=true ∧ (tok d C x i).race<4) := by
  unfold readyAt
  rw [rankReady_iff,←predecessor_projection]
  rfl

theorem not_ready_parked (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (H : healthyAdmit (params d s) (tok d C x i))
    (A : chartGate d C x i=true) (R : (tok d C x i).race<4) :
    readyAt d C x i=false :=
  Bool.eq_false_iff.mpr (fun B=>((ready_iff d C x i).mp B).2 ⟨H,A,R⟩)

theorem raw_out_norm (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i<C.L)
    (A : chartGate d C x i=true)
    (H : healthyAdmit (params d s) (tok d C x i))
    (R : (tok d C x i).race<4) :
    tok d C (rawNext s x (out C i)) i =
      decode (params d s) true (rankNormWire (params d s) 3 true (wire d C x i)) := by
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have T := H.1
  rw [predecessor_projection] at T
  have NR := not_ready_parked d C x i H A R
  have E := rank_idle_left (params d s) (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) (C.route.port i) NR (.inl T)
  rw [tok_wire,gate_frame d C hh G x y X Y i I,W.1,workL,E]
  change decode (params d s) (chartGate d C x i)
    (rankNormWire (params d s) 3 (chartGate d C x i) (wire d C x i))=_
  rw [A]

theorem raw_in_norm (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x (i+1)=true)
    (P : (tok d C x i).tag≠2)
    (H : healthyAdmit (params d s) (tok d C x (i+1))) :
    tok d C (rawNext s x (out C i)) (i+1) =
      decode (params d s) true (rankNormWire (params d s) 2 true (wire d C x (i+1))) := by
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have NR : readyAt d C x i=false :=
    Bool.eq_false_iff.mpr (fun R=>P ((ready_iff d C x i).mp R).1)
  have D : (publicationToken (params d s) (h (rightNeighbor e))
      (bytesR d x e) (C.route.port (i+1))).tag≠3 := by
    rw [←successor_projection d C x i,H.1]
    decide
  have E := rank_idle_right (params d s) (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ (internal_dest C i I) NR (.inr D)
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,W.2,workR,E]
  -- CHECK: chart_succ, bytesR and chartGate, ReportOwnerProvenanceTransport:15,25.
  change decode (params d s) (chartGate d C x (i+1))
    (rankNormWire (params d s) 2 (chartGate d C x (i+1)) (wire d C x (i+1)))=_
  rw [A]

-- Two incoming decisions, 1→2 and 3→5, with the old trail
-- rather than a newly normalized predecessor as the router input.
theorem raw_incoming_decisions (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x (i+1)=true) (P : (tok d C x i).tag≠2)
    (H : healthyAdmit (params d s) (tok d C x (i+1)))
    (R : (tok d C x (i+1)).race=1 ∨ (tok d C x (i+1)).race=3) :
    tok d C (rawNext s x (out C i)) (i+1) =
      { (tok d C x (i+1)) with
        race:=admitRaceAfter 2 (tok d C x (i+1)).race } := by
  have T : tok d C x (i+1)=decode (params d s) true (wire d C x (i+1)) := by
    rw [tok_wire,A]
  rw [raw_in_norm d C N hh G F x X i I A P H,T]
  rw [T] at H R
  exact rank_norm_race _ _ 2 (.inl rfl) H (by simpa using R)

-- Two outgoing decisions, 1→3 and 2→4. No old-ready departure
-- can be credited on either mark.
theorem raw_outgoing_decisions (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i<C.L)
    (A : chartGate d C x i=true)
    (H : healthyAdmit (params d s) (tok d C x i))
    (R : (tok d C x i).race=1 ∨ (tok d C x i).race=2) :
    tok d C (rawNext s x (out C i)) i =
      {(tok d C x i) with race:=admitRaceAfter 3 (tok d C x i).race} := by
  have B : (tok d C x i).race<4 := by rcases R with R|R <;> omega
  have T : tok d C x i=decode (params d s) true (wire d C x i) := by
    rw [tok_wire,A]
  rw [raw_out_norm d C N hh G F x X i I A H B,T]
  rw [T] at H R
  exact rank_norm_race _ _ 3 (.inr rfl) H (by simpa using R)

-- Fifth decision, with exact outgoing old payload. Gate is not the last
-- occurrence: on the production chart the third positive gap follows it.
theorem raw_ready_depart (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x i=true) (B : chartGate d C x (i+1)=false)
    (H : healthyAdmit (params d s) (tok d C x i))
    (R : 4≤(tok d C x i).race) :
    let y := rawNext s x (out C i)
    tok d C y i=MISByteCodec.T ∧
    tok d C y (i+1)=
      {(tok d C x i) with race:=0,payload:=(tok d C x i).race-4} := by
  dsimp only
  let p := params d s
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have RD : readyAt d C x i=true :=
    (ready_iff d C x i).mpr ⟨H.1,fun K=>by omega⟩
  have V := ready_joined d C x N (CF.mask x X) i I RD
  dsimp only at V
  have H' := H
  have R' := R
  rw [predecessor_projection] at H' R'
  have B' : rankGate p (h (rightNeighbor e)) (bytesR d x e)
      (C.route.port (i+1))=false := by
    -- CHECK: chartGate/rawGate and rankGate, chart_succ.
    rw [chart_succ]
    exact B
  have K := fast_depart_route p (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ H' A B' R'
  obtain ⟨t,T,W⟩ := V.2
  have tE := Option.some.inj (T.symm.trans K)
  rw [←predecessor_projection d C x i] at tE
  refine ⟨(ready_locations d C x N (CF.mask x X) i I RD).1,?_⟩
  have S : tok d C x i=decode p true (wire d C x i) := by rw [tok_wire,A]
  rw [S] at H
  obtain ⟨q,r,Q0,L,U,E⟩ := rank_admit_shape p (wire d C x i) H
  have J : tok d C x i=({tag:=2,opcode:=admitOp p,payload:=q,race:=r}:Tok) := S.trans E
  have R0 : 4≤r := by simpa [J] using R
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,B,W,tE,J]
  change decode p false (resetTokenWire p
    ({tag:=2,opcode:=admitOp p,payload:=r-4}:Tok))=_
  exact fast_admit_off_roundtrip p (r-4) (by omega)

-- Actual birth at the gate: no credit from an incumbent normalization.
-- Q0 is the decoded old off-gate payload bound; it is not a ghost coin.
theorem raw_gate_arrival (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x i=false) (B : chartGate d C x (i+1)=true)
    (q : Nat) (Q0 : q<2)
    (H : tok d C x i=({tag:=2,opcode:=admitOp (params d s),payload:=q}:Tok)) :
    let y := rawNext s x (out C i)
    tok d C y i=MISByteCodec.T ∧
    tok d C y (i+1)=({tag:=2,opcode:=admitOp (params d s),payload:=q,race:=1}:Tok) := by
  dsimp only
  let p := params d s
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have RD : readyAt d C x i=true := by
    apply (ready_iff d C x i).mpr
    refine ⟨by rw [H],fun K=>?_⟩
    rw [A] at K
    exact Bool.noConfusion K.2.1
  have V := ready_joined d C x N (CF.mask x X) i I RD
  dsimp only at V
  have H' := H
  rw [predecessor_projection] at H'
  have B' : rankGate p (h (rightNeighbor e)) (bytesR d x e)
      (C.route.port (i+1))=true := by rw [chart_succ]; exact B
  have K := fast_arrive_route p (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ q H' A B'
  obtain ⟨t,T,W⟩ := V.2
  have tE := Option.some.inj (T.symm.trans K)
  refine ⟨(ready_locations d C x N (CF.mask x X) i I RD).1,?_⟩
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,B,W,tE]
  exact fast_admit_on_roundtrip p q 1 Q0 (by decide) (by decide)

theorem raw_admit_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (P : readPC d C x=(2,admitOp (params d s)))
    (T : (tok d C x 0).tag=3)
    (O : (tok d C x 0).opcode=admitOp (params d s))
    (F0 : (tok d C x 0).fault=false)
    (Q0 : (tok d C x 0).outcome=0) :
    let y := rawNext s x (door C)
    readPC d C y=(1,if (tok d C x 0).payload=1 then acqOp (params d s) else 0) ∧
    wire d C y 0=resetTokenWire (params d s) MISByteCodec.E := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have TE : tok d C x 0=t := by rw [root_tok]; rfl
  have R := fast_admit_consume_control p v t
    (congrArg Prod.fst P) (congrArg Prod.snd P)
    (TE ▸ T) (TE ▸ O) (TE ▸ F0) (TE ▸ Q0)
  have W := raw_door_final d C x N mask
  dsimp only at W R
  constructor
  · rw [TE]
    exact W.1.trans R.1
  · -- CHECK: rootPort, out C 0=C.root, ReportResetRawHooks:27.
    unfold wire
    rw [show C.route.port 0=0 from C.rootPort]
    change resetTokenRead p (selectBytes d (rawNext s x (door C) C.root)) 0=_
    rw [W.2]
    change (match (source p v t).2 with
      | none => prelaunchDoorNormWire p v
      | some u => resetTokenWire p u)=_
    rw [R.2]

end L4.ReportFastGateRaw

