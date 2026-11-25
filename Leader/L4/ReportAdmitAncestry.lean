import Leader.L4.ReportWriteSplit

namespace L4.ReportAdmitAncestry
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ShortLayerGeometry ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportByteRows
open ReportRawProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerIssueControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportOwnerWriteTransport
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def admitF (p : Params) (q : Nat) : Tok := {tag:=2,opcode:=admitOp p,payload:=q}

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

theorem off_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (R : ForwardWait d C x k) (e : Fin n) (A : e≠out C k)
    (G0 : chartGate d C x k=false) (q : Nat)
    (Pkt : tok d C x k=admitF (params d s) q) :
    tok d C (rawNext s x e) k=tok d C x k := by
  let CF := cached_fibre d N hh Q F
  have I := R.2.1
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
        exact (R.2.2 0 C.positive).trans rfl
      have P : sourcePhase p v=2 := R.1.1
      have O : sourceOpcode p v≤commitOp p := R.1.2
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
      have LT : (tok d C x j).tag=1 := by rw [R.2.2 j (by omega)]; simp [frontTag]
      have RT : (tok d C x (j+1)).tag≠3 := by
        rw [R.2.2 (j+1) I]
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
      have Y' := CF.closed x (out C j) X
      have Gate : chartGate d C x (j+1)=rankGate p (h (rightNeighbor (out C j))) v b := by
        change rankGate p (h (out C (j+1))) (bytesL d x (out C (j+1))) b=_
        simp only [bytesL,bytesR,v,chart_succ]
      have Gate0 : rankGate p (h (rightNeighbor (out C j))) v b=false := Gate.symm.trans G0
      have WH : healthyAdmit p (decode p false (resetTokenRead p v b)) := by
        have Z := Pkt
        rw [successor_projection,rankToken_wire,Gate0] at Z
        rw [Z]
        exact ⟨rfl,rfl,rfl⟩
      rw [tok_wire d C (rawNext s x (out C j)),gate_frame d C hh G x _ X Y' (j+1) I,Gate,W.2,workR,E,Gate0,
        fast_off_norm p 2 _ WH,tok_wire,Gate,Gate0]
      rfl
  · apply decoded_frame d C hh G x _ X Y k I
    unfold wire
    rw [raw_spectator x e _ (Ne.symm A) (Ne.symm H)]



theorem off_hop (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1<C.L)
    (A : chartGate d C x k=false) (B : chartGate d C x (k+1)=false)
    (q : Nat) (Q0 : q<2) (Pkt : tok d C x k=admitF (params d s) q) :
    tok d C (rawNext s x (out C k)) (k+1)=admitF (params d s) q := by
  let p := params d s
  let e := out C k
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have RD : readyAt d C x k=true := by
    unfold readyAt
    rw [rankReady_iff,←predecessor_projection]
    refine ⟨by rw [Pkt]; rfl,?_⟩
    intro W
    have Gate : rankGate p (h e) (bytesL d x e) (C.route.port k)=false := A
    have Wg := W.2.1
    change rankGate p (h e) (bytesL d x e) (C.route.port k)=true at Wg
    rw [Gate] at Wg
    contradiction
  obtain ⟨_,t,T,W⟩ := ready_joined d C x N (CF.mask x X) k J RD
  rw [predecessor_projection] at Pkt
  have B' : rankGate p (h (rightNeighbor e)) (bytesR d x e)
      (C.route.port (k+1))=false := by rw [chart_succ]; exact B
  have H := fast_off_route p (h e) (h (rightNeighbor e)) (bytesL d x e) (bytesR d x e)
    _ _ q Pkt A B'
  have E := Option.some.inj (T.symm.trans H)
  rw [tok_wire,gate_frame d C hh G x y X Y (k+1) J,B,W,E]
  exact fast_admit_off_roundtrip p q Q0

theorem origin_launch (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (Op : (readPC d C x).2=admitOp (params d s)) :
    let y := rawNext s x (door C)
    ForwardWait d C y 0 ∧ tok d C y 0=admitF (params d s) 0 := by
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
  rw [fast_admit_issue_packet p v old I.2.1 Op] at W
  have P : tok d C y 0=admitF p 0 := by
    rw [root_tok,W]
    exact fast_admit_off_roundtrip p 0 (by decide)
  rcases ReportOwnerIssueControl.door_step d C hh G F N x X I with A|⟨A,_⟩
  · have H := A.2.2 0 C.positive
    rw [P] at H
    contradiction
  · exact ⟨A,P⟩


/-- Genuine pre-gate ADMIT from the owner launch: zero is not an assumed
    canonical payload at a later arrival. -/
def OffFront (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  k<C.a+2 ∧ ForwardWait d C x k ∧ tok d C x k=admitF (params d s) 0

theorem origin_seed (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (Op : (readPC d C x).2=admitOp (params d s)) :
    OffFront d C (rawNext s x (door C)) 0 :=
  ⟨by omega, origin_launch d C hh G F N x X I Op⟩

theorem before_gate_mark (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : OffFront d C x k)
    (e : Fin n) :
    let y := rawNext s x e
    (e=out C k ∧ k+1=C.a+2) ∨ (∃ j, OffFront d C y j) := by
  dsimp only
  have Geom := gate_geometry (s:=s) d C hh G (Q:=Q)
  have I : k+1<C.L := by have := Geom.2.1; have := R.1; omega
  have A : chartGate d C x k=false :=
    Bool.eq_false_iff.mpr (fun H=>by have := (Geom.2.2 x X k (by omega)).mp H; have := R.1; omega)
  have RD : readyAt d C x k=true := by
    unfold readyAt
    rw [rankReady_iff,←predecessor_projection]
    refine ⟨by rw [R.2.2]; rfl,?_⟩
    intro W
    have Wg := W.2.1
    change chartGate d C x k=true at Wg
    rw [A] at Wg
    contradiction
  have S := ReportOwnerForwardControl.all_mark d C hh G F N x X k R.2.1 e
  by_cases E : e=out C k
  · by_cases H : k+1=C.a+2
    · exact .inl ⟨E,H⟩
    subst e
    rcases S with U|⟨_,U|⟨L,_⟩⟩
    · have CF := cached_fibre d N hh Q F
      have K := (ready_locations d C x N (CF.mask x X) k I RD).1
      have W := U.2.2 k (by omega)
      rw [K] at W
      simp [frontTag,MISByteCodec.T] at W
    · have B : chartGate d C x (k+1)=false :=
        Bool.eq_false_iff.mpr (fun Z=>H ((Geom.2.2 x X _ I).mp Z))
      exact .inr ⟨k+1,by have := R.1; omega,U,off_hop d C N hh G F x X k I A B 0 (by decide) R.2.2⟩
    · omega
  · rcases S with U|⟨V,_⟩
    · exact .inr ⟨k,R.1,U,(off_hold d C hh G F N x X k R.2.1 e E A 0 R.2.2).trans R.2.2⟩
    · exact False.elim (E V)

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
    unfold readyAt
    rw [rankReady_iff,←predecessor_projection]
    refine ⟨by rw [H],?_⟩
    intro W
    have Wg := W.2.1
    change chartGate d C x i=true at Wg
    rw [A] at Wg
    contradiction
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


theorem origin_arrive (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : OffFront d C x k)
    (K : k+1=C.a+2) :
    let y := rawNext s x (out C k)
    tok d C y k=MISByteCodec.T ∧
      tok d C y (C.a+2)={tag:=2,opcode:=admitOp (params d s),payload:=0,race:=1} := by
  have Geom := gate_geometry (s:=s) d C hh G (Q:=Q)
  have I : k+1<C.L := K ▸ Geom.2.1
  have A : chartGate d C x k=false := Bool.eq_false_iff.mpr (fun H=>by
    have := (Geom.2.2 x X k (by omega)).mp H
    omega)
  have B : chartGate d C x (k+1)=true := (Geom.2.2 x X _ I).mpr K
  simpa only [K] using raw_gate_arrival d C N hh G F x X k I A B 0 (by decide) R.2.2

/-- Either this actual bounded tape has not reached the gate, or it has
    an exact decomposition at an old live ADMIT's first arrival mark.
    The zero payload and healthy race-1 token come from launch. -/
theorem before_gate_tape (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : OffFront d C x k)
    (w : List (Fin n)) :
    (∃ j,OffFront d C (rawRun x w) j) ∨
    ∃ pre post j,
      w=pre++out C j::post ∧ j+1=C.a+2 ∧ OffFront d C (rawRun x pre) j ∧
      tok d C (rawNext s (rawRun x pre) (out C j)) (C.a+2)=
        {tag:=2,opcode:=admitOp (params d s),payload:=0,race:=1} := by
  induction w generalizing x k with
  | nil => exact .inl ⟨k,R⟩
  | cons e w IH =>
    rcases before_gate_mark d C hh G F N x X k R e with ⟨E,K⟩|⟨j,S⟩
    · exact .inr ⟨[],w,k,by simp [E],K,R,(origin_arrive d C hh G F N x X k R K).2⟩
    · have Y := (cached_fibre d N hh Q F).closed x e X
      rcases IH (rawNext s x e) Y j S with A|⟨pre,post,j,H,K,B,E⟩
      · exact .inl A
      · exact .inr ⟨e::pre,post,j,by simp [H],K,B,E⟩

theorem before_turn_off (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (Seed : OffFront d C x 0)
    (w : List (Fin n)) (k : Nat) (T : ReportWriteSplit.BeforeTurn d C x w k)
    (K : k<C.a+2) : OffFront d C (rawRun x w) k := by
  have Geom := gate_geometry (s:=s) d C hh G (Q:=Q)
  let CF := cached_fibre d N hh Q F
  have off (z : Raw s n) (Z : Cached d hh Q z) (j : Nat) (J : j<C.a+2) :
      chartGate d C z j=false :=
    Bool.eq_false_iff.mpr (fun B=>by have := (Geom.2.2 z Z j (by have := Geom.2.1; omega)).mp B; omega)
  revert K
  induction T with
  | nil _ => exact fun _=>Seed
  | @hold u j R e S IH =>
    intro J
    have P := IH J
    have Z := (ReportWriteSplit.before_turn_pc d C N hh F x X u j R).1
    let z := rawRun x u
    have G0 := off z Z j J
    have NE : e≠out C j := by
      intro H
      subst e
      have Ready : readyAt d C z j=true := by
        unfold readyAt
        rw [rankReady_iff,←predecessor_projection]
        refine ⟨by rw [P.2.2]; rfl,?_⟩
        intro C0
        have CG := C0.2.1
        change chartGate d C z j=true at CG
        rw [G0] at CG
        contradiction
      have A := (ready_locations d C z N (CF.mask z Z) j (by have := Geom.2.1; omega) Ready).1
      have B := S.2.2 j S.2.1
      rw [A] at B
      simp [frontTag,MISByteCodec.T] at B
    rw [ShortOwnerEpochJS.raw_snoc]
    exact ⟨J,S,(off_hold d C hh G F N z Z j P.2.1 e NE G0 0 P.2.2).trans P.2.2⟩
  | @hop u j R S IH =>
    intro J
    have P := IH (by omega)
    have Z := (ReportWriteSplit.before_turn_pc d C N hh F x X u j R).1
    rw [ShortOwnerEpochJS.raw_snoc]
    exact ⟨J,S,off_hop d C N hh G F _ Z j (by have := Geom.2.1; omega)
      (off _ Z j (by omega)) (off _ Z (j+1) J) 0 (by decide) P.2.2⟩

theorem off_front_of_issue_history (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (w : List (Fin n)) (k : Nat)
    (K : k<C.a+2) (A : ForwardWait d C (rawRun x w) k)
    (Op : (readPC d C (rawRun x w)).2=admitOp (params d s)) :
    OffFront d C (rawRun x w) k := by
  obtain ⟨pre,fly,E,Y,J,P,T⟩ := ReportWriteSplit.forward_issue_split d C N hh G F digit x X I w k A
  have Seed := origin_seed d C hh G F N _ Y J (P.trans Op)
  have Y' := (cached_fibre d N hh Q F).closed _ (door C) Y
  rw [E,ShortOwnerEpochJS.raw_append]
  exact before_turn_off d C hh G F N _ Y' Seed fly k T K

open ReportOwnerCommandRail ReportPrelaunchK1

theorem off_front_of_receipt (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (reset w : List (Fin n)) (R : Generated d C x reset .done) (k : Nat) (K : k<C.a+2)
    (A : ForwardWait d C (rawRun (rawRun x reset) w) k)
    (Op : (readPC d C (rawRun (rawRun x reset) w)).2=admitOp (params d s)) :
    OffFront d C (rawRun (rawRun x reset) w) k := by
  let b := rawRun x reset
  have Xb := (cached_genuine_full_parked d C N hh F x X reset R).1
  have Sb := seed_receipt d C N hh F x X reset R
  have Ib : LegalIssue d C b := by
    rcases Sb.1 with I|⟨j,I⟩|⟨j,I⟩
    · exact I
    · have P := (cached_genuine_full_parked d C N hh F x X reset R).2.1.1
      have E := pc_fields d C b .issue1 (by decide) P
      have V : (readPC d C b).1=2 := I.1.1
      change readPC d C b=(1,1) at E
      rw [E] at V
      contradiction
    · have P := (cached_genuine_full_parked d C N hh F x X reset R).2.1.1
      have E := pc_fields d C b .issue1 (by decide) P
      have V : (readPC d C b).1=2 := I.1.1
      change readPC d C b=(1,1) at E
      rw [E] at V
      contradiction
  exact off_front_of_issue_history d C hh G F N digit b Xb Ib w k K A Op

theorem arrival_of_receipt (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (reset w : List (Fin n)) (R : Generated d C x reset .done)
    (A : ForwardWait d C (rawRun (rawRun x reset) w) (C.a+1))
    (Op : (readPC d C (rawRun (rawRun x reset) w)).2=admitOp (params d s)) :
    let y := rawNext s (rawRun (rawRun x reset) w) (out C (C.a+1))
    tok d C y (C.a+1)=MISByteCodec.T ∧
      tok d C y (C.a+2)={tag:=2,opcode:=admitOp (params d s),payload:=0,race:=1} := by
  have Z := (cached_genuine_full_parked d C N hh F x X reset R).1
  have I := off_front_of_receipt d C hh G F N digit x X reset w R (C.a+1) (by omega) A Op
  have Y' : Cached d hh Q (rawRun (rawRun x reset) w) := by
    have cached_run (z : Raw s n) (Z : Cached d hh Q z) (t : List (Fin n)) : Cached d hh Q (rawRun z t) := by
      induction t generalizing z with
      | nil => exact Z
      | cons e t IH => exact IH _ ((cached_fibre d N hh Q F).closed z e Z)
    exact cached_run _ Z w
  exact origin_arrive d C hh G F N _ Y' (C.a+1) I (by omega)

#print axioms off_hold
#print axioms off_hop
#print axioms origin_launch
#print axioms origin_seed
#print axioms before_gate_mark
#print axioms origin_arrive
#print axioms before_gate_tape
#print axioms before_turn_off
#print axioms off_front_of_issue_history
#print axioms off_front_of_receipt
#print axioms arrival_of_receipt
end L4.ReportAdmitAncestry
