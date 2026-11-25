import Leader.L4.ReportOwnerAcquireReturn
import Leader.L4.ReportOwnerSerial
import Leader.L4.ReportLeaseOwner
import Leader.L4.ReportAcquireCaptureBits

namespace L4.ReportOwnerAcquireProvenance
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ShortLayerGeometry ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportByteRows
open ReportRawProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerIssueControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportLeaseGrants ReportJoinedGrants

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Frozen geometry, not a premise concerning the current work bytes. -/
theorem centre_geometry (C : Chart h) (G : GapInput h) :
    C.a+1<C.L ∧ ∀ i,i<C.L→
      (h (out C i)=true ∧ C.route.port i=1 ↔ i=C.a) := by
  obtain ⟨a,A,A',F⟩ := G.gaps C.root C.rootHeader
  obtain ⟨b,B,B',J⟩ := G.gaps (nextAt C.root a) F.atEnd
  obtain ⟨c,D,D',K⟩ := G.gaps (nextAt (nextAt C.root a) b) J.atEnd
  have room : a+b+c<n := by have := G.room; omega
  let C' := chart_of_three C.rootHeader F J K room
  have U := ShortReadCaptureGeometry.chart_unique C C' rfl
  have L : C.L=a+b+c := U.1
  have ports (i : Nat) (I : i<C.L) :
      C.route.port i=ShortResetChart.lane a b i := U.2 i I
  have one : ShortResetChart.lane C.a C.b a=1 := by
    exact (ports a (by omega)).trans
      (by simp [ShortResetChart.lane,show a<a+b by omega])
  have zero : ShortResetChart.lane C.a C.b (a-1)=0 := by
    exact (ports (a-1) (by omega)).trans
      (by simp [ShortResetChart.lane,show a-1<a by omega])
  have V := (lane1 _ _ _).mp one
  have W := (lane0 _ _ _).mp zero
  have ca : C.a=a := by omega
  refine ⟨by omega,?_⟩
  intro i I
  rw [ports i I,ca]
  constructor
  · rintro ⟨H,P⟩
    have R := (lane1 a b i).mp P
    have Z := (three_gap_exact F J K i (by omega) (by omega)).mp H
    omega
  · intro E
    subst i
    exact ⟨F.atEnd,by simp [ShortResetChart.lane,show a<a+b by omega]⟩

def stepPayload (d : Sheet) (C : Chart h) (x : Raw s n) (k q : Nat) : Nat :=
  acqFlightNext (params d s) (h (out C k)) (bytesL d x (out C k))
    (C.route.port k) q

def CentreWin (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  acqFlightWin (params d s) true (selectBytes d (x (out C C.a))) 1=true

def CentreSample (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  publicationSelector (params d s) (selectBytes d (x (out C C.a)))

structure FState (d : Sheet) (C : Chart h) (x : Raw s n) (k q : Nat) : Prop where
  shape : ForwardWait d C x k
  pc : readPC d C x=(2,acqOp (params d s))
  bound : q<128
  packet : tok d C x k=acqFlightF (params d s) q

structure DState (d : Sheet) (C : Chart h) (x : Raw s n) (k q : Nat) : Prop where
  shape : ReverseWait d C x k
  pc : readPC d C x=(2,acqOp (params d s))
  bound : q<128
  packet : tok d C x k=acqFlightD (params d s) q

private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

private theorem not_ready (p : Params) (hu : Bool) (u : BitVec p.w) (j : Fin 3)
    (T : (publicationToken p hu u j).tag≠2) : rankReady p hu u j=false := by
  apply Bool.eq_false_iff.mpr
  intro H
  exact T ((rankReady_iff p hu u j).mp H).1

private theorem incoming_zero (C : Chart h) (e : Fin n)
    (E : rightNeighbor e=out C 0) : e=door C := by
  unfold door
  have R : out C 0=C.root := rfl
  rw [←R,←E,RearTrace.predecessor_right]

private theorem incoming_succ (C : Chart h) (e : Fin n) (j : Nat)
    (E : rightNeighbor e=out C (j+1)) : e=out C j :=
  ShortChartOwnership.right_injective (E.trans (chart_succ C j).symm)

private theorem spectator_token (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (I : k<C.L) (e : Fin n)
    (A : e≠out C k) (B : rightNeighbor e≠out C k) :
    tok d C (rawNext s x e) k=tok d C x k := by
  apply decoded_frame d C hh G x _ X
    ((cached_fibre d N hh Q F).closed x e X) k I
  unfold wire
  rw [raw_spectator x e _ (Ne.symm A) (Ne.symm B)]

private theorem wait_pc (d : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (P : readPC d C x=(2,acqOp (params d s)))
    (T : e=door C → (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2) :
    readPC d C (rawNext s x e)=readPC d C x := by
  by_cases E : e=door C
  · have A := T E
    subst e
    rw [root_pub] at A
    let p := params d s
    let v := selectBytes d (x C.root)
    let t := publicationToken p true v 0
    have V : sourcePhase p v=2 := congrArg Prod.fst P
    have O : sourceOpcode p v≤commitOp p := by
      have O0 : sourceOpcode p v=acqOp p := congrArg Prod.snd P
      rw [O0]
      unfold acqOp commitOp
      omega
    exact (raw_door_final d C x N mask).1.trans
      (prelaunch_hold_controls p v t V O A)
  · exact raw_nondoor_control d C x e N mask E

theorem launch (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (P : readPC d C x=(1,acqOp (params d s))) :
    Cached d hh Q (rawNext s x (door C)) ∧
    FState d C (rawNext s x (door C)) 0 64 := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let y := rawNext s x (door C)
  let CF := cached_fibre d N hh Q F
  have Y := CF.closed x (door C) X
  have P0 : sourcePhase p v=1 := congrArg Prod.fst P
  have P1 : sourceOpcode p v=acqOp p := congrArg Prod.snd P
  have W := (raw_door_final d C x N (CF.mask x X)).2
  change resetTokenRead p (selectBytes d (y C.root)) 0 =
    (match (source p v (publicationToken p true v 0)).2 with
      | none => prelaunchDoorNormWire p v
      | some t => resetTokenWire p t) at W
  rw [acqFlight_issue p v _ P0 P1] at W
  have A : tok d C y 0=acqFlightF p 64 := by
    rw [root_tok,W]
    exact acqFlight_F_roundtrip p false 64 (by decide)
  rcases ReportOwnerIssueControl.door_step d C hh G F N x X I with B|⟨B,J⟩
  · have H := B.2.2 0 C.positive
    rw [A] at H
    contradiction
  · exact ⟨Y,⟨B,Prod.ext B.1.1 (J.trans P1),by decide,A⟩⟩

theorem raw_hop (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k q : Nat) (I : k+1<C.L) (R : FState d C x k q) :
    tok d C (rawNext s x (out C k)) (k+1)=
      acqFlightF (params d s) (stepPayload d C x k q) := by
  have A := R.packet
  rw [predecessor_projection] at A
  have W := raw_pair_wire d C x N mask k
  rw [tok_wire,W.2]
  exact rankAcq_hop (params d s) (h (out C k)) (h (rightNeighbor (out C k)))
    (bytesL d x (out C k)) (bytesR d x (out C k)) _ _
    (internal_dest C k I) _ q R.bound A

theorem raw_turn (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k q : Nat) (I : k+1=C.L) (R : FState d C x k q) :
    tok d C (rawNext s x (out C k)) k=
      acqFlightD (params d s) (stepPayload d C x k q) := by
  have A := R.packet
  rw [predecessor_projection] at A
  have W := raw_pair_wire d C x N mask k
  rw [tok_wire,W.1]
  exact rankAcq_turn (params d s) (h (out C k)) (h (rightNeighbor (out C k)))
    (bytesL d x (out C k)) (bytesR d x (out C k)) _
    (end_dest C k I) _ q R.bound A

private theorem F_root_hold (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (q : Nat) (R : FState d C x 0 q) :
    tok d C (rawNext s x (door C)) 0=tok d C x 0 := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have E : t=acqFlightF p q := (root_pub d C x).symm.trans R.packet
  have P : sourcePhase p v=2 := congrArg Prod.fst R.pc
  have O : sourceOpcode p v≤commitOp p := by
    have O0 : sourceOpcode p v=acqOp p := congrArg Prod.snd R.pc
    rw [O0]
    unfold acqOp commitOp
    omega
  have H : t.tag=2 := by rw [E]; rfl
  have L : t.fault=false := by rw [E]; rfl
  have W := (raw_door_final d C x N mask).2
  change resetTokenRead p (selectBytes d (rawNext s x (door C) C.root)) 0 =
    (match (source p v t).2 with
      | none => prelaunchDoorNormWire p v
      | some z => resetTokenWire p z) at W
  rw [prelaunch_wait_hold p v t P O (.inr H)] at W
  rw [rankAcq_door_norm p v L] at W
  rw [root_tok,root_tok,W]

private theorem F_incoming_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (j q : Nat) (R : FState d C x (j+1) q) :
    tok d C (rawNext s x (out C j)) (j+1)=tok d C x (j+1) := by
  let p := params d s
  let e := out C j
  let u := bytesL d x e
  let v := bytesR d x e
  let a := C.route.port j
  let b := C.route.port (j+1)
  let CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have I := R.shape.2.1
  have L : (tok d C x j).tag=1 := by
    rw [R.shape.2.2 j (by omega)]
    simp [frontTag]
  rw [predecessor_projection] at L
  have A := R.packet
  rw [successor_projection] at A
  have NR := not_ready p (h e) u a (by rw [L]; decide)
  have T : (publicationToken p (h (rightNeighbor e)) v b).tag≠3 := by
    rw [A]; change (2:Nat)≠3; decide
  have W := raw_pair_wire d C x N (CF.mask x X) j
  have E := rank_idle_right p (h e) (h (rightNeighbor e)) u v a b
    (internal_dest C j I) NR (.inr T)
  have Norm := rankAcq_norm p 2 (h (rightNeighbor e)) v b
    (by rw [A]; rfl) (by rw [A]; rfl)
  apply decoded_frame d C hh G x _ X Y (j+1) I
  rw [W.2,workR,E,Norm]
  rfl

private theorem F_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k q : Nat) (R : FState d C x k q) (e : Fin n) (E : e≠out C k) :
    tok d C (rawNext s x e) k=tok d C x k := by
  by_cases H : rightNeighbor e=out C k
  · cases k with
    | zero =>
      have A := incoming_zero C e H
      subst e
      exact F_root_hold d C x N ((cached_fibre d N hh Q F).mask x X) q R
    | succ j =>
      have A := incoming_succ C e j H
      subst e
      exact F_incoming_hold d C hh G F N x X j q R
  · exact spectator_token d C hh G F N x X k R.shape.2.1 e E H

theorem raw_reverse_hop (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j q : Nat) (R : DState d C x (j+1) q) :
    tok d C (rawNext s x (out C j)) j=acqFlightD (params d s) q := by
  have I := R.shape.2.1
  have T : (tok d C x j).tag≠2 := by
    rw [R.shape.2.2 j (by omega)]
    simp [backTag]
  have D : (tok d C x (j+1)).tag=3 := by rw [R.packet]; simp
  have W := (reverse_joined d C x N mask j I T D).1
  rw [tok_wire,W,R.packet]
  exact acqFlight_D_roundtrip (params d s) _ q

private theorem D_outgoing_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k q : Nat) (R : DState d C x k q) :
    tok d C (rawNext s x (out C k)) k=tok d C x k := by
  let p := params d s
  let e := out C k
  let u := bytesL d x e
  let v := bytesR d x e
  let a := C.route.port k
  let CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have I := R.shape.2.1
  have A := R.packet
  rw [predecessor_projection] at A
  have T : (publicationToken p (h e) u a).tag≠2 := by rw [A]; simp
  have NR := not_ready p (h e) u a T
  have H : match reset0Destination (h (rightNeighbor e)) a with
    | none => (publicationToken p (h e) u a).tag≠1
    | some b => (publicationToken p (h (rightNeighbor e)) v b).tag≠3 ∧
      ¬((publicationToken p (h e) u a).tag=1 ∧
         (publicationToken p (h (rightNeighbor e)) v b).tag=0) := by
    by_cases K : k+1<C.L
    · rw [internal_dest C k K]
      have S : (tok d C x (k+1)).tag=0 := by
        rw [R.shape.2.2 (k+1) K]
        simp [backTag]
      rw [successor_projection] at S
      exact ⟨by rw [S]; decide,by rw [A]; simp⟩
    · rw [end_dest C k (by omega),A]
      simp
  have E := rank_idle_left p (h e) (h (rightNeighbor e)) u v a NR (.inr ⟨T,H⟩)
  have Norm := rankAcq_norm p 3 (h e) u a (by rw [A]; simp) (by rw [A]; exact acqFlightD_op p q)
  apply decoded_frame d C hh G x _ X Y k I
  rw [(raw_pair_wire d C x N (CF.mask x X) k).1,workL,E,Norm]
  rfl

def NoConsume (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  e≠door C ∨ (tok d C x 0).tag≠3

private theorem D_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k q : Nat) (R : DState d C x k q) (e : Fin n)
    (M : ¬∃ j,k=j+1 ∧ e=out C j) (NC : NoConsume d C x e) :
    tok d C (rawNext s x e) k=tok d C x k := by
  by_cases E : e=out C k
  · subst e
    exact D_outgoing_hold d C hh G F N x X k q R
  · by_cases H : rightNeighbor e=out C k
    · cases k with
      | zero =>
        have A := incoming_zero C e H
        have T : (tok d C x 0).tag=3 := by rw [R.packet]; simp
        exact (NC.elim (fun B=>B A) (fun B=>B T)).elim
      | succ j =>
        exact (M ⟨j,rfl,incoming_succ C e j H⟩).elim
    · exact spectator_token d C hh G F N x X k R.shape.2.1 e E H

/-- The structural all-mark theorem is used only for tags. The packet
    equality is proved independently from the complete physical rows. -/
theorem F_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k q : Nat)
    (R : FState d C x k q) (e : Fin n) :
    let y := rawNext s x e
    FState d C y k q ∨
      (e=out C k ∧ FState d C y (k+1) (stepPayload d C x k q)) ∨
      (e=out C k ∧ k+1=C.L ∧ DState d C y k (stepPayload d C x k q)) := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  let y := rawNext s x e
  have I := R.shape.2.1
  have HT : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
    rw [R.shape.2.2 0 C.positive]
    by_cases Z : k=0
    · subst k; exact .inr rfl
    · exact .inl (by simp [frontTag,show 0<k by omega])
  have PC := (wait_pc d C x e N (CF.mask x X) R.pc (fun _=>HT)).trans R.pc
  have S := ReportOwnerForwardControl.all_mark d C hh G F N x X k R.shape e
  have B := (acqFlight_next_spec (params d s) (h (out C k))
    (bytesL d x (out C k)) (C.route.port k) q R.bound).1
  by_cases E : e=out C k
  · subst e
    by_cases J : k+1<C.L
    · have A := raw_hop d C x N (CF.mask x X) k q J R
      rcases S with H|⟨_,H|⟨K,H⟩⟩
      · have T := H.2.2 (k+1) J
        rw [A] at T
        simp [acqFlightF,frontTag,show ¬k+1<k by omega] at T
      · exact .inr (.inl ⟨rfl,⟨H,PC,B,A⟩⟩)
      · omega
    · have J0 : k+1=C.L := by omega
      have A := raw_turn d C x N (CF.mask x X) k q J0 R
      rcases S with H|⟨_,H|⟨K,H⟩⟩
      · have T := H.2.2 k I
        rw [A] at T
        simp [frontTag] at T
      · have Z := H.2.1
        omega
      · exact .inr (.inr ⟨rfl,J0,⟨H,PC,B,A⟩⟩)
  · rcases S with H|⟨U,_⟩
    · exact .inl ⟨H,PC,R.bound,(F_hold d C hh G F N x X k q R e E).trans R.packet⟩
    · exact (E U).elim

theorem D_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k q : Nat)
    (R : DState d C x k q) (digit : 0<(params d s).digits)
    (e : Fin n) (NC : NoConsume d C x e) :
    let y := rawNext s x e
    DState d C y k q ∨ ∃ j,k=j+1 ∧ e=out C j ∧ DState d C y j q := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  have rootD (Z : k=0) : (tok d C x 0).tag=3 := by
    rw [←Z,R.packet]
    simp
  have HT (E : e=door C) : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
    have K : k≠0 := fun Z=>NC.elim (fun L=>L E) (fun L=>L (rootD Z))
    rw [R.shape.2.2 0 C.positive]
    exact .inl (by simp [backTag,show 0<k by omega])
  have PC := (wait_pc d C x e N (CF.mask x X) R.pc HT).trans R.pc
  have S := ReportOwnerReverseControl.all_mark d C hh G F N x X k R.shape digit e
  by_cases M : ∃ j,k=j+1 ∧ e=out C j
  · obtain ⟨j,J,E⟩ := M
    subst k e
    have A := raw_reverse_hop d C x N (CF.mask x X) j q R
    rcases S with H|⟨l,L,_,H⟩|⟨Z,_,_⟩
    · have T := H.2.2 j (by have := R.shape.2.1; omega)
      rw [A] at T
      simp [backTag] at T
    · have L0 : l=j := by omega
      subst l
      exact .inr ⟨j,rfl,rfl,⟨H,PC,R.bound,A⟩⟩
    · omega
  · rcases S with H|⟨j,J,E,_⟩|⟨Z,E,_⟩
    · exact .inl ⟨H,PC,R.bound,(D_hold d C hh G F N x X k q R e M NC).trans R.packet⟩
    · exact (M ⟨j,J,E⟩).elim
    · exact (NC.elim (fun B=>B E) (fun B=>B (rootD Z))).elim

theorem centre_grant (d : Sheet) (C : Chart h) (G : GapInput h)
    (x : Raw s n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (W : CentreWin d C x) :
    rawGrant d (rawNext s x (out C C.a)) (out C C.a) 1=true := by
  let e := out C C.a
  have L := centre_geometry C G
  have H := (L.2 C.a (by omega)).mpr rfl
  have A := (raw_grant_rows d x e (edge_sep N e) 1).1
  rw [mask e,H.1,next_agrees] at A
  exact A.trans (acqFlight_win_grant (params d s) (selectBytes d (x e)) 1 W)

/-- A witness is a literal prefix/suffix split of the original tape.
    The state before the centre mark is reconstructed, not supplied
    independently as a possibly unrelated old snapshot. -/
def Witness (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (q : Nat) : Prop :=
  ∃ u v : List (Fin n), ∃ r : Nat,
    w=u++(out C C.a::v) ∧
    let z := rawRun x0 u
    FState d C z C.a r ∧ CentreWin d C z ∧
    rawGrant d (rawNext s z (out C C.a)) (out C C.a) 1=true ∧
    q/16%2=CentreSample d C z

private theorem witness_extend (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (e : Fin n) (q r : Nat)
    (W : Witness d C x0 w q) (E : r/16%2=q/16%2) :
    Witness d C x0 (w++[e]) r := by
  obtain ⟨u,v,q0,L,A,B,D,Z⟩ := W
  refine ⟨u,v++[e],q0,?_,A,B,D,E.trans Z⟩
  rw [L,List.append_assoc]
  rfl

def FlightAt (d : Sheet) (C : Chart h) (x0 : Raw s n) (w : List (Fin n)) : Prop :=
  (∃ k q, FState d C (rawRun x0 w) k q ∧
      (C.a<k → q/64=1 → Witness d C x0 w q)) ∨
  (∃ k q, DState d C (rawRun x0 w) k q ∧
      (q/64=1 → Witness d C x0 w q))

private theorem advance_witness (d : Sheet) (C : Chart h)
    (G : GapInput h) (N : 1<n) (x0 : Raw s n) (w : List (Fin n))
    (mask : ∀ i,lower d (oldHeaders (rows s) (rawRun x0 w i))=h i)
    (k q : Nat) (R : FState d C (rawRun x0 w) k q)
    (Old : C.a<k → q/64=1 → Witness d C x0 w q)
    (P : C.a<k+1)
    (Success : stepPayload d C (rawRun x0 w) k q/64=1) :
    Witness d C x0 (w++[out C k]) (stepPayload d C (rawRun x0 w) k q) := by
  let x := rawRun x0 w
  let p := params d s
  have Geo := centre_geometry C G
  have I := R.shape.2.1
  have S := acqFlight_next_spec p (h (out C k)) (bytesL d x (out C k))
    (C.route.port k) q R.bound
  change (stepPayload d C x k q)<128 ∧
    (stepPayload d C x k q/64=1→q/64=1) ∧
    (h (out C k)=true ∧ C.route.port k=1 →
      stepPayload d C x k q/64=1 →
      acqFlightWin p (h (out C k)) (bytesL d x (out C k)) (C.route.port k)=true ∧
      stepPayload d C x k q/16%2=publicationSelector p (bytesL d x (out C k))) ∧
    (¬(h (out C k)=true ∧ C.route.port k=1) →
      stepPayload d C x k q/16%2=q/16%2) at S
  by_cases K : k=C.a
  · subst k
    have H := (Geo.2 C.a I).mpr rfl
    have T := S.2.2.1 H Success
    have W : CentreWin d C x := by
      unfold CentreWin
      simpa only [H.1,H.2,bytesL] using T.1
    exact ⟨w,[],q,rfl,R,W,centre_grant d C G x N mask W,T.2⟩
  · have H : ¬(h (out C k)=true ∧ C.route.port k=1) :=
      fun T=>K ((Geo.2 k I).mp T)
    exact witness_extend d C x0 w (out C k) q _
      (Old (by omega) (S.2.1 Success)) (S.2.2.2 H)

theorem flight_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (w : List (Fin n))
    (X : Cached d hh Q (rawRun x0 w)) (A : FlightAt d C x0 w)
    (digit : 0<(params d s).digits) (e : Fin n)
    (NC : NoConsume d C (rawRun x0 w) e) :
    FlightAt d C x0 (w++[e]) := by
  let x := rawRun x0 w
  let CF := cached_fibre d N hh Q F
  have E : rawRun x0 (w++[e])=rawNext s x e :=
    ShortOwnerEpochJS.raw_snoc x0 w e
  rcases A with ⟨k,q,R,H⟩|⟨k,q,R,H⟩
  · rcases F_step d C hh G F N x X k q R e with A|⟨J,A⟩|⟨J,T,A⟩
    · left
      refine ⟨k,q,?_,fun P S=>witness_extend d C x0 w e q q (H P S) rfl⟩
      rw [E]
      exact A
    · subst e
      left
      refine ⟨k+1,stepPayload d C x k q,?_,?_⟩
      · rw [E]
        exact A
      · intro P S
        exact advance_witness d C G N x0 w (CF.mask x X) k q R H P S
    · subst e
      right
      refine ⟨k,stepPayload d C x k q,?_,?_⟩
      · rw [E]
        exact A
      · intro S
        have C0 := (centre_geometry C G).1
        exact advance_witness d C G N x0 w (CF.mask x X) k q R H (by omega) S
  · rcases D_step d C hh G F N x X k q R digit e NC with A|⟨j,_,_,A⟩
    · right
      refine ⟨k,q,?_,fun S=>witness_extend d C x0 w e q q (H S) rfl⟩
      rw [E]
      exact A
    · right
      refine ⟨j,q,?_,fun S=>witness_extend d C x0 w e q q (H S) rfl⟩
      rw [E]
      exact A

/-- Exactly the prefixes up to, but not including, this command's
    first door-consume mark. The test is on each actual OLD state.
    Other marks at a root D (including arbitrarily many repeats of
    its outgoing edge) remain in the prefix. -/
inductive BeforeConsume (d : Sheet) (C : Chart h) (x0 : Raw s n) :
    List (Fin n) → Prop
  | nil : BeforeConsume d C x0 []
  | snoc {w : List (Fin n)} (e : Fin n) (old : BeforeConsume d C x0 w)
      (nc : NoConsume d C (rawRun x0 w) e) :
      BeforeConsume d C x0 (w++[e])

theorem flight_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w) :
    Cached d hh Q (rawRun x0 w) ∧ FlightAt d C x0 w := by
  induction T with
  | nil =>
    exact ⟨X,.inl ⟨0,64,A,fun H=> (by omega : False).elim⟩⟩
  | @snoc w e T NC IH =>
    -- CHECK: ShortOwnerEpochJS.lean:28–35, raw_snoc and
    -- constructor induction binder order for BeforeConsume.snoc.
    constructor
    · rw [ShortOwnerEpochJS.raw_snoc]
      exact (cached_fibre d N hh Q F).closed _ e IH.1
    · exact flight_step d C hh G F N x0 w IH.1 IH.2 digit e NC

/-- A successful root reply belongs to this flight. No separate
    "matching generation" or "no foreign D" input occurs. -/
theorem successful_root (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (Tag : (tok d C (rawRun x0 w) 0).tag=3)
    (ND : (tok d C (rawRun x0 w) 0).outcome≠1) :
    let x := rawRun x0 w
    Cached d hh Q x ∧ ReverseWait d C x 0 ∧
    (readPC d C x).2=acqOp (params d s) ∧
    (tok d C x 0).opcode=acqOp (params d s) ∧
    (tok d C x 0).fault=false ∧
    ∃ u v : List (Fin n), ∃ q : Nat,
      w=u++(out C C.a::v) ∧
      let z := rawRun x0 u
      FState d C z C.a q ∧ CentreWin d C z ∧
      rawGrant d (rawNext s z (out C C.a)) (out C C.a) 1=true ∧
      (tok d C x 0).payload/16%2=CentreSample d C z := by
  dsimp only
  obtain ⟨Y,H⟩ := flight_run d C hh G F N x0 X A digit w T
  rcases H with ⟨k,q,R,_⟩|⟨k,q,R,W⟩
  · rw [R.shape.2.2 0 C.positive] at Tag
    unfold frontTag at Tag
    split at Tag <;> try contradiction
    split at Tag <;> contradiction
  · have K : k=0 := by
      by_cases K : k=0
      · exact K
      · rw [R.shape.2.2 0 C.positive] at Tag
        simp [backTag,show 0<k by omega] at Tag
    subst k
    have ND0 : (acqFlightD (params d s) q).outcome≠1 := by
      rw [←R.packet]
      exact ND
    have P := acqFlight_D_success (params d s) q R.bound ND0
    obtain ⟨u,v,r,L,Old,Win,Grant,B⟩ := W P.1
    refine ⟨Y,R.shape,congrArg Prod.snd R.pc,?_,?_,u,v,r,L,Old,Win,Grant,?_⟩
    · rw [R.packet]; simp
    · rw [R.packet]; simp
    · rw [R.packet,P.2]
      exact B

/-- Public entry point: an actual empty legal ISSUE(ACQ) and the
    actual next door mark, followed by any prefix before its consume. -/
theorem from_genuine_issue (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s x (door C)) w) 0).outcome≠1) :
    let x0 := rawNext s x (door C)
    let y := rawRun x0 w
    Cached d hh Q y ∧ ReverseWait d C y 0 ∧
    (readPC d C y).2=acqOp (params d s) ∧
    (tok d C y 0).opcode=acqOp (params d s) ∧
    (tok d C y 0).fault=false ∧
    ∃ u v : List (Fin n), ∃ q : Nat,
      w=u++(out C C.a::v) ∧
      let z := rawRun x0 u
      FState d C z C.a q ∧ CentreWin d C z ∧
      rawGrant d (rawNext s z (out C C.a)) (out C C.a) 1=true ∧
      (tok d C y 0).payload/16%2=CentreSample d C z := by
  obtain ⟨Y,A⟩ := launch d C hh G F N x X I P
  exact successful_root d C hh G F N _ Y A digit w T Tag ND

#print axioms centre_grant
#print axioms flight_step
#print axioms flight_run
#print axioms successful_root
#print axioms from_genuine_issue

/-- Compose the authentic centre sample with the literal source consume
and file transport on the original suffix. The result refers to the
actual winning old state, not the current selector at the consumer. -/
theorem genuine_issue_installs_centre_sample (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (P : readPC d C x=(1,acqOp (params d s))) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s x (door C)) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : ReportOwnerAcquireReturn.NoRestartTape d C
      (rawNext s (rawRun (rawNext s x (door C)) w) (door C)) v) :
    let launched := rawNext s x (door C)
    let old := rawRun launched w
    let final := rawRun (rawNext s old (door C)) v
    Cached d hh Q final ∧ PostAcqPC (params d s) (readPC d C final) ∧
    ∃ pre post : List (Fin n), ∃ q : Nat,
      w=pre++(out C C.a::post) ∧
      let z := rawRun launched pre
      FState d C z C.a q ∧ CentreWin d C z ∧
      rawGrant d (rawNext s z (out C C.a)) (out C C.a) 1=true ∧
      ReportWriterPayload.capturedSelector (params d s)
        (selectBytes d (final C.root))=CentreSample d C z := by
  dsimp only
  let launched := rawNext s x (door C)
  let old := rawRun launched w
  obtain ⟨Y,R,O,K,Live,pre,post,q,W,Old,Win,Grant,Sample⟩ :=
    from_genuine_issue d C hh G F N x X I P digit w T Tag ND
  have S : acqReplyCentre (tok d C old 0)=CentreSample d C (rawRun launched pre) :=
    Sample
  have A := ReportOwnerAcquireReturn.acq_consume_then_run
    d C hh G F N old Y R O K Live ND (CentreSample d C (rawRun launched pre)) S digit v NR
  exact ⟨A.1,A.2.1,pre,post,q,W,Old,Win,Grant,A.2.2.2⟩

#print axioms genuine_issue_installs_centre_sample

/-- A real RESET receipt followed by an actual prefix to ISSUE(ACQ)
supplies the legal empty rail required by the flight theorem. The
prefix may include competing marks and unrelated owner activity. -/
theorem legal_acq_issue_after_receipt (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (reset pre : List (Fin n))
    (Receipt : Generated d C x reset .done) (digit : 0<(params d s).digits)
    (PC : readPC d C (rawRun x (reset++pre))=(1,acqOp (params d s))) :
    let y := rawRun x (reset++pre)
    Cached d hh Q y ∧ LegalIssue d C y := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  have Both (z : Raw s n) (w : List (Fin n))
      (Y : Cached d hh Q z) (S : ReportOwnerSerial.Serial d C z) :
      Cached d hh Q (rawRun z w) ∧ ReportOwnerSerial.Serial d C (rawRun z w) := by
    induction w generalizing z with
    | nil => exact ⟨Y,S⟩
    | cons e w IH =>
      exact IH (rawNext s z e) (CF.closed z e Y)
        (ReportOwnerSerial.all_mark d C N hh G F z Y S digit e)
  have A := ReportOwnerSerial.seed_at_genuine_receipt d C N hh F x X reset Receipt
  have C0 := (cached_genuine_full_parked d C N hh F x X reset Receipt).1
  have H := Both _ pre C0 A
  rw [←ShortOwnerEpochJS.raw_append] at H
  refine ⟨H.1,?_⟩
  rcases H.2 with S|⟨k,S⟩|⟨k,S⟩
  · exact S
  · have E := S.1.1
    rw [PC] at E
    change (1:Nat)=2 at E
    omega
  · have E := S.1.1
    rw [PC] at E
    change (1:Nat)=2 at E
    omega

#print axioms legal_acq_issue_after_receipt

#print axioms centre_geometry
#print axioms launch
#print axioms raw_hop
#print axioms raw_turn
#print axioms raw_reverse_hop
#print axioms F_step
#print axioms D_step
end L4.ReportOwnerAcquireProvenance
