import Leader.L4.ReportAcquireAllCaptures
import Leader.L4.ReportOwnerCommandRail

namespace L4.ReportOwnerIndexedFlight
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ShortLayerGeometry ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportByteRows
open ReportRawProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerIssueControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportLeaseGrants ReportJoinedGrants
open ReportOwnerAcquireProvenance (NoConsume BeforeConsume)

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def stepPayload (d : Sheet) (C : Chart h) (op : Nat)
    (x : Raw s n) (k : Nat) (q : Option IndexedData) : Option IndexedData :=
  indexedNext (params d s) op (h (out C k))
    (bytesL d x (out C k)) (C.route.port k) q

structure FState (d : Sheet) (C : Chart h) (op : Nat) (x : Raw s n)
    (k : Nat) (q : Option IndexedData) : Prop where
  shape : ForwardWait d C x k
  pc : readPC d C x=(2,op)
  bound : IndexedGood (params d s) op q
  packet : tok d C x k=indexedF (params d s) op q

structure DState (d : Sheet) (C : Chart h) (op : Nat) (x : Raw s n)
    (k : Nat) (q : Option IndexedData) : Prop where
  shape : ReverseWait d C x k
  pc : readPC d C x=(2,op)
  bound : IndexedGood (params d s) op q
  packet : tok d C x k=indexedD (params d s) op q

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

private theorem wait_pc (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (P : readPC d C x=(2,op))
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
      have O0 : sourceOpcode p v=op := congrArg Prod.snd P
      rw [O0]
      exact indexed_op_le p op Range
    exact (raw_door_final d C x N mask).1.trans
      (prelaunch_hold_controls p v t V O A)
  · exact raw_nondoor_control d C x e N mask E

theorem raw_hop (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (q : Option IndexedData) (I : k+1<C.L) (R : FState d C op x k q) :
    tok d C (rawNext s x (out C k)) (k+1)=
      indexedF (params d s) op (stepPayload d C op x k q) := by
  have A := R.packet
  rw [predecessor_projection] at A
  have W := raw_pair_wire d C x N mask k
  rw [tok_wire,W.2]
  exact rankIndexed_hop (params d s) op Range (h (out C k)) (h (rightNeighbor (out C k)))
    (bytesL d x (out C k)) (bytesR d x (out C k)) _ _
    (internal_dest C k I) _ q R.bound A

theorem raw_turn (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (q : Option IndexedData) (I : k+1=C.L) (R : FState d C op x k q) :
    tok d C (rawNext s x (out C k)) k=
      indexedD (params d s) op (stepPayload d C op x k q) := by
  have A := R.packet
  rw [predecessor_projection] at A
  have W := raw_pair_wire d C x N mask k
  rw [tok_wire,W.1]
  exact rankIndexed_turn (params d s) op Range (h (out C k)) (h (rightNeighbor (out C k)))
    (bytesL d x (out C k)) (bytesR d x (out C k)) _
    (end_dest C k I) _ q R.bound A

private theorem F_root_hold (d : Sheet) (C : Chart h)
    (op : Nat) (Range : IndexedOp (params d s) op) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (q : Option IndexedData) (R : FState d C op x 0 q) :
    tok d C (rawNext s x (door C)) 0=tok d C x 0 := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have E : t=indexedF p op q := (root_pub d C x).symm.trans R.packet
  have P : sourcePhase p v=2 := congrArg Prod.fst R.pc
  have O : sourceOpcode p v≤commitOp p := by
    have O0 : sourceOpcode p v=op := congrArg Prod.snd R.pc
    rw [O0]
    exact indexed_op_le p op Range
  have H : t.tag=2 := by rw [E]; simp
  have W := (raw_door_final d C x N mask).2
  change resetTokenRead p (selectBytes d (rawNext s x (door C) C.root)) 0 =
    (match (source p v t).2 with
      | none => prelaunchDoorNormWire p v
      | some z => resetTokenWire p z) at W
  rw [prelaunch_wait_hold p v t P O (.inr H)] at W
  rw [root_tok d C (rawNext s x (door C)),W,root_pub]
  exact indexed_root_norm p v

private theorem chart_rank_gate (d : Sheet) (C : Chart h)
    (x : Raw s n) (i : Nat) :
    chartGate d C x i=rankGate (params d s) (h (out C i))
      (bytesL d x (out C i)) (C.route.port i) := rfl

private theorem F_incoming_hold (d : Sheet) (C : Chart h)
    (op : Nat) (_Range : IndexedOp (params d s) op)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (j : Nat) (q : Option IndexedData) (R : FState d C op x (j+1) q) :
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
    rw [A]
    simp
  have W := raw_pair_wire d C x N (CF.mask x X) j
  have E := rank_idle_right p (h e) (h (rightNeighbor e)) u v a b
    (internal_dest C j I) NR (.inr T)
  have Z : (decode p (chartGate d C x (j+1)) (wire d C x (j+1))).race=0 := by
    rw [←tok_wire,R.packet]
    simp
  rw [tok_wire,gate_frame d C hh G x _ X Y (j+1) I,W.2,workR,E]
  -- CHECK: ReportOwnerProvenanceTransport.successor_projection;
  -- the old gate and old wire are exactly those of the right site.
  change decode p (chartGate d C x (j+1))
    (rankNormWire p 2 (chartGate d C x (j+1)) (wire d C x (j+1)))=_
  exact (indexed_zero_race_norm p _ _ 2 (.inl rfl) Z).trans (tok_wire d C x (j+1)).symm

private theorem D_outgoing_hold (d : Sheet) (C : Chart h)
    (op : Nat) (_Range : IndexedOp (params d s) op)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (q : Option IndexedData) (R : DState d C op x k q) :
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
  have Z : (decode p (chartGate d C x k) (wire d C x k)).race=0 := by
    rw [←tok_wire,R.packet]
    simp
  rw [tok_wire,gate_frame d C hh G x _ X Y k I,
    (raw_pair_wire d C x N (CF.mask x X) k).1,workL,E]
  change decode p (chartGate d C x k)
    (rankNormWire p 3 (chartGate d C x k) (wire d C x k))=_
  exact (indexed_zero_race_norm p _ _ 3 (.inr rfl) Z).trans (tok_wire d C x k).symm

private theorem F_hold (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (q : Option IndexedData) (R : FState d C op x k q) (e : Fin n) (E : e≠out C k) :
    tok d C (rawNext s x e) k=tok d C x k := by
  by_cases H : rightNeighbor e=out C k
  · cases k with
    | zero =>
      have A := incoming_zero C e H
      subst e
      exact F_root_hold d C op Range x N ((cached_fibre d N hh Q F).mask x X) q R
    | succ j =>
      have A := incoming_succ C e j H
      subst e
      exact F_incoming_hold d C op Range hh G F N x X j q R
  · exact spectator_token d C hh G F N x X k R.shape.2.1 e E H

theorem raw_reverse_hop (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (q : Option IndexedData) (R : DState d C op x (j+1) q) :
    tok d C (rawNext s x (out C j)) j=indexedD (params d s) op q := by
  have I := R.shape.2.1
  have T : (tok d C x j).tag≠2 := by
    rw [R.shape.2.2 j (by omega)]
    simp [backTag]
  have D : (tok d C x (j+1)).tag=3 := by rw [R.packet]; simp
  have W := (reverse_joined d C x N mask j I T D).1
  rw [tok_wire,W,R.packet]
  exact indexed_D_roundtrip (params d s) op Range _ q R.bound

private theorem D_hold (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (q : Option IndexedData) (R : DState d C op x k q) (e : Fin n)
    (M : ¬∃ j,k=j+1 ∧ e=out C j) (NC : NoConsume d C x e) :
    tok d C (rawNext s x e) k=tok d C x k := by
  by_cases E : e=out C k
  · subst e
    exact D_outgoing_hold d C op Range hh G F N x X k q R
  · by_cases H : rightNeighbor e=out C k
    · cases k with
      | zero =>
        have A := incoming_zero C e H
        have T : (tok d C x 0).tag=3 := by rw [R.packet]; simp
        exact (NC.elim (fun B=>B A) (fun B=>B T)).elim
      | succ j =>
        exact (M ⟨j,rfl,incoming_succ C e j H⟩).elim
    · exact spectator_token d C hh G F N x X k R.shape.2.1 e E H

theorem F_step (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (q : Option IndexedData)
    (R : FState d C op x k q) (e : Fin n) :
    let y := rawNext s x e
    FState d C op y k q ∨
      (e=out C k ∧ FState d C op y (k+1) (stepPayload d C op x k q)) ∨
      (e=out C k ∧ k+1=C.L ∧ DState d C op y k (stepPayload d C op x k q)) := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  let y := rawNext s x e
  have I := R.shape.2.1
  have HT : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
    rw [R.shape.2.2 0 C.positive]
    by_cases Z : k=0
    · subst k; exact .inr rfl
    · exact .inl (by simp [frontTag,show 0<k by omega])
  have PC := (wait_pc d C op Range x e N (CF.mask x X) R.pc (fun _=>HT)).trans R.pc
  have S := ReportOwnerForwardControl.all_mark d C hh G F N x X k R.shape e
  have B := indexed_next_good (params d s) op Range (h (out C k))
    (bytesL d x (out C k)) (C.route.port k) q R.bound
  by_cases E : e=out C k
  · subst e
    by_cases J : k+1<C.L
    · have A := raw_hop d C op Range x N (CF.mask x X) k q J R
      rcases S with H|⟨_,H|⟨K,H⟩⟩
      · have T := H.2.2 (k+1) J
        rw [A] at T
        simp [indexedF_tag,frontTag,show ¬k+1<k by omega] at T
      · exact .inr (.inl ⟨rfl,⟨H,PC,B,A⟩⟩)
      · omega
    · have J0 : k+1=C.L := by omega
      have A := raw_turn d C op Range x N (CF.mask x X) k q J0 R
      rcases S with H|⟨_,H|⟨K,H⟩⟩
      · have T := H.2.2 k I
        rw [A] at T
        simp [frontTag] at T
      · have Z := H.2.1
        omega
      · exact .inr (.inr ⟨rfl,J0,⟨H,PC,B,A⟩⟩)
  · rcases S with H|⟨U,_⟩
    · exact .inl ⟨H,PC,R.bound,(F_hold d C op Range hh G F N x X k q R e E).trans R.packet⟩
    · exact (E U).elim

theorem D_step (d : Sheet) (C : Chart h) (op : Nat) (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (q : Option IndexedData)
    (R : DState d C op x k q) (digit : 0<(params d s).digits)
    (e : Fin n) (NC : NoConsume d C x e) :
    let y := rawNext s x e
    DState d C op y k q ∨ ∃ j,k=j+1 ∧ e=out C j ∧ DState d C op y j q := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  have rootD (Z : k=0) : (tok d C x 0).tag=3 := by
    rw [←Z,R.packet]
    simp
  have HT (E : e=door C) : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
    have K : k≠0 := fun Z=>NC.elim (fun L=>L E) (fun L=>L (rootD Z))
    rw [R.shape.2.2 0 C.positive]
    exact .inl (by simp [backTag,show 0<k by omega])
  have PC := (wait_pc d C op Range x e N (CF.mask x X) R.pc HT).trans R.pc
  have S := ReportOwnerReverseControl.all_mark d C hh G F N x X k R.shape digit e
  by_cases M : ∃ j,k=j+1 ∧ e=out C j
  · obtain ⟨j,J,E⟩ := M
    subst k e
    have A := raw_reverse_hop d C op Range x N (CF.mask x X) j q R
    rcases S with H|⟨l,L,_,H⟩|⟨Z,_,_⟩
    · have T := H.2.2 j (by have := R.shape.2.1; omega)
      rw [A] at T
      simp [backTag] at T
    · have L0 : l=j := by omega
      subst l
      exact .inr ⟨j,rfl,rfl,⟨H,PC,R.bound,A⟩⟩
    · omega
  · rcases S with H|⟨j,J,E,_⟩|⟨Z,E,_⟩
    · exact .inl ⟨H,PC,R.bound,(D_hold d C op Range hh G F N x X k q R e M NC).trans R.packet⟩
    · exact (M ⟨j,J,E⟩).elim
    · exact (NC.elim (fun B=>B E) (fun B=>B (rootD Z))).elim

/-- The historical trace stores the complete accumulator at each
    old departure. All constructors are tied to the original tape;
    in particular the turn and the return are not separately chosen. -/
inductive Cursor where
  | forward (k : Nat) (q : Option IndexedData)
  | backward (k : Nat) (q : Option IndexedData)

def At (d : Sheet) (C : Chart h) (op : Nat) (x : Raw s n) : Cursor→Prop
  | .forward k q => FState d C op x k q
  | .backward k q => DState d C op x k q

inductive Walk (d : Sheet) (C : Chart h) (op : Nat) (x0 : Raw s n)
    (q0 : Option IndexedData) : List (Fin n)→Cursor→Prop
  | seed (A : FState d C op x0 0 q0) : Walk d C op x0 q0 [] (.forward 0 q0)
  | fhold {w k q} (e : Fin n) :
      Walk d C op x0 q0 w (.forward k q) →
      FState d C op (rawRun x0 (w++[e])) k q →
      Walk d C op x0 q0 (w++[e]) (.forward k q)
  | hop {w k q} :
      Walk d C op x0 q0 w (.forward k q) →
      FState d C op (rawRun x0 w) k q →
      FState d C op (rawRun x0 (w++[out C k])) (k+1)
        (stepPayload d C op (rawRun x0 w) k q) →
      Walk d C op x0 q0 (w++[out C k])
        (.forward (k+1) (stepPayload d C op (rawRun x0 w) k q))
  | turn {w k q} :
      Walk d C op x0 q0 w (.forward k q) →
      FState d C op (rawRun x0 w) k q → k+1=C.L →
      DState d C op (rawRun x0 (w++[out C k])) k
        (stepPayload d C op (rawRun x0 w) k q) →
      Walk d C op x0 q0 (w++[out C k])
        (.backward k (stepPayload d C op (rawRun x0 w) k q))
  | dhold {w k q} (e : Fin n) :
      Walk d C op x0 q0 w (.backward k q) →
      DState d C op (rawRun x0 (w++[e])) k q →
      Walk d C op x0 q0 (w++[e]) (.backward k q)
  | back {w j q} :
      Walk d C op x0 q0 w (.backward (j+1) q) →
      DState d C op (rawRun x0 (w++[out C j])) j q →
      Walk d C op x0 q0 (w++[out C j]) (.backward j q)

theorem walk_at (d : Sheet) (C : Chart h) (op : Nat)
    (x0 : Raw s n) (q0 : Option IndexedData) (w : List (Fin n)) (c : Cursor)
    (W : Walk d C op x0 q0 w c) : At d C op (rawRun x0 w) c := by
  cases W with
  | seed A => exact A
  | fhold _ _ A => exact A
  | hop _ _ A => exact A
  | turn _ _ _ A => exact A
  | dhold _ _ A => exact A
  | back _ A => exact A

/-- All-mark propagation of full packet ancestry. -/
theorem walk_run (d : Sheet) (C : Chart h) (op : Nat)
    (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (q0 : Option IndexedData)
    (A : FState d C op x0 0 q0) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w) :
    Cached d hh Q (rawRun x0 w) ∧ ∃ c,Walk d C op x0 q0 w c := by
  induction T with
  | nil => exact ⟨X,.forward 0 q0,.seed A⟩
  | @snoc w e T IHNC IH =>
    obtain ⟨Y,c,W⟩ := IH
    have Y' : Cached d hh Q (rawRun x0 (w++[e])) := by
      rw [ShortOwnerEpochJS.raw_snoc]
      exact (cached_fibre d N hh Q F).closed _ e Y
    refine ⟨Y',?_⟩
    have H := walk_at d C op x0 q0 w c W
    cases c with
    | forward k q =>
      rcases F_step d C op Range hh G F N (rawRun x0 w) Y k q H e with S|⟨E,S⟩|⟨E,K,S⟩
      · exact ⟨_,.fhold e W (by rw [ShortOwnerEpochJS.raw_snoc]; exact S)⟩
      · subst e
        exact ⟨_,.hop W H (by rw [ShortOwnerEpochJS.raw_snoc]; exact S)⟩
      · subst e
        exact ⟨_,.turn W H K (by rw [ShortOwnerEpochJS.raw_snoc]; exact S)⟩
    | backward k q =>
      rcases D_step d C op Range hh G F N (rawRun x0 w) Y k q H digit e IHNC with S|⟨j,K,E,S⟩
      · exact ⟨_,.dhold e W (by rw [ShortOwnerEpochJS.raw_snoc]; exact S)⟩
      · subst k e
        exact ⟨_,.back W (by rw [ShortOwnerEpochJS.raw_snoc]; exact S)⟩

theorem walk_successful_root (d : Sheet) (C : Chart h) (op : Nat)
    (Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (q0 : Option IndexedData)
    (A : FState d C op x0 0 q0) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (Tag : (tok d C (rawRun x0 w) 0).tag=3)
    (Live : (tok d C (rawRun x0 w) 0).fault=false) :
    ∃ q : IndexedData,
      Walk d C op x0 q0 w (.backward 0 (some q)) ∧
      DState d C op (rawRun x0 w) 0 (some q) := by
  obtain ⟨_,c,W⟩ := walk_run d C op Range hh G F N x0 X q0 A digit w T
  have B := walk_at d C op x0 q0 w c W
  cases c with
  | forward k q =>
    have R : FState d C op (rawRun x0 w) k q := B
    rw [R.shape.2.2 0 C.positive] at Tag
    unfold frontTag at Tag
    split at Tag <;> try contradiction
    split at Tag <;> contradiction
  | backward k q =>
    have R : DState d C op (rawRun x0 w) k q := B
    have K : k=0 := by
      by_cases E : k=0
      · exact E
      · rw [R.shape.2.2 0 C.positive] at Tag
        simp [backTag,show 0<k by omega] at Tag
    subst k
    cases q with
    | none =>
      rw [R.packet] at Live
      contradiction
    | some a => exact ⟨a,W,R⟩

/-- The exact source door launched packet is given in the
    IssuedSegment. LegalIssue plus the actual root F is sufficient
    to seed the physical flight; no payload inference from a PC. -/
theorem launch_from_token (d : Sheet) (C : Chart h) (op : Nat)
    (_Range : IndexedOp (params d s) op) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (PC : readPC d C x=(1,op)) (q : IndexedData)
    (B : q.OK (params d s) op)
    (A : tok d C (rawNext s x (door C)) 0=indexedF (params d s) op (some q)) :
    FState d C op (rawNext s x (door C)) 0 (some q) := by
  rcases ReportOwnerIssueControl.door_step d C hh G F N x X I with R|⟨R,J⟩
  · have T := R.2.2 0 C.positive
    rw [A] at T
    simp at T
  · have Old : (readPC d C x).2=op := congrArg Prod.snd PC
    exact ⟨R,Prod.ext R.1.1 (J.trans Old),B,A⟩

end L4.ReportOwnerIndexedFlight
