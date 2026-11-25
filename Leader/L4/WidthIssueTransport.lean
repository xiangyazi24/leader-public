import Leader.L4.WidthJoinedProjection

namespace L4.WidthIssueTransport
open AllSizeProtocol WidthByteRows WidthOwnerController WidthChecksum PhysicalCustody
set_option maxHeartbeats 1000000

def issueToken (op arg : Nat) : Token :=
  {tag:=2,op:=op,arg:=if op==3 then arg else if op==4 then 1 else 0}

private theorem arg_lt {c : Nat} (v : BitVec (W c)) : argument (c:=c) v<4 :=
  ((suffixField c 12 2 (by decide)).read v).isLt

private theorem decode_issue_fin (op : Fin 6) (arg : Fin 4) :
    decode (encode (issueToken op.val arg.val))=issueToken op.val arg.val := by
  revert op arg
  decide

theorem decode_issue (op arg : Nat) (O : op≤5) (A : arg<4) :
    decode (encode (issueToken op arg))=issueToken op arg :=
  decode_issue_fin ⟨op,by omega⟩ ⟨arg,A⟩

/-- Legitimate source ISSUE for every operation in the emitted width
table. K is overwritten no matter what was previously decoded. -/
theorem issue_door {c : Nat} (x : BitVec (W c)) (t : Token)
    (P : phase (c:=c) x=1) (O : opcode (c:=c) x≤5) :
    doorPatch (c:=c) x t =
      (put c 7 2 (by decide) 2).compose
        (tokenPatch c (issueToken (opcode (c:=c) x) (argument (c:=c) x))) := by
  have N : ¬5<opcode (c:=c) x := by omega
  unfold phase at P
  unfold opcode at N
  simp [doorPatch,P,N,issueToken,opcode,argument]

theorem incoming_issue_wire {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=1) (O : opcode (c:=c) v≤5) :
    ((suffixField c 14 16 (by decide)).read
      ((row (c:=c) r (hu,true) (u,v)).2.apply v))=
        encode (issueToken (opcode (c:=c) v) (argument (c:=c) v)) := by
  unfold row
  simp only [issue_door v _ P O,if_true,Patch.compose_apply]
  exact Field.read_assign _ _ _

theorem incoming_issue_packet {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=1) (O : opcode (c:=c) v≤5) :
    packet (c:=c) ((row (c:=c) r (hu,true) (u,v)).2.apply v)=
      issueToken (opcode (c:=c) v) (argument (c:=c) v) := by
  unfold packet
  rw [incoming_issue_wire r hu u v P O,decode_issue _ _ O (arg_lt v)]

theorem incoming_issue_phase {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=1) (O : opcode (c:=c) v≤5) :
    phase (c:=c) ((row (c:=c) r (hu,true) (u,v)).2.apply v)=2 := by
  unfold row
  simp only [issue_door v _ P O,if_true,Patch.compose_apply]
  unfold phase WidthByteRows.get put tokenPatch
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField])),Field.read_assign]
  rfl

theorem incoming_issue_opcode {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=1) (O : opcode (c:=c) v≤5) :
    opcode (c:=c) ((row (c:=c) r (hu,true) (u,v)).2.apply v)=opcode (c:=c) v := by
  have norm (t : Token) (x : BitVec (W c)) :
      opcode (c:=c) ((tokenPatch c t).apply x)=opcode (c:=c) x := by
    unfold opcode WidthByteRows.get tokenPatch
    rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField]))]
  have ph (x : BitVec (W c)) :
      opcode (c:=c) ((put c 7 2 (by decide) 2).apply x)=opcode (c:=c) x := by
    unfold opcode WidthByteRows.get put
    rw [Field.read_other_assign _ _ _ _ (.inl (by simp [suffixField]))]
  have emp (x : BitVec (W c)) : (Patch.empty (W c)).apply x=x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    exact Patch.hold _ _ _ (by simp [Patch.empty])
  let d := decode ((suffixField c 14 16 (by decide)).read v)
  let t := issueToken (opcode (c:=c) v) (argument (c:=c) v)
  have X : ((row (c:=c) r (hu,true) (u,v)).2).apply v =
      (tokenPatch c t).apply ((put c 7 2 (by decide) 2).apply
        ((if d.fault then tokenPatch c d else Patch.empty _).apply v)) := by
    have I := issue_door v d P O
    unfold d t at *
    by_cases F : (decode ((suffixField c 14 16 (by decide)).read u)).tag=2
    · simp [row,F,I,Patch.compose_apply,emp]
    · by_cases G : (decode ((suffixField c 14 16 (by decide)).read u)).tag=1 <;>
        simp [row,F,G,I,Patch.compose_apply,emp]
  rw [X,norm,ph]
  by_cases E : d.fault=true
  · rw [if_pos E,norm]
  · rw [if_neg E,emp]

private theorem join_opcode (s : Nat) (u v : LargeSite (WidthJoinedProjection.P s)) :
    let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
    opcode (c:=s+11) (largePair (rows s) (u,v)).2.widthClient =
      opcode (c:=s+11) ((row (c:=s+11) (radWidth s) h (u.widthClient,v.widthClient)).2.apply
        v.widthClient) := by
  dsimp only
  unfold opcode WidthByteRows.get
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
  let L : BitVec (W (s+11)) := (largePair (rows s) (u,v)).2.widthClient
  let R : BitVec (W (s+11)) :=
    ((row (c:=s+11) (radWidth s) h (u.widthClient,v.widthClient)).2.apply v.widthClient)
  change (L.extractLsb' 18 3).getLsbD i=(R.extractLsb' 18 3).getLsbD i
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  exact (WidthJoinedProjection.pair_bit s u v (18+i) (by omega) (.inr (by omega))).2

theorem raw_incoming_issue {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (H : (oldHeaders (rows s) (x (rightNeighbor e))).h6=true)
    (P : phase (c:=s+11) (x (rightNeighbor e)).widthClient=1)
    (O : opcode (c:=s+11) (x (rightNeighbor e)).widthClient≤5) :
    let v := (x (rightNeighbor e)).widthClient
    let y := (rawNext s x e (rightNeighbor e)).widthClient
    phase (c:=s+11) y=2 ∧ opcode (c:=s+11) y=opcode (c:=s+11) v ∧
      packet (c:=s+11) y=issueToken (opcode (c:=s+11) v) (argument (c:=s+11) v) := by
  let u := x e
  let v := x (rightNeighbor e)
  let hu := (oldHeaders (rows s) u).h6
  have E := (WidthJoinedProjection.pair_phase s u v).2
  have F := (WidthJoinedProjection.pair_packet s u v).2
  have G := join_opcode s u v
  change (oldHeaders (rows s) v).h6=true at H
  simp only [H] at E F G
  have stepEq : AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)=
      (largePair (rows s) (u,v)).2 := by simp [AllSizeS1Geometry.step,Ne.symm sep,u,v]
  change phase (c:=s+11) (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient=2 ∧
    opcode (c:=s+11) (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient=
      opcode (c:=s+11) v.widthClient ∧
    packet (c:=s+11) (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient=
      issueToken (opcode (c:=s+11) v.widthClient) (argument (c:=s+11) v.widthClient)
  rw [stepEq,E,G,F]
  exact ⟨incoming_issue_phase _ hu _ _ P O,incoming_issue_opcode _ hu _ _ P O,
    incoming_issue_packet _ hu _ _ P O⟩

/-- The narrowing wrapper never suppresses COMPARE's two saved flags,
including when the incoming matching D2 happens to leave the bits
numerically unchanged. -/
theorem compare_not_narrowed {c : Nat} (hv : Bool) (v : BitVec (W c))
    (O : opcode (c:=c) v=2) : BStarShort.widthHoldFlags (c:=c) hv v=false := by
  unfold opcode at O
  simp [BStarShort.widthHoldFlags,O]

private theorem right_geo_bit {c : Nat} (h : Pair Bool) (x : Pair (BitVec (W c)))
    (q : Pair (Patch (W c))) (i : Nat) (I : i<29) :
    (patchPair ((ShortGeo.width c).patches c h x q) x).2.getLsbD i=(q.2.apply x.2).getLsbD i := by
  let G := ShortGeo.width c
  have U : ¬G.owned i := by
    intro H
    have L := H.1
    change 29≤i at L
    omega
  have D := G.work_other_mask q.2 i U
  have off (v : BitVec (W c)) :
      ((G.off.assign (G.nextOff c h x)).apply v).getLsbD i=v.getLsbD i :=
    G.off.hold_outside _ v i (.inl (show i<30 by omega))
  change (((G.work q.2).compose (G.off.assign (G.nextOff c h x))).apply
      x.2).getLsbD i=(q.2.apply x.2).getLsbD i
  rw [Patch.compose_apply,off]
  cases E : q.2.mask.getLsbD i
  · rw [Patch.hold _ _ _ (D.trans E),Patch.hold _ _ _ E]
  · rw [Patch.write _ _ _ (D.trans E),Patch.write _ _ _ E]
    rfl

/-- Production geometry writes do not touch the two source argument
bits, and the width wrapper is disabled by old opcode COMPARE2. -/
theorem joined_compare_argument (s : Nat) (u v : LargeSite (WidthJoinedProjection.P s))
    (O : opcode (c:=s+11) v.widthClient=2) :
    let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
    argument (c:=s+11) (largePair (rows s) (u,v)).2.widthClient=
      argument (c:=s+11) ((row (c:=s+11) (radWidth s) h
        (u.widthClient,v.widthClient)).2.apply v.widthClient) := by
  let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
  let x : Pair (BitVec (W (s+11))) := (u.widthClient,v.widthClient)
  let p := row (c:=s+11) (radWidth s) h x
  let q := BStarShort.widthWork (c:=s+11) (radWidth s) h x
  have H : q.2=p.2 := by
    have V : BStarShort.widthHoldFlags (c:=s+11) h.2 x.2=false :=
      compare_not_narrowed (c:=s+11) h.2 x.2 O
    change (if BStarShort.widthHoldFlags (c:=s+11) h.2 x.2 then _ else p.2)=p.2
    simp [V]
  let L : BitVec (W (s+11)) := (largePair (rows s) (u,v)).2.widthClient
  let R : BitVec (W (s+11)) := p.2.apply v.widthClient
  change argument (c:=s+11) L=argument (c:=s+11) R
  unfold argument WidthByteRows.get
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  change (L.extractLsb' 16 2).getLsbD i=(R.extractLsb' 16 2).getLsbD i
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  have U := right_geo_bit h x q (16+i) (by omega)
  change L.getLsbD (16+i)=(q.2.apply v.widthClient).getLsbD (16+i) at U
  rwa [H] at U

theorem incoming_compare_argument {c : Nat} (r : Nat) (hu : Bool)
    (u v : BitVec (W c)) (P : phase (c:=c) v=2) (O : opcode (c:=c) v=2)
    (T : (packet (c:=c) v).tag=3) (M : (packet (c:=c) v).op=2)
    (F : (packet (c:=c) v).fault=false) (A : (packet (c:=c) v).arg<4) :
    argument (c:=c) ((row (c:=c) r (hu,true) (u,v)).2.apply v)=(packet (c:=c) v).arg := by
  let t := packet (c:=c) v
  have X := wait_good_reply v t P (by omega) T (M.trans O.symm) F
  rw [show t.op=2 from M] at X
  change doorPatch (c:=c) v (decode ((suffixField c 14 16 (by decide)).read v)) =
    clearDoor c 3 t.arg at X
  unfold row
  simp only [X,if_true,Patch.compose_apply,clearDoor]
  unfold argument WidthByteRows.get tokenPatch
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField]))]
  have argWrite (prev : BitVec (W c)) :
      ((suffixField c 12 2 (by decide)).read ((control c 1 3 t.arg).apply prev)).toNat=t.arg := by
    let y := (control c 1 3 t.arg).apply prev
    have E : ((suffixField c 7 7 (by decide)).read y).extractLsb' 0 2 =
        (suffixField c 12 2 (by decide)).read y := by
      apply BitVec.eq_of_getLsbD_eq
      intro i I
      change ((y.extractLsb' 16 7).extractLsb' 0 2).getLsbD i=
        (y.extractLsb' 16 2).getLsbD i
      simp [I,show i<7 by omega]
    change ((suffixField c 12 2 (by decide)).read y).toNat=t.arg
    rw [←E]
    have J : (suffixField c 7 7 (by decide)).read y=BitVec.ofNat 7 (44+t.arg) :=
      Field.read_assign _ _ _
    have AL : t.arg<4 := A
    have L : (44+t.arg)%2^7=44+t.arg := Nat.mod_eq_of_lt (by omega)
    rw [J,BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,L]
    simp only [Nat.shiftRight_zero]
    omega
  exact argWrite _

theorem raw_incoming_compare_argument {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (H : (oldHeaders (rows s) (x (rightNeighbor e))).h6=true)
    (P : phase (c:=s+11) (x (rightNeighbor e)).widthClient=2)
    (O : opcode (c:=s+11) (x (rightNeighbor e)).widthClient=2)
    (T : (packet (c:=s+11) (x (rightNeighbor e)).widthClient).tag=3)
    (M : (packet (c:=s+11) (x (rightNeighbor e)).widthClient).op=2)
    (F : (packet (c:=s+11) (x (rightNeighbor e)).widthClient).fault=false)
    (A : (packet (c:=s+11) (x (rightNeighbor e)).widthClient).arg<4) :
    argument (c:=s+11) (rawNext s x e (rightNeighbor e)).widthClient=
      (packet (c:=s+11) (x (rightNeighbor e)).widthClient).arg := by
  let u := x e
  let v := x (rightNeighbor e)
  let hu := (oldHeaders (rows s) u).h6
  have E := joined_compare_argument s u v O
  change (oldHeaders (rows s) v).h6=true at H
  simp only [H] at E
  have stepEq : AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)=
      (largePair (rows s) (u,v)).2 := by simp [AllSizeS1Geometry.step,Ne.symm sep,u,v]
  change argument (c:=s+11) (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient=
    (packet (c:=s+11) v.widthClient).arg
  rw [stepEq,E]
  exact incoming_compare_argument _ hu _ _ P O T M F A

end L4.WidthIssueTransport
