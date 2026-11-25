import Leader.L4.ReportSealCommitOrigin
import Leader.L4.ReportWriteSplit
import Leader.L4.ReportOwnerAcquireProvenance
namespace L4.ReportSealReverse
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerForwardControl ReportOwnerIssueControl ReportOwnerReverseControl
open ReportByteRows ReportRawProjection ReportWriteSplit ReportSealCommitOrigin
open ReportOwnerDoorProjection ReportPrelaunchDoorLift ReportOwnerReverseShape
open ReportOwnerAcquireProvenance (BeforeConsume NoConsume)
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

private def get {w : Nat} (x : BitVec w) (k b : Nat) : Nat := (x.extractLsb' k b).toNat
private def encode (p : Params) (t : Tok) : Nat :=
  let b := payW p
  t.tag*2^(7+o p+b)+t.fault.toNat*2^(6+o p+b)+
    t.opcode*2^(b+6)+t.race*2^(b+3)+t.outcome*2^(b+1)+t.applied.toNat*2^b+t.payload

private def rPack (w l u : Nat) : Nat := l+2^w*u

private theorem rPack_lt {w v l u : Nat}
    (L : l<2^w) (U : u<2^v) : rPack w l u<2^(w+v) := by
  unfold rPack
  rw [Nat.pow_add]
  have B := Nat.mul_le_mul_left (2^w) (show u+1≤2^v by omega)
  rw [Nat.mul_succ] at B
  omega

private theorem rPack_div {w l u : Nat} (L : l<2^w) :
    rPack w l u / 2^w=u := by
  unfold rPack
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt L,Nat.zero_add]

private theorem rPack_mod {w l u : Nat} (L : l<2^w) :
    rPack w l u % 2^w=l := by
  unfold rPack
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt L]

private theorem rPack_extract {w k b l u : Nat} (L : l<2^w) :
    (rPack w l u / 2^(w+k))%2^b=(u/2^k)%2^b := by
  rw [Nat.pow_add,←Nat.div_div_eq_div_mul,rPack_div L]

private def rCode (p : Params) (t : Tok) : Nat :=
  rPack (payW p) t.payload
    (rPack 1 t.applied.toNat
      (rPack 2 t.outcome
        (rPack 3 t.race
          (rPack (o p) t.opcode (rPack 1 t.fault.toNat t.tag)))))

private theorem rCode_eq (p : Params) (t : Tok) : encode p t=rCode p t := by
  unfold encode rCode rPack
  dsimp only
  rw [show 7+o p+payW p=payW p+1+2+3+o p+1 by omega,
    show 6+o p+payW p=payW p+1+2+3+o p by omega,
    show payW p+6=payW p+1+2+3 by omega,
    show payW p+3=payW p+1+2 by omega]
  simp only [Nat.pow_add,Nat.mul_add]
  ac_rfl

private theorem rCode_lt (p : Params) (t : Tok) (H : RankFits p t) :
    rCode p t<2^tokenW p := by
  have f : t.fault.toNat<2^1 := by cases t.fault <;> decide
  have a : t.applied.toNat<2^1 := by cases t.applied <;> decide
  have A := rPack_lt (v:=2) f H.tag
  have B := rPack_lt H.op A
  have C := rPack_lt (show t.race<2^3 from H.race) B
  have D := rPack_lt (show t.outcome<2^2 from H.outcome) C
  have E := rPack_lt a D
  have G := rPack_lt H.payload E
  unfold rCode tokenW
  simpa only [show payW p+(1+(2+(3+(o p+(1+2)))))=9+o p+payW p by omega] using G

private theorem rWire_nat (p : Params) (t : Tok) (H : RankFits p t) :
    (resetTokenWire p t).toNat=rCode p t := by
  change (BitVec.ofNat (tokenW p) (encode p t)).toNat=rCode p t
  rw [BitVec.toNat_ofNat,rCode_eq,Nat.mod_eq_of_lt (rCode_lt p t H)]

private theorem rGet_nat {w : Nat} (x : BitVec w) (k b : Nat) :
    get x k b=x.toNat/2^k%2^b := by
  -- CHECK: same extraction identity as dr_field_sub.
  rw [get,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

/-- The seven exact non-overlapping wire fields. This avoids any
    claim that malformed padding roundtrips to the original raw word. -/
private theorem rReadFields (p : Params) (t : Tok) (H : RankFits p t) :
    get (resetTokenWire p t) (7+o p+payW p) 2=t.tag ∧
    get (resetTokenWire p t) (6+o p+payW p) 1=t.fault.toNat ∧
    get (resetTokenWire p t) (payW p+6) (o p)=t.opcode ∧
    get (resetTokenWire p t) (payW p+3) 3=t.race ∧
    get (resetTokenWire p t) (payW p+1) 2=t.outcome ∧
    get (resetTokenWire p t) (payW p) 1=t.applied.toNat ∧
    get (resetTokenWire p t) 0 (payW p)=t.payload := by
  have f : t.fault.toNat<2^1 := by cases t.fault <;> decide
  have a : t.applied.toNat<2^1 := by cases t.applied <;> decide
  have r : t.race<2^3 := H.race
  have z : t.outcome<2^2 := H.outcome
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show 7+o p+payW p=payW p+(1+(2+(3+(o p+(1+(0)))))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    rw [rPack_extract r]
    rw [rPack_extract H.op]
    rw [rPack_extract f]
    simp only [Nat.pow_zero,Nat.div_one]
    exact Nat.mod_eq_of_lt H.tag
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show 6+o p+payW p=payW p+(1+(2+(3+(o p+(0))))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    rw [rPack_extract r]
    rw [rPack_extract H.op]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod f
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show payW p+6=payW p+(1+(2+(3+(0)))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    rw [rPack_extract r]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod H.op
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show payW p+3=payW p+(1+(2+(0))) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    rw [rPack_extract z]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod r
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [show payW p+1=payW p+(1+(0)) by omega]
    rw [rPack_extract H.payload]
    rw [rPack_extract a]
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod z
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    rw [rPack_div H.payload]
    exact rPack_mod a
  · rw [rGet_nat,rWire_nat p t H]
    unfold rCode
    simp only [Nat.pow_zero,Nat.div_one]
    exact rPack_mod H.payload

private theorem rGet_bit {w : Nat} (x : BitVec w) (k : Nat) :
    x.getLsbD k=decide (get x k 1=1) := by
  -- CHECK: BitVec.getLsbD and Nat.testBit_eq_decide_div_mod_eq;
  -- same identity as selector_toNat.
  rw [rGet_nat,BitVec.getLsbD,Nat.testBit_eq_decide_div_mod_eq]

private def bit (x k : Nat) : Bool := (x >>> k)%2==1
private def legalDesc (x : Nat) : Bool := bit x 3 != bit x 2
private def digitPair (p : Params) (z : Nat) : Bool :=
  z%2^d p<p.beta && (z/2^d p)%2^d p<p.beta
private abbrev F := MISByteCodec.faultToken
private abbrev E := MISByteCodec.E
private abbrev T := MISByteCodec.T

private def decodeFields (p : Params) (gate : Bool) (raw : BitVec (tokenW p)) : Tok :=
  let b := payW p
  let tag := get raw (7+o p+b) 2
  let ft := raw.getLsbD (6+o p+b)
  let op := get raw (b+6) (o p)
  let race := get raw (b+3) 3
  let outcome := get raw (b+1) 2
  let q := get raw 0 b
  let atGate := gate && op==admitOp p
  if tag==0 then E else if tag==1 then T
  else if ft || commitOp p<op then F tag
  else if tag==2 then
    if outcome != 0 || (if atGate then race<1 || 5<race else race != 0) then F tag
    else
      let k := if op==acqOp p then 7 else if op==admitOp p then 1 else
        if cmpOp p≤op && op<sealOp p then 2+2*d p else if sealOp p≤op then 4 else 0
      let q := q%2^k
      if (cmpOp p≤op && op<sealOp p && !digitPair p q) ||
         (writeOp p≤op && op<sealOp p && bit q (2*d p)==bit q (2*d p+1)) ||
         (sealOp p≤op && !legalDesc q) then F tag
      else ⟨tag,op,q,race,0,false,op==commitOp p && raw.getLsbD b⟩
  else if race != 0 || (outcome != 0 && !(op==acqOp p && outcome==1)) then F tag
  else
    let k := if op==acqOp p then 6 else if op==admitOp p then 1 else
      if cmpOp p≤op && op<writeOp p then 2*d p else 0
    let q := if outcome==1 then 0 else q%2^k
    if cmpOp p≤op && op<writeOp p && !digitPair p q then F tag
    else ⟨tag,op,q,0,outcome,false,false⟩

theorem seal_ack_decode (p : Params) (g : Bool) (fit : sealOp p<2^o p) :
    decode p g (resetTokenWire p ({tag:=3,opcode:=sealOp p}:Tok))=
      ({tag:=3,opcode:=sealOp p}:Tok) := by
  let t : Tok := {tag:=3,opcode:=sealOp p}
  have Fit : RankFits p t := ⟨(by decide : 3<4),fit,Nat.two_pow_pos _,(by decide : 0<8),(by decide : 0<4)⟩
  have F := rReadFields p t Fit
  have B : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,F.2.1]
    rfl
  have A : sealOp p≠acqOp p := by unfold sealOp acqOp; omega
  have D : sealOp p≠admitOp p := by unfold sealOp admitOp; omega
  have L : ¬sealOp p<writeOp p := by unfold sealOp writeOp; omega
  change decode p g (resetTokenWire p t)=t
  change decodeFields p g (resetTokenWire p t)=t
  simp only [decodeFields,F.1,F.2.2.1,F.2.2.2.1,F.2.2.2.2.1,F.2.2.2.2.2.2,B]
  have M : ¬commitOp p<sealOp p := by unfold commitOp sealOp; omega
  simp [t,A,D,L,M]

def Reply (p : Params) : Tok := {tag:=3,opcode:=sealOp p}

private theorem seal_op_fit (p : Params) : sealOp p<2^o p := by
  have H := power_of_ell (5+4*p.digits)
  unfold o sealOp
  omega

structure SealD (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop where
  shape : ReverseWait d C x k
  pc : readPC d C x=(2,sealOp (params d s))
  packet : tok d C x k=Reply (params d s)

theorem healthy_seal_terminal (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1=C.L)
    (R : ForwardWait d C x k) (Src : readPC d C x=(2,sealOp (params d s)))
    (H : SealCommitForward (params d s) (tok d C x k))
    (O : (tok d C x k).opcode=sealOp (params d s)) :
    let y := rawNext s x (out C k)
    Cached d hh Q y ∧ SealD d C y k := by
  dsimp only
  let p := params d s
  let e := out C k
  let y := rawNext s x e
  let CF := cached_fibre d N hh Q F
  have M := CF.mask x X
  rw [predecessor_projection] at H O
  have W := raw_pair_wire d C x N M k
  have Rw := seal_terminal_pair p (h e) (h (rightNeighbor e)) (bytesL d x e) (bytesR d x e)
    _ (end_dest C k J) H O
  have P : tok d C y k=Reply p := by
    change tok d C (rawNext s x (out C k)) k=_
    rw [tok_wire,W.1,workL,Rw]
    exact seal_ack_decode p _ (seal_op_fit p)
  have A : ReverseWait d C y k := by
    rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R e with A|⟨_,A|⟨_,A⟩⟩
    · have K := A.2.2 k R.2.1
      change (tok d C y k).tag=frontTag k k at K
      rw [P] at K
      simp [Reply,frontTag] at K
    · have I := A.2.1
      omega
    · exact A
  exact ⟨CF.closed x e X,⟨A,(forward_step_control d C N hh F x X k R e).trans Src,P⟩⟩

theorem raw_seal_reverse_hop (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (R : SealD d C x (j+1)) :
    tok d C (rawNext s x (out C j)) j=Reply (params d s) := by
  have I := R.shape.2.1
  have T : (tok d C x j).tag≠2 := by
    rw [R.shape.2.2 j (by omega)]
    simp [backTag]
  have D : (tok d C x (j+1)).tag=3 := by rw [R.packet]; rfl
  have W := (reverse_joined d C x N mask j I T D).1
  rw [tok_wire,W,R.packet]
  exact seal_ack_decode (params d s) _ (seal_op_fit _)
private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok]; rfl

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
    (P : readPC d C x=(2,sealOp (params d s)))
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
      have O0 : sourceOpcode p v=sealOp p := congrArg Prod.snd P
      rw [O0]
      unfold sealOp commitOp
      omega
    exact (raw_door_final d C x N mask).1.trans
      (prelaunch_hold_controls p v t V O A)
  · exact raw_nondoor_control d C x e N mask E

private theorem D_outgoing_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (R : SealD d C x k) :
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
  have T : (publicationToken p (h e) u a).tag≠2 := by rw [A]; simp [Reply]
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
      exact ⟨by rw [S]; decide,by rw [A]; simp [Reply]⟩
    · rw [end_dest C k (by omega),A]
      simp [Reply]
  have E := rank_idle_left p (h e) (h (rightNeighbor e)) u v a NR (.inr ⟨T,H⟩)
  have Gate : chartGate d C x k=rankGate p (h e) u a := rfl
  rw [tok_wire d C (rawNext s x e),gate_frame d C hh G x _ X Y k I,Gate,
    (raw_pair_wire d C x N (CF.mask x X) k).1,workL,E,tok_wire,Gate]
  apply rank_nondadmit_norm_token p 3 _ _ (.inr rfl)
  left
  have A' := A
  rw [rankToken_wire] at A'
  rw [A']
  change sealOp p≠admitOp p
  unfold sealOp admitOp
  omega

private theorem D_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (R : SealD d C x k) (e : Fin n)
    (M : ¬∃ j,k=j+1 ∧ e=out C j) (NC : NoConsume d C x e) :
    tok d C (rawNext s x e) k=tok d C x k := by
  by_cases E : e=out C k
  · subst e
    exact D_outgoing_hold d C hh G F N x X k R
  · by_cases H : rightNeighbor e=out C k
    · cases k with
      | zero =>
        have A := incoming_zero C e H
        have T : (tok d C x 0).tag=3 := by rw [R.packet]; simp [Reply]
        exact (NC.elim (fun B=>B A) (fun B=>B T)).elim
      | succ j =>
        exact (M ⟨j,rfl,incoming_succ C e j H⟩).elim
    · exact spectator_token d C hh G F N x X k R.shape.2.1 e E H

/-- The structural all-mark theorem is used only for tags. The packet
    equality is proved independently from the complete physical rows. -/
theorem seal_reverse_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (R : SealD d C x k) (digit : 0<(params d s).digits)
    (e : Fin n) (NC : NoConsume d C x e) :
    let y := rawNext s x e
    SealD d C y k ∨ ∃ j,k=j+1 ∧ e=out C j ∧ SealD d C y j := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  have rootD (Z : k=0) : (tok d C x 0).tag=3 := by
    rw [←Z,R.packet]
    rfl
  have HT (E : e=door C) : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2 := by
    have K : k≠0 := fun Z=>NC.elim (fun L=>L E) (fun L=>L (rootD Z))
    rw [R.shape.2.2 0 C.positive]
    exact .inl (by simp [backTag,show 0<k by omega])
  have PC := (wait_pc d C x e N (CF.mask x X) R.pc HT).trans R.pc
  have S := ReportOwnerReverseControl.all_mark d C hh G F N x X k R.shape digit e
  by_cases M : ∃ j,k=j+1 ∧ e=out C j
  · obtain ⟨j,J,E⟩ := M
    subst k e
    have A := raw_seal_reverse_hop d C x N (CF.mask x X) j R
    rcases S with H|⟨l,L,_,H⟩|⟨Z,_,_⟩
    · have T := H.2.2 j (by have := R.shape.2.1; omega)
      rw [A] at T
      simp [backTag,Reply] at T
    · have L0 : l=j := by omega
      subst l
      exact .inr ⟨j,rfl,rfl,⟨H,PC,A⟩⟩
    · omega
  · rcases S with H|⟨j,J,E,_⟩|⟨Z,E,_⟩
    · exact .inl ⟨H,PC,(D_hold d C hh G F N x X k R e M NC).trans R.packet⟩
    · exact (M ⟨j,J,E⟩).elim
    · exact (NC.elim (fun B=>B E) (fun B=>B (rootD Z))).elim

/-- Each actual pre-consume mark preserves the exact old healthy reply at
its current reverse cursor or transfers it to its predecessor. -/
theorem seal_reverse_run (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : SealD d C x k)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x w) :
    Cached d hh Q (rawRun x w) ∧ ∃ j≤k, SealD d C (rawRun x w) j := by
  let CF := cached_fibre d N hh Q F
  induction T with
  | nil => exact ⟨X,k,Nat.le_refl _,R⟩
  | @snoc w e T nc IH =>
    obtain ⟨Y,j,J,A⟩ := IH
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨CF.closed _ e Y,?_⟩
    rcases seal_reverse_step d C hh G F N _ Y j A digit e nc with B|⟨i,I,_,B⟩
    · exact ⟨j,J,B⟩
    · exact ⟨i,by omega,B⟩

theorem seal_root_consume (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (A : SealD d C x 0)
    (digit : 0<(params d s).digits) :
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ EmptyIssueShape d C y ∧
      readPC d C y=(1,commitOp (params d s)) := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  let CF := cached_fibre d N hh Q F
  have ReplyOld : t=Reply p := (root_pub d C x).symm.trans A.packet
  have O : sourceOpcode p v=sealOp p := congrArg Prod.snd A.pc
  have L : writeOp p≤sourceOpcode p v := by rw [O]; unfold writeOp sealOp; omega
  have H := write_seal_ack_control p v t (congrArg Prod.fst A.pc) L (Nat.le_of_eq O)
    (by rw [ReplyOld]; rfl) (by rw [ReplyOld,O]; rfl) (by rw [ReplyOld]; rfl)
    (by rw [ReplyOld]; change (0:Nat)≠1; decide)
  rw [O] at H
  have H' : acqSourcePC p v t=(1,commitOp p) := by
    rw [H]
    unfold writeSealNext
    rw [if_neg (Nat.lt_irrefl _)]
  exact ⟨CF.closed x (door C) X,door_consumes_root d C hh G F N x X A.shape digit,
     (raw_door_final d C x N (CF.mask x X)).1.trans H'⟩

/-- Literal SEAL turn followed by the actual reverse word and the source's
first consume. The terminal packet is assumed healthy; the reverse
transport and source success require no further bank premise. -/
theorem healthy_seal_turn_to_consume (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (K : k+1=C.L)
    (R : ForwardWait d C x k) (Src : readPC d C x=(2,sealOp (params d s)))
    (H : SealCommitForward (params d s) (tok d C x k))
    (O : (tok d C x k).opcode=sealOp (params d s))
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (out C k)) w)
    (Tag : (tok d C (rawRun (rawNext s x (out C k)) w) 0).tag=3) :
    let old := rawRun (rawNext s x (out C k)) w
    tok d C old 0=Reply (params d s) ∧
      readPC d C (rawNext s old (door C))=(1,commitOp (params d s)) := by
  dsimp only
  obtain ⟨Y,B⟩ := healthy_seal_terminal d C N hh G F x X k K R Src H O
  obtain ⟨Z,j,_,S⟩ := seal_reverse_run d C hh G F N _ Y k B digit w T
  have J : j=0 := by
    by_cases P : j=0
    · exact P
    · have E := S.shape.2.2 0 C.positive
      rw [Tag] at E
      simp [backTag,show 0<j by omega] at E
  subst j
  exact ⟨S.packet,(seal_root_consume d C hh G F N _ Z S digit).2.2⟩

end L4.ReportSealReverse
