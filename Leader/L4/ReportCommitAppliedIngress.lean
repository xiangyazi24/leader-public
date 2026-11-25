import Leader.L4.ReportLateIngressSplit
import Leader.L4.ReportIngressOwnership

namespace L4.ReportCommitAppliedIngress
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerDoorProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl ReportOwnerIssueControl
open ReportOwnerReverseControl ReportByteRows ReportRawProjection ReportWriteSplit
open ReportLeaseOwner ReportIngressOwnership

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem applied_ingress_at (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1<C.L)
    (R : ForwardWait d C x k)
    (hdr : h (rightNeighbor (out C k))=true)
    (L : C.route.port k=0) (K : C.route.port (k+1)=1)
    (t : Tok) (T : tok d C x k=t)
    (H : SealCommitForward (params d s) t)
    (O : t.opcode=commitOp (params d s))
    (Accept : packetCommitGuard (params d s) (bytesR d x (out C k)) t=true) :
    let y := rawNext s x (out C k)
    Cached d hh Q y ∧ ForwardWait d C y (k+1) ∧ readPC d C y=readPC d C x ∧
      tok d C y k=MISByteCodec.T ∧ tok d C y (k+1)={t with applied:=true} := by
  let p := params d s
  let e := out C k
  let y := rawNext s x e
  let u := bytesL d x e
  let v := bytesR d x e
  let CF := cached_fibre d N hh Q F
  have P : publicationToken p (h e) u (C.route.port k)=t := by
    rwa [predecessor_projection] at T
  have W := raw_pair_wire d C x N (CF.mask x X) k
  have E := seal_commit_hop_pair p (h e) (h (rightNeighbor e)) u v
    (C.route.port k) (C.route.port (k+1)) (internal_dest C k J)
    (P.symm ▸ H) (chartGate d C y (k+1))
  dsimp only at E
  have In : (effect p u v (h e) (h (rightNeighbor e)) (C.route.port k)
      (some (C.route.port (k+1))) (winOld p u (grantAsk p (h e) u (acqOp p)) (grantAsk p (h e) u 0) (C.route.port k))
      (publicationToken p (h e) u (C.route.port k))).2.2={t with applied:=true} := by
    rw [P,commit_effect_token p _ _ u v _ _ _ t O H.2.2.2.2.2.2.1,
      if_pos ⟨hdr,L,K⟩,if_pos Accept]
  have Trail : tok d C y k=MISByteCodec.T := by
    change tok d C (rawNext s x (out C k)) k=_
    rw [tok_wire,W.1,workL,E.1]
    exact drain_decode_T p _
  have Pkt : tok d C y (k+1)={t with applied:=true} := by
    change tok d C (rawNext s x (out C k)) (k+1)=_
    rw [tok_wire,W.2,workR,E.2.2]
    exact In
  have PC := forward_step_control d C N hh F x X k R e
  refine ⟨CF.closed x e X,?_,PC,Trail,Pkt⟩
  rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R e with A|⟨_,A|⟨E0,_⟩⟩
  · have B := A.2.2 k R.2.1
    change (tok d C y k).tag=frontTag k k at B
    rw [Trail] at B
    simp [MISByteCodec.T,frontTag] at B
  · exact A
  · omega

theorem applied_ingress (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (t : Tok)
    (R : ForwardWait d (charter G r) x ((charter G r).a-1))
    (T : tok d (charter G r) x ((charter G r).a-1)=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=commitOp (params d s))
    (Accept : packetCommitGuard (params d s) (bytesR d x (out (charter G r) ((charter G r).a-1))) t=true) :
    let C := charter G r
    let y := rawNext s x (out C (C.a-1))
    Cached d hh Q y ∧ ForwardWait d C y C.a ∧ readPC d C y=readPC d C x ∧
      tok d C y (C.a-1)=MISByteCodec.T ∧ tok d C y C.a={t with applied:=true} := by
  dsimp only
  let C := charter G r
  obtain ⟨pos,below,head,one,zero⟩ := canonical_centre G r
  change 0<C.a at pos
  change C.a<C.L at below
  have Eq : C.a-1+1=C.a := by omega
  have Hd : h (rightNeighbor (out C (C.a-1)))=true := by
    rw [chart_succ,Eq]
    exact head
  have K : C.route.port (C.a-1+1)=1 := by
    rw [Eq]
    exact one
  have P := applied_ingress_at d C hh G F N x X (C.a-1)
    (by omega) R Hd zero K t T H O Accept
  dsimp only at P
  rw [Eq] at P
  exact P

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

private theorem fault3_decode (p : Params) (g : Bool) :
    decode p g (resetTokenWire p (MISByteCodec.faultToken 3))=MISByteCodec.faultToken 3 := by
  let t := MISByteCodec.faultToken 3
  have Fit : RankFits p t := ⟨by decide,Nat.two_pow_pos _,Nat.two_pow_pos _,by decide,by decide⟩
  have A := rReadFields p t Fit
  have J : (resetTokenWire p t).getLsbD (6+o p+payW p)=true := by
    rw [rGet_bit,A.2.1]
    rfl
  have G : get (resetTokenWire p t) (7+o p+payW p) 2 = 3 := A.1
  change decode p g (resetTokenWire p t)=t
  change decodeFields p g (resetTokenWire p t)=t
  simp only [decodeFields,G,J]
  rfl

theorem commit_ack_decode (p : Params) (g : Bool) (fit : commitOp p<2^o p) :
    decode p g (resetTokenWire p ({tag:=3,opcode:=commitOp p}:Tok))=
      ({tag:=3,opcode:=commitOp p}:Tok) := by
  let t : Tok := {tag:=3,opcode:=commitOp p}
  have Fit : RankFits p t := ⟨(by decide : 3<4),fit,Nat.two_pow_pos _,(by decide : 0<8),(by decide : 0<4)⟩
  have F := rReadFields p t Fit
  have B : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,F.2.1]
    rfl
  have A : commitOp p≠acqOp p := by unfold commitOp acqOp; omega
  have D : commitOp p≠admitOp p := by unfold commitOp admitOp; omega
  have L : ¬commitOp p<writeOp p := by unfold commitOp writeOp; omega
  change decode p g (resetTokenWire p t)=t
  change decodeFields p g (resetTokenWire p t)=t
  simp only [decodeFields,F.1,F.2.2.1,F.2.2.2.1,F.2.2.2.2.1,F.2.2.2.2.2.2,B]
  simp [t,A,D,L]

/-- The actual terminal row can acknowledge a healthy COMMIT only
after its applied bit is set. An unapplied healthy token turns to D-fault. -/
theorem commit_terminal_joined (d : Sheet) (C : Chart h) (x : Raw s n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (J : k+1=C.L) (t : Tok) (T : tok d C x k=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=commitOp (params d s)) :
    let y := rawNext s x (out C k)
    tok d C y k=if t.applied then {tag:=3,opcode:=commitOp (params d s)}
      else MISByteCodec.faultToken 3 := by
  dsimp only
  let e := out C k
  let p := params d s
  let u := bytesL d x e
  let v := bytesR d x e
  let j := C.route.port k
  have P : publicationToken p (h e) u j=t := by
    rwa [predecessor_projection] at T
  have W := raw_pair_wire d C x N mask k
  have E := commit_terminal_pair p (h e) (h (rightNeighbor e)) u v j
    (end_dest C k J) (P.symm ▸ H) (P.symm ▸ O)
  dsimp only at E
  rw [P] at E
  rw [tok_wire,W.1,workL,E]
  cases B : t.applied
  · simp only [Bool.false_eq_true,if_false]
    exact fault3_decode p _
  · simp only [if_true]
    have Fit : RankFits p t := P ▸ rank_decoded_fits p (rankGate p (h e) u j) (resetTokenRead p u j)
    exact commit_ack_decode p _ (O ▸ Fit.op)

#print axioms commit_ack_decode
#print axioms commit_terminal_joined
#print axioms applied_ingress_at
#print axioms applied_ingress
end L4.ReportCommitAppliedIngress
