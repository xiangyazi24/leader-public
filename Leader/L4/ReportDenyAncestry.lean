import Leader.L4.ReportAdmitAncestry
import Leader.L4.ReportFastGateRaw
import Leader.L4.ReportFastNoRearm
import Leader.L4.ReportFastTargetFence
import Leader.L4.ReportWriteSplit
import Leader.L4.ReportOwnerAcquireProvenance

namespace L4.ReportDenyAncestry
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerForwardControl ReportOwnerIssueControl ReportOwnerReverseControl
open ReportLeaseGrants ReportFastNoRearm ReportFastTargetFence ReportOwnerSerial ReportOwnerCommandRail
open ReportByteRows ReportRawProjection ReportWriteSplit ReportAdmitAncestry ReportFastGateRaw
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

theorem admit_ack_decode (p : Params) (g : Bool) (fit : admitOp p<2^o p) :
    decode p g (resetTokenWire p ({tag:=3,opcode:=admitOp p}:Tok))=
      ({tag:=3,opcode:=admitOp p}:Tok) := by
  let t : Tok := {tag:=3,opcode:=admitOp p}
  have Fit : RankFits p t := ⟨(by decide : 3<4),fit,Nat.two_pow_pos _,(by decide : 0<8),(by decide : 0<4)⟩
  have F := rReadFields p t Fit
  have B : (resetTokenWire p t).getLsbD (6+o p+payW p)=false := by
    rw [rGet_bit,F.2.1]
    rfl
  have A : admitOp p≠acqOp p := by unfold admitOp acqOp; omega
  have L : admitOp p<writeOp p := by unfold admitOp writeOp; omega
  change decode p g (resetTokenWire p t)=t
  change decodeFields p g (resetTokenWire p t)=t
  simp only [decodeFields,F.1,F.2.2.1,F.2.2.2.1,F.2.2.2.2.1,F.2.2.2.2.2.2,B]
  have M : ¬commitOp p<admitOp p := by unfold commitOp admitOp; omega
  simp [t,A,L,M,show ¬cmpOp p≤admitOp p by unfold cmpOp admitOp; omega]

def Reply (p : Params) : Tok := {tag:=3,opcode:=admitOp p}

private theorem admit_op_fit (p : Params) : admitOp p<2^o p := by
  have H := power_of_ell (5+4*p.digits)
  unfold o admitOp
  omega

structure AdmitD (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop where
  shape : ReverseWait d C x k
  pc : readPC d C x=(2,admitOp (params d s))
  packet : tok d C x k=Reply (params d s)

theorem denied_terminal (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1=C.L)
    (R : ForwardWait d C x k) (Src : readPC d C x=(2,admitOp (params d s)))
    (Off : chartGate d C x k=false) (A : tok d C x k=admitF (params d s) 0) :
    let y := rawNext s x (out C k)
    Cached d hh Q y ∧ AdmitD d C y k := by
  dsimp only
  let p := params d s
  let e := out C k
  let y := rawNext s x e
  let CF := cached_fibre d N hh Q F
  have M := CF.mask x X
  rw [predecessor_projection] at A
  have W := raw_pair_wire d C x N M k
  have Rw := deny_admit_terminal_wire p (h e) (h (rightNeighbor e)) (bytesL d x e) (bytesR d x e)
    _ (end_dest C k J) Off A
  have P : tok d C y k=Reply p := by
    change tok d C (rawNext s x (out C k)) k=_
    rw [tok_wire,W.1,workL,Rw]
    exact admit_ack_decode p _ (admit_op_fit p)
  have B : ReverseWait d C y k := by
    rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R e with B|⟨_,B|⟨_,B⟩⟩
    · have K := B.2.2 k R.2.1
      rw [P] at K
      simp [Reply,frontTag] at K
    · have I := B.2.1
      omega
    · exact B
  exact ⟨CF.closed x e X,⟨B,(forward_step_control d C N hh F x X k R e).trans Src,P⟩⟩

theorem raw_admit_reverse_hop (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (R : AdmitD d C x (j+1)) :
    tok d C (rawNext s x (out C j)) j=Reply (params d s) := by
  have I := R.shape.2.1
  have T : (tok d C x j).tag≠2 := by
    rw [R.shape.2.2 j (by omega)]
    simp [backTag]
  have D : (tok d C x (j+1)).tag=3 := by rw [R.packet]; rfl
  have W := (reverse_joined d C x N mask j I T D).1
  rw [tok_wire,W,R.packet]
  exact admit_ack_decode (params d s) _ (admit_op_fit _)
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
    (P : readPC d C x=(2,admitOp (params d s)))
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
      have O0 : sourceOpcode p v=admitOp p := congrArg Prod.snd P
      rw [O0]
      unfold admitOp commitOp
      omega
    exact (raw_door_final d C x N mask).1.trans
      (prelaunch_hold_controls p v t V O A)
  · exact raw_nondoor_control d C x e N mask E

private theorem D_outgoing_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (R : AdmitD d C x k) :
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
  rcases rank_norm_cases p _ _ 3 (.inr rfl) with E|E
  · exact E
  · have A' := A
    rw [rankToken_wire] at A'
    have J := E.2.1
    rw [A'] at J
    simp [Reply] at J

private theorem D_hold (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (R : AdmitD d C x k) (e : Fin n)
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
theorem admit_reverse_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (R : AdmitD d C x k) (digit : 0<(params d s).digits)
    (e : Fin n) (NC : NoConsume d C x e) :
    let y := rawNext s x e
    AdmitD d C y k ∨ ∃ j,k=j+1 ∧ e=out C j ∧ AdmitD d C y j := by
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
    have A := raw_admit_reverse_hop d C x N (CF.mask x X) j R
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
theorem admit_reverse_run (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : AdmitD d C x k)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x w) :
    Cached d hh Q (rawRun x w) ∧ ∃ j≤k, AdmitD d C (rawRun x w) j := by
  let CF := cached_fibre d N hh Q F
  induction T with
  | nil => exact ⟨X,k,Nat.le_refl _,R⟩
  | @snoc w e T nc IH =>
    obtain ⟨Y,j,J,A⟩ := IH
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨CF.closed _ e Y,?_⟩
    rcases admit_reverse_step d C hh G F N _ Y j A digit e nc with B|⟨i,I,_,B⟩
    · exact ⟨j,J,B⟩
    · exact ⟨i,by omega,B⟩

structure TailF (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop where
  pastGate : C.a+2<k
  shape : ForwardWait d C x k
  pc : readPC d C x=(2,admitOp (params d s))
  packet : tok d C x k=admitF (params d s) 0

theorem gate_depart_seeds (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1<C.L) (K : k=C.a+2)
    (R : ForwardWait d C x k) (PC : readPC d C x=(2,admitOp (params d s)))
    (A : healthyAdmit (params d s) (tok d C x k)) (D : (tok d C x k).race=4) :
    TailF d C (rawNext s x (out C k)) (k+1) := by
  have Geo := (gate_geometry d C hh G (Q:=Q)).2.2 x X
  have H := (Geo k R.2.1).mpr K
  have F0 := Bool.eq_false_iff.mpr (fun A => by have := (Geo (k+1) J).mp A; omega)
  have E : tok d C x k=decode (params d s) true (wire d C x k) := by rw [tok_wire,H]
  obtain ⟨q,r,_,_,_,S⟩ := rank_admit_shape _ _ (E ▸ A)
  have Shape := E.trans S
  have P := (raw_ready_depart d C N hh G F x X k J H F0 A (by omega)).2
  have Packet : tok d C (rawNext s x (out C k)) (k+1)=admitF (params d s) 0 := by
    rw [P,D,Shape]
    rfl
  have T : (tok d C (rawNext s x (out C k)) (k+1)).tag=2 := by rw [Packet]; rfl
  have Shape' : ForwardWait d C (rawNext s x (out C k)) (k+1) := by
    rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R (out C k) with V|⟨_,V|⟨B,V⟩⟩
    · have Bad := V.2.2 (k+1) J
      rw [T] at Bad
      simp [frontTag,show ¬k+1<k by omega] at Bad
    · exact V
    · omega
  exact ⟨by omega,Shape',(forward_step_control d C N hh F x X k R _).trans PC,Packet⟩

theorem tail_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : TailF d C x k) (e : Fin n) :
    let y := rawNext s x e
    TailF d C y k ∨ TailF d C y (k+1) ∨ AdmitD d C y k := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  let y := rawNext s x e
  have off (j : Nat) (B : j<C.L) (P : C.a+2<j) : chartGate d C x j=false :=
    Bool.eq_false_iff.mpr (fun H=>Nat.ne_of_gt P ((gate_geometry d C hh G (Q:=Q)).2.2 x X j B |>.mp H))
  have PC := (forward_step_control d C N hh F x X k R.shape e).trans R.pc
  rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R.shape e with V|⟨E,V|⟨J,V⟩⟩
  · have NE : e≠out C k := by
      intro E
      subst e
      by_cases I : k+1<C.L
      · have H := off_hop d C N hh G F x X k I
          (off k R.shape.2.1 R.pastGate) (off (k+1) I (by have := R.pastGate; omega)) _ (by decide) R.packet
        have P := V.2.2 (k+1) I
        rw [H] at P
        simp [admitF,frontTag,show ¬k+1<k by omega] at P
      · have L : k+1=C.L := by have := R.shape.2.1; omega
        have H := (denied_terminal d C N hh G F x X k L R.shape R.pc (off k R.shape.2.1 R.pastGate) R.packet).2.packet
        have P := V.2.2 k R.shape.2.1
        rw [H] at P
        simp [Reply,frontTag] at P
    exact .inl ⟨R.pastGate,V,PC, (off_hold d C hh G F N x X k R.shape e NE (off k R.shape.2.1 R.pastGate) _ R.packet).trans R.packet⟩
  · subst e
    have I := V.2.1
    have P : C.a+2<k+1 := by have := R.pastGate; omega
    exact .inr (.inl ⟨P,V,PC,off_hop d C N hh G F _ X k I (off k R.shape.2.1 R.pastGate) (off _ I P) _ (by decide) R.packet⟩)
  · subst e
    exact .inr (.inr (denied_terminal d C N hh G F x X k J R.shape R.pc (off k R.shape.2.1 R.pastGate) R.packet).2)

/-- The exact post-decision tape may include any unrelated marks,
holds, forward hops, the turn, and reverse hops. The own root consume
is excluded by BeforeConsume; no timing or fairness assumptions. -/
theorem deny_tail_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : TailF d C x k)
    (digit : 0<(params d s).digits) (w : List (Fin n)) (T : BeforeConsume d C x w) :
    Cached d hh Q (rawRun x w) ∧
      ((∃ j,TailF d C (rawRun x w) j) ∨ ∃ j,AdmitD d C (rawRun x w) j) := by
  let CF := cached_fibre d N hh Q F
  induction T with
  | nil => exact ⟨X,.inl ⟨k,R⟩⟩
  | @snoc w e T nc IH =>
    obtain ⟨Y,P⟩ := IH
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨CF.closed _ e Y,?_⟩
    rcases P with ⟨j,A⟩|⟨j,A⟩
    · rcases tail_step d C N hh G F _ Y j A e with B|B|B
      · exact .inl ⟨j,B⟩
      · exact .inl ⟨j+1,B⟩
      · exact .inr ⟨j,B⟩
    · rcases admit_reverse_step d C hh G F N _ Y j A digit e nc with B|⟨l,_,_,B⟩
      · exact .inr ⟨j,B⟩
      · exact .inr ⟨l,B⟩

/-- A real root return following the actual denied gate departure is the
canonical payload-zero ADMIT D, and its actual own consume retries. -/
theorem denied_departure_to_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1<C.L) (K : k=C.a+2)
    (R : ForwardWait d C x k) (PC : readPC d C x=(2,admitOp (params d s)))
    (A : healthyAdmit (params d s) (tok d C x k)) (D : (tok d C x k).race=4)
    (digit : 0<(params d s).digits) (w : List (Fin n))
    (T : BeforeConsume d C (rawNext s x (out C k)) w)
    (Tag : (tok d C (rawRun (rawNext s x (out C k)) w) 0).tag=3) :
    let old := rawRun (rawNext s x (out C k)) w
    AdmitD d C old 0 ∧ readPC d C (rawNext s old (door C))=(1,0) := by
  dsimp only
  let y := rawNext s x (out C k)
  let CF := cached_fibre d N hh Q F
  have Seed := gate_depart_seeds d C N hh G F x X k J K R PC A D
  obtain ⟨Y,S⟩ := deny_tail_run d C N hh G F y (CF.closed x _ X) (k+1) Seed digit w T
  have Root : AdmitD d C (rawRun y w) 0 := by
    rcases S with ⟨j,B⟩|⟨j,B⟩
    · rw [B.shape.2.2 0 C.positive] at Tag
      unfold frontTag at Tag
      split at Tag <;> try contradiction
      split at Tag <;> contradiction
    · by_cases H : j=0
      · simpa [H] using B
      · rw [B.shape.2.2 0 C.positive] at Tag
        simp [backTag,show 0<j by omega] at Tag
  refine ⟨Root,?_⟩
  have A0 : (tok d C (rawRun y w) 0).opcode=admitOp (params d s) := by rw [Root.packet]; rfl
  have L : (tok d C (rawRun y w) 0).fault=false := by rw [Root.packet]; rfl
  have O : (tok d C (rawRun y w) 0).outcome=0 := by rw [Root.packet]; rfl
  have Out := (raw_admit_consume d C N _ (CF.mask _ Y) Root.pc Tag A0 L O).1
  rw [Root.packet] at Out
  exact Out

structure DenyGate (d : Sheet) (C : Chart h) (x : Raw s n) (i r : Nat) : Prop where
  atGate : i+1=C.a+2
  shape : ForwardWait d C x (i+1)
  pc : readPC d C x=(2,admitOp (params d s))
  healthy : healthyAdmit (params d s) (tok d C x (i+1))
  race : (tok d C x (i+1)).race=r

/-- The sole extra mark restriction is at a real live race 1:
incoming is unblocked, outgoing is mapped away. At race2 the
outgoing mark must be allowed to settle to rank4. -/
theorem deny_gate_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i r : Nat) (R : DenyGate d C x i r)
    (OK : r=1 ∨ r=2 ∨ r=4) (J : i+1+1<C.L) (e : Fin n)
    (Map : r=1 → e≠out C (i+1)) :
    let y := rawNext s x e
    (∃ r', (r'=1 ∨ r'=2 ∨ r'=4) ∧ DenyGate d C y i r') ∨ TailF d C y (i+1+1) := by
  dsimp only
  let y := rawNext s x e
  have I := R.shape.2.1
  have A := ((gate_geometry d C hh G (Q:=Q)).2.2 x X (i+1) I).mpr R.atGate
  have P : (tok d C x i).tag≠2 := by
    rw [R.shape.2.2 i (by omega)]
    simp [frontTag]
  have PC := (forward_step_control d C N hh F x X (i+1) R.shape e).trans R.pc
  have same (W : tok d C y (i+1)=tok d C x (i+1)) :
      (∃ r', (r'=1 ∨ r'=2 ∨ r'=4) ∧ DenyGate d C y i r') ∨ TailF d C y (i+1+1) := by
    have T : (tok d C y (i+1)).tag=2 := by rw [W]; exact R.healthy.1
    have V : ForwardWait d C y (i+1) := by
      rcases ReportOwnerForwardControl.all_mark d C hh G F N x X (i+1) R.shape e with V|⟨_,V|⟨Z,V⟩⟩
      · exact V
      · have B := V.2.2 (i+1) I
        rw [T] at B
        simp [frontTag] at B
      · omega
    exact .inl ⟨r,OK,⟨R.atGate,V,PC,by rw [W]; exact R.healthy,by rw [W]; exact R.race⟩⟩
  have decideTo (r' : Nat) (K : r'=2 ∨ r'=4)
      (W : tok d C y (i+1)={(tok d C x (i+1)) with race:=r'}) :
      (∃ r', (r'=1 ∨ r'=2 ∨ r'=4) ∧ DenyGate d C y i r') ∨ TailF d C y (i+1+1) := by
    have T : (tok d C y (i+1)).tag=2 := by rw [W]; exact R.healthy.1
    have V : ForwardWait d C y (i+1) := by
      rcases ReportOwnerForwardControl.all_mark d C hh G F N x X (i+1) R.shape e with V|⟨_,V|⟨Z,V⟩⟩
      · exact V
      · have B := V.2.2 (i+1) I
        rw [T] at B
        simp [frontTag] at B
      · omega
    have Healthy : healthyAdmit (params d s) (tok d C y (i+1)) := by
      rw [W]
      exact R.healthy
    exact .inl ⟨r',.inr K,⟨R.atGate,V,PC,Healthy,congrArg (fun t : Tok=>t.race) W⟩⟩
  rcases OK with O|O|O
  · by_cases E : e=out C i
    · subst e
      apply decideTo 2 (.inl rfl)
      rw [raw_incoming_decisions d C N hh G F x X i I A P R.healthy (.inl (R.race.trans O)),R.race,O]
      rfl
    · apply same
      exact raw_gate_spectator d C N hh G F x X i I e E (Map O)
  · by_cases E : e=out C (i+1)
    · subst e
      apply decideTo 4 (.inr rfl)
      rw [raw_outgoing_decisions d C N hh G F x X (i+1) I A R.healthy (.inr (R.race.trans O)),R.race,O]
      rfl
    · apply same
      exact raw_no_rearm_step d C N hh G F x X (.inr (.inl ⟨i+1,R.shape⟩)) i I A
        R.healthy false (R.race.trans O) e E
  · by_cases E : e=out C (i+1)
    · subst e
      exact .inr (gate_depart_seeds d C N hh G F x X (i+1) J R.atGate R.shape R.pc R.healthy (R.race.trans O))
    · by_cases E' : e=out C i
      · subst e
        apply same
        have Tok : tok d C x (i+1)=decode (params d s) true (wire d C x (i+1)) := by rw [tok_wire,A]
        have V := raw_in_norm d C N hh G F x X i I A P R.healthy
        rcases rank_norm_cases (params d s) true (wire d C x (i+1)) 2 (.inl rfl) with L|L
        · exact V.trans (L.trans Tok.symm)
        · rw [←Tok,R.race,O] at L
          rcases L.2.2.2.2.2 with L|L|L <;> omega
      · exact same (raw_gate_spectator d C N hh G F x X i I e E' E)

/-- Match the *actual mapped* tape, not a restriction on arbitrary draws. -/
def DenyMapped (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∀ (u v : List (Fin n)) (e : Fin n), w=u++e::v →
    healthyAdmit (params d s) (tok d C (rawRun x u) (C.a+2)) →
    (tok d C (rawRun x u) (C.a+2)).race=1 → e≠out C (C.a+2)

def DenyFlight (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Prop :=
  (∃ r,(r=1 ∨ r=2 ∨ r=4) ∧ DenyGate d C x i r) ∨
  (∃ k,TailF d C x k) ∨ ∃ k,AdmitD d C x k

theorem deny_before_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (J : i+1+1<C.L)
    (digit : 0<(params d s).digits)
    (A : DenyFlight d C x i) (w : List (Fin n))
    (T : BeforeConsume d C x w) (Map : DenyMapped d C x w) :
    DenyFlight d C (rawRun x w) i := by
  let CF := cached_fibre d N hh Q F
  suffices H : Cached d hh Q (rawRun x w) ∧ DenyFlight d C (rawRun x w) i from H.2
  induction T with
  | nil => exact ⟨X,A⟩
  | @snoc w e T nc IH =>
    have M : DenyMapped d C x w := by
      intro u v f E
      exact Map u (v++[e]) f (by rw [E,List.append_assoc]; rfl)
    have M0 := Map w [] e rfl
    obtain ⟨Y,P⟩ := IH M
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨CF.closed _ e Y,?_⟩
    rcases P with ⟨r,O,R⟩|⟨k,R⟩|⟨k,R⟩
    · have Rule : r=1 → e≠out C (i+1) := by
        intro E
        rw [R.atGate]
        apply M0
        · rw [←R.atGate]
          exact R.healthy
        · rw [←R.atGate]
          exact R.race.trans E
      rcases deny_gate_step d C N hh G F _ Y i r R O J e Rule with H|H
      · exact .inl H
      · exact .inr (.inl ⟨_,H⟩)
    · rcases tail_step d C N hh G F _ Y k R e with B|B|B
      · exact .inr (.inl ⟨k,B⟩)
      · exact .inr (.inl ⟨k+1,B⟩)
      · exact .inr (.inr ⟨k,B⟩)
    · rcases admit_reverse_step d C hh G F N _ Y k R digit e nc with B|⟨l,_,_,B⟩
      · exact .inr (.inr ⟨k,B⟩)
      · exact .inr (.inr ⟨l,B⟩)

def DenyInv (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  ((readPC d C x).2≠acqOp (params d s) ∧
    ((readPC d C x).2≠admitOp (params d s) ∨ (readPC d C x).1=1)) ∨
  ((readPC d C x)=(2,admitOp (params d s)) ∧
    ∃ k,OffFront d C x k) ∨
  DenyFlight d C x (C.a+1)

theorem deny_nonacq (d : Sheet) (C : Chart h) (x : Raw s n)
    (D : DenyInv d C x) : (readPC d C x).2≠acqOp (params d s) := by
  have Ne : admitOp (params d s)≠acqOp (params d s) := by unfold admitOp acqOp; omega
  rcases D with A|⟨P,_⟩|⟨_,_,R⟩|⟨_,R⟩|⟨_,R⟩
  · exact A.1
  · exact fun H=>Ne ((congrArg Prod.snd P).symm.trans H)
  · exact fun H=>Ne ((congrArg Prod.snd R.pc).symm.trans H)
  · exact fun H=>Ne ((congrArg Prod.snd R.pc).symm.trans H)
  · exact fun H=>Ne ((congrArg Prod.snd R.pc).symm.trans H)

theorem deny_inv_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d C x)
    (digit : 0<(params d s).digits) (e : Fin n) (D : DenyInv d C x)
    (Map : healthyAdmit (params d s) (tok d C x (C.a+2)) →
      (tok d C x (C.a+2)).race=1 → e≠out C (C.a+2)) :
    DenyInv d C (rawNext s x e) := by
  let y := rawNext s x e
  have J := (ReportFastOwnerSupport.gate_room C G).1
  rcases D with ⟨No,A⟩|⟨PC,k,R⟩|⟨r,O,R⟩|⟨k,R⟩|⟨k,R⟩
  · by_cases A0 : (readPC d C x).2=admitOp (params d s)
    · have PH := A.resolve_left (fun p=>p A0)
      have I : LegalIssue d C x := by
        rcases S.1 with I|⟨k,I⟩|⟨k,I⟩
        · exact I
        · have H := I.1.1; omega
        · have H := I.1.1; omega
      by_cases E : e=door C
      · subst e
        have F0 := origin_seed d C hh G F N x X I A0
        have P : readPC d C y=(2,admitOp (params d s)) := by
          have S' := strong_step d C N hh G F x X S digit (door C)
          exact Prod.ext F0.2.1.1.1
            ((S'.2 0 F0.2.1.2.1 (.inl (by rw [F0.2.2]; rfl)) (by rw [F0.2.2]; rfl)).symm.trans
              (by rw [F0.2.2]; rfl))
        exact .inr (.inl ⟨P,0,F0⟩)
      · have P := (ReportOwnerIssueControl.nondoor_preserves d C hh G F N x X I e E).2
        exact .inl ⟨by rw [P]; exact No,.inr (by rw [P]; exact PH)⟩
    · have No' : (readPC d C y).2≠acqOp (params d s) :=
        fun E => A0 (fresh_acq_requires_admit_door d C N hh G F digit x X S e No E).2
      refine .inl ⟨No',?_⟩
      by_cases B : (readPC d C y).2=admitOp (params d s)
      · right
        rcases pc_step_with_phase d C N hh G F digit x X S e with V|V|⟨PH,_⟩
        · have P := V.1
          rw [B] at P
          unfold admitOp at P
          omega
        · exact False.elim (A0 (V.symm.trans B))
        · exact PH
      · exact .inl B
  · have P := (forward_step_control d C N hh F x X k R.2.1 e).trans PC
    rcases before_gate_mark d C hh G F N x X k R e with ⟨E,K⟩|⟨j,V⟩
    · subst e
      have I : k+1<C.L := by omega
      have H := (origin_arrive d C hh G F N x X k R K).2
      rw [←K] at H
      have Wait : ForwardWait d C y (k+1) := by
        rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R.2.1 (out C k) with B|⟨_,B|⟨D,_⟩⟩
        · have V := B.2.2 (k+1) I
          rw [H] at V
          simp [frontTag,show ¬k+1<k by omega] at V
        · exact B
        · omega
      have G1 : DenyGate d C y k 1 := ⟨K,Wait,P,by rw [H]; exact ⟨rfl,rfl,rfl⟩,by rw [H]⟩
      have E : k=C.a+1 := by omega
      exact .inr (.inr (.inl ⟨1,.inl rfl,E ▸ G1⟩))
    · exact .inr (.inl ⟨P,j,V⟩)
  · have Rule : r=1 → e≠out C (C.a+1+1) := by
      intro E
      rw [R.atGate]
      exact Map (R.atGate ▸ R.healthy) (R.atGate ▸ R.race.trans E)
    rcases deny_gate_step d C N hh G F x X _ r R O (by omega) e Rule with B|B
    · exact .inr (.inr (.inl B))
    · exact .inr (.inr (.inr (.inl ⟨_,B⟩)))
  · rcases tail_step d C N hh G F x X k R e with B|B|B
    · exact .inr (.inr (.inr (.inl ⟨_,B⟩)))
    · exact .inr (.inr (.inr (.inl ⟨_,B⟩)))
    · exact .inr (.inr (.inr (.inr ⟨_,B⟩)))
  · by_cases E : k=0 ∧ e=door C
    · obtain ⟨rfl,rfl⟩ := E
      have T : (tok d C x 0).tag=3 := by rw [R.packet]; rfl
      have O : (tok d C x 0).opcode=admitOp (params d s) := by rw [R.packet]; rfl
      have L : (tok d C x 0).fault=false := by rw [R.packet]; rfl
      have Q0 : (tok d C x 0).outcome=0 := by rw [R.packet]; rfl
      have V := (raw_admit_consume d C N x ((cached_fibre d N hh Q F).mask x X) R.pc T O L Q0).1
      rw [R.packet] at V
      change readPC d C y=(1,0) at V
      exact .inl ⟨by rw [V]; unfold acqOp; omega,.inr (by rw [V])⟩
    · have NC : NoConsume d C x e := by
        by_cases A : e=door C
        · right
          have B : k≠0 := fun B=>E ⟨B,A⟩
          rw [R.shape.2.2 0 C.positive]
          simp [backTag,show 0<k by omega]
        · exact .inl A
      rcases admit_reverse_step d C hh G F N x X k R digit e NC with B|⟨j,_,_,B⟩
      · exact .inr (.inr (.inr (.inr ⟨_,B⟩)))
      · exact .inr (.inr (.inr (.inr ⟨_,B⟩)))

theorem deny_inv_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d C x)
    (digit : 0<(params d s).digits) (w : List (Fin n))
    (D : DenyInv d C x) (Map : DenyMapped d C x w)
    (Clear : ∀ k,k<C.L→h (out C k)=true→rawGrant d x (out C k) (C.route.port k)=false) :
    DenyInv d C (rawRun x w) ∧
      (∀ k,k<C.L→h (out C k)=true→rawGrant d (rawRun x w) (out C k) (C.route.port k)=false) := by
  let CF := cached_fibre d N hh Q F
  induction w generalizing x with
  | nil => exact ⟨D,Clear⟩
  | cons e w IH =>
    let y := rawNext s x e
    have Map0 := Map [] w e rfl
    have Map1 : DenyMapped d C y w := by
      intro u v f E
      exact Map (e::u) v f (congrArg (List.cons e) E)
    have R := deny_inv_step d C N hh G F x X S digit e D Map0
    exact IH y (CF.closed x e X) (strong_step d C N hh G F x X S digit e)
      R Map1 (fun k K H => absent_step d x N e _ _ (Clear k K H)
        (fun _=>no_ask_of_non_acq_pc d C x k K S (CF.mask x X _) (deny_nonacq d C x D)))

/-- A genuine own RESET receipt starts the permanent-denial interval.
On a mapped suffix every old owner lane stays clear, and no ACQ is issued. -/
theorem deny_after_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (digit : 0<(params d s).digits) (reset w : List (Fin n))
    (Receipt : Generated d C x reset .done) (Map : DenyMapped d C (rawRun x reset) w) :
    (readPC d C (rawRun (rawRun x reset) w)).2≠acqOp (params d s) ∧
      (∀ k,k<C.L→h (out C k)=true→
        rawGrant d (rawRun (rawRun x reset) w) (out C k) (C.route.port k)=false) := by
  let a := rawRun x reset
  obtain ⟨Y,P⟩ := cached_genuine_full_parked d C N hh F x X reset Receipt
  have S := seed_receipt d C N hh F x X reset Receipt
  have PC : readPC d C a=(1,1) := pc_fields d C a .issue1 (by decide) P.1.1
  have D : DenyInv d C a := .inl ⟨by rw [PC]; unfold acqOp; omega,.inr (congrArg Prod.fst PC)⟩
  have Clear (k : Nat) (K : k<C.L) (H : h (out C k)=true) :
      rawGrant d a (out C k) (C.route.port k)=false := P.1.2.2 k K H
  obtain ⟨R,A⟩ := deny_inv_run d C N hh G F a Y S digit w D Map Clear
  exact ⟨deny_nonacq d C _ R,A⟩

end L4.ReportDenyAncestry
