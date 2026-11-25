import Leader.L4.ReportRawProjection

namespace L4.ReportWriterPayload
open AllSizeProtocol ReportByteRows

/-- The centre selector stored in this controller's capture file.
It is not a read of the current live centre. -/
def capturedSelector (p : Params) (raw : BitVec p.w) : Nat :=
  ((raw.extractLsb' (sourceBase p + (16+2*d p)) 3).toNat/2)%2

def targetBank (p : Params) (t : Tok) : Nat := (t.payload/2^(2*d p))%2
def priorBank (p : Params) (t : Tok) : Nat := t.payload/2^(2*d p+1)

theorem payload_bounds (m c v : Nat) (H : 0 < m) (C : c ≤ 1) (V : v < m) :
    ((2*c+(1-c))*m+v)/m%2 = 1-c ∧
    ((2*c+(1-c))*m+v)/(2*m) = c := by
  rw [Nat.mul_comm (2*c+(1-c)) m, Nat.mul_add_div H,
    Nat.div_eq_of_lt V,Nat.add_zero]
  constructor
  · omega
  · rw [Nat.mul_comm 2 m, ←Nat.div_div_eq_div_mul]
    rw [Nat.mul_add_div H,Nat.div_eq_of_lt V,Nat.add_zero]
    omega

/-- A WRITE launched by the actual source encodes both its captured
selector and the complementary target. Showing the capture is still
current at a nonheader departure is a separate owner-epoch obligation. -/
theorem issue_write_banks (p : Params) (raw : BitVec p.w) (old t : Tok)
    (P : sourcePhase p raw=1)
    (W : writeOp p≤sourceOpcode p raw) (L : sourceOpcode p raw<sealOp p)
    (T : (source p raw old).2=some t) (Forward : t.tag=2) :
    t.tag = 2 ∧ t.opcode = sourceOpcode p raw ∧ t.fault=false ∧
      priorBank p t = capturedSelector p raw ∧ targetBank p t = 1-capturedSelector p raw := by
  let c := capturedSelector p raw
  let v := (raw.extractLsb' (sourceBase p+3) (2*d p)).toNat
  have H : 0<2^(2*d p) := Nat.two_pow_pos _
  have C : c≤1 := by unfold c capturedSelector; omega
  have V : v<2^(2*d p) := BitVec.isLt _
  have A : ¬commitOp p<sourceOpcode p raw := by unfold sealOp commitOp at *; omega
  have B : sourceOpcode p raw≠acqOp p := by unfold writeOp acqOp at *; omega
  have J : ¬sourceOpcode p raw<writeOp p := Nat.not_lt_of_ge W
  have K : ¬sealOp p≤sourceOpcode p raw := Nat.not_le_of_lt L
  have Z : sourceOpcode p raw≠0 := by unfold writeOp at W; omega
  unfold sourcePhase at P
  unfold sourceOpcode at A B J K W L Z
  simp only [source,P,A,decide_false,show ((1:Nat)==0)=false by decide,
    show ((1:Nat)==3)=false by decide,Bool.false_or,Bool.false_eq_true,
    if_false,beq_self_eq_true,if_true,J,W,L,K,decide_true,Bool.and_true,Bool.true_and] at T
  split at T
  · simp only [Option.some.injEq] at T
    subst t
    simp [MISByteCodec.E] at Forward
  · have U := Option.some.inj T
    subst t
    simp only [beq_iff_eq,B,Bool.and_false,Bool.false_eq_true,if_false]
    have Q := payload_bounds (2^(2*d p)) c v H C V
    change True ∧ sourceOpcode p raw=sourceOpcode p raw ∧ True ∧
      ((2*c+(1-c))*2^(2*d p)+v)/2^(2*d p+1)=c ∧
      ((2*c+(1-c))*2^(2*d p)+v)/2^(2*d p)%2=1-c
    rw [Nat.pow_succ, Nat.mul_comm (2^(2*d p)) 2]
    exact ⟨trivial,rfl,trivial,Q.2,Q.1⟩

private def offset (p : Params) (sel : Nat) :=
  sealBase p+5+(1-sel)*bankW p

/-- The nonheader WRITE effect on the initiator leaves the currently
selected digit pair untouched once the generation supplies equality
with the current centre selector. This is only the effect slice, not
a claim about the entire joined transition or about inherited tokens. -/
theorem nonheader_write_effect_frames_selected (p : Params) (hv win : Bool)
    (u v src : BitVec p.w) (old packet t : Tok)
    (command : Fin p.digits) (next : Option (Fin 3)) (sel : Nat)
    (P : sourcePhase p src=1)
    (W : writeOp p≤sourceOpcode p src) (L : sourceOpcode p src<sealOp p)
    (sent : (source p src old).2=some packet) (forward : packet.tag=2)
    (carried : t.payload=packet.payload) (kept : sel=capturedSelector p src)
    (O : reportOldOffset p false u=command.val)
    (live : t.fault=false) (op : t.opcode=writeOp p+command.val) :
    let patch := (effect p u v false hv 1 next win t).1
    let wide : Patch p.w := ⟨patch.mask.setWidth p.w,patch.value.setWidth p.w⟩
    reportDigitPair p (wide.apply u) sel = reportDigitPair p u sel := by
  have D := issue_write_banks p src old packet P W L sent forward
  have B : (t.payload/2^(2*d p))%2=1-sel := by
    rw [carried,kept]
    exact D.2.2.2.2
  have S : sel≤1 := by rw [kept]; unfold capturedSelector; omega
  rw [show effect p u v false hv 1 next win t =
      (⟨(BitVec.allOnes (2*d p)).setWidth (workW p) <<< offset p (1-sel),
         (BitVec.ofNat (2*d p) (t.payload%2^(2*d p))).setWidth (workW p) <<<
           offset p (1-sel)⟩,Patch.empty _,t) from by
      have E := write_digit_old p false hv u v command next win t O live op (.inl rfl)
      rw [B] at E
      exact E]
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  let j := offset p sel+i
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  change (_ : BitVec p.w).getLsbD j=u.getLsbD j
  apply Patch.hold
  have disj : j<offset p (1-sel) ∨ offset p (1-sel)+2*d p≤j := by
    have V : sel=0 ∨ sel=1 := by omega
    rcases V with rfl|rfl
    · right
      simp [j,offset,bankW]
      omega
    · left
      simp [j,offset,bankW]
      omega
  rcases disj with H|H
  · simp [BitVec.getLsbD_setWidth,BitVec.getLsbD_shiftLeft,show ¬offset p (1-sel)≤j by omega]
  · have Q : 2*d p≤j-offset p (1-sel) := by omega
    simp [BitVec.getLsbD_setWidth,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_of_ge _ _ Q]

end L4.ReportWriterPayload
