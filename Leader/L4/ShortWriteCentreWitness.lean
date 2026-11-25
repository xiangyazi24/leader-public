import Leader.L4.ShortStageSealRowsRaw
import Leader.L4.ShortWritePacketCodec
import Leader.L4.ShortResetCycle

namespace L4.ShortWriteCentreWitness
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortWritePacketCodec ShortStageSealRowsRaw ShortResetCycle ShortResetForwardH2

inductive Cmd where
  | stage
  | seal

def Cmd.op : Cmd → Nat
  | .stage => 4
  | .seal => 5

def Cmd.accepts (cmd : Cmd) (b : BitVec 96) (d : Fin 8) : Bool :=
  stageSealOwner b d.val && (match cmd with
    | .stage => true
    | .seal => sealBankMatches b d.val)

def Cmd.effectField (cmd : Cmd) (d : Fin 8) : Field 96 (match cmd with
    | .stage => 1
    | .seal => 4) :=
  match cmd with
  | .stage => lane (88-(d.val/2)%2) 1 (by omega)
  | .seal => lane 83 4 (by decide)

def Cmd.effectBits (cmd : Cmd) (d : Fin 8) : BitVec (match cmd with
    | .stage => 1
    | .seal => 4) :=
  match cmd with
  | .stage => BitVec.ofNat 1 (d.val%2==1).toNat
  | .seal => BitVec.ofNat 4 (8+d.val)

def Cmd.packet (cmd : Cmd) (d : Fin 8) : Token := writeFwd cmd.op d false

def Cmd.ack (cmd : Cmd) : Token := writeAck cmd.op

theorem Cmd.decode_packet (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true) (gate : Bool) :
    decode gate (encode (cmd.packet d))=cmd.packet d := by
  cases cmd <;> exact decode_write_forward gate _ d false (by decide) (by decide) D

theorem Cmd.decode_ack (cmd : Cmd) (gate : Bool) :
    decode gate (encode cmd.ack)=cmd.ack := by
  cases cmd <;> exact decode_write_ack gate _ (by decide) (by decide)

/-- Receipt for the literal old pair on the actual sampled mark. It
retains the old writer+selector guard and, for SEAL, the matching bank,
plus the exact bank or seal write after the joined raw step. -/
structure CentreEffect {s n : Nat} (cmd : Cmd) (d : Fin 8) (x : Raw s n) (e : Fin n) : Prop where
  headerOld : header x e=true
  tokenOld : oldK true (x e).mis1 1=cmd.packet d
  guardOld : cmd.accepts (x e).mis1 d=true
  wrote : (cmd.effectField d).read (rawNext s x e e).mis1=cmd.effectBits d

theorem centre_raw_exact {s n : Nat} (cmd : Cmd) (d : Fin 8) (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x e=true) (k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) 1=some k)
    (old : oldK true (x e).mis1 1=cmd.packet d) :
    let y := rawNext s x e
    (kField 1).read (y e).mis1=encode T ∧
      (kField k).read (y (rightNeighbor e)).mis1=
        encode (if cmd.accepts (x e).mis1 d then cmd.packet d else faultToken 2) ∧
      (cmd.accepts (x e).mis1 d=true → CentreEffect cmd d x e) := by
  dsimp only
  cases cmd with
  | stage =>
    have S := stage_out x e sep head k dst _ old rfl rfl rfl
    refine ⟨S.1,?_,fun G=>?_⟩
    · cases G : stageSealOwner (x e).mis1 d.val <;>
        simpa [Cmd.accepts,Cmd.packet,writeFwd,G] using S.2
    · refine ⟨head,old,G,?_⟩
      let i : Fin 2 := ⟨(d.val/2)%2, Nat.mod_lt _ (by decide)⟩
      have B := stage_bank x e head (Cmd.stage.packet d) i old rfl rfl rfl
      have H : stageSealOwner (x e).mis1 d.val=true := by simpa only [Cmd.accepts,Bool.and_true] using G
      change (Cmd.stage.effectField d).read (rawNext s x e e).mis1=_
      simpa only [Cmd.effectField,Cmd.effectBits,Cmd.packet,writeFwd,i,H,
        beq_self_eq_true,Bool.true_and,if_true] using B
  | «seal» =>
    have S := seal_out x e sep head k dst _ old rfl rfl rfl
    refine ⟨S.1,S.2,fun G=>⟨head,old,G,?_⟩⟩
    have B := seal_value x e head (Cmd.seal.packet d) old rfl rfl rfl
    change (stageSealOwner (x e).mis1 d.val && sealBankMatches (x e).mis1 d.val)=true at G
    simpa only [Cmd.effectField,Cmd.effectBits,Cmd.packet,writeFwd,G,if_true] using B

/-- A positive forwarded centre packet cannot be the canonical fault
even if the ACK consumer is not yet reached. -/
theorem centre_wire_live_is_effect {s n : Nat} (cmd : Cmd) (d : Fin 8) (x : Raw s n)
    (e : Fin n) (sep : e≠rightNeighbor e) (head : header x e=true) (k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) 1=some k)
    (D : descValid d.val=true) (old : oldK true (x e).mis1 1=cmd.packet d)
    (wire : (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode (cmd.packet d)) :
    CentreEffect cmd d x e := by
  have Q := centre_raw_exact cmd d x e sep head k dst old
  by_cases H : cmd.accepts (x e).mis1 d=true
  · exact Q.2.2 H
  · have C := Q.2.1
    rw [if_neg H,wire] at C
    have F := congrArg (decode false) C
    rw [Cmd.decode_packet cmd d D false,(decode_write_faults false).1] at F
    have G := congrArg Token.fault F
    contradiction

/-- The receipt exposes the position of the centre mark on the
original (not filtered or resampled) tape and its exact old pair. -/
def SampledEffect {s n : Nat} (cmd : Cmd) (d : Fin 8) (x : Raw s n) (e : Fin n)
    (tape : List (Fin n)) : Prop :=
  ∃ lead tail : List (Fin n), tape=lead++e::tail ∧ CentreEffect cmd d (rawRun x lead) e

theorem sampled_effect_extend {s n : Nat} (cmd : Cmd) (d : Fin 8) (x : Raw s n) (e : Fin n)
    (tape suffix : List (Fin n)) (P : SampledEffect cmd d x e tape) :
    SampledEffect cmd d x e (tape++suffix) := by
  obtain ⟨lead,tail,T,E⟩ := P
  exact ⟨lead,tail++suffix,by rw [T,List.append_assoc]; rfl,E⟩

theorem sampled_effect_record {s n : Nat} (cmd : Cmd) (d : Fin 8) (x : Raw s n) (e : Fin n)
    (marks : List (Fin n)) (P : CentreEffect cmd d (rawRun x marks) e) :
    SampledEffect cmd d x e (marks++[e]) :=
  ⟨marks,[],rfl,P⟩

end L4.ShortWriteCentreWitness
