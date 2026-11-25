import Leader.L4.BStarLongLayout
import Std.Tactic.BVDecide

/-! Structural long token reads. Binding a token to an old physical
slot and validating opcode-specific live payload is the next phase.
Neither read nor a subsequent held-byte patch rewrites ignored padding. -/
namespace L4.BStarLongToken
open AllSizeProtocol BStarTrace BStarLongLayout

structure Payload where
  fault : BitVec 1
  opcode : BitVec 9
  race : BitVec 3
  outcome : BitVec 2
  argument : BitVec 34
  deriving DecidableEq, Repr

inductive Token
  | empty
  | trail
  | forward (p : Payload)
  | reply (p : Payload)
  deriving DecidableEq, Repr

def readPayload (x : BitVec 52) : Payload :=
  ⟨x.extractLsb' 49 1,x.extractLsb' 40 9,x.extractLsb' 37 3,
   x.extractLsb' 35 2,x.extractLsb' 0 34⟩

def decode (x : BitVec 52) : Token :=
  let tag := x.extractLsb' 50 2
  if tag=0 then .empty else if tag=1 then .trail
  else if tag=2 then .forward (readPayload x) else .reply (readPayload x)

def encodePayload (tag : BitVec 2) (p : Payload) : BitVec 52 :=
  (((((tag ++ p.fault) ++ p.opcode) ++ p.race) ++ p.outcome) ++ (0 : BitVec 1)) ++ p.argument

def encode : Token → BitVec 52
  | .empty => 0
  | .trail => (1 : BitVec 2) ++ (0 : BitVec 50)
  | .forward p => encodePayload 2 p
  | .reply p => encodePayload 3 p

theorem readPayload_encode (tag : BitVec 2) (p : Payload) :
    readPayload (encodePayload tag p)=p := by
  rcases p with ⟨f,o,r,s,a⟩
  simp only [readPayload,encodePayload,Payload.mk.injEq]
  constructor
  · bv_decide
  · constructor
    · bv_decide
    · constructor
      · bv_decide
      · constructor <;> bv_decide

theorem encode_tag (tag : BitVec 2) (p : Payload) :
    (encodePayload tag p).extractLsb' 50 2=tag := by
  rcases p with ⟨f,o,r,s,a⟩
  unfold encodePayload
  bv_decide

theorem encode_applied_zero (tag : BitVec 2) (p : Payload) :
    (encodePayload tag p).extractLsb' 34 1=0 := by
  rcases p with ⟨f,o,r,s,a⟩
  unfold encodePayload
  bv_decide

theorem decode_encode (t : Token) : decode (encode t)=t := by
  cases t with
  | empty => decide
  | trail => decide
  | forward p => simp [decode,encode,encode_tag,readPayload_encode]
  | reply p => simp [decode,encode,encode_tag,readPayload_encode]

def atSite (x : BitVec LW) (j : Fin 11) : Token := decode ((kField j).read x)
def setToken (j : Fin 11) (t : Token) : Patch LW := (kField j).assign (encode t)

theorem atSite_after (x : BitVec LW) (j : Fin 11) (t : Token) :
    atSite ((setToken j t).apply x) j=t := by
  unfold atSite setToken
  rw [Field.read_assign,decode_encode]

theorem other_token_raw_holds (x : BitVec LW) (i j : Fin 11) (h : i≠j) (t : Token) :
    (kField i).read ((setToken j t).apply x)=(kField i).read x := by
  have h' : Disjoint (kField i) (kField j) := by
    exact kPart_spacing i j h 0 52 0 52 (by decide) (by decide)
  exact Field.read_other_assign _ _ _ _ h'

theorem other_token_holds (x : BitVec LW) (i j : Fin 11) (h : i≠j) (t : Token) :
    atSite ((setToken j t).apply x) i=atSite x i := by
  simp only [atSite,other_token_raw_holds x i j h]

/-- Semantic equality for a padding-dirty old buffer need not mean there was
no setter. An E write still covers the whole local 52-bit slot. -/
theorem setToken_support (j : Fin 11) (t : Token) (i : Nat) :
    (setToken j t).mask.getLsbD i=true ↔ kBase j≤i ∧ i<kBase j+52 :=
  Field.inMask _ _ _

end L4.BStarLongToken
