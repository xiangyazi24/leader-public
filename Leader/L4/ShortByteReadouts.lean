import Leader.L4.AllSizeProtocol

/-! Constant readouts of the old selected bank and pulse bit. No
producer work row is supplied by this module. Field order follows
the scaled layout, serialized here in high-first numerical lanes. -/
namespace L4.ShortByteReadouts
open AllSizeProtocol

/-- MIS layout top: off[2], successorHeader[1], selector[1],
grants[3], bank0[1], bank1[1]. -/
def misSelector : Field 96 1 := ⟨92,by decide⟩
def misBank (selected : Bool) : Field 96 1 :=
  if selected then ⟨87,by decide⟩ else ⟨88,by decide⟩

def misSelected (x : BitVec 96) : Bool :=
  ((misBank ((misSelector.read x).getLsbD 0)).read x).getLsbD 0

/-- Report ends in Z, two pulse-race bits, then streak[ell J]. -/
def reportPulseField (β t J : Nat) : Field (reportWidth β t J) 1 :=
  ⟨ell J+2,by unfold reportWidth; omega⟩

def reportPulse (β t J : Nat) (x : BitVec (reportWidth β t J)) : Bool :=
  ((reportPulseField β t J).read x).getLsbD 0

def report1Pulse (a : LargeParams) : BitVec (reportWidth (a.k1+1) 1 a.J1) → Bool :=
  reportPulse (a.k1+1) 1 a.J1

def report2Pulse (a : LargeParams) : BitVec (reportWidth 2 a.t2 a.J2) → Bool :=
  reportPulse 2 a.t2 a.J2

theorem mis_switches_bank :
    misSelected (BitVec.ofNat 96 (2^88))=true ∧
    misSelected (BitVec.ofNat 96 (2^92+2^88))=false ∧
    misSelected (BitVec.ofNat 96 (2^92+2^87))=true := by decide

end L4.ShortByteReadouts
