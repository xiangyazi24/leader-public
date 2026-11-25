import Leader.L4.ShortEmptyOwnership
import Leader.L4.ShortControllerMIS1

namespace L4.ShortClearLaunch
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortResetForwardH2 ShortEmptyOwnership ShortControllerMIS1

def ClearIssue {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) (o : Nat) : Prop :=
  o<7 ∧ Clear C x ∧ get (x C.root).mis1 81 2 (by decide)=1 ∧
    get (x C.root).mis1 78 3 (by decide)=o

/-- Every canonical-clear valid ISSUE remains ready on nondoor marks.
No assumptions on adjacent owners' packets are needed. -/
theorem clear_issue_nondoor {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ q, header x q=h q) (o : Nat) (A : ClearIssue C x o)
    (e : Fin n) (neDoor : e≠RearTrace.predecessor C.root) :
    ClearIssue C (rawNext s x e) o := by
  have H : header x C.root=true := (heads _).trans C.rootHeader
  refine ⟨A.1,clear_nondoor C x heads e neDoor A.2.1,?_⟩
  by_cases D : e=C.root
  · subst e
    have F := reset_controller_outgoing_raw x C.root H
    exact ⟨F.1.trans A.2.2.1,F.2.trans A.2.2.2⟩
  · have R : C.root≠rightNeighbor e := by
      intro B
      apply neDoor
      rw [B,RearTrace.predecessor_right]
    rw [reset_remote_frame_raw _ _ _ (Ne.symm D) R]
    exact A.2.2

/-- The fresh source payload for every ordinary valid ISSUE, read only
from the literal old responder file. -/
def launchToken (o : Nat) (b : BitVec 96) : Token :=
  { tag := 2, opcode := o,
    payload := if o=3 then 64 else if 4≤o then issuedDescriptor b else 0 }

/-- The actual owner incoming mark turns a clean ISSUE into the
corresponding WAIT and installs exactly the fresh K0 packet.
No other owner slot is populated on this mark. -/
theorem clean_launch {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ q, header x q=h q) (o : Nat) (A : ClearIssue C x o) :
    let y := rawNext s x (RearTrace.predecessor C.root)
    get (y C.root).mis1 81 2 (by decide)=2 ∧
    get (y C.root).mis1 78 3 (by decide)=o ∧
    bits C.route y 0=encode (launchToken o (x C.root).mis1) ∧
    ∀ i, 0<i → i<C.L → bits C.route y i=encode E := by
  let d := RearTrace.predecessor C.root
  have L := C.length_lt
  have P := C.positive
  have R : rightNeighbor d=C.root := RearTrace.right_predecessor C.root
  have H : header x (rightNeighbor d)=true := by rw [R,heads,C.rootHeader]
  have F := issue_fresh_raw x d (edge_sep (by omega) d) H o
    (by simpa only [R] using A.2.2.1) (by simpa only [R] using A.2.2.2) A.1
  dsimp only at F
  rw [R] at F
  refine ⟨F.1,F.2.1,?_,fun i I J=>clear_door_except_root C x A.2.1 i J (by omega)⟩
  change (kField (ShortResetChart.lane C.a C.b 0)).read (rawNext s x d C.root).mis1=_
  rw [C.rootPort]
  exact F.2.2

#print axioms clear_issue_nondoor
#print axioms clean_launch
end L4.ShortClearLaunch
