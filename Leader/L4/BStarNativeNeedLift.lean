import Leader.L4.BStarNativeLogicalTrace

namespace L4.BStarNativeNeedLift
open L4.Compiler.Native
open BStarNativePortGeometry BStarH6WordChart BStarAcquireAnchors

/-- Bias and wrap for a chosen lifted natural counter within the
legitimate upper half. A residue alone does not determine the lift. -/
def liftResidue (P count : Nat) : Nat := P+count%P

def Represents (P : Nat) (x : NativeRecord) (count : Nat) : Prop :=
  x.err=false ∧ x.tick=liftResidue P count

theorem successor_lift (M P count : Nat) (twice : M=2*P) (positive : 0<P) :
    successor M (liftResidue P count)=liftResidue P (count+1) := by
  subst M
  let b := count%P
  have B : b<P := Nat.mod_lt _ positive
  have step : (count+1)%P=(b+1)%P := by
    rw [Nat.add_mod count 1 P,Nat.add_mod b 1 P]
    simp [b]
  unfold successor liftResidue
  change (if P+b=2*P-1 then 2*P/2 else P+b+1)=P+(count+1)%P
  rw [step]
  split
  · rename_i H
    have E : b+1=P := by omega
    rw [E,Nat.mod_self]
    omega
  · rename_i H
    rw [Nat.mod_eq_of_lt (show b+1<P by omega),Nat.add_assoc]

/-- Opcode eligibility at the native interface is strictly stronger
than merely publishing or incrementing. It names the actual old row. -/
theorem need_iff (M : Nat) (left center right : NativeRecord) :
    pendingNeed (nativeClock M left center right) center=true ↔
      nativeClock M left center right=.inc (successor M center.tick) ∧
      center.tick%32=1 ∧ center.curr.anchor=true ∧ center.curr.z=0 := by
  have unique (t : Nat) (E : nativeClock M left center right=.inc t) : t=successor M center.tick := by
    unfold nativeClock at E
    dsimp only at E
    repeat' split at E
    all_goals first | cases E; rfl | contradiction
  generalize E : nativeClock M left center right=a
  cases a <;> simp [pendingNeed,and_assoc]
  rename_i t
  rw [unique t E]
  simp

theorem self_port {n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true) (center : Header h) :
    neighborHeader hh center 1=center := by
  apply header_word_injective
  change word h (neighborHeader hh center 1).val=word h center.val
  rw [neighborHeader_word]
  change (word h center.val + 1 - 1) % (total h : Int)=word h center.val
  rw [Int.add_sub_cancel,Int.emod_eq_of_lt (word_range h center.val hh).1 (word_range h center.val hh).2]

/-- Replay exactly one atomically decoded eligible publication. The
counter chosen by the replay increments once, including at wrap; all
other owners keep their exact decoded records and represented lifts. -/
theorem tagged_native_increment {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (before after : Header h→NativeRecord) (center : Header h) (bank : Bank) (delta : Bool)
    (ports : ∀ q,decodeBank r bank q=before (neighborHeader hh center q))
    (need : (nativeSpec r bank).1=true)
    (write : after=activate (r:=r) hh before center delta)
    (P : Nat) (M : modulus r=2*P) (positive : 0<P)
    (count : Header h→Nat) (init : ∀ i, Represents P (before i) (count i)) :
    (∀ i, Represents P (after i) (if i=center then count i+1 else count i)) ∧
      (∀ i,i≠center→after i=before i) ∧
      (before center).tick%32=1 ∧ (before center).curr.anchor=true ∧ (before center).curr.z=0 := by
  let l := before (neighborHeader hh center 0)
  let c := before center
  let z := before (neighborHeader hh center 2)
  have self : neighborHeader hh center 1=center := by
    exact self_port hh center
  have N : pendingNeed (nativeClock (modulus r) l c z) c=true := by
    change pendingNeed (nativeClock (modulus r) (decodeBank r bank 0) (decodeBank r bank 1)
      (decodeBank r bank 2)) (decodeBank r bank 1)=true at need
    rwa [ports 0,ports 1,ports 2,self] at need
  obtain ⟨inc,phase,anchor,zero⟩ := (need_iff _ _ _ _).mp N
  have frame (i : Header h) (off : i≠center) : after i=before i := by
    rw [write]
    exact if_neg off
  refine ⟨?_,frame,phase,anchor,zero⟩
  intro i
  by_cases eq : i=center
  · subst i
    rw [if_pos rfl,write]
    unfold activate
    rw [if_pos rfl,self]
    change Represents P (finishNative (heightMod r) l (before center) z
      (nativeClock (modulus r) l (before center) z) delta) (count center+1)
    change nativeClock (modulus r) l (before center) z=.inc (successor (modulus r) (before center).tick) at inc
    rw [inc]
    exact ⟨rfl,by
      change successor (modulus r) (before center).tick=liftResidue P (count center+1)
      rw [(init center).2]
      exact successor_lift _ _ _ M positive⟩
  · rw [if_neg eq,frame i eq]
    exact init i

/-- A silent physical mark or another owner's publication stutters at
the considered owner's lifted coordinate. -/
theorem owner_lift_frame {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (before after : Header h→NativeRecord) (owner : Header h) (P count : Nat)
    (init : Represents P (before owner) count)
    (step : after=before ∨ ∃ center delta, owner≠center ∧
      after=activate (r:=r) hh before center delta) :
    Represents P (after owner) count := by
  rcases step with E|⟨center,delta,N,E⟩
  · rwa [E]
  · rw [E]
    change Represents P (if owner=center then _ else before owner) count
    rwa [if_neg N]

#print axioms self_port
#print axioms tagged_native_increment
#print axioms owner_lift_frame
end L4.BStarNativeNeedLift
