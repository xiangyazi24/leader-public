import Leader.L4.BStarLongLayout
import Std.Tactic.BVDecide

/-! Local COMMIT selector/descriptor row. This gives the literal
output when an already selected, validated forward front departs the
centre occurrence. Command arbitration and source provenance are separate. -/
namespace L4.BStarLongPublication
open AllSizeProtocol BStarTrace BStarLongLayout

structure Descriptor where
  old : Fin 3
  b0 : Fin 3
  b1 : Fin 3
  need : Bool
  deriving DecidableEq, Repr

def Descriptor.valid (d : Descriptor) : Bool :=
  d.b0.val == (d.old.val+1)%3 && d.b1.val == (d.old.val+2)%3

def encode (d : Descriptor) : BitVec 7 :=
  (((BitVec.ofNat 2 d.old.val ++ BitVec.ofNat 2 d.b0.val) ++
      BitVec.ofNat 2 d.b1.val) ++ BitVec.ofBool d.need)

def decode (x : BitVec 7) : Option Descriptor :=
  let a := (x.extractLsb' 5 2).toNat
  let b := (x.extractLsb' 3 2).toNat
  let c := (x.extractLsb' 1 2).toNat
  if ha : a<3 then if hb : b<3 then if hc : c<3 then
    let d : Descriptor := ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,x.getLsbD 0⟩
    if d.valid then some d else none
  else none else none else none

def readOptional (x : BitVec 8) : Option Descriptor :=
  if x.getLsbD 7 then decode (x.extractLsb' 0 7) else none

def packOptional : Option Descriptor → BitVec 8
  | none => 0
  | some d => (1 : BitVec 1) ++ encode d

def readSel (x : BitVec LW) : Fin 3 :=
  let i := (selector.read x).toNat
  if h : i<3 then ⟨i,h⟩ else 0

def typedGuard (header centre writer : Bool) (oldSel : Fin 3)
    (oldStage oldSeal : Option Descriptor) (d : Descriptor) (b : Fin 3) : Bool :=
  header && centre && writer && d.valid && oldSel==d.old &&
    oldStage==some d && oldSeal==some d && (b==d.b0 || (d.need && b==d.b1))

def guard (header : Bool) (occ : Fin 11) (x : BitVec LW)
    (d : Descriptor) (b : Fin 3) : Bool :=
  typedGuard header (occ==1) (((grant 1).read x).getLsbD 0) (readSel x)
    (readOptional (stage.read x)) (readOptional (sealField.read x)) d b

def setter (b : Fin 3) : Patch LW :=
  ((selector.assign (BitVec.ofNat 2 b.val)).compose (stage.assign 0)).compose (sealField.assign 0)

def commit (header : Bool) (occ : Fin 11) (x : BitVec LW)
    (d : Descriptor) (b : Fin 3) : Patch LW × Option (Fin 3) :=
  if guard header occ x d b then (setter b,some b) else (.empty _,none)

theorem commit_event (header : Bool) (occ : Fin 11) (x : BitVec LW)
    (d : Descriptor) (b : Fin 3) :
    (commit header occ x d b).2=some b ↔ guard header occ x d b=true := by
  cases h : guard header occ x d b <;> simp [commit,h]

theorem setter_values (x : BitVec LW) (b : Fin 3) :
    let y := (setter b).apply x
    selector.read y=BitVec.ofNat 2 b.val ∧ stage.read y=0 ∧ sealField.read y=0 := by
  simp only [setter,Patch.compose_apply]
  refine ⟨?_,?_,?_⟩
  · rw [Field.read_other_assign selector sealField _ _ (by decide),
      Field.read_other_assign selector stage _ _ (by decide),Field.read_assign]
  · rw [Field.read_other_assign stage sealField _ _ (by decide),Field.read_assign]
  · exact Field.read_assign sealField _ _

theorem commit_assignment (header : Bool) (occ : Fin 11) (x : BitVec LW)
    (d : Descriptor) (b : Fin 3) (evt : (commit header occ x d b).2=some b) :
    let y := (commit header occ x d b).1.apply x
    selector.read y=BitVec.ofNat 2 b.val ∧ stage.read y=0 ∧ sealField.read y=0 := by
  have h := (commit_event header occ x d b).mp evt
  unfold commit
  rw [if_pos h]
  exact setter_values x b

theorem setter_support (b : Fin 3) (i : Nat) :
    (setter b).mask.getLsbD i=true ↔ (2206≤i ∧ i<2222) ∨ (2360≤i ∧ i<2362) := by
  simp only [setter,Patch.compose,BitVec.getLsbD_or,Bool.or_eq_true,Field.inMask,selector,stage,sealField]
  omega

/-- An observed COMMIT always represents the actual conditional setter.
An inherited valid COMMIT is not excluded by an issue/provenance hypothesis. -/
theorem commit_support (header : Bool) (occ : Fin 11) (x : BitVec LW)
    (d : Descriptor) (b : Fin 3) (i : Nat) :
    (commit header occ x d b).1.mask.getLsbD i=true ↔
      (commit header occ x d b).2=some b ∧ ((2206≤i ∧ i<2222) ∨ (2360≤i ∧ i<2362)) := by
  cases h : guard header occ x d b <;> simp [commit,h,setter_support,Patch.empty]

end L4.BStarLongPublication
