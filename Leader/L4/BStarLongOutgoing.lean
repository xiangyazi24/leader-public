import Leader.L4.BStarLongDoor
import Leader.L4.BStarLongFieldBridge

/-! Physical STAGE/SEAL/COMMIT/RCLEAR departures, read only from the old
endpoint. The row produces a named write even when the old field
already has its specified value. -/
namespace L4.BStarLongOutgoing
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongCommand BStarLongToken
open BStarLongPublication
open BStarLongSignatures

def actual (x : BitVec LW) (d : Descriptor) : Bool :=
  ((grant 1).read x).getLsbD 0 && readSel x==d.old

def descriptorClear : Patch LW := (stage.assign 0).compose (sealField.assign 0)

structure Effect where
  row : Patch LW
  carried : Token
  published : Option (Fin 3)

def hold (p : Payload) : Effect := ⟨.empty _,.forward p,none⟩
def refuse : Effect := ⟨.empty _,fault false,none⟩

def outIndex (b : Bool) (f : Fin 9) : Nat :=
  (if b then outDigits1 else outDigits0).getD f.val 0

def readDigit (x : BitVec LW) (b : Bool) (f : Fin 9) : BitVec 4 :=
  BitVec.ofNat 4 (((BStarLongRegisters.numeric (outIndex b f)).read x).toNat)

def dimDigits (x : BitVec LW) (b : Bool) (i : Fin 3) : List (Patch LW) :=
  (List.finRange 9).map fun f => (bankDigit i f).assign (readDigit x b f)

def dimHeaders (n : Nat) (b : Bool) (i : Fin 3) : List (Patch LW) :=
  (List.finRange 9).map fun f =>
    (bankHeader i f).assign (BitVec.ofNat 1 (n / 2^(9*(if b then 0 else 1)+(8-f.val))))

def fuse (qs : List (Patch LW)) : Patch LW :=
  qs.foldl Patch.compose (.empty _)

def stagePatch (head inside : Bool) (x : BitVec LW) (d : Descriptor) (n : Nat) : Patch LW :=
  let ds := if inside then dimDigits x false d.b0 ++ dimDigits x true d.b1 else []
  let hs := if head then dimHeaders n false d.b0 ++ dimHeaders n true d.b1 ++
      [stage.assign (packOptional (some d))] else []
  fuse (ds++hs)

/-- This local handler is called after the old forward's gate and
prep cancellation decisions. A malformed or refused operand faults
without changing bank, selector, header, stage, or seal. -/
def execute (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) : Effect :=
  let op := p.opcode.toNat
  let n := p.argument.toNat
  let head := g.axes.h6
  if j.val != 1 || p.fault != 0 then hold p
  else if op==1 && head then ⟨descriptorClear,.forward p,none⟩
  else if op==stageOp then
    match BStarLongPublication.decode (BitVec.ofNat 7 (n/2^18)) with
    | none => refuse
    | some d =>
      if head && !actual x d then refuse
      else ⟨stagePatch head g.inside x d n,.forward p,none⟩
  else if op==sealOp && head then
    match BStarLongPublication.decode (BitVec.ofNat 7 (n/2)) with
    | none => refuse
    | some d =>
      if actual x d && readOptional (stage.read x)==some d then
        ⟨sealField.assign (packOptional (some d)),
          .forward {p with argument:=BitVec.ofNat 34 (2*(n/2)+d.need.toNat)},none⟩
      else refuse
  else if op==commitOp && head then
    match BStarLongPublication.decode (BitVec.ofNat 7 (n/4)) with
    | none => refuse
    | some d =>
      if h : n%4<3 then
        let b : Fin 3 := ⟨n%4,h⟩
        let q := commit head j x d b
        if q.2.isSome then ⟨q.1,.forward p,q.2⟩ else refuse
      else refuse
  else hold p

theorem noncenter_hold (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (h : j.val ≠ 1) : execute g j x p=hold p := by
  simp [execute,h]

theorem faulty_hold (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (h : p.fault≠0) : execute g j x p=hold p := by
  have hn : (p.fault != 0)=true := bne_iff_ne.mpr h
  simp only [execute,hn,Bool.or_true,if_true]

theorem stage_rejection (g : LongGeometry) (x : BitVec LW) (p : Payload) (d : Descriptor)
    (h : p.opcode.toNat=stageOp) (hh : g.axes.h6=true)
    (hd : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d)
    (hf : p.fault=0) (ha : actual x d=false) :
    execute g 1 x p=refuse := by
  simp [execute,h,hh,hd,hf,ha,stageOp]

theorem center_commit (g : LongGeometry) (x : BitVec LW) (p : Payload) (d : Descriptor)
    (b : Fin 3) (hh : g.axes.h6=true) (hf : p.fault=0)
    (hop : p.opcode.toNat=commitOp)
    (hd : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d)
    (hb : p.argument.toNat%4=b.val)
    (hc : guard true 1 x d b=true) :
    execute g 1 x p=⟨setter b,.forward p,some b⟩ := by
  simp [execute,hh,hf,hop,hd,hb,b.isLt,stageOp,commitOp,sealOp,commit,hc]

/-- Every reported local publication comes from that old occurrence's
physical COMMIT guard, including an inherited command. -/
theorem event_sound (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (b : Fin 3) (H : (execute g j x p).published=some b) :
    j.val=1 ∧ g.axes.h6=true ∧ p.fault=0 ∧ p.opcode.toNat=commitOp ∧
      ∃ d, BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
        p.argument.toNat%4=b.val ∧ guard true j x d b=true := by
  by_cases hj : j.val=1
  case neg =>
    rw [noncenter_hold _ _ _ _ hj] at H
    contradiction
  by_cases hf : p.fault=0
  case neg =>
    rw [faulty_hold _ _ _ _ hf] at H
    contradiction
  have H' := H
  have h0 : ((j.val != 1) || (p.fault != 0))=false := by simp [hj,hf]
  simp only [execute,h0,Bool.false_eq_true,if_false] at H' 
  split at H'
  · contradiction
  split at H'
  · split at H'
    all_goals
      first | contradiction | (split at H' <;> contradiction)
  split at H'
  · split at H'
    all_goals
      first | contradiction | (split at H' <;> contradiction)
  split at H'
  · rename_i E
    have ⟨ho,hh⟩ := Bool.and_eq_true_iff.mp E
    have he := beq_iff_eq.mp ho
    split at H'
    · contradiction
    rename_i d hd
    split at H'
    · rename_i hchoice
      let z : Fin 3 := ⟨p.argument.toNat%4,hchoice⟩
      by_cases hg : guard true j x d z=true
      · have hz : z=b := by simpa [commit,hh,hg,z,show guard g.axes.h6 j x d z=true by rw [hh]; exact hg] using H'
        refine ⟨hj,hh,hf,he,d,hd,?_,?_⟩
        · exact congrArg Fin.val hz
        · simpa [hz] using hg
      · simp [commit,hh,hg,z,refuse] at H'
    · contradiction
  · contradiction

set_option maxRecDepth 4096 in
theorem all_out_digit_slots :
    (outDigits0++outDigits1).all (fun i => BStarLongRegisters.widthAt BStarLongRegisters.wordWidths i==4)=true := by decide

end L4.BStarLongOutgoing
