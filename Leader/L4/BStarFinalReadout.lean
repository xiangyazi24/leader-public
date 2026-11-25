import Leader.L4.BStarAliasPaired
import Leader.L4.BStarStageIssuedHistory

namespace L4.BStarFinalReadout
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongClaims BStarLongWork BStarLongTransport BStarLongDoor
open BStarFinalCandidate BStarAliasPaired BStarLongCommand
open BStarLongEvents BStarCommitIssue BStarH6WordChart
set_option maxRecDepth 4096

private theorem stage_schedule_frame {m : Nat} (f : Field LW m)
    (lo : 1764≤f.offset) (hi : f.offset+m≤2195) (x : BitVec LW) :
    f.read ((schedule stageOp).apply x)=f.read x := by
  unfold schedule setToken
  simp only [Patch.compose_apply]
  rw [Field.read_other_assign f (kField 0) _ _ (.inr lo),
    Field.read_other_assign f ctrlOp _ _ (.inl hi),
    Field.read_other_assign f ctrlPhase _ _ (.inl (Nat.le_trans hi (by decide)))]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "A" => production k₁ k₂ t₂ J₁ J₂ r c p c₁

/-- A healthy final WAIT return installs both packed readout fields
through the *actual* simultaneous joined pair; no old scratch
value is substituted for the newly assigned candidate headers. -/
theorem joined_final_readout (x : Pair (LargeSite A)) (f : Payload)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2)
    (op : (ctrlOp.read x.2.long).toNat=lastOp)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=lastOp)
    (h : ((capturedSelector 1).read x.2.long).toNat<3) :
    need.read (largePair B x).2.long=BitVec.ofBool (finalChoice x.2.long) ∧
      candidateHeaders.read (largePair B x).2.long=finalHeaders x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have RR : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have S := BStarResetControllerEntry.wait_reply_selected g raw f hdr V ph R
  have E := S.2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at E
  have N : (f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=false := by
    change (f.fault != 0 || f.opcode.toNat != (ctrlOp.read x.2.long).toNat)=false
    simp [F,O,op]
  have ar : (arithKind (ctrlOp.read raw.2).toNat).isSome=true := by
    change (arithKind (ctrlOp.read x.2.long).toNat).isSome=true
    rw [op]
    decide
  have hh : ((capturedSelector 1).read raw.2).toNat<3 := h
  have E' : (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).work=
      [(true,finalEffect raw.2 hh)] := by
    rw [if_neg (show ¬(f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=true from fun k => by rw [N] at k; cases k),if_pos ar] at E
    rw [RR,E,show (ctrlOp.read raw.2).toNat=lastOp from op,final_receipt_exact raw.2 f hh]
  have project {m : Nat} (field : Field LW m) (hi : field.offset+m≤2195) :
      field.read (largePair B x).2.long=field.read (patchPair (longWork g raw) raw).2 := by
    change field.read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
    have VV : LongDoorGuard.valid manifest raw.2=true := V
    simp only [LongDoorGuard.guard,VV,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
      Patch.compose_apply]
    exact Field.read_other_assign field offField _ _ (.inl (Nat.le_trans hi (by decide)))
  constructor
  · rw [project need (by decide)]
    change need.read (patchPair (longWork g raw) raw).2=BitVec.ofBool (finalChoice raw.2)
    apply door_field need (by decide) (by decide) g raw hdr _ E'
      (fun _ => BitVec.ofBool (finalChoice raw.2))
    intro y
    simp only [finalEffect,Patch.compose_apply]
    rw [stage_schedule_frame need (by decide) (by decide),
        Field.read_other_assign need candidateHeaders _ _ (by decide),Field.read_assign]
  · rw [project candidateHeaders (by decide)]
    change candidateHeaders.read (patchPair (longWork g raw) raw).2=finalHeaders raw.2
    apply door_field candidateHeaders (by decide) (by decide) g raw hdr _ E'
      (fun _ => finalHeaders raw.2)
    intro y
    simp only [finalEffect,Patch.compose_apply]
    rw [stage_schedule_frame candidateHeaders (by decide) (by decide),Field.read_assign]

open BStarLongArithmetic BStarAliasFold
open L4.Compiler.Native L4.Compiler.Interp

/-- Exact accepted-code connection, with the old scalar operand wiring
and old file representation made explicit. In particular, index 473
uses the newly computed BMUX, not the previous value in its slot. -/
theorem final_headers_native {r : Nat} (T : PrimTable r) (bank : Bank)
    (x : BitVec LW) (regs : List Value) (L : regs.length=473)
    (Hq : OldBool x regs 137) (Ha : OldBool x regs 5) (Hb : OldBool x regs 472)
    (Old : ∀ j∈BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1,
      j<473 → OldBool x regs j) :
    let ys := runCodes T bank regs [.bmux 137 5 472]
    finalHeaders x = BitVec.ofNat 18 ((BStarLongSignatures.outHeaders0++
      BStarLongSignatures.outHeaders1).foldl
      (fun a j => a*2+((readReg ys j).asBool).toNat) 0) := by
  dsimp only
  obtain ⟨b,N,E⟩ := exact_boolean_head T bank x regs (.bmux 137 5 472) 0
    (HeadOK.mux 137 5 472 Hq Ha Hb)
  change finalHeaders x = BitVec.ofNat 18 ((BStarLongSignatures.outHeaders0++
    BStarLongSignatures.outHeaders1).foldl
    (fun a j => a*2+((readReg (regs++[evalInstr (toInstr T bank (.bmux 137 5 472)) regs]) j).asBool).toNat) 0)
  rw [E]
  have M : ∀ j∈BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1,
      j≤473 → newest x (finalValues x) j=
      ((readReg (regs++[Value.boolean b]) j).asBool).toNat := by
    intro j mem J
    unfold finalValues
    rw [N]
    by_cases Q : j=473
    · subst j
      have T : readReg (regs++[Value.boolean b]) 473=Value.boolean b := by
        rw [← L]
        simp [readReg]
      simp [T,newest,lastNode,Value.asBool]
    · have U : j<473 := by omega
      rw [readReg_append_left _ _ _ (by omega)]
      simpa [newest,lastNode,Ne.symm Q,OldBool] using Old j mem U
  have bound : ∀ j∈BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1, j≤473 := by
    have H : (BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).all
        (fun j => decide (j≤473))=true := by decide +kernel
    intro j h
    exact of_decide_eq_true (List.all_eq_true.mp H j h)
  unfold finalHeaders
  congr 1
  generalize (BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1)=is at *
  suffices ∀ k, is.foldl (fun a j => a*2+newest x (finalValues x) j) k =
      is.foldl (fun a j => a*2+((readReg (regs++[Value.boolean b]) j).asBool).toNat) k from this 0
  induction is with
  | nil => intro k; rfl
  | cons j js ih =>
    intro k
    simp only [List.foldl_cons]
    rw [M j List.mem_cons_self (bound j List.mem_cons_self)]
    exact ih (fun l h => Old l (List.mem_cons_of_mem _ h))
      (fun l h => M l (List.mem_cons_of_mem _ h))
      (fun l h => bound l (List.mem_cons_of_mem _ h)) _

theorem final_need_native {r : Nat} (T : PrimTable r) (bank : Bank)
    (x : BitVec LW) (regs : List Value) (L : regs.length=473)
    (Old : OldBool x regs BStarLongSignatures.needIx) :
    finalChoice x =
      (readReg (runCodes T bank regs [.bmux 137 5 472]) BStarLongSignatures.needIx).asBool := by
  change (source x BStarLongSignatures.needIx==1)=
    (readReg (regs++[evalInstr (toInstr T bank (.bmux 137 5 472)) regs])
      BStarLongSignatures.needIx).asBool
  rw [readReg_append_left _ _ _ (by rw [L]; decide)]
  rw [show source x BStarLongSignatures.needIx=(readReg regs BStarLongSignatures.needIx).asBool.toNat from Old]
  cases (readReg regs BStarLongSignatures.needIx).asBool <;> rfl

#print axioms final_need_native
#print axioms final_headers_native
#print axioms joined_final_readout
end L4.BStarFinalReadout
