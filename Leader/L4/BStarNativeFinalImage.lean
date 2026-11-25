import Leader.L4.BStarNativePackedRep
import Leader.L4.BStarFinalReadout
import Leader.L4.BStarStageIssuedHistory
import Leader.L4.BStarAliasPaired
import Leader.L4.BStarNumericWordFrame

namespace L4.BStarNativeFinalImage
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongDoor
open BStarLongClaims BStarLongCommand BStarLongRegisters BStarLongArithmetic BStarCommitIssue
open BStarNativePackedRep BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction
open BStarFinalCandidate BStarFinalReadout BStarGeneratedOwner BStarNativeReceiptTape
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart BStarResetChartTouch
open BStarAcquireForwardTrace BStarSeparatorControl BStarLongEvents BStarNumericChartCoverage
open BStarNativeZeroHead BStarStageIssuedHistory
open BStarResetChartService BStarPhysicalDigitSem BStarPhysicalWordSem
open L4.Compiler.Native L4.Compiler.Interp
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

set_option maxRecDepth 4096

private def boolCode : Code → Bool
  | .header _ _ | .bconst _ | .cmpEq _ | .cmpLt _ | .not _ | .and _ _
  | .or _ _ | .bmux _ _ _ | .phaseEq _ _ => true
  | _ => false

private def refs : List Nat :=
  137::5::472::BStarLongSignatures.needIx::
    ((BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).filter (·<473))

private theorem refs_checked : refs.all (fun j => decide (j<473) && ((get j).map boolCode).getD false)=true := by
  decide +kernel

private theorem bool_value {width : Nat} (T : PrimTable width) (bank : Bank)
    (regs : List Value) {c : Code} (isBool : boolCode c=true) :
    ∃ b, evalInstr (toInstr T bank c) regs=.boolean b := by
  cases c <;> first | exact ⟨_,rfl⟩ | cases isBool

private theorem typed_from_get {width : Nat} (T : PrimTable width) (bank : Bank)
    (program : List Code) (i : Nat) (c : Code) (found : program[i]?=some c)
    (Bcode : boolCode c=true) :
    ∃ b, readReg (runCodes T bank [] program) i=.boolean b := by
  obtain ⟨K,H⟩ := List.getElem?_eq_some_iff.mp found
  have ev := runCodes_new T bank [] program i K
  rw [H] at ev
  obtain ⟨b,Bb⟩ := bool_value T bank (runCodes T bank [] (program.take i)) Bcode
  exact ⟨b,by simpa only [List.length_nil,Nat.zero_add] using ev.trans Bb⟩

private theorem final_old_bool {width : Nat} (T : PrimTable width) (bank : Bank)
    (old : BitVec LW) (R : WellRep old [] (regsBefore T bank 394) literalCmp)
    (i : Nat) (M : i∈refs) : OldBool old (regsBefore T bank 394) i := by
  have E := List.all_eq_true.mp refs_checked i M
  have j : i<473 := of_decide_eq_true (Bool.and_eq_true_iff.mp E).1
  have L : start 394=473 := by decide +kernel
  have il : i<L4.Compiler.Native.literal.length := by rw [literal_length]; omega
  let c := L4.Compiler.Native.literal[i]'il
  have C : get i=some c := List.getElem?_eq_getElem il
  have bc : boolCode c=true := by
    have H := (Bool.and_eq_true_iff.mp E).2
    rw [C] at H
    exact H
  have P : (L4.Compiler.Native.literal.take (start 394))[i]?=some c := by
    rw [List.getElem?_take]
    exact if_pos (by omega) |>.trans C
  obtain ⟨b,doc⟩ := typed_from_get T bank _ i c P bc
  have len : i<(regsBefore T bank 394).length := by rw [prefix_length T bank (by decide),L]; exact j
  have d : readReg (regsBefore T bank 394) i=.boolean b := doc
  have src := (R i len).1 b d
  unfold OldBool
  rw [d]
  exact src

private theorem typed_readout {width : Nat} (T : PrimTable width) (bank : Bank)
    (old : BitVec LW) (R : WellRep old [] (regsBefore T bank 394) literalCmp) :
    let regs := regsBefore T bank 394
    let ys := runCodes T bank [] L4.Compiler.Native.literal
    ∃ b, nodeResult old 0 (.bmux 137 5 472)=some b.toNat ∧ ys=regs++[.boolean b] ∧
      finalChoice old=(readReg ys BStarLongSignatures.needIx).asBool ∧
      finalHeaders old=BitVec.ofNat 18 ((BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).foldl
        (fun a j => a*2+((readReg ys j).asBool).toNat) 0) := by
  dsimp only
  let regs := regsBefore T bank 394
  have L : regs.length=473 := (prefix_length T bank (by decide)).trans (by decide +kernel)
  have hq : OldBool old regs 137 := final_old_bool T bank old R _ (by decide)
  have ha : OldBool old regs 5 := final_old_bool T bank old R _ (by decide)
  have hb : OldBool old regs 472 := final_old_bool T bank old R _ (by decide)
  have hn : OldBool old regs BStarLongSignatures.needIx := final_old_bool T bank old R _ (by decide)
  have ho (j : Nat) (m : j∈BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1)
      (lt : j<473) : OldBool old regs j := by
    apply final_old_bool T bank old R
    unfold refs
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨m,decide_eq_true lt⟩))))
  obtain ⟨b,Hb,E⟩ := exact_boolean_head T bank old regs (.bmux 137 5 472) 0 (.mux 137 5 472 hq ha hb)
  have exactRun : runCodes T bank [] L4.Compiler.Native.literal=runCodes T bank regs [.bmux 137 5 472] := by
    rw [←prefix_final,show (395:Nat)=394+1 by decide,prefix_step T bank (by decide)]
    have C : chunk 394=[.bmux 137 5 472] := by decide +kernel
    rw [C]
  refine ⟨b,Hb,?_,?_,?_⟩
  · rw [exactRun]
    change regs++[evalInstr (toInstr T bank (.bmux 137 5 472)) regs]=_
    rw [E]
  · rw [exactRun]
    exact final_need_native T bank old regs L hn
  · rw [exactRun]
    exact final_headers_native T bank old regs L hq ha hb ho

/-- Each entry of the canonical significant-digit list has an actual
K1 address on the source chart. -/
theorem digit_on_chart (base : X) (addr : Nat → Pos n) (len width : Nat)
    (L : (significantSites hp base addr len).length=width) (u : Fin width) :
    ∃ j≤len,addr j=(digitSite hp base addr len width L u,1) := by
  have M : digitSite hp base addr len width L u∈significantSites hp base addr len := by
    unfold digitSite
    exact List.getElem_mem _
  unfold significantSites at M
  obtain ⟨j,J,K⟩ := List.mem_map.mp M
  obtain ⟨lt,sig⟩ := List.mem_filter.mp J
  have tag : (addr j).2.val=1 := by
    unfold significantIndex at sig
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp sig).1
  exact ⟨j,Nat.le_of_lt (List.mem_range.mp lt),Prod.ext K (Fin.ext tag)⟩

private theorem schedule_scalar (i : Nat) (x : BitVec LW) :
    (scalar i).read ((schedule stageOp).apply x)=(scalar i).read x := by
  have lo : 1764≤(scalar i).offset := by simp [scalar]
  have hi : (scalar i).offset+widthAt scalarWidths i≤2195 :=
    Nat.le_trans (scalar_before_choice i) (by decide)
  unfold schedule setToken
  simp only [Patch.compose_apply]
  rw [Field.read_other_assign (scalar i) (kField 0) _ _ (.inr lo),
    Field.read_other_assign (scalar i) ctrlOp _ _ (.inl hi),
    Field.read_other_assign (scalar i) ctrlPhase _ _ (.inl (Nat.le_trans hi (by decide)))]

private theorem joined_scalar (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (f : Payload) (b : Bool) (i : Nat)
    (hdr : (oldHeaders B x.2).h6=true) (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2) (op : (ctrlOp.read x.2.long).toNat=lastOp)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=lastOp)
    (h : ((capturedSelector 1).read x.2.long).toNat<3)
    (Hb : nodeResult x.2.long 0 (.bmux 137 5 472)=some b.toNat) :
    source (largePair B x).2.long i=newest x.2.long [(473,b.toNat)] i := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have RR : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have E := (BStarResetControllerEntry.wait_reply_selected g raw f hdr V ph R).2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at E
  have N : (f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=false := by
    change (f.fault != 0 || f.opcode.toNat != (ctrlOp.read x.2.long).toNat)=false
    simp [F,O,op]
  have ar : (arithKind (ctrlOp.read raw.2).toNat).isSome=true := by
    change (arithKind (ctrlOp.read x.2.long).toNat).isSome=true
    rw [op]
    decide
  have E' : (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).work=
      [(true,finalEffect raw.2 h)] := by
    rw [if_neg (show ¬(f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=true from fun k => by rw [N] at k; cases k),if_pos ar] at E
    rw [RR,E,show (ctrlOp.read raw.2).toNat=lastOp from op,final_receipt_exact raw.2 f h]
  have lo : 1764≤(scalar i).offset := by simp [scalar]
  have hi : (scalar i).offset+widthAt scalarWidths i≤2195 :=
    Nat.le_trans (scalar_before_choice i) (by decide)
  have project : (scalar i).read (largePair B x).2.long=(scalar i).read (patchPair (longWork g raw) raw).2 := by
    change (scalar i).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
    have VV : LongDoorGuard.valid manifest raw.2=true := V
    simp only [LongDoorGuard.guard,VV,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
      Patch.compose_apply]
    exact Field.read_other_assign (scalar i) offField _ _ (.inl (Nat.le_trans hi (by decide)))
  let k (z : BitVec (widthAt scalarWidths i)) := if i=473 then BitVec.ofNat _ b.toNat else z
  have patch (y : BitVec LW) : (scalar i).read ((finalEffect raw.2 h).apply y)=k ((scalar i).read y) := by
    have B' : nodeResult raw.2 0 (.bmux 137 5 472)=some b.toNat := Hb
    simp only [finalEffect,Patch.compose_apply]
    rw [schedule_scalar,
      Field.read_other_assign (scalar i) candidateHeaders _ _ (.inl (Nat.le_trans
        (scalar_before_choice i) (by decide))),
      Field.read_other_assign (scalar i) need _ _ (.inl (Nat.le_trans
        (scalar_before_choice i) (by decide))),
      Field.read_other_assign (scalar i) sourceDescriptor _ _ (.inl (Nat.le_trans
        (scalar_before_choice i) (by decide)))]
    simp only [finalValues,B',Option.toList_some,List.map_cons,List.map_nil,List.reverse_cons,
      List.reverse_nil,List.nil_append,BStarLongOutgoing.fuse,List.foldl_cons,List.foldl_nil,
      Patch.compose_apply,writeScalar,lastNode]
    have empty : (Patch.empty LW).apply y=y := by simp [Patch.apply,Patch.empty]
    rw [empty]
    by_cases same : i=473
    · subst i
      exact Field.read_assign _ _ _
    · rw [Field.read_other_assign _ _ _ _ (scalar_distinct _ _ same)]
      simp only [k,if_neg same]
  have J := BStarAliasPaired.door_field (scalar i) lo hi g raw hdr _ E' k patch
  unfold source
  rw [project,J]
  by_cases same : i=473
  · subst i
    have W : widthAt scalarWidths 473=1 := by decide +kernel
    simp only [k,if_true,newest,beq_self_eq_true,List.find?_cons_of_pos,Option.map_some,Option.getD_some,
      BitVec.toNat_ofNat,W]
    cases b <;> decide
  · simp [k,same,newest,Ne.symm same,source]
    rfl

private theorem packed_boolean (old fresh : BitVec LW) (regs : List Value) (b : Bool)
    (R : WellRep old [] regs literalCmp) (L : regs.length=473)
    (E : ∀ i, source fresh i=newest old [(473,b.toNat)] i) :
    WellRep fresh [] (regs++[.boolean b]) literalCmp := by
  have NC : ¬literalCmp 473 := by unfold literalCmp; decide +kernel
  have R' := extend_rep old [] regs literalCmp b R (L.symm ▸ NC)
  rw [L] at R'
  intro i hi
  obtain ⟨A,C⟩ := R' i hi
  have equiv : newest fresh [] i=newest old [(473,b.toNat)] i := E i
  exact ⟨fun q Q => equiv.trans (A q Q),fun H => by simpa only [CmpRep,equiv] using C H⟩

private theorem retained_word {base x : X} {addr : Nat → Pos n} {len : Nat}
    {e : Fin n} (sep : e≠rightNeighbor e)
    (hit : Hit hp base addr len x e 407)
    {width : Nat} (sites : Fin width→Fin n)
    (onChart : ∀ j, ∃ k≤len,addr k=(sites j,1))
    (j : Nat) (slot : WordSlot j) :
    wordAt x sites j slot=wordAt (step x e) sites j slot := by
  unfold wordAt
  apply congrArg L4.Compiler.Digits.val
  funext d
  apply Fin.ext
  change num (x (sites d)).long j=num (step x e (sites d)).long j
  obtain ⟨k,hk,atK⟩ := onChart d
  have M : ¬anyTag.F (atCursor x (sites d,1)) := by
    rw [←atK]
    exact BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 hit.1.2.1 k hk
  exact congrArg BitVec.toNat ((BStarNumericWordFrame.step_no_forward hp x e (sites d) j sep M).symm)

private theorem final_numeric {base x : X} {addr : Nat → Pos n} {len : Nat}
    {e : Fin n} (sep : e≠rightNeighbor e)
    (hit : Hit hp base addr len x e 407)
    {width : Nat} (sites : Fin width→Fin n)
    (onChart : ∀ j, ∃ k≤len,addr k=(sites j,1))
    (regs : List Value) (b : Bool)
    (P : PackedRep x (addr 0).1 sites 394 regs)
    (j : Nat) (J : j<395) (slot : WordSlot (start j)) :
    readReg (regs++[.boolean b]) (start j)=.word (wordAt (step x e) sites (start j) slot) := by
  have early : j<394 := by
    by_cases same : j=394
    · subst j
      exact False.elim ((by decide +kernel : widthAt wordWidths (start 394)≠4) slot)
    · omega
  have idx : start j<regs.length := by rw [P.length]; exact start_lt early (by decide)
  rw [readReg_append_left _ _ _ idx,P.numeric j early slot]
  exact congrArg Value.word (retained_word hp sep hit sites onChart (start j) slot)

private theorem desc_congr {a b : BitVec LW} (E : a=b)
    (A : ((capturedSelector 1).read a).toNat<3) (B₀ : ((capturedSelector 1).read b).toNat<3) :
    finalDesc a A=finalDesc b B₀ := by subst b; rfl

/-- The actual final consume appends the last typed Boolean without
overwriting a distributed word, then installs the STAGE source image. -/
theorem final_hit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {e : Fin n} (sep : e≠rightNeighbor e)
    (hit : Hit hp base (fun j=>S.getD j fall) len x e 407)
    {width : Nat} (sites : Fin width→Fin n)
    (onChart : ∀ j, ∃ k≤len,S.getD k fall=(sites j,1))
    (T : PrimTable width) (bank : Bank)
    (P : PackedRep x (S.getD 0 fall).1 sites 394 (regsBefore T bank 394))
    (h : ((capturedSelector 1).read (x (S.getD 0 fall).1).long).toNat<3) :
    let old := (x (S.getD 0 fall).1).long
    let fresh := (step x e (S.getD 0 fall).1).long
    let ys := runCodes T bank [] L4.Compiler.Native.literal
    PackedRep (step x e) (S.getD 0 fall).1 sites 395 ys ∧
    BStarResetControllerEntry.snapshot fresh=((.empty,1),BitVec.ofNat 9 stageOp) ∧
    need.read fresh=BitVec.ofBool (readReg ys BStarLongSignatures.needIx).asBool ∧
    candidateHeaders.read fresh=BitVec.ofNat 18 ((BStarLongSignatures.outHeaders0++
      BStarLongSignatures.outHeaders1).foldl (fun a j => a*2+((readReg ys j).asBool).toNat) 0) ∧
    sourceDescriptor.read fresh=BStarLongPublication.encode (finalDesc old h) ∧
    (finalDesc old h).need=(readReg ys BStarLongSignatures.needIx).asBool := by
  dsimp only
  let root := (S.getD 0 fall).1
  let old := (x root).long
  let new := (step x e root).long
  let ys := runCodes T bank [] L4.Compiler.Native.literal
  obtain ⟨b,Hb,ysEq,needEq,headers⟩ := typed_readout T bank old P.scalar
  have right : rightNeighbor e=root := by rw [hit.2.2.2.2.1]; exact RearTrace.right_predecessor _
  obtain ⟨f,R,F,O⟩ := hit.2.2.2.2.2
  have hdr : oldH6 B x root=true := (root_header hp chart hit.1.1.1).1
  have valid : LongDoorGuard.valid manifest old=true := hit.1.1.2.1
  have ph : (ctrlPhase.read old).toNat=2 := hit.1.1.2.2.1
  have op : (ctrlOp.read old).toNat=lastOp := hit.1.1.2.2.2
  have pairEq : step x e root=(largePair B (x e,x (rightNeighbor e))).2 := by
    rw [←right]
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true]
  have scalarEq : ∀ i, source new i=newest old [(473,b.toNat)] i := by
    intro i
    change source (step x e root).long i=_
    rw [pairEq]
    have U := joined_scalar hp (x e,x (rightNeighbor e)) f b i
      (right.symm ▸ hdr) (right.symm ▸ valid) (right.symm ▸ ph) (right.symm ▸ op)
      (right.symm ▸ R) F O (right.symm ▸ h) (right.symm ▸ Hb)
    exact U.trans (congrArg (fun z => newest (x z).long [(473,b.toNat)] i) right)
  have L : (regsBefore T bank 394).length=473 := P.length.trans (by decide +kernel)
  have ysEq' : ys=regsBefore T bank 394++[.boolean b] := ysEq
  have Q : PackedRep (step x e) root sites 395 ys := by
    refine ⟨?_,?_,?_⟩
    · unfold ys
      rw [←prefix_final]
      exact prefix_length T bank (by decide)
    · change WellRep new [] ys literalCmp
      rw [ysEq']
      exact packed_boolean old new _ b P.scalar L scalarEq
    · intro j J slot
      rw [ysEq']
      exact final_numeric hp sep hit sites onChart _ b P j J slot
  have head := final_arrival hp x e sep f (right.symm ▸ hdr)
    (right.symm ▸ valid) (right.symm ▸ ph) (right.symm ▸ op) (right.symm ▸ R) F O (right.symm ▸ h)
  have readout := joined_final_readout hp (x e,x (rightNeighbor e)) f (right.symm ▸ hdr)
    (right.symm ▸ valid) (right.symm ▸ ph) (right.symm ▸ op) (right.symm ▸ R) F O (right.symm ▸ h)
  have snap : BStarResetControllerEntry.snapshot new=((.empty,1),BitVec.ofNat 9 stageOp) :=
    (congrArg (fun z => BStarResetControllerEntry.snapshot (step x e z).long) right).symm.trans head.1
  have desc : sourceDescriptor.read new=BStarLongPublication.encode (finalDesc old h) := by
    refine (congrArg (fun z => sourceDescriptor.read (step x e z).long) right).symm.trans (head.2.1.trans ?_)
    exact congrArg BStarLongPublication.encode (desc_congr (congrArg (fun z => (x z).long) right) _ h)
  have readNeed : need.read new=BitVec.ofBool (finalChoice old) := by
    change need.read (step x e root).long=_
    rw [pairEq]
    exact readout.1.trans (congrArg (fun z => BitVec.ofBool (finalChoice (x z).long)) right)
  have readHeaders : candidateHeaders.read new=finalHeaders old := by
    change candidateHeaders.read (step x e root).long=_
    rw [pairEq]
    exact readout.2.trans (congrArg (fun z => finalHeaders (x z).long) right)
  exact ⟨Q,snap,readNeed.trans (congrArg BitVec.ofBool needEq),readHeaders.trans headers,desc,needEq⟩

#print axioms digit_on_chart
#print axioms final_hit
end L4.BStarNativeFinalImage
