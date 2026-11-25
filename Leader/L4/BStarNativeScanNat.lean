import Leader.L4.BStarScalarFlightTrace
import Leader.L4.BStarAliasPaired
import Leader.L4.BStarNativePackedRep

namespace L4.BStarNativeScanNat
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarGeneratedBandScan BStarScalarHistory
open BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart
open BStarLongFixedRouting BStarResetChartTouch BStarOwnerControlHistory
open BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl
open BStarLiteralPC BStarArithmeticControllerReturn BStarJoinedControllerReturn

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "PROTO" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step PROTO
local notation "run" => BStarResetSchedule.run step

open BStarScalarFlightTrace BStarNativeReceiptTape BStarScalarFits
open BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction
open BStarLongArithmetic L4.Compiler.Native L4.Compiler.Interp
open BStarPhysicalDigitSem

open BStarNativeScalarRecurrence BStarNativeOperandCustody
open BStarNativeZeroHead BStarNumericChartCoverage

open BStarLongRegisters

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def ScanNatRep (old : BitVec LW) (regs : List Value) : Prop :=
  ∀ i<regs.length, ∀ a, get i=some (.scan5 a) → source old i=(readReg regs i).asWord

def HasBool (regs : List Value) (i : Nat) : Prop := ∃ b, readReg regs i=.boolean b

inductive SourceTypes (regs : List Value) : Code → Prop
  | neg (a : Nat) : HasBool regs a → SourceTypes regs (.not a)
  | and (a b : Nat) : HasBool regs a → HasBool regs b → SourceTypes regs (.and a b)
  | or (a b : Nat) : HasBool regs a → HasBool regs b → SourceTypes regs (.or a b)
  | mux (q a b : Nat) : HasBool regs q → HasBool regs a → HasBool regs b → SourceTypes regs (.bmux q a b)
  | phase (a j q : Nat) : a<regs.length → get a=some (.scan5 q) → SourceTypes regs (.phaseEq a j)

private theorem bool_bound {regs : List Value} {i : Nat} (h : HasBool regs i) : i<regs.length := by
  obtain ⟨b,R⟩ := h
  by_cases B : i<regs.length
  · exact B
  unfold readReg at R
  rw [List.getElem?_eq_none (by omega)] at R
  cases R

theorem source_head_of_rep {old : BitVec LW} {regs : List Value} {c : Code}
    (R : WellRep old [] regs literalCmp) (N : ScanNatRep old regs) (T : SourceTypes regs c) :
    HeadOK old regs c := by
  have O (i : Nat) (B : HasBool regs i) : OldBool old regs i := by
    have bound := bool_bound B
    obtain ⟨b,E⟩ := B
    have H := (R i bound).1 b E
    unfold OldBool
    rw [E]
    exact H
  cases T with
  | neg a A => exact .neg a (O a A)
  | and a b A B => exact .and a b (O a A) (O b B)
  | or a b A B => exact .or a b (O a A) (O b B)
  | mux q a b Q A B => exact .mux q a b (O q Q) (O a A) (O b B)
  | phase a j q A E => exact .phase a j (N a A q E)

private theorem find_alias_early (old : BitVec LW) (cs : List Code) (i j : Nat)
    (early : i<j) (xs : Pending) :
    (aliases old j cs xs).find? (fun x => x.1==i)=xs.find? (fun x => x.1==i) := by
  induction cs generalizing j xs with
  | nil => rfl
  | cons c cs ih =>
    unfold aliases
    split
    · rfl
    · rw [ih (j+1) (by omega)]
      simp [show j≠i by omega]

private theorem scan_not_in_aliases (cs : List Code) (a : Nat) :
    .scan5 a ∉ cs.takeWhile (fun c => !BStarCmpReceipt.physical c) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    intro mem
    by_cases H : (!BStarCmpReceipt.physical c)=true
    · rw [List.takeWhile_cons,if_pos H,List.mem_cons] at mem
      rcases mem with eq|tail
      · subst c
        simp [BStarCmpReceipt.physical] at H
      · exact ih tail
    · rw [List.takeWhile_cons,if_neg H] at mem
      exact List.not_mem_nil mem

private theorem kind_exists {k : Nat} (K : k<395) : (arithKind (13+k)).isSome=true := by
  have L : k<BStarLongSignatures.arithmetic.length := by rw [signature_pins.1]; omega
  simp [arithKind,show ¬13+k<13 by omega,L]

theorem actual_scanNat_step {base x : X} {hh : ∃ i,oldH6 PROTO base i=true}
    {o : Owners (oldH6 PROTO base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i,Layout PROTO base i=Layout PROTO x i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {e : Fin n} {k : Nat}
    (K : k<394) (c' : Code) (G : get (start k)=some c')
    (hit : Hit hp base (fun j => S.getD j fall) len x e (13+k))
    {pre : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len (step x e) .idle pre
      (.busy (13+k+1) (.back 0)))
    (flat : Flat hp (step x e) (S.getD 0 fall).1 pre)
    (nextSame : ∀ u, ∀ i, Layout PROTO base i=Layout PROTO (run (step x e) u) i)
    (f : Payload)
    (found : bind (longGeometry PROTO (x (S.getD 0 fall).1)) 0
      (atSite (x (S.getD 0 fall).1).long 0)=.reply f)
    {width : Nat} (table : PrimTable width) (bank : Bank)
    (regs : List Value) (L : regs.length=start k)
    (oldRep : ScanNatRep (x (S.getD 0 fall).1).long regs)
    (scanResult : ∀ a, c'=.scan5 a → f.argument.toNat<32 ∧
      (evalInstr (toInstr table bank c') regs).asWord=f.argument.toNat) :
    ScanNatRep (run (step x e) pre (S.getD 0 fall).1).long
      (runCodes table bank regs (chunk k)) := by
  let r0 := (S.getD 0 fall).1
  obtain ⟨cur,_,opc,npc,own,factual,R,F,O⟩ := hit
  have fEq : factual=f := Token.reply.inj (R.symm.trans found)
  subst factual
  change e=RearTrace.predecessor r0 at own
  have eq : rightNeighbor e=r0 := own ▸ RearTrace.right_predecessor _
  have HH := (root_header hp C same).1
  have HN : pc (step x e) r0=13+k+1 := npc
  have hb₁ : 13≤pc (step x e) (S.getD 0 fall).1 := by change 13≤pc (step x e) r0; omega
  have hb₂ : pc (step x e) (S.getD 0 fall).1≤408 := by change pc (step x e) r0≤408; omega
  have flights := flat_flight hp C nextSame sep T flat hb₁ hb₂
  have vv := cur.1.2.1
  have ph := cur.1.2.2.1
  have K' : k<395 := by omega
  have bounds := BStarNativeReceiptInduction.bounds K'
  have val_early (i : Nat) (B : i≤start k) :
      source (run (step x e) pre r0).long i =
      (match (headPending (x r0).long k f c').find? (fun a : Nat × Nat => a.1==i) with
      | none => (scalar i).read (x r0).long
      | some a => BitVec.ofNat _ a.2).toNat := by
    rw [word_scalar_hold hp (step x e) r0 pre sep flights]
    let pair := (x e,x (rightNeighbor e))
    have pp : step x e r0=(largePair PROTO pair).2 := by
      rw [←eq]
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm (sep e)),if_true,pair]
    rw [pp]
    have E := BStarAliasPaired.joined_accept_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair f (13+k)
      (start k) i c' (scheduled_node K') G (by omega) (kind_exists K')
    have eHead : (oldHeaders PROTO pair.2).h6=true := by
      change oldH6 PROTO x (rightNeighbor e)=true
      rw [eq]
      exact HH
    have vv' : LongDoorGuard.valid manifest pair.2.long=true := by
      dsimp only [pair]
      rw [eq]
      exact vv
    have ph' : (ctrlPhase.read pair.2.long).toNat=2 := by
      dsimp only [pair]
      rw [eq]
      exact ph
    have op' : (ctrlOp.read pair.2.long).toNat=13+k := by
      dsimp only [pair]
      rw [eq]
      exact opc
    have rr : bind (longGeometry PROTO pair.2) 0 (atSite pair.2.long 0)=.reply f := by
      dsimp only [pair]
      rw [eq]
      exact R
    have read := E eHead vv' ph' op' rr F O
    unfold source
    rw [read]
    have early := find_alias_early pair.2.long (literal.drop (start k+1)) i (start k+1)
      (by omega) (headPending pair.2.long k f c')
    change (match (aliases pair.2.long (start k+1) (literal.drop (start k+1))
      (headPending pair.2.long k f c')).find? (fun a : Nat × Nat => a.1==i) with
      | none => (scalar i).read pair.2.long
      | some a => BitVec.ofNat _ a.2).toNat = _
    rw [early]
    simp only [pair,eq]
  have regLength : (runCodes table bank regs (chunk k)).length=start (k+1) := by
    have A := BStarNativeReceiptInduction.bounds K'
    rw [runCodes_length,L]
    unfold chunk
    simp only [List.length_take,List.length_drop,literal_length]
    omega
  intro i hi a Ha
  by_cases B : i<start k
  · have good : i<regs.length := L.symm ▸ B
    have V := val_early i (by omega)
    have readNil : (headPending (x r0).long k f c').find? (fun a : Nat × Nat => a.1==i)=none := by
      unfold headPending
      cases nodeResult (x r0).long f.argument.toNat c' <;> simp [show start k≠i by omega]
    rw [readNil] at V
    rw [runCodes_prefix table bank regs (chunk k) i good]
    exact V.trans (oldRep i good a Ha)
  · have hi₁ : i<start (k+1) := regLength ▸ hi
    have E : i=start k := by
      by_cases E : i=start k
      · exact E
      have row : (suffix k)[i-(start k+1)]?=some (.scan5 a) := by
        unfold suffix
        rw [List.getElem?_take,List.getElem?_drop]
        simp only [show i-(start k+1)<start (k+1)-start k-1 by omega,if_true]
        have J : start k+1+(i-(start k+1))=i := by omega
        rw [J]
        exact Ha
      have canon := maximal_suffix K'
      have M : .scan5 a∈suffix k := List.mem_of_getElem? row
      rw [←canon] at M
      exact False.elim ((scan_not_in_aliases _ a) M)
    subst i
    have CA : c'=.scan5 a := Option.some.inj (G.symm.trans Ha)
    obtain ⟨fit,value⟩ := scanResult a CA
    have V := val_early (start k) (Nat.le_refl _)
    have read : (headPending (x r0).long k f c').find? (fun a => a.1==start k)=
      some (start k,f.argument.toNat) := by simp [headPending,CA,nodeResult]
    rw [read] at V
    have Width := literal_width Ha
    have good : f.argument.toNat < 2^(widthAt scalarWidths (start k)) := by
      have B : 5≤widthAt scalarWidths (start k) := Width
      exact Nat.lt_of_lt_of_le fit (Nat.pow_le_pow_right (by decide : 0<(2:Nat)) B)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt good] at V
    rw [BStarNativePackedRep.chunk_head_read K' table bank regs L c' G]
    exact V.trans value.symm

end L4.BStarNativeScanNat
