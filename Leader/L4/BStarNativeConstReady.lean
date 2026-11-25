import Leader.L4.BStarNativePrefixInduction
import Leader.L4.BStarNativeNumberRetention
import Leader.L4.BStarNativeZeroReceipt
import Leader.L4.BStarNativePReceipt
import Leader.L4.BStarNativeRadixActual
import Leader.L4.BStarNativeBM1Actual

namespace L4.BStarNativeConstReady
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongCommand
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6Ordinal
open BStarOwnerLaunchOrigin BStarNativeReceiptTape BStarNativePrefixInduction
open BStarLongArithmetic L4.Compiler.Native L4.Compiler.Interp
open BStarNativeReceiptInduction BStarAliasRoster BStarAliasFold BStarNativeScalarRecurrence
open BStarNumericChartCoverage BStarNativeZeroHead
open BStarResetChartTouch BStarResetMarkAdapter BStarSeparatingRail BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- CONST never overlays a source scalar; extending by its distributed word
therefore preserves the exact old scalar representation. -/
theorem scalar {width : Nat} (T : PrimTable width) (bank : Bank)
    (old : BitVec LW) (k : Nat) (f : Payload) (v : ConstId) (regs : List Value)
    (G : get (start k)=some (.const v)) (L : regs.length=start k)
    (R : WellRep old [] regs literalCmp) : ScalarHead T bank old k regs (.const v) f := by
  have U : ¬literalCmp (start k) := by simp [literalCmp,G,BStarCmpReceipt.isCmp]
  refine .ready True.intro True.intro ?_
  have W : ∃ m, evalInstr (toInstr T bank (.const v)) regs=.word m := ⟨_,rfl⟩
  obtain ⟨m,W⟩ := W
  simp only [headPending,nodeResult,Option.toList_none,List.map_nil,W]
  intro i hi
  by_cases h : i<regs.length
  · have E := readReg_append_left regs [Value.word m] i h
    simpa only [BoolRep,CmpRep,E] using R i h
  · have eq : i=regs.length := by simp at hi; omega
    subst i
    have E : readReg (regs++[Value.word m]) regs.length=.word m := by
      simp [readReg]
    refine ⟨?_,?_⟩
    · intro b H
      rw [E] at H
      contradiction
    · intro C
      exact False.elim (U (L ▸ C))

set_option maxRecDepth 4096

/-- Only physical PC13 can be a zero constant in the fixed compiler band. -/
theorem zero_head {k : Nat} (K : k<395) (G : get (start k)=some (.const .zero)) : k=0 := by
  have C : (literal.drop 1).all (fun c => match c with
      | .const .zero => false | _ => true)=true := by decide +kernel
  have E : start k=0 := by
    by_cases z : start k=0
    · exact z
    · obtain ⟨J,E⟩ := List.getElem?_eq_some_iff.mp G
      have M : (.const .zero : Code) ∈ literal.drop 1 := by
        have Q : start k-1<(literal.drop 1).length := by simp; omega
        have J' := List.getElem_mem (l:=literal.drop 1) Q
        simp only [List.getElem_drop, show 1+(start k-1)=start k by omega,E] at J'
        exact J'
      have F := List.all_eq_true.mp C _ M
      contradiction
  have N := scheduled_node K
  rw [E] at N
  have Q := BStarNativeNumberRetention.opcode_of_node N first_op.1
  omega

/-- Concrete Ready record for the fixed CONST family. The later visit geometry
comes from the real PC13 sweep. The launch history and matching consume are
the ones in the enclosing receipt induction. -/
theorem ready {base initial x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)} {width k : Nat}
    (K : k<395) (v : ConstId) (G : get (start k)=some (.const v))
    (F : Found hp base (fun j => S.getD j fall) len (13+k) x w (.back 0))
    (H : Hit hp base (fun j => S.getD j fall) len (run x w) door (13+k))
    (later : 0<k → ∃ w0 door0 between,
      Found hp base (fun j => S.getD j fall) len 13 initial w0 (.back 0) ∧
      Hit hp base (fun j => S.getD j fall) len (run initial w0) door0 13 ∧
      x=run (step (run initial w0) door0) between ∧
      (∀ u z,w0++door0::(between++w)=u++z →
        ∀ j, Layout B (run initial u) j=Layout B base j))
    (hr : 1<width)
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (T : PrimTable width) (bank : Bank) (sem : PrimSem T bank)
    (capture : ∀ q d, ((capturedHeader q d).read (run x w (S.getD 0 fall).1).long).toNat=
      (bank.hdr q d).toNat)
    (P : BStarNativePackedRep.PackedRep (run x w) (S.getD 0 fall).1
      (digitSite hp base (fun j => S.getD j fall) len width L) k (regsBefore T bank k)) :
    Ready hp T bank (run x w) (step (run x w) door) (S.getD 0 fall).1
      (digitSite hp base (fun j => S.getD j fall) len width L) k (.const v)
      (regsBefore T bank k) := by
  refine ⟨G,capture,fun f _ => Or.inr (scalar T bank _ k f v _ G P.length P.scalar),
    ?_,?_⟩
  · intro _ _ _ E
    cases E
  · intro slot
    have N := scheduled_node K
    have hi : 13+k<408 := by omega
    have lo : 13≤13+k := by omega
    have fl := fun j => (flags j).1
    cases v with
    | zero =>
      have z := zero_head K G
      subst k
      obtain ⟨L',_,E,_⟩ := BStarNativeZeroReceipt.zero_receipt hp chart sep F H fl notShort T bank sem
      rw [prefix_zero]
      exact E
    | p =>
      obtain ⟨L',E⟩ := BStarNativePReceipt.p_receipt hp chart sep F H lo hi N G slot (by omega)
        flags notShort T bank sem _
      exact E
    | bm1 =>
      have nz : 0<k := by
        apply Decidable.byContradiction
        intro E
        have eq : k=0 := by omega
        subst k
        have A : get (start 0)=some (.const .zero) := by decide +kernel
        cases A.symm.trans G
      obtain ⟨w0,door0,between,F0,H0,Q,stable⟩ := later nz
      obtain ⟨L',E⟩ := BStarNativeBM1Actual.bm1_receipt hp chart sep F0 H0 Q F H lo hi N G
        slot hr flags notShort stable T bank sem _
      exact E
    | one | eight | max =>
      have nz : 0<k := by
        apply Decidable.byContradiction
        intro E
        have eq : k=0 := by omega
        subst k
        have A : get (start 0)=some (.const .zero) := by decide +kernel
        cases A.symm.trans G
      obtain ⟨w0,door0,between,F0,H0,Q,stable⟩ := later nz
      obtain ⟨L',E⟩ := BStarNativeRadixActual.radix_receipt hp chart sep F0 H0 Q F H lo hi N _
        (by decide) G slot (by omega) fl notShort stable T bank sem _
      exact E
  
#print axioms ready
end L4.BStarNativeConstReady
