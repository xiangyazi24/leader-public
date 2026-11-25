import Leader.L4.BStarFreshNumericLaunch
import Leader.L4.BStarArithmeticControllerReturn

/-! A returned healthy numeric token drives the literal source to the
successor instruction. The last route needs only the valid center
capture selector, not success of a later STAGE or publication. -/
namespace L4.BStarFreshNumericConsume
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken
open BStarLongCommand BStarLongSignatures BStarLongLayout BStarLongArithmetic
open BStarArithmeticControllerReturn BStarAcquireWaitControl BStarLongDoor L4.Compiler.Native

theorem successor_exact (old : BitVec LW) (op : Nat) (L : 13≤op) (U : op<408)
    (center : op=407 → ((capturedSelector 1).read old).toNat<3) :
    successor old op=op+1 := by
  have len : op-13<tourNodes.length := by rw [actual_table_lengths.1]; omega
  let i := tourNodes[op-13]
  have im : i∈tourNodes := List.getElem_mem len
  rw [BStarCmpReceipt.physical_table] at im
  have bound : i<literal.length := by
    rw [actual_table_lengths.2]
    exact List.mem_range.mp (List.mem_filter.mp im).1
  have node : nodeOf op=some i := by simp [nodeOf,Nat.not_lt.mpr L,List.getElem?_eq_getElem len,i]
  have code : BStarLongArithmetic.get i=some literal[i] := by
    simp [BStarLongArithmetic.get,List.getElem?_eq_getElem bound]
  simp only [successor,node,code]
  by_cases low : op<407
  · simp [low]
  · have eq : op=407 := by omega
    simp [center eq,eq,stageOp]

private theorem arith_exists (op : Nat) (L : 13≤op) (U : op<408) :
    (arithKind op).isSome=true := by
  have len : op-13<arithmetic.length := by rw [signature_pins.1]; omega
  simp [arithKind,Nat.not_lt.mpr L,List.getElem?_eq_getElem len]

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarFreshNumericTrace BStarNumericReturn

variable {k₁ k₂ t₂ J₁ J₂ r c pmod c₁ n : Nat} (hp : 0<pmod)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c pmod c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- The nominated incoming physical mark consumes the legitimate
numeric reply, and reaches the exact next PC (including 407→408). -/
theorem source_successor {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (lo : 13≤op) (hi : op<408)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (H : HealthAt op (project (fun j => S.getD j fall) x) (.back 0))
    (center : op=407 → ((capturedSelector 1).read (x (S.getD 0 fall).1).long).toNat<3) :
    let root := (S.getD 0 fall).1
    let y := step x (RearTrace.predecessor root)
    control (y root).long=(1,BitVec.ofNat 9 (op+1)) := by
  dsimp only
  let root := (S.getD 0 fall).1
  let e := RearTrace.predecessor root
  have reach : rightNeighbor e=root := RearTrace.right_predecessor root
  obtain ⟨f,F,V,O⟩ := H
  obtain ⟨head,occurrence⟩ := root_header hp chart W.1
  change atSite (x root).long (S.getD 0 fall).2=.reply f at F
  rw [occurrence] at F
  have R : BStarLongCommand.bind (longGeometry B (x root)) 0 (atSite (x root).long 0)=.reply f :=
    (congrArg (BStarLongCommand.bind (longGeometry B (x root)) 0) F).trans (V.2 _ _)
  have neq : root≠e := reach ▸ (Ne.symm (sep e))
  have post : ((step x e) root).long=(largePair B (x e,x root)).2.long := by
    simp only [AllSizeS1Geometry.step,reach,if_neg neq,if_true]
  rw [post]
  have oldOp : (ctrlOp.read (x root).long).toNat=op := W.2.2.2
  have J := joined_arithmetic_control k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp (x e,x root) f
    head W.2.1 W.2.2.1 R V.1 (O.trans oldOp.symm) (oldOp.symm ▸ arith_exists op lo hi)
  change control (largePair B (x e,x root)).2.long=
    (1,BitVec.ofNat 9 (successor (x root).long (ctrlOp.read (x root).long).toNat)) at J
  rw [oldOp,successor_exact _ op lo hi center] at J
  exact J

#print axioms source_successor
end L4.BStarFreshNumericConsume
