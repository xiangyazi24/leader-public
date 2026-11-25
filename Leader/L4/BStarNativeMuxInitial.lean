import Leader.L4.BStarNativeAddInitial
import Leader.L4.BStarNumericHealthy
import Leader.L4.BStarNumericConsecutive
import Leader.L4.BStarAcquireAckAncestry

namespace L4.BStarNativeMuxInitial
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongArithmetic
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule
open BStarNumericChronology BStarNumericCarry BStarNumericContinuity BStarNumericConsecutive
open BStarLongDoor BStarClearanceSource BStarResetControllerEntry

open BStarLongSignatures BStarLongRegisters
open L4.Compiler.Native

private def muxSlotCheck (k : Nat) : Bool :=
  match (nodeOf (13+k)).bind get with
  | some (.mux q _ _) =>
    (((muxInputs.find? fun e => e.1==13+k).map Prod.snd)==some q) &&
      (widthAt scalarWidths q==1)
  | _ => true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem muxSlotCensus : (List.range 395).all muxSlotCheck=true := by decide +kernel

theorem initial_mux (x : BitVec LW) {op i q a b : Nat}
    (lo : 13≤op) (hi : op<408)
    (N : nodeOf op=some i) (G : get i=some (.mux q a b)) :
    initial op x=some (source x q) ∧ source x q<2 := by
  have E : op=13+(op-13) := by omega
  have T := List.all_eq_true.mp muxSlotCensus (op-13) (List.mem_range.mpr (by omega))
  unfold muxSlotCheck at T
  rw [←E,N] at T
  simp only [Option.bind_some,G,Bool.and_eq_true,beq_iff_eq] at T
  have kind : arithKind op=some .mux := BStarNumericWidth.kind_exact lo hi N G
  have A : op≠acquire := by unfold acquire; omega
  have C : op≠copyLoad := by unfold copyLoad; omega
  have S : op≠stageOp := by unfold stageOp; omega
  have K : op≠sealOp := by unfold sealOp; omega
  have M : op≠commitOp := by unfold commitOp; omega
  constructor
  · have h : initial op x=scalarMux op x := by simp [initial,A,C,S,K,M,kind]
    rw [h]
    unfold scalarMux
    cases H : muxInputs.find? (fun e=>e.1==op) with
    | none => simp [H] at T
    | some pair =>
      have R := T.1
      rw [H] at R
      have R' : pair.2=q := Option.some.inj R
      exact congrArg (fun j => some ((scalar j).read x).toNat) R'
  · have L := ((scalar q).read x).isLt
    change ((scalar q).read x).toNat<2
    simpa [T.2] using L

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

open BStarNativeAddInitial

theorem first_mux_value {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (kind : arithKind op=some .mux)
    (qv : Nat) (qwidth : qv<2)
    (start : project (fun j => S.getD j fall) x 0=forward op qv)
    (d : D) (tail : List D)
    (first : ds.filter (significant hp base (fun j => S.getD j fall))=d::tail)
    (healthy : Numeric d.offer) :
    d.offer.argument.toNat=qv := by
  let addr := fun j => S.getD j fall
  let p0 : Payload := ⟨0,BitVec.ofNat 9 op,0,0,BitVec.ofNat 34 qv⟩
  have range := BStarArithmeticControllerReturn.arithmetic_range op (by rw [kind]; rfl)
  have op' : p0.opcode.toNat=op := Nat.mod_eq_of_lt (by omega)
  have N0 : Numeric p0 := ⟨rfl,op' ▸ range.1,op' ▸ range.2⟩
  have W0 : ∀ g j, BStarLongCommand.bind g j (.forward p0)=.forward p0 := by
    intro g j
    apply slot_bind g j p0 N0 rfl rfl 1
    · rw [op']
      have ad : op≠admit := by unfold admit; omega
      have bi : op≠bitOp := by unfold bitOp; omega
      have aq : op≠acquire := by unfold acquire; omega
      have cp : op≠copyLoad := by unfold copyLoad; omega
      have st : op≠stageOp := by unfold stageOp; omega
      have se : op≠sealOp := by unfold sealOp; omega
      have cm : op≠commitOp := by unfold commitOp; omega
      simp [forwardWidth,ad,bi,aq,cp,st,se,cm,kind]
    · change qv % 2^34<2
      rw [Nat.mod_eq_of_lt (by omega)]
      exact qwidth
  have inF : d∈ds.filter (significant hp base addr) := by rw [first]; simp
  obtain ⟨M,_⟩ := List.mem_filter.mp inF
  obtain ⟨V,_,hi⟩ := Aligned.record_facts hp A d M
  obtain ⟨pre,_,_,T,replay⟩ := Aligned.prefix_to hp A d M
  let g := oldPair B d.old d.mark
  let raw : Pair (BitVec LW) := ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)
  obtain ⟨q,Q,Hq,opq⟩ := BStarForwardProvenance.offer_origin g raw d.claim d.offer V.1 healthy.1
  have Nq : Numeric q := ⟨Hq,by rw [opq]; exact healthy.2.1,by rw [opq]; exact healthy.2.2⟩
  have here : project addr d.old d.index=.forward q := by
    change atCursor d.old (addr d.index)=_
    have E : addr d.index=address d.mark d.claim.source := V.2.2.1
    rw [E,←old_read d.old d.mark d.claim.source]
    exact Q
  have P : ∀ j, 0≤j → j<d.index →
      (addr j).2.val≠1 ∨ (longGeometry B (base (addr j).1)).inside=false :=
    fun j _ h => first_padding hp A d tail first j h
  have carried := busy_padding hp chart sep T 0 d.index p0 q rfl rfl (Nat.le_of_lt hi) P
    start N0 W0 (by rw [replay]; exact here) Nq
  have chosen := offer_exact g raw d.claim d.offer V.1 healthy
  unfold bound at chosen
  rw [Q,←carried,W0 _ _] at chosen
  have V := congrArg (fun y : Payload => y.argument.toNat) (Token.forward.inj chosen).symm
  change (d.offer.argument).toNat=qv%2^34 at V
  rwa [Nat.mod_eq_of_lt (by omega)] at V

theorem mux_first_from_launch {base before x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op i q a b : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (lo : 13≤op) (hi : op<408)
    (N : nodeOf op=some i) (G : get i=some (.mux q a b))
    (oldPC : (ctrlOp.read (before (S.getD 0 fall).1).long).toNat=op)
    (L : Launch (before (S.getD 0 fall).1).long (x (S.getD 0 fall).1).long)
    (d : D) (tail : List D)
    (first : ds.filter (significant hp base (fun j => S.getD j fall))=d::tail)
    (healthy : Numeric d.offer) :
    d.offer.argument.toNat=source (before (S.getD 0 fall).1).long q := by
  let root := (S.getD 0 fall).1
  let v := source (before root).long q
  have kind : arithKind op=some .mux := BStarNumericWidth.kind_exact lo hi N G
  have init := initial_mux (before root).long lo hi N G
  have geometry := (BStarResetChartService.root_header hp chart (busy_start hp (Aligned.busy hp A)).1.1).2
  have start : project (fun j => S.getD j fall) x 0=forward op v := by
    change atSite (x root).long (S.getD 0 fall).2=_
    rw [geometry]
    obtain ⟨_,a,I,T⟩ := L
    rw [oldPC,init.1] at I
    obtain rfl := Option.some.inj I
    have E := congrArg (fun v : (_ × BitVec 2) × BitVec 9 => v.1.1) T
    change atSite (x root).long 0=forward (ctrlOp.read (before root).long).toNat v at E
    rwa [oldPC] at E
  exact first_mux_value hp chart sep A kind v init.2 start d tail first healthy

end L4.BStarNativeMuxInitial
