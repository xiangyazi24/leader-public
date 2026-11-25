import Leader.L4.BStarNumericHealthy
import Leader.L4.BStarNumericConsecutive
import Leader.L4.BStarAcquireAckAncestry

namespace L4.BStarNativeAddInitial
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongArithmetic
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule
open BStarNumericChronology BStarNumericCarry BStarNumericContinuity BStarNumericConsecutive
open BStarLongDoor BStarClearanceSource BStarResetControllerEntry

theorem bitCarry_initial (x : BitVec LW) {op : Nat} (G : arithKind op=some .bitCarry) :
    initial op x=some 0 := by
  have Z := BStarArithmeticControllerReturn.arithmetic_range op (by rw [G]; rfl)
  have A : op≠acquire := by unfold acquire; omega
  have C : op≠copyLoad := by unfold copyLoad; omega
  have S : op≠stageOp := by unfold stageOp; omega
  have K : op≠sealOp := by unfold sealOp; omega
  have M : op≠commitOp := by unfold commitOp; omega
  simp [initial,A,C,S,K,M,G]

theorem launch_zero (old fresh : BitVec LW) {op : Nat}
    (O : (ctrlOp.read old).toNat=op) (G : arithKind op=some .bitCarry)
    (L : Launch old fresh) : atSite fresh 0=forward op 0 := by
  obtain ⟨_,a,I,T⟩ := L
  rw [O,bitCarry_initial old G] at I
  obtain rfl := Option.some.inj I
  have E := congrArg (fun v : (_ × BitVec 2) × BitVec 9 => v.1.1) T
  change atSite fresh 0=forward (ctrlOp.read old).toNat 0 at E
  rwa [O] at E

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

private theorem enum_index {ds : List D} {len : Nat}
    (idx : ds.map Departure.index=List.range' 0 len)
    (j : Nat) (J : j<ds.length) :
    (ds[j]'J).index=j := by
  have Q := congrArg (fun a : List Nat => a[j]?) idx
  have R : j<(List.range' 0 len).length := by rw [←idx,List.length_map]; exact J
  rw [List.getElem?_map,List.getElem?_eq_getElem J,List.getElem?_eq_getElem R,
    List.getElem_range' R] at Q
  simpa using Option.some.inj Q

/-- Every chart index before the first significant departure is padding,
because the actual aligned record list enumerates every outward index. -/
theorem first_padding {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x 0 w len ds) (d : D) (tail : List D)
    (first : ds.filter (significant hp base addr)=d::tail) :
    ∀ j, j<d.index → (addr j).2.val≠1 ∨ (longGeometry B (base (addr j).1)).inside=false := by
  obtain ⟨pre,post,E,preFalse,_,_⟩ := List.filter_eq_cons_iff.mp first
  have idx := (OutTape.indices hp (Aligned.to_tape hp A)).2
  rw [Nat.sub_zero] at idx
  have kl : pre.length<ds.length := by rw [E,List.length_append,List.length_cons]; omega
  have atIdx := enum_index idx pre.length kl
  have dEq : (ds[pre.length]'kl)=d := by
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem kl,E,List.getElem?_append_right (Nat.le_refl _)]
    simp
  rw [dEq] at atIdx
  intro j J
  have jb : j<pre.length := by omega
  have jj : j<ds.length := by omega
  have el : (ds[j]'jj)=(pre[j]'jb) := by
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem jj,E,List.getElem?_append_left jb,List.getElem?_eq_getElem jb]
  have ji := enum_index idx j jj
  rw [el] at ji
  have T := preFalse _ (List.getElem_mem jb)
  unfold significant at T
  rw [ji] at T
  cases K : (longGeometry B (base (addr j).1)).inside
  · exact .inr rfl
  · exact .inl (by simpa [K] using T)

/-- Exact zero carry at the first significant selected offer from the
actual launch. All intervening marks come from the original aligned
outward word. Its first selected offer is healthy on a successful
numeric return by NumericHealthy.records_ready. -/
theorem first_significant_zero {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (kind : arithKind op=some .bitCarry)
    (start : project (fun j => S.getD j fall) x 0=forward op 0)
    (d : D) (tail : List D)
    (first : ds.filter (significant hp base (fun j => S.getD j fall))=d::tail)
    (healthy : Numeric d.offer) :
    d.offer.argument.toNat=0 := by
  let addr := fun j => S.getD j fall
  let p0 : Payload := ⟨0,BitVec.ofNat 9 op,0,0,0⟩
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
    · change 0<2; decide
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
  exact congrArg (fun y : Payload => y.argument.toNat) (Token.forward.inj chosen).symm

/-- ADD and SUB share the literal bit-carry initialization. The input
is the real launch's old/new source snapshot, not a caller-supplied
packet equality at chart index zero. -/
theorem add_first_from_launch {base before x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op i a b : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (lo : 13≤op) (hi : op<408)
    (N : nodeOf op=some i) (G : get i=some (.add a b))
    (oldPC : (ctrlOp.read (before (S.getD 0 fall).1).long).toNat=op)
    (L : Launch (before (S.getD 0 fall).1).long (x (S.getD 0 fall).1).long)
    (d : D) (tail : List D)
    (first : ds.filter (significant hp base (fun j => S.getD j fall))=d::tail)
    (healthy : Numeric d.offer) :
    d.offer.argument.toNat=0 := by
  have kind : arithKind op=some .bitCarry := BStarNumericWidth.kind_exact lo hi N G
  have geometry := (BStarResetChartService.root_header hp chart (busy_start hp (Aligned.busy hp A)).1.1).2
  have start : project (fun j => S.getD j fall) x 0=forward op 0 := by
    change atSite (x (S.getD 0 fall).1).long (S.getD 0 fall).2=_
    rw [geometry]
    exact launch_zero _ _ oldPC kind L
  exact first_significant_zero hp chart sep A kind start d tail first healthy

end L4.BStarNativeAddInitial
