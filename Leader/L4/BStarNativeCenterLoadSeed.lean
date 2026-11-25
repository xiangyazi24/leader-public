import Leader.L4.BStarNativeLoadTours
import Leader.L4.BStarNativeAddInitial
import Leader.L4.BStarCapturedCompilerInputs

namespace L4.BStarNativeCenterLoadSeed
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims BStarLongLayout
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongArithmetic
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule
open BStarNumericChronology BStarNumericCarry BStarNumericContinuity BStarNumericConsecutive
open BStarLongDoor BStarClearanceSource BStarResetControllerEntry BStarNativeLoadTours

def seed (q : Fin 3) (bank : Fin 3) : Nat := if q=1 then bank.val else 0

theorem seed_bound (q bank : Fin 3) : seed q bank<3 := by
  unfold seed
  split
  · exact bank.isLt
  · decide

private theorem initial_load (q : Fin 3) (f : Fin 9) (bank : Fin 3) (x : BitVec LW)
    (cap : ((capturedSelector 1).read x).toNat=bank.val) :
    initial (loadOp q f) x=some (seed q bank) := by
  have lo : 13≤loadOp q f := by unfold loadOp; omega
  have hi : loadOp q f<408 := by have := q.isLt; have := f.isLt; unfold loadOp; omega
  have kind := (literal_load_slots q f).2.2
  by_cases h : q=1
  · rw [BStarCapturedCompilerInputs.center_load_initial x _ (by simpa [h] using kind) lo hi,cap]
    simp [seed,h,Nat.ne_of_lt bank.isLt]
  · have A : loadOp q f≠acquire := by unfold acquire; omega
    have C : loadOp q f≠copyLoad := by unfold copyLoad; omega
    have S : loadOp q f≠stageOp := by unfold stageOp; omega
    have T : loadOp q f≠sealOp := by unfold sealOp; omega
    have F : loadOp q f≠commitOp := by unfold commitOp; omega
    simp [initial,A,C,S,T,F,kind,h,seed]

theorem launch_seed (q : Fin 3) (f : Fin 9) (bank : Fin 3) (old fresh : BitVec LW)
    (op : (ctrlOp.read old).toNat=loadOp q f)
    (cap : ((capturedSelector 1).read old).toNat=bank.val) (L : Launch old fresh) :
    atSite fresh 0=forward (loadOp q f) (seed q bank) := by
  obtain ⟨_,a,I,T⟩ := L
  rw [op,initial_load q f bank old cap] at I
  have eq := Option.some.inj I.symm
  subst a
  have E := congrArg (fun v : (_ × BitVec 2) × BitVec 9 => v.1.1) T
  change atSite fresh 0=forward (ctrlOp.read old).toNat (seed q bank) at E
  rwa [op] at E

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

theorem first_seed {base before x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (q : Fin 3) (f : Fin 9) (bank : Fin 3)
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j=>S.getD j fall) len (loadOp q f) x 0 w len ds)
    (oldPC : (ctrlOp.read (before (S.getD 0 fall).1).long).toNat=loadOp q f)
    (cap : ((capturedSelector 1).read (before (S.getD 0 fall).1).long).toNat=bank.val)
    (L : Launch (before (S.getD 0 fall).1).long (x (S.getD 0 fall).1).long)
    (d : D) (tail : List D)
    (first : ds.filter (significant hp base (fun j=>S.getD j fall))=d::tail)
    (healthy : Numeric d.offer) :
    d.offer.argument.toNat=seed q bank := by
  let addr := fun j=>S.getD j fall
  let op := loadOp q f
  let a := seed q bank
  let p0 : Payload := ⟨0,BitVec.ofNat 9 op,0,0,BitVec.ofNat 34 a⟩
  have lo : 13≤op := by unfold op loadOp; omega
  have hi : op<408 := by have := q.isLt; have := f.isLt; unfold op loadOp; omega
  have op' : p0.opcode.toNat=op := Nat.mod_eq_of_lt (by omega)
  have small := seed_bound q bank
  have arg : p0.argument.toNat=a := Nat.mod_eq_of_lt (by change a<2^34; change a<3 at small; omega)
  have N0 : Numeric p0 := ⟨rfl,op' ▸ lo,op' ▸ hi⟩
  have kind := (literal_load_slots q f).2.2
  have W0 : ∀ g j, BStarLongCommand.bind g j (.forward p0)=.forward p0 := by
    intro g j
    by_cases h : q=1
    · apply slot_bind g j p0 N0 rfl rfl 2
      · rw [op',arg,BStarNumericWidth.width_numeric lo hi]
        change arithKind op=some _ at kind
        rw [kind]
        have ar : a%4≠3 := by rw [Nat.mod_eq_of_lt (show a<4 by change a<3 at small; omega)]; omega
        simp [h,ar]
      · rw [arg]
        change a<3 at small
        omega
    · have aa : a=0 := by simp [a,seed,h]
      apply slot_bind g j p0 N0 rfl rfl 0
      · rw [op',arg,BStarNumericWidth.width_numeric lo hi]
        change arithKind op=some _ at kind
        rw [kind]
        simp [h]
      · rw [arg,aa]
        decide
  have start : project addr x 0=.forward p0 := by
    change atSite (x (addr 0).1).long (addr 0).2=_
    rw [show (addr 0).2=0 from congrArg Prod.snd chart.root]
    exact launch_seed q f bank _ _ oldPC cap L
  have inF : d∈ds.filter (significant hp base addr) := by rw [first]; simp
  obtain ⟨M,_⟩ := List.mem_filter.mp inF
  obtain ⟨V,_,indexBound⟩ := Aligned.record_facts hp A d M
  obtain ⟨pre,_,_,T,replay⟩ := Aligned.prefix_to hp A d M
  let g := oldPair B d.old d.mark
  let raw : Pair (BitVec LW) := ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)
  obtain ⟨z,Z,Hz,opz⟩ := BStarForwardProvenance.offer_origin g raw d.claim d.offer V.1 healthy.1
  have NZ : Numeric z := ⟨Hz,by rw [opz]; exact healthy.2.1,by rw [opz]; exact healthy.2.2⟩
  have here : project addr d.old d.index=.forward z := by
    change atCursor d.old (addr d.index)=_
    have E : addr d.index=address d.mark d.claim.source := V.2.2.1
    rw [E,←old_read d.old d.mark d.claim.source]
    exact Z
  have P : ∀ j, 0≤j → j<d.index →
      (addr j).2.val≠1 ∨ (longGeometry B (base (addr j).1)).inside=false :=
    fun j _ h => BStarNativeAddInitial.first_padding hp A d tail first j h
  have carried := busy_padding hp chart sep T 0 d.index p0 z rfl rfl (Nat.le_of_lt indexBound) P
    start N0 W0 (by rw [replay]; exact here) NZ
  have chosen := offer_exact g raw d.claim d.offer V.1 healthy
  unfold bound at chosen
  rw [Z,←carried,W0 _ _] at chosen
  exact (congrArg (fun y : Payload => y.argument.toNat) (Token.forward.inj chosen).symm).trans arg

#print axioms launch_seed
#print axioms first_seed
end L4.BStarNativeCenterLoadSeed
