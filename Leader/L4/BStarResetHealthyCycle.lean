import Leader.L4.BStarResetCycle
import Leader.L4.BStarResetHealthyService
import Leader.L4.BStarResetChartNomination
import Leader.L4.BStarResetConsumedClean

/-! Clean reset service in a literal ring after an actual issue, under
a fixed lower layout. This is not arbitrary-entry reachability. -/
namespace L4.BStarResetHealthyCycle
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireAnchors BStarAcquireLiteralChain BStarAcquireForwardTrace
open BStarLongFixedRouting BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarResetSchedule
open BStarSeparatingRail BStarSeparatingProgress BStarAcquireWaitControl

open BStarResetCycle BStarResetHealthyService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem healthy_return_on {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (init : Q x)
    (op : Nat) (ho : op<3)
    (oldP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=1)
    (oldO : (ctrlOp.read (x (S.getD 0 fallback).1).long).toNat=op) :
    let root := (S.getD 0 fallback).1
    let door := RearTrace.predecessor root
    let step := AllSizeS1Geometry.step (n:=n) B
    let y := step x door
    let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
    ∃ pre post,
      sweeps n (2*len+1)=pre++post ∧ (pre++[door]).length≤n*(2*len+1)+1 ∧
      Seen step track (healthyTag op) len y (.out 0) pre (.back 0) ∧
      Clean track (healthyTag op) len (BStarResetSchedule.run step y pre) ∧
      let old := BStarResetSchedule.run step y pre
      let out := BStarResetSchedule.run step y (pre++[door])
      (∀ j≤len, track out j=.empty) ∧ Q out ∧ (ctrlPhase.read (out root).long)=1 ∧
      track old 0=finish (BStarResetTaggedRows.resetPayload op) ∧
      (ctrlOp.read (out root).long)=BitVec.ofNat 9 (op+1) := by
  dsimp only
  let root := (S.getD 0 fallback).1
  let door := RearTrace.predecessor root
  let step := AllSizeS1Geometry.step (n:=n) B
  let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x init)
  have hdr : oldH6 B x (rightNeighbor door)=true := by rw [R]; exact H
  have E := genuine_wait hp x door (distinct door) op ho hdr
    (show (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 by rw [R]; exact oldP)
    (show (ctrlOp.read (x (rightNeighbor door)).long).toNat=op by rw [R]; exact oldO)
  rw [R] at E
  let y := step x door
  have yQ : Q y := closed x init door
  have inv : Q y ∧ Waiting hp base root op y := ⟨yQ,fiber y yQ,E.2.1,E.2.2⟩
  have T {z : XX} : track z 0=atCursor z (root,0) :=
    congrArg (atCursor z) (Prod.ext rfl K)
  have F : (healthyTag op).F (track y 0) :=
    T.trans E.1
  obtain ⟨eOf,L,Tm⟩ := fixed_nominations hp C head cont
  have A := healthy_adapter_on hp C Q fiber closed distinct op ho eOf L Tm
  let Handled (a b : XX) := (∀ j≤len, track b j=.empty) ∧ Q b ∧
    (ctrlPhase.read (b root).long)=1 ∧
    track a 0=finish (BStarResetTaggedRows.resetPayload op) ∧
    (ctrlOp.read (b root).long)=BitVec.ofNat 9 (op+1)
  have handle (a : XX) (W : Q a ∧ Waiting hp base root op a)
      (L : Clean track (healthyTag op) len a) : Handled a (step a door) := by
    have weak : Clean track (resetTag op) len a := ⟨weakD op _ L.1,L.2⟩
    obtain ⟨empty,ph,opn⟩ := BStarResetConsumedClean.consumed_clean hp C op ho W.2 weak distinct
    exact ⟨empty,closed a W.1 door,ph,L.1,opn L.1⟩
  exact reset_prefix_then_door A y inv F door Handled handle

/-- A stage names the actual issue at its first mark, the healthy
tagged route, the still-old reply, then one independently applied
consumption mark. -/
def Stage (addr : Nat → Pos n) (len op : Nat) (x : XX) (w : List (Fin n)) (y : XX) : Prop :=
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let step := AllSizeS1Geometry.step (n:=n) B
  let track : XX → BStarSeparatingRail.Rail := project addr
  ∃ pre, w=door::(pre++[door]) ∧ y=BStarResetSchedule.run step x w ∧
    (ctrlPhase.read (x root).long).toNat=1 ∧ (ctrlOp.read (x root).long).toNat=op ∧
    Seen step track (healthyTag op) len (step x door) (.out 0) pre (.back 0) ∧
    track (BStarResetSchedule.run step (step x door) pre) 0=
      finish (BStarResetTaggedRows.resetPayload op)

theorem three_resets {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (init : Q x)
    (oldP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=1)
    (oldO : (ctrlOp.read (x (S.getD 0 fallback).1).long).toNat=0) :
    let addr := fun j => S.getD j fallback
    let root := (addr 0).1
    ∃ w₀ w₁ w₂ y₁ y₂ y₃,
      Stage hp addr len 0 x w₀ y₁ ∧ Stage hp addr len 1 y₁ w₁ y₂ ∧
      Stage hp addr len 2 y₂ w₂ y₃ ∧
      Q y₃ ∧ (∀ j≤len, atCursor y₃ (addr j)=.empty) ∧
      (ctrlPhase.read (y₃ root).long).toNat=1 ∧ (ctrlOp.read (y₃ root).long).toNat=3 ∧
      (w₀++w₁++w₂).length≤3*(n*(2*len+1)+2) := by
  dsimp only
  let addr := fun j => S.getD j fallback
  let root := (addr 0).1
  let step := AllSizeS1Geometry.step (n:=n) B
  let door := RearTrace.predecessor root
  have one (t : XX) (h : Q t) (op : Nat) (ho : op<3)
      (oldP : (ctrlPhase.read (t root).long).toNat=1) (oldO : (ctrlOp.read (t root).long).toNat=op) :
      ∃ w y, Stage hp addr len op t w y ∧ Q y ∧
        (∀ j≤len, atCursor y (addr j)=.empty) ∧
        (ctrlPhase.read (y root).long).toNat=1 ∧ (ctrlOp.read (y root).long).toNat=op+1 ∧
        w.length≤n*(2*len+1)+2 := by
    obtain ⟨pre,post,_,l,seen,_,empty,hQ,P,good,O⟩ :=
      healthy_return_on hp C Q fiber closed distinct head cont h op ho oldP oldO
    let w := door::(pre++[door])
    let y := BStarResetSchedule.run step t w
    have ex : (BitVec.ofNat 9 (op+1)).toNat=op+1 := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      omega
    refine ⟨w,y,⟨pre,rfl,rfl,oldP,oldO,seen,good⟩,hQ,empty,
      congrArg BitVec.toNat P,(congrArg BitVec.toNat O).trans ex,?_⟩
    change (pre++[door]).length+1≤n*(2*len+1)+2
    change (pre++[door]).length≤n*(2*len+1)+1 at l
    omega
  obtain ⟨w₀,y₁,A,Q₁,_,P₁,O₁,H₀⟩ := one x init 0 (by decide) oldP oldO
  obtain ⟨w₁,y₂,D,Q₂,_,P₂,O₂,H₁⟩ := one y₁ Q₁ 1 (by decide) P₁ O₁
  obtain ⟨w₂,y₃,F,Q₃,K,P₃,O₃,H₂⟩ := one y₂ Q₂ 2 (by decide) P₂ O₂
  refine ⟨w₀,w₁,w₂,y₁,y₂,y₃,A,D,F,Q₃,K,P₃,O₃,?_⟩
  simp only [List.length_append]
  omega

end L4.BStarResetHealthyCycle
