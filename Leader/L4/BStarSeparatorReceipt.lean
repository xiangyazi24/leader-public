import Leader.L4.BStarSeparatorRing
import Leader.L4.BStarResetConsumedClean
import Leader.L4.BStarJoinedControllerReturn

/-! Consume the pointed reply at a separate old predecessor mark.
Whether the reply is healthy, a miss, or a canonical fault, the actual
owner rail is empty and the phase is ISSUE on a legal next opcode. -/
namespace L4.BStarSeparatorReceipt
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarResetSchedule
open BStarLongDoor BStarResetChartService BStarResetControllerEntry

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem consume {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback) (op : Nat)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (wait : Waiting hp base (S.getD 0 fallback).1 op x)
    (clean : Clean (project (fun j => S.getD j fallback)) anyTag len x) :
    let track := project (fun j => S.getD j fallback)
    let root := (S.getD 0 fallback).1
    let e := RearTrace.predecessor root
    let y := AllSizeS1Geometry.step B x e
    (∀ j≤len, track y j=.empty) ∧ (ctrlPhase.read (y root).long).toNat=1 ∧
      ∃ a, (a=0 ∨ (op<a ∧ a<413)) ∧ (ctrlOp.read (y root).long).toNat=a := by
  dsimp only
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let e := RearTrace.predecessor root
  let y := AllSizeS1Geometry.step B x e
  let track : XX → BStarSeparatingRail.Rail := project adr
  have R : rightNeighbor e=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C wait.1
  obtain ⟨pay,P⟩ := clean.1
  have F {z : XX} : track z 0=atSite (z root).long 0 := by
    change atSite (z root).long (adr 0).2=_
    rw [K]
  have RD : atSite (x (rightNeighbor e)).long 0=.reply pay := by rw [R]; exact F.symm.trans P
  let v : BitVec LW := (x (rightNeighbor e)).long
  let g := longGeometry B (x (rightNeighbor e))
  obtain ⟨bound,Bd⟩ := bound_D g 0 pay
  have G : BStarLongCommand.bind g 0 (atSite v 0)=.reply bound := by rw [show atSite v 0=.reply pay from RD]; exact Bd
  obtain ⟨a,A,E⟩ := BStarJoinedControllerReturn.joined_reply k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) bound (by rw [R]; exact H) (by rw [R]; exact wait.2.1)
      (by rw [R]; exact wait.2.2.1) G
  have Y : y root=(largePair B (x e,x (rightNeighbor e))).2 := by
    simp only [y,AllSizeS1Geometry.step,←R,if_neg (Ne.symm (distinct e)),if_true]
  rw [←Y] at E
  have ha : a<413 := by rcases A with Z|Z <;> omega
  have OP : (ctrlOp.read (y root).long).toNat=a := by
    have F' : ctrlOp.read (y root).long=BitVec.ofNat 9 a := congrArg Prod.snd E
    rw [F']
    change a % 512=a
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_,?_,a,?_,OP⟩
  · intro j h
    by_cases J : j=0
    · subst j
      have rootE : atSite (y root).long 0=.empty := congrArg (fun s => s.1.1) E
      exact F.trans rootE
    · exact BStarResetConsumedClean.suffix_empty_any hp C wait.1 clean e (distinct e) j (Nat.pos_of_ne_zero J) h
  · have V : ctrlPhase.read (y root).long=1 := congrArg (fun s => s.1.2) E
    exact congrArg BitVec.toNat V
  · change a=0 ∨ (ctrlOp.read (x (rightNeighbor e)).long).toNat<a ∧ a<413 at A
    rw [R,wait.2.2.2] at A
    exact A

#print axioms consume
end L4.BStarSeparatorReceipt
