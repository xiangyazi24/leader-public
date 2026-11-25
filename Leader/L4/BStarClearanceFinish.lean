import Leader.L4.BStarClearancePhysical
import Leader.L4.BStarSeparatorRing
import Leader.L4.BStarSeparatorReceipt

namespace L4.BStarClearanceFinish
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearancePhysical BStarClearanceOffset
open BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The actual rank forcing word cannot end while the tracked command
is still in flight. Its first tagged return, including a canonical
fault, is attained in a prefix of that same finite word. -/
theorem finish_pointed {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (I : Q x) (cx : correct (oldH6 B base) hh 5 x)
    (op : Nat) (z : Cursor)
    (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) z) :
    let adr := fun j => S.getD j fall
    let root := (adr 0).1
    let track := project adr
    ∃ w, let y := BStarResetSchedule.run step x w
      Seen step track anyTag len x z w (.back 0) ∧
      Q y ∧ Waiting hp base root op y ∧ Clean track anyTag len y := by
  dsimp only
  let adr := fun j => S.getD j fall
  let root := (adr 0).1
  let track : X → BStarSeparatingRail.Rail := project adr
  obtain ⟨w,_,_,R⟩ := reach_nonheld hp chart sep head cont Q closed same heads conts cb I cx
  obtain ⟨pre,post,d,W,H,J,A,K,P,T⟩ := BStarSeparatorRing.lift_word hp chart Q same
    (fun y hy e => closed y e hy) sep op w z I wait G
  by_cases D : d=.back 0
  · exact ⟨pre,D ▸ H,J,A,P D⟩
  have done : post=[] := T.resolve_left D
  have eq : w=pre := by simpa only [done,List.append_nil] using W
  have rooteq : root=(endpoint (oldH6 B base) hh o 0).1 := congrArg Prod.fst chart.root
  rw [eq,←rooteq] at R
  exfalso
  apply R
  refine ⟨A.2.1,A.2.2.1,?_⟩
  let y := BStarResetSchedule.run step x pre
  have rootToken : track y 0 = atSite (y root).long 0 := by
    change atSite (y root).long (adr 0).2=_
    rw [(root_header hp chart A.1).2]
  have V := before_receipt K D
  change track y 0=.trail ∨ (∃ q,track y 0=.forward q) at V
  rwa [rootToken] at V

#print axioms finish_pointed
end L4.BStarClearanceFinish
