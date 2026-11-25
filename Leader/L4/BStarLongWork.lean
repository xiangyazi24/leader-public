import Leader.L4.BStarLongArithmetic
import Leader.L4.BStarLongGrant
import Leader.L4.BStarLongCommandData
import Leader.L4.BStarLongTransport
import Leader.L4.BStarIntegration

/-! The concrete long producer and the concrete bundle. Every
physical operation is wired to an executable handler, and all old
reads are captured before lowering a single patch. This definition
does not itself prove the independent whole-row refinement or the all-size composition. -/
namespace L4.BStarLongWork
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongTransport

abbrev CmdOffer := CommandClaim × BStarLongCommand.Offer

structure Publication where
  endpoint : Side
  bank : Fin 3
  deriving DecidableEq, Repr

structure Selected where
  k : List KWrite
  work : List (Bool × Patch LW)
  publications : List Publication

def Selected.append (u v : Selected) : Selected :=
  ⟨u.k++v.k,u.work++v.work,u.publications++v.publications⟩

def atOld (x : Pair (BitVec LW)) (a : AtK) : BitVec LW :=
  BStarTrace.lane (a.side==.right) x

/-- A source door and a terminal can both execute at the seam, from
their distinct old slots. This handler's semantic input is a classified
offer whose gate, data cancellation and grant response are resolved. -/
def selected (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : CmdOffer) : Selected :=
  let (c,t) := o
  let a := c.source
  let s := a.side==.right
  let old := atOld x a
  let degree := BStarLongCommand.geometry g a.side
  match t with
  | .door k =>
    match BStarLongDoor.oldDoor old k with
    | .hold => ⟨[],[],[]⟩
    | .write q => ⟨[],[(s,q)],[]⟩
    | .acceptTour op p => ⟨[],[(s,BStarLongArithmetic.acceptFile old op p)],[]⟩
  | .advance p =>
    let (num,afterDigit) := BStarLongArithmetic.visit degree a.occurrence old p
    let z := BStarLongOutgoing.execute degree a.occurrence old afterDigit
    let after := match z.carried with
      | .forward q => q
      | _ => ⟨1,0,0,0,0⟩
    ⟨advanceK g c after,[(s,num),(s,z.row)],
      z.published.toList.map (fun b => ⟨a.side,b⟩)⟩
  | _ => ⟨direct c t,[],[]⟩

def nonheader (g : LongGeometry) : Patch LW :=
  if g.axes.h6 then .empty _
  else
    let ctrl := (BStarLongDoor.ctrlPhase.assign 1).compose (BStarLongDoor.ctrlOp.assign 0)
    (ctrl.compose BStarLongDoor.clearFile).compose BStarLongOutgoing.descriptorClear

structure Trace where
  assignments : List (Bool × Patch LW)
  publications : List Publication

def longTrace (g : Pair LongGeometry) (x : Pair (BitVec LW)) : Trace :=
  let data := BStarLongCommandData.round g x
  let authority := BStarLongGrant.run g x data.offered
  let selectedRow : Selected := authority.departures.foldl
      (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let first := normalization g (readK x)
  let ks := first++selectedRow.k
  let last := observations g (readK x) ks
  let clear := [(false,nonheader g.1),(true,nonheader g.2)]
  { assignments := first.map lowerOne ++ clear ++
      authority.writes.map Write.patch ++ data.writes.map Write.patch ++
      selectedRow.work ++ (selectedRow.k++last).map lowerOne
    publications := selectedRow.publications }

def longWork (g : Pair LongGeometry) (x : Pair (BitVec LW)) : Pair (Patch LW) :=
  lower (longTrace g x).assignments

theorem long_exec (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    patchPair (longWork g x) x=(longTrace g x).assignments.foldl runWrite x :=
  lower_apply (longTrace g x).assignments x

theorem exact_assignment_mask (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (endpoint : Bool) (i : Nat) :
    (BStarTrace.lane endpoint (longWork g x)).mask.getLsbD i =
      (longTrace g x).assignments.any (fun t => t.1==endpoint && t.2.mask.getLsbD i) :=
  lower_mask (longTrace g x).assignments endpoint i

def bStar (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p) :
    LargeRows (production k₁ k₂ t₂ J₁ J₂ r c p c₁) :=
  BStarIntegration.productionWithLong k₁ k₂ t₂ J₁ J₂ r c p c₁ hp longWork

theorem bStar_long (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p) :
    (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp).longWork=longWork := rfl

theorem nonadvancing_no_publication (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (t : BStarLongCommand.Offer)
    (h : ∀ p, t≠.advance p) : (selected g x (c,t)).publications=[] := by
  cases t with
  | advance p => exact (h p rfl).elim
  | door token =>
    unfold selected
    dsimp only
    split <;> rfl
  | _ => rfl

end L4.BStarLongWork
