import Leader.L4.BStarForwardNumericBand
import Leader.L4.BStarFreshNumericOperandPrefix

/-! The numeric band guard and physical retained operands are proved
together, forward from the single real drained cut. -/
namespace L4.BStarNumericDrainedBand
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets BStarLongLayout
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarGeneratedBandScan BStarLongFixedRouting
open BStarFreshNumericOperands BStarFreshNumericOperandPrefix BStarForwardNumericBand
open BStarResetChartService

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- From actual ISSUE13 with drained active owned lines and both
valid retained tags, a generated raw word cannot abandon the numeric
band by reset. The first exit is the actual idle ISSUE408. A partial
word may end inside the band, with the current packet still healthy.
No lower PC bound or tag validity is assumed at later cuts. -/
theorem from_drained_seed {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w : List (Fin n)) (b : Mode)
    (hist : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++w) b)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len (play origin lead) .idle w b)
    (initial : pc (play origin lead) (S.getD 0 fall).1=13)
    (layout : ∀ u v,w=u++v → ∀ i,Layout B base i=Layout B (play (play origin lead) u) i)
    (center : ∀ u e v,w=u++e::v →
      ((capturedSelector 1).read (play (play origin lead) u (S.getD 0 fall).1).long).toNat<3)
    (drained : ∀ i sh,ActiveOwner hp base o.val i sh →
      (readLane (Sheet.index sh) ((play origin lead) i).long).mobile=.empty)
    (retained : ∀ i sh,ActiveOwner hp base o.val i sh → (sh=.ld ∨ sh=.rd) →
      ∃ d,(readLane (Sheet.index sh) ((play origin lead) i).long).retained=.data d) :
    let x := play origin lead
    let addr := fun j=>S.getD j fall
    ∃ pre post m,w=pre++post ∧
      GeneratedOwner hp base addr len x .idle pre m ∧
      GeneratedOwner hp base addr len (play x pre) m post b ∧
      (∀ u e v, pre=u++e::v → 13≤pc (play x u) (addr 0).1 ∧ pc (play x u) (addr 0).1<408) ∧
      (Issue408 addr (play x pre) m ∨ post=[] ∧ Live addr (play x pre) m) := by
  dsimp only
  let x := play origin lead
  have L : Live (fun j=>S.getD j fall) x .idle :=
    ⟨(by change 13≤pc (play origin lead) (S.getD 0 fall).1 ∧ pc (play origin lead) (S.getD 0 fall).1<408
         rw [initial]
         decide),fun _ _ E=>by cases E⟩
  apply stopped_word hp chart sep T L
  intro u e v U old
  have AU : w=u++(e::v) := U
  have F := layout u (e::v) AU
  have W : lead++w=(lead++u)++e::v := by rw [AU,List.append_assoc]
  obtain ⟨m,H,_⟩ := BStarGeneratedTapeCuts.split hp (lead++u) (e::v) (W ▸ hist)
  refine ⟨(root_header hp chart F).1,center u e v U,?_⟩
  apply single_prefix_operands hp chart sep lead u m H _ drained retained F
  intro a f t A
  refine ⟨layout a (f::t++e::v) ?_,old a f t A⟩
  rw [U,A,List.append_assoc]

#print axioms from_drained_seed
end L4.BStarNumericDrainedBand
