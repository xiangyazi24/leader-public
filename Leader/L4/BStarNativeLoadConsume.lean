import Leader.L4.BStarNumericWordFrame
import Leader.L4.BStarNativeReceiptTape

namespace L4.BStarNativeLoadConsume
open AllSizeProtocol BStarTrace BStarLongWork BStarLongArithmetic BStarLongRegisters
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarSeparatorControl
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarNativeReceiptTape
open BStarNumericWordFrame

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem retain_through_consume {base out : X} {slot : Nat → Pos n} {len op : Nat}
    {turn ack : Fin n} {back : List (Fin n)}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : BusyOnly hp base slot len op out (.out len) (turn::back) (.back 0))
    (H : Hit hp base slot len (play (step out turn) back) ack op)
    {ix : Nat} (I : ix<len) {s : Fin n} (loc : slot ix=(s,1)) (node : Nat) :
    num (play (step out turn) back s).long node=num (out s).long node ∧
      num (step (play (step out turn) back) ack s).long node=num (out s).long node := by
  have old := busy_past hp T sep (Nat.le_of_lt I) s loc I node
  have no : ¬anyTag.F (atCursor (play (step out turn) back) (s,1)) := by
    have no := BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 H.1.2.1 ix (Nat.le_of_lt I)
    change ¬anyTag.F (atCursor (play (step out turn) back) (slot ix)) at no
    rwa [loc] at no
  have hold := step_no_forward hp _ ack s node (sep ack) no
  exact ⟨congrArg BitVec.toNat old,congrArg BitVec.toNat (hold.trans old)⟩

end L4.BStarNativeLoadConsume
