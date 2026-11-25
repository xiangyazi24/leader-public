import Leader.L4.BStarNeedPrefix
import Leader.L4.BStarOwnerLaunchOrigin

namespace L4.BStarNeedTrace
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNeedPrefix

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def tailWord (door : Fin n) (sf wait1 bit wait2 commit : List (Fin n)) :=
  sf++door::(wait1++door::(bit++door::(wait2++door::commit)))

/-- The exact phases of a physical matched NEED tail. An idle gap has
no owner door mark; the one BIT interval is a true uninterrupted
flight, surrounded only by the SEAL and COMMIT controllers. -/
structure Phases (base : X) (addr : Nat→Pos n) (len k : Nat) (x : X)
    (sf wait1 bit wait2 commit : List (Fin n)) : Prop where
  sealFlight : BusyOnly hp base addr len sealOp x (.out (k+1)) sf (.back 0)
  sealAck : Event hp addr len (play x sf) (RearTrace.predecessor (addr 0).1)
    (.busy sealOp (.back 0)) .idle
  waitBit : GeneratedOwner hp base addr len (step (play x sf) (RearTrace.predecessor (addr 0).1)) .idle wait1 .idle
  beforeBitOff : ∀ e∈wait1,rightNeighbor e≠(addr 0).1
  bitIssue : let door := RearTrace.predecessor (addr 0).1
    let x := play (step (play x sf) door) wait1
    Event hp addr len x door .idle (.busy bitOp (.out 0))
  bitFlight : let door := RearTrace.predecessor (addr 0).1
    let x := step (play (step (play x sf) door) wait1) door
    BusyOnly hp base addr len bitOp x (.out 0) bit (.back 0)
  bitAck : let door := RearTrace.predecessor (addr 0).1
    let x := play (step (play (step (play x sf) door) wait1) door) bit
    Event hp addr len x door (.busy bitOp (.back 0)) .idle
  waitCommit : let door := RearTrace.predecessor (addr 0).1
    let x := step (play (step (play (step (play x sf) door) wait1) door) bit) door
    GeneratedOwner hp base addr len x .idle wait2 .idle
  beforeCommitOff : ∀ e∈wait2,rightNeighbor e≠(addr 0).1
  commitIssue : let door := RearTrace.predecessor (addr 0).1
    let x := play (step (play (step (play (step (play x sf) door) wait1) door) bit) door) wait2
    Event hp addr len x door .idle (.busy commitOp (.out 0))
  commitFlight : let door := RearTrace.predecessor (addr 0).1
    let x := step (play (step (play (step (play (step (play x sf) door) wait1) door) bit) door) wait2) door
    BusyOnly hp base addr len commitOp x (.out 0) commit (.out k)

def Matched (base : X) (addr : Nat→Pos n) (len k : Nat) (x : X) (w : List (Fin n)) : Prop :=
  ∃ sf wait1 bit wait2 commit, w=tailWord (RearTrace.predecessor (addr 0).1) sf wait1 bit wait2 commit ∧
    Phases hp base addr len k x sf wait1 bit wait2 commit

theorem busy_generated {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {a b : Cursor} (T : BusyOnly hp base addr len op x a w b) :
    GeneratedOwner hp base addr len x (.busy op a) w (.busy op b) := by
  induction T with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

#print axioms busy_generated
end L4.BStarNeedTrace
