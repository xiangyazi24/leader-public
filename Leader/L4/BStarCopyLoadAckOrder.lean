import Leader.L4.BStarCopySetupReplay
import Leader.L4.BStarWriterTransferWindow

namespace L4.BStarCopyLoadAckOrder
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarLongDoor BStarWriterTransferWindow BStarCopySetupReplay

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- A true ISSUE8 whose physical busy flight is still at the chosen
LOAD mark cannot precede the actual ACK5 cut. Otherwise the old
ACK5 configuration would be on this busy flight with PC8. -/
theorem issue8_after_ack5 {base origin : X} {slot : Nat→Pos n} {len : Nat}
    (lead ackLead post rest : List (Fin n)) (issue ack : Fin n) {z : Cursor}
    (shape : lead++issue::post=ackLead++ack::rest)
    (at8 : pc (play origin lead) (slot 0).1=8)
    (at5 : pc (play origin ackLead) (slot 0).1=5)
    (busy : BusyOnly hp base slot len 8 (ring (play origin lead) issue) (.out 0) post z) :
    ∃ gap,lead=(ackLead++[ack])++gap := by
  rcases List.append_eq_append_iff.mp shape with ⟨q,E,V⟩|⟨q,E,V⟩
  · cases q with
    | nil =>
      rw [List.append_nil] at E
      rw [←E,at5] at at8
      contradiction
    | cons m q =>
      obtain ⟨rfl,P⟩ := List.cons.inj V
      have pc8 := busy_prefix_pc hp busy q (ack::rest) P
      have state : play origin ackLead=play (ring (play origin lead) issue) q := by
        rw [E,BStarResetSchedule.run_append]; rfl
      rw [state,pc8] at at5
      contradiction
  · cases q with
    | nil =>
      rw [List.append_nil] at E
      rw [←E,at8] at at5
      contradiction
    | cons m q =>
      obtain ⟨rfl,_⟩ := List.cons.inj V.symm
      exact ⟨q,by rw [E,List.append_assoc]; rfl⟩

#print axioms issue8_after_ack5
end L4.BStarCopyLoadAckOrder
