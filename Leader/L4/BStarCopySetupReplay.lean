import Leader.L4.BStarCopySetupCuts
import Leader.L4.BStarCopyCleanupOriginal
import Leader.L4.BStarCopyLeftFenceHold
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopySetupReplay
open BStarCopyFenceCuts
open BStarLongCommand
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarGeneratedPCAncestry
open BStarGeneratedBandScan BStarNativeReceiptTape BStarOwnerLaunchOrigin
open BStarCopyGateAuthority BStarOwnerControlHistory BStarResetChartService
open BStarCopyAttemptBand (band_step_exact)
open BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarClearanceSource BStarGeneratedTapeCuts

/-- A real setup receipt gives its exact preceding ISSUE cut, with
generated idle provenance from the same entry and the same raw band. -/
theorem issue_cut {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    {w : List (Fin n)} {op : Nat} {z : Cursor}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy op z))
    (V : LiveAt hp chart x w) :
    ∃ (lead : List (Fin n)) (e : Fin n) (tail : List (Fin n)),
      w=lead++e::tail ∧ GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle lead .idle ∧
      LiveAt hp chart x lead ∧
      Launch ((play x lead) (S.getD 0 fall).1).long ((step (play x lead) e) (S.getD 0 fall).1).long ∧
      e=RearTrace.predecessor (S.getD 0 fall).1 ∧ pc (play x lead) (S.getD 0 fall).1=op ∧
      BusyOnly hp base (fun j=>S.getD j fall) len op (step (play x lead) e) (.out 0) tail z := by
  obtain ⟨lead,tail,e,W,own,L,P,out⟩ := from_idle hp G
  obtain ⟨mode,pre,_⟩ := BStarGeneratedTapeCuts.split hp lead (e::tail) (W ▸ G)
  have now := BStarGeneratedTapeCuts.at_end hp pre
  have modeIdle : mode=.idle := by
    cases mode with
    | idle => rfl
    | busy p z =>
      have wait := now.1.2.2.1
      have phase := L.1.2
      change (ctrlPhase.read ((play x lead) (S.getD 0 fall).1).long).toNat=2 at wait
      change (ctrlPhase.read ((play x lead) (S.getD 0 fall).1).long).toNat=1 at phase
      omega
  subst mode
  exact ⟨lead,e,tail,W,pre,(split_live hp chart (W ▸ V)).1,L,own,P,out⟩

/-- Shift a matching issue state from the post-ACK5 tape back to its
absolute position in the original attempt without altering a mark. -/
theorem ack_issue_replay (x : X) (lead : List (Fin n)) (ack : Fin n)
    (before : List (Fin n)) (issue : Fin n) :
    play (step (play x lead) ack) before=play x ((lead++[ack])++before) ∧
    step (play (step (play x lead) ack) before) issue=
      play x (((lead++[ack])++before)++[issue]) := by
  have E : play (step (play x lead) ack) before=play x ((lead++[ack])++before) := by
    rw [BStarResetSchedule.run_append step x (lead++[ack]) before,
      BStarResetSchedule.run_append step x lead [ack]]
    rfl
  refine ⟨E,?_⟩
  rw [E,BStarResetSchedule.run_append step x ((lead++[ack])++before) [issue]]
  rfl

#print axioms issue_cut
#print axioms ack_issue_replay
end L4.BStarCopySetupReplay
