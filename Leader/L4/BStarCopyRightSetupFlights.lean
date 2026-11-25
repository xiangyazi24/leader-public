import Leader.L4.BStarCopySetupCuts
import Leader.L4.BStarCopyRightRecoveryTwoOrigin
import Leader.L4.BStarCopyRightInjectPositive

namespace L4.BStarCopyRightSetupFlights
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarClearanceSource
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail BStarNativeReceiptTape
open BStarAcquireAckAncestry BStarAcquireHistoryReturn BStarCopyEnableTerminal

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- The PC10 Found/Hit pair of original_setup yields one actual
ISSUE, outward prefix with its healthy terminal, and returning suffix.
The terminal and launch are not separately supplied cuts. -/
theorem flight10_of_setup {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {ack : Fin n}
    (F : Found hp base (fun j=>S.getD j fall) len 10 x w (.back 0))
    (H : Hit hp base (fun j=>S.getD j fall) len (play x w) ack 10) :
    ∃ (pre out back : List (Fin n)) (issue turn : Fin n) (f : Payload),
      w=(pre++issue::out)++turn::back ∧
      let root := (S.getD 0 fall).1
      let y := ring (play x pre) issue
      let old := play y out
      let last := play (ring old turn) back
      issue=RearTrace.predecessor root ∧
      pc (play x pre) root=10 ∧
      Launch ((play x pre) root).long (y root).long ∧
      BusyOnly hp base (fun j=>S.getD j fall) len 10 y (.out 0) out (.out len) ∧
      project (fun j=>S.getD j fall) old len=.forward f ∧ f.fault=0 ∧ f.opcode.toNat=10 ∧
      Event hp (fun j=>S.getD j fall) len old turn (.busy 10 (.out len)) (.busy 10 (.back len)) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len 10 (ring old turn) (.back len) back (.back 0) ∧
      Event hp (fun j=>S.getD j fall) len last ack (.busy 10 (.back 0)) .idle ∧
      pc (ring last ack) root=11 := by
  obtain ⟨lead,turn,back,W,launch,turning,returning⟩ := found_split_turn hp F
  obtain ⟨pre,out,issue,L,door,issued,pc10,flight⟩ := launch
  have eq : play x lead=play (ring (play x pre) issue) out := by
    rw [L,BStarResetSchedule.run_append]
    rfl
  have received : play x w=play (ring (play x lead) turn) back := by
    rw [W,BStarResetSchedule.run_append]; rfl
  obtain ⟨ans,read,healthy,op⟩ := H.2.2.2.2.2
  rw [received] at read
  obtain ⟨f,raw,clean,precise⟩ := terminal_old_healthy hp chart sep turn back 10
    (eq.symm ▸ busy_end hp flight) returning ans healthy (by rw [op]; decide) read
  refine ⟨pre,out,back,issue,turn,f,W.trans (congrArg (·++turn::back) L),door,pc10,issued,flight,
     eq ▸ raw,clean,(congrArg BitVec.toNat precise).trans op,eq ▸ turning,eq ▸ returning,?_,?_⟩
  · have E := H.2.1
    rw [received,eq] at E
    exact E
  · have pc11 := H.2.2.2.1
    rw [received,eq] at pc11
    exact pc11

#print axioms flight10_of_setup
end L4.BStarCopyRightSetupFlights
