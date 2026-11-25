import Leader.L4.BStarCopyRightReleaseCursor
import Leader.L4.BStarCopyLaunchEntry
import Leader.L4.BStarCopyRightGeometryWord

namespace L4.BStarCopyRightRecovered
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongCommand BStarLongTransport BStarLongPrep
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarCopyRightStrip BStarCopyRightReleaseClass BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarAcquireHistoryReturn BStarOwnerControlHistory
open BStarClearanceCommandFrame
open BStarSeparatorControl BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightReleaseCapture BStarCopyRightLoadToInject BStarCopyRightDeposit
open BStarClearanceDataChart BStarCommitOperands BStarLongPublication BStarLongDoor
open BStarLongFixedRouting BStarGeneratedBandScan BStarClearanceSource
open BStarCaptureDoorHistory BStarLongLayout

open BStarCopyRightReleaseCursor BStarCopyRightActiveFold BStarCopyRightMixed BStarCopyRightReleaseOrder
open BStarCopyRightRetained BStarCopyRightMark BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarCopyRightGeometryWord BStarCopyRightReturn BStarCopyLaunchEntry

/-- Full recovered right PC10 outward fold on a supplied authenticated
attempt split. Cleanup, gates, and every loaded byte are consequences,
not projection premises. -/
theorem recovered_right_outward {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : tail+1=seam+r)
    (w8 middle tour : List (Fin n))
    (M : OwnMiddle hp base origin (fun t=>S.getD t fall) len w8 middle)
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (w8++middle)) (.out 0) tour (.out len))
    (cut whole : List (Fin n))
    (A : Acquisition hp origin cut whole (endpoint (oldH6 B base) hh o 2).1 2)
    (common : ∃ v,whole=cut++v)
    (sameWhole : ∃ suffix,whole=((w8++middle)++tour)++suffix)
    (ackLead : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (ack2 : ((capturedSelector 2).read (ring (play origin ackLead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play origin A.lead) (endpoint (oldH6 B base) hh o 2).1).long).val)
    (launchAfterAck : ∀ lead issue suffix,
      (∃ rest, w8=(lead++issue::suffix)++rest) →
      issue=RearTrace.predecessor (S.getD 0 fall).1 →
      (ctrlOp.read ((play origin lead) (S.getD 0 fall).1).long).toNat=8 →
      Launch ((play origin lead) (S.getD 0 fall).1).long
        ((ring (play origin lead) issue) (S.getD 0 fall).1).long →
      ∃ beforeIssue m,
        lead=(ackLead++[ack])++beforeIssue ∧
        GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
          .idle beforeIssue m ∧
        (∀ p q,beforeIssue=p++q →
          let y := play origin ((ackLead++[ack])++p)
          Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)))
    (layout : ∀ w,oldH6 B (play origin (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play origin (cut++w)) e z
      (endpoint (oldH6 B base) hh o 2).1)
    (root : Fin n) (dest : Dest B base root r)
    (join : addr a 0=addr root (r-1))
    (lead10 : List (Fin n)) (issue10 : Fin n)
    (preIssue : w8++middle=lead10++[issue10])
    (idle10 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead10 .idle)
    (startPC : pc origin (S.getD 0 fall).1≤6)
    (oldPC : pc (play origin lead10) (S.getD 0 fall).1=10)
    (w9 gap : List (Fin n)) (ack9 : Fin n)
    (enableCut : w8++middle=w9++ack9::gap)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : pc (ring (play origin w9) ack9) (S.getD 0 fall).1=10)
    (full : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle ((w8++middle)++tour) (.busy 10 (.out len)))
    (valid : ∀ u v,((w8++middle)++tour)=u++v →
      (∀ i,Layout B base i=Layout B (play origin u) i) ∧ Band (play origin u) (S.getD 0 fall).1)
    (f : Payload) (F : project (fun j=>S.getD j fall) (play (play origin (w8++middle)) tour) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10) :
    let digits := digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam
    let plan := planOf (fun i=>i-seam) seam tail
    let y := play (play origin (w8++middle)) tour
    ∃ (t : Ledger Nat) (post : Nat→Option Nat), t.release.pending=[] ∧
      OrderedPrefix plan t (stripWord tail post) ∧
      RetainedMatches digits y root r t ∧ MobileMatches digits y a seam tail post := by
  dsimp only
  let lead := w8++middle
  let y := play origin lead
  let digits := digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam
  let atSource := fun i : Nat => i-seam
  have totalEq : ((w8++middle)++tour)=w9++ack9::(gap++tour) := by
    rw [enableCut]
    simp only [List.append_assoc,List.cons_append]
  have scopedValid (u v : List (Fin n)) (E : w9++ack9::(gap++tour)=u++v) := valid u v (totalEq.trans E)
  have gates := right_gates_word hp chart sep w9 (gap++tour) ack9 (.busy 10 (.out len)) G9 event9
    accepted9 (totalEq ▸ full) scopedValid root a r seam tail dest strip join ownHead
  have initialGates : GeometryGates hp base y root a r seam tail := by
    have H := gates gap tour rfl
    rw [←enableCut] at H
    exact H
  have later (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (E : tour=u++e::v) :
      GeometryGates hp base (play y u) root a r seam tail := by
    have H := gates (gap++u) (e::v) (by rw [E,List.append_assoc])
    have tape : w9++ack9::(gap++u)=lead++u := by
      change _=(w8++middle)++u
      rw [enableCut]
      simp only [List.append_assoc,List.cons_append]
    rw [tape,BStarResetSchedule.run_append] at H
    exact H
  have yEq : y=ring (play origin lead10) issue10 := by
    change play origin (w8++middle)=_
    rw [preIssue,BStarResetSchedule.run_append]
    rfl
  have iy : Current hp base (fun j=>S.getD j fall) len y (.busy 10 (.out 0)) := busy_start hp P10
  have clr := launch_drained hp chart sep idle10
    (fun u v E => valid u (v++issue10::tour) (by simp only [preIssue,E,List.append_assoc,List.singleton_append]))
    startPC oldPC (yEq ▸ iy)
  have cleanY : BStarCopyCleanupWindow.DrainedOwner hp base y o.val := yEq.symm ▸ clr
  obtain ⟨first,block⟩ := k2_block hp chart a seam tail strip ownHead
  obtain ⟨P,old,mob,vac,pending⟩ := right_of_drained hp digits atSource chart root a r seam tail first
    initialGates.dest initialGates.strip join ownHead initialGates.same cleanY
  have cap := all_release_bytes hp chart sep a seam tail strip ownHead width w8 middle tour M P10
    (fun q z E => (valid q z E).1) cut whole A common sameWhole ackLead ack birthBeforeAck ack2 launchAfterAck layout auth
  have size : (planOf atSource seam tail).length=r := by simp [planOf]; omega
  exact inject_active_outward_fold hp digits atSource chart sep root a r seam tail first dest strip join ownHead
    block P10 f F clear op size 0 lead _ _ rfl rfl M.end10 P old mob vac pending (fun u e v E => by
      obtain ⟨L,C,U,rg,ug⟩ := later u e v E
      exact ⟨L,C,U,rg,ug,cap u e v E⟩)

#print axioms recovered_right_outward
end L4.BStarCopyRightRecovered
