import Leader.L4.BStarCopyFenceCuts
import Leader.L4.BStarCopyLeftReleaseCursor
import Leader.L4.BStarCopyLeftGeometryWord
import Leader.L4.BStarCopyLaunchEntry
import Leader.L4.BStarCopyLeftFenceHold

namespace L4.BStarCopyLeftRecovered
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarClearanceSource BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarH6Ordinal
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNativeReceiptTape BStarGeneratedTapeCuts BStarAcquireHistoryReturn
open BStarCopyRightStrip (addr)
open BStarClearanceDataChart
open BStarCopyLeftStrip BStarCopyLeftReleaseClass BStarCopyLeftReleaseOrder BStarCopyLeftMark
open BStarCopyLeftReturn BStarCopyLeftGeometryWord BStarCopyLeftRetained
open BStarCopyLeftPending BStarCopyLeftInjectFold BStarCopyLeftDeposit BStarCopyLeftFence
open BStarCopyMarkedLedger BStarCopyFenceSaturation BStarCopyLaunchEntry
open BStarCopyLeftFenceHold BStarCopyLeftDataSweep BStarLongPackets BStarCopyFenceCuts

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- Start at the post-ACQUIRE recovered compiler entry. The exact
original captured table may be proved on a longer origin prefix.
All physical initialization and old gate scope are derived here. -/
theorem recovered_left_outward {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (digits : Nat→BitVec 36) (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (root : a=(S.getD 0 fall).1) (ws : width≤seam)
    (flag : ∀ j<seam,(longGeometry B (base (addr a j))).inside=true ↔ j<width)
    (start tour lead10 : List (Fin n)) (issue10 : Fin n)
    (preIssue : start=lead10++[issue10])
    (idle10 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead10 .idle)
    (startPC : pc origin (S.getD 0 fall).1≤6)
    (oldPC : pc (play origin lead10) (S.getD 0 fall).1=10)
    (Gstart : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle start (.busy 10 (.out 0)))
    (P10 : BusyOnly hp base (fun j=>S.getD j fall) len 10
      (play origin start) (.out 0) tour (.out len))
    (w9 gap : List (Fin n)) (ack9 : Fin n)
    (enableCut : start=w9++ack9::gap)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : pc (ring (play origin w9) ack9) (S.getD 0 fall).1=10)
    (full : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (start++tour) (.busy 10 (.out len)))
    (valid : LiveAt hp chart origin (start++tour))
    (f : Payload) (F : project (fun j=>S.getD j fall) (play (play origin start) tour) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10)
    (cap : ∀ u e v,tour=u++e::v →
      ∀ m (R : ReleaseAt hp (play (play origin start) u) e a seam (fun j=>S.getD j fall) len m),
      (sample (play (play origin start) u) a seam R.i).frozen=.data (digits R.i)) :
    let plan := pending id width
    let y := play (play origin start) tour
    ∃ t : Ledger Nat, ∃ labels : Nat→Option Nat,
      t.release.pending=[] ∧ OrderedPrefix plan t (headFirst seam labels) ∧
      RetainedMatches digits y (addr a seam) width t ∧ UpstreamMatches digits y a seam labels := by
  dsimp only
  let y := play origin start
  let plan := pending (id : Nat→Nat) width
  have totalEq : start++tour=w9++ack9::(gap++tour) := by
    rw [enableCut]
    simp only [List.append_assoc,List.cons_append]
  have G := left_gates_word hp chart sep w9 (gap++tour) ack9 (.busy 10 (.out len))
    G9 event9 accepted9 (totalEq ▸ full) (fun u v E=>valid u v (totalEq.trans E))
    a seam width strip root
  have initial : GeometryGates hp base y a seam width := by
    have H := G gap tour rfl
    rw [←enableCut] at H
    exact H
  have later (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (E : tour=u++e::v) :
      GeometryGates hp base (play y u) a seam width := by
    have H := G (gap++u) (e::v) (by rw [E,List.append_assoc])
    have tape : w9++ack9::(gap++u)=start++u := by
      rw [enableCut]
      simp only [List.append_assoc,List.cons_append]
    rw [tape,BStarResetSchedule.run_append] at H
    exact H
  have yEq : y=ring (play origin lead10) issue10 := by
    change play origin start=_
    rw [preIssue,BStarResetSchedule.run_append]
    rfl
  have iy : Current hp base (fun j=>S.getD j fall) len y (.busy 10 (.out 0)) := busy_start hp P10
  have clr := launch_drained hp chart sep idle10
    (fun u v E=>valid u (v++issue10::tour) (by simp only [preIssue,E,List.append_assoc,List.singleton_append]))
    startPC oldPC (yEq ▸ iy)
  have cleanY : BStarCopyCleanupWindow.DrainedOwner hp base y o.val := yEq.symm ▸ clr
  have owned := BStarCopyLeftReadyWord.all_owner hp chart a seam width strip root
  have up : ∀ j<seam,dataOwner (oldH6 B base) (addr a j) .ls=o.val :=
    fun j J => by simpa [rail,J] using owned j (by omega)
  have ld : ∀ j<width,dataOwner (oldH6 B base) (addr (addr a seam) j) .ld=o.val := by
    intro j J
    rw [address_add]
    simpa [rail,show ¬seam+j<seam by omega] using owned (seam+j) (by omega)
  obtain ⟨P,old,mob,vac⟩ := left_of_drained hp digits plan chart (addr a seam) a width seam
    (dest_of_strip hp y a seam width initial.strip) up ld cleanY
  obtain ⟨end5,es,K⟩ := k5_ordinal hp chart a seam width 0 strip root strip.seam_pos
  have aft : width≤end5+1 := by
    have F := affine_chart hp chart a seam width end5 strip root es K (seam-1) (by have := strip.seam_pos; omega)
    omega
  have pend : (Ledger.init plan).release.pending=pending id (remaining end5 width (.out 0)) := by
    change plan=pending id (min width (end5+1-0))
    rw [Nat.sub_zero,Nat.min_eq_left aft]
  have size : plan.length=width := by simp [plan,pending]
  exact inject_outward_fold hp digits id chart sep a seam width end5 strip root es K ws flag
    P10 f F clear op plan size 0 start (Ledger.init plan) (fun _=>none) rfl rfl Gstart P old mob
    (cutVacant_of_active hp y S fall len 0 vac) pend (fun u e v E => by
      obtain ⟨L,C,DL,LS⟩ := later u e v E
      exact ⟨L,C,DL,LS,cap u e v E⟩)

#print axioms recovered_left_outward
end L4.BStarCopyLeftRecovered
