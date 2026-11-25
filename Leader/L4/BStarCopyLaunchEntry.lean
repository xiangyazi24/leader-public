import Leader.L4.BStarCopyCleanupOriginal
import Leader.L4.BStarCopyRightActiveEntry
import Leader.L4.BStarCopyLeftRetained

namespace L4.BStarCopyLaunchEntry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarClearanceDataChart
open BStarResetMarkAdapter BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin
open BStarCopyCleanupFrame BStarCopyCleanupCoverage BStarCopyEntryGates BStarCopyGateAuthority

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarCopyAttemptBand BStarGeneratedTapeCuts BStarCopyDrainedHistory BStarCopyCleanupWindow
open BStarSeparatingRail BStarResetChartService BStarSeparatorControl BStarResetControllerEntry BStarOwnerControlHistory

open BStarCopyCleanupOriginal BStarCopyDrainedHistory BStarCopyCleanupWindow
open BStarCopyActiveVacancy BStarGeneratedTapeCuts BStarCopyRightActiveEntry
open BStarCopyRightStrip BStarCopyRightReady BStarCopyRightAuthority BStarCopyRightReleaseOrder
open BStarCopyMarkedLedger BStarCopyFIFO BStarCopyFenceSaturation BStarCopyRightMixed
open BStarCopyRightMark (MobileMatches stripWord)
open BStarCopyRightRetained (Dest RetainedMatches)

theorem launch_drained {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {e : Fin n}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (valid : ∀ a b,w=a++b →
      (∀ i, Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1≤6) (done : pc (play x w) (S.getD 0 fall).1=10)
    (post : Current hp base (fun j => S.getD j fall) len (step (play x w) e) (.busy 10 (.out 0))) :
    DrainedOwner hp base (step (play x w) e) o.val := by
  have old := BStarGeneratedTapeCuts.at_end hp G
  have ly := (valid w [] (List.append_nil _).symm).1
  apply drained_step hp e (sep e) o.val ly post.1.1
    (drained_original_issue10 hp chart sep G valid init done)
  intro a win own
  have Q := BStarCopyOwnedFrozen.safe_idle hp chart ly e
    (site e a.claim.lane.side) a.claim.lane.occurrence own old.2
  have K : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
  rcases Q a.claim.lane.side rfl a win K with H|H|H <;> rw [H] <;> decide

theorem right_of_drained {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (root a : Fin n) (width seam tail first : Nat)
    (C : Dest B y root width) (U : Strip B y a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (layout : ∀ i, Layout B base i=Layout B y i)
    (clean : DrainedOwner hp base y o.val) :
    let plan := planOf atSource seam tail
    let s := Ledger.init plan
    let lab : Nat → Option Tag := fun _ => none
    OrderedPrefix plan s (stripWord tail lab) ∧
    RetainedMatches digits y root width s ∧ MobileMatches digits y a seam tail lab ∧
    ActiveCutVacant hp y S fall len 0 true ∧
    s.release.pending=PendingAt atSource seam tail first 0 := by
  have same : oldH6 B base=oldH6 B y := funext fun i => congrArg Prod.fst (layout i)
  have baseRD : rail seam 0=.rd := if_pos U.seam_pos
  apply initial_right hp digits atSource chart root a width seam tail first C U join own layout
  · exact fun i sh active id => (clean i sh active id).1
  · intro j jL
    have owner := dest_owner hp root width C j jL
    rw [←join,←same,←baseRD] at owner
    exact (clean _ .rd rfl (baseRD ▸ owner.trans own)).2

open BStarCopyLeftMark (UpstreamMatches sample upstreamWord)
open BStarCopyLeftDeposit (headFirst)
open BStarCopyLeftStrip in
theorem left_of_drained {Tag : Type} (digits : Tag→BitVec 36) (plan : List Tag)
    {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (root a : Fin n) (width seam : Nat)
    (D : Dest B y root width)
    (upOwner : ∀ j<seam, dataOwner (oldH6 B base) (addr a j) .ls=o.val)
    (downOwner : ∀ j<width, dataOwner (oldH6 B base) (addr root j) .ld=o.val)
    (clean : DrainedOwner hp base y o.val) :
    let s := Ledger.init plan
    let lab : Nat→Option Tag := fun _ => none
    OrderedPrefix plan s (headFirst seam lab) ∧
    BStarCopyLeftRetained.RetainedMatches digits y root width s ∧
    UpstreamMatches digits y a seam lab ∧ ActiveCutVacant hp y S fall len 0 false := by
  dsimp only
  refine ⟨?_,?_,?_,active_from_owner_empty hp chart false (fun i sh A O => (clean i sh A O).1)⟩
  · suffices headFirst seam (fun _ => none : Nat→Option Tag)=[] by rw [this]; exact .init
    simp [headFirst,upstreamWord,List.flatMap_eq_nil_iff]
  · intro j hj
    exact clean _ .ld (D.inside j hj) (downOwner j hj)
  · intro j hj
    change (readLane (Sheet.index (BStarCopyLeftStrip.rail seam j)) (y (addr a j)).long).mobile=.empty
    rw [show BStarCopyLeftStrip.rail seam j=.ls from if_pos hj]
    exact (clean _ .ls rfl (upOwner j hj)).1

end L4.BStarCopyLaunchEntry
