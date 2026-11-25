import Leader.L4.BStarCopyRightWrappedReleaseClass
import Leader.L4.BStarCopyLaunchEntry
import Leader.L4.BStarCopyRightActiveFold
import Leader.L4.BStarCopyRightReady

namespace L4.BStarCopyRightWrappedEntry
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarLongPackets BStarLongPrep BStarAcquireVisitOrder BStarResetChartTouch
open BStarCopyRightStrip BStarCopyRightMark BStarCopyRightRetained BStarCopyRightReady
open BStarCopyRightAuthority BStarCopyRightReleaseOrder BStarCopyMarkedLedger BStarCopyFIFO
open BStarCopyFenceSaturation BStarCopyActiveVacancy BStarClearanceDataChart
open BStarCopyRightMixed BStarAcquireLiteralChain

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- An empty owned active mobile projection starts the fresh right tag
word. Empty retained destinations are a separate literal cut fact;
nothing is required of inactive RS bytes or irrelevant retained slots. -/
theorem initial_right {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (root a : Fin n) (width seam tail first : Nat)
    (C : Dest B x root width) (U : BStarCopyRightWrappedGeometry.WrappedStrip B x a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (layout : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (mobile : ActiveOwnerEmpty hp base x o.val)
    (retained : ∀ j<width,(readLane (Sheet.index .rd) (x (addr root j)).long).retained=.empty) :
    let plan := planOf atSource seam tail
    let s := Ledger.init plan
    let lab : Nat → Option Tag := fun _ => none
    OrderedPrefix plan s (stripWord tail lab) ∧
    RetainedMatches digits x root width s ∧ MobileMatches digits x a seam tail lab ∧
    ActiveCutVacant hp x S fall len 0 true ∧
    s.release.pending=PendingAt atSource seam tail first 0 := by
  have same : oldH6 B base=oldH6 B x := by
    funext i
    exact congrArg Prod.fst (layout i)
  have baseRD : rail seam 0=.rd := if_pos U.seam_pos
  dsimp only
  refine ⟨?_,?_,?_,active_from_owner_empty hp chart true mobile,?_⟩
  · suffices stripWord tail (fun _ => none : Nat→Option Tag)=[] by
      rw [this]
      exact .init
    simp [stripWord,List.flatMap_eq_nil_iff]
  · intro j jL
    have owner := dest_owner hp root width C j jL
    rw [←join,←same,←baseRD] at owner
    refine ⟨?_,retained j jL⟩
    exact mobile _ .rd rfl (baseRD ▸ owner.trans own)
  · intro j jP jT
    have owner := BStarCopyRightWrappedReleaseClass.strip_same_owner U j jT
    rw [←same] at owner
    apply mobile _ _ _ (owner.trans own)
    by_cases H : j<seam
    · rw [show rail seam j=.rd from if_pos H]; rfl
    · rw [show rail seam j=.rs from if_neg H]
      exact U.rs_in _ (by omega) jT
  · exact (pending_initial atSource seam tail first).symm

open BStarCopyLaunchEntry BStarCopyCleanupOriginal BStarCopyCleanupWindow

theorem right_of_drained {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (root a : Fin n) (width seam tail first : Nat)
    (C : Dest B y root width) (U : BStarCopyRightWrappedGeometry.WrappedStrip B y a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (layout : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B y i)
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

#print axioms initial_right
#print axioms right_of_drained
end L4.BStarCopyRightWrappedEntry
