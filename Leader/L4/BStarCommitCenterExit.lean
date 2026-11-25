import Leader.L4.BStarCommitNoPrior
import Leader.L4.BStarCommitHealthyFlight
import Leader.L4.BStarSealOwnerFrame

namespace L4.BStarCommitCenterExit
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireHistorySample
open BStarSeparatorControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A selected center departure writes TRAIL independently of whether
the outgoing handler accepts or refuses its publication. -/
theorem selected_center_leaves (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (p : Payload)
    (selected : (centerLink (oldPair B x e),.advance p)∈
      actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    atCursor (step x e) (e,1)=.trail := by
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  let C := centerLink g
  let d : AtK := R (if g.2.axes.h6 then 2 else 1)
  have dst : C.destination=some d := rfl
  have ne := (BStarAcquireReturn.link_shape g C d (center_mem g) dst).1
  have T := (BStarClearanceForward.move_lands g raw C p d dst selected (Ne.symm ne)).1
  let pair := (x e,x (rightNeighbor e))
  have J := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp pair C.source
    (fun hr _ => (by change Side.left=Side.right at hr; contradiction))
  change atCursor (step x e) (address e C.source)=_
  rw [←new_read B x e sep C.source,J]
  change decode (readRaw (patchPair (longWork g raw) raw) C.source)=_
  rw [T,decode_encode]

/-- A generated busy suffix ending at the same outward center cannot
begin with its selected outgoing mark. This isolates the exact skipped
mark fact needed when the owner is waiting for center service. -/
theorem no_selected_mark_before_end {base x : X} {addr : Nat → Pos n}
    {len op k : Nat} {v : List (Fin n)} {e : Fin n}
    (sep : e≠rightNeighbor e) (idx : addr k=(e,1)) (p : Payload)
    (selected : (centerLink (oldPair B x e),.advance p)∈
      actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    ¬BusyOnly hp base addr len op x (.out k) (e::v) (.out k) := by
  intro busy
  cases busy with
  | cons I E tail =>
    obtain ⟨j,J⟩ := busy_no_back_to_out hp tail ⟨k,rfl⟩
    have M : j≤k := BStarCommitNoPrior.outward_mono hp tail j k J rfl
    have A : Advance len (.out k) (.out j) := by
      rw [←J]
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ finish => cases finish; exact A
    have eq : j=k := by cases A <;> omega
    have next := busy_start hp tail
    rw [J,eq] at next
    have F := next.2.1.2.1
    change anyTag.F (atCursor (step x e) (addr k)) at F
    rw [idx,selected_center_leaves hp x e sep p selected] at F
    exact BStarSeparatorParked.forward_not_trail F

open BStarLongCommand BStarLongDoor BStarResetControllerEntry BStarClearanceSource

local notation "play" => BStarResetSchedule.run step

private theorem split_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {z endC : Cursor} (T : BusyOnly hp base addr len op x z w endC) :
    ∀ u v,w=u++v → ∃ t, BusyOnly hp base addr len op x z u t ∧
      BusyOnly hp base addr len op (play x u) t v endC := by
  induction T with
  | nil I =>
    intro u v S
    have E := List.append_eq_nil_iff.mp S.symm
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,.nil I,.nil I⟩
  | @cons x z t endC e w I E T ih =>
    intro u v S
    cases u with
    | nil =>
      change e::w=v at S
      subst v
      exact ⟨_,.nil I,.cons I E T⟩
    | cons a u =>
      obtain ⟨rfl,P⟩ := List.cons.inj S
      obtain ⟨m,U,V⟩ := ih u v P
      exact ⟨m,.cons I E U,V⟩

/-- The literal launched COMMIT's entire precenter word excludes
latch-changing selection on actual outgoing center marks. The owner
can already be waiting at that cursor on other labels. -/
theorem outgoing_modes_before_center {base start : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door i : Fin n) (w : List (Fin n)) (k : Nat) (L : k<len)
    (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (pc : (ctrlOp.read (start (S.getD 0 fall).1).long).toNat=commitOp)
    (launch : Launch (start (S.getD 0 fall).1).long ((step start door) (S.getD 0 fall).1).long)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step start door) (.out 0) w (.out k)) :
    ∀ u v,w=u++i::v → ∃ z,
      Current hp base (fun j=>S.getD j fall) len (play (step start door) u) (.busy commitOp z) ∧
      BStarSealOwnerFrame.Excluded k (.busy commitOp z) := by
  intro u v E
  obtain ⟨z,U,V⟩ := split_busy hp T u (i::v) E
  refine ⟨z,busy_start hp V,?_⟩
  intro op _ impossible
  have Z := (Mode.busy.inj impossible).2
  subst z
  obtain ⟨p,_,selected⟩ := BStarCommitHealthyFlight.selected_at_center hp C sep door i u k L
    idx head pc launch U
  exact no_selected_mark_before_end hp (sep i) idx p selected V

#print axioms selected_center_leaves
#print axioms no_selected_mark_before_end
#print axioms outgoing_modes_before_center
end L4.BStarCommitCenterExit
