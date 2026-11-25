import Leader.L4.BStarCopyRightReleaseCapture
import Leader.L4.BStarClearanceCommandFrame

namespace L4.BStarCopyRightReleaseCursor
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

theorem cut_busy {base x : X} {slot : Nat→Pos n} {len op : Nat}
    {start fin : Cursor} (u v : List (Fin n))
    (T : BusyOnly hp base slot len op x start (u++v) fin) :
    ∃ mid,BusyOnly hp base slot len op x start u mid ∧
      BusyOnly hp base slot len op (play x u) mid v fin := by
  induction u generalizing x start with
  | nil => exact ⟨_,.nil (busy_start hp T),T⟩
  | cons e u ih =>
    cases T with
    | cons I E rest =>
      obtain ⟨m,F,G⟩ := ih rest
      exact ⟨m,.cons I E F,G⟩

private theorem bind_forward (g : LongGeometry) (j : Fin 11) (t : Token) (q : Payload)
    (H : BStarLongCommand.bind g j t=.forward q) : anyTag.F t := by
  cases t with
  | empty => cases H
  | trail => cases H
  | forward p => exact ⟨p,rfl⟩
  | reply p =>
    simp only [BStarLongCommand.bind] at H
    split at H
    · cases H
    · split at H <;> cases H

/-- A ReleaseAt's selected literal old offer authenticates the cursor
even if the mark was passed at an existential intermediate mode.
No mode label or pointer equality is supplied by the caller. -/
theorem release_cursor {base x : X} {S : List (Pos n)} {fall : Pos n} {len seam tail : Nat}
    {a e : Fin n} {m : Mode} {z : Cursor}
    (A : Current hp base (fun j=>S.getD j fall) len x (.busy 10 z))
    (R : ReleaseAt hp x e a seam tail (fun j=>S.getD j fall) len m) :
    z=.out R.k := by
  obtain ⟨c,f,C,F⟩ := R.advance
  obtain ⟨q,Q⟩ := advance_origin (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) c f F
  rw [C] at Q
  have h : anyTag.F (atSite (x e).long 2) :=
    bind_forward (oldPair B x e).1 2 (atSite (x e).long 2) q Q
  have here : anyTag.F (project (fun j=>S.getD j fall) x R.k) := by
    change anyTag.F (BStarAcquireForwardTrace.atCursor x (S.getD R.k fall))
    rw [R.ptr,←R.markAt]
    exact h
  cases z with
  | out k =>
    have eq := (pointed_unique_forward _ len k A.2.1 A.2.2 _ (Nat.le_of_lt R.strict)).mp here
    rw [eq]
  | back k =>
    exact (pointed_backward_no_forward _ len k A.2.1 _ (Nat.le_of_lt R.strict) here).elim

open BStarCopyRightReleaseCapture BStarCopyRightLoadToInject BStarCopyRightDeposit
open BStarClearanceDataChart BStarCommitOperands BStarLongPublication BStarLongDoor
open BStarLongFixedRouting BStarGeneratedBandScan BStarClearanceSource
open BStarCaptureDoorHistory BStarLongLayout

theorem all_release_bytes {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : tail+1=seam+r)
    (w8 middle tour : List (Fin n)) {fin : Cursor}
    (M : OwnMiddle hp base origin (fun t=>S.getD t fall) len w8 middle)
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (w8++middle)) (.out 0) tour fin)
    (fiber : ∀ q z, ((w8++middle)++tour)=q++z →
      ∀ i,Layout B base i=Layout B (play origin q) i)
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
      (endpoint (oldH6 B base) hh o 2).1) :
    ∀ u e v,tour=u++e::v →
      ∀ m (R : ReleaseAt hp (play (play origin (w8++middle)) u) e a seam tail (fun j=>S.getD j fall) len m),
      (lanes (play (play origin (w8++middle)) u) (addr a R.i) .rs).frozen=
        .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam (R.i-seam)) := by
  intro u e v E
  obtain ⟨cursor,P,_⟩ := cut_busy hp u (e::v) (E ▸ P10)
  have exactAt (y : X) (Y : y=play origin ((w8++middle)++u)) :
      ∀ m (R : ReleaseAt hp y e a seam tail (fun j=>S.getD j fall) len m),
      Current hp base (fun j=>S.getD j fall) len y (.busy 10 cursor) →
      (lanes y (addr a R.i) .rs).frozen=
        .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam (R.i-seam)) := by
    subst y
    intro m R cur
    have pos := release_cursor hp cur R
    have cl := P
    rw [pos] at cl
    apply release_bytes hp chart sep a seam tail strip ownHead width w8 middle u e m R M cl _ cut whole A common _
      ackLead ack birthBeforeAck ack2 launchAfterAck layout auth
    · intro q z D
      apply fiber q (z++e::v)
      exact (congrArg ((w8++middle)++·) E).trans
        ((List.append_assoc _ u _).symm.trans (by rw [D,List.append_assoc]))
    · obtain ⟨z,W⟩ := sameWhole
      refine ⟨(e::v)++z,?_⟩
      rw [W]
      exact congrArg (· ++ z) ((congrArg ((w8++middle)++·) E).trans (List.append_assoc _ u _).symm) |>.trans
        (List.append_assoc _ _ _)
  exact fun m R => exactAt _ (BStarResetSchedule.run_append _ _ _ _).symm m R (busy_end hp P)

#print axioms all_release_bytes
#print axioms release_cursor
end L4.BStarCopyRightReleaseCursor
