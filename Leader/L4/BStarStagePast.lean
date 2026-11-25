import Leader.L4.BStarStageCandidateRetention
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarCommitNoPrior

namespace L4.BStarStagePast
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting BStarLongCommand
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireRailCoverage BStarAcquireAnchors
open BStarStageCandidateRetention BStarBankTrace BStarStageProvenance
open BStarLongFiberOwner
open BStarResetSchedule BStarSeparatorControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The actual legal center departure, including STAGE, leaves a
literal T behind on the same packed old center K1. -/
theorem departure_trail (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (p : Payload)
    (sel : (C,.advance p)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (center : C.source.occurrence.val=1) :
    C.source=L 1 ∧ atCursor (step x e) (e,1)=.trail := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have hm : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have CK := center_of g C hm center
  have src : C.source=L 1 := by rw [CK]; rfl
  refine ⟨src,?_⟩
  let d : AtK := R (if g.2.axes.h6 then 2 else 1)
  have dst : C.destination=some d := by rw [CK]; rfl
  have ne := (BStarAcquireReturn.link_shape g C d hm dst).1
  have T := (BStarClearanceForward.move_lands g raw C p d dst sel (Ne.symm ne)).1
  have J := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source
      (fun hr _ => (by rw [src] at hr; contradiction))
  have h : address e C.source=(e,1) := by rw [src]; rfl
  rw [←h,←new_read B x e sep C.source,J]
  change decode (readRaw (patchPair (longWork g raw) raw) C.source)=_
  rw [T,BStarLongToken.decode_encode]

def Past (k : Nat) : Cursor → Prop
  | .out j => k<j
  | .back _ => True

private theorem single {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ t _ tail => cases tail; exact t

private theorem past_event {x : X} {addr : Nat → Pos n} {len op k : Nat}
    {e : Fin n} {z d : Cursor} (P : Past k z)
    (E : Event hp addr len x e (.busy op z) (.busy op d)) :
    Past k d := by
  cases E with
  | transit _ _ _ _ seen =>
    cases (single hp seen)
    · exact P
    · unfold Past at *; omega
    · exact True.intro
    · exact True.intro
  | arrived_hold _ => exact True.intro

/-- On a generated STAGE tour, the only possible write to an owner's
tracked K1 is when the outward cursor is exactly its ordinal. -/
theorem excludes_stage_at {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (e i : Fin n) (k : Nat) (hk : k≤len) (addr : S.getD k fall=(i,1))
    (no : m≠.busy stageOp (.out k)) :
    RingNoStage hp (run x w) e i := by
  intro s loc K p sel hs hj hf ho
  have idx : address e K.source=(i,1) :=
    Prod.ext ((congrArg (site e) hs).trans loc.symm) (Fin.ext hj)
  have A := BStarBodyStageProvenance.selected_descriptor hp C sep P now k hk e K p
    (addr.trans idx.symm) sel ⟨hf,ho⟩
  exact no A.1

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (run x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

/-- All subsequent marks in this same busy STAGE tour keep the bank
after its actual physical K1 departure. The old mark's trail proves
this was not a stay. The rest may include the return trip. -/
theorem busy_keeps_after_departure {base origin x : X}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead : List (Fin n)) (xOld : x=run origin lead)
    (e : Fin n) (k : Nat) (hk : k≤len) (idx : S.getD k fall=(e,1))
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle lead (.busy stageOp (.out k)))
    (C : CommandClaim) (p : Payload)
    (selected : (C,.advance p)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (center : C.source.occurrence.val=1)
    {z d : Cursor} {w : List (Fin n)}
    (E : Event hp (fun j => S.getD j fall) len x e (.busy stageOp (.out k)) (.busy stageOp z))
    (tail : BusyOnly hp base (fun j => S.getD j fall) len stageOp (step x e) z w d)
    (b : Fin 3) :
    BankAt b (run (step x e) w e).long=BankAt b (step x e e).long := by
  subst x
  let addr := fun j => S.getD j fall
  have T := (departure_trail hp _ e (sep e) C p selected center).2
  have Q : Advance len (.out k) z := by
    cases E with
    | transit _ _ _ _ seen => exact single hp seen
  have past : Past k z := by
    cases Q with
    | turn => exact True.intro
    | forward => exact Nat.lt_succ_self _
    | stay =>
      have next := (busy_start hp tail).2.1.2.1
      change anyTag.F (atCursor (step (run origin lead) e) (S.getD k fall)) at next
      rw [idx,T] at next
      exact (BStarSeparatorParked.forward_not_trail next).elim
  have stepRetains : ∀ (path : List (Fin n)) (y : X) (c f : Cursor) (tape : List (Fin n)),
      y=run origin path →
      GeneratedOwner hp base addr len origin .idle path (.busy stageOp c) →
      BusyOnly hp base addr len stageOp y c tape f → Past k c →
      BankAt b (run y tape e).long=BankAt b (y e).long := by
    intro path y c f tape Y G H
    induction H generalizing path with
    | nil => intro _; rfl
    | @cons y c f endC mark tape I EV tail ih =>
      intro past
      have M : RingNoStage hp y mark e := by
        rw [Y]
        apply excludes_stage_at hp chart sep G (Y ▸ I) mark e k hk idx
        intro eq
        have eq' : c=.out k := (Mode.busy.inj eq).2
        rw [eq'] at past
        exact Nat.lt_irrefl _ past
      have now := ring_keeps hp y mark e (sep mark) b M
      have Y' : step y mark=run origin (path++[mark]) := by
        rw [BStarResetSchedule.run_append,←Y]; rfl
      have G' := generated_append hp G
        (Y ▸ GeneratedOwner.next I EV (.endpoint (busy_start hp tail)))
      exact (ih (path++[mark]) Y' G' (past_event hp past EV)).trans now
  have G' := generated_append hp P
    (GeneratedOwner.next (BStarGeneratedTapeCuts.at_end hp P) E (.endpoint (busy_start hp tail)))
  exact stepRetains (lead++[e]) _ _ _ _ (by rw [BStarResetSchedule.run_append]; rfl) G' tail past

#print axioms departure_trail
#print axioms busy_keeps_after_departure
end L4.BStarStagePast
