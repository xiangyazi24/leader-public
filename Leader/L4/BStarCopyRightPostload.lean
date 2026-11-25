import Leader.L4.BStarCopyRightPreinject

namespace L4.BStarCopyRightPostload
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarCopyOperand BStarCopyRightCapture BStarCopyRightK2Past
open BStarAcquireVisitOrder BStarOwnerLaunchOrigin BStarGeneratedOwner BStarAcquireForwardTrace
open BStarResetChartTouch BStarResetChartIndex BStarClearanceDataChart BStarAcquireAnchors
open BStarSeparatingRail BStarAcquireHistorySample BStarResetSchedule BStarResetMarkAdapter
open BStarAcquireLiteralChain BStarLongEvents BStarLongToken BStarCopyOwnedFrozen BStarSeparatorControl BStarResetQuiet

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

def Past (k : Nat) : Cursor → Prop
  | .out j => k<j
  | .back _ => True

private theorem single {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen ring (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ on _ tail => cases tail; exact on

private theorem past_event {x : X} {addr : Nat→Pos n} {len op k : Nat}
    {e : Fin n} {z d : Cursor} (old : Past k z)
    (E : Event hp addr len x e (.busy op z) (.busy op d)) : Past k d := by
  cases E with
  | transit _ _ _ _ N =>
    cases single hp N
    · exact old
    · unfold Past at *; omega
    · exact True.intro
    · exact True.intro
  | arrived_hold _ => exact True.intro

/-- The actual selected K2 LOAD leaves a Trail. This authenticates
strict past immediately after the genuine LOAD mark, allowing all
same-attempt follow-up labels without a no-revisit hook. -/
theorem load_enters_past {base x : X} {addr : Nat→Pos n} {len k : Nat}
    (e : Fin n) (sep : e≠rightNeighbor e) (C : CommandClaim) (f : Payload)
    (K : C.source.occurrence=2) (atK : address e C.source=addr k)
    (selected : (C,.advance f)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    {z : Cursor}
    (E : Event hp addr len x e (.busy 8 (.out k)) (.busy 8 z))
    (next : Current hp base addr len (ring x e) (.busy 8 z)) :
    Past k z := by
  have A : Advance len (.out k) z := by
    cases E with
    | transit _ _ _ _ N => exact single hp N
  cases A with
  | turn => exact True.intro
  | forward => exact Nat.lt_succ_self _
  | stay =>
    have T := k2_departure_trail hp x e sep C f selected K
    have fwd := next.2.1.2.1
    change anyTag.F (atCursor (ring x e) (addr k)) at fwd
    rw [←atK,T] at fwd
    exact (BStarSeparatorParked.forward_not_trail fwd).elim

/-- PC8 after the one addressed LOAD and all PC9 busy marks preserve
the same frozen source. PC8 uses actual Past, PC9 needs no cursor
exclusion, and returns are safe on every mark. -/
theorem frozen_busy_suffix {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (kl : k≤len)
    (atSource : S.getD k fall=(i,2))
    (own : dataOwner (oldH6 B base) i .rs=o.val)
    (op : Nat) (opBand : op=8 ∨ op=9)
    (lead : List (Fin n)) {x : X} {z d : Cursor} {w : List (Fin n)}
    (old : x=play origin lead)
    (history : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy op z))
    (busy : BusyOnly hp base (fun t => S.getD t fall) len op x z w d)
    (past : op=8 → Past k z)
    (layout : ∀ a e b, w=a++e::b →
      ∀ j, BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (play x a) j) :
    (readLane (Sheet.index .rs) (play x w i).long).frozen=
      (readLane (Sheet.index .rs) (x i).long).frozen := by
  induction busy generalizing lead with
  | nil => rfl
  | @cons x z d fin e w I ev tail ih =>
    have same := layout [] e w rfl
    have F : FrozenSafe hp x e i .rs := by
      cases z with
      | back j => exact safe_returning hp chart same e i .rs j own I.2.1
      | out j =>
        have N : ∀ h : op≠9, S.getD j fall≠(i,2) := by
          intro H E
          have eq8 := opBand.resolve_right H
          have le := I.2.1.1
          have eq := (List.getD_inj (by have := chart.length; omega)
            (by have := chart.length; omega) chart.nodup).mp (E.trans atSource.symm)
          subst j
          exact Nat.lt_irrefl _ (past eq8)
        rw [old]
        exact rs_frozen_outward hp chart sep history (old ▸ I) (old ▸ same)
          e i own (by omega) (by omega) N
    have frame := ring_frozen_frame hp x e i .rs (sep e) F
    have newly : ring x e=play origin (lead++[e]) := by
      rw [BStarResetSchedule.run_append,←old]; rfl
    have added := generated_append hp history
      (old ▸ GeneratedOwner.next I ev (.endpoint (busy_start hp tail)))
    exact (ih (lead++[e]) newly added (fun h => past_event hp (past h) ev)
      (fun a f b E => layout (e::a) f b (congrArg (List.cons e) E))).trans frame

end L4.BStarCopyRightPostload
