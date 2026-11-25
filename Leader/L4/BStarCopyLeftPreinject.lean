import Leader.L4.BStarCopyLeftK5Past
import Leader.L4.BStarGeneratedTapeCuts

namespace L4.BStarCopyLeftPreinject
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarCopyOperand BStarCopyLeftK5Past
open BStarAcquireVisitOrder BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarResetChartTouch BStarResetChartIndex BStarClearanceDataChart BStarAcquireAnchors BStarAcquireLiteralChain
open BStarSeparatingRail BStarAcquireHistorySample

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
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

/-- Every actual pre-INJECT PC10 raw mark preserves this source's
frozen packet, including arbitrarily many same-K5 waits. Does not
require a caller-supplied exclusion of the source cursor or a
postulated frozen frame at any mark. -/
theorem frozen_pc10_prefix {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (kl : k≤len)
    (atSource : S.getD k fall=(i,5))
    (own : dataOwner (oldH6 B base) i .ls=o.val)
    (lead : List (Fin n)) {x : X} {z : Cursor} {w : List (Fin n)}
    (old : x=play origin lead)
    (history : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy 10 z))
    (busy : BusyOnly hp base (fun t => S.getD t fall) len 10 x z w (.out k))
    (layout : ∀ a e b, w=a++e::b →
      ∀ j, BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (play x a) j) :
    (readLane (Sheet.index .ls) (play x w i).long).frozen=
      (readLane (Sheet.index .ls) (x i).long).frozen := by
  generalize F : Cursor.out k=fin at busy
  induction busy generalizing lead with
  | nil => rfl
  | @cons x z d fin e w I ev tail ih =>
    rw [←F] at tail
    obtain ⟨j,J⟩ := busy_no_back_to_out hp (.cons I ev tail) ⟨k,rfl⟩
    subst z
    have same := layout [] e w rfl
    have Now : Current hp base (fun t => S.getD t fall) len (play origin lead) (.busy 10 (.out j)) :=
      old ▸ I
    have real := no_ls_prep_until_inject hp chart sep lead e i k j kl atSource own history Now
      (old ▸ same) (old ▸ ev) (old ▸ tail)
    have S : FrozenSafe hp x e i .ls := by
      rw [old]
      intro s loc a win pick
      exact False.elim (real s loc (List.mem_map.mpr ⟨a,win,pick⟩))
    have frame := ring_frozen_frame hp x e i .ls (sep e) S
    have newly : ring x e=play origin (lead++[e]) := by
      rw [BStarResetSchedule.run_append,←old]
      rfl
    have added := generated_append hp history
      (old ▸ GeneratedOwner.next I ev (.endpoint (busy_start hp tail)))
    have result := ih (lead++[e]) newly added (fun a f b E =>
      layout (e::a) f b (congrArg (List.cons e) E)) F
    exact result.trans frame

#print axioms frozen_pc10_prefix
end L4.BStarCopyLeftPreinject
