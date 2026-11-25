import Leader.L4.BStarCopyDownstream
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopyPreIssueEmpty
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder BStarResetMarkAdapter
open BStarAcquireLiteralChain BStarAcquireAnchors BStarClearanceDataChart
open BStarCopyEntryGates BStarCopyGateAuthority BStarGeneratedOwner BStarGeneratedBandScan

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- In the actual recovered history, only controller PC10 can issue a
winning INJECT on its own lane. Other simultaneous winners do not
compromise the exclusion. -/
theorem no_inject_before_10 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i, Layout B base i=Layout B (play x w) i)
    (small : pc (play x w) (S.getD 0 fall).1<10) (e : Fin n) :
    NoOwnerInject hp base (play x w) e o.val := by
  intro a win own equal
  have H := winning_prep_pc hp chart sep hist now layout e a own win
  rw [equal] at H
  unfold prepOf at H
  split at H <;> simp_all

/-- Preserving already-cleared lanes before the first ISSUE10, on
the actual marked prefix and allowing arbitrary foreign selections. -/
theorem empty_through_prep {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead middle : List (Fin n)) (m : Mode)
    (history : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle (lead++middle) m)
    (empty : MobilesEmpty hp base (play x lead) o.val)
    (layout : ∀ a b,middle=a++b →
      ∀ i, Layout B base i=Layout B (play x (lead++a)) i)
    (small : ∀ a e b,middle=a++e::b → pc (play x (lead++a)) (S.getD 0 fall).1<10) :
    MobilesEmpty hp base (play x (lead++middle)) o.val := by
  rw [BStarResetSchedule.run_append]
  apply empty_word hp base (play x lead) middle o.val sep empty
  · intro a b eq
    rw [←BStarResetSchedule.run_append]
    exact funext (fun i => (congrArg Prod.fst (layout a b eq i)).symm)
  · intro a e b eq
    rw [←BStarResetSchedule.run_append]
    have W : lead++middle=(lead++a)++e::b := by rw [eq,List.append_assoc]
    obtain ⟨mode,H,C⟩ := history_prefix hp (lead++a) (e::b) (W ▸ history)
    exact no_inject_before_10 hp chart sep H C (layout a (e::b) eq) (small a e b eq) e

#print axioms no_inject_before_10
#print axioms empty_through_prep
end L4.BStarCopyPreIssueEmpty
