import Leader.L4.Height.FreshVisitedOperands
import Leader.L4.Height.FreshFenceGuards
import Leader.L4.Height.FreshNumericInputs

namespace L4.Height.FreshFenceInspection
open AllSizeProtocol BStarTrace BStarLongWork BStarLongPackets BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongFixedRouting BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarAcquireAnchors BStarResetMarkAdapter BStarH6Ordinal BStarLongFiberOwner
open BStarCopyRightStrip (addr)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)
open FreshFenceContinuation FreshFenceGuards

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Discharge the prospective guard at every marked outgoing chart slot
from clean open owned lanes and the two retaining-visit conclusions. -/
theorem guard_of_operands {base x : X} {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n} (C : Chart hp base hh o S len fall)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (frame : ∀ i,Layout B base i=Layout B x i) (k : Nat) (bound : k≤len)
    (e : Fin n) (a : AtK) (loc : S.getD k fall=address e a)
    (opened : OpenOwner hp base x o.val) (clean : CleanOwner hp base x o.val)
    (left : ∀ j,j<r → S.getD k fall=(addr (S.getD len fall).1 j,fencePort .ld) →
      ∃ d,(ldRead x (S.getD len fall).1 j).retained=.data d)
    (right : ∀ j,j<r → S.getD k fall=(addr (S.getD len fall).1 (r-1-j),fencePort .rd) →
      ∃ d,(rdRead x (S.getD len fall).1 r j).retained=.data d) :
    checkFence (oldPair B x e) (view ((x e).long,(x (rightNeighbor e)).long)) a (unit 11)≠.fault := by
  let g := oldPair B x e
  let i := site e a.side
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  cases M : fenceSheet (geometry g a.side) a.occurrence with
  | none =>
    change checkFence g (view raw) a (unit 11)≠.fault
    simp [checkFence,unit,M]
  | some sh =>
    obtain ⟨gate,nonfault⟩ := pointed_inspection_clean hp C e k bound a loc sh M frame opened clean
    apply (mapped_guard_nofault g (view raw) a sh M).mpr
    refine ⟨gate,nonfault.1,?_⟩
    let v : At Sheet := ⟨a.side,sh⟩
    by_cases held : BStarLongPackets.retains g v=false
    · exact .inr (.inl held)
    have kind : (geometry g a.side).inside=true ∧ (sh=.ld ∨ sh=.rd) := by
      cases side : a.side <;> cases sh <;> simp_all [BStarLongPackets.retains,v,geometry]
    have siteEq : (S.getD k fall).1=i := congrArg Prod.fst loc
    have portEq : (S.getD k fall).2=a.occurrence := congrArg Prod.snd loc
    have geo : geometry g a.side=longGeometry B (x i) := by cases side : a.side <;> simp [g,i,geometry,site,oldPair,side]
    have inside : (longGeometry B (x (S.getD k fall).1)).inside=true := by
      rw [siteEq,←geo]; exact kind.1
    have port : a.occurrence=fencePort sh := by
      let geometr (inside : Bool) : LongGeometry := ⟨⟨false,false,false,false,false,false⟩,inside,false,0,false⟩
      have rows (inside : Bool) : ∀ (j : Fin 11) (s : Sheet),
          fenceSheet (geometr inside) j=some s → j=fencePort s := by
        cases inside <;> decide +kernel
      exact rows (geometry g a.side).inside a.occurrence sh M
    have disp : cmdDispl (S.getD k fall).2=1 := by
      rw [portEq,port]
      rcases kind.2 with rfl|rfl <;> rfl
    obtain ⟨d,digit⟩ := FreshNumericInputs.digit_at_displacement hp C flags notShort frame k bound disp inside
    have pointed : S.getD k fall=(addr (S.getD len fall).1 d.val,fencePort sh) :=
      Prod.ext digit (portEq.trans port)
    have old := BStarCopyRightMark.old_access x e v
    change view raw v=readLane (Sheet.index sh) (x i).long at old
    rw [←siteEq,digit] at old
    refine .inr (.inr ?_)
    rcases kind.2 with rfl|rfl
    · obtain ⟨tag,tagAt⟩ := left d.val d.isLt pointed
      rw [show (view raw v).retained=.data tag from (congrArg Lane.retained old).trans tagAt]
      rfl
    · let j := r-1-d.val
      have size := d.isLt
      have eq : r-1-j=d.val := by dsimp [j]; omega
      obtain ⟨tag,tagAt⟩ := right j (by dsimp [j]; omega) (by rw [eq]; exact pointed)
      unfold rdRead at tagAt
      rw [eq] at tagAt
      rw [show (view raw v).retained=.data tag from (congrArg Lane.retained old).trans tagAt]
      rfl

#print axioms guard_of_operands
end L4.Height.FreshFenceInspection
