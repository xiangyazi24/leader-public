import Leader.L4.BStarCopyDrainedHistory

namespace L4.BStarCopyCleanupCuts
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

theorem advance_is_consume {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,Layout B base i=Layout B x i)
    {m m' : Mode} (e : Fin n)
    (I : Current hp base (fun j => S.getD j fall) len x m)
    (E : Event hp (fun j => S.getD j fall) len x e m m')
    (post : Current hp base (fun j => S.getD j fall) len (step x e) m')
    (k : Nat) (old : pc x (S.getD 0 fall).1=k) (new : pc (step x e) (S.getD 0 fall).1=k+1)
    (low : 6≤k) :
    m=.busy k (.back 0) ∧ m'=.idle := by
  cases m with
  | idle =>
    rcases idle_launch_or_hold hp chart layout I.2 sep e I.1 with L|N|H
    · have eq := congrArg (fun t : BitVec 2×BitVec 9 => t.2.toNat) L.2.2.1
      change pc (step x e) (S.getD 0 fall).1=pc x (S.getD 0 fall).1 at eq
      omega
    · have eq := congrArg (fun q : (Token×BitVec 2)×BitVec 9 => q.2.toNat) N.2.2.1
      change pc (step x e) (S.getD 0 fall).1=0 at eq
      omega
    · obtain ⟨_,⟨_,_,_,snap⟩,_,_⟩ := H
      have eq := congrArg (fun q : (Token×BitVec 2)×BitVec 9 => q.2.toNat) snap
      change pc (step x e) (S.getD 0 fall).1=pc x (S.getD 0 fall).1 at eq
      omega
  | busy op z =>
    have opEq : pc x (S.getD 0 fall).1=op := I.1.2.2.2
    cases E with
    | transit _ _ _ _ _ =>
      have eq : pc (step x e) (S.getD 0 fall).1=op := post.1.2.2.2
      omega
    | arrived_hold _ _ =>
      have eq : pc (step x e) (S.getD 0 fall).1=op := post.1.2.2.2
      omega
    | consume _ _ _ => exact ⟨by rw [←opEq,old],rfl⟩

/-- First extract the literal accepted setup mark, not just an
increasing numerical PC projection. -/
theorem accepted_cut {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (valid : ∀ a b,w=a++b →
      (∀ i, Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1)
    (k : Nat) (lo : pc x (S.getD 0 fall).1≤k) (hi : k<pc (play x w) (S.getD 0 fall).1) :
    ∃ (pre : List (Fin n)) (ack : Fin n) (tail : List (Fin n)), w=pre++ack::tail ∧
      GeneratedOwner hp base (fun j => S.getD j fall) len x .idle pre (.busy k (.back 0)) ∧
      Event hp (fun j => S.getD j fall) len (play x pre) ack (.busy k (.back 0)) .idle ∧
      pc (step (play x pre) ack) (S.getD 0 fall).1=k+1 := by
  obtain ⟨pre,ack,tail,W,old,new⟩ := exact_crossing hp chart sep G valid k lo hi
  obtain ⟨mode,lead,rest⟩ := BStarGeneratedTapeCuts.split hp pre (ack::tail) (W ▸ G)
  cases rest with
  | @next _ _ _ _ b _ I ev suffix =>
    have endI : Current hp base (fun j => S.getD j fall) len (step (play x pre) ack) b := by
      cases suffix with
      | endpoint E => exact E
      | next E _ _ => exact E
    have low := (valid pre (ack::tail) W).2.1
    obtain ⟨M,N⟩ := advance_is_consume hp chart sep (valid pre (ack::tail) W).1 ack I ev endI k old new (by omega)
    cases M
    cases N
    exact ⟨pre,ack,tail,W,lead,ev,new⟩

end L4.BStarCopyCleanupCuts
