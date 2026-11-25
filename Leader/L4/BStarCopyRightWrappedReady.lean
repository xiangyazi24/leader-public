import Leader.L4.BStarCopyRightWrappedGates
import Leader.L4.BStarCopyRightMixed
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopyRightWrappedReady
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightRetainedClassify BStarCopyRightDataSweep
open BStarCopyRightAuthority BStarCopyFenceSaturation
open BStarClearanceDataChart BStarCopyGateAuthority BStarCopyAttemptBand BStarGeneratedBandScan
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarAcquireAnchors
open BStarGeneratedOwner BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightReady

/-- Given coverage of actual ENABLE winners, all the remaining
physical DataReady conditions follow on late PC11 marks of the same
generated attempt. No per-mark gate or no-reservation oracle. -/
theorem data_ready_late {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t => S.getD t fall) len x .idle w m)
    (valid : ∀ u v, w=u++v → (∀ j, Layout B base j=Layout B (play x u) j) ∧
      Band (play x u) (S.getD 0 fall).1)
    (late : 11≤pc (play x w) (S.getD 0 fall).1)
    (e root baseAddr : Fin n) (width seam tail : Nat)
    (baseDest : Dest B base root width) (baseStrip : BStarCopyRightWrappedGeometry.WrappedStrip B base baseAddr seam tail)
    (dest : Dest B (play x w) root width) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B (play x w) baseAddr seam tail)
    (join : addr baseAddr 0=addr root (width-1))
    (ownHead : dataOwner (oldH6 B base) (addr baseAddr 0) (rail seam 0)=o.val)
    (rdCoverage : ∀ j<width, EnabledOn hp x w (addr root j) .rd)
    (upCoverage : ∀ j, 0<j → j≤tail → EnabledOn hp x w (addr baseAddr j) (rail seam j)) :
    BStarCopyRightWrappedSweep.DataReady hp (play x w) root baseAddr e width seam tail := by
  let y := play x w
  have f := valid w [] (by simp)
  have same := f.1
  have now := BStarGeneratedTapeCuts.at_end hp G
  have rsh : rail seam 0=.rd := if_pos baseStrip.seam_pos
  have headOwn : dataOwner (oldH6 B base) (addr root (width-1)) .rd=o.val := by
    rwa [rsh,join] at ownHead
  have rd (j : Nat) (J : j<width) :
      dataOwner (oldH6 B base) (addr root j) .rd=o.val :=
    (dest_owner hp root width baseDest j J).trans headOwn
  have up (j : Nat) (J : j≤tail) :
      dataOwner (oldH6 B base) (addr baseAddr j) (rail seam j)=o.val :=
    (BStarCopyRightWrappedReleaseClass.strip_same_owner baseStrip j J).trans ownHead
  have noPrep (a : At Sheet)
      (own : dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val) :
      a∉reserved (round (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)).prep := by
    apply no_prep_late _ _ _ _ late
    intro offer win eq
    exact winning_prep_pc hp chart sep G now same e offer (by rwa [eq]) win
  exact ⟨dest,strip,
    fun j J => gate_from_enabled hp chart sep w m G valid _ _ (rd j J) (rdCoverage j J),
    fun j U J => gate_from_enabled hp chart sep w m G valid _ _ (up j J) (upCoverage j U J),
    fun j J s loc => noPrep ⟨s,.rd⟩ (by change dataOwner _ (site e s) .rd=o.val; rw [loc]; exact rd j J),
    fun j _ J s loc => noPrep ⟨s,rail seam j⟩ (by change dataOwner _ (site e s) (rail seam j)=o.val; rw [loc]; exact up j J)⟩

end L4.BStarCopyRightWrappedReady
