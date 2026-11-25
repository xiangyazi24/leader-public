import Leader.L4.BStarCopyRightSetupFlights
import Leader.L4.BStarCopyRightMiddle
import Leader.L4.BStarGeneratedTapeCuts

namespace L4.BStarCopyRightSetupMiddle
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarClearanceSource BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarCopyRightLoadToInject BStarCopyRightMiddle BStarGeneratedTapeCuts
open BStarCopyAttemptBand BStarCopyFenceCuts

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

theorem middle_from_actual_cuts {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w8 early : List (Fin n)) (issue : Fin n)
    (G8 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w8 (.busy 8 (.back 0)))
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len (play origin w8) (.busy 8 (.back 0)) early .idle)
    (V : LiveAt hp chart (play origin w8) early)
    (old10 : pc (play (play origin w8) early) (S.getD 0 fall).1=10)
    (own : issue=RearTrace.predecessor (S.getD 0 fall).1)
    (launch : Launch ((play (play origin w8) early) (S.getD 0 fall).1).long
      ((ring (play (play origin w8) early) issue) (S.getD 0 fall).1).long)
    (new : Current hp base (fun j=>S.getD j fall) len (ring (play (play origin w8) early) issue) (.busy 10 (.out 0))) :
    OwnMiddle hp base origin (fun j=>S.getD j fall) len w8 (early++[issue]) := by
  have L : Event hp (fun j=>S.getD j fall) len (play (play origin w8) early) issue .idle (.busy 10 (.out 0)) := by
    have ev := Event.launch (hp:=hp) (len:=len) (addr:=fun j=>S.getD j fall) own launch
    change pc (play (play origin w8) early) (S.getD 0 fall).1=10 at old10
    exact old10 ▸ ev
  have old8 : pc (play origin w8) (S.getD 0 fall).1=8 := (at_end hp G8).1.2.2.2
  apply own_middle_of_band hp chart sep w8 early issue G8 G L new
  · intro a b E
    obtain ⟨_,P,Q⟩ := split hp a b (E ▸ G)
    have low := band_word hp chart sep P (fun u v H => V u (v++b) (by rw [E,H,List.append_assoc]))
    have high := band_word hp chart sep Q (fun u v H => by
      have W := V (a++u) v (by rw [E,H,List.append_assoc])
      rwa [BStarResetSchedule.run_append] at W)
    have hh := old10
    rw [E,BStarResetSchedule.run_append] at hh
    exact ⟨old8 ▸ low,hh ▸ high⟩
  · exact fun a b E => (V a b E).1

end L4.BStarCopyRightSetupMiddle
