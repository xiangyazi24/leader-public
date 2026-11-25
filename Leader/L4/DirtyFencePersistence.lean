import Leader.L4.DirtyFenceEntryMean
import Leader.L4.BStarFenceEmptySuffix

namespace L4.DirtyFencePersistence
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarResetChartTouch
open BStarFenceShadow BStarFencePorts BStarFenceLineGeometry BStarFenceSweepClock
open BStarFenceEmptySuffix (empty_advance ownedLines)
open DirtyFenceShadow (both_mark owner_reservation_free_of_cutoff)
open BStarClearanceIndexedSum (distance)
open BStarClearanceIndexedWait (BeforeOwnService)
open DirtyLeastForward (ringF ring_origin)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Once cleared, both actual mobile lines stay empty throughout the
unchanged fixed-chart, before-own-service tape from an empty prep cutoff.
This is about literal mobile occupancy, not a sticky monitor bit. -/
theorem empty_until_own_service
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (tape : List (Fin n)) (cutoff : Nat)
    (onPrep : ∀ u∈S, (∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) →
      cutoff<distance S u)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u)
    (good : ∀ pre e post, tape=pre++e::post →
      let z := pre.foldl step x
      (∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B z i) ∧
      BeforeOwnService hp z (endpoint (oldH6 B base) hh o 0).1 e) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    Empty (ownedLines Lroot Rroot l d r' x) →
    Empty (ownedLines Lroot Rroot l d r' (tape.foldl step x)) := by
  dsimp only
  intro E
  induction tape generalizing x with
  | nil => exact E
  | cons e w ih =>
    have H := good [] e w rfl
    let z := ownedLines (S.getD 0 fall).1 (S.getD len fall).1 l d r' x
    have self : z.below z := ⟨fun _ t => t,fun _ t => t⟩
    have shadow := both_mark hp chart sep H.1
      (owner_reservation_free_of_cutoff hp chart H.1 cutoff onPrep clear)
      LF RF dp flags notShort e z self
    have next := empty_of_below shadow (empty_advance _ _ e z E)
    apply ih (x:=step x e)
    · intro u U cut F
      rcases ring_origin hp chart H.1 e (sep e) H.2 u U F with old|⟨v,V,old,far⟩
      · exact clear u U cut old
      · exact clear v V (by omega) old
    · intro pre f post EQ
      exact good (e::pre) f post (congrArg (List.cons e) EQ)
    · exact next

/-- Any valid geometric width bound composes with the raw clock without
changing the event or introducing a new scheduler. -/
theorem mean_widen {Y : Type} {m l r W : Nat} {next : Y→Fin m→Y}
    {goal : Y→Prop} {x : Y} (width : max l r≤W)
    (clock : Height.IIDExpectedHittingTimeAtMost next goal x (92*m*max l r)) :
    Height.IIDExpectedHittingTimeAtMost next goal x (92*m*W) := by
  intro t
  exact Nat.le_trans (clock t)
    (Nat.mul_le_mul_right (m^t) (Nat.mul_le_mul_left (92*m) width))

end L4.DirtyFencePersistence
