import Leader.L4.BStarFencePhysicalDelivery
import Leader.L4.BStarFenceSweepClock
import Leader.L4.BStarFenceRightShadow

namespace L4.BStarFenceBStarMean
open L4.Height
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarGeneratedOwner
open BStarResetChartTouch BStarGeneratedBandScan
open BStarFenceShadow BStarFencePorts BStarFenceRightShadow BStarFenceLineGeometry
open BStarParkedSteering BStarSteeredLikelihood

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Finite-horizon expected time until the selected physical phase
ends or both owned data lines are empty. This verifies its uniform
(128 n H) service envelope with slack, on the full raw candidate
alphabet and with the real pair update. It does not assert that an
arbitrary raw configuration has entered this phase or that it cannot
be re-armed; those are separate production obligations. -/
theorem clearance_mean {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    (ready : ∀ q,Q q→BStarClearanceOffset.correct (oldH6 B base) hh 5 q)
    (idle : Current hp base (fun j => S.getD j fall) len x .idle)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+r') (lc : l+r'≤n) (rc : d+r'≤n)
    {fresh : Word n→Fin n→Prop} {redirect : Word n→Fin n→Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (owners : ∀ a i, fresh a i → Nonempty
      (BStarFenceTwoCandidates.GateOwner hp base hh (play x a) i))
    (phase : Word n→Bool)
    (fence : ∀ a,phase a=true→pc (play x a) (S.getD 0 fall).1=11)
    (a : Word n) (horizon : Nat) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun a : Word n =>
      (⟨BStarFenceLeftShadow.leftOcc (play x a) Lroot l r',rightOcc (play x a) Rroot d r'⟩ :
        Two (l:=l+r') (r:=d+r'))
    let choose := chooseBy redirect
    let next := fun (t : Word n) e => t++[choose t e]
    Thru.wordSum (BStarFenceSweepClock.actual next phase phys a horizon) horizon ≤
      92*n*max (l+r') (d+r')*n^horizon := by
  dsimp only
  let Lroot := (S.getD 0 fall).1
  let Rroot := (S.getD len fall).1
  let phys := fun a : Word n =>
    (⟨BStarFenceLeftShadow.leftOcc (play x a) Lroot l r',rightOcc (play x a) Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
  let choose := chooseBy redirect
  let next := fun (t : Word n) e => t++[choose t e]
  have same (b w : Word n) :
      BStarFenceSweepClock.emitted next choose b w=emit choose b w := by
    induction w generalizing b with
    | nil => rfl
    | cons e w ih =>
      change choose b e :: BStarFenceSweepClock.emitted next choose (next b e) w = _
      rw [ih]
      rfl
  have one (b : Word n) (e : Fin n) (_ : True) (act : phase b=true) :
      Mark (leftPort Lroot) (choose b e) (phys b).left (phys (next b e)).left ∧
      Mark (rightPort Rroot) (choose b e) (phys b).right (phys (next b e)).right := by
    obtain ⟨m,hist,live,now⟩ := generated_word hp chart Q layout closed sep b .idle I idle
    have Eq : play x (b++[choose b e])=step (play x b) (choose b e) := by
      rw [BStarResetSchedule.run_append]
      rfl
    dsimp only [phys,next]
    rw [Eq]
    exact ⟨BStarFenceLeftShadow.left_mark hp chart sep hist now (layout _ live) (fence b act) LF (choose b e),
      right_mark hp chart sep hist now (layout _ live) (fence b act) RF dp
        (right_tail_from_flags hp RF flags notShort) (choose b e)⟩
  exact BStarFenceSweepClock.physical_stopped_mean hn (leftPort Lroot) (rightPort Rroot)
    hl (by omega) (fun _ _=>left_labels_injective Lroot lc) (fun _ _=>right_labels_injective Rroot rc)
    choose a (BStarFencePhysicalDelivery.physical_delivery hp Q layout closed ready sep x I mask owners)
    next choose phase (fun _=>True) phys (fun _ _ _ _=>True.intro) one a True.intro horizon (same a)

end L4.BStarFenceBStarMean
