import Leader.L4.DirtyPrepRank

namespace L4.DirtyPrepDrainStable
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarResetChartTouch
open BStarFenceShadow BStarFencePorts BStarFenceLineGeometry BStarFenceSweepClock
open BStarFenceLeftShadow (leftOcc)
open BStarFenceRightShadow (rightOcc)
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum (distance distance_idx)
open DirtyLeastForward (ringF ring_origin)
open L4.Height

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

open DirtyPrepRank (debt expected_to_high_cut_of_local)

private theorem sum_mono {m : Nat} {f g : Fin m→Nat} (H : ∀ i,f i≤g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (H 0) (ih (fun i=>H i.succ))

/-- Adding a reachable-state invariant to the intermediate target
does not levy additional cost; it is carried to every first-hit state. -/
theorem mean_mono_before_hit {Y : Type} {m : Nat} {next : Y→Fin m→Y} {A G Q : Y→Prop}
    (closed : ∀ q,Q q→¬G q→∀ e,Q (next q e))
    (includeA : ∀ q,Q q→A q→G q) (t : Nat) (x : Y) (init : Q x) :
    Height.iidHitCost next G t x ≤ Height.iidHitCost next A t x := by
  classical
  induction t generalizing x with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases hit : G x
    · rw [Height.iidHitCost_of_target next G x hit]
      exact Nat.zero_le _
    · have notA : ¬A x := fun h=>hit (includeA x init h)
      simp only [Height.iidHitCost, if_neg hit, if_neg notA]
      exact Nat.add_le_add_left (sum_mono (fun e=>ih _ (closed x init hit e))) _

theorem expected_through_prep_and_stable_drain_of_local
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+r') (lc : l+r'≤n) (rc : d+r'≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    {j : Nat} (J : j≤len) (high : 6≤(S.getD j fall).2.val) :
    let root := (S.getD 0 fall).1
    let A (q : X) := Held (q root).long
    let F (q : X) (i : Nat) := ringF q (S.getD i fall)
    let D (q : X) (i : Nat) := debt hp base q (S.getD i fall)
    let least (q : X) (i : Nat) := i<j ∧ F q i ∧ ∀ k,k<i→¬F q k
    let phys := fun q : X => (⟨leftOcc q root l r', rightOcc q (S.getD len fall).1 d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    (∀ q i,Q q→A q→least q i→∀ e,F (step q e) i→D (step q e) i≤D q i) →
    (∀ q i,Q q→A q→least q i→∃ e,F (step q e) i→D (step q e) i<D q i) →
    Height.IIDExpectedHittingTimeAtMost step (fun q=>¬A q ∨ (∀ i,i<j→¬F q i) ∧ Empty (phys q)) x
      (n*(3*j+2)+92*n*max (l+r') (d+r')) := by
  dsimp only
  let root := (S.getD 0 fall).1
  let phys := fun q : X => (⟨leftOcc q root l r', rightOcc q (S.getD len fall).1 d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
  let clear (q : X) := ∀ i,i<j→¬ringF q (S.getD i fall)
  let final (q : X) := ¬Held (q root).long ∨ clear q ∧ Empty (phys q)
  let mid (q : X) := Q q ∧ clear q
  intro weak pay
  have P := expected_to_high_cut_of_local hp chart sep Q I layout closed J weak pay
  have first : Height.IIDExpectedHittingTimeAtMost step (fun q=>mid q∨final q) x (n*(3*j+2)) := by
    intro t
    exact Nat.le_trans (mean_mono_before_hit (fun q Qq _ e=>closed q Qq e)
      (fun q Qq h=> h.elim (fun N=>.inr (.inl N)) (fun C=>.inl ⟨Qq,C⟩)) t x I) (P t)
  apply Height.iid_stage_le step hn x mid final _ _ first
  intro q C t
  have next := DirtyFenceFixedCut.expected_from_high_cut hp chart sep Q C.1 layout closed
    LF RF dp flags notShort hn hl lc rc head cont J high C.2
  let U (y : X) := Q y ∧ clear y
  have stepU (y : X) (Hy : U y) (N : ¬final y) (e : Fin n) : U (step y e) := by
    have H : Held (y root).long := Classical.byContradiction (fun h=>N (.inl h))
    exact ⟨closed y Hy.1 e,DirtyPrepRank.no_prefix_refill hp chart sep (layout y Hy.1) H J Hy.2 e⟩
  exact Nat.le_trans (mean_mono_before_hit stepU
    (fun y H E=>E.elim Or.inl (fun f=>.inr ⟨H.2,f⟩)) t q C) (next t)

end L4.DirtyPrepDrainStable
