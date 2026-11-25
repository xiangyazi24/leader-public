import Leader.L4.DirtyPrepPaidMean
import Leader.L4.DirtyForwardEmptyClock
import Leader.L4.DirtyTrailSuffix
import Leader.L4.BStarOwnerChartWidth
import Leader.L4.NonheldPhysicalIID

namespace L4.DirtyOwnerRelease
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart BStarH6Ordinal
open BStarResetChartTouch BStarLongFixedRouting BStarClearanceOffset BStarClearanceSource
open BStarFenceLineGeometry BStarFenceEmptySuffix BStarFenceSweepClock BStarLongCommandData
open BStarClearanceIndexedSum DirtyLeastForward DirtyFenceOccurrence DirtyPrepRank
open DirtyPrepDrainStable (mean_mono_before_hit)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Complete dirty Held-release clock on a settled owner chart. This
starts with arbitrary command and data bytes, carries the actual
unreserved empty phase, and includes reverse replies and trails. The
clock uses real IID marks without substitutions or fabricated words. -/
theorem held_release_expected
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,Layout B base i=Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=w))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → w≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 B base) hh 5 q) :
    Height.IIDExpectedHittingTimeAtMost step (fun y=>¬Held (y (S.getD 0 fall).1).long) x
      (n*(3*len+2)+92*n*max (l+w) (d+w)+n*S.length+(n*S.length+n*S.length)) := by
  classical
  obtain ⟨j,J,high,low⟩ := DirtyFenceFixedCut.exists_first_high hp chart
  let root := (S.getD 0 fall).1
  let rootR := (S.getD len fall).1
  let stop (q : X) := ¬Held (q root).long
  let clear (q : X) := ∀ i,i<j→¬ringF q (S.getD i fall)
  let phase (q : X) := clear q ∧ Empty (ownedLines root rootR l d w q)
  let post (q : X) := Q q ∧ phase q
  let NF (q : X) := ∀ u∈S, ¬ringF q u
  let afterForward (q : X) := Q q ∧ NF q
  have rootId : root=(endpoint (oldH6 B base) hh o 0).1 := congrArg Prod.fst chart.root
  let C₁ := n*(3*len+2)+92*n*max (l+w) (d+w)
  let C₂ := n*S.length
  let C₃ := n*S.length+n*S.length
  have prep := DirtyPrepPaidMean.expected_through_prep_and_stable_drain hp
    chart sep Q I layout closed LF RF dp flags notShort hn hl lc rc head cont cb cx J high low
  have first : Height.IIDExpectedHittingTimeAtMost step (fun q=>post q∨stop q) x C₁ := by
    intro t
    have cost := mean_mono_before_hit (Q:=Q) (G:=fun q=>post q∨stop q) (fun q H _ e=>closed q H e)
      (fun q H (A : stop q ∨ phase q)=>A.elim Or.inr (fun E=>.inl ⟨H,E⟩)) t x I
    apply Nat.le_trans cost (Nat.le_trans (prep t) ?_)
    apply Nat.mul_le_mul_right
    dsimp only [C₁]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) _
  have fromPhase (y : X) (P : post y) :
      Height.IIDExpectedHittingTimeAtMost step (fun q=>afterForward q ∨ stop q) y C₂ := by
    have size := chart.length
    let cut := distance S (S.getD j fall)
    have jS : j<S.length := by omega
    have dCut : cut=S.length-j := by
      dsimp only [cut]
      rw [←List.getElem_eq_getD (h:=jS) fall,distance_idx chart.nodup jS]
    have clearCut (a : X) (U : clear a) : ∀ u∈S,cut<distance S u→¬ringF a u := by
      intro u Hu D
      obtain ⟨i,iS,ei⟩ := List.mem_iff_getElem.mp Hu
      have dU : distance S u=S.length-i := by rw [←ei,distance_idx chart.nodup iS]
      rw [dCut,dU] at D
      rw [←ei,List.getElem_eq_getD (h:=iS) fall]
      exact U i (by omega)
    have onPrep : ∀ u∈S,(∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op)→
        cut<distance S u := by
      rintro u U ⟨sh,op,Pp⟩
      exact DirtyFenceFixedCut.prep_before_high hp chart head cont J high U Pp
    have onRace : ∀ u∈S,u.2.val=1→cut<distance S u := by
      intro u U K
      obtain ⟨i,iS,ei⟩ := List.mem_iff_getElem.mp U
      have eq : S.getD i fall=u := (List.getElem_eq_getD (h:=iS) fall).symm.trans ei
      have earlier : i<j := by
        by_cases E : i<j
        · exact E
        · have mono := chart_occurrence_mono hp chart head cont (by omega : j≤i) (by omega : i≤len)
          rw [eq,K] at mono
          omega
      rw [dCut,←ei,distance_idx chart.nodup iS]
      omega
    have clock := DirtyForwardEmptyClock.expected hp chart head cont sep Q P.1 layout (fun q e H=>closed q H e)
      dp LF RF seam flags notShort cut onPrep onRace (clearCut y P.2.1) P.2.2
    intro t
    exact Nat.le_trans (mean_mono_before_hit (Q:=Q) (G:=fun q=>afterForward q∨stop q) (fun a H _ e=>closed a H e)
      (fun a H (K : stop a ∨ NF a)=>K.elim Or.inr (fun N=>.inl ⟨H,N⟩)) t y P.1) (clock t)
  have firstTwo : Height.IIDExpectedHittingTimeAtMost step
      (fun q=>afterForward q∨stop q) x (C₁+C₂) := by
    have ff : Height.IIDExpectedHittingTimeAtMost step
        (fun q=>post q∨(afterForward q∨stop q)) x C₁ := by
      intro t
      exact Nat.le_trans (mean_mono_before_hit
        (Q:=fun _=>True) (fun _ _ _ _=>trivial)
        (fun q _ (H : post q∨stop q)=>H.elim Or.inl (fun h=>.inr (.inr h))) t x trivial) (first t)
    exact Height.iid_stage_le step hn x post (fun q=>afterForward q∨stop q) C₁ C₂ ff fromPhase
  apply Height.iid_stage_le step hn x afterForward stop (C₁+C₂) C₃ firstTwo
  intro y H
  have rest := DirtyTrailSuffix.forward_free_exit_expected hp chart head cont sep Q H.1 layout (fun q e H=>closed q H e) cb cx H.2
  rwa [←rootId] at rest

theorem held_release_expected_linear
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,Layout B base i=Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=w))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → w≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 B base) hh 5 q)
    (W : Nat) (wW : w≤W)
    (width : ∀ i,oldH6 B base (rightNeighbor i)=true → oldOrdinal B base hh i+1≤W) :
    Height.IIDExpectedHittingTimeAtMost step (fun y=>¬Held (y (S.getD 0 fall).1).long) x
      (252*n*W) := by
  have wb : 0<W := Nat.lt_of_lt_of_le LF.width_pos wW
  have word_bound (a : Fin n) (m : Nat) (mp : 0<m) (A : oldH6 B base a=true)
      (body : ∀ j,0<j→j<m→oldH6 B base (BStarCopyRightStrip.addr a j)=false) : m≤W := by
    let h := oldH6 B base
    let k := m-1
    have O := BStarCopyRightStrip.address_ordinal_run a h hh 0 k
      (fun j P J=>by simpa only [Nat.zero_add] using body j P (by omega)) k (Nat.le_refl _)
    simp only [Nat.zero_add] at O
    have zero : BStarCopyRightStrip.addr a 0=a :=
      Fin.ext (Nat.mod_eq_of_lt a.isLt)
    rw [zero,(ordinal_zero h hh a).mpr A,Nat.zero_add] at O
    have Z := BStarOwnerChartWidth.ordinal_lt_of_width_bound h hh W width
      (BStarCopyRightStrip.addr a k)
    rw [O] at Z
    omega
  have lW := word_bound _ l LF.seam_pos LF.source_header LF.ls_body
  have dW := word_bound _ d dp RF.terminal_header RF.body
  have L := BStarOwnerChartWidth.chart_length_le_width_mul hp chart W width
  have lenS := chart.length
  have H := held_release_expected hp chart sep Q I layout closed LF RF dp seam flags
    notShort hn hl lc rc head cont cb cx
  have C : n*(3*len+2)+92*n*max (l+w) (d+w)+n*S.length+(n*S.length+n*S.length) ≤ 252*n*W := by
    have m : max (l+w) (d+w)≤2*W := Nat.max_le.mpr ⟨by omega,by omega⟩
    have inside : 3*len+2+92*max (l+w) (d+w)+S.length+(S.length+S.length)≤252*W := by omega
    have B₁ := Nat.mul_le_mul_left n inside
    simp only [Nat.mul_add,←Nat.mul_assoc] at B₁
    simpa only [Nat.mul_add,←Nat.mul_assoc,Nat.mul_comm n 92,Nat.mul_comm n 252] using B₁
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ C)

theorem genuine_launch_expected_linear
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,Layout B base i=Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=w))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → w≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 B base) hh 5 q)
    (W : Nat) (wW : w≤W)
    (width : ∀ i,oldH6 B base (rightNeighbor i)=true → oldOrdinal B base hh i+1≤W) :

    Height.IIDExpectedHittingTimeAtMost (IssueLaunchIID.observe hp (S.getD 0 fall).1)
      (fun y=>y.2=true) (x,false) (252*n*W+3*n) := by
  classical
  let root := (S.getD 0 fall).1
  let next : X × Bool → Fin n → X × Bool := IssueLaunchIID.observe hp root
  let Ready (q : X × Bool) := Q q.1 ∧ ¬Held (q.1 root).long
  let Stop (q : X × Bool) := q.2=true
  let hit (q : X) := ¬Held (q root).long
  have obs (q : X×Bool) (e : Fin n) : (next q e).1=step q.1 e := rfl
  have sum_mono {m : Nat} {f g : Fin m→Nat} (H : ∀ i,f i≤g i) :
      (List.ofFn f).sum ≤ (List.ofFn g).sum := by
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      simp only [List.ofFn_succ,List.sum_cons]
      exact Nat.add_le_add (H 0) (ih (fun i=>H i.succ))
  have cost (t : Nat) (y : X×Bool) (Z : Q y.1) :
      Height.iidHitCost next (fun q=>Ready q∨Stop q) t y ≤ Height.iidHitCost step hit t y.1 := by
    induction t generalizing y with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      by_cases E : Ready y∨Stop y
      · rw [Height.iidHitCost_of_target next (fun q=>Ready q∨Stop q) y E]
        exact Nat.zero_le _
      · have N : ¬hit y.1 := fun q=>E (.inl ⟨Z,q⟩)
        simp only [Height.iidHitCost,if_neg E,if_neg N]
        apply Nat.add_le_add_left
        apply sum_mono
        intro e
        have nextQ : Q (next y e).1 := obs y e ▸ closed _ Z e
        rw [←obs y e]
        exact ih _ nextQ
  have release := held_release_expected_linear hp chart sep Q I layout closed LF RF dp seam flags
    notShort hn hl lc rc head cont cb cx W wW width
  apply Height.iid_stage_le next hn (x,false) Ready Stop (252*n*W) (3*n)
    (fun t=>Nat.le_trans (cost t (x,false) I) (release t))
  rintro ⟨y,seen⟩ ⟨Y,nonheld⟩
  cases seen
  · exact NonheldPhysical.chart_nonheld_launch_expected hp chart Q layout
      (fun y e H=>closed y H e) sep y Y nonheld
  · intro t
    rw [Height.iidHitCost_of_target _ Stop _ (show Stop (y,true) from rfl)]
    exact Nat.zero_le _

#print axioms held_release_expected
#print axioms held_release_expected_linear
#print axioms genuine_launch_expected_linear
end L4.DirtyOwnerRelease
