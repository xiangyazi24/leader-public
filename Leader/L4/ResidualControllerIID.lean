import Leader.L4.SeparatorReturnConsume
import Leader.L4.ResidualIssueIID
import Leader.L4.ControllerTapeIID
import Leader.L4.ControllerMacroIID

namespace L4.ResidualControllerIID
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearancePhysical BStarClearanceOffset
open BStarLongDoor BStarClearanceLex

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarFenceLineGeometry BStarH6Ordinal BStarLongCommand BStarClearanceResidual
open ControllerTapeIID (expected_of_prefix expected_after_prefix)

theorem attempt_expected_linear
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop)
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
    let addr := fun j=>S.getD j fall
    let pc := fun y : X=>(ctrlOp.read (y (addr 0).1).long).toNat
    let Inv := Boundary Q (oldH6 B base) hh addr len
    Inv x →
    Height.IIDExpectedHittingTimeAtMost step
      (fun y=>Inv y ∧ (pc y=0 ∨ pc x<pc y)) x (n+(252*n*W+n)) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let Inv := Boundary Q (oldH6 B base) hh addr len
  let pc := fun y : X=>(ctrlOp.read (y root).long).toNat
  let G : X→Prop := fun y=>Inv y ∧ (pc y=0 ∨ pc x<pc y)
  let P : List (Fin n)→Prop := fun w=>∃ pre tail,w=pre++tail ∧ G (play x pre)
  let A : List (Fin n)→Prop := fun k=>∃ pre,k=pre++[door] ∧
      let y:=play x pre
      let z:=step y door
      Inv y ∧ pc y=pc x ∧ Launch (y root).long (z root).long
  intro init
  have first := ResidualIssueIID.first_issue_mark_expected hp chart sep Q
    (fun y e Y=>closed y Y e) layout init
  apply expected_of_prefix step x G P _ (fun _ h=>h)
  apply Height.iid_stage_le ResetReturnIID.appendTape hn [] A P n (252*n*W+n)
  · apply expected_after_prefix _ _ [] n _ first
    intro w H
    obtain ⟨pre,eq,_,I,E,_,_,done|launch⟩ := H
    rw [List.nil_append]
    · exact .inr ⟨w,[],by simp,by rw [eq,BStarResetSchedule.run_append]; exact ⟨done.1,.inl done.2⟩⟩
    · exact .inl ⟨pre,eq,I,E,launch⟩
  · intro k T
    obtain ⟨pre,hk,I,E,launch⟩ := T
    let y := play x pre
    let z := step y door
    have vz : play x k=z := by rw [hk,BStarResetSchedule.run_append]; rfl
    have moments := SeparatorReturnConsume.return_consume_after_launch_expected_linear hp chart sep
      Q I.lower layout closed LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width launch
    apply expected_after_prefix _ P k _ _ moments
    intro w C
    obtain ⟨letour,gap,tail,eq,_,_,_,_,Qf,empty,ph,final,advance,same⟩ := C
    let u := k++((letour++gap)++[door])
    let f := step (play z (letour++gap)) door
    change w=letour++(gap++door::tail) at eq
    have Wd : k++w=u++tail := by
      rw [eq]
      simp [u,List.append_assoc]
    have Xf : play x u=f := by
      rw [show u=k++((letour++gap)++[door]) from rfl,BStarResetSchedule.run_append,vz,
        BStarResetSchedule.run_append]
      rfl
    have range : final<413 := advance.elim (fun v=>v.symm ▸ (by decide : 0<413)) And.right
    have I' : Inv f := ⟨Qf,cx _ Qf,legal_issue _ ph (same.symm ▸ range),empty⟩
    refine ⟨u,tail,Wd,?_⟩
    rw [Xf]
    refine ⟨I',?_⟩
    change pc f=0 ∨ pc x<pc f
    change pc f=final at same
    rw [same,←E]
    exact advance.imp id And.left

theorem to_issue_zero_expected_linear
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop)
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
    let addr := fun j=>S.getD j fall
    let pc := fun y : X=>(ctrlOp.read (y (addr 0).1).long).toNat
    let Inv := Boundary Q (oldH6 B base) hh addr len
    Inv x →
    Height.IIDExpectedHittingTimeAtMost step
      (fun y=>Inv y ∧ pc y=0) x (412*(n+(252*n*W+n))) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let Inv := Boundary Q (oldH6 B base) hh addr len
  let pc := fun y : X=>(ctrlOp.read (y root).long).toNat
  let final := fun y=>Inv y ∧ pc y=0
  let rank := fun y=>BStarControllerLoop.remaining (pc y)
  intro init
  have zero (y : X) (Y : Inv y) (R : rank y=0) : final y := by
    refine ⟨Y,?_⟩
    have V := issue_range Y.issue
    change (if pc y=0 then 0 else 413-pc y)=0 at R
    change pc y<413 at V
    split at R
    · assumption
    · omega
  have stages (y : X) (Y : Inv y) (L : ¬final y) :
      Height.IIDExpectedHittingTimeAtMost step (fun z=>(Inv z∧rank z<rank y)∨final z)
        y (n+(252*n*W+n)) := by
    have H := attempt_expected_linear hp chart sep Q layout closed LF RF dp seam flags
      notShort hn hl lc rc head cont cb cx W wW width Y
    intro t
    apply Nat.le_trans _ (H t)
    apply DirtyPrepDrainStable.mean_mono_before_hit (Q:=fun _=>True) (fun _ _ _ _=>trivial) _ t y trivial
    intro z _ A
    change Inv z ∧ (pc z=0 ∨ pc y<pc z) at A
    rcases A.2 with pz|grow
    · exact .inr ⟨A.1,pz⟩
    · exact .inl ⟨A.1,BStarControllerLoop.charge (issue_range Y.issue) (fun e=>L ⟨Y,e⟩) (.inr grow)⟩
  have h := ControllerMacroIID.expected_of_rank_stages hn step Inv final rank _ zero stages x init
  have R : rank x≤412 := by
    change (if pc x=0 then 0 else 413-pc x)≤412
    split <;> omega
  intro t
  exact Nat.le_trans (h t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ R))

private theorem snoc_ind {L : Type} {P : List L→Prop}
    (nil : P []) (append_singleton : ∀ w e,P w→P (w++[e])) (w : List L) : P w := by
  have H (k : Nat) : ∀ v : List L,v.length=k→P v := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro v Vk
      rcases List.eq_nil_or_concat v with rfl|⟨u,e,E⟩
      · exact nil
      · subst v
        have V : u.length<k := by simp [List.concat_eq_append] at Vk; omega
        rw [List.concat_eq_append]
        exact append_singleton u e (ih _ V _ rfl)
  exact H w.length w rfl

/-- Historical relift of the sticky launch bit: it names a physical original
prefix and the selected door mark, not the endpoint's inherited bytes. -/
theorem launch_tape_of_observer (x : X) (root : Fin n) (K : Nat)
    (H : Height.IIDExpectedHittingTimeAtMost (IssueLaunchIID.observe hp root)
      (fun q=>q.2=true) (x,false) K) :
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (fun w=>∃ pre tail,w=pre++(RearTrace.predecessor root)::tail ∧
        let y:=play x pre
        Launch (y root).long (step y (RearTrace.predecessor root) root).long) [] K := by
  classical
  let door := RearTrace.predecessor root
  let next : X×Bool→Fin n→X×Bool := IssueLaunchIID.observe hp root
  let replay := BStarResetSchedule.run next (x,false)
  let P : List (Fin n)→Prop := fun w=>∃ pre tail,w=pre++door::tail ∧
    let y:=play x pre
    Launch (y root).long (step y door root).long
  have first (w : List (Fin n)) : (replay w).1=play x w := by
    induction w using snoc_ind with
    | nil => rfl
    | append_singleton w e ih =>
      rw [show replay (w++[e])=next (replay w) e from BStarResetSchedule.run_append _ _ _ _,
        BStarResetSchedule.run_append]
      change step (replay w).1 e=step (play x w) e
      rw [ih]
  have seen (w : List (Fin n)) : (replay w).2=true → P w := by
    induction w using snoc_ind with
    | nil => intro h; cases h
    | append_singleton w e ih =>
      rw [show replay (w++[e])=next (replay w) e from BStarResetSchedule.run_append _ _ _ _]
      change ((replay w).2 || decide (e=door ∧ Launch ((replay w).1 root).long
        (step (replay w).1 e root).long))=true → P (w++[e])
      intro t
      rcases Bool.or_eq_true_iff.mp t with old|event
      · obtain ⟨pre,tail,F,L⟩ := ih old
        exact ⟨pre,tail++[e],by rw [F,List.append_assoc]; rfl,L⟩
      · obtain ⟨rfl,L⟩ := of_decide_eq_true event
        rw [first] at L
        exact ⟨w,[],rfl,L⟩
  have compare (t : Nat) (w : List (Fin n)) :
      Height.iidHitCost ResetReturnIID.appendTape P t w ≤
        Height.iidHitCost next (fun q=>q.2=true) t (replay w) := by
    induction t generalizing w with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      by_cases hit : P w
      · rw [Height.iidHitCost_of_target _ _ _ hit]
        exact Nat.zero_le _
      · have N : ¬(replay w).2=true := fun j=>hit (seen w j)
        simp only [Height.iidHitCost,if_neg hit,if_neg N]
        apply Nat.add_le_add_left
        apply ControllerTapeIID.sum_mono
        intro e
        rw [←show replay (ResetReturnIID.appendTape w e)=next (replay w) e from
          BStarResetSchedule.run_append _ _ _ _]
        exact ih _
  intro t
  exact Nat.le_trans (compare t []) (H t)

theorem arbitrary_to_boundary_expected_linear
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (qx : Q x)
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
    let addr := fun j=>S.getD j fall
    let Inv := Boundary Q (oldH6 B base) hh addr len
    Height.IIDExpectedHittingTimeAtMost step Inv x ((252*n*W+3*n)+(252*n*W+n)) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let Inv := Boundary Q (oldH6 B base) hh addr len
  let P : List (Fin n)→Prop := fun w=>∃ pre tail,w=pre++tail ∧ Inv (play x pre)
  let A : List (Fin n)→Prop := fun w=>∃ pre,w=pre++[door] ∧
    let y:=play x pre
    Launch (y root).long (step y door root).long
  let C₁ := 252*n*W+3*n
  let C₂ := 252*n*W+n
  have Qrun (y : X) (w : List (Fin n)) (q : Q y) : Q (play y w) := by
    induction w generalizing y with
    | nil => exact q
    | cons e w ih => exact ih _ (closed y q e)
  have launch := launch_tape_of_observer hp x root C₁
    (DirtyOwnerRelease.genuine_launch_expected_linear hp chart sep Q qx layout closed
      LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width)
  have runTape (a b : List (Fin n)) : BStarResetSchedule.run ResetReturnIID.appendTape a b=a++b := by
    induction b generalizing a with
    | nil => simp [BStarResetSchedule.run]
    | cons e t ih => simpa only [BStarResetSchedule.run,ResetReturnIID.appendTape,List.append_assoc,List.singleton_append] using ih (a++[e])
  have exactLaunch : Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape A [] C₁ := by
    apply expected_of_prefix ResetReturnIID.appendTape [] A _ C₁ _ launch
    intro w T
    obtain ⟨pre,tail,E,L⟩ := T
    refine ⟨pre++[door],tail,?_,?_⟩
    · change w=pre++door::tail at E
      simpa only [List.append_assoc,List.singleton_append] using E
    · rw [runTape,List.nil_append]
      exact ⟨pre,rfl,L⟩
  apply expected_of_prefix step x Inv P _ (fun _ h=>h)
  apply Height.iid_stage_le ResetReturnIID.appendTape hn [] A P C₁ C₂
    (expected_after_prefix _ _ [] _ (fun _ h=>.inl h) exactLaunch)
  intro w T
  obtain ⟨pre,E,L⟩ := T
  let y := play x pre
  let z := step y door
  let v := pre++[door]
  have vz : play x v=z := by rw [show v=pre++[door] from rfl,BStarResetSchedule.run_append]; rfl
  have before : Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape P v C₂ := by
    have moments := SeparatorReturnConsume.return_consume_after_launch_expected_linear hp chart sep
      Q (Qrun x pre qx) layout closed LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width L
    apply expected_after_prefix _ P v _ _ moments
    intro q C
    obtain ⟨tour,gap,rest,F,_,_,_,_,Qf,empty,ph,final,advance,same⟩ := C
    let u := v++((tour++gap)++[door])
    let f := step (play z (tour++gap)) door
    change q=tour++(gap++door::rest) at F
    have eq : v++q=u++rest := by rw [F]; simp [u,List.append_assoc]
    have finalReplay : play x u=f := by
      rw [show u=v++((tour++gap)++[door]) from rfl,BStarResetSchedule.run_append,vz,
        BStarResetSchedule.run_append]
      rfl
    have range : final<413 := advance.elim (fun h=>h.symm ▸ (by decide : 0<413)) And.right
    exact ⟨u,rest,eq,finalReplay.symm ▸ ⟨Qf,cx _ Qf,legal_issue _ ph (same.symm ▸ range),empty⟩⟩
  rw [E]
  exact before

/-- From arbitrary old command/data on a settled owner chart, the
actual IID process reaches a clean ISSUE0 in linear-width time.
It does not assert that the following healthy RESET chain is complete. -/
theorem arbitrary_to_issue_zero_expected_linear
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (qx : Q x)
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
    let addr := fun j=>S.getD j fall
    let Inv := Boundary Q (oldH6 B base) hh addr len
    let pc := fun y : X=>(ctrlOp.read (y (addr 0).1).long).toNat
    Height.IIDExpectedHittingTimeAtMost step (fun y=>Inv y ∧ pc y=0) x
      (((252*n*W+3*n)+(252*n*W+n))+412*(n+(252*n*W+n))) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let Inv := Boundary Q (oldH6 B base) hh addr len
  let pc := fun y : X=>(ctrlOp.read (y (addr 0).1).long).toNat
  let P := fun y=>Inv y ∧ pc y=0
  have enter := arbitrary_to_boundary_expected_linear hp chart sep Q qx layout closed LF RF dp
    seam flags notShort hn hl lc rc head cont cb cx W wW width
  apply Height.iid_stage_le step hn x Inv P
  · intro t
    apply Nat.le_trans _ (enter t)
    exact DirtyPrepDrainStable.mean_mono_before_hit (Q:=fun _=>True)
      (fun _ _ _ _=>trivial) (fun _ _ h=>.inl h) t x trivial
  · intro y Y
    exact to_issue_zero_expected_linear hp chart sep Q layout closed LF RF dp
      seam flags notShort hn hl lc rc head cont cb cx W wW width Y

end L4.ResidualControllerIID
