import Leader.L4.SeparatorReturnLinear
import Leader.L4.SeparatorConsumeIID
import Leader.L4.Height.LeaderBridge

namespace L4.SeparatorReturnConsume
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarLongDoor
open BStarClearanceSource BStarClearancePhysical BStarClearanceOffset
open BStarFenceLineGeometry BStarH6Ordinal BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- An earlier authenticated receipt followed by the first own door mark
after it. Both cuts occur on the unmodified tape. -/
def ReturnConsumed (base x : X) (addr : Nat→Pos n) (len op : Nat)
    (Q : X→Prop) (z : Cursor) (w : List (Fin n)) : Prop :=
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let track := project addr
  ∃ pre gap tail, w=pre++(gap++door::tail) ∧ door∉gap ∧
    Seen step track anyTag len x z pre (.back 0) ∧
    (let y := play x pre
     Q y ∧ Waiting hp base root op y ∧ Clean track anyTag len y) ∧
    (let y := play x (pre++gap)
     Q y ∧ Waiting hp base root op y ∧ Clean track anyTag len y) ∧
    (let q := step (play x (pre++gap)) door
     Q q ∧ (∀ j≤len, track q j=.empty) ∧ (ctrlPhase.read (q root).long).toNat=1 ∧
      ∃ pc,(pc=0 ∨ (op<pc ∧ pc<413)) ∧ (ctrlOp.read (q root).long).toNat=pc)

private theorem sums_mono {m : Nat} {f g : Fin m→Nat} (H : ∀ i,f i≤g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (H 0) (ih (fun i=>H i.succ))

private theorem cost_mono {U : Type} {m : Nat} (next : U→Fin m→U)
    (P R : U→Prop) (imp : ∀ y, P y→R y) (t : Nat) (y : U) :
    Height.iidHitCost next R t y ≤ Height.iidHitCost next P t y := by
  classical
  induction t generalizing y with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    by_cases T : R y
    · rw [Height.iidHitCost_of_target _ _ _ T]
      exact Nat.zero_le _
    · have N : ¬P y := fun q=>T (imp y q)
      simp only [Height.iidHitCost,if_neg T,if_neg N]
      exact Nat.add_le_add_left (sums_mono (fun e=>ih (next y e))) _

theorem return_consume_expected_of_return {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (hn : 0<n)
    (Q : X→Prop) (closed : ∀ y e,Q y→Q (step y e))
    (same : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (z : Cursor) (cost : Nat)
    (H : let addr := fun j=>S.getD j fall
         let root := (addr 0).1
         let Inv := fun y => (Q y ∧ correct (oldH6 B base) hh 5 y) ∧ Waiting hp base root op y
         Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
           (Stopped step (project addr) anyTag len Inv x z) [] cost) :
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (ReturnConsumed hp base x (fun j=>S.getD j fall) len op Q z) [] (cost+n) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let Inv : X→Prop := fun y=>Q y ∧ Waiting hp base root op y ∧ Clean (project addr) anyTag len y
  let A := Stopped step (project addr) anyTag len
    (fun y=>(Q y ∧ correct (oldH6 B base) hh 5 y) ∧ Waiting hp base root op y) x z
  let P := ReturnConsumed hp base x addr len op Q z
  let Live : List (Fin n) → Nat → Prop := fun w k=>k=1 ∧
    ∃ pre gap, w=pre++gap ∧ door∉gap ∧ Seen step (project addr) anyTag len x z pre (.back 0) ∧
      Inv (play x pre) ∧ Inv (play x w)
  have hit {w pre gap tail : List (Fin n)}
      (W : w=pre++(gap++door::tail)) (N : door∉gap)
      (S0 : Seen step (project addr) anyTag len x z pre (.back 0))
      (I0 : Inv (play x pre)) (I : Inv (play x (pre++gap))) : P w :=
    ⟨pre,gap,tail,W,N,S0,I0,I,closed _ _ I.1,
      BStarSeparatorReceipt.consume hp C op sep I.2.1 I.2.2⟩
  have advance (w : List (Fin n)) (k : Nat) (L : Live w k) : ∃ d : Fin n, ∀ e : Fin n,
      P (ResetReturnIID.appendTape w e) ∨
        ∃ k', Live (ResetReturnIID.appendTape w e) k' ∧ k'≤k ∧ (e=d→k'<k) := by
    refine ⟨door,fun e=>?_⟩
    obtain ⟨rfl,pre,gap,W,N,S0,I0,I⟩ := L
    subst w
    by_cases E : e=door
    · subst e
      exact .inl (hit (tail:=[]) (List.append_assoc _ _ _) N S0 I0 I)
    · refine .inr ⟨1,⟨rfl,pre,gap++[e],List.append_assoc _ _ _,?_,S0,I0,?_⟩,Nat.le_refl _,fun h=>(E h).elim⟩
      · simpa [E,Ne.symm E] using N
      · rw [ResetReturnIID.appendTape,BStarResetSchedule.run_append]
        exact SeparatorConsumeIID.hold_before_door hp C sep Q closed same e E I.1 I.2.1 I.2.2
  have part (w : List (Fin n)) (T : A w) : P w ∨ Live w 1 := by
    obtain ⟨pre,post,rfl,S0,⟨⟨q,_⟩,wait⟩,clean⟩ := T
    have I0 : Inv (play x pre) := ⟨q,wait,clean⟩
    have split (gap tail : List (Fin n)) (N : door∉gap) (I : Inv (play x (pre++gap))) :
        P (pre++(gap++tail)) ∨ Live (pre++(gap++tail)) 1 := by
      induction tail generalizing gap with
      | nil =>
        simp only [List.append_nil]
        exact .inr ⟨rfl,pre,gap,rfl,N,S0,I0,I⟩
      | cons e rest ih =>
        by_cases E : e=door
        · subst e
          exact .inl (hit rfl N S0 I0 I)
        · have N' : door∉gap++[e] := by simpa [E,Ne.symm E] using N
          have I' : Inv (play x (pre++(gap++[e]))) := by
            rw [←List.append_assoc,BStarResetSchedule.run_append]
            exact SeparatorConsumeIID.hold_before_door hp C sep Q closed same e E I.1 I.2.1 I.2.2
          simpa only [List.append_assoc,List.singleton_append] using ih (gap++[e]) N' I'
    simpa using split [] post (by simp) (by simpa using I0)
  have first : Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape (fun w=>A w∨P w) [] cost :=
    fun t=>Nat.le_trans (cost_mono _ A _ (fun _ v=>.inl v) t []) (H t)
  apply Height.iid_stage_le ResetReturnIID.appendTape hn [] A P cost n first
  intro w T
  simpa only [Nat.mul_one] using
    ResetReturnIID.iid_of_relational_rank ResetReturnIID.appendTape P Live
      (fun _ _ L=>L.1.symm ▸ Nat.one_pos) advance w 1 (part w T)

/-- From a real launch the first pointed receipt and first later own door
consume cost at most (252W+1)n expected marks on one physical IID tape. -/
theorem return_consume_after_launch_expected_linear
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
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let op := (ctrlOp.read (x root).long).toNat
    let y := step x (RearTrace.predecessor root)
    Launch (x root).long (y root).long →
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (ReturnConsumed hp base y addr len op Q (.out 0)) [] (252*n*W+n) := by
  dsimp only
  intro L
  apply return_consume_expected_of_return hp chart sep hn Q (fun z e Z=>closed z Z e) layout
  exact SeparatorReturnLinear.separator_after_launch_expected_linear hp chart sep Q I layout closed
    LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width L

end L4.SeparatorReturnConsume
