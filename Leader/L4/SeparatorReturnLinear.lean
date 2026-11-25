import Leader.L4.DirtyOwnerRelease
import Leader.L4.SeparatorReturnIID
import Leader.L4.BStarClearanceFinish
import Leader.L4.BStarClearanceResidual

namespace L4.SeparatorReturnLinear
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

/-- Transfer a raw release clock to the authenticated first receipt on the same IID tape. -/
theorem separator_return_of_release {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (qx : Q x) (cx : correct (oldH6 B base) hh 5 x)
    (op : Nat) (z : Cursor)
    (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j=>S.getD j fall) x) z)
    (cost : Nat)
    (release : Height.IIDExpectedHittingTimeAtMost step
      (fun y=>¬Held (y (S.getD 0 fall).1).long) x cost) :
    let track := project (fun j=>S.getD j fall)
    let Inv := fun y => (Q y ∧ correct (oldH6 B base) hh 5 y) ∧ Waiting hp base (S.getD 0 fall).1 op y
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (Stopped step track anyTag len Inv x z) [] cost := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let track : X → BStarSeparatingRail.Rail := project addr
  let J : X→Prop := fun y=>Q y ∧ correct (oldH6 B base) hh 5 y
  let Inv : X→Prop := fun y=>J y ∧ Waiting hp base root op y
  let P := Stopped step track anyTag len Inv x z
  let H : X → Prop := fun y=>¬Held (y root).long
  have jClosed (y : X) (e : Fin n) (j : J y) : J (step y e) :=
    BStarClearanceSettled.settled_step hp _ hh sep Q closed
      (fun a b i=>(congrArg Prod.fst (same a b i)).symm) y e j
  have atExit (w : List (Fin n)) (E : H (play x w)) : P w := by
    obtain ⟨pre,post,d,W,S',j',W',G',D,U⟩ := BStarSeparatorRing.lift_word hp C J
      (fun y q=>same _ q.1) (fun y q f=>jClosed y f q) sep op w z ⟨qx,cx⟩ wait G
    by_cases hit : d=.back 0
    · exact ⟨pre,post,W,hit ▸ S',⟨j',W'⟩,D hit⟩
    have word : w=pre := by simpa only [U.resolve_left hit,List.append_nil] using W
    rw [word] at E
    exfalso
    apply E
    refine ⟨W'.2.1,W'.2.2.1,?_⟩
    let y := play x pre
    have read : track y 0=atSite (y root).long 0 := by
      change atSite (y root).long (addr 0).2=_
      rw [(root_header hp C W'.1).2]
    exact read ▸ before_receipt G' hit
  classical
  have sum_mono {m : Nat} {f g : Fin m→Nat} (L : ∀ i,f i≤g i) :
      (List.ofFn f).sum ≤ (List.ofFn g).sum := by
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      simp only [List.ofFn_succ,List.sum_cons]
      exact Nat.add_le_add (L 0) (ih (fun i=>L i.succ))
  have compare (t : Nat) (w : List (Fin n)) :
      Height.iidHitCost ResetReturnIID.appendTape P t w ≤ Height.iidHitCost step H t (play x w) := by
    induction t generalizing w with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      by_cases T : P w
      · rw [Height.iidHitCost_of_target _ _ _ T]
        exact Nat.zero_le _
      · have N : ¬H (play x w) := fun q=>T (atExit w q)
        simp only [Height.iidHitCost,if_neg T,if_neg N]
        apply Nat.add_le_add_left
        apply sum_mono
        intro e
        have E : play x (ResetReturnIID.appendTape w e)=step (play x w) e :=
          BStarResetSchedule.run_append _ _ _ _
        rw [←E]
        exact ih _
  intro t
  exact Nat.le_trans (compare t []) (release t)

open BStarLongCommand BStarAcquireWaitControl BStarResetControllerEntry

/-- Production cutoff immediately after the exact independent issue
mark, for any legal old opcode. This charges physical progress to the
first clean returned prefix, not the actual later consume mark. -/
theorem separator_after_launch_of_release {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (qx : Q x) (cx : correct (oldH6 B base) hh 5 x) (cost : Nat) :
    let addr := fun j=>S.getD j fall
    let track : X→BStarSeparatingRail.Rail := project addr
    let root := (addr 0).1
    let op := (ctrlOp.read (x root).long).toNat
    let y := step x (RearTrace.predecessor root)
    let Inv := fun z => (Q z ∧ correct (oldH6 B base) hh 5 z) ∧ Waiting hp base root op z
    Height.IIDExpectedHittingTimeAtMost step (fun u=>¬Held (u root).long) y cost →
    Launch (x root).long (y root).long →
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (Stopped step track anyTag len Inv y (.out 0)) [] cost := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let y := step x door
  let op := (ctrlOp.read (x root).long).toNat
  intro release L
  have qy := closed _ door qx
  have cy := (BStarClearanceSettled.settled_step hp _ hh sep Q closed
      (fun a b i=>(congrArg Prod.fst (same a b i)).symm) x door ⟨qx,cx⟩).2
  obtain ⟨I,a,_,E⟩ := L
  have phase : (ctrlPhase.read (y root).long).toNat=2 :=
    congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.2.toNat) E
  have pc : (ctrlOp.read (y root).long).toNat=op :=
    congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.2.toNat) E
  have ok : op<413 := BStarClearanceResidual.issue_range I
  have legal : LongDoorGuard.valid manifest (y root).long=true := by
    change ((((ctrlPhase.read (y root).long).toNat==1)||
       ((ctrlPhase.read (y root).long).toNat==2)) && decide ((ctrlOp.read (y root).long).toNat<413))=true
    rw [phase,pc]
    simp [ok]
  have front : project addr y 0=forward op a := by
    have K := (root_header hp C (same _ qy)).2
    change atSite (y root).long (addr 0).2=_
    rw [K]
    exact congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.1) E
  exact separator_return_of_release hp C sep Q closed same qy cy
    op (.out 0) ⟨same _ qy,legal,phase,pc⟩
    ⟨Nat.zero_le _,⟨_,front⟩,fun _ J=>(Nat.not_lt_zero _ J).elim⟩ cost release

open BStarFenceLineGeometry BStarH6Ordinal

/-- Uniform linear-width first authenticated receipt after a genuine launch.
The stopped prefix and its unused suffix lie on the unmodified physical tape. -/
theorem separator_after_launch_expected_linear
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
    let track : X→BStarSeparatingRail.Rail := project addr
    let root := (addr 0).1
    let op := (ctrlOp.read (x root).long).toNat
    let y := step x (RearTrace.predecessor root)
    let Inv := fun z => (Q z ∧ correct (oldH6 B base) hh 5 z) ∧ Waiting hp base root op z
    Launch (x root).long (y root).long →
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (Stopped step track anyTag len Inv y (.out 0)) [] (252*n*W) := by
  dsimp only
  let root := (S.getD 0 fall).1
  let door := RearTrace.predecessor root
  have qy := closed x I door
  have release := DirtyOwnerRelease.held_release_expected_linear hp chart sep Q qy layout closed
    LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width
  exact separator_after_launch_of_release hp chart sep Q (fun z e Z=>closed z Z e)
    layout I (cx x I) (252*n*W) release

end L4.SeparatorReturnLinear
