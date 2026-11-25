import Leader.L4.ResetReturnIID
import Leader.L4.BStarClearanceFinish
import Leader.L4.BStarClearanceResidual

namespace L4.SeparatorReturnIID
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

/-- Arbitrary opcode after an actual pointed separation launch. Raw
marks may park a forward cursor, so pay the literal four-coordinate
clearance rank, not the healthy RESET cursor rank. No source consume
is included and no linear-width bound is claimed for the scalar. -/
theorem separator_return_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (heads : ∀ y,Q y → ∀ i,let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y,Q y → ∀ i,let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (cap : Four) (bounded : ∀ y,Q y → Bounded cap (coord hp base hh o S y))
    (qx : Q x) (cx : correct (oldH6 B base) hh 5 x)
    (op : Nat) (z : Cursor)
    (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j=>S.getD j fall) x) z) :
    let track := project (fun j=>S.getD j fall)
    let Inv := fun y => (Q y ∧ correct (oldH6 B base) hh 5 y) ∧ Waiting hp base (S.getD 0 fall).1 op y
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (Stopped step track anyTag len Inv x z) [] (n*(scalar cap (coord hp base hh o S x)+1)) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let track : X → BStarSeparatingRail.Rail := project addr
  let J : X→Prop := fun y=>Q y ∧ correct (oldH6 B base) hh 5 y
  let Inv : X→Prop := fun y=>J y ∧ Waiting hp base root op y
  let P := Stopped step track anyTag len Inv x z
  let weight := fun (y : X)=>scalar cap (coord hp base hh o S y)+1
  let Live := fun (w : List (Fin n)) (r : Nat)=>∃ d, Seen step track anyTag len x z w d ∧ Inv (play x w) ∧
    Good anyTag len (track (play x w)) d ∧ d≠.back 0 ∧ r=weight (play x w)
  have jClosed (y : X) (e : Fin n) (j : J y) : J (step y e) :=
    BStarClearanceSettled.settled_step hp _ hh sep Q closed
      (fun a b i=>(congrArg Prod.fst (same a b i)).symm) y e j
  have pos (w : List (Fin n)) (r : Nat) (l : Live w r) : 0<r := by
    obtain ⟨_,_,_,_,_,E⟩ := l
    rw [E]
    exact Nat.zero_lt_succ _
  have advance (w : List (Fin n)) (r : Nat) (l : Live w r) : ∃ e : Fin n, ∀ f : Fin n,
      P (ResetReturnIID.appendTape w f) ∨
      ∃ r', Live (ResetReturnIID.appendTape w f) r' ∧ r'≤r ∧ (f=e→r'<r) := by
    obtain ⟨d,S,I,g,live,R⟩ := l
    let old := play x w
    have H : Held (old (endpoint (oldH6 B base) hh o 0).1).long := by
      rw [←show root=(endpoint (oldH6 B base) hh o 0).1 from congrArg Prod.fst C.root]
      refine ⟨I.2.2.1,I.2.2.2.1,?_⟩
      have read : track old 0=atSite (old root).long 0 := by
        change atSite (old root).long (addr 0).2=_
        rw [(root_header hp C I.2.1).2]
      exact read ▸ before_receipt g live
    obtain ⟨e,pay⟩ := held_nominate hp C (same _ I.1.1) cb I.1.2 sep head cont
      (heads _ I.1.1) (conts _ I.1.1) H
    refine ⟨e,fun f=>?_⟩
    obtain ⟨pre,post,d',W,S',j',W',G',D,E⟩ := BStarSeparatorRing.lift_word hp C J
      (fun y q=>same _ q.1) (fun y q f=>jClosed y f q) sep op [f] d I.1 I.2 g
    by_cases stop : d'=.back 0
    · left
      refine ⟨w++pre,post,?_,Seen.append S (stop ▸ S'),?_,?_⟩
      · unfold ResetReturnIID.appendTape
        rw [W,List.append_assoc]
      · rw [BStarResetSchedule.run_append]
        exact ⟨j',W'⟩
      · rw [BStarResetSchedule.run_append]
        exact D stop
    · have rest := E.resolve_left stop
      have word : [f]=pre := by simpa only [rest,List.append_nil] using W
      subst pre
      let new := step old f
      have replay : play x (ResetReturnIID.appendTape w f)=new :=
        BStarResetSchedule.run_append _ _ _ _
      have Wk := before_weak hp C (same _ I.1.1) cb I.1.2 f (sep f) H
      have bOld := bounded old I.1.1
      have bNew := bounded new j'.1
      right
      refine ⟨weight new,⟨d',Seen.append S S',?_,?_,stop,congrArg weight replay.symm⟩,?_,?_⟩
      · rw [replay]; exact ⟨j',W'⟩
      · rw [replay]; exact G'
      · rw [R]
        exact Nat.add_le_add_right ((scalar_le bNew bOld).mpr Wk) 1
      · intro eq
        subst f
        rw [R]
        exact Nat.add_lt_add_right ((scalar_lt bNew bOld).mpr pay) 1
  refine ResetReturnIID.iid_of_relational_rank ResetReturnIID.appendTape P Live pos advance [] (weight x) ?_
  by_cases terminal : z=.back 0
  · subst z
    exact .inl ⟨[],[],rfl,.nil _ _,⟨⟨qx,cx⟩,wait⟩,⟨G.2.1,G.2.2.2⟩⟩
  · exact .inr ⟨z,.nil _ _,⟨⟨qx,cx⟩,wait⟩,G,terminal,rfl⟩

#print axioms separator_return_expected

open BStarLongCommand BStarAcquireWaitControl BStarResetControllerEntry

/-- Production cutoff immediately after the exact independent issue
mark, for any legal old opcode. This charges physical progress to the
first clean returned prefix, not the actual later consume mark. -/
theorem separator_after_launch_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (heads : ∀ y,Q y → ∀ i,let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y,Q y → ∀ i,let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (cap : Four) (bounded : ∀ y,Q y → Bounded cap (coord hp base hh o S y))
    (qx : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    let addr := fun j=>S.getD j fall
    let track : X→BStarSeparatingRail.Rail := project addr
    let root := (addr 0).1
    let op := (ctrlOp.read (x root).long).toNat
    let y := step x (RearTrace.predecessor root)
    let Inv := fun z => (Q z ∧ correct (oldH6 B base) hh 5 z) ∧ Waiting hp base root op z
    Launch (x root).long (y root).long →
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (Stopped step track anyTag len Inv y (.out 0)) [] (n*(scalar cap (coord hp base hh o S y)+1)) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let y := step x door
  let op := (ctrlOp.read (x root).long).toNat
  intro L
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
  exact separator_return_expected hp C sep head cont Q closed same heads conts cb cap bounded qy cy
    op (.out 0) ⟨same _ qy,legal,phase,pc⟩
    ⟨Nat.zero_le _,⟨_,front⟩,fun _ J=>(Nat.not_lt_zero _ J).elim⟩

#print axioms separator_after_launch_expected
end L4.SeparatorReturnIID
