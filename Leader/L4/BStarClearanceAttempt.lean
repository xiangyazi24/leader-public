import Leader.L4.BStarClearanceFinish

namespace L4.BStarClearanceAttempt
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearancePhysical BStarClearanceOffset
open BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

open BStarClearanceSettled BStarResetControllerEntry BStarAcquireWaitControl
open BStarLongCommand BStarSeparatorReceipt

theorem from_issue {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    let adr := fun j => S.getD j fall
    let root := (adr 0).1
    let e := RearTrace.predecessor root
    let y := step x e
    let v := (x root).long
    let op := (ctrlOp.read v).toNat
    Issue v →
    (initial op v=none ∧ snapshot (y root).long=((.empty,1),0) ∧
      Q y ∧ correct (oldH6 B base) hh 5 y) ∨
    (∃ a w, let z := BStarResetSchedule.run step y w
      let final := step z e
      initial op v=some a ∧ project adr y 0=forward op a ∧
      Seen step (project adr) anyTag len y (.out 0) w (.back 0) ∧
      Clean (project adr) anyTag len z ∧
      Waiting hp base root op z ∧
      Q final ∧ correct (oldH6 B base) hh 5 final ∧
      (∀ j≤len, project adr final j=.empty) ∧
      (ctrlPhase.read (final root).long).toNat=1 ∧
      ∃ next, (next=0 ∨ (op<next ∧ next<413)) ∧
        (ctrlOp.read (final root).long).toNat=next) := by
  dsimp only
  intro issue
  let adr := fun j => S.getD j fall
  let root := (adr 0).1
  let e := RearTrace.predecessor root
  let y := step x e
  let v := (x root).long
  let op := (ctrlOp.read v).toNat
  let P := fun y : X => Q y ∧ correct (oldH6 B base) hh 5 y
  have pc (y : X) (e : Fin n) (J : P y) : P (step y e) :=
    settled_step hp (oldH6 B base) hh sep Q closed
      (fun q h i => (congrArg Prod.fst (same q h i)).symm) y e J
  have Y : P y := pc x e ⟨I,cx⟩
  rcases issue_chart hp chart (same _ I) sep issue.1 issue.2 with D|⟨a,A,F,G,ctl⟩
  · exact .inl ⟨D.1,D.2,Y⟩
  · have ph : (ctrlPhase.read (y root).long).toNat=2 :=
      congrArg (fun q : BitVec 2 × BitVec 9 => q.1.toNat) ctl
    have pcval : (ctrlOp.read (y root).long).toNat=op :=
      congrArg (fun q : BitVec 2 × BitVec 9 => q.2.toNat) ctl
    have V (w : BitVec LW) : LongDoorGuard.valid manifest w=
        ((((ctrlPhase.read w).toNat==1)||((ctrlPhase.read w).toNat==2)) &&
         decide ((ctrlOp.read w).toNat<413)) := rfl
    have OK : op<413 := by
      have h := issue.1
      rw [V v] at h
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    have wait : Waiting hp base root op y := by
      refine ⟨same _ Y.1,?_,ph,pcval⟩
      change ((((ctrlPhase.read (y root).long).toNat==1)||((ctrlPhase.read (y root).long).toNat==2)) && decide ((ctrlOp.read (y root).long).toNat<413))=true
      rw [ph,pcval]
      simp [OK]
    obtain ⟨w,H,J,K,L⟩ := BStarClearanceFinish.finish_pointed hp chart sep head cont P pc
      (fun q h => same q h.1) (fun q h => heads q h.1) (fun q h => conts q h.1)
      cb Y Y.2 op (.out 0) wait G
    let z := BStarResetSchedule.run step y w
    have endY := pc z e J
    obtain ⟨E,ph',W⟩ := consume hp chart op sep K L
    exact .inr ⟨a,w,A,F,H,L,K,endY.1,endY.2,E,ph',W⟩

theorem arbitrary_attempt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    let adr := fun j => S.getD j fall
    let root := (adr 0).1
    let e := RearTrace.predecessor root
    ∃ (u : List (Fin n)) (a : Nat) (w : List (Fin n)), let z := BStarResetSchedule.run step x u
      let v := step z e
      let r := BStarResetSchedule.run step v w
      let final := step r e
      let op := (ctrlOp.read (z root).long).toNat
      Launch (z root).long (v root).long ∧
      initial op (z root).long=some a ∧ project adr v 0=forward op a ∧
      Seen step (project adr) anyTag len v (.out 0) w (.back 0) ∧
      Clean (project adr) anyTag len r ∧ Waiting hp base root op r ∧
      Q final ∧ correct (oldH6 B base) hh 5 final ∧
      (∀ j≤len, project adr final j=.empty) ∧
      (ctrlPhase.read (final root).long).toNat=1 ∧
      ∃ next, (next=0 ∨ (op<next ∧ next<413)) ∧
        (ctrlOp.read (final root).long).toNat=next := by
  dsimp only
  let adr := fun j => S.getD j fall
  let root := (adr 0).1
  let e := RearTrace.predecessor root
  let P := fun y : X => Q y ∧ correct (oldH6 B base) hh 5 y
  have pc (y : X) (e : Fin n) (J : P y) : P (step y e) :=
    settled_step hp (oldH6 B base) hh sep Q closed
      (fun q h i => (congrArg Prod.fst (same q h i)).symm) y e J
  obtain ⟨u,J,_,L⟩ := reach_launch hp chart sep head cont P pc
    (fun q h => same q h.1) (fun q h => heads q h.1) (fun q h => conts q h.1)
    cb ⟨I,cx⟩ cx
  let z := BStarResetSchedule.run step x u
  have R : root=(endpoint (oldH6 B base) hh o 0).1 := congrArg Prod.fst chart.root
  rw [←R] at L
  change Launch (z root).long (step z e root).long at L
  rcases from_issue hp chart sep head cont Q closed same heads conts cb J.1 J.2 L.1 with bad|G
  · obtain ⟨a,A,_⟩ := L.2
    have q := bad.1
    rw [A] at q
    contradiction
  · obtain ⟨a,w,G⟩ := G
    exact ⟨u,a,w,L,G⟩

end L4.BStarClearanceAttempt
