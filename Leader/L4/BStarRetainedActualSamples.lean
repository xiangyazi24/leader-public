import Leader.L4.BStarStageCaptureOrigin
import Leader.L4.BStarAcquireAckAncestry

namespace L4.BStarRetainedActualSamples
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarResetSchedule BStarGeneratedOwner BStarOwnerLaunchOrigin BStarLongDoor BStarLongCommand
open BStarGeneratedBandScan BStarSeparatingRail BStarSeparatorControl BStarLongLayout
open BStarAcquireReadout BStarResetChartService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The computation-band origin is not just a syntactically valid
old D. The actual pre-origin history forces a genuine three-win
ACQUIRE. Every stored selector/header remains exactly its own
old sample at the end of the certified band tape. -/
theorem retained_samples {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (initial : Current hp base (fun j => S.getD j fall) len x .idle)
    (w : List (Fin n))
    (origin : Origin hp (S.getD 0 fall).1 x w) :
    ∃ (pre : List (Fin n)) (door : Fin n) (mid : List (Fin n))
      (beforeTurn : List (Fin n)) (turn : Fin n) (ret : List (Fin n))
      (vs : List BStarAcquireLatch.Visit),
      w=pre++door::mid ∧ pre=beforeTurn++turn::ret ∧
      Found hp base (fun j => S.getD j fall) len acquire x beforeTurn (.out len) ∧
      vs.all BStarAcquireLatch.Visit.wins=true ∧
      (∀ j : Fin 3, (vs.filter (fun v => v.incidence.val==j.val)).length=1) ∧
      (∃ (u v : List (Fin n)) (a : Fin n) (ps : List (Pos n)),
        beforeTurn=u++a::v ∧
        BStarAcquireForwardTrace.Trace hp base (step (run x u) a) (S.getD 0 fall)
          v (run x beforeTurn) (S.getD len fall) ps vs) ∧
      ∀ v∈vs, let y := (run x w (S.getD 0 fall).1).long
        (((capturedSelector v.incidence).read y).toNat,((headerBlock v.incidence).read y).toNat)=
          (v.selector.val,v.headers.toNat) := by
  obtain ⟨pre,e,mid,f,W,door,⟨pc5,valid,phase,old⟩,hf,hop,outcome,into6,live⟩ := origin
  let adr := fun j => S.getD j fall
  let i := (adr 0).1
  let y := run x pre
  obtain ⟨m,H,J,cur⟩ := generated_word hp C Q fiber (fun z K d => closed z d K) sep pre .idle I initial
  have mode : m=.busy acquire (.back 0) := by
    cases m with
    | idle =>
      have P := cur.1.2
      exact False.elim ((by decide : (1:Nat)≠2) (P.symm.trans phase))
    | busy op z =>
      have A : op=acquire := cur.1.2.2.2.symm.trans pc5
      subst op
      have K : z=.back 0 := by
        apply Classical.byContradiction
        intro N
        have E := before_receipt cur.2.1 N
        have r := (root_header hp C (fiber _ J)).2
        have rootEq : project adr y 0=atSite (y i).long 0 := by
          change atSite (y i).long (adr 0).2=_
          rw [r]
        rw [rootEq] at E
        rcases E with E|⟨p,E⟩
        · rw [show atSite (y i).long 0=.trail from E] at old
          contradiction
        · obtain ⟨q,Bp⟩ := bound_F (longGeometry B (y i)) 0 p
          have Z : bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.forward q := by
            rw [E]
            exact Bp
          exact Token.noConfusion (Z.symm.trans old)
      rw [K]
  subst m
  have clean : Clean (project adr) anyTag len y := ⟨cur.2.1.2.1,cur.2.1.2.2.2⟩
  have norm := BStarSeparatorReceipt.consume hp C acquire sep cur.1 clean
  have E' : ∀ j≤len, project adr (step y e) j=.empty := door.symm ▸ norm.1
  have consume : Event hp adr len y e (.busy acquire (.back 0)) .idle :=
    .consume acquire door E'
  obtain ⟨u,turn,ret,vs,U,F,T,R,trace,win,once,FIELDS⟩ :=
    BStarAcquireAckAncestry.consume_six_samples hp C sep H consume into6
  refine ⟨pre,e,mid,u,turn,ret,vs,W,U,F,win,once,trace,?_⟩
  intro a A
  have Pa := FIELDS a A
  have hold := BStarCaptureDoorHistory.word_capture_hold hp (step y e) i mid sep
    (fun p m t Y => (live p m t Y).2)
  have snap : BStarAcquireJoined.snapshot ((run (step y e) mid) i).long=
      BStarAcquireJoined.snapshot (step y e i).long :=
    Prod.ext hold.1 hold.2.1
  rw [W,BStarResetSchedule.run_append]
  have loc : rightNeighbor e=i := door.symm ▸ RearTrace.right_predecessor i
  have hh0 : oldH6 B y i=true := (root_header hp C (fiber y J)).1
  have got := BStarAcquisitionToStage.capture_mark hp y e (sep e) f
    (loc.symm ▸ hh0) (loc.symm ▸ valid) (loc.symm ▸ phase) (loc.symm ▸ pc5)
    (loc.symm ▸ old) hf hop outcome
  have read0 : BStarAcquireJoined.snapshot (step y e i).long=BStarAcquireLanding.expected f :=
    loc ▸ got
  have lhs := BStarAcquireReadout.source_fields_payload ((run (step y e) mid) i).long f
    (snap.trans read0) a.incidence
  have rhs := BStarAcquireReadout.source_fields_payload (step y e i).long f read0 a.incidence
  exact lhs.trans (rhs.symm.trans Pa)

/-- Expose the actual old consume witnessed by the backward band
scan, not an independent matching-byte event. -/
theorem origin_consume {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (initial : Current hp base (fun j => S.getD j fall) len x .idle)
    (w : List (Fin n)) (origin : Origin hp (S.getD 0 fall).1 x w) :
    ∃ pre e mid, w=pre++e::mid ∧
      GeneratedOwner hp base (fun j => S.getD j fall) len x .idle pre (.busy acquire (.back 0)) ∧
      Event hp (fun j => S.getD j fall) len (run x pre) e (.busy acquire (.back 0)) .idle ∧
      pc (step (run x pre) e) (S.getD 0 fall).1=6 ∧
      LiveWord hp (S.getD 0 fall).1 (step (run x pre) e) mid := by
  obtain ⟨pre,e,mid,f,W,door,⟨pc5,_,phase,old⟩,_,_,_,into6,live⟩ := origin
  let adr := fun j => S.getD j fall
  let i := (adr 0).1
  let y := run x pre
  obtain ⟨m,H,J,cur⟩ := generated_word hp C Q fiber (fun z K d => closed z d K) sep pre .idle I initial
  have mode : m=.busy acquire (.back 0) := by
    cases m with
    | idle =>
      have P := cur.1.2
      exact False.elim ((by decide : (1:Nat)≠2) (P.symm.trans phase))
    | busy op z =>
      have A : op=acquire := cur.1.2.2.2.symm.trans pc5
      subst op
      have K : z=.back 0 := by
        apply Classical.byContradiction
        intro N
        have E := before_receipt cur.2.1 N
        have r := (root_header hp C (fiber _ J)).2
        have rootEq : project adr y 0=atSite (y i).long 0 := by
          change atSite (y i).long (adr 0).2=_
          rw [r]
        rw [rootEq] at E
        rcases E with E|⟨p,E⟩
        · rw [show atSite (y i).long 0=.trail from E] at old
          contradiction
        · obtain ⟨q,Bp⟩ := bound_F (longGeometry B (y i)) 0 p
          have Z : bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.forward q := by
            rw [E]
            exact Bp
          exact Token.noConfusion (Z.symm.trans old)
      rw [K]
  subst m
  have clean : Clean (project adr) anyTag len y := ⟨cur.2.1.2.1,cur.2.1.2.2.2⟩
  have norm := BStarSeparatorReceipt.consume hp C acquire sep cur.1 clean
  have E' : ∀ j≤len, project adr (step y e) j=.empty := door.symm ▸ norm.1
  have consume : Event hp adr len y e (.busy acquire (.back 0)) .idle :=
    .consume acquire door E'
  exact ⟨pre,e,mid,W,H,consume,into6,live⟩

#print axioms origin_consume
#print axioms retained_samples
end L4.BStarRetainedActualSamples
