import Leader.L4.BStarBitGateCover
import Leader.L4.BStarBitFlight
import Leader.L4.BStarBitHealthyService

namespace L4.BStarBitGatePositive
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarClearanceOffset BStarBitGateGeometry BStarClearanceRaceMark
open BStarBitParity BStarBitDepart BStarBitHealthyService BStarBitSegment BStarBitGateCover
open BStarLongDoor BStarLongLayout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every physical mark of a healthy gate implements exactly its
literal phase scanner. Here the cursor progress is the conclusion,
not a supplied future departure or healthy return. -/
theorem next_actual_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (qx : Q x) (ready : correct (oldH6 B base) hh 5 x)
    (I : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (v : Payload) (F : v.fault=0) (Op : v.opcode.toNat=bitOp) (out : v.outcome=0) (arg : v.argument=0)
    (phase : Phase) (old : atSite (x i).long 1=.forward {v with race:=cycleCode phase})
    (e : Fin n) :
    match nextPhase i phase e with
    | some next =>
      Event hp (fun j=>S.getD j fall) len x e (.busy bitOp (.out k)) (.busy bitOp (.out k)) ∧
      Current hp base (fun j=>S.getD j fall) len (step x e) (.busy bitOp (.out k)) ∧
      atSite (step x e i).long 1=.forward {v with race:=cycleCode next}
    | none => ∃ s, phase=.complete s ∧ e=i ∧
      Event hp (fun j=>S.getD j fall) len x e (.busy bitOp (.out k)) (.busy bitOp (.out (k+1))) ∧
      Current hp base (fun j=>S.getD j fall) len (step x e) (.busy bitOp (.out (k+1))) ∧
      project (fun j=>S.getD j fall) (step x e) (k+1)=.forward (cleanBit v s) := by
  have fixed : ∀ j,oldH6 B x j=oldH6 B base j := fun j=>(congrArg Prod.fst (fiber x qx j)).symm
  have off := next_not_gate hp fixed ready i O
  have localStep := literal_phase_step hp C fixed ready sep i k idx O I v F Op out arg phase old off e
  obtain ⟨m,E,nextI⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out k)) I
  cases E with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go A G tail =>
      cases tail
      cases scan : nextPhase i phase e with
      | some next =>
        rw [scan] at localStep
        cases A with
        | stay _ => exact ⟨.transit _ _ _ live (.cons M go (.stay _) G (.nil _ _)),nextI,localStep⟩
        | forward _ =>
          have trail := nextI.2.1.2.2 k (by omega)
          change atCursor (step x e) (S.getD k fall)=.trail at trail
          rw [idx] at trail
          exact Token.noConfusion (trail.symm.trans localStep)
        | turn => omega
      | none =>
        rw [scan] at localStep
        obtain ⟨s,phaseEnd,mark,trail,land⟩ := localStep
        cases A with
        | stay _ =>
          obtain ⟨p,P⟩ := nextI.2.1.2.1
          change atCursor (step x e) (S.getD k fall)=.forward p at P
          rw [idx] at P
          exact Token.noConfusion (P.symm.trans trail)
        | forward _ =>
          have next := BStarBitFlight.chart_successor hp C fixed i k K idx
          have P : project (fun j=>S.getD j fall) (step x e) (k+1)=.forward (cleanBit v s) := by
            change atCursor (step x e) (S.getD (k+1) fall)=_
            rwa [next]
          exact ⟨s,phaseEnd,mark,.transit _ _ _ live (.cons M go (.forward k) G (.nil _ _)),nextI,P⟩
        | turn => omega

/-- Positive physical extraction of the scanner's first completing
prefix. It admits all real marks, including repeats and unrelated
interleavings, on the same original tape. -/
theorem exits_when_scanner_exits {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (v : Payload) (F : v.fault=0) (Op : v.opcode.toNat=bitOp) (out : v.outcome=0) (arg : v.argument=0)
    (w : List (Fin n)) :
    ∀ (phase : Phase) (x : X), Q x → correct (oldH6 B base) hh 5 x →
      Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)) →
      atSite (x i).long 1=.forward {v with race:=cycleCode phase} →
      w.foldl (absorbing i) (.some phase)=none →
    ∃ pre post s, w=pre++post ∧ readSegment i phase pre=some s ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out k) pre (.out (k+1)) ∧
      project (fun j=>S.getD j fall) (play x pre) (k+1)=.forward (cleanBit v s) ∧
      Wire (cleanBit v s) := by
  have well (s : Side) : Wire (cleanBit v s) := by
    refine ⟨F,Op,rfl,out,?_⟩
    cases s
    · change (1 : Nat)<2; decide
    · change (0 : Nat)<2; decide
  induction w with
  | nil =>
    intro phase x _ _ _ _ impossible
    contradiction
  | cons e w ih =>
    intro phase x qx ready I old exit
    have Local := next_actual_mark hp C Q fiber closed sep i k K idx O qx ready I v F Op out arg phase old e
    cases scan : nextPhase i phase e with
    | some next =>
      rw [scan] at Local
      have ready' := BStarClearanceOffset.stable hp _ hh x e (sep e)
        (fun j=>(congrArg Prod.fst (fiber x qx j)).symm) (BStarClearanceOffsetMask.leftFrame hp x e) ready
      have E : w.foldl (absorbing i) (some next)=none := by
        change w.foldl (absorbing i) (nextPhase i phase e)=none at exit
        rwa [scan] at exit
      obtain ⟨pre,post,s,W,Read,T,P,verified⟩ := ih next (step x e) (closed _ qx e) ready' Local.2.1 Local.2.2 E
      exact ⟨e::pre,post,s,congrArg (List.cons e) W,by simp [readSegment,scan,Read],
        .cons I Local.1 T,P,verified⟩
    | none =>
      rw [scan] at Local
      obtain ⟨s,markPhase,_,Ev,Next,P⟩ := Local
      refine ⟨[e],w,s,rfl,?_,.cons I Ev (.nil Next),P,well s⟩
      subst phase
      simp [readSegment,scan]

/-- On the true physical gate, the fixed L,R,L subsequence suffices
from the canonical pending state. The output reports the actual
first side; it is not chosen by the service word. -/
theorem gate_exits_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (v : Payload) (F : v.fault=0) (Op : v.opcode.toNat=bitOp) (out : v.outcome=0) (arg : v.argument=0)
    (w : List (Fin n))
    (cover : [incident i .left,incident i .right,incident i .left].Sublist w)
    (qx : Q x) (ready : correct (oldH6 B base) hh 5 x)
    (I : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (old : atSite (x i).long 1=.forward {v with race:=1}) :
    ∃ pre post s, w=pre++post ∧ readSegment i .fresh pre=some s ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out k) pre (.out (k+1)) ∧
      project (fun j=>S.getD j fall) (play x pre) (k+1)=.forward (cleanBit v s) ∧
      Wire (cleanBit v s) := by
  have diff : incident i .left≠incident i .right := by
    intro E
    exact Side.noConfusion (incident_injective (oldH6 B base) hh i i O O .left .right E).2
  exact exits_when_scanner_exits hp C Q fiber closed sep i k K idx O v F Op out arg w
    .fresh x qx ready I old (left_right_left i diff .fresh w cover)

end L4.BStarBitGatePositive
