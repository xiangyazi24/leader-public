import Leader.L4.BStarParkedTwoHits

/-! A shadow edge is nominated in the full candidate alphabet. The first
hit either emits that edge or parks the fresh ADMIT that diverted it.
This interface quantifies over *any* eligible gate, not just the source
whose FENCE lines are being shadowed. -/
namespace L4.BStarFenceTwoCandidates
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarLongToken BStarLongLayout BStarResetMarkAdapter BStarSeparatingRail
open BStarGeneratedOwner BStarAcquireVisitOrder BStarH6WordChart BStarH6Ordinal
open BStarResetChartTouch BStarAcquireLiteralChain BStarAdmitIncidentGeometry
open BStarGateStutter BStarBitParity BStarClearanceRaceMark BStarParkedSteering
open BStarSteeringSupport BStarSteeredLikelihood BStarParkedPhysical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A fresh gate carries the actual current owner occurrence, possibly
belonging to a different chart from the FENCE being timed. -/
structure GateOwner (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (i : Fin n) where
  owner : Owners (oldH6 B base)
  sites : List (Pos n)
  length : Nat
  fallback : Pos n
  chart : Chart hp base hh owner sites length fallback
  index : Nat
  atGate : sites.getD index fallback=(i,1)
  current : Current hp base (fun j=>sites.getD j fallback) length x
    (.busy (gateOpcode false) (.out index))
  payload : Payload
  read : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward payload
  opcode : payload.opcode.toNat=gateOpcode false
  healthy : payload.fault=0
  race : payload.race=1

/-- No matter when the first hit arrives, either it goes through or a
second strict occurrence of the same label goes through. The intervening
word is arbitrary subject only to absence of the nominated raw label. -/
theorem emits_in_two {base : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (start : X) {fresh : Word n→Fin n→Prop} {redirect : Word n→Fin n→Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (owners : ∀ a i, fresh a i → GateOwner hp base hh (run start a) i)
    (a skipped : Word n) (e : Fin n) (qa : Q (run start a))
    (avoid : ∀ d∈skipped,d≠e) :
    let emit' := emit (chooseBy redirect)
    chooseBy redirect a e=e ∨
      chooseBy redirect (a++emit' a (e::skipped)) e=e := by
  dsimp only
  cases H : redirect a e with
  | none =>
    left
    unfold chooseBy
    rw [H]
    rfl
  | some f =>
    obtain ⟨i,s,I,F,L,R⟩ := mask a e f H
    subst e
    subst f
    let G := owners a i F
    have freshSound (u : Word n) (j : Fin n) (F' : fresh u j) :
        ∃ v, bind (longGeometry B (run start u j)) 1 (atSite (run start u j).long 1)=.forward v ∧
          v.race=1 :=
      ⟨(owners u j F').payload,(owners u j F').read,(owners u j F').race⟩
    obtain ⟨pay,_,_,_,_,_⟩ := BStarParkedTwoHits.suppressed_then_paid hp G.chart Q fiber
      closed ready distinct start mask freshSound i G.index G.atGate I G.payload
      G.opcode G.healthy s G.race a skipped qa G.current G.read H avoid
    right
    simpa only [emit,chooseBy,H,Option.getD_some,List.append_assoc,List.cons_append,
      List.nil_append] using pay

theorem emit_append {n : Nat} (choose : Word n→Fin n→Fin n)
    (a u v : Word n) :
    emit choose a (u++v)=emit choose a u++emit choose (a++emit choose a u) v := by
  induction u generalizing a with
  | nil => simp [emit]
  | cons e u ih =>
    rw [List.cons_append,emit,emit,ih]
    simp only [List.cons_append,List.append_assoc,List.nil_append]

/-- A cut is followed by an arbitrary delay, then the first nominated
hit, a hit-free wait, and the second hit. The emitted suffix through
that second hit necessarily contains the requested physical label. -/
theorem emits_by_second_hit {base : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (start : X) {fresh : Word n→Fin n→Prop} {redirect : Word n→Fin n→Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (owners : ∀ a i, fresh a i → GateOwner hp base hh (run start a) i)
    (a w skipped : Word n) (e : Fin n) (qa : Q (run start a))
    (avoid : ∀ d∈skipped,d≠e) :
    e∈emit (chooseBy redirect) a (w++e::(skipped++[e])) := by
  let choose := chooseBy redirect
  have allQ (x : X) (v : Word n) (hx : Q x) : Q (run x v) := by
    induction v generalizing x with
    | nil => exact hx
    | cons d v ih => exact ih _ (closed _ hx d)
  let b := a++emit choose a w
  have qb : Q (run start b) := by
    unfold b
    rw [BStarResetSchedule.run_append]
    exact allQ _ _ qa
  change e∈emit choose a (w++e::(skipped++[e]))
  rw [emit_append]
  apply List.mem_append_right
  change e∈emit choose b (e::(skipped++[e]))
  rcases emits_in_two hp Q fiber closed ready distinct start mask owners b skipped e qb avoid with h|h
  · rw [emit,show choose b e=e from h]
    exact List.mem_cons_self
  · have E : e::(skipped++[e])=(e::skipped)++[e] := rfl
    rw [E,emit_append]
    apply List.mem_append_right
    rw [emit,show choose (b++emit choose b (e::skipped)) e=e from h,emit]
    exact List.mem_cons_self

#print axioms emits_in_two
#print axioms emits_by_second_hit
end L4.BStarFenceTwoCandidates
