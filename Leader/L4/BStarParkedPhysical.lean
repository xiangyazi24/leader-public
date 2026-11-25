import Leader.L4.BStarParkedSteering
import Leader.L4.BStarGateStutter

namespace L4.BStarParkedPhysical
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarLongToken BStarLongLayout BStarResetMarkAdapter BStarSeparatingRail
open BStarGeneratedOwner BStarAcquireVisitOrder BStarH6WordChart BStarH6Ordinal
open BStarResetChartTouch BStarAcquireLiteralChain BStarAdmitIncidentGeometry
open BStarGateStutter BStarBitParity BStarClearanceRaceMark BStarParkedSteering
open BStarSteeringSupport BStarSteeredLikelihood

private theorem site_incident {n : Nat} (e i : Fin n) (s : Side)
    (H : BStarAcquireDoorHistory.siteOf e s=i) : e=incident i s := by
  cases s
  · exact H
  · change rightNeighbor e=i at H
    exact (RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor H)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- Physical residence on all emitted marks before the first nominated
candidate, even while other gates are predictably steered. Freshness
soundness mentions only the actual bound ADMIT at the same site. -/
theorem parked_after_skipped {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (start : X) {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (freshSound : ∀ (a : Word n) (j : Fin n), fresh a j →
      let y := BStarResetSchedule.run step start a
      ∃ u, BStarLongCommand.bind (longGeometry B (y j)) 1 (atSite (y j).long 1)=.forward u ∧ u.race=1)
    (i : Fin n) (k : Nat) (atGate : S.getD k fall=(i,1))
    (I : oldOrdinal B base hh i=gateOrdinal false)
    (v : Payload) (op : v.opcode.toNat=gateOpcode false) (fault : v.fault=0)
    (s : Side) (race : v.race=firstCode s)
    (skipped a : Word n)
    (q : Q (BStarResetSchedule.run step start a))
    (cur : Current hp base (fun j => S.getD j fall) len (BStarResetSchedule.run step start a)
      (.busy (gateOpcode false) (.out k)))
    (read : let y := BStarResetSchedule.run step start a
      BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward v)
    (encoded : (kField 1).read ((BStarResetSchedule.run step start a) i).long=encode (.forward v))
    (avoid : ∀ e∈skipped, e≠incident i (opposite s)) :
    let a' := a++emit (chooseBy redirect) a skipped
    let y := BStarResetSchedule.run step start a'
    Q y ∧ Current hp base (fun j => S.getD j fall) len y (.busy (gateOpcode false) (.out k)) ∧
      BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward v ∧
      (kField 1).read (y i).long=encode (.forward v) ∧
      chooseBy redirect a' (incident i (opposite s))=incident i (opposite s) := by
  have nonfresh (a : Word n) (h : let y := BStarResetSchedule.run step start a
      BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward v) :
      ¬fresh a i := by
    intro M
    obtain ⟨u,U,R⟩ := freshSound a i M
    dsimp only at U h
    rw [h] at U
    have E := Token.forward.inj U
    subst u
    rw [race] at R
    cases s <;> contradiction
  induction skipped generalizing a with
  | nil =>
    simp only [emit,List.append_nil]
    exact ⟨q,cur,read,encoded,parked_candidate_unchanged mask a i I (nonfresh a read) _⟩
  | cons e w ih =>
    let f := chooseBy redirect a e
    have F : f≠incident i (opposite s) := fun eq =>
      avoid e (List.mem_cons_self) ((parked_fiber mask a i I (nonfresh a read) _ e).mp eq)
    have hit (a : Fin n) (ha : a∈[f]) (t : Side)
        (H : BStarAcquireDoorHistory.siteOf a t=i) : t=s := by
      have E : a=f := by simpa only [List.mem_singleton] using ha
      subst a
      by_cases T : t=s
      · exact T
      · have K : t=opposite s := by cases t <;> cases s <;> simp_all [opposite]
        exact (F ((site_incident f i t H).trans (congrArg (incident i) K))).elim
    obtain ⟨next,readNext,rawNext⟩ := first_wait_word hp C Q fiber closed ready distinct
      i false k atGate I v op fault s race [f] _ q cur read encoded hit
    have R : BStarResetSchedule.run step start (a++[f]) =
        step (BStarResetSchedule.run step start a) f := by
      rw [BStarResetSchedule.run_append]
      rfl
    have tail := ih (a++[f]) (R.symm ▸ closed _ q f)
      (R.symm ▸ next) (R.symm ▸ readNext) (R.symm ▸ rawNext)
      (fun b M => avoid b (List.mem_cons_of_mem _ M))
    simpa only [emit,List.append_assoc,List.singleton_append] using tail

end L4.BStarParkedPhysical
