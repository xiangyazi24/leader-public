import Leader.L4.BStarParkedPhysical

namespace L4.BStarParkedTwoHits
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

private theorem at_incident {n : Nat} (i : Fin n) (s : Side) :
    BStarAcquireDoorHistory.siteOf (incident i s) s=i := by
  cases s
  · rfl
  · exact RearTrace.right_predecessor i

/-- If the nominated candidate is diverted at an actual fresh ADMIT,
the next hit of that same candidate is emitted undiverted and completes
the race. All intervening candidate marks are replayed through the
actual steering function; only absence of this nominated candidate is
assumed. This pays the missing-side observation, not the next departure. -/
theorem suppressed_then_paid {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (start : X) {fresh : Word n→Fin n→Prop} {redirect : Word n→Fin n→Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (freshSound : ∀ (a : Word n) (j : Fin n), fresh a j →
      let y := run start a
      ∃ u, bind (longGeometry B (y j)) 1 (atSite (y j).long 1)=.forward u ∧ u.race=1)
    (i : Fin n) (k : Nat) (atGate : S.getD k fall=(i,1))
    (I : oldOrdinal B base hh i=gateOrdinal false)
    (v : Payload) (op : v.opcode.toNat=gateOpcode false) (fault : v.fault=0)
    (s : Side) (race : v.race=1)
    (a skipped : Word n)
    (qa : Q (run start a))
    (cur : Current hp base (fun j=>S.getD j fall) len (run start a)
      (.busy (gateOpcode false) (.out k)))
    (read : bind (longGeometry B (run start a i)) 1 (atSite (run start a i).long 1)=.forward v)
    (divert : redirect a (incident i s)=some (incident i (opposite s)))
    (avoid : ∀ e∈skipped,e≠incident i s) :
    let f := incident i (opposite s)
    let e := incident i s
    let mid := (a++[f])++emit (chooseBy redirect) (a++[f]) skipped
    let y := run start mid
    let old := {v with race:=firstCode (opposite s)}
    let paid := {v with race:=finalCode (opposite s)}
    chooseBy redirect mid e=e ∧
      a++emit (chooseBy redirect) a (e::(skipped++[e]))=mid++[e] ∧
      Event hp (fun j=>S.getD j fall) len y e
        (.busy (gateOpcode false) (.out k)) (.busy (gateOpcode false) (.out k)) ∧
      bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward old ∧
      (kField 1).read (run start (mid++[e]) i).long=encode (.forward paid) ∧
      Current hp base (fun j=>S.getD j fall) len (run start (mid++[e]))
        (.busy (gateOpcode false) (.out k)) := by
  dsimp only
  let t := opposite s
  let f := incident i t
  let e := incident i s
  let b := a++[f]
  let mid := b++emit (chooseBy redirect) b skipped
  let y := run start mid
  let first := {v with race:=firstCode t}
  let changeOne (p : Word n) (d : Fin n) : run start (p++[d])=step (run start p) d := by
    rw [BStarResetSchedule.run_append]
    rfl
  have gateAt (x : X) (qx : Q x) : gate (gateOpcode false) 1 (longGeometry B (x i))=true :=
    (selected_gate_iff hp hh (fun j=>(congrArg Prod.fst (fiber x qx j)).symm)
      (ready x qx) i 1 false).mpr ⟨rfl,I⟩
  obtain ⟨bytes,_,C1,R1⟩ := observed_race_step hp C Q fiber closed distinct i f false k qa
    atGate cur v read op fault (ready _ qa) (ready _ (closed _ qa f))
    (gateAt _ qa) t (at_incident i t) (firstCode t) (.inl ⟨race,rfl⟩)
  have qb : Q (run start b) := (changeOne a f).symm ▸ closed _ qa f
  have Cb : Current hp base (fun j=>S.getD j fall) len (run start b)
      (.busy (gateOpcode false) (.out k)) := (changeOne a f).symm ▸ C1
  have Rb : bind (longGeometry B (run start b i)) 1 (atSite (run start b i).long 1)=.forward first :=
    (changeOne a f).symm ▸ R1
  have Fb : (kField 1).read (run start b i).long=encode (.forward first) :=
    (changeOne a f).symm ▸ bytes
  have avoid' : ∀ d∈skipped,d≠incident i (opposite t) := by
    rw [show opposite t=s from opposite_opposite s]
    exact avoid
  obtain ⟨qy,Cy,Ry,_,self⟩ := parked_after_skipped hp C Q fiber closed ready distinct start
    mask freshSound i k atGate I first op fault t rfl skipped b qb Cb Rb Fb avoid'
  have Ey : chooseBy redirect mid e=e := by
    simpa only [t,opposite_opposite] using self
  have word : a++emit (chooseBy redirect) a (e::(skipped++[e]))=mid++[e] := by
    have firstHit : chooseBy redirect a e=f := by
      unfold chooseBy
      exact congrArg (fun u : Option (Fin n)=>u.getD e) divert
    rw [emit,firstHit]
    have out := parked_first_candidate mask b skipped [] i I s
    have nf : ¬fresh mid i := by
      intro freshNow
      obtain ⟨u,U,H⟩ := freshSound mid i freshNow
      rw [Ry] at U
      have E := Token.forward.inj U
      subst u
      change firstCode t=1 at H
      exact (show ∀ s : Side, firstCode s≠1 from fun s=>by cases s <;> decide) t H
    specialize out nf
    simp only [emit] at out
    change emit (chooseBy redirect) b (skipped++[e])=emit (chooseBy redirect) b skipped++[e] at out
    rw [out]
    simp only [mid,b,List.append_assoc,List.cons_append,List.nil_append]
  have diff : t≠s := by cases s <;> decide
  obtain ⟨done,Ev,Final,_⟩ := observed_race_step hp C Q fiber closed distinct i e false k qy
    atGate Cy first Ry op fault (ready _ qy) (ready _ (closed _ qy e))
    (gateAt _ qy) s (at_incident i s) (finalCode t) (.inr ⟨t,diff,rfl,rfl⟩)
  refine ⟨Ey,word,Ev,Ry,?_,?_⟩
  · rw [changeOne]
    exact done
  · rw [changeOne]
    exact Final

#print axioms suppressed_then_paid
end L4.BStarParkedTwoHits
