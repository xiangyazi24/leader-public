import Leader.L4.BStarGeneratedOwner
import Leader.L4.BStarGateUnmask

namespace L4.BStarGateIncoming
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarLongToken BStarLongTransport BStarLongKOne BStarLongLayout
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarSeparatingRail BStarAcquireAnchors
open BStarAdmitIncidentGeometry BStarGeneratedOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem chart_advance_incoming {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (e : Fin n) (body : oldH6 B x (rightNeighbor e)=false)
    {k : Nat} (hk : k≤len) (atGate : S.getD k fall=(rightNeighbor e,1)) :
    ∃ j, j+1=k ∧ S.getD j fall=(e,1) := by
  have size := C.length
  have body' : oldH6 B base (rightNeighbor e)=false :=
    (congrArg Prod.fst (same (rightNeighbor e))).trans body
  have mem : advance∈orderedCommands (oldPair B base e) := by
    apply (one_mem _ _ (by rfl)).mpr
    change (if oldH6 B base (rightNeighbor e) then advance=enter ∨ advance=exit else advance=advance)
    simp [body']
  have target : (rightNeighbor e, (1:Fin 11))∈S := by
    rw [←atGate,←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have owner := actual_command_owner B base e advance (R 1) mem rfl
  change commandOwner (oldH6 B base) e 1 =
    commandOwner (oldH6 B base) (rightNeighbor e) 1 at owner
  have source : (e,(1:Fin 11))∈S := C.cover _ (by rfl) (owner.trans (C.entries _ target).2)
  have edge : Edge B base (e,1) (rightNeighbor e,1) :=
    ⟨e,advance,R 1,mem,rfl,rfl,rfl⟩
  obtain ⟨j,hj,P,Q⟩ := C.edge _ _ source edge
  have D : S.getD (j+1) fall=(rightNeighbor e,1) := (List.getElem_eq_getD _).symm.trans Q
  exact ⟨j,(List.getD_inj (by omega) (by omega) C.nodup).mp (D.trans atGate.symm),
    (List.getElem_eq_getD _).symm.trans P⟩

theorem incoming_frame {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (bit : Bool) (k : Nat)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (atGate : S.getD k fall=(rightNeighbor e,1))
    (G : gate (gateOpcode bit) 1 (longGeometry B (x (rightNeighbor e)))=true)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k))) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail := by
  obtain ⟨W,H,_⟩ := cur
  have same := W.1
  have fixed : ∀ i,oldH6 B x i=oldH6 B base i :=
    fun i => (congrArg Prod.fst (same i)).symm
  have O := ((selected_gate_iff hp hh fixed ready (rightNeighbor e) 1 bit).mp G).2
  have nb : oldH6 B base (rightNeighbor e)=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have P := (ordinal_zero (oldH6 B base) hh (rightNeighbor e)).mpr h
    change ordinal _ _ _ = gateOrdinal bit at O
    rw [P] at O
    cases bit <;> contradiction
  have body := (fixed (rightNeighbor e)).trans nb
  obtain ⟨j,E,A⟩ := chart_advance_incoming hp C same e body H.1 atGate
  have T := H.2.2 j (by omega)
  change atSite (x (S.getD j fall).1).long (S.getD j fall).2=.trail at T
  rw [A] at T
  exact ⟨body,by change bind _ _ (atSite (x e).long 1)=.trail; rw [T]; rfl⟩

#print axioms chart_advance_incoming
#print axioms incoming_frame
/-- One actual mark of a Current generated gate. The old payload is read at
the actual chart address. For the incoming side no extra trail or header
hypothesis is needed; these follow from the generated prefix. -/
theorem physical_mark_of_current {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (i e : Fin n) (sep : e≠rightNeighbor e) (bit : Bool) (k : Nat)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (atGate : S.getD k fall=(i,1))
    (G : gate (gateOpcode bit) 1 (longGeometry B (x i))=true)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (v : Payload)
    (read : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (op : v.opcode.toNat=gateOpcode bit)
    (fault : v.fault=0) (race : v.race=1 ∨ ∃ old, v.race=BStarBitParity.firstCode old) :
    let old := (kField 1).read (x i).long
    let obs := fun s => ((BStarLongCommand.observe ⟨s,1⟩ (longGeometry B (x i)) v).map
      (fun u => encode (.forward u))).getD old
    (kField 1).read (AllSizeS1Geometry.step B x e i).long =
      if i=e then obs .left else if i=rightNeighbor e then obs .right else old := by
  dsimp only
  let z := (x e,x (rightNeighbor e))
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
  have matchSite (s : Side) (E : BStarAcquireDoorHistory.siteOf e s=i) :
      geometry g s=longGeometry B (x i) ∧ readK raw ⟨s,1⟩=atSite (x i).long 1 := by
    cases s <;> subst i <;> exact ⟨rfl,rfl⟩
  have matchBound (s : Side) (E : BStarAcquireDoorHistory.siteOf e s=i) :
      bound g (readK raw) ⟨s,1⟩=.forward v := by
    obtain ⟨L,K⟩ := matchSite s E
    unfold bound
    rw [L,K,read]
  apply BStarGateUnmask.physical_gate_mark k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp x i e sep
  · intro s E
    refine ⟨v,matchBound s E,fault,?_,?_,race⟩
    · change gate v.opcode.toNat 1 (geometry g s)=true
      rw [(matchSite s E).1,op]; exact G
    · intro es
      subst s
      change rightNeighbor e=i at E
      subst i
      exact incoming_frame hp C e bit k ready atGate G cur
  · intro s E w hw
    have P := Token.forward.inj ((matchBound s E).symm.trans hw)
    subst w
    change _ = ((observe ⟨s,1⟩ (geometry g s) v).map
      (fun u => encode (.forward u))).getD ((kField 1).read (x i).long)
    rw [(matchSite s E).1]
    cases s
    · change e=i at E
      rw [if_pos E.symm]
    · change rightNeighbor e=i at E
      have N : i≠e := by rw [←E]; exact Ne.symm sep
      rw [if_neg N,if_pos E.symm]
  · rintro ⟨L,R⟩
    rw [if_neg L,if_neg R]

#print axioms physical_mark_of_current
end L4.BStarGateIncoming
