import Leader.L4.BStarPaceChronology
import Leader.L4.BStarAcquireIncidence
import Leader.L4.BStarSeparatorRing

namespace L4.BStarPacePhysicalCharge
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetMarkAdapter BStarResetSchedule
open BStarSeparatingRail BStarSeparatorRing BStarSeparatorParked BStarGeneratedOwner
open BStarResetChartTouch BStarSeparatorControl
open BStarAcquireRailUniqueness BStarLongTransport

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

private theorem out_event {x : X} {addr : Nat→Pos n} {len k : Nat} {e : Fin n}
    {z : Cursor} (E : Event hp addr len x e (.busy 3 (.out k)) (.busy 3 z)) :
    Advance len (.out k) z ∧ Good anyTag len (project addr (step x e)) z := by
  cases E with
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ a g R =>
      cases R
      exact ⟨a,g⟩

/-- A strict outgoing advance of a genuine PACE cursor is on its
literal selected chart link. An arbitrary abstract Mark in the
Event witness is not taken as evidence for that physical link. -/
theorem advance_on_link {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e) (k : Nat)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy 3 (.out k)))
    (ev : Event hp (fun j=>S.getD j fall) len x e (.busy 3 (.out k)) (.busy 3 (.out (k+1)))) :
    linkAt hp x e (fun j=>S.getD j fall) len k ∧
      project (fun j=>S.getD j fall) (step x e) k=.trail := by
  let addr := fun j=>S.getD j fall
  let U := project addr x
  let V := project addr (step x e)
  have G := (out_event hp ev).2
  have trail : V k=.trail := G.2.2 k (by omega)
  have less : k<len := by have := G.1; omega
  let mark := mark_at hp C e he 3 cur.1 (.out k) (by intro E; cases E) cur.2.1
  change V k=.trail at trail
  refine ⟨?_,trail⟩
  by_cases outgoing : linkAt hp x e addr len k
  · exact outgoing
  have survives : anyTag.F (V k) := by
    by_cases incoming : ∃ j, j+1=k ∧ linkAt hp x e addr len j
    · obtain ⟨j,J,L⟩ := incoming
      have T : U j=.trail := cur.2.1.2.2 j (by omega)
      have F : anyTag.F (U (j+1)) := J ▸ cur.2.1.2.1
      exact J ▸ (mark.tf j L T F).2
    · exact (mark.idle k (Nat.le_of_lt less) outgoing (fun j J R=>incoming ⟨j,J,R⟩)
        (fun E _=>Nat.ne_of_lt less E)).2.2.1 cur.2.1.2.1
  exact False.elim (forward_not_trail (trail ▸ survives))

private theorem different_side_impossible (x : X) (e f : Fin n)
    (E : e=rightNeighbor f) (C K : CommandClaim) (k : Fin 11)
    (hC : C∈orderedCommands (oldPair B x e)) (hK : K∈orderedCommands (oldPair B x f))
    (sC : C.source=L k) (sK : K.source=R k)
    (c : C.kind≠.door) (d : K.kind≠.door) : False := by
  subst e
  exact one_departure_port _ _ _ K C k hK hC sK sC d c

private theorem slot_left (s : At (Fin 11)) (H : s.side=.left) : s=L s.occurrence := by
  rcases s with ⟨side,k⟩
  cases H
  rfl

private theorem slot_right (s : At (Fin 11)) (H : s.side=.right) : s=R s.occurrence := by
  rcases s with ⟨side,k⟩
  cases H
  rfl

/-- A fixed root rail link can be charged on only one raw label,
even across distinct old snapshots having the same fixed layout.
This allows a predictable nomination before the raw mark is read. -/
theorem link_label_unique {x y : X} (layout : ∀ i,Layout B x i=Layout B y i)
    (addr : Nat→Pos n) (len k : Nat) (e f : Fin n)
    (U : linkAt hp x e addr len k) (V : linkAt hp y f addr len k) : e=f := by
  obtain ⟨_,C,c,hC,hc,src,_⟩ := U
  obtain ⟨_,D,d,hD,hd,dst,_⟩ := V
  have hD' : D∈orderedCommands (oldPair B x f) :=
    (command_eq B x y layout f).symm ▸ hD
  have kC : C.kind≠.door := by rw [(BStarAcquireReturn.link_shape _ C c hC hc).2.1]; decide
  have kD : D.kind≠.door := by rw [(BStarAcquireReturn.link_shape _ D d hD hd).2.1]; decide
  have E := src.symm.trans dst
  have edge := congrArg Prod.fst E
  have occurrence : C.source.occurrence=D.source.occurrence := congrArg Prod.snd E
  cases sideC : C.source.side <;> cases sideD : D.source.side
  · simpa [address,site,sideC,sideD] using edge
  · exact False.elim (different_side_impossible hp x e f (by simpa [address,site,sideC,sideD] using edge)
      C D _ hC hD' (slot_left _ sideC) ((slot_right _ sideD).trans (congrArg R occurrence.symm)) kC kD)
  · exact False.elim (different_side_impossible hp x f e (by simpa [address,site,sideC,sideD] using edge.symm)
      D C _ hD' hC (slot_left _ sideD) ((slot_right _ sideC).trans (congrArg R occurrence)) kD kC)
  · exact FreshSeparation.succ_inj (by simpa [address,site,sideC,sideD] using edge)

#print axioms advance_on_link
#print axioms link_label_unique
end L4.BStarPacePhysicalCharge

