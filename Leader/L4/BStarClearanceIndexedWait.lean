import Leader.L4.BStarClearanceIndexedSum

namespace L4.BStarClearanceIndexedWait
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6WordChart BStarLongFiberOwner
open BStarResetChartTouch BStarClearanceIndexedSum BStarClearanceCommandSum
open BStarLongFixedRouting BStarClearanceOffset BStarResetMarkAdapter
open BStarLongTransport BStarLongRouting BStarLongCommand BStarLongDoor
open BStarLongEvents BStarResetQuietTable

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

private theorem door_safe_wait (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (hv : LongDoorGuard.valid manifest raw.2=true)
    (hw : (ctrlPhase.read raw.2).toNat=2)
    (hf : bound g (readK raw) (R 0)=.trail ∨
      ∃ pay, bound g (readK raw) (R 0)=.forward pay) : DoorSafe g raw (R 0) := by
  refine ⟨fun _ _ => hv,?_⟩
  intro _ c t ht _
  obtain ⟨rfl,rfl⟩ := BStarK0Frame.door_eq g raw c t ht
  change oldDoor raw.2 (bound g (readK raw) (R 0))=.hold
  rcases hf with T|⟨q,F⟩
  · rw [T]
    exact wait_holds_trail raw.2 hv hw
  · rw [F]
    exact wait_holds_forward raw.2 q hv hw

private theorem only_door_touch (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (H : g.2.axes.h6=true) :
    BStarResetQuiet.avoids (R 0) (BStarResetQuiet.middle g raw) := by
  apply BStarResetQuiet.middle_avoids_of_chart
  intro o ho hslot
  have hc : o.1∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨o,ho,rfl⟩
  have hd : BStarCommitIssue.doorClaim∈orderedCommands g := by
    have D := BStarDoorUnique.claim_door_singleton g H
    exact (List.mem_filter.mp (D.symm ▸ (List.mem_singleton_self _))).1
  have oc := BStarAcquireIncidence.same_claim g o.1 BStarCommitIssue.doorClaim (R 0)
    hc hd hslot (by decide)
  have eg : BStarLongLiteral.gatedAt g raw o.1=.door (bound g (readK raw) (R 0)) := by
    rw [oc]
    rfl
  have od := BStarAcquireNonRouting.actual_door g raw o ho _ eg
  obtain ⟨c,f⟩ := o
  dsimp only at od
  subst f
  intro w hw
  unfold selected at hw
  dsimp only at hw
  split at hw <;> simp at hw

private theorem door_safe_off_header (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (H : g.2.axes.h6=false) : DoorSafe g raw (R 0) := by
  refine ⟨fun _ E => by rw [H] at E; contradiction,?_⟩
  intro _ C k hc _
  have hC : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,hc,rfl⟩
  have E := (BStarK0Frame.door_eq g raw C k hc).1
  have Q := (BStarResetChartIndex.selected_door g C hC (E ▸ rfl)).2.1
  rw [H] at Q
  contradiction

/-- A marked live WAIT is before source service iff the owned right
door, if selected, has a trail or forward old bound token. A
selected reply is the stop mark; empty would be a repair stop and
is not silently treated as WAIT retention. Exterior marks impose
no unrelated source-controller premise. -/
def BeforeOwnService (x : X) (root : Fin n) (e : Fin n) : Prop :=
  rightNeighbor e=root →
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    LongDoorGuard.valid manifest raw.2=true ∧
    (ctrlPhase.read raw.2).toNat=2 ∧
    (bound g (readK raw) (R 0)=.trail ∨ ∃ q, bound g (readK raw) (R 0)=.forward q)

/-- At a pre-service WAIT mark the actual source door supplies both
the safe framing hook and the no-ISSUE rank law. -/
theorem pre_service_hypotheses {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let y := AllSizeS1Geometry.step B x e
    let adr := address e
    let rank := physicalRank B x
    let dist := distance S
    (∀ a, adr a∈S → DoorSafe g raw a) ∧
    (∀ C∈orderedCommands g, physicalOwner (oldH6 B x) e cmdDispl C.source=o.val →
      C.kind=.door → rank y dist (adr C.source)≤rank x dist (adr C.source)) := by
  dsimp only
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let y := AllSizeS1Geometry.step B x e
  let old := oldH6 B base
  let root := endpoint old hh o 0
  have Base (H : g.2.axes.h6=true) : old (rightNeighbor e)=true :=
    (congrArg Prod.fst (same (rightNeighbor e))).trans H
  have atRoot (H : g.2.axes.h6=true)
      (O : physicalOwner old e cmdDispl (R 0)=o.val) : rightNeighbor e=root.1 :=
    congrArg Prod.fst ((endpoint_spec old hh o 0).2.2 _ (Base H) O)
  have safe (a : AtK) (ha : address e a∈S) : DoorSafe g raw a := by
    by_cases Z : a=R 0
    · subst a
      cases H : g.2.axes.h6
      · exact door_safe_off_header g raw H
      · have own : physicalOwner old e cmdDispl (R 0)=o.val := (chart.entries _ ha).2
        obtain ⟨v,w,f⟩ := wait (atRoot H own)
        exact door_safe_wait g raw v w f
    · exact safe_nonright g raw a Z
  refine ⟨safe,?_⟩
  intro C hc owner H
  obtain ⟨E,T,_⟩ := BStarResetChartIndex.selected_door g C hc H
  have G : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  rw [G,E] at owner
  rw [E]
  obtain ⟨v,w,f⟩ := wait (atRoot T owner)
  let s := R (0 : Fin 11)
  have K := BStarClearanceNonforward.joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) s (distance S (address e s)) (only_door_touch g raw T)
    (door_safe_wait g raw v w f)
  change physicalRank B x y (distance S) (address e s) ≤ physicalRank B x x (distance S) (address e s)
  change BStarClearanceForward.ranked g s (distance S (address e s))
    (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s) ≤
    BStarClearanceForward.ranked g s (distance S (address e s)) (readRaw raw s) at K
  have F : y (rightNeighbor e)=(largePair B (x e,x (rightNeighbor e))).2 := by
    simp only [y,AllSizeS1Geometry.step,if_neg (Ne.symm he),if_true]
  let u := rightNeighbor e
  let geom := longGeometry B (x u)
  let q := distance S (u,0)
  change BStarClearanceForward.ranked (geom,geom) (L 0) q
    (readRaw ((y u).long,(y u).long) (L 0)) ≤
    BStarClearanceForward.ranked (geom,geom) (L 0) q
      (readRaw ((x u).long,(x u).long) (L 0))
  rw [show y u=(largePair B (x e,x u)).2 from F]
  exact K

theorem pre_service_sum {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let y := AllSizeS1Geometry.step B x e
    let rank := physicalRank B base
    let dist := distance S
    BStarClearanceAggregate.total (rank y dist) S≤BStarClearanceAggregate.total (rank x dist) S ∧
    ((∃ C q, (C,.advance q)∈actualOffers g raw ∧
          physicalOwner (oldH6 B base) e cmdDispl C.source=o.val) →
      BStarClearanceAggregate.total (rank y dist) S<BStarClearanceAggregate.total (rank x dist) S) := by
  dsimp only
  let post := AllSizeS1Geometry.step B x e
  have eq : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  obtain ⟨safe,door⟩ := pre_service_hypotheses hp chart same e he wait
  apply indexed_sum hp chart same cb cx e he safe
  intro C hc own hd
  rw [rank_fixed hp _ hh base x post (fun _ => rfl) (congrFun eq) cb cx,
      rank_fixed hp _ hh base x x (fun _ => rfl) (congrFun eq) cb cx]
  exact door C hc (by rwa [eq]) hd

#print axioms pre_service_sum
end L4.BStarClearanceIndexedWait
