import Leader.L4.DirtyLeastForward
import Leader.L4.BStarClearanceForward

namespace L4.DirtyForwardAdvance
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongEvents BStarLongRouting BStarLongCommand BStarLongTransport
open BStarAcquireVisitOrder BStarH6WordChart BStarResetMarkAdapter
open BStarClearanceForward BStarClearanceCommandFrame DirtyLeastForward

/-- A selected forward advance pays at the old slot even if it
carries a fault: links leave a trail and terminals leave a reply. -/
theorem advance_removes_forward (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (q : Payload)
    (A : (C,.advance q)∈actualOffers g raw)
    (distinct : ∀ a,C.destination=some a→C.source≠a) :
    forwardCount (decode (readRaw (patchPair (longWork g raw) raw) C.source))=0 := by
  cases D : C.destination with
  | some a =>
    rw [(move_lands g raw C q a D A (distinct a D)).1,decode_encode]
    rfl
  | none =>
    rw [BStarResetQuiet.terminal_finish g raw C q D A,decode_encode]
    unfold finish
    dsimp only
    repeat (first | rfl | split)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- Exact physical mark lift of selected advance payment. -/
theorem ring_advance_removes_forward (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (C : CommandClaim) (q : Payload)
    (offered : (C,.advance q)∈actualOffers (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long))
    (nonDoor : C.kind≠.door) :
    ¬ringF (AllSizeS1Geometry.step B x e) (address e C.source) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have selected : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,offered,rfl⟩
  have safe (H : C.source.side=.right) (J : C.source.occurrence.val=0) :
      g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true := by
    cases D : C.destination with
    | some a => exact ((BStarAcquireReturn.link_shape g C a selected D).2.2 H J).elim
    | none =>
      have T := (BStarAcquireChainEndpoints.terminal g C selected D nonDoor).2.2.2
      omega
  have Dst (a : AtK) (D : C.destination=some a) : C.source≠a :=
    Ne.symm (BStarAcquireReturn.link_shape g C a selected D).1
  have Z := advance_removes_forward g raw C q offered Dst
  have E := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp
    (x e,x (rightNeighbor e)) C.source safe
  intro F
  have eq : readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) C.source =
      atSite ((AllSizeS1Geometry.step B x e) (address e C.source).1).long
        (address e C.source).2 := by
    rcases h : C.source with ⟨side,j⟩
    cases side <;> simp [readK,site,AllSizeS1Geometry.step,Ne.symm he] <;> rfl
  change forwardCount (atSite _ _)=1 at F
  change forwardCount (readK (patchPair (longWork g raw) raw) C.source)=0 at Z
  change readK _ _ = readK (patchPair (longWork g raw) raw) C.source at E
  rw [←E,eq,F] at Z
  contradiction

open BStarAcquireLiteralChain BStarResetChartTouch BStarAcquireAnchors
open BStarClearanceIndexedSum BStarClearanceIndexedWait

/-- If an actual advancing command touches the least forward, it
cannot be an incoming advance: that would have an earlier old forward.
Consequently the selected physical mark removes the least old slot. -/
theorem touching_advance_clears_least
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e) (a : AtK) (ha : (address e a)∈S)
    (least : ∀ v∈S,distance S (address e a)<distance S v → ¬ringF x v)
    (C : CommandClaim) (pay : Payload)
    (offered : (C,.advance pay)∈actualOffers (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long))
    (touch : a∈C.slots) :
    ¬ringF (AllSizeS1Geometry.step B x e) (address e a) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have selected : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,offered,rfl⟩
  have nonDoor : C.kind≠.door := by
    intro E
    have dg : BStarLongLiteral.gatedAt g raw C =
        .door (bound g (readK raw) C.source) := by
      unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
      simp [E,classify,BStarLongCommandData.checkOffer,bound,readK,BStarLongCommandData.oldTokens]
    have Z := BStarAcquireNonRouting.actual_door g raw (C,.advance pay) offered _ dg
    cases Z
  have which : a=C.source ∨ C.destination=some a := by
    cases D : C.destination <;> simpa [Claim.slots,D,eq_comm] using touch
  rcases which with eq|incoming
  · subst a
    exact ring_advance_removes_forward hp x e he C pay offered nonDoor
  · obtain ⟨part,own,adj⟩ := chart_owner_hypotheses hp chart same e
    have oq := (BStarClearanceChartFootprint.footprint_owner B x e C selected a touch).symm.trans (own a ha)
    have cs : address e C.source∈S := by
      exact part (List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨C,
        List.mem_filter.mpr ⟨selected,beq_iff_eq.mpr oq⟩,rfl⟩,
        List.mem_map.mpr ⟨C.source,by simp [Claim.slots],rfl⟩⟩)
    have D := (adj C selected (own _ cs)).1 _ incoming
    obtain ⟨u,U⟩ := BStarClearanceCommandFrame.advance_origin g raw C pay offered
    have F : IsForward g C.source (readRaw raw C.source) := ⟨u,U⟩
    have ring : ringF x (address e C.source) := by
      rw [isForward_iff] at F
      rcases h : C.source with ⟨s,j⟩
      rw [h] at F
      cases s <;> exact F
    exact (least _ cs (by omega) ring).elim

end L4.DirtyForwardAdvance
