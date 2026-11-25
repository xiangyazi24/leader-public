import Leader.L4.BStarCopyLoadCarry
import Leader.L4.BStarClearanceMobileRing
import Leader.L4.BStarGeneratedOwner

namespace L4.BStarCopyOwnedFrozen
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongCommand BStarLongLiteral
open BStarLongTransport BStarLongEvents BStarCopyOperand BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarLongFiberOwner BStarClearanceDataChart
open BStarResetChartTouch BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerControlHistory BStarSeparatorControl
open BStarAcquireLiteralChain BStarResetMarkAdapter BStarResetQuiet BStarClearanceCommandFrame

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

private theorem in_offers {α : Type} (key : α → Nat) (a : α) (ls : List α) :
    a∈offers key ls → a∈ls := by
  induction ls with
  | nil => simp [offers]
  | cons b ls ih =>
    change a∈insert key b (offers key ls) → _
    intro h
    exact (List.mem_cons.mpr ((mem_insert key b a _).mp h |>.imp_right ih))

theorem candidate_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (M : a∈(round g raw).prep) :
    ∃ C f q, (C,.advance f)∈gated g raw ∧
      (C,.advance q)∈actualOffers g raw ∧
      prepOf f.opcode.toNat=some a.claim.op ∧ f.fault=0 ∧
      a∈fieldOffers g raw C.source f ∧
      a.claim.origin=C.source ∧ a.claim.lane.side=C.source.side ∧
      a.claim.lane.occurrence∈prepSites (geometry g C.source.side) C.source.occurrence a.claim.op := by
  change a∈preparedBy g raw (gated g raw) at M
  obtain ⟨⟨C,f⟩,mem,hit⟩ := List.mem_flatMap.mp M
  cases f <;> try (simp at hit)
  rename_i f
  change a∈fieldOffers g raw C.source f at hit
  have fmem := hit
  have eq : f.fault=0 := by
    -- Gate checks the pre-transport fault bit.
    by_cases E : f.fault=0
    · exact E
    · simp [fieldOffers] at hit
      exact hit.1
  simp only [fieldOffers,eq,bne_self_eq_false] at hit
  cases O : prepOf f.opcode.toNat with
  | none => simp [O] at hit
  | some op =>
    rw [O] at hit
    obtain ⟨cl,_,rfl⟩ := List.mem_map.mp hit
    rename_i hcl
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hcl
    obtain ⟨q,Q⟩ := BStarClearancePrepOwner.gated_still_departs g raw C f mem
    exact ⟨C,f,q,mem,Q,O,eq,fmem,rfl,rfl,hs⟩

theorem winner_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (win : a∈(arbitration (round g raw).prep).1) :
    ∃ C f q, (C,.advance f)∈gated g raw ∧
      (C,.advance q)∈actualOffers g raw ∧
      prepOf f.opcode.toNat=some a.claim.op ∧ f.fault=0 ∧
      a.claim.origin=C.source ∧ a.claim.lane.side=C.source.side ∧
      a.claim.lane.occurrence∈prepSites (geometry g C.source.side) C.source.occurrence a.claim.op := by
  have W := win
  unfold arbitration at W
  rw [arbitrate_winners] at W
  have M := in_offers offerPriority a _ ((select_sublist ..).subset W)
  change a∈preparedBy g raw (gated g raw) at M
  obtain ⟨⟨C,f⟩,mem,hit⟩ := List.mem_flatMap.mp M
  cases f <;> try (simp at hit)
  rename_i f
  change a∈fieldOffers g raw C.source f at hit
  have eq : f.fault=0 := by
    -- Gate checks the pre-transport fault bit.
    by_cases E : f.fault=0
    · exact E
    · simp [fieldOffers] at hit
      exact hit.1
  simp only [fieldOffers,eq,bne_self_eq_false] at hit
  cases O : prepOf f.opcode.toNat with
  | none => simp [O] at hit
  | some op =>
    rw [O] at hit
    obtain ⟨cl,_,rfl⟩ := List.mem_map.mp hit
    rename_i hcl
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hcl
    obtain ⟨q,Q⟩ := BStarClearancePrepOwner.gated_still_departs g raw C f mem
    exact ⟨C,f,q,mem,Q,O,eq,rfl,rfl,hs⟩

/-- Real prep winners at a physical lane can only belong to that lane's
intrinsic owner, and this refers to the actual selected departure. -/
theorem winner_owner (x : X) (e : Fin n) (a : BStarLongPrep.Offer)
    (win : a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    ∃ C f q, (C,.advance f)∈gated g raw ∧ (C,.advance q)∈actualOffers g raw ∧
      prepOf f.opcode.toNat=some a.claim.op ∧ f.fault=0 ∧ a.claim.origin=C.source ∧
      commandOwner (oldH6 B x) (site e C.source.side) C.source.occurrence =
      dataOwner (oldH6 B x) (site e a.claim.lane.side) a.claim.lane.occurrence := by
  dsimp only
  obtain ⟨C,f,q,H,Q,op,clean,origin,side,lanes⟩ := winner_origin _ _ a win
  refine ⟨C,f,q,H,Q,op,clean,origin,?_⟩
  change physicalOwner (oldH6 B x) e cmdDispl C.source =
    physicalOwner (oldH6 B x) e dataDispl a.claim.lane
  rw [physical_pair_owner,physical_pair_owner]
  have E : (⟨C.source.side,a.claim.lane.occurrence⟩ : At Sheet)=a.claim.lane := by
    generalize Y : a.claim.lane=w at side ⊢
    obtain ⟨s,t⟩ := w
    exact congrArg (fun z => At.mk z t) side.symm
  rw [←E]
  exact prep_owner _ _ _ _ _ _ lanes

/-- A criterion in terms of literal, selected old departures, not raw
opcode bytes at unrelated sites. Foreign owners cannot invalidate the
frozen packet. Owner ENABLE and STOP remain allowed. -/
theorem safe_of_owner_preps (x : X) (e i : Fin n) (sh : Sheet)
    (ok : ∀ C f q, (C,.advance f)∈gated (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) →
      (C,.advance q)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) →
      commandOwner (oldH6 B x) (site e C.source.side) C.source.occurrence=
        dataOwner (oldH6 B x) i sh →
      ∀ op, prepOf f.opcode.toNat=some op → op=.stop ∨ op=.rstop ∨ op=.enable) :
    FrozenSafe hp x e i sh := by
  intro s eq a win lane
  obtain ⟨C,f,q,H,Q,O,_,_,own⟩ := winner_owner hp x e a win
  rw [lane] at own
  exact ok C f q H Q (own.trans (by simpa only using congrArg (fun z => dataOwner (oldH6 B x) z sh) eq))
    a.claim.op O

open BStarAcquireRailCoverage BStarResetChartIndex BStarResetRailRing

private theorem own_slot {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (C : CommandClaim)
    (sel : C∈orderedCommands (oldPair B x e))
    (own : commandOwner (oldH6 B base) (site e C.source.side) C.source.occurrence=o.val) :
    (site e C.source.side,C.source.occurrence)∈S := by
  let u : Pos n := (site e C.source.side,C.source.occurrence)
  have L := chart.length
  rcases selected_endpoint_or_link B base x hh same o e C sel own with ⟨_,_,R⟩|⟨_,_,R⟩|⟨d,dst,_⟩
  · change (site e C.source.side,C.source.occurrence)∈S
    rw [R,←chart.root,←List.getElem_eq_getD (h:=show 0<S.length by omega)]
    exact List.getElem_mem _
  · change (site e C.source.side,C.source.occurrence)∈S
    rw [R,←chart.terminal,←List.getElem_eq_getD (h:=show len<S.length by omega)]
    exact List.getElem_mem _
  · have baseSel := command_eq B x base (fun i => (same i).symm) e ▸ sel
    have act := (BStarAcquireChainEndpoints.link_endpoints _ C d baseSel dst).1
    apply chart.cover _ _ own
    cases hs : C.source.side <;> simpa [u,site,hs,geometry,oldPair] using act

/-- A selected old forward departure of the owner is from the unique
pointed outward occurrence. It cannot occur while the owner returns. -/
theorem actual_owner_departure {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (C : CommandClaim) (p : Payload) (z : Cursor)
    (sel : (C,.advance p)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (own : commandOwner (oldH6 B base) (site e C.source.side) C.source.occurrence=o.val)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) z)
    (out : OutClean len (project (fun j => S.getD j fall) x) z) :
    ∃ k, z=.out k ∧ S.getD k fall=(site e C.source.side,C.source.occurrence) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  obtain ⟨k,hk,idx⟩ := List.getElem_of_mem (own_slot hp chart same e C mem own)
  have L := chart.length
  have idx : S.getD k fall=address e C.source := (List.getElem_eq_getD _).symm.trans idx
  obtain ⟨q,advance⟩ := advance_origin g raw C p sel
  have old : readK raw C.source=project (fun j => S.getD j fall) x k :=
    (old_read x e _).trans ((congrArg (atCursor x) idx).symm)
  have FF : anyTag.F (project (fun j => S.getD j fall) x k) := by
    generalize E : project (fun j => S.getD j fall) x k=t
    rw [E] at old
    cases t
    case forward p => exact ⟨p,rfl⟩
    all_goals simp [bound,old,BStarLongCommand.bind] at advance
    all_goals try (repeat' first | contradiction | split at advance)
  cases z with
  | back i =>
      exact (pointed_backward_no_forward _ _ _ G k (by omega) FF).elim
  | out i =>
      have K := (pointed_unique_forward _ _ _ G out k (by omega)).mp FF
      subst k
      exact ⟨i,rfl,idx⟩

theorem safe_returning {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e i : Fin n) (sh : Sheet) (j : Nat)
    (own : dataOwner (oldH6 B base) i sh=o.val)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.back j)) :
    FrozenSafe hp x e i sh := by
  apply safe_of_owner_preps hp x e i sh
  intro C f q gated sel H op opEq
  have eq : oldH6 B x=oldH6 B base := funext (fun a => (congrArg Prod.fst (same a)).symm)
  rw [eq,own] at H
  obtain ⟨_,bad,_⟩ := actual_owner_departure hp chart same e C q (.back j) sel H G trivial
  cases bad

theorem safe_idle {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e i : Fin n) (sh : Sheet)
    (own : dataOwner (oldH6 B base) i sh=o.val)
    (clean : ∀ j≤len, project (fun k => S.getD k fall) x j=.empty) :
    FrozenSafe hp x e i sh := by
  apply safe_of_owner_preps hp x e i sh
  intro C f q gated sel H op opEq
  have eq : oldH6 B x=oldH6 B base := funext (fun a => (congrArg Prod.fst (same a)).symm)
  rw [eq,own] at H
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have mem : C∈orderedCommands g := ((gated_mem g raw C _).mp gated).1
  obtain ⟨k,hk,idx⟩ := List.getElem_of_mem (own_slot hp chart same e C mem H)
  have L := chart.length
  have idx : S.getD k fall=address e C.source := (List.getElem_eq_getD _).symm.trans idx
  have old : readK raw C.source=.empty :=
    (old_read x e _).trans (((congrArg (atCursor x) idx).symm).trans (clean k (by omega)))
  obtain ⟨a,E⟩ := advance_origin g raw C q sel
  have no : bound g (readK raw) C.source=.empty := quiet_bound g _ _ (.inl old) |>.trans old
  rw [no] at E
  cases E

/-- On an outward tour, only the current owner's one pointed forward
origin can invalidate the monitored lane. If that old origin has no
mutating candidate on the lane, all foreign prep and data are harmless. -/
theorem safe_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e i : Fin n) (sh : Sheet) (j : Nat)
    (own : dataOwner (oldH6 B base) i sh=o.val)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out j))
    (out : OutClean len (project (fun j => S.getD j fall) x) (.out j))
    (safeFront : ∀ s : Side, site e s=i → ∀ a∈
        (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
        a.claim.lane=⟨s,sh⟩ →
        address e a.claim.origin=S.getD j fall →
        a.claim.op=.stop ∨ a.claim.op=.rstop ∨ a.claim.op=.enable) :
    FrozenSafe hp x e i sh := by
  intro s hs a win lane
  obtain ⟨C,f,q,_,sel,_,_,src,H⟩ := winner_owner hp x e a win
  have eq : oldH6 B x=oldH6 B base := funext (fun a => (congrArg Prod.fst (same a)).symm)
  rw [eq,lane,hs,own] at H
  obtain ⟨k,E,idx⟩ := actual_owner_departure hp chart same e C q (.out j) sel H G out
  have J := Cursor.out.inj E
  subst k
  exact safeFront s hs a win lane (src ▸ idx.symm)

local notation "play" => BStarResetSchedule.run step

/-- The same-owner exceptional hook needs evidence only at an outward
old cursor and only for its own prep at the monitored physical lane. -/
def OutwardSafe (x : X) (e i : Fin n) (sh : Sheet) (cursor : Pos n) : Prop :=
  ∀ s : Side, site e s=i →
    ∀ a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      a.claim.lane=⟨s,sh⟩ → address e a.claim.origin=cursor →
      a.claim.op=.stop ∨ a.claim.op=.rstop ∨ a.claim.op=.enable

/-- Following the exact GeneratedOwner word, only outward states need
a local check: idle and returning states preserve frozen unconditionally.
The hypothesis permits all simultaneous prep/data of other owners. -/
theorem generated_frozen_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {start fin : Mode} {w : List (Fin n)}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x start w fin)
    (i : Fin n) (sh : Sheet) (own : dataOwner (oldH6 B base) i sh=o.val)
    (layout : ∀ pre tail, w=pre++tail →
      ∀ r, BStarLongFixedRouting.Layout B base r=BStarLongFixedRouting.Layout B (play x pre) r)
    (out : ∀ pre e post, w=pre++e::post →
      ∀ op k, Current hp base (fun j => S.getD j fall) len (play x pre) (.busy op (.out k)) →
        OutwardSafe hp (play x pre) e i sh (S.getD k fall)) :
    (readLane (Sheet.index sh) (play x w i).long).frozen=
      (readLane (Sheet.index sh) (x i).long).frozen := by
  induction hist with
  | endpoint _ => rfl
  | @next old start e w mid fin I event next ih =>
    have L := layout [] (e::w) rfl
    have F : FrozenSafe hp old e i sh := by
      cases start with
      | idle => exact safe_idle hp chart L e i sh own I.2
      | busy op cursor =>
        cases cursor with
        | back j => exact safe_returning hp chart L e i sh j own I.2.1
        | out j =>
          exact safe_outward hp chart L e i sh j own I.2.1 I.2.2
            (out [] e w rfl op j I)
    exact (ih
      (fun pre tail E => layout (e::pre) tail (congrArg (List.cons e) E))
      (fun pre a post E => out (e::pre) a post (congrArg (List.cons e) E))).trans
      (ring_frozen_frame hp old e i sh (sep e) F)

/-- In an actually pointed LOAD state, even losing foreign candidates
cannot contend with the lane of that very old command. This derives
the exclusivity premise for the actual selected freeze. -/
theorem pointed_load_exclusive {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (sep : e≠rightNeighbor e) (C : CommandClaim) (u : Nat)
    (s : Side) (rev : Bool) (j : Nat)
    (laneOwner : dataOwner (oldH6 B base) (site e s) (loadLane s rev).occurrence=o.val)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out j))
    (out : OutClean len (project (fun j => S.getD j fall) x) (.out j))
    (ptr : address e C.source=S.getD j fall)
    (source : C.source=⟨s,loadOcc rev⟩)
    (select : (C,.advance (BStarCopyLoadCarry.payload u))∈
        gated (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    ∀ a∈(round (oldPair B x e) raw).prep, a.claim.lane=loadLane s rev →
      a.claim=loadClaim s rev ∧ a.payload=loadPayload raw (loadLane s rev) (BStarCopyLoadCarry.payload u) := by
  dsimp only
  intro a ma lane
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨D,f,q,gate,move,op,fault,fmem,orig,side,lanes⟩ := candidate_origin g raw a ma
  have E : (⟨D.source.side,a.claim.lane.occurrence⟩ : At Sheet)=a.claim.lane := by
    generalize Q : a.claim.lane=v at side ⊢
    obtain ⟨a,b⟩ := v
    exact congrArg (fun k => At.mk k b) side.symm
  have oEq : physicalOwner (oldH6 B x) e cmdDispl D.source =
      physicalOwner (oldH6 B x) e dataDispl a.claim.lane := by
    rw [physical_pair_owner,physical_pair_owner,←E]
    exact prep_owner g _ _ _ _ _ lanes
  have L : oldH6 B x=oldH6 B base := funext fun i => (congrArg Prod.fst (same i)).symm
  rw [L,lane] at oEq
  have ownD : commandOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o.val :=
    oEq.trans laneOwner
  obtain ⟨k,J,atD⟩ := actual_owner_departure hp chart same e D q (.out j) move ownD G out
  have kj := Cursor.out.inj J
  subst k
  have eqSource : C.source=D.source := address_inj e sep (ptr.trans atD)
  have cmem := ((gated_mem g raw C _).mp select).1
  have dmem := ((gated_mem g raw D _).mp gate).1
  have club := BStarAcquireIncidence.same_claim g C D C.source cmem dmem
    (by simp [Claim.slots]) (by simp [Claim.slots,eqSource])
  subst D
  have F := Offer.advance.inj (((gated_mem g raw C _).mp gate).2.trans
    ((gated_mem g raw C _).mp select).2.symm)
  subst f
  have O : a.claim.op=.load := (Option.some.inj op).symm
  constructor
  · have J : a.claim=⟨a.claim.op,a.claim.origin,a.claim.lane⟩ := by cases a.claim; rfl
    exact J.trans (by rw [O,orig,source,lane]; rfl)
  · simp only [fieldOffers,BStarCopyLoadCarry.payload,bne_self_eq_false,prepOf] at fmem
    obtain ⟨cl,_,M⟩ := List.mem_map.mp fmem
    have S := congrArg BStarLongPrep.Offer.claim M
    have V := congrArg BStarLongPrep.Offer.payload M
    change cl=a.claim at S
    change loadPayload raw cl.lane (BStarCopyLoadCarry.payload u)=a.payload at V
    rw [S,lane] at V
    exact V.symm

open BStarCopyLoadCarry BStarClearanceSource BStarLongDoor

/-- An authenticated LOAD cursor in its owner's pointed rail freezes
the launched capture-index bank without a separate exclusivity premise.
A matching actual selected old command, not a scheduled logical phase
alone, names the freezing mark. -/
theorem pointed_freeze_from_launch {base old launched : X}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (L : Launch (old (S.getD 0 fall).1).long (launched (S.getD 0 fall).1).long)
    (op8 : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=8)
    (w : List (Fin n)) (e : Fin n) (s : Side) (rev : Bool) (C : CommandClaim)
    (sep : e≠rightNeighbor e) (j : Nat)
    (trail : LoadWord hp launched ((S.getD 0 fall).1,0) w (address e C.source)) :
    let root := (S.getD 0 fall).1
    let u := (captures.read (old root).long).toNat
    let x := play launched w
    let g := oldPair B x e
    let i := site e s
    Current hp base (fun j => S.getD j fall) len x (.busy 8 (.out j)) →
    address e C.source=S.getD j fall →
    dataOwner (oldH6 B base) i (loadLane s rev).occurrence=o.val →
    C∈orderedCommands g → C.kind≠.door →
    C.source=⟨s,loadOcc rev⟩ → (geometry g s).inside=true →
    ∃ k : Fin 3,
      k.val=(if rev then u%4 else u/16%4) ∧
      (readLane (Sheet.index (loadLane s rev).occurrence) (step x e i).long).frozen=
        oldBankPacket (x i).long k := by
  dsimp only
  intro cur ptr own sel door origin inside
  let root := (S.getD 0 fall).1
  let u := (captures.read (old root).long).toNat
  let x := play launched w
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨valid,pay⟩ := carries_from_launch hp root old launched L op8 trail
  have read : readK raw C.source=.forward (payload u) := (old_read x e _).trans pay
  have H : gatedAt g raw C=.advance (payload u) := by
    unfold gatedAt classifyOld
    change checkOffer g (view raw) (C,classify C (geometry g C.source.side)
      (BStarLongCommand.bind (geometry g C.source.side) C.source.occurrence (readK raw C.source)) _) = _
    rw [read,load_bind _ _ _ (captures.read (old root).long).isLt valid]
    simp [classify,door,depart,gate,admit,bitOp,checkOffer,checkFence,payload]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  have selected := (gated_mem g raw C _).mpr ⟨sel,H.symm⟩
  have ex := pointed_load_exclusive hp chart cur.1.1 e sep C u s rev j own cur.2.1
    cur.2.2 ptr origin selected
  exact selected_freeze_from_launch hp root old launched L op8 w e s rev C sep trail
    sel door origin inside ex

private theorem source_site_cases (g : LongGeometry) (j : Fin 11) (op : Prep)
    (sh : Sheet) (H : sh∈prepSites g j op) :
    (sh=.ls → j=0 ∨ j=5) ∧ (sh=.rs → j=2) := by
  have all (inside : Bool) (op : Prep) :
      ∀ j : Fin 11, (.ls∈prepSites ⟨⟨false,false,false,false,false,false⟩,inside,false,0,false⟩ j op →
        j=0 ∨ j=5) ∧
      (.rs∈prepSites ⟨⟨false,false,false,false,false,false⟩,inside,false,0,false⟩ j op → j=2) := by
    cases inside <;> cases op <;> decide +kernel
  have eq : prepSites g j op=
      prepSites ⟨⟨false,false,false,false,false,false⟩,g.inside,false,0,false⟩ j op := by
    cases op <;> rfl
  rw [eq] at H
  exact ⟨fun h => (all g.inside op j).1 (h ▸ H),fun h => (all g.inside op j).2 (h ▸ H)⟩

/-- On a source lane of a frozen COPY operand, only exactly the
physical K0/K5 (LS) or K2 (RS) cursor can even request a prep. -/
theorem outward_far_safe (x : X) (e i : Fin n) (sh : Sheet) (cursor : Pos n)
    (h : sh=.ls ∨ sh=.rs)
    (farL : sh=.ls → cursor≠(i,0) ∧ cursor≠(i,5))
    (farR : sh=.rs → cursor≠(i,2)) :
    OutwardSafe hp x e i sh cursor := by
  intro side atSide a win lane same
  obtain ⟨C,_,_,_,_,_,_,orig,sharing,sites⟩ := winner_origin _ _ a win
  have cases := source_site_cases _ _ _ _ sites
  have pos : cursor=(i,C.source.occurrence) := by
    rw [←same,orig]
    change (site e C.source.side,C.source.occurrence)=_
    have E : C.source.side=side := sharing.symm.trans (congrArg At.side lane)
    rw [E,atSide]
  have shEq : a.claim.lane.occurrence=sh := congrArg At.occurrence lane
  rcases h with l|r
  · have K := cases.1 (shEq.trans l)
    rcases K with z|f
    · exact ((farL l).1 (pos.trans (congrArg (Prod.mk i) z))).elim
    · exact ((farL l).2 (pos.trans (congrArg (Prod.mk i) f))).elim
  · exact ((farR r) (pos.trans (congrArg (Prod.mk i) (cases.2 (shEq.trans r))))).elim

/-- One actual generated continuation releases the same frozen digit at
its selected INJECT, with no competing-owner assumption. The remaining
outward guard is only for the single own cursor, and is automatic away
from the exact source incidences in outward_far_safe. -/
theorem generated_inject_frozen {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {start fin : Mode} {w : List (Fin n)}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x start w fin)
    (e : Fin n) (s : Side) (rev : Bool) (value : BitVec 36) :
    let i := site e s
    let sh := (loadLane s rev).occurrence
    let ln := Sheet.index sh
    let y := play x w
    dataOwner (oldH6 B base) i sh=o.val →
    (∀ pre tail, w=pre++tail →
      ∀ r, BStarLongFixedRouting.Layout B base r=BStarLongFixedRouting.Layout B (play x pre) r) →
    (∀ pre e post, w=pre++e::post →
      ∀ op k, Current hp base (fun j => S.getD j fall) len (play x pre) (.busy op (.out k)) →
        OutwardSafe hp (play x pre) e i sh (S.getD k fall)) →
    (readLane ln (x i).long).frozen=.data value →
    BStarCopyInjection.injection s rev∈
      (arbitration (round (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)).prep).1 →
    (readLane ln (y i).long).gate=true →
    (readLane ln (y i).long).mobile=.empty →
    let out := readLane ln (step y e i).long
    out.mobile=.data value ∧ out.frozen=.empty := by
  dsimp only
  intro own layout outScope old win enabled vacant
  have frame := generated_frozen_word hp chart sep hist (site e s) (loadLane s rev).occurrence own layout outScope
  have res := ring_inject hp (play x w) e (sep e) s rev value win enabled (frame.trans old) vacant
  exact ⟨congrArg Lane.mobile res,congrArg Lane.frozen res⟩

end L4.BStarCopyOwnedFrozen
