import Leader.L4.BStarAcquireMarkedSample
import Leader.L4.BStarAcquireMarkedPath
import Leader.L4.BStarAcquireDoorHistory

namespace L4.BStarAcquireForwardTrace
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongWork BStarAcquireLatch BStarAcquireMarkedSample BStarAcquireMarkedPath
open BStarH6WordChart BStarCommandChronology BStarAcquireVisitOrder

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}

def atCursor (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (u : Pos n) : Token := readK ((x u.1).long,(x u.1).long) (L u.2)

variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Ring B n

/-- A forward observation follows the exact ring marks from the chosen
issue. A traversed edge is an actual selected old-pair link. A silent
mark requires a frame at the tracked address, not just absence of an
ACQUIRE advance. No receipt matching is used in this relation. -/
inductive Trace (base : X) : X → Pos n → List (Fin n) → X → Pos n →
    List (Pos n) → List Visit → Prop where
  | done (x u) : Trace base x u [] x u [] []
  | idle {x y u z e w ps vs} :
      BStarAcquireMarkedPath.NoDeparture (b:=B) x e u →
      atCursor (marked B x e) u=atCursor x u →
      Trace base (marked B x e) u w y z ps vs →
      Trace base x u (e::w) y z ps vs
  | hop {x y z e w ps vs} (C : CommandClaim) (D : AtK) :
      e ≠ rightNeighbor e →
      (∀ i, BStarLongFixedRouting.Layout B x i=BStarLongFixedRouting.Layout B base i) →
      C ∈ orderedCommands (oldPair B x e) → C.destination=some D →
      Trace base (marked B x e) (site e D.side,D.occurrence) w y z ps vs →
      Trace base x (site e C.source.side,C.source.occurrence) (e::w) y z
        ((site e C.source.side,C.source.occurrence)::ps)
        ((event (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) C).toList ++ vs)

theorem idle_exterior {base x y : X} {u z : Pos n} {e : Fin n} {w ps vs}
    (hl : u.1≠e) (hr : u.1≠rightNeighbor e)
    (h : Trace hp base (marked B x e) u w y z ps vs) :
    Trace hp base x u (e::w) y z ps vs :=
  let off := off_pair (b:=B) (x:=x) hl hr
  .idle off.1 (by unfold atCursor; rw [off.2]) h

/-- The end configuration is independently the ordinary ring update
fold, and the end payload is the fold of the literal capture samples. -/
theorem sound {base x y : X} {u z : Pos n} {w ps vs}
    (h : Trace hp base x u w y z ps vs) (pay : Payload)
    (hold : atCursor x u=.forward pay) (healthy : BStarAcquireHop.Healthy pay) :
    let q := vs.foldl (fun q v => v.apply q) pay
    BStarAcquireMarkedPath.run B x w=y ∧ atCursor y z=.forward q ∧ BStarAcquireHop.Healthy q := by
  induction h generalizing pay with
  | done => exact ⟨rfl,hold,healthy⟩
  | idle _ frame _ ih => exact ih pay (frame.trans hold) healthy
  | @hop x y z e w ps vs C D he _ hc hd _ ih =>
    dsimp only
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    let q := BStarAcquireHop.argUpdate g raw (BStarLongCommandData.round g raw).offered C pay
    have src : readK raw C.source=.forward pay := by
      cases side : C.source.side <;>
        simpa [atCursor,readK,raw,site,side,L,BStarTrace.lane] using hold
    have post := (marked_hop hp x e he C D pay hc hd src healthy).2
    have H := BStarAcquireHealthy.actual_hop_healthy g raw (BStarLongCommandData.round g raw).offered C pay healthy
    have tail := ih q post H
    rw [List.foldl_append,event_apply]
    exact tail

theorem route {base x y : X} {u z : Pos n} {w ps vs}
    (h : Trace hp base x u w y z ps vs) : Path B base u ps z := by
  induction h with
  | done => exact .nil _
  | idle _ _ _ ih => exact ih
  | @hop x y z e w ps vs C D _ lay hc hd _ ih =>
    apply Path.cons _ ih
    exact ⟨e,C,D,BStarLongFixedRouting.command_eq B x base lay e ▸ hc,hd,rfl,rfl⟩

theorem sample_count {base x y : X} {u z : Pos n} {w ps vs}
    (h : Trace hp base x u w y z ps vs) (k : Nat) (hk : k<3) :
    (vs.filter (fun v => v.incidence.val==k)).length =
      (ps.filter (fun v => v.2.val==k && oldH6 B base v.1)).length := by
  induction h with
  | done => rfl
  | idle _ _ _ ih => exact ih
  | @hop x y z e w ps vs C D _ lay hc hd _ ih =>
    have E : (BStarLongCommand.geometry (oldPair B x e) C.source.side).axes.h6 =
        oldH6 B base (site e C.source.side) := by
      have P := congrArg Prod.fst (lay (site e C.source.side))
      cases H : C.source.side <;>
        simpa [BStarLongFixedRouting.Layout,oldH6,oldPair,site,H,BStarLongCommand.geometry,longGeometry] using P
    rw [List.filter_append,List.length_append,event_count _ _ _ k hk,ih,E]
    by_cases q : (C.source.occurrence.val==k && oldH6 B base (site e C.source.side))=true
    · simp [q]
      omega
    · have qf : (C.source.occurrence.val==k && oldH6 B base (site e C.source.side))=false :=
        Bool.eq_false_iff.mpr q
      simp [qf]

theorem capture_once {base x y : X} {u z : Pos n} {w ps vs}
    (h : Trace hp base x u w y z ps vs)
    (hu : u.2.val=0) (huH : oldH6 B base u.1=true) (hz : z.2.val=10) (k : Fin 3) :
    (vs.filter (fun v => v.incidence.val==k.val)).length=1 := by
  rw [sample_count hp h k.val k.isLt]
  exact departures_once (route hp h) hu huH hz k.val (by omega)

/-- An observed K0-to-terminal forward prefix with healthy initial
payload reaches an actual terminal mark. The literal terminal replies
with the folded bytes, and the success latch is exactly the
conjunction of the observed grants. -/
theorem completes_at {base x y : X} {u z : Pos n} {w ps vs}
    (h : Trace hp base x u w y z ps vs)
    (init : atCursor x u=.forward BStarAcquireSource.initPayload)
    (e : Fin n) (he : e≠rightNeighbor e) (C : CommandClaim)
    (hc : C∈orderedCommands (oldPair B y e)) (ht : C.kind=.terminal)
    (hd : C.destination=none) (hk : C.source.occurrence.val=10)
    (atC : z=(site e C.source.side,C.source.occurrence)) :
    let pay := vs.foldl (fun q v => v.apply q) BStarAcquireSource.initPayload
    ∃ receipt, atCursor (marked B y e) z=.reply receipt ∧
      BStarLongCommand.finish pay=.reply receipt ∧ BStarAcquireReturn.ValidReply receipt ∧
      latch pay=vs.all Visit.wins := by
  dsimp only
  obtain ⟨_,atZ,healthy⟩ := sound hp h _ init BStarAcquireHealthy.initialized_healthy
  subst z
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  let pay := vs.foldl (fun q v => v.apply q) BStarAcquireSource.initPayload
  have src : readK raw C.source=.forward pay := by
    cases side : C.source.side <;>
      simpa [atCursor,readK,raw,site,side,L,BStarTrace.lane] using atZ
  obtain ⟨a,ha,term,valid⟩ :=
    BStarAcquireReturn.raw_terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (y e,y (rightNeighbor e)) C pay hk hd ht healthy hc src
  refine ⟨a,?_,term,valid,?_⟩
  · cases side : C.source.side
    · simpa [atCursor,marked,readK,site,side,L,BStarTrace.lane,Pair.map] using ha
    · simpa [atCursor,marked,readK,site,side,L,BStarTrace.lane,Pair.map,Ne.symm he] using ha
  · rw [fold_latch]
    rfl

/-- A checked physical reverse route starting immediately after
this terminal supplies the old source receipt before the next source
mark. The route is a witness of custody, not a payload-equality test
on an unrelated pre-existing source reply. -/
theorem returned {base x y out : X} {u z dest : Pos n} {w ps vs rev}
    (h : Trace hp base x u w y z ps vs)
    (init : atCursor x u=.forward BStarAcquireSource.initPayload)
    (e : Fin n) (he : e≠rightNeighbor e) (C : CommandClaim)
    (hc : C∈orderedCommands (oldPair B y e)) (ht : C.kind=.terminal)
    (hd : C.destination=none) (hk : C.source.occurrence.val=10)
    (atC : z=(site e C.source.side,C.source.occurrence))
    (receipt : Payload)
    (fin : BStarLongCommand.finish
      (vs.foldl (fun q v => v.apply q) BStarAcquireSource.initPayload)=.reply receipt)
    (back : BStarAcquireDoorHistory.Trace (AllSizeS1Geometry.step B) (atCursor) 
      (BStarAcquireDoorHistory.chosenOn B) receipt (marked B y e) z rev out dest) :
    atCursor out dest=.reply receipt ∧ BStarAcquireReturn.ValidReply receipt := by
  obtain ⟨pay,old,term,valid,_⟩ := completes_at hp h init e he C hc ht hd hk atC
  have E := Token.reply.inj (term.symm.trans fin)
  subst pay
  exact ⟨back.reply old,valid⟩

end L4.BStarAcquireForwardTrace
