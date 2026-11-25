import Leader.L4.BStarLongFixedRouting
import Leader.L4.BStarLongEvents
import Leader.L4.BStarAcquireDepart

/-! The observed ACQUIRE path on an actual marked word. Selection is
read from the literal old pair after grant; no itinerary is supplied. -/
namespace L4.BStarAcquireMarkedPath
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarAcquireVisitOrder
open BStarLongFixedRouting BStarLongEvents BStarLongToken
open BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}

/-- The physical ring edge update, including the joined non-long rows. -/
def marked {a : LargeParams} (b : LargeRows a) (x : Fin n → LargeSite a)
    (e : Fin n) : Fin n → LargeSite a :=
  let j := rightNeighbor e
  let y := largePair b (x e,x j)
  fun i => if i=e then y.1 else if i=j then y.2 else x i

variable {b : LargeRows (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)}
abbrev Ring (_b : LargeRows (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (n : Nat) := Fin n → LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Actual post-grant offers on the selected old packed pair. -/
def offers (b : LargeRows (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (x : Ring b n) (e : Fin n) :=
  actualOffers (oldPair b x e) ((x e).long,(x (rightNeighbor e)).long)

/-- A continuing ACQUIRE selected from the old pair at the tracked
cursor, with its exact destination from the selected claim. -/
def Advance (x : Ring b n) (e : Fin n) (u v : Pos n) : Prop :=
  ∃ C D P, (C,.advance P) ∈ offers b x e ∧ P.opcode.toNat = acquire ∧ P.fault=0 ∧
    C.destination=some D ∧
    u=(site e C.source.side,C.source.occurrence) ∧ v=(site e D.side,D.occurrence)

/-- No selected ACQUIRE departure from the tracked cursor (including
the final slot's terminal action). Does not itself certify retention. -/
def NoDeparture (x : Ring b n) (e : Fin n) (u : Pos n) : Prop :=
  ¬ ∃ C P, (C,.advance P) ∈ offers b x e ∧ P.opcode.toNat = acquire ∧ P.fault=0 ∧
    u=(site e C.source.side,C.source.occurrence)

theorem advance_edge {x : Ring b n} {e : Fin n} {u v : Pos n} (H : Advance x e u v) :
    Edge b x u v := by
  obtain ⟨C,D,P,h,_,_,hd,hu,hv⟩ := H
  refine ⟨e,C,D,?_,hd,hu,hv⟩
  change C ∈ orderedCommands (oldPair b x e)
  rw [←actualOffers_claims _ ((x e).long,(x (rightNeighbor e)).long)]
  exact List.mem_map.mpr ⟨(C,Offer.advance P),h,rfl⟩

/-- Observation of the tracked token on an exact marked word.
Frame/lineage is explicit: a client chooses the tracked cursor and
must justify that a silent observation retains the intended token.
All movement and every updated physical state are literal. -/
inductive Observed (b : LargeRows (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Ring b n) : Ring b n → Pos n → List (Fin n) →
      Ring b n → Pos n → List (Pos n) → Prop where
  | nil (x u) : Observed b base x u [] x u []
  | silent {x y u z e w L} :
      NoDeparture (b:=b) x e u →
      Observed b base (marked b x e) u w y z L →
      Observed b base x u (e::w) y z L
  | depart {x y u v z e w L} :
      (∀ i, BStarLongFixedRouting.Layout b x i=BStarLongFixedRouting.Layout b base i) →
      Advance (b:=b) x e u v →
      Observed b base (marked b x e) v w y z L →
      Observed b base x u (e::w) y z (u::L)

/-- The finite exact marked observations accumulate a structural path
on the fixed layout, so the itinerary is a conclusion, not a premise. -/
theorem observed_path {base x y : Ring b n} {u z : Pos n} {w : List (Fin n)}
    {L : List (Pos n)} (H : Observed b base x u w y z L) :
    Path b base u L z := by
  induction H with
  | nil => exact .nil _
  | silent _ _ ih => exact ih
  | @depart x y u v z e w L lay obs _ ih =>
    have hh : Edge b x u v := advance_edge (b:=b) (x:=x) (e:=e) obs
    have hh' : Edge b base u v := (edge_fixed b x base lay u v).mp hh
    exact .cons hh' ih

/-- Independent evaluator for the exact underlying physical word. -/
def run {a : LargeParams} (b : LargeRows a) (x : Fin n → LargeSite a)
    (w : List (Fin n)) : Fin n → LargeSite a :=
  w.foldl (marked b) x

/-- Retaining or departing the tracked cursor cannot change the real
physical endpoint: both branches apply the same joined transition. -/
theorem observed_endpoint {base x y : Ring b n} {u z : Pos n} {w : List (Fin n)}
    {L : List (Pos n)} (H : Observed b base x u w y z L) :
    run b x w = y := by
  induction H with
  | nil => rfl
  | silent _ _ ih => exact ih
  | depart _ _ _ ih => exact ih

/-- A mark not incident to the tracked site has no ACQUIRE departure
there and preserves the whole cell, not just its long field. -/
theorem off_pair {x : Ring b n} {e : Fin n} {u : Pos n}
    (hl : u.1 ≠ e) (hr : u.1 ≠ rightNeighbor e) :
    NoDeparture (b:=b) x e u ∧ marked b x e u.1=x u.1 := by
  refine ⟨?_, by simp [marked,hl,hr]⟩
  rintro ⟨C,P,_,_,_,hu⟩
  have eq := congrArg Prod.fst hu
  cases H : C.source.side
  · exact hl (by simpa only [H,site] using eq)
  · exact hr (by simpa only [H,site] using eq)

/-- An observed K0-header to K10 marked interval uses the three
header departures exactly once on its fixed physical rail. -/
theorem observed_departures_once {base x y : Ring b n} {u z : Pos n} {w : List (Fin n)}
    {L : List (Pos n)} (H : Observed b base x u w y z L)
    (hu : u.2.val=0) (huH : oldH6 b base u.1=true) (hz : z.2.val=10)
    (k : Nat) (hk : k≤2) :
    (L.filter (fun v => v.2.val == k && oldH6 b base v.1)).length = 1 :=
  departures_once (observed_path H) hu huH hz k hk

open BStarTrace BStarLongTransport BStarLongRouting BStarLongLayout BStarLongWork

private theorem ring_read {a : LargeParams} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (h : e ≠ rightNeighbor e) (s : AtK)
    (lw : (q : LargeSite a) → BitVec LW) :
    readK (Pair.map lw (largePair b (x e,x (rightNeighbor e)))) s =
      readK (lw (marked b x e (site e s.side)),lw (marked b x e (site e s.side))) (L s.occurrence) := by
  cases s with
  | mk side k =>
    cases side
    · simp [marked,site,readK,L,Pair.map]; rfl
    · simp [marked,site,readK,L,Pair.map,Ne.symm h]; rfl

/-- A healthy old tracked token on a literal continuing link has
a Trail at its real old site and the updated forward payload at its
real new site after the identical marked ring transition. -/
theorem marked_hop (hp : 0<p)
    (x : Ring (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) n) (e : Fin n)
    (he : e ≠ rightNeighbor e) (C : CommandClaim) (D : AtK) (pay : Payload)
    (hc : C∈orderedCommands (oldPair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x e))
    (hd : C.destination=some D)
    (hold : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward pay)
    (healthy : BStarAcquireHop.Healthy pay) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let y := marked b x e
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    readK ((y (site e C.source.side)).long,(y (site e C.source.side)).long) (L C.source.occurrence)
      = .trail ∧
    readK ((y (site e D.side)).long,(y (site e D.side)).long) (L D.occurrence)
      = .forward (BStarAcquireHop.argUpdate g raw (BStarLongCommandData.round g raw).offered C pay) := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let xy := (x e,x (rightNeighbor e))
  let g := oldPair b x e
  have shape := BStarAcquireReturn.link_shape g C D hc hd
  have hn : C.kind ≠ .door := by rw [shape.2.1]; decide
  have a := BStarAcquireDepart.joined_departs k₁ k₂ t₂ J₁ J₂ r c p c₁ hp xy C D pay hc hd hold healthy
  have d := BStarAcquireJoinedHop.joined_acquire_lands k₁ k₂ t₂ J₁ J₂ r c p c₁ hp xy C D pay hc hd hn hold healthy
  rw [ring_read b x e he C.source LargeSite.long] at a
  rw [ring_read b x e he D LargeSite.long] at d
  exact ⟨a,d⟩

#print axioms marked_hop
#print axioms observed_path
#print axioms observed_departures_once
end L4.BStarAcquireMarkedPath
