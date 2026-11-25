import Leader.L4.BStarBitHealthyService
import Leader.L4.BStarAcquireHistorySample

namespace L4.BStarBitHealthyIdle
open AllSizeProtocol BStarTrace BStarLongToken BStarLongClaims BStarLongTransport
open BStarLongCommand BStarLongWork BStarLongRouting BStarLongLayout
open BStarLongRoutingFrame BStarAcquireJoinedHop BStarLongEvents
open BStarBitHealthyService
open BStarAcquireNonRouting (actual_door actual_hold)

theorem bound_old (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Wire p)
    (off : gate bitOp a.occurrence (geometry g a.side)=false) :
    bound g (readK x) a=.forward p := by
  unfold bound
  have W : forwardWidth bitOp p.argument.toNat=some 1 := by simp [forwardWidth,bitOp,admit]
  have eq : cropped p 1=p := by
    have A : BitVec.ofNat 34 (low p.argument.toNat 1)=p.argument := by
      rw [show low p.argument.toNat 1=p.argument.toNat from Nat.mod_eq_of_lt healthy.small]
      simp
    cases p
    simp_all [cropped]
  rw [old,bind_bit _ _ _ healthy.fault healthy.op healthy.race healthy.outcome W off,eq]

theorem observe_none (a : AtK) (g : LongGeometry) (p : Payload)
    (healthy : Wire p)
    (off : gate bitOp a.occurrence g=false) : observe a g p=none := by
  simp [observe,healthy.op,off]

theorem normalization_away (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Wire p)
    (off : gate bitOp a.occurrence (geometry g a.side)=false)
    (retained : a∉discarded g) :
    ∀ w∈normalization g (readK x),w.1≠a := by
  have ha := bound_old g x a p old healthy off
  rintro ⟨j,t⟩ hm hj
  change j=a at hj
  subst j
  rcases List.mem_append.mp hm with H|H
  · obtain ⟨j,_,E⟩ := List.mem_filterMap.mp H
    dsimp only at E
    split at E
    · have A : j=a := congrArg Prod.fst (Option.some.inj E)
      subst j
      simp_all [isFault,healthy.fault]
    · cases E
  · obtain ⟨j,hs,E⟩ := List.mem_map.mp H
    have J : j=a := congrArg Prod.fst E
    subst j
    exact retained hs

theorem observations_away (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Wire p)
    (off : gate bitOp a.occurrence (geometry g a.side)=false)
    (written : List KWrite) :
    ∀ w∈observations g (readK x) written,w.1≠a := by
  have ha := bound_old g x a p old healthy off
  rintro ⟨j,t⟩ hm hj
  change j=a at hj
  subst j
  obtain ⟨j,_,E⟩ := List.mem_filterMap.mp hm
  split at E
  · cases E
  · split at E
    · rename_i q hq
      have J : j=a := by
        cases H : observe j (geometry g j.side) q <;> simp_all
      subst j
      rw [ha] at hq
      cases hq
      simp [observe_none _ _ _ healthy off] at E
    · cases E

/-- The immediately preceding Trail and our old healthy off F force a
literal hold. An arbitrary old predecessor F would not. -/
theorem incoming_trail_holds (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (a : AtK) (p : Payload)
    (hd : C.destination=some a) (hn : C.kind=.link)
    (hs : readK x C.source=.trail) (ha : readK x a=.forward p)
    (hp : Wire p)
    (off : gate bitOp a.occurrence (geometry g a.side)=false) :
    BStarLongLiteral.gatedAt g x C=.hold := by
  unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
  change BStarLongCommandData.checkOffer g _ (C,classify C _ (bound g (readK x) C.source)
    ((C.destination.map (bound g (readK x))).getD .empty))=.hold
  rw [hd,Option.map_some,Option.getD_some,bound_old g x a p ha hp off]
  have T : bound g (readK x) C.source=.trail := by simp [bound,hs,BStarLongCommand.bind]
  rw [T]
  simp [classify,hn,BStarLongCommandData.checkOffer]

/-- For a healthy, non-discarded F it suffices to exclude actual
selected command writes to prove that the entire raw routing list
frames its address. -/
theorem routing_away (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : AtK) (p : Payload) (old : readK x a=.forward p) (healthy : Wire p)
    (off : gate bitOp a.occurrence (geometry g a.side)=false)
    (retained : a∉discarded g)
    (cs : ∀ o∈BStarLongEvents.actualOffers g x, ∀ w∈(selected g x o).k,w.1≠a) :
    ∀ w∈routing g x,w.1≠a := by
  have loop (ls : List CmdOffer) (z : Selected)
      (hz : ∀ w∈z.k,w.1≠a)
      (hl : ∀ o∈ls, ∀ w∈(selected g x o).k,w.1≠a) :
      ∀ w∈(ls.foldl (fun acc o => Selected.append acc (selected g x o)) z).k,w.1≠a := by
    induction ls generalizing z with
    | nil => exact hz
    | cons o tl ih =>
      apply ih
      · intro w H
        rcases List.mem_append.mp H with P|P
        · exact hz w P
        · exact hl o List.mem_cons_self w P
      · exact fun o ho => hl o (List.mem_cons_of_mem _ ho)
  let ls := BStarLongEvents.actualOffers g x
  let sel := ls.foldl (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let prior := normalization g (readK x) ++ sel.k
  intro w H
  change w∈prior++observations g (readK x) prior at H
  rcases List.mem_append.mp H with hh|hh
  · rcases List.mem_append.mp hh with h|h
    · exact normalization_away g x a p old healthy off retained w h
    · exact loop ls ⟨[],[],[]⟩ (by simp) cs w h
  · exact observations_away g x a p old healthy off prior w hh

/-- This is the exact local incident-silence obligation: the mark
does not select the forward successor, and its selected predecessor
(if any) is the old Trail. The source door has no routing intents;
its separate WAIT write mask is handled by the K0 frame lemma. -/
theorem row_silent (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Wire p)
    (off : gate bitOp a.occurrence (geometry g a.side)=false)
    (retained : a∉discarded g)
    (noSuccessor : ∀ C∈orderedCommands g,C.source=a → C.kind=.door)
    (predTrail : ∀ C∈orderedCommands g,C.destination=some a → readK x C.source=.trail) :
    ∀ w∈routing g x,w.1≠a := by
  apply routing_away g x a p old healthy off retained
  rintro ⟨C,t⟩ ho w hw he
  have M : C∈orderedCommands g := by
    rw [← BStarLongEvents.actualOffers_claims g x]
    exact List.mem_map.mpr ⟨(C,t),ho,rfl⟩
  have Z : a∈C.slots := he ▸ BStarAcquireLandingHop.selected_slot g x (C,t) w hw
  have either : a=C.source ∨ C.destination=some a := by
    cases H : C.destination <;> simpa [Claim.slots,H,eq_comm] using Z
  rcases either with hs|hd
  · have door := noSuccessor C M hs.symm
    have H : BStarLongLiteral.gatedAt g x C=.door (bound g (readK x) a) := by
      unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
      simp [door,classify,hs,BStarLongCommandData.checkOffer,bound,BStarLongTransport.readK,BStarLongCommandData.oldTokens]
    have Q := actual_door g x (C,t) ho _ H
    dsimp only at Q
    subst t
    unfold selected at hw
    dsimp only at hw
    split at hw <;> cases hw
  · have H := incoming_trail_holds g x C a p hd
      (BStarAcquireReturn.link_shape g C a M hd).2.1 (predTrail C M hd) old healthy off
    have Q := actual_hold g x (C,t) ho H
    dsimp only at Q
    subst t
    cases hw



open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarResetQuiet
open BStarResetChartService BStarResetQuietAdapter BStarResetQuietTable

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Exact full payload retention on each real mark which selects
neither successor nor terminal of the healthy owned BIT. -/
theorem silent_at_bit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x) (pay : Payload)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (F : project (fun j => S.getD j fall) x k=.forward pay) (H : Wire pay)
    (away : gate bitOp (S.getD k fall).2 (longGeometry B (x (S.getD k fall).1))=false)
    (noL : ¬ linkAt hp x e (fun j => S.getD j fall) len k)
    (noT : k=len → ¬ onTerminal hp x e (fun j => S.getD j fall) len) :
    let a := S.getD k fall
    BStarAcquireMarkedPath.NoDeparture (b:=B) x e a ∧
    atCursor (step x e) a=atCursor x a := by
  dsimp only
  let addr := fun j => S.getD j fall
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old (j : Nat) (a : AtK) (E : addr j=address e a) :
      readK raw a=project addr x j :=
    (old_read x e a).trans ((congrArg (atCursor x) E).symm)
  have noOut (a : AtK) (E : addr k=address e a) (cl : CommandClaim)
      (hcl : cl∈orderedCommands g) (src : cl.source=a) : cl.kind=.door := by
    subst a
    rcases touches hp C W.1 e k G.1 cl cl.source hcl (by simp [Claim.slots]) E with D|T|L|⟨i,ik,I⟩
    · exact D.2.1
    · exact (noT T.1 T.2).elim
    · exact (noL L).elim
    · obtain ⟨_,J,d,mem,hd,_,dst⟩ := I
      have eq : cl.source=d := address_inj e he (E.symm.trans (ik ▸ dst))
      have same := BStarAcquireIncidence.same_claim g cl J cl.source hcl mem
        (by simp [Claim.slots]) (by simp [Claim.slots,hd,eq])
      subst J
      exact ((BStarAcquireReturn.link_shape g cl d hcl hd).1 eq.symm).elim
  constructor
  · rintro ⟨cl,q,mem,_,_,E⟩
    have hcl : cl∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨(cl,.advance q),mem,rfl⟩
    have nd := noOut cl.source E cl hcl rfl
    obtain ⟨_,G⟩ := BStarClearanceCommandFrame.advance_origin g raw cl q mem
    have dg : BStarLongLiteral.gatedAt g raw cl =
        .door (bound g (readK raw) cl.source) := by
      unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
      simp [nd,classify,BStarLongCommandData.checkOffer,bound,readK,BStarLongCommandData.oldTokens]
    have Z := actual_door g raw (cl,.advance q) mem _ dg
    cases Z
  · have frame (a : AtK) (E : addr k=address e a) :
        project addr (step x e) k=project addr x k := by
      have MF := frames_any hp C W.1 e (.out k) (by intro zz; cases zz) G W.2.1 W.2.2.1
      obtain ⟨keep,safe⟩ := MF.safe k G.1 a E
      have noPred (cl : CommandClaim) (hc : cl∈orderedCommands g) (hd : cl.destination=some a) :
          readK raw cl.source=.trail := by
        obtain ⟨ne,kind,_⟩ := BStarAcquireReturn.link_shape g cl a hc hd
        rcases touches hp C W.1 e k G.1 cl a hc (by simp [Claim.slots,hd]) E with D|T|L|⟨i,ik,I⟩
        · rw [kind] at D; cases D.2.1
        · exact (noT T.1 T.2).elim
        · exact (noL L).elim
        · obtain ⟨_,J,d,mem,dh,src,dst⟩ := I
          have ed : a=d := address_inj e he (E.symm.trans (ik ▸ dst))
          have same := BStarAcquireIncidence.same_claim g cl J a hc mem
            (by simp [Claim.slots,hd]) (by simp [Claim.slots,dh,ed])
          subst J
          exact (old _ _ src).trans (G.2.2 i (by omega))
      have off : gate bitOp a.occurrence (geometry g a.side)=false := by
        change gate bitOp (addr k).2 (longGeometry B (x (addr k).1))=false at away
        rw [E] at away
        cases a with
        | mk s b => cases s <;> exact away
      have route := row_silent g raw a pay ((old _ _ E).trans F) H off keep (noOut a E) noPred
      have post := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
      exact post.symm.trans ((BStarAcquireHistorySample.joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) a safe route).trans (old _ _ E))
    by_cases l : (addr k).1=e
    · exact frame (L (addr k).2) (Prod.ext l rfl)
    · by_cases r : (addr k).1=rightNeighbor e
      · exact frame (R (addr k).2) (Prod.ext r rfl)
      · exact BStarResetIdleRing.idle_off_pair hp x e (addr k) l r



end L4.BStarBitHealthyIdle
