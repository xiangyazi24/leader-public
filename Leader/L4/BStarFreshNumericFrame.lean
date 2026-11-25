import Leader.L4.BStarFreshNumeric
import Leader.L4.BStarSeparatorRing

/-! An unselected healthy numeric front is unchanged on the literal
joined mark; an incoming trail link cannot spoil it. -/
namespace L4.BStarFreshNumericFrame
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongCommandData
open BStarLongCommand BStarLongArithmetic BStarLongSignatures BStarNumericCarry
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarResetMarkAdapter
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetQuietAdapter
open BStarResetRailRing BStarResetChartService BStarSeparatorQuiet BStarSeparatingRail
open BStarSeparatorControl BStarResetQuietTable BStarResetQuiet BStarResetIdleRing
open BStarLongRouting BStarAcquireHistorySample BStarFreshNumeric

private theorem canonical_quiet (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (p : Payload) (E : bound g (readK raw) a=.forward p)
    (H : Numeric p) (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    avoids a (routing g raw) := by
  intro w M W
  rw [routing_parts] at M
  rcases List.mem_append.mp M with h|h
  · rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp h
        dsimp only at Q
        split at Q
        · rename_i bad
          have eq := (congrArg Prod.fst (Option.some.inj Q)).trans W
          change q=a at eq
          subst q
          simp [E,isFault,H.1] at bad
        · contradiction
      · obtain ⟨q,hq,Q⟩ := List.mem_map.mp h
        have eq := (congrArg Prod.fst Q).trans W
        change q=a at eq
        subst q
        exact keep hq
    · exact mid w h W
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp h
    split at Q
    · contradiction
    · split at Q
      · rename_i t V
        cases A : observe q (geometry g q.side) t <;>
          simp only [A,Option.map_some,Option.map_none] at Q
        · contradiction
        · have eq := (congrArg Prod.fst (Option.some.inj Q)).trans W
          change q=a at eq
          subst q
          change bound g (readK raw) a=.forward t at V
          rw [E] at V
          cases V
          have G := numeric_gate (geometry g a.side) a.occurrence p H
          simp [observe,G] at A
      · contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c pmod c₁ n : Nat} (hp : 0<pmod)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c pmod c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem ring_hold {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (p : Payload) (F : project (fun j => S.getD j fall) x k=.forward p) (H : Healthy p)
    (N : ¬linkAt hp x e (fun j => S.getD j fall) len k)
    (T : k=len → ¬onTerminal hp x e (fun j => S.getD j fall) len) :
    project (fun j => S.getD j fall) (step x e) k=.forward p := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have MF := frames_any hp chart W.1 e (.out k) (by intro E; cases E) G W.2.1 W.2.2.1
  have old (j : Nat) (a : AtK) (E : addr j=address e a) : readK raw a=project addr x j :=
    (old_read x e a).trans ((congrArg (atCursor x) E).symm)
  have exact_at (a : AtK) (D : addr k=address e a) (A : avoids a (middle g raw)) :
      project addr (step x e) k=.forward p := by
    obtain ⟨keep,safe⟩ := MF.safe k G.1 a D
    have bound : bound g (readK raw) a=.forward p := by
      unfold BStarLongTransport.bound
      rw [(old k a D).trans F]
      exact H.bound _ _
    have J := joined_silent k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp (x e,x (rightNeighbor e)) a safe
      (canonical_quiet g raw a p bound H.numeric keep A)
    exact (congrArg (atCursor (step x e)) D).trans ((new_read B x e he a).symm.trans (J.trans ((old k a D).trans F)))
  by_cases prev : ∃ j, j+1=k ∧ linkAt hp x e addr len j
  · obtain ⟨j,E,_,C,d,mem,dst,src,tgt⟩ := prev
    have K := (BStarAcquireReturn.link_shape g C d mem dst).2.1
    have L : LinkHold (bound g (readK raw) C.source) (bound g (readK raw) d) := by
      unfold BStarLongTransport.bound
      rw [(old j C.source src).trans (G.2.2 j (by omega)), (old (j+1) d tgt).trans (E.symm ▸ F),
        H.bound _ _]
      exact .tf p
    have A := (link_avoids g raw C d mem K dst L).2
    exact exact_at d (E ▸ tgt) A
  · by_cases left : (addr k).1=e
    · have D : addr k=address e (L (addr k).2) := Prod.ext left rfl
      exact exact_at _ D (MF.idle_avoids k G.1 _ D N (fun j E H => prev ⟨j,E,H⟩) T)
    · by_cases right : (addr k).1=rightNeighbor e
      · have D : addr k=address e (R (addr k).2) := Prod.ext right rfl
        exact exact_at _ D (MF.idle_avoids k G.1 _ D N (fun j E H => prev ⟨j,E,H⟩) T)
      · exact (idle_off_pair hp x e (addr k) left right).trans F

/-- The old carrier leaves a Trail on this very mark. This rules out
the stay branch of a geometric cursor observation without post-health. -/
theorem ring_link_trail {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (p : Payload) (F : project (fun j => S.getD j fall) x k=.forward p) (H : Healthy p)
    (L : linkAt hp x e (fun j => S.getD j fall) len k) :
    project (fun j => S.getD j fall) (step x e) k=.trail := by
  obtain ⟨_,C,a,mem,dst,src,_⟩ := L
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have O := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans F)
  obtain ⟨ne,kind,_⟩ := BStarAcquireReturn.link_shape g C a mem dst
  have NK : C.kind≠.door := by rw [kind]; decide
  have sel := selected_advance g raw C p mem NK O H
  have MF := frames_any hp chart W.1 e (.out k) (by intro E; cases E) G W.2.1 W.2.2.1
  have A := BStarClearanceForward.move_lands g raw C p a dst sel (Ne.symm ne)
  have J := (new_read B x e he C.source).trans ((congrArg (atCursor (step x e)) src).symm)
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) C.source)=_ at J
  have gh := joined_work_raw k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp (x e,x (rightNeighbor e)) C.source
    (MF.safe k G.1 C.source src).2.valid
  erw [gh,A.1,decode_encode] at J
  exact J.symm

end L4.BStarFreshNumericFrame
