import Leader.L4.BStarResetChartIndex
import Leader.L4.BStarResetMarkAdapter

namespace L4.BStarResetChartTouch
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartIndex BStarResetMarkAdapter
open BStarAcquireRailCoverage BStarAcquireGlobalChain

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

structure Chart (base : X) (hh : ∃ i, oldH6 B base i=true)
    (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fallback : Pos n) : Prop where
  length : S.length=len+1
  nodup : S.Nodup
  root : S.getD 0 fallback=endpoint (oldH6 B base) hh o 0
  terminal : S.getD len fallback=endpoint (oldH6 B base) hh o 10
  cover : ∀ u, active (longGeometry B (base u.1)) u.2=true →
    commandOwner (oldH6 B base) u.1 u.2=o.val → u∈S
  entries : ∀ u∈S, active (longGeometry B (base u.1)) u.2=true ∧
    commandOwner (oldH6 B base) u.1 u.2=o.val
  edge : ∀ u v, u∈S → Edge B base u v → adjacent S u v

private theorem addr_mem {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (h : S.length=len+1) {j : Nat} (hj : j≤len) : S.getD j fallback∈S := by
  rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
  exact List.getElem_mem _

/-- Classify a selected old command slot touching the indexed rail.
The link labels refer to this very mark, not merely to a link
somewhere on the fixed layout. -/
theorem touches {base y : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B y i) (e : Fin n)
    (j : Nat) (hj : j≤len) (C : CommandClaim) (a : At (Fin 11))
    (hc : C∈orderedCommands (oldPair B y e)) (ha : a∈C.slots)
    (hit : S.getD j fallback=address e a) :
    (j=0 ∧ C.kind=.door ∧ a=R 0) ∨
    (j=len ∧ onTerminal hp y e (fun j => S.getD j fallback) len) ∨
    linkAt hp y e (fun j => S.getD j fallback) len j ∨
    ∃ i, i+1=j ∧ linkAt hp y e (fun j => S.getD j fallback) len i := by
  let addr := fun k => S.getD k fallback
  have lenS := chart.length
  have inj (i k : Nat) (hi : i≤len) (hk : k≤len) (eq : addr i=addr k) : i=k :=
    (List.getD_inj (by omega) (by omega) chart.nodup).mp eq
  have J := chart.entries _ (addr_mem (fallback:=fallback) lenS hj)
  have link (D : At (Fin 11)) (dC : C.destination=some D)
      (uM : address e C.source∈S) :
      ∃ i, linkAt hp y e addr len i ∧ addr i=address e C.source ∧ addr (i+1)=address e D := by
    have E : Edge B y (address e C.source) (address e D) := ⟨e,C,D,hc,dC,rfl,rfl⟩
    obtain ⟨i,hi,L,R⟩ := chart.edge _ _ uM ((edge_fixed B base y same _ _).mpr E)
    have L' : addr i=address e C.source := (List.getElem_eq_getD _).symm.trans L
    have R' : addr (i+1)=address e D := (List.getElem_eq_getD _).symm.trans R
    exact ⟨i,⟨by omega,C,D,hc,dC,L',R'⟩,L',R'⟩
  have touchesSlot : a=C.source ∨ C.destination=some a := by
    cases D : C.destination <;> simpa [Claim.slots,D,eq_comm] using ha
  rcases touchesSlot with rfl|dest
  · have own : commandOwner (oldH6 B base) (address e C.source).1 C.source.occurrence=o.val := by
      simpa only [hit] using J.2
    rcases selected_endpoint_or_link B base y hh same o e C hc own with hd|ht|hl
    · have H := selected_door _ C hc hd.1
      exact .inl ⟨inj j 0 hj (Nat.zero_le _) (hit.trans (hd.2.2.trans chart.root.symm)),hd.1,H.1⟩
    · have k := inj j len hj (Nat.le_refl _) (hit.trans (ht.2.2.trans chart.terminal.symm))
      have K := BStarAcquireChainEndpoints.terminal _ C hc ht.2.1 (by rw [ht.1]; decide)
      exact .inr (.inl ⟨k,C,hc,ht.1,ht.2.1,K.2.2.2,k ▸ hit⟩)
    · obtain ⟨D,dC,_⟩ := hl
      have M : address e C.source∈S := hit ▸ addr_mem (fallback:=fallback) lenS hj
      obtain ⟨i,il,L,_⟩ := link D dC M
      have E := inj j i hj (Nat.le_of_lt il.1) (hit.trans L.symm)
      exact .inr (.inr (.inl (E.symm ▸ il)))
  · have E := BStarAcquireChainEndpoints.link_endpoints _ C a hc dest
    have own : commandOwner (oldH6 B base) (address e C.source).1 C.source.occurrence=o.val := by
      have H := actual_command_owner B base e C a ((command_eq B base y same e).symm ▸ hc) dest
      have Q := J.2
      rw [hit] at Q
      exact H.trans Q
    have LC := (command_eq B base y same e).symm ▸ hc
    have H := (BStarAcquireChainEndpoints.link_endpoints _ C a LC dest).1
    have gg : BStarLongCommand.geometry (oldPair B base e) C.source.side =
        longGeometry B (base (address e C.source).1) := by cases s : C.source.side <;> simp [s, BStarLongCommand.geometry, oldPair, site]
    rw [gg] at H
    -- Source coverage is supplied by the caller's exact owner chart.
    have M : address e C.source∈S := by
      exact chart.cover _ H own
    obtain ⟨i,il,_,R⟩ := link a dest M
    have eq := inj j (i+1) hj (by have := il.1; omega) (hit.trans R.symm)
    exact .inr (.inr (.inr ⟨i,eq.symm,il⟩))

/-- Active indexed addresses cannot be erased by local off-IN
K8/K9 cleanup at a fixed-layout snapshot. -/
theorem not_discarded {base y : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B y i) (e : Fin n)
    (j : Nat) (hj : j≤len) (a : At (Fin 11)) (hit : S.getD j fallback=address e a) :
    a∉discarded (oldPair B y e) := by
  intro D
  have H := (chart.entries _ (addr_mem (fallback:=fallback) chart.length hj)).1
  rw [hit] at H
  have eq := congrArg (fun z : Bool × Bool × Bool => z.2.1) (same (address e a).1)
  change (longGeometry B (base (address e a).1)).inside =
    (longGeometry B (y (address e a).1)).inside at eq
  unfold active at H
  rw [eq] at H
  obtain ⟨side,k⟩ := a
  cases side
  · change (L k)∈discarded (oldPair B y e) at D
    cases I : (longGeometry B (y e)).inside <;>
      cases T : (longGeometry B (y (rightNeighbor e))).inside <;>
      simp [discarded,oldPair,I,T,L,R] at D <;>
      (rcases D with rfl|rfl) <;> simp [site,I] at H <;> omega
  · change (R k)∈discarded (oldPair B y e) at D
    cases I : (longGeometry B (y e)).inside <;>
      cases T : (longGeometry B (y (rightNeighbor e))).inside <;>
      simp [discarded,oldPair,I,T,L,R] at D <;>
      (rcases D with rfl|rfl) <;> simp [site,T] at H <;> omega

private theorem route_entries {V O : Type} {G : BStarAcquireGlobalChain.Rail V O}
    {u z : V} {L : List V} (P : Route G u L z) (H : G.active u) :
    ∀ v∈L++[z], G.active v ∧ G.owner v=G.owner u := by
  induction P with
  | nil u =>
    intro v hv
    have E : v=u := List.mem_singleton.mp hv
    exact E.symm ▸ ⟨H,rfl⟩
  | cons E Q ih =>
    intro v hv
    rcases List.mem_cons.mp hv with q|q
    · exact q.symm ▸ ⟨H,rfl⟩
    · obtain ⟨h,Eq⟩ := ih (G.edge_active E).2 v q
      exact ⟨h,Eq.trans (G.edge_owner E).symm⟩

/-- Construct the complete indexed chart of an actual owner directly
from legitimate fixed H6/IN/LAST geometry, not from supplied routes. -/
theorem chart_exists (base : X) (hh : ∃ i, oldH6 B base i=true) (width : Nat)
    (hw : 0<width)
    (flags : ∀ i, let g := longGeometry B (base i)
      g.inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<width) ∧
      g.last=decide (BStarH6Ordinal.oldOrdinal B base hh i+1=width))
    (notShort : ∀ i, oldH6 B base (rightNeighbor i)=true →
      width≤BStarH6Ordinal.oldOrdinal B base hh i+1)
    (o : Owners (oldH6 B base)) (fallback : Pos n) :
    ∃ S len, Chart hp base hh o S len fallback := by
  let G := literal B base hh width hw flags notShort
  obtain ⟨L,P,_,cover⟩ := owner_chain G o
  let S := L++[G.terminal o]
  have own_eq (v : Pos n) : G.owner v=o ↔ commandOwner (oldH6 B base) v.1 v.2=o.val :=
    ⟨congrArg Subtype.val, fun e => Subtype.ext e⟩
  have len : S.length=L.length+1 := by simp [S]
  refine ⟨S,L.length,len, route_nodup P,?_,?_,?_,?_,?_⟩
  · rw [←List.getElem_eq_getD (h:=show 0<S.length by omega)]
    change S[0] = G.root o
    have eq {u z : Pos n} {W : List (Pos n)} (Q : Route G u W z) :
        (W++[z])[0]'(by simp)=u := by
      cases Q <;> rfl
    exact eq P
  · rw [←List.getElem_eq_getD (h:=show L.length<S.length by omega)]
    change (L++[G.terminal o])[L.length] = G.terminal o
    rw [List.getElem_append_right (by omega)]
    simp
  · intro u hu ou
    exact cover u hu ((own_eq u).mpr ou)
  · intro u mu
    obtain ⟨h,e⟩ := route_entries P (G.root_active o) u mu
    exact ⟨h,(own_eq u).mp (e.trans (G.root_owner o))⟩
  · intro u v mu E
    exact (route_edges P (fun _ H => G.no_terminal_exit H (by rw [G.terminal_owner])) u v).mp ⟨mu,E⟩

#print axioms chart_exists
#print axioms touches
#print axioms not_discarded
end L4.BStarResetChartTouch
