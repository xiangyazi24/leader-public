import Leader.L4.BStarAcquireLiteralChain
import Leader.L4.BStarLongFixedRouting

namespace L4.BStarResetChartIndex
open BStarAcquireGlobalChain

variable {V O : Type} {G : BStarAcquireGlobalChain.Rail V O}

/-- Zero-based physical positions on the finite list, including the
terminal at the last index. -/
def adjacent (S : List V) (u v : V) : Prop :=
  ∃ (i : Nat) (h : i+1<S.length), S[i]'(by omega)=u ∧ S[i+1]=v

private theorem adjacent_cons (a u v : V) (S : List V) :
    adjacent (a::S) u v ↔
      (∃ h : 0<S.length, a=u ∧ S[0]=v) ∨ adjacent S u v := by
  constructor
  · rintro ⟨i,h,U,W⟩
    cases i with
    | zero => exact .inl ⟨by simpa using h,U,W⟩
    | succ i => exact .inr ⟨i,by simpa using h,U,W⟩
  · rintro (⟨h,U,W⟩|⟨i,h,U,W⟩)
    · exact ⟨0,by simpa using h,U,W⟩
    · exact ⟨i+1,by simpa using h,U,W⟩

private theorem initial_zero {u z : V} {L : List V} (_P : Route G u L z) :
    ∃ h : 0<(L++[z]).length, (L++[z])[0]=u := by
  cases _P with
  | nil => exact ⟨by simp,rfl⟩
  | cons => exact ⟨by simp,rfl⟩

/-- Every actual outgoing edge of a listed vertex is precisely the
adjacent indexed edge of the list, with no outgoing at its terminal. -/
theorem route_edges {u z : V} {L : List V} (P : Route G u L z)
    (halt : ∀ t, ¬ G.edge z t) (s t : V) :
    (s∈L++[z] ∧ G.edge s t) ↔ adjacent (L++[z]) s t := by
  induction P with
  | nil =>
    simp only [List.nil_append,List.mem_singleton]
    constructor
    · rintro ⟨rfl,E⟩
      exact (halt _ E).elim
    · rintro ⟨i,h,_,_⟩
      simp at h
  | @cons u v z L E P ih =>
    simp only [List.cons_append,adjacent_cons,List.mem_cons]
    obtain ⟨h,head⟩ := initial_zero P
    constructor
    · rintro ⟨rfl|hs,F⟩
      · exact .inl ⟨h,rfl,head.trans (G.succ_unique E F)⟩
      · exact .inr ((ih halt).mp ⟨hs,F⟩)
    · rintro (⟨_,rfl,H⟩|A)
      · have eq := head.symm.trans H
        exact ⟨.inl rfl,eq ▸ E⟩
      · obtain ⟨m,F⟩ := (ih halt).mpr A
        exact ⟨.inr m,F⟩

/-- Rank is strictly increasing on the indexed chart, hence it
contains no physical address twice. -/
theorem route_rank {u z : V} {L : List V} (_P : Route G u L z) :
    (L++[z]).Pairwise (fun s t => G.rank s<G.rank t) := by
  have lower {s z : V} {W : List V} (Q : Route G s W z) :
      ∀ v∈W++[z], G.rank s≤G.rank v := by
    induction Q with
    | nil => simp
    | cons E P ih =>
      intro v h
      rcases List.mem_cons.mp h with rfl|m
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_of_lt (G.edge_rank E)) (ih v m)
  induction _P with
  | nil => simp
  | cons E P ih =>
    exact .cons (fun t ht => Nat.lt_of_lt_of_le (G.edge_rank E) (lower P t ht)) ih

theorem route_nodup {u z : V} {L : List V} (_P : Route G u L z) :
    (L++[z]).Nodup :=
  (route_rank _P).imp (fun {s t} Lt (eq : s=t) => (Nat.lt_irrefl _ (eq ▸ Lt)))

open AllSizeProtocol BStarAcquireVisitOrder BStarLongFixedRouting
open BStarAcquireLiteralChain BStarH6WordChart

/-- A route supplied by the literal fixed rail is an indexed exact
chart for all selected edges out of its addresses, even when the
packed state is taken at another snapshot on the same fixed layout. -/
theorem fixed_edges {a : LargeParams} {n r : Nat} (b : LargeRows a)
    (x y : Fin n → LargeSite a) (hh : ∃ i, oldH6 b x i=true)
    (hr : 0<r)
    (flags : ∀ i, let g := longGeometry b (x i)
      g.inside=decide (BStarH6Ordinal.oldOrdinal b x hh i<r) ∧
      g.last=decide (BStarH6Ordinal.oldOrdinal b x hh i+1=r))
    (notShort : ∀ i, oldH6 b x (rightNeighbor i)=true →
      r≤BStarH6Ordinal.oldOrdinal b x hh i+1)
    (same : ∀ i, Layout b x i=Layout b y i)
    (o : Owners (oldH6 b x)) :
    let K := literal b x hh r hr flags notShort
    ∃ L, Route K (K.root o) L (K.terminal o) ∧
      (L++[K.terminal o]).Nodup ∧
      (∀ v, K.active v → K.owner v=o → v∈L++[K.terminal o]) ∧
      ∀ u v, (u∈L++[K.terminal o] ∧ Edge b y u v) ↔ adjacent (L++[K.terminal o]) u v := by
  dsimp only
  let K := literal b x hh r hr flags notShort
  obtain ⟨L,P,_,cover⟩ := owner_chain K o
  refine ⟨L,P,route_nodup P,cover,?_⟩
  intro u v
  rw [←edge_fixed b x y same u v]
  exact route_edges P (fun _ E => K.no_terminal_exit E (by rw [K.terminal_owner])) u v

open BStarLongClaims BStarAcquireAnchors

private def smallGeo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- A selected door is exactly old right H6 K0, with no destination. -/
theorem selected_door (g : Pair LongGeometry) (C : CommandClaim)
    (hc : C∈orderedCommands g) (hd : C.kind=.door) :
    C.source=R 0 ∧ g.2.axes.h6=true ∧ C.destination=none := by
  obtain ⟨x,y⟩ := g
  let test (h : Bool) (C : CommandClaim) : Bool :=
    C.kind != .door || (C.source == R 0 && h && C.destination.isNone)
  have A (I L H J : Bool) :
      (commandClaims (smallGeo false I L,smallGeo H J false)).all (test H)=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_command_raw _ _ hc
  change C ∈ commandClaims (smallGeo false x.inside x.last,
    smallGeo y.axes.h6 y.inside false) at raw
  have F := List.all_eq_true.mp (A x.inside x.last y.axes.h6 y.inside) C raw
  cases H : C.destination <;> simp [test,hd,H] at F ⊢
  exact F

/-- For an actual selected claim of an owner, the door/terminal are
the indexed root/end. The link case yields the actual Edge, to
be converted to adjacent indices by the fixed chart theorem. -/
theorem selected_endpoint_or_link {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x y : Fin n → LargeSite a) (hh : ∃ i, oldH6 b x i=true)
    (same : ∀ i, Layout b x i=Layout b y i) (o : Owners (oldH6 b x))
    (e : Fin n) (C : CommandClaim) (hc : C ∈ orderedCommands (oldPair b y e))
    (ho : commandOwner (oldH6 b x) (site e C.source.side) C.source.occurrence=o.val) :
    let u : Pos n := (site e C.source.side,C.source.occurrence)
    (C.kind=.door ∧ C.destination=none ∧ u=endpoint (oldH6 b x) hh o 0) ∨
    (C.kind=.terminal ∧ C.destination=none ∧ u=endpoint (oldH6 b x) hh o 10) ∨
    ∃ D, C.destination=some D ∧ Edge b y u (site e D.side,D.occurrence) := by
  dsimp only
  have H : oldH6 b x (rightNeighbor e)=oldH6 b y (rightNeighbor e) :=
    congrArg Prod.fst (same (rightNeighbor e))
  by_cases hd : C.kind=.door
  · obtain ⟨s,T,nD⟩ := selected_door _ C hc hd
    left
    refine ⟨hd,nD,?_⟩
    simp only [s,R,site] at ho ⊢
    exact (endpoint_spec _ hh o 0).2.2 _ (H.trans T) ho
  · cases D : C.destination with
    | some d => exact .inr (.inr ⟨d,rfl,e,C,d,hc,D,rfl,rfl⟩)
    | none =>
      obtain ⟨t,s,T,k⟩ := BStarAcquireChainEndpoints.terminal _ C hc D hd
      right; left
      refine ⟨t,rfl,?_⟩
      have K : C.source.occurrence=10 := Fin.ext k
      simp only [s,site,K] at ho ⊢
      exact (endpoint_spec _ hh o 10).2.2 _ (H.trans T) ho

end L4.BStarResetChartIndex
