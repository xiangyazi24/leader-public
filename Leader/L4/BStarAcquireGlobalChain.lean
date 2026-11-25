import Leader.L4.BStarAcquireRailCoverage

/-! Finite deterministic command chains. The literal chart must supply
the active fixed endpoints and both unique-neighbor conditions. -/
namespace L4.BStarAcquireGlobalChain

structure Rail (V O : Type) where
  active : V → Prop
  owner : V → O
  rank : V → Nat
  root : O → V
  terminal : O → V
  edge : V → V → Prop
  root_active : ∀ o, active (root o)
  root_owner : ∀ o, owner (root o)=o
  terminal_owner : ∀ o, owner (terminal o)=o
  edge_active : ∀ {u v}, edge u v → active u ∧ active v
  edge_owner : ∀ {u v}, edge u v → owner u=owner v
  edge_rank : ∀ {u v}, edge u v → rank u<rank v
  fuel : Nat
  rank_bound : ∀ v, active v → rank v≤fuel
  pred : ∀ v, active v → v≠root (owner v) → ∃ u, edge u v
  succ : ∀ v, active v → v≠terminal (owner v) → ∃ u, edge v u
  succ_unique : ∀ {u v w}, edge u v → edge u w → v=w
  no_terminal_exit : ∀ {u v}, edge u v → u≠terminal (owner u)

inductive Route {V O : Type} (G : Rail V O) : V → List V → V → Prop where
  | nil (u) : Route G u [] u
  | cons {u v z L} : G.edge u v → Route G v L z → Route G u (u::L) z

variable {V O : Type} {G : Rail V O}

theorem Route.append {u v z : V} {L W : List V}
    (A : Route G u L v) (B : Route G v W z) : Route G u (L++W) z := by
  induction A with
  | nil => exact B
  | cons E Q ih => exact .cons E (ih B)

theorem Route.contains_at_join {u v z : V} {L W : List V}
    (_A : Route G u L v) (B : Route G v W z) : v ∈ (L++W)++[z] := by
  have h : v∈W++[z] := by
    cases B with
    | nil => simp
    | cons => simp
  simpa only [List.append_assoc] using List.mem_append_right L h

/-- Ranking backwards recovers a source root for every active slot. -/
theorem from_root (G : Rail V O) (v : V) (hv : G.active v) :
    ∃ L, Route G (G.root (G.owner v)) L v := by
  suffices all : ∀ i, ∀ v : V, G.rank v≤i → G.active v →
       ∃ L, Route G (G.root (G.owner v)) L v from all (G.rank v) v (Nat.le_refl _) hv
  intro i
  induction i with
  | zero =>
    intro v h hv
    by_cases eq : v=G.root (G.owner v)
    · exact ⟨[], eq ▸ Route.nil v⟩
    · obtain ⟨u,E⟩ := G.pred v hv eq
      have k := G.edge_rank E
      omega
  | succ i ih =>
    intro v h hv
    by_cases eq : v=G.root (G.owner v)
    · exact ⟨[], eq ▸ Route.nil v⟩
    · obtain ⟨u,E⟩ := G.pred v hv eq
      have k := G.edge_rank E
      obtain ⟨L,R⟩ := ih u (by omega) (G.edge_active E).1
      have H := R.append (Route.cons E (Route.nil v))
      exact ⟨L++[u], by rwa [G.edge_owner E] at H⟩

/-- Every active cursor has a finite continuation to its own terminal. -/
theorem to_terminal (G : Rail V O) (v : V) (hv : G.active v) :
    ∃ L, Route G v L (G.terminal (G.owner v)) := by
  suffices all : ∀ i, ∀ v : V, G.fuel-G.rank v≤i → G.active v →
       ∃ L, Route G v L (G.terminal (G.owner v)) from
    all (G.fuel-G.rank v) v (Nat.le_refl _) hv
  intro i
  induction i with
  | zero =>
    intro v h hv
    by_cases eq : v=G.terminal (G.owner v)
    · exact ⟨[], eq ▸ Route.nil v⟩
    · obtain ⟨u,E⟩ := G.succ v hv eq
      have k := G.edge_rank E
      have b := G.rank_bound u (G.edge_active E).2
      omega
  | succ i ih =>
    intro v h hv
    by_cases eq : v=G.terminal (G.owner v)
    · exact ⟨[], eq ▸ Route.nil v⟩
    · obtain ⟨u,E⟩ := G.succ v hv eq
      have k := G.edge_rank E
      have b := G.rank_bound u (G.edge_active E).2
      obtain ⟨L,R⟩ := ih u (by omega) (G.edge_active E).2
      rw [←G.edge_owner E] at R
      exact ⟨v::L,.cons E R⟩

private theorem unique_at {u z : V} {L W : List V}
    (A : Route G u L z) (B : Route G u W z)
    (halt : ∀ v, ¬ G.edge z v) : L=W := by
  induction A generalizing W with
  | nil =>
    cases B with
    | nil => rfl
    | cons F _ => exact (halt _ F).elim
  | cons E Q ih =>
    cases B with
    | nil => exact (halt _ E).elim
    | cons F S =>
      have eq := G.succ_unique E F
      cases eq
      rw [ih S halt]

private theorem unique_to (o : O) {u : V} {L W : List V}
    (A : Route G u L (G.terminal o)) (B : Route G u W (G.terminal o)) : L=W :=
  unique_at A B (fun _ F => G.no_terminal_exit F (by rw [G.terminal_owner]))

/-- The source-to-terminal departure list is unique and contains all
active addresses of the same owner, with terminal appended. -/
theorem owner_chain (G : Rail V O) (o : O) :
    ∃ L : List V, Route G (G.root o) L (G.terminal o) ∧
      (∀ W, Route G (G.root o) W (G.terminal o) → W=L) ∧
      ∀ v, G.active v → G.owner v=o → v∈L++[G.terminal o] := by
  obtain ⟨L,P⟩ := to_terminal G (G.root o) (G.root_active o)
  rw [G.root_owner] at P
  refine ⟨L,P,fun _ Q => unique_to o Q P,?_⟩
  intro v hv own
  obtain ⟨A,F⟩ := from_root G v hv
  obtain ⟨B,R⟩ := to_terminal G v hv
  rw [own] at F R
  have eq := unique_to o (F.append R) P
  rw [←eq]
  exact F.contains_at_join R

end L4.BStarAcquireGlobalChain
