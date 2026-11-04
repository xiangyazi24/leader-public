import Leader.Wu.Authorization.CheckSuffixPathFrame
import Leader.Wu.Authorization.SerialDischarge
import Leader.Wu.Authorization.HoleRouting

set_option autoImplicit false

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthGenDrain PPLLAuthSeam

/-! The exact stale-escape input belongs to the physical hole sector. -/

/-- Every site of the three-cell ring is one of the three named cells. -/
private theorem staleEscape_fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hi with h | h | h
  · left
    apply Fin.ext
    simpa using h
  · right; left
    apply Fin.ext
    simpa using h
  · right; right
    apply Fin.ext
    simpa using h

/-- The fully specified initial configuration lies in the zero-leader hole
sector.  The sole hole is physical role two. -/
theorem staleEscape_sector :
    HoleSectorE 0 staleEscapeRing staleEscapeConfig := by
  refine {
    ll := ?_, rf := ?_, lbf := ?_, pl := ?_, domain := ?_,
    noProduce := ?_, noDone := ?_, headsOccupied := ?_,
    holeExists := ?_ }
  · intro i
    rcases staleEscape_fin3 i with h | h | h <;>
      subst i <;>
      simp [staleEscapeConfig, staleEscapeLeft, staleEscapeRight, staleEscapeBase]
  · intro i
    rcases staleEscape_fin3 i with h | h | h <;>
      subst i <;>
      simp [staleEscapeConfig, staleEscapeLeft, staleEscapeRight, staleEscapeBase]
  · constructor
    · intro i
      rcases staleEscape_fin3 i with h | h | h <;>
        subst i <;>
        simp [PPLLAuthBitFrozen.NIc, staleEscapeConfig,
          staleEscapeLeft, staleEscapeRight, staleEscapeBase]
    · intro t ht
      left
      intro p hp
      rcases staleEscape_fin3 t with h | h | h <;>
        subst t <;>
        simp [staleEscapeConfig, staleEscapeLeft, staleEscapeRight,
          staleEscapeBase] at hp
  · intro i
    rcases staleEscape_fin3 i with h | h | h <;>
      subst i <;>
      simp [staleEscapeConfig, staleEscapeLeft, staleEscapeRight, staleEscapeBase]
  · intro i
    rcases staleEscape_fin3 i with h | h | h <;>
      subst i <;>
      simp [AgentState.inProtocolDomain, staleEscapeConfig,
        staleEscapeLeft, staleEscapeRight, staleEscapeBase]
  · intro i
    rcases staleEscape_fin3 i with h | h | h <;>
      subst i <;>
      simp [staleEscapeConfig, staleEscapeLeft, staleEscapeRight, staleEscapeBase]
  · intro i
    rcases staleEscape_fin3 i with h | h | h <;>
      subst i <;>
      simp [staleEscapeConfig, staleEscapeLeft, staleEscapeRight, staleEscapeBase]
  · intro i hi
    have h0 : i = (0 : Fin 3) := by
      apply Fin.ext
      have hv : i.val < 3 := i.isLt
      have hm : i.val % 3 = 0 := hi
      omega
    subst i
    simp [staleEscapeConfig, staleEscapeBase]
  · refine ⟨2, ?_⟩
    simp [staleEscapeConfig, staleEscapeRight, staleEscapeBase]

/-- In the concrete configuration, role two is a hole. -/
theorem staleEscape_hole_role_two :
    HoleAtRoleE staleEscapeRing staleEscapeConfig 2 := by
  refine ⟨by omega, 0, by omega, ?_⟩
  simp [bcell, staleEscapeRing, staleEscapeConfig,
    staleEscapeRight, staleEscapeBase]

/-- The bounded minimum is role two: its lower roles are occupied. -/
theorem staleEscape_HE : HE staleEscapeRing staleEscapeConfig = 2 := by
  have hle : HE staleEscapeRing staleEscapeConfig ≤ 2 :=
    HE_le staleEscapeRing staleEscapeConfig staleEscape_hole_role_two
  have hpos : 0 < HE staleEscapeRing staleEscapeConfig :=
    (staleEscape_sector.minimum_hole_geometry (by omega)).1
  have hnotone : HE staleEscapeRing staleEscapeConfig ≠ 1 := by
    intro he
    obtain ⟨hk, g, hg, hh⟩ :=
      HE_spec staleEscapeRing staleEscapeConfig
        (holeAtRoleE_exists (by omega) staleEscapeRing
          staleEscapeConfig staleEscape_sector.holeExists)
    have hg0 : g = 0 := by omega
    subst g
    rw [he] at hh
    simp [bcell, staleEscapeRing, staleEscapeConfig,
      staleEscapeLeft, staleEscapeBase] at hh
  omega

/-- The three main paths are occupied exactly at roles zero and one. -/
theorem staleEscape_Npath : NpathE staleEscapeConfig = 2 := by
  rfl

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.staleEscape_sector
#print axioms PPLLAuthHoleRouting.staleEscape_HE
#print axioms PPLLAuthHoleRouting.staleEscape_Npath

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthGenDrain PPLLAuthSeam

/-- The actual global protocol successor serving physical edge one. -/
def staleEscapeNext : Fin 3 → AuthState 3 × Fin 3 :=
  (seamProtocolE (by omega : 3 > 0) 0 sVplusE).step
    staleEscapeRing staleEscapeConfig 1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The global step uses precisely the accepted two-cell replay row. -/
private theorem staleEscapeNext_left :
    staleEscapeNext 1 = (staleEscapeRow.1.1, staleEscapeRow.2.1) := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The right endpoint of the same global interaction. -/
private theorem staleEscapeNext_right :
    staleEscapeNext 2 = (staleEscapeRow.1.2, staleEscapeRow.2.2) := by
  rfl

/-- The unrelated physical head is unchanged by the edge-one step. -/
private theorem staleEscapeNext_head :
    staleEscapeNext 0 = staleEscapeConfig 0 := by
  rfl

/-- The accepted row replay, transported to the actual global configuration,
keeps the sender occupied, the receiver empty, and both leaders false. -/
theorem staleEscapeNext_endpoint :
    (staleEscapeNext 1).1.core.path = .some 0 0 ∧
    (staleEscapeNext 1).1.core.state = .depart ∧
    (staleEscapeNext 1).1.core.leader = false ∧
    (staleEscapeNext 2).1.core.path = .bot ∧
    (staleEscapeNext 2).1.core.leader = false := by
  rw [staleEscapeNext_left, staleEscapeNext_right]
  simpa only [staleEscapeEndpoint, Prod.mk.injEq] using
    staleEscape_endpoint_replay

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The physical role of the surviving hole is still two after the genuine
global row.  The bounded search is handled through its specification. -/
theorem staleEscapeNext_HE : HE staleEscapeRing staleEscapeNext = 2 := by
  obtain ⟨hp1, _, _, hp2, _⟩ := staleEscapeNext_endpoint
  have hp0 : (staleEscapeNext 0).1.core.path = .some 0 0 := by
    rw [staleEscapeNext_head]
    rfl
  have htwo : HoleAtRoleE staleEscapeRing staleEscapeNext 2 := by
    refine ⟨by omega, 0, by omega, ?_⟩
    simpa [bcell, staleEscapeRing] using hp2
  have hle : HE staleEscapeRing staleEscapeNext ≤ 2 :=
    HE_le staleEscapeRing staleEscapeNext htwo
  obtain ⟨_, g, hg, hh⟩ :=
    HE_spec staleEscapeRing staleEscapeNext ⟨2, htwo⟩
  have hg0 : g = 0 := by omega
  subst g
  by_cases heq : HE staleEscapeRing staleEscapeNext = 2
  · exact heq
  exfalso
  have halt : HE staleEscapeRing staleEscapeNext = 0 ∨
      HE staleEscapeRing staleEscapeNext = 1 := by omega
  rcases halt with hzero | hone
  · rw [hzero] at hh
    have hhole : (staleEscapeNext 0).1.core.path = .bot := by
      simpa [bcell, staleEscapeRing] using hh
    rw [hp0] at hhole
    cases hhole
  · rw [hone] at hh
    have hhole : (staleEscapeNext 1).1.core.path = .bot := by
      simpa [bcell, staleEscapeRing] using hh
    rw [hp1] at hhole
    cases hhole

/-- Finite unfolding of the three-cell path count, independent of the
configuration's contents. -/
private theorem staleEscape_NpathE_three
    (C : Fin 3 → AuthState 3 × Fin 3) :
    NpathE C =
      (if (C 0).1.core.path = .bot then 0 else 1) +
      ((if (C 1).1.core.path = .bot then 0 else 1) +
       ((if (C 2).1.core.path = .bot then 0 else 1) + 0)) := by
  rfl

/-- This genuine one-row successor still has two occupied main paths and no
leader at any of its three sites. -/
theorem staleEscapeNext_mass_and_leaders :
    NpathE staleEscapeNext = 2 ∧
    HE staleEscapeRing staleEscapeNext = 2 ∧
    (∀ i : Fin 3, (staleEscapeNext i).1.core.leader = false) := by
  obtain ⟨hp1, _, hl1, hp2, hl2⟩ := staleEscapeNext_endpoint
  have hp0 : (staleEscapeNext 0).1.core.path = .some 0 0 := by
    rw [staleEscapeNext_head]
    rfl
  have hl0 : (staleEscapeNext 0).1.core.leader = false := by
    rw [staleEscapeNext_head]
    rfl
  refine ⟨?_, staleEscapeNext_HE, ?_⟩
  · rw [staleEscape_NpathE_three]
    simp [hp0, hp1, hp2]
  · intro i
    rcases staleEscape_fin3 i with h | h | h
    · simpa [h] using hl0
    · simpa [h] using hl1
    · simpa [h] using hl2

#print axioms PPLLAuthHoleRouting.staleEscapeNext_endpoint
#print axioms PPLLAuthHoleRouting.staleEscapeNext_HE
#print axioms PPLLAuthHoleRouting.staleEscapeNext_mass_and_leaders

end PPLLAuthHoleRouting

set_option autoImplicit false

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthGenDrain PPLLAuthSeam

/-- The main-path occupancy of a single cell; episode counters are irrelevant. -/
def pathMass {ψ : Nat} (u : AuthState ψ) : Nat :=
  if u.core.path = .bot then 0 else 1

/-- Occupancy of the two interacting cells. -/
def pairPathMass {ψ : Nat} (q : AuthState ψ × AuthState ψ) : Nat :=
  pathMass q.1 + pathMass q.2

/-- Step1 transfers one existing path or does nothing, for arbitrary raw inputs. -/
theorem step1Auth_pairPathMass {ψ : Nat} (l r : AuthState ψ) :
    pairPathMass (step1Auth l r) = pairPathMass (l, r) := by
  cases hl : l.core.path <;> cases hr : r.core.path <;>
    simp only [step1Auth, hl, hr]
  all_goals repeat split
  all_goals simp_all [pairPathMass, pathMass]

/-- Replacing a main path by a vacancy never raises single-cell occupancy. -/
theorem pathMass_le_of_eq_or_bot {ψ : Nat} (u v : AuthState ψ)
    (h : v.core.path = u.core.path ∨ v.core.path = .bot) :
    pathMass v ≤ pathMass u := by
  rcases h with h | h
  · simp [pathMass, h]
  · simp [pathMass, h]

private theorem sum_ofFn_congr_local : ∀ {m : Nat} (f g : Fin m → Nat),
    (∀ i, f i = g i) → (List.ofFn f).sum = (List.ofFn g).sum := by
  intro m
  induction m with
  | zero => intros; simp
  | succ m ih =>
    intro f g h
    rw [List.ofFn_succ, List.ofFn_succ, List.sum_cons, List.sum_cons,
      h 0, ih (fun j => f j.succ) (fun j => g j.succ) (fun j => h j.succ)]

/-- Exact additive accounting for a change at a single index; no subtraction. -/
theorem path_sum_swap_single : ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
    (∀ j, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i = (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero => intro f g i _; exact Fin.elim0 i
  | succ m ih =>
    intro f g i h
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht : (List.ofFn (fun j : Fin m => f j.succ)).sum =
          (List.ofFn (fun j : Fin m => g j.succ)).sum := by
        apply sum_ofFn_congr_local
        intro j
        apply h
        intro hz
        have hv := congrArg Fin.val hz
        simp at hv
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
        omega
      let j : Fin m := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun a : Fin m => f a.succ) (fun a : Fin m => g a.succ) j (by
        intro a ha
        apply h
        intro hz
        apply ha
        apply Fin.ext
        have hv := congrArg Fin.val hz
        have hv' := congrArg Fin.val hj
        simp at hv hv' ⊢
        omega)
      have h0 := h 0 (fun hz => hi hz.symm)
      simp only [hj] at ht
      omega

/-- Exact two-index accounting, valid even when one local occupancy increases
by receiving a path from the other endpoint. -/
theorem path_sum_swap_pair {m : Nat} (f g : Fin m → Nat) (i j : Fin m)
    (hij : i ≠ j) (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (List.ofFn f).sum + g i + g j = (List.ofFn g).sum + f i + f j := by
  let mid : Fin m → Nat := fun k => if k = i then g k else f k
  have hfirst := path_sum_swap_single f mid i (by
    intro k hk
    simp [mid, hk])
  have hsecond := path_sum_swap_single mid g j (by
    intro k hkj
    by_cases hki : k = i
    · simp [mid, hki]
    · simp [mid, hki, hrest k hki hkj])
  have hji : j ≠ i := Ne.symm hij
  simp only [mid, if_pos rfl, if_neg hji] at hfirst hsecond
  omega

/-- A pair inequality and exact stuttering elsewhere imply the global sum
inequality. The pair inequality remains an explicit, separate obligation. -/
theorem path_sum_pair_nonincrease {m : Nat} (f g : Fin m → Nat) (i j : Fin m)
    (hij : i ≠ j) (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k)
    (hpair : g i + g j ≤ f i + f j) :
    (List.ofFn g).sum ≤ (List.ofFn f).sum := by
  have h := path_sum_swap_pair f g i j hij hrest
  omega

/-- Lift a supplied completed-row pair inequality to NpathE for the actual
scheduling operation. This is supporting arithmetic, not Lemma 2: proving
hpair from HoleSectorE is still required. Distinct endpoints are essential. -/
theorem seam_step_NpathE_of_pair {n ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : SeamCfg) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AuthState ψ × Fin 3) (e : Fin n)
    (hpair : pairPathMass (seamStepE hp κ c (C e).1
      (C (ring.rightNeighbor e)).1 (C e).2 (C (ring.rightNeighbor e)).2).1 ≤
        pathMass (C e).1 + pathMass (C (ring.rightNeighbor e)).1) :
    NpathE ((seamProtocolE hp κ c).step ring C e) ≤ NpathE C := by
  let D := (seamProtocolE hp κ c).step ring C e
  have hne : e ≠ ring.rightNeighbor e := Ne.symm (bneighbor_ne ring hn e)
  change (List.ofFn (fun k => pathMass (D k).1)).sum ≤
    (List.ofFn (fun k => pathMass (C k).1)).sum
  apply path_sum_pair_nonincrease (fun k => pathMass (C k).1)
    (fun k => pathMass (D k).1) e (ring.rightNeighbor e) hne
  · intro k hki hkj
    simp only [D, PopulationProtocol.step, if_neg hki, if_neg hkj]
  · simpa only [D, PopulationProtocol.step, seamProtocolE, pairPathMass,
      if_pos rfl, if_neg (Ne.symm hne), ite_true]
      using hpair

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.step1Auth_pairPathMass
#print axioms PPLLAuthHoleRouting.path_sum_swap_pair
#print axioms PPLLAuthHoleRouting.seam_step_NpathE_of_pair
#print axioms PPLLAuthHoleRouting.pathMass_le_of_eq_or_bot
#print axioms PPLLAuthHoleRouting.path_sum_swap_single
#print axioms PPLLAuthHoleRouting.path_sum_pair_nonincrease

/-! ## Hole-routing Lemma 2: the P′ cut

Append after the current `PPLLAuthHoleRouting` declarations.  On a correctly
labelled leaderless edge, P′ changes only probe bits, so neither main-path
occupancy nor generation state changes before WAIT/GENSIG. -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthGenDrain PPLLAuthBitFrozen

/-- Perfect labelling turns a zero-label cell into a physical head; the
occupied-head premise then blocks GENSIG's head-start guard. -/
theorem PL_occupied_zero_label {n ψ : Nat} (hp : ψ > 0)
    (C : Fin n → AuthState ψ × Fin 3)
    (hpl : PL (fun i => (C i).1))
    (heads : ∀ i, i.val % ψ = 0 → (C i).1.core.path ≠ .bot)
    (i : Fin n) :
    (C i).1.core.label = (⟨0, hp⟩ : Fin ψ) →
      (C i).1.core.path ≠ .bot := by
  intro hz
  apply heads i
  have hv := hpl i
  have hzero : (C i).1.core.label.val = 0 := congrArg Fin.val hz
  exact hv.symm.trans hzero

/-- Under `ψ ∣ n`, physical successors have consecutive logical labels even
across the last-to-first wraparound edge. -/
theorem PL_adjacent_labels {n ψ : Nat} (hd : ψ ∣ n)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ × Fin 3)
    (hpl : PL (fun i => (C i).1)) (e : Fin n) :
    (C (ring.rightNeighbor e)).1.core.label.val =
      ((C e).1.core.label.val + 1) % ψ := by
  rw [hpl (ring.rightNeighbor e), hpl e]
  exact succ_mod_of_dvd hd e.val

/-- P′ on an adjacent follower pair only moves probes.  The pair equation
frames labels, main paths, states, and leader flags at once. -/
theorem pPsiProbeWall_followers_frame {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hlab : r.core.label.val = (l.core.label.val + 1) % ψ) :
    ∃ x y : Bool,
      lift2 (PPLLPostElectionGuard.pPsiProbeWall hp) l r =
        ({ l with core := { l.core with probe := x } },
         { r with core := { r.core with probe := y } }) := by
  exact P0_frame hp l r hl hr hlab

/-- The pair equation applies to every served physical edge of a perfectly
labelled leaderless ring. -/
theorem pPsiProbeWall_ring_frame {n ψ : Nat} (hp : ψ > 0)
    (hd : ψ ∣ n) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3)
    (hpl : PL (fun i => (C i).1))
    (hll : ∀ i, (C i).1.core.leader = false)
    (e : Fin n) :
    ∃ x y : Bool,
      lift2 (PPLLPostElectionGuard.pPsiProbeWall hp)
        (C e).1 (C (ring.rightNeighbor e)).1 =
        ({ (C e).1 with core := { (C e).1.core with probe := x } },
         { (C (ring.rightNeighbor e)).1 with
           core := { (C (ring.rightNeighbor e)).1.core with probe := y } }) := by
  exact pPsiProbeWall_followers_frame hp _ _
    (hll e) (hll (ring.rightNeighbor e))
    (PL_adjacent_labels hd ring C hpl e)

/-- Probe updates preserve the exact number of occupied main paths. -/
theorem pPsiProbeWall_pairPathMass {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hlab : r.core.label.val = (l.core.label.val + 1) % ψ) :
    pairPathMass (lift2 (PPLLPostElectionGuard.pPsiProbeWall hp) l r) =
      pairPathMass (l, r) := by
  obtain ⟨x, y, h⟩ := pPsiProbeWall_followers_frame hp l r hl hr hlab
  rw [h]
  rfl

/-- The P′ occupancy frame in the ring coordinates used by Lemma 2. -/
theorem pPsiProbeWall_ring_pairPathMass {n ψ : Nat} (hp : ψ > 0)
    (hd : ψ ∣ n) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3)
    (hpl : PL (fun i => (C i).1))
    (hll : ∀ i, (C i).1.core.leader = false)
    (e : Fin n) :
    pairPathMass (lift2 (PPLLPostElectionGuard.pPsiProbeWall hp)
      (C e).1 (C (ring.rightNeighbor e)).1) =
      pairPathMass ((C e).1, (C (ring.rightNeighbor e)).1) :=
  pPsiProbeWall_pairPathMass hp _ _ (hll e) (hll (ring.rightNeighbor e))
    (PL_adjacent_labels hd ring C hpl e)

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.PL_occupied_zero_label
#print axioms PPLLAuthHoleRouting.PL_adjacent_labels
#print axioms PPLLAuthHoleRouting.pPsiProbeWall_followers_frame
#print axioms PPLLAuthHoleRouting.pPsiProbeWall_ring_frame
#print axioms PPLLAuthHoleRouting.pPsiProbeWall_pairPathMass
#print axioms PPLLAuthHoleRouting.pPsiProbeWall_ring_pairPathMass

/-! ## Hole-routing Lemma 2: WAIT/GENSIG cut

Append after the P′ increment.  GENSIG is factored through the imported
`gs_reduce`; WAIT is used only through its proved field frame.  The occupied
zero-label condition refers to the actual GENSIG input after P′. -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthGenDrain

/-- Every writing guard in the five-map GENSIG body is false on a
generation-free pair whose zero-label initiator already has a main path.
The result is body identity, including all ancillary fields. -/
private theorem gsBody_idle {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ)
    (hhead : l.core.label = (⟨0, hp⟩ : Fin ψ) → l.core.path ≠ .bot)
    (hlp : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrp : r.core.state ≠ .produce) :
    gsBody hp l r = (l, r) := by
  have hH : gsH hp l r = l := by
    unfold gsH
    split
    · rename_i h
      exact False.elim ((hhead h.2.1) h.2.2.2)
    · rfl
  have hR : gsR hp l r = r := by
    unfold gsR
    split
    · rename_i h
      exact False.elim (hlp (by simpa only [AuthState.st] using h.2.1))
    · rfl
  have hE : gsE hp r = r := by
    unfold gsE
    split
    · rename_i h
      exact False.elim (hrp (by simpa only [AuthState.st] using h.2))
    · rfl
  have hPair : gsPair hp l r = (l, r) := by
    unfold gsPair
    split
    · rename_i h
      exact False.elim (hlp (by simpa only [AuthState.st] using h.2.1))
    · rfl
  have hF : gsF hp l = l := by
    unfold gsF
    split
    · rename_i h
      exact False.elim (hld (by simpa only [AuthState.st] using h.2))
    · rfl
  simp only [gsBody, hH, hR, hE, hPair, hF]

/-- The actual `genSigAuth` call retains both main paths and keeps both
endpoints outside `produce`/`done`.  WAIT's field agreements come from
`gs_reduce`/`W_fields`; no WAIT implementation is unfolded here. -/
theorem genSigAuth_no_birth_at_occupied_head {ψ : Nat} (hp : ψ > 0)
    (κ : Nat) (l r : AuthState ψ)
    (hhead : l.core.label = (⟨0, hp⟩ : Fin ψ) → l.core.path ≠ .bot)
    (hlp : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrp : r.core.state ≠ .produce) (hrd : r.core.state ≠ .done) :
    (genSigAuth hp κ l r).1.core.path = l.core.path ∧
    (genSigAuth hp κ l r).2.core.path = r.core.path ∧
    (genSigAuth hp κ l r).1.core.state ≠ .produce ∧
    (genSigAuth hp κ l r).1.core.state ≠ .done ∧
    (genSigAuth hp κ l r).2.core.state ≠ .produce ∧
    (genSigAuth hp κ l r).2.core.state ≠ .done := by
  apply gs_reduce hp κ l r (fun q =>
    q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path ∧
    q.1.core.state ≠ .produce ∧ q.1.core.state ≠ .done ∧
    q.2.core.state ≠ .produce ∧ q.2.core.state ≠ .done)
  intro l1 r1 hls hlpath _ hlabel _ _ _ hrs hrpath _ _ _ _ _
  have hhead1 : l1.core.label = (⟨0, hp⟩ : Fin ψ) → l1.core.path ≠ .bot := by
    intro hz
    rw [hlpath]
    apply hhead
    rw [← hlabel]
    exact hz
  have hlp1 : l1.core.state ≠ .produce := by rw [hls]; exact hlp
  have hld1 : l1.core.state ≠ .done := by rw [hls]; exact hld
  have hrp1 : r1.core.state ≠ .produce := by rw [hrs]; exact hrp
  have hrd1 : r1.core.state ≠ .done := by rw [hrs]; exact hrd
  rw [gsBody_idle hp l1 r1 hhead1 hlp1 hld1 hrp1]
  exact ⟨hlpath, hrpath, hlp1, hld1, hrp1, hrd1⟩

/-- Exact pair occupancy through GENSIG under the post-P′ head guard and
generation-free input states. -/
theorem row_genSig_mass {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ)
    (hhead : l.core.label = (⟨0, hp⟩ : Fin ψ) → l.core.path ≠ .bot)
    (hlp : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrp : r.core.state ≠ .produce) (hrd : r.core.state ≠ .done) :
    pairPathMass (genSigAuth hp κ l r) = pairPathMass (l, r) := by
  have h := genSigAuth_no_birth_at_occupied_head hp κ l r hhead hlp hld hrp hrd
  simp [pairPathMass, pathMass, h.1, h.2.1]

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.genSigAuth_no_birth_at_occupied_head
#print axioms PPLLAuthHoleRouting.row_genSig_mass

/-! ## Hole-routing Lemma 2: hygiene and single-cell CLEAN application

Append after the GENSIG increment.  Hygiene never writes a main path.  The
seam command-target guard can clear records before `cleanApplyAuth`, but these
record edits frame both path and state.  The full pair CLEAN prefix follows in
a separate increment. -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthSeam PPLLAuthGenDrain

/-- Hygiene scrubs ancillary records on occupied and empty cells without
changing the main path. -/
theorem hygieneOne_path {ψ : Nat} (c : SeamCfg) (u : AuthState ψ) :
    (hygieneOne c u).core.path = u.core.path := by
  unfold hygieneOne occHygiene emptyHygiene
  repeat split
  all_goals repeat split
  all_goals simp_all (maxSteps := 4000000)

/-- The actual `sVplusE` hygiene pair preserves main-path occupancy exactly. -/
theorem hygiene_pairPathMass {ψ : Nat} (l r : AuthState ψ) :
    pairPathMass (hygieneOne sVplusE l, hygieneOne sVplusE r) =
      pairPathMass (l, r) := by
  simp [pairPathMass, pathMass, hygieneOne_path]

/-- Clearing the local path4 record changes neither the main path nor the
lifecycle state read by the CLEAN occupancy argument. -/
private theorem clearPath4_frame {ψ : Nat} (u : AuthState ψ) :
    ({ u with core := { u.core with path4 := none } }).core.path = u.core.path ∧
    ({ u with core := { u.core with path4 := none } }).core.state = u.core.state :=
  ⟨rfl, rfl⟩

/-- The analogous metadata frame for the path5 record. -/
private theorem clearPath5_frame {ψ : Nat} (u : AuthState ψ) :
    ({ u with core := { u.core with path5 := none } }).core.path = u.core.path ∧
    ({ u with core := { u.core with path5 := none } }).core.state = u.core.state :=
  ⟨rfl, rfl⟩

/-- The imported CLEAN view lemma gives the state projection as well as
retention-or-deletion of the main path. -/
private theorem cleanApplyAuth_path_state {ψ : Nat} (u : AuthState ψ) :
    ((cleanApplyAuth u).core.path = u.core.path ∨
      (cleanApplyAuth u).core.path = .bot) ∧
    (cleanApplyAuth u).core.state = u.core.state := by
  have hc := cleanApply_cv u
  have hs := congrArg Prod.fst hc.1
  exact ⟨hc.2, hs⟩

/-- The actual seam command-target guard only clears path4/path5 metadata.
Its final `cleanApplyAuth` may erase a main path but cannot create one, and
neither operation changes the lifecycle state. -/
theorem cleanApplyS_path_state {ψ : Nat} (c : SeamCfg) (u : AuthState ψ) :
    ((cleanApplyS c u).core.path = u.core.path ∨
      (cleanApplyS c u).core.path = .bot) ∧
    (cleanApplyS c u).core.state = u.core.state := by
  unfold cleanApplyS
  split
  · exact cleanApplyAuth_path_state u
  · cases hpath : u.core.path with
    | bot =>
        simp [hpath]
    | some pl bit =>
        let u4 : AuthState ψ :=
          if pl == ψ - 1 && isCmd u.core.path4 then
            { u with core := { u.core with path4 := none } } else u
        let u5 : AuthState ψ :=
          if pl == 0 && isCmd u4.core.path5 then
            { u4 with core := { u4.core with path5 := none } } else u4
        have h4 : u4.core.path = u.core.path ∧
            u4.core.state = u.core.state := by
          dsimp [u4]
          split
          · exact clearPath4_frame u
          · exact ⟨rfl, rfl⟩
        have h5 : u5.core.path = u4.core.path ∧
            u5.core.state = u4.core.state := by
          dsimp [u5]
          split
          · exact clearPath5_frame u4
          · exact ⟨rfl, rfl⟩
        have hc := cleanApplyAuth_path_state u5
        change ((cleanApplyAuth u5).core.path = .some pl bit ∨
          (cleanApplyAuth u5).core.path = .bot) ∧
          (cleanApplyAuth u5).core.state = u.core.state
        refine ⟨?_, hc.2.trans (h5.2.trans h4.2)⟩
        rcases hc.1 with hp | hp
        · exact Or.inl (hp.trans (h5.1.trans (h4.1.trans hpath)))
        · exact Or.inr hp

#print axioms PPLLAuthHoleRouting.hygieneOne_path
#print axioms PPLLAuthHoleRouting.hygiene_pairPathMass
#print axioms PPLLAuthHoleRouting.cleanApplyS_path_state

end PPLLAuthHoleRouting

/-! ## Hole-routing Lemma 2: actual seam CLEAN prefix

Append after the hygiene/cleanApplyS increment.  The prefix follows
`seamCleanSourceAuth`'s source order; its record propagation frames both main
paths.  The final command applications can only retain or erase them. -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthSeam PPLLAuthGenDrain

/-- Seam fencing changes path4/path5 records only. -/
private theorem seamFenceS_paths {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) :
    (seamFenceS c l r).1.core.path = l.core.path ∧
    (seamFenceS c l r).2.core.path = r.core.path := by
  unfold seamFenceS
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

/-- The five record-propagation cuts before `cleanApplyS`, with exactly the
same order and command bypasses as the actual seam CLEAN source. -/
private def cleanPrefix {ψ : Nat} (hp : ψ > 0) (c : SeamCfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := genConnectAuth l
  let r := genConnectAuth r
  let (l, r) := seamFenceS c l r
  let skip := c.sfNoGen && isSeam l r
  let (l, r) := if skip then (l, r) else step3Auth c.base.cleanNbr c.base.markClean l r
  let (l, r) := if skip then (l, r) else step4Auth c.base.cleanNbr c.base.markClean l r
  let (l, r) := if isCmd l.core.path4 then
    (l, { r with core := { r.core with path4 := none } }) else step5Auth hp l r
  let (l, r) := if isCmd r.core.path5 then
    ({ l with core := { l.core with path5 := none } }, r) else step6Auth hp l r
  (l, r)

/-- Every prefix cut preserves both main paths; the step3/4 seam skip and
step5/6 command bypasses are handled separately. -/
private theorem cleanPrefix_paths {ψ : Nat} (hp : ψ > 0) (c : SeamCfg)
    (l r : AuthState ψ) :
    (cleanPrefix hp c l r).1.core.path = l.core.path ∧
    (cleanPrefix hp c l r).2.core.path = r.core.path := by
  let q0 : AuthState ψ × AuthState ψ := (genConnectAuth l, genConnectAuth r)
  let q1 := seamFenceS c q0.1 q0.2
  let skip := c.sfNoGen && isSeam q1.1 q1.2
  let q2 := if skip then q1 else step3Auth c.base.cleanNbr c.base.markClean q1.1 q1.2
  let q3 := if skip then q2 else step4Auth c.base.cleanNbr c.base.markClean q2.1 q2.2
  let q4 := if isCmd q3.1.core.path4 then
    (q3.1, { q3.2 with core := { q3.2.core with path4 := none } })
    else step5Auth hp q3.1 q3.2
  let q5 := if isCmd q4.2.core.path5 then
    ({ q4.1 with core := { q4.1.core with path5 := none } }, q4.2)
    else step6Auth hp q4.1 q4.2
  have h0 : q0.1.core.path = l.core.path ∧ q0.2.core.path = r.core.path :=
    ⟨(genConnectAuth_cv l).2, (genConnectAuth_cv r).2⟩
  have h1 : q1.1.core.path = q0.1.core.path ∧
      q1.2.core.path = q0.2.core.path := seamFenceS_paths c q0.1 q0.2
  have h2 : q2.1.core.path = q1.1.core.path ∧
      q2.2.core.path = q1.2.core.path := by
    dsimp only [q2]
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨(step3_cv c.base.cleanNbr c.base.markClean q1.1 q1.2).2.2.1,
             (step3_cv c.base.cleanNbr c.base.markClean q1.1 q1.2).2.2.2⟩
  have h3 : q3.1.core.path = q2.1.core.path ∧
      q3.2.core.path = q2.2.core.path := by
    dsimp only [q3]
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨(step4_cv c.base.cleanNbr c.base.markClean q2.1 q2.2).2.2.1,
             (step4_cv c.base.cleanNbr c.base.markClean q2.1 q2.2).2.2.2⟩
  have h4 : q4.1.core.path = q3.1.core.path ∧
      q4.2.core.path = q3.2.core.path := by
    dsimp only [q4]
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨(step5_cv hp q3.1 q3.2).2.2.1,
             (step5_cv hp q3.1 q3.2).2.2.2⟩
  have h5 : q5.1.core.path = q4.1.core.path ∧
      q5.2.core.path = q4.2.core.path := by
    dsimp only [q5]
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨(step6_cv hp q4.1 q4.2).2.2.1,
             (step6_cv hp q4.1 q4.2).2.2.2⟩
  have hfactor : cleanPrefix hp c l r = q5 := by rfl
  rw [hfactor]
  exact ⟨h5.1.trans (h4.1.trans (h3.1.trans (h2.1.trans (h1.1.trans h0.1)))),
         h5.2.trans (h4.2.trans (h3.2.trans (h2.2.trans (h1.2.trans h0.2))))⟩

/-- The actual `sVplusE` CLEAN stage can only delete main paths.  Arbitrary
stale CLEAN records are admitted; the proof uses each source substage. -/
theorem row_clean_mass {ψ : Nat} (hp : ψ > 0) (l r : AuthState ψ) :
    pairPathMass (seamCleanSourceAuth hp sVplusE l r) ≤
      pairPathMass (l, r) := by
  let q := cleanPrefix hp sVplusE l r
  have hpre := cleanPrefix_paths hp sVplusE l r
  have hl := (cleanApplyS_path_state sVplusE q.1).1
  have hr := (cleanApplyS_path_state sVplusE q.2).1
  have hl' : (cleanApplyS sVplusE q.1).core.path = l.core.path ∨
      (cleanApplyS sVplusE q.1).core.path = .bot := by
    rcases hl with hl | hl
    · exact Or.inl (hl.trans hpre.1)
    · exact Or.inr hl
  have hr' : (cleanApplyS sVplusE q.2).core.path = r.core.path ∨
      (cleanApplyS sVplusE q.2).core.path = .bot := by
    rcases hr with hr | hr
    · exact Or.inl (hr.trans hpre.2)
    · exact Or.inr hr
  have hfactor : seamCleanSourceAuth hp sVplusE l r =
      (cleanApplyS sVplusE q.1, cleanApplyS sVplusE q.2) := by rfl
  rw [hfactor]
  exact Nat.add_le_add (pathMass_le_of_eq_or_bot l _ hl')
    (pathMass_le_of_eq_or_bot r _ hr')

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.row_clean_mass

/-! ## Hole-routing Lemma 2: RELEASE and ELIMINATE_SIG cuts -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAstraDesign3

/-- A `lift2Life` lifecycle update keeps the path of its supplied core.
Both sides of its depart-lineage condition use the same core. -/
private theorem lift2Life_fix_path {ψ : Nat} (u : AuthState ψ)
    (v : AgentState ψ) :
    (if v.state ≠ u.core.state ∧ v.state = MainState.depart then
      { u with core := v, ctrl_mark := u.path_mark }
     else { u with core := v }).core.path = v.path := by
  split
  · rfl
  · rfl

/-- RELEASE changes only the responder lifecycle state. -/
private theorem releaseSource_core_paths {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    (releaseSource hp l r).1.path = l.path ∧
    (releaseSource hp l r).2.path = r.path := by
  unfold releaseSource
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The source-release cut preserves both lifted main paths. -/
theorem row_release_path {ψ : Nat} (hp : ψ > 0) (l r : AuthState ψ) :
    (lift2Life (releaseSource hp) l r).1.core.path = l.core.path ∧
    (lift2Life (releaseSource hp) l r).2.core.path = r.core.path := by
  have h := releaseSource_core_paths hp l.core r.core
  simpa only [lift2Life, lift2Life_fix_path] using h

/-- RELEASE therefore preserves pair occupancy exactly. -/
theorem row_release_mass {ψ : Nat} (hp : ψ > 0) (l r : AuthState ψ) :
    pairPathMass (lift2Life (releaseSource hp) l r) = pairPathMass (l, r) := by
  have h := row_release_path hp l r
  simp [pairPathMass, pathMass, h.1, h.2]

/-- ELIMINATE_SIG either retains both paths or erases only the responder.
The initiator's possible state change does not affect occupancy. -/
theorem row_eliminate_paths {ψ : Nat} (hp : ψ > 0) (l r : AuthState ψ) :
    (lift2 (eliminateSig hp) l r).1.core.path = l.core.path ∧
    ((lift2 (eliminateSig hp) l r).2.core.path = r.core.path ∨
      (lift2 (eliminateSig hp) l r).2.core.path = .bot) := by
  unfold lift2 eliminateSig
  split
  · split
    · exact ⟨rfl, Or.inr rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩

/-- ELIMINATE_SIG weakly decreases pair occupancy. -/
theorem row_eliminate_mass {ψ : Nat} (hp : ψ > 0) (l r : AuthState ψ) :
    pairPathMass (lift2 (eliminateSig hp) l r) ≤ pairPathMass (l, r) := by
  have h := row_eliminate_paths hp l r
  have hl : pathMass (lift2 (eliminateSig hp) l r).1 = pathMass l := by
    simp [pathMass, h.1]
  unfold pairPathMass
  rw [hl]
  exact Nat.add_le_add_left
    (pathMass_le_of_eq_or_bot r (lift2 (eliminateSig hp) l r).2 h.2) _

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.row_release_path
#print axioms PPLLAuthHoleRouting.row_release_mass
#print axioms PPLLAuthHoleRouting.row_eliminate_paths
#print axioms PPLLAuthHoleRouting.row_eliminate_mass

/-! ## Hole-routing Lemma 2: MOVE entrance, through the cut before Step1 -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthSeam PPLLAuthChamp PPLLAuthGenDrain

/-- Comparison clearing vacates its holder's main path. -/
private theorem move_clear_path {ψ : Nat} (u : AuthState ψ) :
    (clearCmpAuth u).core.path = .bot := by
  simp [clearCmpAuth, PPLLPostElectionGuard.clearCmp]

/-- Path projection commutes with a conditional cell update. -/
private theorem move_authPath_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AuthState ψ) :
    (if p then a else b).core.path = if p then a.core.path else b.core.path := by
  split <;> rfl

/-- CHECK validation may demote lifecycle state or drop path2, but frames
both main paths. -/
private theorem move_validate_paths {ψ : Nat} (l r : AuthState ψ) :
    (validateCheck l r).1.core.path = l.core.path ∧
    (validateCheck l r).2.core.path = r.core.path := by
  simp only [validateCheck, demote, move_authPath_ite, ite_self, and_self]

/-- Holder validation changes only path2. -/
private theorem sanitizeP2_path {ψ : Nat} (u : AuthState ψ) :
    (sanitizeP2 u).core.path = u.core.path := by
  unfold sanitizeP2
  split
  · rfl
  · rfl

/-- The strict-scope extension either keeps the holder or drops path2. -/
private theorem strictScopeOne_path {ψ : Nat} (cc : ChampCfg)
    (u : AuthState ψ) :
    (strictScopeOne cc u).core.path = u.core.path := by
  unfold strictScopeOne
  split
  · rfl
  · cases h : u.core.path2 with
    | none => rfl
    | some t =>
        simp only [move_authPath_ite, AuthState.dropP2, ite_self]

/-- The actual champion sanitation composes the two path frames. -/
private theorem champSanitizeP2_path {ψ : Nat} (cc : ChampCfg)
    (u : AuthState ψ) :
    (champSanitizeP2 cc u).core.path = u.core.path := by
  unfold champSanitizeP2
  exact (strictScopeOne_path cc (sanitizeP2 u)).trans (sanitizeP2_path u)

/-- Exact MOVE entrance: leader-related clear, CHECK validation, and both
holder sanitizers; Step1 follows this cut in `seamMoveSourceAuth`. -/
private def movePrefix {ψ : Nat} (hp : ψ > 0) (c : SeamCfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩
  let l := if l.core.leader = true ∨
      (r.core.leader = true ∧ r.core.label ≠ nextLabel) then clearCmpAuth l else l
  let r := if r.core.leader = true then clearCmpAuth r else r
  let q := validateCheck l r
  (champSanitizeP2 (toChamp c) q.1, champSanitizeP2 (toChamp c) q.2)

/-- Before Step1, MOVE can only retain or erase each input main path.
Validation and sanitation frame the path after any leader clearing. -/
theorem movePrefix_pairPathMass {ψ : Nat} (hp : ψ > 0)
    (c : SeamCfg) (l r : AuthState ψ) :
    pairPathMass (movePrefix hp c l r) ≤ pairPathMass (l, r) := by
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩
  let a := if l.core.leader = true ∨
      (r.core.leader = true ∧ r.core.label ≠ nextLabel) then clearCmpAuth l else l
  let b := if r.core.leader = true then clearCmpAuth r else r
  let q := validateCheck a b
  have ha : a.core.path = l.core.path ∨ a.core.path = .bot := by
    dsimp only [a]
    split
    · exact Or.inr (move_clear_path l)
    · exact Or.inl rfl
  have hb : b.core.path = r.core.path ∨ b.core.path = .bot := by
    dsimp only [b]
    split
    · exact Or.inr (move_clear_path r)
    · exact Or.inl rfl
  have hv := move_validate_paths a b
  have hsa := champSanitizeP2_path (toChamp c) q.1
  have hsb := champSanitizeP2_path (toChamp c) q.2
  have hfactor : movePrefix hp c l r =
      (champSanitizeP2 (toChamp c) q.1,
       champSanitizeP2 (toChamp c) q.2) := by rfl
  rw [hfactor]
  have hleft : (champSanitizeP2 (toChamp c) q.1).core.path = l.core.path ∨
      (champSanitizeP2 (toChamp c) q.1).core.path = .bot := by
    rcases ha with ha | ha
    · exact Or.inl (hsa.trans (hv.1.trans ha))
    · exact Or.inr (hsa.trans (hv.1.trans ha))
  have hright : (champSanitizeP2 (toChamp c) q.2).core.path = r.core.path ∨
      (champSanitizeP2 (toChamp c) q.2).core.path = .bot := by
    rcases hb with hb | hb
    · exact Or.inl (hsb.trans (hv.2.trans hb))
    · exact Or.inr (hsb.trans (hv.2.trans hb))
  unfold pairPathMass
  exact Nat.add_le_add
    (pathMass_le_of_eq_or_bot l _ hleft)
    (pathMass_le_of_eq_or_bot r _ hright)

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.movePrefix_pairPathMass

/-! ## Hole-routing Lemma 2: MOVE between Step1 and token transfer -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthSeam PPLLFableDesignR1

/-- The done guard either bypasses Step1 or runs its already proved
one-path transfer.  Both branches conserve pair occupancy exactly. -/
theorem moveStep1_pairPathMass {ψ : Nat} (l r : AuthState ψ) :
    pairPathMass (if l.st = MainState.done then (l, r) else step1Auth l r) =
      pairPathMass (l, r) := by
  split
  · rfl
  · exact step1Auth_pairPathMass l r

/-- Lottery arrival scrub uses the original pre-Step1 paths to detect a
vacated sender; it only writes `p` and `p_carry` on the post-Step1 left cell. -/
private def lotteryArrival {ψ : Nat} (c : SeamCfg)
    (preL preR l : AuthState ψ) : AuthState ψ :=
  if c.lotteryScrub then
    match preL.core.path, preR.core.path, l.core.path with
    | .some _ _, .bot, .bot =>
        { l with core := { l.core with p := false, p_carry := false } }
    | _, _, _ => l
  else l

/-- All eight path-shape branches of lottery arrival retain the post-Step1
main path, independent of the scrub switch. -/
private theorem lotteryArrival_path {ψ : Nat} (c : SeamCfg)
    (preL preR l : AuthState ψ) :
    (lotteryArrival c preL preR l).core.path = l.core.path := by
  cases hs : c.lotteryScrub
  · simp [lotteryArrival, hs]
  · cases hpL : preL.core.path <;>
      cases hpR : preR.core.path <;>
      cases hl : l.core.path <;>
      simp [lotteryArrival, hs, hpL, hpR, hl]

/-- An A2 claim and the ensuing token drop leave the main path untouched. -/
private theorem claimA2_dropP2_path {ψ : Nat} (σ : ProvColor)
    (u : AuthState ψ) :
    ((claimA2 σ u).dropP2).core.path = u.core.path := by
  simp [claimA2, AuthState.dropP2]

/-- A2 preemption keeps its Boolean eligibility tests opaque; the only
writing branch is the claim/drop pair. -/
private def a2Guarded {ψ : Nat} (c : SeamCfg)
    (r l : AuthState ψ) : AuthState ψ :=
  if c.a2Preempt then
    let incoming2 : Bool := match r.core.path2 with
      | some t => r.path2_scope == .session && p2Valid r && t.action == 2 && canMoveL r.core t
      | none => false
    let linePre : Bool := l.hasPath && l.ctrl_mark == l.path_mark &&
      (l.st == MainState.depart || l.st == MainState.equal || l.st == MainState.less) &&
      (match l.core.path2 with
        | none => true
        | some t' => t'.action == 6 && l.path2_scope == .line && l.path2_mark == l.path_mark)
    if incoming2 && linePre then (claimA2 r.path2_mark l).dropP2 else l
  else l

/-- A2 preemption changes path2 and provenance, never the main path. -/
private theorem a2Guarded_path {ψ : Nat} (c : SeamCfg)
    (r l : AuthState ψ) :
    (a2Guarded c r l).core.path = l.core.path := by
  unfold a2Guarded
  split
  · let incoming2 : Bool := match r.core.path2 with
        | some t => r.path2_scope == .session && p2Valid r && t.action == 2 && canMoveL r.core t
        | none => false
    let linePre : Bool := l.hasPath && l.ctrl_mark == l.path_mark &&
      (l.st == MainState.depart || l.st == MainState.equal || l.st == MainState.less) &&
      (match l.core.path2 with
        | none => true
        | some t' => t'.action == 6 && l.path2_scope == .line && l.path2_mark == l.path_mark)
    change (if incoming2 && linePre then (claimA2 r.path2_mark l).dropP2 else l).core.path = l.core.path
    split
    · exact claimA2_dropP2_path r.path2_mark l
    · rfl
  · rfl

/-- Exact metadata portion of `seamMoveSourceAuth`, retaining the original
pre-Step1 pair for the lottery condition. -/
private def moveMiddle {ψ : Nat} (c : SeamCfg)
    (preL preR l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := lotteryArrival c preL preR l
  let l := a2Guarded c r l
  (l, r)

/-- Both metadata writes preserve pair occupancy after Step1. -/
theorem moveMiddle_pairPathMass {ψ : Nat} (c : SeamCfg)
    (preL preR l r : AuthState ψ) :
    pairPathMass (moveMiddle c preL preR l r) = pairPathMass (l, r) := by
  have hp : (moveMiddle c preL preR l r).1.core.path = l.core.path :=
    (a2Guarded_path c r (lotteryArrival c preL preR l)).trans
      (lotteryArrival_path c preL preR l)
  unfold pairPathMass
  rw [show pathMass (moveMiddle c preL preR l r).1 = pathMass l by
    simp [pathMass, hp]]
  rfl

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.moveStep1_pairPathMass
#print axioms PPLLAuthHoleRouting.moveMiddle_pairPathMass
/-! ## MOVE after token routing: clearing, control consumption and release -/
namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLBirthPatch

/-- A raw path projection commutes with conditional state/metadata writes. -/
private theorem tail_rawPath_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

/-- The MOVE leader wall retains or deletes each path independently. -/
theorem moveLeaderWall_paths {ψ : Nat} (l r : AuthState ψ) :
    ((leaderWallAuth l r).1.core.path = l.core.path ∨
      (leaderWallAuth l r).1.core.path = .bot) ∧
    ((leaderWallAuth l r).2.core.path = r.core.path ∨
      (leaderWallAuth l r).2.core.path = .bot) := by
  unfold leaderWallAuth
  dsimp only
  constructor
  · split
    · exact Or.inr (move_clear_path l)
    · exact Or.inl rfl
  · split
    · exact Or.inr (move_clear_path r)
    · exact Or.inl rfl

/-- Consequently the wall never raises the total occupancy of its pair. -/
theorem moveLeaderWall_pairPathMass {ψ : Nat} (l r : AuthState ψ) :
    pairPathMass (leaderWallAuth l r) ≤ pairPathMass (l, r) := by
  obtain ⟨hl, hr⟩ := moveLeaderWall_paths l r
  exact Nat.add_le_add (pathMass_le_of_eq_or_bot l _ hl)
    (pathMass_le_of_eq_or_bot r _ hr)

/-- Raw control consumption changes state and path2, never the main path. -/
private theorem tail_controlCore_path {ψ : Nat} (hp : ψ > 0)
    (u : AgentState ψ) :
    (sigMoveApplyControlConsume hp u).path = u.path := by
  cases h2 : u.path2 <;>
    simp only [sigMoveApplyControlConsume, h2, tail_rawPath_ite, ite_self]

/-- Ownership rejection only drops path2; accepted control consumption also
preserves the main path, including branches that update ctrl_mark. -/
theorem moveControl_path {ψ : Nat} (hp : ψ > 0) (u : AuthState ψ) :
    (applyControlAuth hp u).core.path = u.core.path := by
  cases h2 : u.core.path2 <;>
    simp only [applyControlAuth, h2, move_authPath_ite,
      AuthState.dropP2, tail_controlCore_path, ite_self]

/-- The final READY release of MOVE alters lifecycle/provenance only. -/
def moveFinalRelease {ψ : Nat} (c : SeamCfg) (l r : AuthState ψ) : AuthState ψ :=
  if r.st = .depart ∧ l.core.label.val < ψ - 1 ∧ l.st = .CHECK_ready ∧
      (!c.lineageRelease || r.path_mark == l.path_mark) then
    l.lineage .depart else l

/-- The final sender release retains its exact main path. -/
theorem moveFinalRelease_path {ψ : Nat} (c : SeamCfg) (l r : AuthState ψ) :
    (moveFinalRelease c l r).core.path = l.core.path := by
  unfold moveFinalRelease
  split <;> rfl

/-- Literal suffix of seamMoveSourceAuth after seamMoveTokensAuth returns.
The token stage is excluded: this cut starts at the leader wall. -/
def moveFinish {ψ : Nat} (hp : ψ > 0) (c : SeamCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let (l, r) := leaderWallAuth l r
  let l := applyControlAuth hp l
  let r := applyControlAuth hp r
  (moveFinalRelease c l r, r)

/-- After its leader wall, the MOVE suffix frames both main paths exactly. -/
theorem moveFinish_paths {ψ : Nat} (hp : ψ > 0) (c : SeamCfg)
    (l r : AuthState ψ) :
    (moveFinish hp c l r).1.core.path = (leaderWallAuth l r).1.core.path ∧
    (moveFinish hp c l r).2.core.path = (leaderWallAuth l r).2.core.path := by
  simp only [moveFinish, moveFinalRelease_path, moveControl_path, and_self]

/-- Control application and final release add no paths after the wall's
possible deletion. This proof is unconditional on token contents and state. -/
theorem moveFinish_pairPathMass {ψ : Nat} (hp : ψ > 0) (c : SeamCfg)
    (l r : AuthState ψ) :
    pairPathMass (moveFinish hp c l r) ≤ pairPathMass (l, r) := by
  obtain ⟨hl, hr⟩ := moveFinish_paths hp c l r
  have hf : pairPathMass (moveFinish hp c l r) =
      pairPathMass (leaderWallAuth l r) := by
    simp only [pairPathMass, pathMass, hl, hr]
  rw [hf]
  exact moveLeaderWall_pairPathMass l r

end PPLLAuthHoleRouting
#print axioms PPLLAuthHoleRouting.moveLeaderWall_pairPathMass
#print axioms PPLLAuthHoleRouting.moveControl_path
#print axioms PPLLAuthHoleRouting.moveFinalRelease_path
#print axioms PPLLAuthHoleRouting.moveFinish_pairPathMass
/-! ## Hole-routing Lemma 2: MOVE token transfer -/

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthSeam PPLLFableDesignR1

/-- Queueing changes only path2 and its provenance, even when a receiver
claims the destination. The entry decisions are parameters here. -/
private def moveTokenQueue {ψ : Nat} (eL eR : Entry)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path2, r.core.path2 with
  | some tl, some tr =>
    if canMoveR l.core tl ∧ canMoveL r.core tr then
      (receive eL r l (dec tr), receive eR l r (dec tl))
    else if canMoveR l.core tl ∧ rightward tr ∧ canMoveR r.core tr then
      (l.dropP2, r)
    else if canMoveL r.core tr ∧ leftward tl ∧ canMoveL l.core tl then
      (l, r.dropP2)
    else (l, r)
  | some tl, none =>
    if canMoveR l.core tl then (l.dropP2, receive eR l r (dec tl)) else (l, r)
  | none, some tr =>
    if canMoveL r.core tr then (receive eL r l (dec tr), r.dropP2) else (l, r)
  | none, none => (l, r)

private theorem moveToken_receive_path {ψ : Nat} (e : Entry)
    (src dst : AuthState ψ) (t : Path2Info) :
    (receive e src dst t).core.path = dst.core.path := by
  unfold receive
  dsimp only
  split <;> rfl

private theorem moveToken_drop_path {ψ : Nat} (u : AuthState ψ) :
    (u.dropP2).core.path = u.core.path := rfl

private theorem moveTokenQueue_paths {ψ : Nat} (eL eR : Entry)
    (l r : AuthState ψ) :
    (moveTokenQueue eL eR l r).1.core.path = l.core.path ∧
    (moveTokenQueue eL eR l r).2.core.path = r.core.path := by
  cases h1 : l.core.path2 <;> cases h2 : r.core.path2 <;>
    simp only [moveTokenQueue, h1, h2] <;>
    (repeat' (first | (dsimp only) | split)) <;>
    simp only [moveToken_receive_path, moveToken_drop_path, and_self]

/-- Rejecting a token before queueing cannot affect either main path. -/
private theorem moveTokenQueue_reject_paths {ψ : Nat} (eL eR : Entry)
    (l r : AuthState ψ) :
    (moveTokenQueue eL eR (if eR = .reject then l.dropP2 else l)
      (if eL = .reject then r.dropP2 else r)).1.core.path = l.core.path ∧
    (moveTokenQueue eL eR (if eR = .reject then l.dropP2 else l)
      (if eL = .reject then r.dropP2 else r)).2.core.path = r.core.path := by
  have hq := moveTokenQueue_paths eL eR
    (if eR = .reject then l.dropP2 else l)
    (if eL = .reject then r.dropP2 else r)
  simpa only [move_authPath_ite, moveToken_drop_path, ite_self] using hq

private def moveRetire4 {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) : Bool :=
  match l.core.path2 with
  | some tl => c.base.retire && tl.action == 4 && l.path2_scope == .line && p2Valid l &&
      canMoveR l.core tl && r.hasPath && l.path2_mark != r.path_mark
  | none => false

private def moveRetire2 {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) : Bool :=
  match r.core.path2 with
  | some tr => c.base.retire && tr.action == 2 && r.path2_scope == .session && p2Valid r &&
      canMoveL r.core tr && l.hasPath &&
      (waveState l.st || l.st == .CHECK_ready || l.st == .equal || l.st == .larger || l.st == .less) &&
      l.ctrl_mark != r.path2_mark && !claimable c.base.claimCheck l
  | none => false

/-- Factor the actual seam transfer at its sender-retirement and token-queue
cuts. The entry test is retained verbatim, with its seam configuration. -/
private def moveTokensFactored {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let failA4 := moveRetire4 c l r
  let failA2 := moveRetire2 c l r
  if failA4 || failA2 then
    ((if failA4 then clearCmpAuth l else l), (if failA2 then clearCmpAuth r else r))
  else
    let eR : Entry := match l.core.path2 with
      | some tl => if canMoveR l.core tl then entryS c l r tl else .ok
      | none => .ok
    let eL : Entry := match r.core.path2 with
      | some tr => if canMoveL r.core tr then entryS c r l tr else .ok
      | none => .ok
    moveTokenQueue eL eR
      (if eR = .reject then l.dropP2 else l)
      (if eL = .reject then r.dropP2 else r)

private theorem moveTokensFactored_eq {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) :
    seamMoveTokensAuth c l r = moveTokensFactored c l r := rfl

/-- In the genuine seam token substage, each endpoint retains its input main
path or loses it through sender retirement. Entry and queueing cannot create
main-path occupancy. -/
theorem seamMoveTokensAuth_paths {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) :
    ((seamMoveTokensAuth c l r).1.core.path = l.core.path ∨
      (seamMoveTokensAuth c l r).1.core.path = .bot) ∧
    ((seamMoveTokensAuth c l r).2.core.path = r.core.path ∨
      (seamMoveTokensAuth c l r).2.core.path = .bot) := by
  rw [moveTokensFactored_eq]
  unfold moveTokensFactored
  dsimp only
  generalize moveRetire4 c l r = b4
  generalize moveRetire2 c l r = b2
  by_cases hret : (b4 || b2) = true
  · rw [if_pos hret]
    constructor
    · change (if b4 then clearCmpAuth l else l).core.path = l.core.path ∨
        (if b4 then clearCmpAuth l else l).core.path = .bot
      cases b4 <;> simp [move_clear_path]
    · change (if b2 then clearCmpAuth r else r).core.path = r.core.path ∨
        (if b2 then clearCmpAuth r else r).core.path = .bot
      cases b2 <;> simp [move_clear_path]
  · rw [if_neg hret]
    exact ⟨Or.inl (moveTokenQueue_reject_paths _ _ l r).1,
      Or.inl (moveTokenQueue_reject_paths _ _ l r).2⟩

/-- Token transfer weakly decreases occupancy of the two actual MOVE cells. -/
theorem seamMoveTokensAuth_pairPathMass {ψ : Nat} (c : SeamCfg)
    (l r : AuthState ψ) :
    pairPathMass (seamMoveTokensAuth c l r) ≤ pairPathMass (l, r) := by
  have h := seamMoveTokensAuth_paths c l r
  unfold pairPathMass
  exact Nat.add_le_add
    (pathMass_le_of_eq_or_bot l _ h.1)
    (pathMass_le_of_eq_or_bot r _ h.2)

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.seamMoveTokensAuth_paths
#print axioms PPLLAuthHoleRouting.seamMoveTokensAuth_pairPathMass

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAstraDesign3 PPLLAstraDesign2 PPLLPostElectionGuard
/-
Append in namespace PPLLAuthHoleRouting, after pathMass and pairPathMass.
PPLLAuthGenDrain is already imported in the old proof file.
No duplicate definitions.
-/

variable {ψ : Nat}

/-- K4 retains both main paths, by the existing four-field kernel frame. -/
theorem suffix_k4_paths (hψ : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hψ l r).1.path = l.path ∧
    (k4Kernel hψ l r).2.path = r.path := by
  have hf := PPLLAuthGenDrain.WFrame.kernel_frame hψ l r
  exact ⟨hf.1.2.1, hf.2.2.1⟩

/-- Lifting K4 preserves pair occupancy exactly. -/
theorem suffix_k4_pairMass (hψ : ψ > 0) (l r : AuthState ψ) :
    pairPathMass (lift2 (k4Kernel hψ) l r) = pairPathMass (l, r) := by
  have hf := suffix_k4_paths hψ l.core r.core
  simp [pairPathMass, pathMass, lift2, hf.1, hf.2]

/-- WRITE retains both main paths, by the existing writer frame. -/
theorem suffix_writeWithBundle_paths (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeWithBundle hψ l r).1.path = l.path ∧
    (writeWithBundle hψ l r).2.path = r.path := by
  have hf := PPLLAuthGenDrain.WFrame.write_frame hψ l r
  exact ⟨hf.1.2.1, hf.2.2.1⟩

/-- Lifting WRITE preserves pair occupancy exactly. -/
theorem suffix_writeWithBundle_pairMass (hψ : ψ > 0) (l r : AuthState ψ) :
    pairPathMass (lift2 (writeWithBundle hψ) l r) = pairPathMass (l, r) := by
  have hf := suffix_writeWithBundle_paths hψ l.core r.core
  simp [pairPathMass, pathMass, lift2, hf.1, hf.2]

end PPLLAuthHoleRouting
#print axioms PPLLAuthHoleRouting.suffix_k4_pairMass
#print axioms PPLLAuthHoleRouting.suffix_writeWithBundle_pairMass

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam PPLLRepair PPLLPostElectionGuard PPLLBirthPatchM2 PPLLAstraDesign3
variable {ψ : Nat}

/-- Stale deletion can only remove the occupied main path. -/
theorem suffix_dropStale_pathMass (u : AuthState ψ) :
    pathMass (liftLife PPLLBirthPatchM2.dropStale u) ≤ pathMass u := by
  have hc := PPLLAuthGenDrain.liftLife_core
    PPLLBirthPatchM2.dropStale u
  by_cases h : u.core.path ≠ .bot ∧ aligned u.core = false ∧
      blockingState u.core = true
  · simp [pathMass, hc, PPLLBirthPatchM2.dropStale, h]
  · simp [pathMass, hc, PPLLBirthPatchM2.dropStale, h]

/-- Stale deletion on both endpoints is mass monotone. -/
theorem suffix_dropStale_pairMass (l r : AuthState ψ) :
    pairPathMass
      (liftLife PPLLBirthPatchM2.dropStale l,
       liftLife PPLLBirthPatchM2.dropStale r) ≤
      pairPathMass (l, r) := by
  unfold pairPathMass
  exact Nat.add_le_add (suffix_dropStale_pathMass l)
    (suffix_dropStale_pathMass r)

/-- Clearing comparison state removes the main path. -/
private theorem suffix_clearCmpAuth_mass (u : AuthState ψ) :
    pathMass (clearCmpAuth u) = 0 := by
  simp [pathMass, clearCmpAuth, PPLLPostElectionGuard.clearCmp]

/-- Pre-CHECK reset independently keeps or deletes each endpoint path. -/
theorem suffix_preCheckReset_pairMass (l r : AuthState ψ) :
    pairPathMass (preCheckResetAuth l r) ≤ pairPathMass (l, r) := by
  cases hs : (l.core.leader || l.core.reset_cmd) <;>
    cases hr : r.core.reset_cmd <;>
    simp [preCheckResetAuth, hs, hr, pairPathMass,
      suffix_clearCmpAuth_mass] <;> omega

/-- Readiness normalization retains the core main path. -/
theorem suffix_normalizeReady_path (u : AuthState ψ) :
    (liftLife normalizeReady u).core.path = u.core.path := by
  rw [PPLLAuthGenDrain.liftLife_core]
  exact PPLLAuthSerialDischarge.ready_path u.core

/-- Readiness normalization preserves pair occupancy exactly. -/
theorem suffix_normalizeReady_pairMass (l r : AuthState ψ) :
    pairPathMass (liftLife normalizeReady l, liftLife normalizeReady r) =
      pairPathMass (l, r) := by
  simp [pairPathMass, pathMass, suffix_normalizeReady_path]

end PPLLAuthHoleRouting
#print axioms PPLLAuthHoleRouting.suffix_dropStale_pairMass
#print axioms PPLLAuthHoleRouting.suffix_preCheckReset_pairMass
#print axioms PPLLAuthHoleRouting.suffix_normalizeReady_pairMass

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam PPLLAuthChamp PPLLAstraDesign3 PPLLAstraDesign2 PPLLPostElectionGuard PPLLFableDesignR1
/-
Append in namespace PPLLAuthHoleRouting, after pathMass and pairPathMass.
Requires import Leader.PPLLAuthCheckSuffixPathFrame.
No duplicate definitions.
-/

variable {ψ : Nat}

/-- CHECK preserves both main paths, including terminal leader birth. -/
theorem suffix_checkSource_pairMass (hψ : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) :
    pairPathMass (checkSourceAuth hψ c l r) = pairPathMass (l, r) := by
  have hp := PPLLAuthCheckSuffixPathFrame.checkSource_path hψ c l r
  unfold pairPathMass pathMass
  rw [hp.1, hp.2]

/-- The lottery-scrub branch of champion disappearance retains both paths. -/
theorem suffix_champDisappear_paths (hψ : ψ > 0) (cc : ChampCfg)
    (hcc : cc.lotteryScrub = true) (l r : AuthState ψ) :
    (champDisappearAuth hψ cc l r).1.core.path = l.core.path ∧
    (champDisappearAuth hψ cc l r).2.core.path = r.core.path := by
  unfold champDisappearAuth
  rw [if_neg (by simp [hcc])]
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- Champion disappearance preserves pair occupancy under sVplusE. -/
theorem suffix_champDisappear_pairMass (hψ : ψ > 0) (cc : ChampCfg)
    (hcc : cc.lotteryScrub = true) (l r : AuthState ψ) :
    pairPathMass (champDisappearAuth hψ cc l r) = pairPathMass (l, r) := by
  have hp := suffix_champDisappear_paths hψ cc hcc l r
  unfold pairPathMass pathMass
  rw [hp.1, hp.2]

/-- Seam repair adds a lineage guard to a path-preserving release. -/
theorem suffix_seamRepair_paths (c : SeamCfg) (l r : AuthState ψ) :
    (seamRepairAuth c l r).1.core.path = l.core.path ∧
    (seamRepairAuth c l r).2.core.path = r.core.path := by
  have hc : ∀ a : AgentState ψ,
      (normalizeCarrier (normalizeOrphan a)).path = a.path :=
    fun a => (PPLLAuthCheckSuffixPathFrame.carrier_path _).trans
      (PPLLAuthCheckSuffixPathFrame.orphan_path a)
  have hl := PPLLAuthCheckSuffixPathFrame.liftLife_path _ hc
  have hr := PPLLAuthCheckSuffixPathFrame.lift2Life_path
    (ψ := ψ) releaseReadySuffix PPLLAuthCheckSuffixPathFrame.releaseSuffix_path
  have ha : ∀ a b : AuthState ψ,
      (ackTailAuth a b).1.core.path = a.core.path ∧
      (ackTailAuth a b).2.core.path = b.core.path := by
    intro a b
    unfold ackTailAuth
    split
    · exact PPLLAuthCheckSuffixPathFrame.lift2_path ackTail
        PPLLAuthCheckSuffixPathFrame.ackTail_path a b
    · exact ⟨rfl, rfl⟩
  simp only [seamRepairAuth, ha]
  split <;> simp only [ha, hr, hl, and_self]

/-- Seam repair preserves pair occupancy. -/
theorem suffix_seamRepair_pairMass (c : SeamCfg) (l r : AuthState ψ) :
    pairPathMass (seamRepairAuth c l r) = pairPathMass (l, r) := by
  have hp := suffix_seamRepair_paths c l r
  unfold pairPathMass pathMass
  rw [hp.1, hp.2]

/-- The chosen sVplusE configuration enters the lottery-scrub branch. -/
theorem suffix_sVplusE_champDisappear_pairMass (hψ : ψ > 0)
    (l r : AuthState ψ) :
    pairPathMass (champDisappearAuth hψ (toChamp sVplusE) l r) =
      pairPathMass (l, r) :=
  suffix_champDisappear_pairMass hψ (toChamp sVplusE) rfl l r

end PPLLAuthHoleRouting
#print axioms PPLLAuthHoleRouting.suffix_checkSource_pairMass
#print axioms PPLLAuthHoleRouting.suffix_champDisappear_pairMass
#print axioms PPLLAuthHoleRouting.suffix_seamRepair_pairMass

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam

/-- The actual complete MOVE stage never increases pair occupancy. The
pre-Step1 pair is retained for the lottery metadata test, Step1 conserves
occupancy, and every other factored stage preserves or deletes paths. -/
theorem seamMoveSourceAuth_pairPathMass {ψ : Nat} (hp : ψ > 0)
    (c : SeamCfg) (l r : AuthState ψ) :
    pairPathMass (seamMoveSourceAuth hp c l r) ≤ pairPathMass (l, r) := by
  let q0 := movePrefix hp c l r
  let q1 := if q0.1.st = MainState.done then (q0.1, q0.2)
    else step1Auth q0.1 q0.2
  let q2 := moveMiddle c q0.1 q0.2 q1.1 q1.2
  let q3 := seamMoveTokensAuth c q2.1 q2.2
  let q4 := moveFinish hp c q3.1 q3.2
  have h0 : pairPathMass q0 ≤ pairPathMass (l, r) :=
    movePrefix_pairPathMass hp c l r
  have h1 : pairPathMass q1 = pairPathMass q0 :=
    moveStep1_pairPathMass q0.1 q0.2
  have h2 : pairPathMass q2 = pairPathMass q1 :=
    moveMiddle_pairPathMass c q0.1 q0.2 q1.1 q1.2
  have h3 : pairPathMass q3 ≤ pairPathMass q2 :=
    seamMoveTokensAuth_pairPathMass c q2.1 q2.2
  have h4 : pairPathMass q4 ≤ pairPathMass q3 :=
    moveFinish_pairPathMass hp c q3.1 q3.2
  have hactual : seamMoveSourceAuth hp c l r = q4 := by rfl
  rw [hactual]
  calc
    pairPathMass q4 ≤ pairPathMass q3 := h4
    _ ≤ pairPathMass q2 := h3
    _ = pairPathMass q1 := h2
    _ = pairPathMass q0 := h1
    _ ≤ pairPathMass (l, r) := h0

end PPLLAuthHoleRouting
#print axioms PPLLAuthHoleRouting.seamMoveSourceAuth_pairPathMass

section synchronousSuffixProofs
set_option Elab.async false

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam PPLLAuthChamp PPLLAstraDesign2 PPLLAstraDesign3 PPLLPostElectionGuard PPLLFableDesignR1
/-
Append in namespace PPLLAuthHoleRouting, after small1 and small4.
Requires PPLLAuthCheckSuffixPathFrame (small3 import).
-/

variable {ψ : Nat}

/-- Each of the five core suppression actions leaves both main paths in place. -/
private theorem suffix_suppressStart_paths (l r : AgentState ψ) :
    (suppressSigStart l r).1.path = l.path ∧
    (suppressSigStart l r).2.path = r.path := by
  simp [suppressSigStart, PPLLAuthCheckSuffixPathFrame.fst_ite,
    PPLLAuthCheckSuffixPathFrame.snd_ite,
    PPLLAuthCheckSuffixPathFrame.path_ite']

private theorem suffix_suppressMove_paths (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.path = l.path ∧
    (suppressSigMoveReset l r).2.path = r.path := by
  simp [suppressSigMoveReset, PPLLAuthCheckSuffixPathFrame.fst_ite,
    PPLLAuthCheckSuffixPathFrame.snd_ite,
    PPLLAuthCheckSuffixPathFrame.path_ite']

private theorem suffix_suppressTerminal_paths (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.path = l.path ∧
    (suppressSigTerminal hψ l r).2.path = r.path := by
  simp [suppressSigTerminal, PPLLAuthCheckSuffixPathFrame.fst_ite,
    PPLLAuthCheckSuffixPathFrame.snd_ite,
    PPLLAuthCheckSuffixPathFrame.path_ite']

private theorem suffix_suppressEcho_paths (l r : AgentState ψ) :
    (suppressSigEcho l r).1.path = l.path ∧
    (suppressSigEcho l r).2.path = r.path := by
  simp [suppressSigEcho, PPLLAuthCheckSuffixPathFrame.fst_ite,
    PPLLAuthCheckSuffixPathFrame.snd_ite,
    PPLLAuthCheckSuffixPathFrame.path_ite']

private theorem suffix_suppressFinish_paths (l r : AgentState ψ) :
    (suppressSigFinish l r).1.path = l.path ∧
    (suppressSigFinish l r).2.path = r.path := by
  simp [suppressSigFinish, PPLLAuthCheckSuffixPathFrame.fst_ite,
    PPLLAuthCheckSuffixPathFrame.snd_ite,
    PPLLAuthCheckSuffixPathFrame.path_ite']

private def suffix_killReset (u : AuthState ψ) : AuthState ψ :=
  if u.core.reset_cmd then clearCmpAuth u else u

private theorem suffix_killReset_mass (u : AuthState ψ) :
    pathMass (suffix_killReset u) ≤ pathMass u := by
  cases h : u.core.reset_cmd <;>
    simp [suffix_killReset, h, pathMass, clearCmpAuth,
      PPLLPostElectionGuard.clearCmp]

private theorem suffix_killReset_pairMass (l r : AuthState ψ) :
    pairPathMass (suffix_killReset l, suffix_killReset r) ≤
      pairPathMass (l, r) := by
  unfold pairPathMass
  exact Nat.add_le_add (suffix_killReset_mass l) (suffix_killReset_mass r)

private theorem suffix_lift2Mass (f : AgentState ψ → AgentState ψ →
    AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) :
    pairPathMass (lift2 f l r) = pairPathMass (l, r) := by
  have hp := PPLLAuthCheckSuffixPathFrame.lift2_path f hf l r
  simp [pairPathMass, pathMass, hp.1, hp.2]

/-- The only possible occupancy losses in suppression are its two reset kills. -/
theorem suffix_suppress_pairMass (hψ : ψ > 0) (l r : AuthState ψ) :
    pairPathMass (suppressSigResetKillAuth hψ l r) ≤
      pairPathMass (l, r) := by
  let q0 := lift2 suppressSigStart l r
  let q0k := (suffix_killReset q0.1, suffix_killReset q0.2)
  let q1 := lift2 suppressSigMoveReset q0k.1 q0k.2
  let q1k := (suffix_killReset q1.1, suffix_killReset q1.2)
  let q2 := lift2 (suppressSigTerminal hψ) q1k.1 q1k.2
  let q3 := lift2 suppressSigEcho q2.1 q2.2
  have hf : suppressSigResetKillAuth hψ l r =
      lift2 suppressSigFinish q3.1 q3.2 := rfl
  rw [hf]
  calc
    pairPathMass (lift2 suppressSigFinish q3.1 q3.2)
        = pairPathMass q3 :=
          suffix_lift2Mass suppressSigFinish suffix_suppressFinish_paths q3.1 q3.2
    _ = pairPathMass q2 :=
          suffix_lift2Mass suppressSigEcho suffix_suppressEcho_paths q2.1 q2.2
    _ = pairPathMass q1k :=
          suffix_lift2Mass (suppressSigTerminal hψ)
            (suffix_suppressTerminal_paths hψ) q1k.1 q1k.2
    _ ≤ pairPathMass q1 := suffix_killReset_pairMass q1.1 q1.2
    _ = pairPathMass q0k :=
          suffix_lift2Mass suppressSigMoveReset suffix_suppressMove_paths q0k.1 q0k.2
    _ ≤ pairPathMass q0 := suffix_killReset_pairMass q0.1 q0.2
    _ = pairPathMass (l, r) :=
          suffix_lift2Mass suppressSigStart suffix_suppressStart_paths l r

end PPLLAuthHoleRouting
#print axioms PPLLAuthHoleRouting.suffix_suppress_pairMass

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam PPLLAuthChamp PPLLAstraDesign2 PPLLAstraDesign3 PPLLPostElectionGuard PPLLFableDesignR1
/-
Append in namespace PPLLAuthHoleRouting, after small3.
Requires PPLLAuthCheckSuffixPathFrame (small3 import).  No new definitions.
-/

variable {ψ : Nat}

private theorem suffix_pairMass_eq_of_paths
    (a b : AuthState ψ × AuthState ψ)
    (h₁ : a.1.core.path = b.1.core.path)
    (h₂ : a.2.core.path = b.2.core.path) :
    pairPathMass a = pairPathMass b := by
  simp [pairPathMass, pathMass, h₁, h₂]

/-- The c2 supplement changes lifecycle state, retaining both main paths. -/
theorem suffix_c2Maintain_paths (l r : AuthState ψ) :
    (c2Maintain l r).1.core.path = l.core.path ∧
    (c2Maintain l r).2.core.path = r.core.path := by
  unfold c2Maintain
  cases hl : l.core.path <;> cases hr : r.core.path <;>
    simp only [hl, hr, PPLLAuthCheckSuffixPathFrame.fst_ite,
      PPLLAuthCheckSuffixPathFrame.snd_ite,
      PPLLAuthCheckSuffixPathFrame.core_ite,
      PPLLAuthCheckSuffixPathFrame.path_ite', ite_self] <;>
    repeat (first | split | simp_all [AuthState.lineage])

private theorem waveSetState_path {ψ : Nat} (u : AuthState ψ) (s : MainState) :
    (u.setState s).core.path = u.core.path := rfl

/-- Metadata-only middle of waveAuthE, between the two cap checks. -/
private def waveMetadata {ψ : Nat} (ll rl : Nat) (start : Bool)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let (l, r) := if start then
    let σ := fresh3 l.ctrl_mark r.ctrl_mark
    ({ l with ctrl_mark := σ },
     { r with core := { r.core with state := .lock, path2 := none, path4 := none, path5 := none },
              ctrl_mark := σ }) else (l, r)
  let r := if l.st = .lock ∧ rl = ll + 1 ∧ r.st = .depart then
    { (r.setState (if rl = ψ - 1 then .compare1 else .lock)) with ctrl_mark := l.ctrl_mark } else r
  let l := if r.st = .compare1 ∧ rl = ll + 1 ∧ l.st = .lock ∧ r.ctrl_mark = l.ctrl_mark then
    l.setState .compare1 else l
  let l := if ll = ψ - 1 ∧ rl = 0 ∧ r.st = .compare1 ∧
      (l.st = .depart ∨ lockedState l.st) ∧ l.ctrl_mark = r.ctrl_mark then
    { l with core := { l.core with state := .compare2, path2 := some (a2Token (ψ := ψ)) },
             path2_scope := .session, path2_mark := r.ctrl_mark } else l
  (l, r)

private theorem waveMetadata_paths {ψ : Nat} (ll rl : Nat) (start : Bool)
    (l r : AuthState ψ) :
    (waveMetadata ll rl start l r).1.core.path = l.core.path ∧
    (waveMetadata ll rl start l r).2.core.path = r.core.path := by
  by_cases hs : start = true
  · simp only [waveMetadata, if_pos hs, move_authPath_ite, waveSetState_path,
      ite_self, and_self]
  · simp only [waveMetadata, if_neg hs, move_authPath_ite, waveSetState_path,
      ite_self, and_self]

/-- The last cap check and token re-emission; both Boolean guards are opaque. -/
private def waveExit {ψ : Nat} (head reemit : Bool) (er : Fin 3)
    (q : AuthState ψ × AuthState ψ) : (AuthState ψ × AuthState ψ) × Fin 3 :=
  if reemit && head && er.val = 2 then
    ((q.1, { q.2 with core := { q.2.core with path := .bot, state := .none } }), er)
  else
    let er : Fin 3 := if reemit && head then
      (if h : er.val < 2 then ⟨er.val + 1, by omega⟩ else er) else er
    let l := if reemit then
      { q.1 with core := { q.1.core with path2 := some (a2Token (ψ := ψ)) },
                 path2_scope := .session, path2_mark := q.2.ctrl_mark } else q.1
    ((l, q.2), er)

private theorem waveExit_paths {ψ : Nat} (head reemit : Bool) (er : Fin 3)
    (q : AuthState ψ × AuthState ψ) :
    (waveExit head reemit er q).1.1.core.path = q.1.core.path ∧
    ((waveExit head reemit er q).1.2.core.path = q.2.core.path ∨
      (waveExit head reemit er q).1.2.core.path = .bot) := by
  unfold waveExit
  split
  · exact ⟨rfl, Or.inr rfl⟩
  · dsimp only
    constructor
    · simp only [move_authPath_ite, ite_self]
    · exact Or.inl rfl

/-- Factoring the two cap checks preserves the initiator path and permits only responder deletion. -/
theorem suffix_waveAuthE_paths_factored {ψ : Nat} (l r : AuthState ψ) (er : Fin 3) :
    (waveAuthE l r er).1.1.core.path = l.core.path ∧
    ((waveAuthE l r er).1.2.core.path = r.core.path ∨
      (waveAuthE l r er).1.2.core.path = .bot) := by
  cases hl : l.core.path with
  | bot => simp only [waveAuthE, hl, true_or, and_self]
  | some ll lb =>
    cases hr : r.core.path with
    | bot => simp only [waveAuthE, hl, hr, true_or, and_self]
    | some rl rb =>
      let head : Bool := decide (r.core.label.val = 0)
      let start : Bool := decide (ll = ψ - 1) && decide (rl = 0) && l.st == .depart &&
        r.st == .depart && l.ctrl_mark == l.path_mark && r.ctrl_mark == r.path_mark &&
        !sessionTokenOn l && !sessionTokenOn r
      let cap : Prop := start && head && er.val = 2
      let er' : Fin 3 := if start && head then
        (if h : er.val < 2 then ⟨er.val + 1, by omega⟩ else er) else er
      let q := waveMetadata ll rl start l r
      let reemit : Bool := decide (ll = ψ - 1 ∧ rl = 0 ∧ q.2.st = .compare1 ∧
        q.1.st = .compare2 ∧ q.1.core.path2 = none ∧ q.2.core.path2 = none ∧
        q.1.ctrl_mark = q.2.ctrl_mark)
      have hfactor : waveAuthE l r er =
          if cap then
            ((l, { r with core := { r.core with path := .bot, state := .none } }), er)
          else waveExit head reemit er' q := by
        unfold waveAuthE
        rw [hl, hr] <;> rfl
      rw [hfactor]
      by_cases hc : cap
      · rw [if_pos hc]
        exact ⟨hl, Or.inr rfl⟩
      · rw [if_neg hc]
        have hm := waveMetadata_paths ll rl start l r
        simp only [hl, hr] at hm
        have he := waveExit_paths head reemit er' q
        refine ⟨he.1.trans hm.1, ?_⟩
        rcases he.2 with he | he
        · exact Or.inl (he.trans hm.2)
        · exact Or.inr he

/-- Episode charging may delete the responder's path; it never creates one. -/
theorem suffix_waveAuthE_paths (l r : AuthState ψ) (er : Fin 3) :
    (waveAuthE l r er).1.1.core.path = l.core.path ∧
    ((waveAuthE l r er).1.2.core.path = r.core.path ∨
     (waveAuthE l r er).1.2.core.path = .bot) := by
  exact suffix_waveAuthE_paths_factored l r er

/-- The charged wave cannot increase the pair's occupied-path count. -/
theorem suffix_waveAuthE_pairMass (l r : AuthState ψ) (er : Fin 3) :
    pairPathMass (waveAuthE l r er).1 ≤ pairPathMass (l, r) := by
  have hp := suffix_waveAuthE_paths l r er
  rcases hp.2 with hkeep | hdrop
  · simp [pairPathMass, pathMass, hp.1, hkeep]
  · simp [pairPathMass, pathMass, hp.1, hdrop]

/-- c2 maintenance followed by the charged wave is mass monotone. -/
theorem suffix_compareLifecycle_pairMass (κ : Nat) (c : SeamCfg)
    (l r : AuthState ψ) (er : Fin 3) :
    pairPathMass (compareLifecycleE κ c l r er).1 ≤ pairPathMass (l, r) := by
  let l0 := match l.core.path with
    | .bot => if l.st = MainState.produce then l else l.setState .none
    | .some _ _ => l
  let q1 := maintainAuth l0 r
  let q2 := if c.c2Release then c2Maintain q1.1 q1.2 else q1
  let q3 := completeWaveAuth q2.1 q2.2
  let q4 := (waveAuthE q3.1 q3.2 er).1
  let q5 := lift2 PPLLFableDesignR1.dropStray q4.1 q4.2
  have h0 : l0.core.path = l.core.path := by
    cases h : l.core.path <;>
      simp only [l0, h, AuthState.setState,
        PPLLAuthCheckSuffixPathFrame.core_ite,
        PPLLAuthCheckSuffixPathFrame.path_ite'] <;>
      repeat (first | split | simp_all)
  have h1 := PPLLAuthCheckSuffixPathFrame.maintain_path l0 r
  have h2 : q2.1.core.path = q1.1.core.path ∧
      q2.2.core.path = q1.2.core.path := by
    by_cases hc : c.c2Release = true
    · simpa [q2, hc] using suffix_c2Maintain_paths q1.1 q1.2
    · simp [q2, hc]
  have h3 := PPLLAuthCheckSuffixPathFrame.completeWave_path q2.1 q2.2
  have h5 := PPLLAuthCheckSuffixPathFrame.lift2_path
    PPLLFableDesignR1.dropStray PPLLAuthCheckSuffixPathFrame.dropStray_path
    q4.1 q4.2
  have hfinal : pairPathMass (compareLifecycleE κ c l r er).1 =
      pairPathMass q4 := by
    have hb := PPLLAuthCheckSuffixPathFrame.landBackwardAuth_path q5.1
    have hf := PPLLAuthCheckSuffixPathFrame.landForwardAuth_path κ q5.2
    change pairPathMass (landBackwardAuth q5.1, landForwardAuth κ q5.2) =
      pairPathMass q4
    exact (suffix_pairMass_eq_of_paths _ _ hb hf).trans
      (suffix_pairMass_eq_of_paths _ _ h5.1 h5.2)
  rw [hfinal]
  have hm := suffix_waveAuthE_pairMass q3.1 q3.2 er
  have e1 : pairPathMass q1 = pairPathMass (l0, r) :=
    suffix_pairMass_eq_of_paths _ _ h1.1 h1.2
  have e2 : pairPathMass q2 = pairPathMass q1 :=
    suffix_pairMass_eq_of_paths _ _ h2.1 h2.2
  have e3 : pairPathMass q3 = pairPathMass q2 :=
    suffix_pairMass_eq_of_paths _ _ h3.1 h3.2
  have e0 : pairPathMass (l0, r) = pairPathMass (l, r) :=
    suffix_pairMass_eq_of_paths _ _ h0 rfl
  have hp : pairPathMass q3 = pairPathMass (l, r) :=
    e3.trans (e2.trans (e1.trans e0))
  change pairPathMass q4 ≤ pairPathMass q3 at hm
  rw [hp] at hm
  exact hm

/-
Append in namespace PPLLAuthHoleRouting after pairPathMass.
This is the source-input leaderless guard used by the real seam row.
-/

variable {ψ : Nat}

/-- If neither original endpoint led, `conserveAuth` cannot fire its
replacement branch, whatever K4 and WRITE did to the intermediate pair. -/
theorem suffix_conserve_no_fired (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (q : AuthState ψ × AuthState ψ) :
    conserveAuth l r q =
      ({ q.1 with core :=
          (PPLLAstraDesign2.conserve .head l.core r.core
            (q.1.core, q.2.core)).1 },
       { q.2 with core :=
          (PPLLAstraDesign2.conserve .head l.core r.core
            (q.1.core, q.2.core)).2 }) := by
  simp [conserveAuth, hl, hr]

/-- Under the same original-input guard, conservation is the identity on
both main paths and hence on their occupancy. -/
theorem suffix_conserve_pairMass (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (q : AuthState ψ × AuthState ψ) :
    pairPathMass (conserveAuth l r q) = pairPathMass q := by
  rw [suffix_conserve_no_fired l r hl hr q]
  simp [pairPathMass, pathMass, PPLLAstraDesign2.conserve, hl, hr]

end PPLLAuthHoleRouting
end synchronousSuffixProofs
#print axioms PPLLAuthHoleRouting.suffix_compareLifecycle_pairMass
#print axioms PPLLAuthHoleRouting.suffix_conserve_pairMass
/-! ## Hole-routing Lemma 2: completed EpisodeCap row and ring lift -/

namespace PPLLAuthHoleRouting

open PPLL PPLLRepair PPLLAuthF PPLLAuthSeam PPLLAuthGenDrain
open PPLLPostElectionGuard PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthChamp
open PPLLBirthPatchM2 PPLLFableDesignR1

variable {ψ : Nat}


set_option Elab.async false in
private theorem q20976_seamStepE_delta
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg)
    (l r : AuthState ψ) (el er : Fin 3) :
    seamStepE hψ κ c l r el er =
      (if !c.episodeCap then
         (seamStep hψ κ c l r, (el, er))
       else if c.episodeResetTouch then
         seamStepT hψ κ c l r el er
       else
         let (q, er) := seamBeforeEliminationE hψ κ c l r er
         let q := lift2 (k4Kernel hψ) q.1 q.2
         let q := lift2 (writeWithBundle hψ) q.1 q.2
         let q := conserveAuth l r q
         let el := if q.1.core.path = l.core.path then el else 0
         let er := if q.2.core.path = r.core.path then er else 0
         (q, (el, er))) := by
  rfl

set_option Elab.async false in
private theorem q20976_sVplusE_outer_of_pair
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (el er0 : Fin 3)
    (p : (AuthState ψ × AuthState ψ) × Fin 3) :
    (if !sVplusE.episodeCap then
       (seamStep hψ κ sVplusE l r, (el, er0))
     else if sVplusE.episodeResetTouch then
       seamStepT hψ κ sVplusE l r el er0
     else
       let (q, er) := p
       let q := lift2 (k4Kernel hψ) q.1 q.2
       let q := lift2 (writeWithBundle hψ) q.1 q.2
       let q := conserveAuth l r q
       let el := if q.1.core.path = l.core.path then el else 0
       let er := if q.2.core.path = r.core.path then er else 0
       (q, (el, er))).1 =
      (let q := p.1
       let q := lift2 (k4Kernel hψ) q.1 q.2
       let q := lift2 (writeWithBundle hψ) q.1 q.2
       conserveAuth l r q) := by
  cases p with
  | mk q er =>
      rfl

set_option Elab.async false in
private theorem q20976_sVplusE_outer_of_before_eq
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (el er : Fin 3)
    (p : (AuthState ψ × AuthState ψ) × Fin 3)
    (hbefore :
      seamBeforeEliminationE hψ κ sVplusE l r er = p) :
    (seamStepE hψ κ sVplusE l r el er).1 =
      (let q := p.1
       let q := lift2 (k4Kernel hψ) q.1 q.2
       let q := lift2 (writeWithBundle hψ) q.1 q.2
       conserveAuth l r q) := by
  rw [q20976_seamStepE_delta
    (hψ := hψ) (κ := κ) (c := sVplusE)
    (l := l) (r := r) (el := el) (er := er)]
  rw [hbefore]
  exact q20976_sVplusE_outer_of_pair
    (hψ := hψ) (κ := κ) (l := l) (r := r)
    (el := el) (er0 := er) (p := p)

set_option Elab.async false in
private theorem seamStepE_sVplusE_outer_factor
    {ψ : Nat} (hp : ψ > 0) (kappa : Nat)
    (l r : AuthState ψ) (el er : Fin 3) :
    (seamStepE hp kappa sVplusE l r el er).1 =
      (let q := (seamBeforeEliminationE hp kappa sVplusE l r er).1
       let q := lift2 (k4Kernel hp) q.1 q.2
       let q := lift2 (writeWithBundle hp) q.1 q.2
       conserveAuth l r q) := by
  exact q20976_sVplusE_outer_of_before_eq
    (hψ := hp) (κ := kappa) (l := l) (r := r)
    (el := el) (er := er)
    (p := seamBeforeEliminationE hp kappa sVplusE l r er)
    (hbefore := rfl)

set_option Elab.async false in
private theorem fst_match_returned_pair_opaque
    {α β γ : Type} (x : α × β) (f : α → γ) :
    (match x with
     | (a, b) => (f a, b)).1 = f x.1 := by
  cases x
  rfl

set_option Elab.async false in
private theorem q20991_seamBeforeEliminationE_delta
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg)
    (l r : AuthState ψ) (er : Fin 3) :
    seamBeforeEliminationE hψ κ c l r er =
      (let cc := toChamp c
       let q1 := lift2 (pPsiProbeWall hψ) l r
       let q2 := genSigAuth hψ κ q1.1 q1.2
       let q3 := (hygieneOne c q2.1, hygieneOne c q2.2)
       let q4 := seamCleanSourceAuth hψ c q3.1 q3.2
       let q5 := lift2Life (releaseSource hψ) q4.1 q4.2
       let q6 := lift2 (eliminateSig hψ) q5.1 q5.2
       let q7 := seamMoveSourceAuth hψ c q6.1 q6.2
       let q8 := (liftLife dropStale q7.1,
                  liftLife dropStale q7.2)
       let q9 := preCheckResetAuth q8.1 q8.2
       let q10 := (liftLife normalizeReady q9.1,
                   liftLife normalizeReady q9.2)
       let q11 := checkSourceAuth hψ c.base q10.1 q10.2
       let q12 := champDisappearAuth hψ cc q11.1 q11.2
       let q13 := seamRepairAuth c q12.1 q12.2
       let (q, er') := compareLifecycleE κ c q13.1 q13.2 er
       (suppressSigResetKillAuth hψ q.1 q.2, er')) := by
  rfl

set_option Elab.async false in
private theorem q20991_seamBeforeEliminationE_of_stages
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : SeamCfg)
    (l r : AuthState ψ) (er : Fin 3)
    (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 :
      AuthState ψ × AuthState ψ)
    (h1 : lift2 (PPLLPostElectionGuard.pPsiProbeWall hψ) l r = q1)
    (h2 : genSigAuth hψ κ q1.1 q1.2 = q2)
    (h3 : (hygieneOne c q2.1, hygieneOne c q2.2) = q3)
    (h4 : seamCleanSourceAuth hψ c q3.1 q3.2 = q4)
    (h5 : lift2Life (PPLLAstraDesign3.releaseSource hψ)
      q4.1 q4.2 = q5)
    (h6 : lift2 (eliminateSig hψ) q5.1 q5.2 = q6)
    (h7 : seamMoveSourceAuth hψ c q6.1 q6.2 = q7)
    (h8 : (liftLife PPLLBirthPatchM2.dropStale q7.1,
      liftLife PPLLBirthPatchM2.dropStale q7.2) = q8)
    (h9 : preCheckResetAuth q8.1 q8.2 = q9)
    (h10 : (liftLife normalizeReady q9.1,
      liftLife normalizeReady q9.2) = q10)
    (h11 : checkSourceAuth hψ c.base q10.1 q10.2 = q11)
    (h12 : champDisappearAuth hψ (toChamp c) q11.1 q11.2 = q12)
    (h13 : seamRepairAuth c q12.1 q12.2 = q13) :
    seamBeforeEliminationE hψ κ c l r er =
      (let (q, er') := compareLifecycleE κ c q13.1 q13.2 er
       (suppressSigResetKillAuth hψ q.1 q.2, er')) := by
  let k13 := fun p : AuthState ψ × AuthState ψ =>
    let (q, er') := compareLifecycleE κ c p.1 p.2 er
    (suppressSigResetKillAuth hψ q.1 q.2, er')
  let k12 := fun p : AuthState ψ × AuthState ψ =>
    k13 (seamRepairAuth c p.1 p.2)
  let k11 := fun p : AuthState ψ × AuthState ψ =>
    k12 (champDisappearAuth hψ (toChamp c) p.1 p.2)
  let k10 := fun p : AuthState ψ × AuthState ψ =>
    k11 (checkSourceAuth hψ c.base p.1 p.2)
  let k9 := fun p : AuthState ψ × AuthState ψ =>
    k10 (liftLife normalizeReady p.1, liftLife normalizeReady p.2)
  let k8 := fun p : AuthState ψ × AuthState ψ =>
    k9 (preCheckResetAuth p.1 p.2)
  let k7 := fun p : AuthState ψ × AuthState ψ =>
    k8 (liftLife PPLLBirthPatchM2.dropStale p.1,
      liftLife PPLLBirthPatchM2.dropStale p.2)
  let k6 := fun p : AuthState ψ × AuthState ψ =>
    k7 (seamMoveSourceAuth hψ c p.1 p.2)
  let k5 := fun p : AuthState ψ × AuthState ψ =>
    k6 (lift2 (eliminateSig hψ) p.1 p.2)
  let k4 := fun p : AuthState ψ × AuthState ψ =>
    k5 (lift2Life (PPLLAstraDesign3.releaseSource hψ) p.1 p.2)
  let k3 := fun p : AuthState ψ × AuthState ψ =>
    k4 (seamCleanSourceAuth hψ c p.1 p.2)
  let k2 := fun p : AuthState ψ × AuthState ψ =>
    k3 (hygieneOne c p.1, hygieneOne c p.2)
  let k1 := fun p : AuthState ψ × AuthState ψ =>
    k2 (genSigAuth hψ κ p.1 p.2)

  calc
    seamBeforeEliminationE hψ κ c l r er =
        k1 (lift2 (PPLLPostElectionGuard.pPsiProbeWall hψ) l r) :=
      q20991_seamBeforeEliminationE_delta
        (hψ := hψ) (κ := κ) (c := c)
        (l := l) (r := r) (er := er)
    _ = k1 q1 := congrArg k1 h1
    _ = k2 q2 := congrArg k2 h2
    _ = k3 q3 := congrArg k3 h3
    _ = k4 q4 := congrArg k4 h4
    _ = k5 q5 := congrArg k5 h5
    _ = k6 q6 := congrArg k6 h6
    _ = k7 q7 := congrArg k7 h7
    _ = k8 q8 := congrArg k8 h8
    _ = k9 q9 := congrArg k9 h9
    _ = k10 q10 := congrArg k10 h10
    _ = k11 q11 := congrArg k11 h11
    _ = k12 q12 := congrArg k12 h12
    _ = k13 q13 := congrArg k13 h13

set_option Elab.async false in
/-- Tuple-input form of RELEASE mass preservation.  The eta transport is
performed while `q` is opaque, so clients need not identify `(q.1, q.2)`
with a concrete operational prefix. -/
private theorem q21000_row_release_mass_pair {ψ : Nat}
    (hp : ψ > 0) (q : AuthState ψ × AuthState ψ) :
    pairPathMass
        (lift2Life (PPLLAstraDesign3.releaseSource hp) q.1 q.2) =
      pairPathMass q := by
  have heta : (q.1, q.2) = q := Prod.eta q
  exact (row_release_mass hp q.1 q.2).trans
    (congrArg
      (fun z : AuthState ψ × AuthState ψ => pairPathMass z)
      heta)

set_option Elab.async false in
private theorem q21003_pairPathMass_eta {ψ : Nat} (q : AuthState ψ × AuthState ψ) :
    pairPathMass (q.1, q.2) = pairPathMass q :=
  congrArg
    (fun z : AuthState ψ × AuthState ψ => pairPathMass z)
    (Prod.eta q)
set_option Elab.async false in
private theorem q21003_row_eliminate_mass_pair {ψ : Nat} (hp : ψ > 0) (q : AuthState ψ × AuthState ψ) :
    pairPathMass (lift2 (eliminateSig hp) q.1 q.2) ≤ pairPathMass q := by
  calc
    pairPathMass (lift2 (eliminateSig hp) q.1 q.2) ≤
        pairPathMass (q.1, q.2) := row_eliminate_mass hp q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_seamMoveSourceAuth_pairMass_pair {ψ : Nat} (hp : ψ > 0) (c : SeamCfg) (q : AuthState ψ × AuthState ψ) :
    pairPathMass (seamMoveSourceAuth hp c q.1 q.2) ≤ pairPathMass q := by
  calc
    pairPathMass (seamMoveSourceAuth hp c q.1 q.2) ≤
        pairPathMass (q.1, q.2) :=
      seamMoveSourceAuth_pairPathMass hp c q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_dropStale_pairMass_pair {ψ : Nat} (q : AuthState ψ × AuthState ψ) :
    pairPathMass
        (liftLife PPLLBirthPatchM2.dropStale q.1,
         liftLife PPLLBirthPatchM2.dropStale q.2) ≤ pairPathMass q := by
  calc
    pairPathMass
        (liftLife PPLLBirthPatchM2.dropStale q.1,
         liftLife PPLLBirthPatchM2.dropStale q.2) ≤
        pairPathMass (q.1, q.2) := suffix_dropStale_pairMass q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_preCheckReset_pairMass_pair {ψ : Nat} (q : AuthState ψ × AuthState ψ) :
    pairPathMass (preCheckResetAuth q.1 q.2) ≤ pairPathMass q := by
  calc
    pairPathMass (preCheckResetAuth q.1 q.2) ≤
        pairPathMass (q.1, q.2) := suffix_preCheckReset_pairMass q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_normalizeReady_pairMass_pair {ψ : Nat}
    (q : AuthState ψ × AuthState ψ) :
    pairPathMass (liftLife normalizeReady q.1, liftLife normalizeReady q.2) =
      pairPathMass q := by
  calc
    pairPathMass (liftLife normalizeReady q.1, liftLife normalizeReady q.2) =
        pairPathMass (q.1, q.2) := suffix_normalizeReady_pairMass q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_checkSource_pairMass_pair {ψ : Nat}
    (hψ : ψ > 0) (c : PPLLAuthF.Cfg)
    (q : AuthState ψ × AuthState ψ) :
    pairPathMass (checkSourceAuth hψ c q.1 q.2) = pairPathMass q := by
  calc
    pairPathMass (checkSourceAuth hψ c q.1 q.2) =
        pairPathMass (q.1, q.2) := suffix_checkSource_pairMass hψ c q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_champDisappear_pairMass_pair {ψ : Nat}
    (hψ : ψ > 0) (cc : ChampCfg) (hcc : cc.lotteryScrub = true)
    (q : AuthState ψ × AuthState ψ) :
    pairPathMass (champDisappearAuth hψ cc q.1 q.2) = pairPathMass q := by
  calc
    pairPathMass (champDisappearAuth hψ cc q.1 q.2) =
        pairPathMass (q.1, q.2) :=
      suffix_champDisappear_pairMass hψ cc hcc q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_seamRepair_pairMass_pair {ψ : Nat}
    (c : SeamCfg) (q : AuthState ψ × AuthState ψ) :
    pairPathMass (seamRepairAuth c q.1 q.2) = pairPathMass q := by
  calc
    pairPathMass (seamRepairAuth c q.1 q.2) =
        pairPathMass (q.1, q.2) := suffix_seamRepair_pairMass c q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_compareLifecycle_pairMass_pair {ψ : Nat}
    (κ : Nat) (c : SeamCfg) (q : AuthState ψ × AuthState ψ) (er : Fin 3) :
    pairPathMass (compareLifecycleE κ c q.1 q.2 er).1 ≤ pairPathMass q := by
  calc
    pairPathMass (compareLifecycleE κ c q.1 q.2 er).1 ≤
        pairPathMass (q.1, q.2) :=
      suffix_compareLifecycle_pairMass κ c q.1 q.2 er
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_suppress_pairMass_pair {ψ : Nat}
    (hψ : ψ > 0) (q : AuthState ψ × AuthState ψ) :
    pairPathMass (suppressSigResetKillAuth hψ q.1 q.2) ≤ pairPathMass q := by
  calc
    pairPathMass (suppressSigResetKillAuth hψ q.1 q.2) ≤
        pairPathMass (q.1, q.2) := suffix_suppress_pairMass hψ q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_k4_pairMass_pair {ψ : Nat}
    (hψ : ψ > 0) (q : AuthState ψ × AuthState ψ) :
    pairPathMass (lift2 (k4Kernel hψ) q.1 q.2) = pairPathMass q := by
  calc
    pairPathMass (lift2 (k4Kernel hψ) q.1 q.2) =
        pairPathMass (q.1, q.2) := suffix_k4_pairMass hψ q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option Elab.async false in
private theorem q21003_suffix_writeWithBundle_pairMass_pair {ψ : Nat}
    (hψ : ψ > 0) (q : AuthState ψ × AuthState ψ) :
    pairPathMass (lift2 (writeWithBundle hψ) q.1 q.2) = pairPathMass q := by
  calc
    pairPathMass (lift2 (writeWithBundle hψ) q.1 q.2) =
        pairPathMass (q.1, q.2) :=
      suffix_writeWithBundle_pairMass hψ q.1 q.2
    _ = pairPathMass q := q21003_pairPathMass_eta q
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
set_option Elab.async false in
/-- One literal EpisodeCap row weakly decreases occupied main paths.  The
post-P′ head-start guard is obtained from the original pair because P′ only
changes probes on a correctly labelled leaderless pair.  All later cuts are
composed in their source order; the initial follower facts also disable
conservation's replacement branch. -/
theorem seamStepE_sVplusE_pairPathMass (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (el er : Fin 3)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hlab : r.core.label.val = (l.core.label.val + 1) % ψ)
    (hhead : l.core.label = (⟨0, hp⟩ : Fin ψ) → l.core.path ≠ .bot)
    (hlp : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrp : r.core.state ≠ .produce) (hrd : r.core.state ≠ .done) :
    pairPathMass (seamStepE hp κ sVplusE l r el er).1 ≤
      pairPathMass (l, r) := by
  /- Compile the order reasoning before introducing any reducible row state.
     These parameters are opaque Nats, so neither proof can zeta-unfold q1–q18. -/
  have suffix_chain :
      ∀ m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 : Nat,
        m8 ≤ m7 →
        m9 ≤ m8 →
        m10 = m9 →
        m11 = m10 →
        m12 = m11 →
        m13 = m12 →
        m14 ≤ m13 →
        m15 ≤ m14 →
        m16 = m15 →
        m17 = m16 →
        m18 = m17 →
        m18 ≤ m7 := by
    intro m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18
    intro h8' h9' h10' h11' h12' h13' h14' h15' h16' h17' h18'
    calc
      m18 = m17 := h18'
      _ = m16 := h17'
      _ = m15 := h16'
      _ ≤ m14 := h15'
      _ ≤ m13 := h14'
      _ = m12 := h13'
      _ = m11 := h12'
      _ = m10 := h11'
      _ = m9 := h10'
      _ ≤ m8 := h9'
      _ ≤ m7 := h8'
  have prefix_chain :
      ∀ m0 m1 m2 m3 m4 m5 m6 m7 m18 : Nat,
        m1 = m0 →
        m2 = m1 →
        m3 = m2 →
        m4 ≤ m3 →
        m5 = m4 →
        m6 ≤ m5 →
        m7 ≤ m6 →
        m18 ≤ m7 →
        m18 ≤ m0 := by
    intro m0 m1 m2 m3 m4 m5 m6 m7 m18
    intro h1' h2' h3' h4' h5' h6' h7' hsuffix'
    calc
      m18 ≤ m7 := hsuffix'
      _ ≤ m6 := h7'
      _ ≤ m5 := h6'
      _ = m4 := h5'
      _ ≤ m3 := h4'
      _ = m2 := h3'
      _ = m1 := h2'
      _ = m0 := h1'
  let q1 := lift2 (PPLLPostElectionGuard.pPsiProbeWall hp) l r
  let q2 := genSigAuth hp κ q1.1 q1.2
  let q3 := (hygieneOne sVplusE q2.1, hygieneOne sVplusE q2.2)
  let q4 := seamCleanSourceAuth hp sVplusE q3.1 q3.2
  let q5 := lift2Life (PPLLAstraDesign3.releaseSource hp) q4.1 q4.2
  let q6 := lift2 (eliminateSig hp) q5.1 q5.2
  let q7 := seamMoveSourceAuth hp sVplusE q6.1 q6.2
  let q8 := (liftLife PPLLBirthPatchM2.dropStale q7.1,
             liftLife PPLLBirthPatchM2.dropStale q7.2)
  let q9 := preCheckResetAuth q8.1 q8.2
  let q10 := (liftLife normalizeReady q9.1, liftLife normalizeReady q9.2)
  let q11 := checkSourceAuth hp sVplusE.base q10.1 q10.2
  let q12 := champDisappearAuth hp (toChamp sVplusE) q11.1 q11.2
  let q13 := seamRepairAuth sVplusE q12.1 q12.2
  let q14 := (compareLifecycleE κ sVplusE q13.1 q13.2 er).1
  let q15 := suppressSigResetKillAuth hp q14.1 q14.2
  let q16 := lift2 (k4Kernel hp) q15.1 q15.2
  let q17 := lift2 (writeWithBundle hp) q16.1 q16.2
  let q18 := conserveAuth l r q17
  /- Expose only the pre-K4 prefix equality. -/
  have hprefix :
      (seamBeforeEliminationE hp κ sVplusE l r er).1 = q15 := by

    have hshape :
        seamBeforeEliminationE hp κ sVplusE l r er =
          (let (q, er') :=
             compareLifecycleE κ sVplusE q13.1 q13.2 er
           (suppressSigResetKillAuth hp q.1 q.2, er')) := by
      apply q20991_seamBeforeEliminationE_of_stages
        (hψ := hp) (κ := κ) (c := sVplusE)
        (l := l) (r := r) (er := er)
        (q1 := q1) (q2 := q2) (q3 := q3) (q4 := q4)
        (q5 := q5) (q6 := q6) (q7 := q7) (q8 := q8)
        (q9 := q9) (q10 := q10) (q11 := q11)
        (q12 := q12) (q13 := q13)
      all_goals rfl


    calc
      (seamBeforeEliminationE hp κ sVplusE l r er).1 =
          (let (q, er') :=
             compareLifecycleE κ sVplusE q13.1 q13.2 er
           (suppressSigResetKillAuth hp q.1 q.2, er')).1 := by
        exact congrArg
          (fun z : (AuthState ψ × AuthState ψ) × Fin 3 => z.1)
          hshape
      _ = suppressSigResetKillAuth hp
            (compareLifecycleE κ sVplusE q13.1 q13.2 er).1.1
            (compareLifecycleE κ sVplusE q13.1 q13.2 er).1.2 := by
        exact fst_match_returned_pair_opaque
          (x := compareLifecycleE κ sVplusE q13.1 q13.2 er)
          (f := fun q : AuthState ψ × AuthState ψ =>
            suppressSigResetKillAuth hp q.1 q.2)
      _ = q15 := by
        rfl




  /- Outer factor owns only the post-prefix K4/WRITE/conservation shell. -/
  have hactual : (seamStepE hp κ sVplusE l r el er).1 = q18 := by
    rw [seamStepE_sVplusE_outer_factor hp κ l r el er]
    rw [hprefix]


  obtain ⟨x, y, hprime⟩ :=
    pPsiProbeWall_followers_frame hp l r hl hr hlab
  have h1 : pairPathMass q1 = pairPathMass (l, r) := by
    simp [q1, hprime, pairPathMass, pathMass]
  have hhead1 : q1.1.core.label = (⟨0, hp⟩ : Fin ψ) →
      q1.1.core.path ≠ .bot := by
    simp only [q1, hprime]
    exact hhead
  have hlp1 : q1.1.core.state ≠ .produce := by
    simpa [q1, hprime] using hlp
  have hld1 : q1.1.core.state ≠ .done := by
    simpa [q1, hprime] using hld
  have hrp1 : q1.2.core.state ≠ .produce := by
    simpa [q1, hprime] using hrp
  have hrd1 : q1.2.core.state ≠ .done := by
    simpa [q1, hprime] using hrd
  have h2 : pairPathMass q2 = pairPathMass q1 :=
    row_genSig_mass hp κ q1.1 q1.2 hhead1 hlp1 hld1 hrp1 hrd1
  have h3 : pairPathMass q3 = pairPathMass q2 :=
    hygiene_pairPathMass q2.1 q2.2
  have h4 : pairPathMass q4 ≤ pairPathMass q3 :=
    row_clean_mass hp q3.1 q3.2
  have h5 : pairPathMass q5 = pairPathMass q4 := by
    have h5raw :=
      q21000_row_release_mass_pair (ψ := ψ) hp q4
    change
      pairPathMass
          (lift2Life (PPLLAstraDesign3.releaseSource hp) q4.1 q4.2) =
        pairPathMass q4
    exact h5raw
  have h6 : pairPathMass q6 ≤ pairPathMass q5 :=
    q21003_row_eliminate_mass_pair (ψ := ψ) hp q5
  have h7 : pairPathMass q7 ≤ pairPathMass q6 :=
    q21003_seamMoveSourceAuth_pairMass_pair (ψ := ψ) hp sVplusE q6
  have h8 : pairPathMass q8 ≤ pairPathMass q7 :=
    q21003_suffix_dropStale_pairMass_pair (ψ := ψ) q7
  have h9 : pairPathMass q9 ≤ pairPathMass q8 :=
    q21003_suffix_preCheckReset_pairMass_pair (ψ := ψ) q8
  have h10 : pairPathMass q10 = pairPathMass q9 :=
    q21003_suffix_normalizeReady_pairMass_pair (ψ := ψ) q9
  have h11 : pairPathMass q11 = pairPathMass q10 :=
    q21003_suffix_checkSource_pairMass_pair
      (ψ := ψ) hp sVplusE.base q10
  have h12 : pairPathMass q12 = pairPathMass q11 :=
    q21003_suffix_champDisappear_pairMass_pair
      (ψ := ψ) hp (toChamp sVplusE) (by rfl) q11
  have h13 : pairPathMass q13 = pairPathMass q12 :=
    q21003_suffix_seamRepair_pairMass_pair (ψ := ψ) sVplusE q12
  have h14 : pairPathMass q14 ≤ pairPathMass q13 :=
    q21003_suffix_compareLifecycle_pairMass_pair
      (ψ := ψ) κ sVplusE q13 er
  have h15 : pairPathMass q15 ≤ pairPathMass q14 :=
    q21003_suffix_suppress_pairMass_pair (ψ := ψ) hp q14
  have h16 : pairPathMass q16 = pairPathMass q15 :=
    q21003_suffix_k4_pairMass_pair (ψ := ψ) hp q15
  have h17 : pairPathMass q17 = pairPathMass q16 :=
    q21003_suffix_writeWithBundle_pairMass_pair (ψ := ψ) hp q16
  have h18 : pairPathMass q18 = pairPathMass q17 :=
    suffix_conserve_pairMass l r hl hr q17
  /- Instantiate the already-checked generic suffix theorem explicitly.
     Expected argument types now contain the same local qᵢ fvars as h8–h18,
     so elaboration has no reason to unfold their definitions. -/
  have hsuffix : pairPathMass q18 ≤ pairPathMass q7 :=
    suffix_chain (pairPathMass q7) (pairPathMass q8) (pairPathMass q9)
      (pairPathMass q10) (pairPathMass q11) (pairPathMass q12)
      (pairPathMass q13) (pairPathMass q14) (pairPathMass q15)
      (pairPathMass q16) (pairPathMass q17) (pairPathMass q18)
      h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  have hmass : pairPathMass q18 ≤ pairPathMass (l, r) :=
    prefix_chain (pairPathMass (l, r)) (pairPathMass q1) (pairPathMass q2)
      (pairPathMass q3) (pairPathMass q4) (pairPathMass q5)
      (pairPathMass q6) (pairPathMass q7) (pairPathMass q18)
      h1 h2 h3 h4 h5 h6 h7 hsuffix
  rw [hactual]
  exact hmass



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- Hole-routing Lemma 2, one scheduled row: from the actual HoleSectorE
hypotheses, every physical edge weakly decreases the global number of
occupied main paths.  `ψ ∣ n` handles the wraparound edge, while the sector's
head occupancy and perfect labels block GENSIG head start. -/
theorem holeSector_step_NpathE {n ψ : Nat} (hp : ψ > 0)
    (hd : ψ ∣ n) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3)
    (hs : HoleSectorE κ ring C) (e : Fin n) :
    NpathE ((seamProtocolE hp κ sVplusE).step ring C e) ≤ NpathE C := by
  have hgeom := hs.minimum_hole_geometry hp
  have hn : 1 < n := by
    obtain ⟨hpos, g, hb, _, _, _⟩ := hgeom
    omega
  have hlab := PL_adjacent_labels hd ring C hs.pl e
  have hhead := PL_occupied_zero_label hp C hs.pl hs.headsOccupied e
  have hpair := seamStepE_sVplusE_pairPathMass hp κ
    (C e).1 (C (ring.rightNeighbor e)).1
    (C e).2 (C (ring.rightNeighbor e)).2
    (hs.ll e) (hs.ll (ring.rightNeighbor e)) hlab hhead
    (hs.noProduce e) (hs.noDone e)
    (hs.noProduce (ring.rightNeighbor e)) (hs.noDone (ring.rightNeighbor e))
  exact seam_step_NpathE_of_pair hp κ sVplusE ring hn C e hpair

#print axioms PPLLAuthHoleRouting.seamStepE_sVplusE_pairPathMass
#print axioms PPLLAuthHoleRouting.holeSector_step_NpathE

end PPLLAuthHoleRouting

