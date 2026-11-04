import Leader.Wu.Authorization.SeamHygiene
import Leader.Wu.Authorization.GenerationDrain
import Leader.Wu.Authorization.BitFrozenCheckpoint
import Leader.Wu.Authorization.BitFrozenClosure

set_option autoImplicit false

namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthGenDrain PPLLAuthSeam

variable {n ψ : Nat}

/-- Total number of occupied main paths, ignoring the episode sidecar. -/
def NpathE (C : Fin n → AuthState ψ × Fin 3) : Nat :=
  (List.ofFn fun i : Fin n => if (C i).1.core.path = .bot then 0 else 1).sum

/-- A hole at physical role `k`, represented by an actual, nonwrapped block cell.
The bound allows a final partial block and does not assume `ψ ∣ n`. -/
def HoleAtRoleE (ring : DirectedRing n) (C : Fin n → AuthState ψ × Fin 3)
    (k : Nat) : Prop :=
  k < ψ ∧ ∃ g, g * ψ + k < n ∧ (C (bcell ring ψ g k)).1.core.path = .bot

/-- Search roles in increasing order below `fuel`. A successful result is the
least physical role seen so far. The finite range makes this independent of
any unbounded minimization API. -/
noncomputable def firstHoleRoleE (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => by
      classical
      exact match firstHoleRoleE ring C fuel with
        | some k => some k
        | none => if HoleAtRoleE ring C fuel then some fuel else none

/-- A successful bounded search returns an actual physical hole role. -/
theorem firstHoleRoleE_spec (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) :
    ∀ {fuel k}, firstHoleRoleE ring C fuel = some k →
      HoleAtRoleE ring C k := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro k h
      simp [firstHoleRoleE] at h
  | succ fuel ih =>
      intro k h
      cases hp : firstHoleRoleE ring C fuel with
      | some j =>
          have hkj : j = k := by
            simpa [firstHoleRoleE, hp] using h
          subst k
          exact ih hp
      | none =>
          by_cases hh : HoleAtRoleE ring C fuel
          · have hkj : fuel = k := by
              simpa [firstHoleRoleE, hp, hh] using h
            subst k
            exact hh
          · simp [firstHoleRoleE, hp, hh] at h

/-- A failed search certifies that every smaller role is occupied. -/
theorem firstHoleRoleE_none (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) :
    ∀ {fuel}, firstHoleRoleE ring C fuel = none →
      ∀ k < fuel, ¬ HoleAtRoleE ring C k := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro h k hk
      omega
  | succ fuel ih =>
      intro h k hk hhole
      cases hp : firstHoleRoleE ring C fuel with
      | some j =>
          simp [firstHoleRoleE, hp] at h
      | none =>
          by_cases hh : HoleAtRoleE ring C fuel
          · simp [firstHoleRoleE, hp, hh] at h
          · by_cases hlt : k < fuel
            · exact ih hp k hlt hhole
            · have heq : k = fuel := by omega
              subst k
              exact hh hhole

/-- A returned role lies inside the searched prefix. -/
theorem firstHoleRoleE_lt (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) :
    ∀ {fuel k}, firstHoleRoleE ring C fuel = some k → k < fuel := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro k h
      simp [firstHoleRoleE] at h
  | succ fuel ih =>
      intro k h
      cases hp : firstHoleRoleE ring C fuel with
      | some j =>
          have hkj : j = k := by
            simpa [firstHoleRoleE, hp] using h
          subst k
          exact Nat.lt_trans (ih hp) (Nat.lt_succ_self fuel)
      | none =>
          by_cases hh : HoleAtRoleE ring C fuel
          · have hkj : fuel = k := by
              simpa [firstHoleRoleE, hp, hh] using h
            subst k
            exact Nat.lt_succ_self fuel
          · simp [firstHoleRoleE, hp, hh] at h

/-- The search result is no larger than any hole in its bounded range. -/
theorem firstHoleRoleE_le (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) :
    ∀ {fuel j k}, firstHoleRoleE ring C fuel = some j →
      k < fuel → HoleAtRoleE ring C k → j ≤ k := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro j k h hk hhole
      omega
  | succ fuel ih =>
      intro j k h hk hhole
      cases hp : firstHoleRoleE ring C fuel with
      | some old =>
          have hjo : old = j := by
            simpa [firstHoleRoleE, hp] using h
          subst j
          by_cases hlt : k < fuel
          · exact ih hp hlt hhole
          · have heq : k = fuel := by omega
            subst k
            exact Nat.le_of_lt (firstHoleRoleE_lt ring C hp)
      | none =>
          by_cases hh : HoleAtRoleE ring C fuel
          · have hj : fuel = j := by
              simpa [firstHoleRoleE, hp, hh] using h
            subst j
            by_cases hlt : k < fuel
            · exact False.elim (firstHoleRoleE_none ring C hp k hlt hhole)
            · have heq : k = fuel := by omega
              subst k
              exact Nat.le_refl fuel
          · simp [firstHoleRoleE, hp, hh] at h

/-- Least physical role of a pathless cell; zero by convention if no hole
exists. All relevant roles are below `ψ`, so the search is finite. -/
noncomputable def HE (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) : Nat := by
  classical
  exact (firstHoleRoleE ring C ψ).getD 0


/-- The zero-leader hole sector: the existing A0 predicates on the AuthState
projection, domain membership, generation-free main states, occupied physical
heads, and at least one missing main path. CLEAN records remain arbitrary. -/
structure HoleSectorE (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) : Prop where
  ll : PPLLAuthStage12.LL (fun i => (C i).1)
  rf : PPLLAuthStage12.RF (fun i => (C i).1)
  lbf : PPLLAuthBitFrozen.LBF (fun i => (C i).1)
  pl : PPLLAuthBitFrozen.PL (fun i => (C i).1)
  domain : ∀ i, AgentState.inProtocolDomain κ (C i).1.core
  noProduce : ∀ i, (C i).1.core.state ≠ .produce
  noDone : ∀ i, (C i).1.core.state ≠ .done
  headsOccupied : ∀ i, i.val % ψ = 0 → (C i).1.core.path ≠ .bot
  holeExists : ∃ i, (C i).1.core.path = .bot

/-- Every physical hole has a within-block role represented by `bcell`. -/
theorem holeAtRoleE_exists (hp : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3) (h : ∃ i, (C i).1.core.path = .bot) :
    ∃ k, HoleAtRoleE ring C k := by
  obtain ⟨i, hi⟩ := h
  have he : i.val / ψ * ψ + i.val % ψ = i.val := by
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i.val ψ
  refine ⟨i.val % ψ, Nat.mod_lt _ hp, i.val / ψ, ?_, ?_⟩
  · rw [he]
    exact i.isLt
  · have hc : bcell ring ψ (i.val / ψ) (i.val % ψ) = i := by
      apply Fin.ext
      change (i.val / ψ * ψ + i.val % ψ) % n = i.val
      rw [he, Nat.mod_eq_of_lt i.isLt]
    simpa only [hc] using hi



/-- The bounded search attains a hole whenever one exists. -/
theorem HE_spec (ring : DirectedRing n) (C : Fin n → AuthState ψ × Fin 3)
    (h : ∃ k, HoleAtRoleE ring C k) : HoleAtRoleE ring C (HE ring C) := by
  classical
  obtain ⟨k, hk⟩ := h
  have hlt : k < ψ := hk.1
  cases hs : firstHoleRoleE ring C ψ with
  | none =>
      exact False.elim (firstHoleRoleE_none ring C hs k hlt hk)
  | some j =>
      simpa [HE, hs] using
        (firstHoleRoleE_spec ring C hs)

/-- Every physical hole role is at least the selected role. -/
theorem HE_le (ring : DirectedRing n) (C : Fin n → AuthState ψ × Fin 3)
    {k : Nat} (hk : HoleAtRoleE ring C k) : HE ring C ≤ k := by
  classical
  cases hs : firstHoleRoleE ring C ψ with
  | none =>
      exact False.elim (firstHoleRoleE_none ring C hs k hk.1 hk)
  | some j =>
      simpa [HE, hs] using
        (firstHoleRoleE_le ring C hs hk.1 hk)

/-- Hole-routing Lemma 1: the minimum hole is not a physical head; its immediate
physical predecessor is occupied. The proof uses only the occupied-head and
hole hypotheses, and the existing `rn_bcell` ring arithmetic. -/
theorem minimum_hole_geometry (hp : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ × Fin 3)
    (heads : ∀ i, i.val % ψ = 0 → (C i).1.core.path ≠ .bot)
    (holes : ∃ i, (C i).1.core.path = .bot) :
    0 < HE ring C ∧ ∃ g,
      g * ψ + HE ring C < n ∧
      (C (bcell ring ψ g (HE ring C))).1.core.path = .bot ∧
      (C (bcell ring ψ g (HE ring C - 1))).1.core.path ≠ .bot ∧
      ring.rightNeighbor (bcell ring ψ g (HE ring C - 1)) =
        bcell ring ψ g (HE ring C) := by
  obtain ⟨hk, g, hbound, hhole⟩ := HE_spec ring C (holeAtRoleE_exists hp ring C holes)
  have hpos : 0 < HE ring C := by
    by_cases hz : HE ring C = 0
    · exfalso
      have hhead : (bcell ring ψ g (HE ring C)).val % ψ = 0 := by
        change ((g * ψ + HE ring C) % n) % ψ = 0
        rw [Nat.mod_eq_of_lt hbound, bcell_mod g (HE ring C) hk, hz]
      exact heads _ hhead hhole
    · omega
  refine ⟨hpos, g, hbound, hhole, ?_, ?_⟩
  · intro hprev
    have hrole : HoleAtRoleE ring C (HE ring C - 1) :=
      ⟨by omega, g, by omega, hprev⟩
    have hmin := HE_le ring C hrole
    omega
  · rw [rn_bcell]
    congr 1
    omega

/-- The hole-sector hypotheses supply the geometry required by the router. -/
theorem HoleSectorE.minimum_hole_geometry {κ : Nat} (hp : 0 < ψ)
    {ring : DirectedRing n} {C : Fin n → AuthState ψ × Fin 3}
    (h : HoleSectorE κ ring C) :
    0 < HE ring C ∧ ∃ g,
      g * ψ + HE ring C < n ∧
      (C (bcell ring ψ g (HE ring C))).1.core.path = .bot ∧
      (C (bcell ring ψ g (HE ring C - 1))).1.core.path ≠ .bot ∧
      ring.rightNeighbor (bcell ring ψ g (HE ring C - 1)) =
        bcell ring ψ g (HE ring C) :=
  PPLLAuthHoleRouting.minimum_hole_geometry hp ring C h.headsOccupied h.holeExists

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.holeAtRoleE_exists
#print axioms PPLLAuthHoleRouting.HE_spec
#print axioms PPLLAuthHoleRouting.HE_le
#print axioms PPLLAuthHoleRouting.minimum_hole_geometry
#print axioms PPLLAuthHoleRouting.HoleSectorE.minimum_hole_geometry


namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLAuthSeam

/-!
A source-level counterexample to hole-routing Lemma 7.
The crucial cut is MOVE's final READY release, before stale-drop.
-/

/-- Empty neutral cell with all registers specified, used to expose every
assumption of the three-cell counterexample. -/
def staleEscapeBase (label : Fin 3) : AuthState 3 :=
  { core := {
      leader := false, probe := false, phase := false, bit := false,
      wait := false, state := .depart, path := .bot, reset := false,
      carry := false, count := 0, label := label, h_field := false,
      path2 := none, path3 := none, path4 := none, path5 := none,
      p := false, p_carry := false, reset_cmd := false, echo := false,
      signal_B := 0, bullet := 0, shield := false,
      write_state := .none, write := .none, last := false,
      last_set := false, last_unset := false, b_carry := false,
      gen_ws := false, ws_echo := false, signal_ws := false },
    path_mark := 0, ctrl_mark := 0, path2_scope := .line,
    path2_mark := 0, path4_mark := 0, path5_mark := 0 }

/-- Misaligned blocking sender: physical role 1 carries logical label 0. -/
def staleEscapeLeft : AuthState 3 :=
  let u := staleEscapeBase 1
  { u with core := { u.core with path := .some 0 0, state := .CHECK_ready } }

/-- Minimum hole, at role 2; its legal pathless depart state triggers release. -/
def staleEscapeRight : AuthState 3 := staleEscapeBase 2

/-- Full three-cell input: role 0 is occupied, so the sole hole has minimum role 2. -/
def staleEscapeConfig (i : Fin 3) : AuthState 3 × Fin 3 :=
  if i.val = 0 then
    let u := staleEscapeBase 0
    ({ u with core := { u.core with path := .some 0 0 } }, 0)
  else if i.val = 1 then (staleEscapeLeft, 0)
  else (staleEscapeRight, 0)

/-- The ring used by the witness. -/
theorem staleEscapeRing : DirectedRing 3 := ⟨by omega⟩

/-- CLEAN merely transports an ordinary witness; the main path survives. -/
def staleEscapeAfterClean : AuthState 3 × AuthState 3 :=
  seamCleanSourceAuth (by omega) sVplusE staleEscapeLeft staleEscapeRight

/-- The precise MOVE cut where READY becomes depart before stale-drop. -/
def staleEscapeAfterMove : AuthState 3 × AuthState 3 :=
  seamMoveSourceAuth (by omega) sVplusE
    staleEscapeAfterClean.1 staleEscapeAfterClean.2

/-- Source counterexample's decisive stage: the blocking state is gone while
its misaligned main path remains. This draft still needs kernel verification. -/
theorem staleEscape_move_projection :
    (staleEscapeAfterMove.1.core.path,
      staleEscapeAfterMove.1.core.state,
      staleEscapeAfterMove.2.core.path) =
      (.some 0 0, .depart, .bot) := by
  rfl

/-- Stale-drop is ineffective after MOVE's release. -/
theorem staleEscape_drop_projection :
    (PPLLBirthPatchM2.dropStale staleEscapeAfterMove.1.core).path = .some 0 0 := by
  rfl

/-- The requested completed row, retained as data for remote evaluation. -/
def staleEscapeRow :=
  seamStepE (by omega : 3 > 0) 0 sVplusE
    staleEscapeLeft staleEscapeRight 0 0

/-- Observable endpoint intended for a separate staged remote check:
expected `(.some 0 0, .depart, false, .bot, false)`.
This definition asserts no unverified full-row theorem. -/
def staleEscapeEndpoint :=
  (staleEscapeRow.1.1.core.path, staleEscapeRow.1.1.core.state,
   staleEscapeRow.1.1.core.leader, staleEscapeRow.1.2.core.path,
   staleEscapeRow.1.2.core.leader)

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.staleEscape_move_projection
#print axioms PPLLAuthHoleRouting.staleEscape_drop_projection


namespace PPLLAuthHoleRouting

open PPLL PPLLAuthF PPLLBirthPatchM2

/-- At the Step1 cut, a nonblocking occupied sender transfers its main path into
an empty nonproducer. This is a stage lemma, not a completed-row assertion. -/
theorem step1Auth_transfer {ψ : Nat} (l r : AuthState ψ) (pl bit : Nat)
    (hl : l.core.path = .some pl bit) (hr : r.core.path = .bot)
    (hb : blockingState l.core = false)
    (ho : PPLLFableZDiv.outcomePending false l.core = false)
    (hp : r.st ≠ MainState.produce) :
    (step1Auth l r).1.core.path = .bot ∧
      (step1Auth l r).2.core.path = l.core.path := by
  simp [step1Auth, hl, hr, hb, ho, hp]

/-- At the stale-drop cut, a misaligned blocking holder loses its main path.
The blocking assumption is needed at this cut: MOVE can demote an input READY
holder to depart when its pathless successor is in depart. -/
theorem dropStale_path_bot {ψ : Nat} (u : AgentState ψ)
    (hp : u.path ≠ .bot) (ha : aligned u = false)
    (hb : blockingState u = true) :
    (dropStale u).path = .bot := by
  simp [dropStale, hp, ha, hb]

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.step1Auth_transfer
#print axioms PPLLAuthHoleRouting.dropStale_path_bot

namespace PPLLAuthHoleRouting
open PPLL PPLLAuthF PPLLAuthSeam PPLLPostElectionGuard PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthChamp

/-! Concrete source-row replay, retaining the actual stage ordering. -/

private def escapeView (q : AuthState 3 × AuthState 3) :=
  (q.1.core.path, q.1.core.state, q.1.core.leader,
   q.2.core.path, q.2.core.leader)

private def escape0 : AuthState 3 × AuthState 3 :=
  (staleEscapeLeft, staleEscapeRight)
private def escape1 := lift2 (pPsiProbeWall (by omega : 3 > 0)) escape0.1 escape0.2
private def escape2 := genSigAuth (by omega : 3 > 0) 0 escape1.1 escape1.2
private def escape3 := (hygieneOne sVplusE escape2.1, hygieneOne sVplusE escape2.2)
private def escape4 := seamCleanSourceAuth (by omega : 3 > 0) sVplusE escape3.1 escape3.2
private def escape5 := lift2Life (releaseSource (by omega : 3 > 0)) escape4.1 escape4.2
private def escape6 := lift2 (eliminateSig (by omega : 3 > 0)) escape5.1 escape5.2
private def escape7 := seamMoveSourceAuth (by omega : 3 > 0) sVplusE escape6.1 escape6.2
private def escape8 := (liftLife PPLLBirthPatchM2.dropStale escape7.1,
                       liftLife PPLLBirthPatchM2.dropStale escape7.2)
private def escape9 := preCheckResetAuth escape8.1 escape8.2
private def escape10 := (liftLife normalizeReady escape9.1,
                        liftLife normalizeReady escape9.2)
private def escape11 := checkSourceAuth (by omega : 3 > 0) sVplusE.base escape10.1 escape10.2
private def escape12 := champDisappearAuth (by omega : 3 > 0) (toChamp sVplusE) escape11.1 escape11.2
private def escape13 := seamRepairAuth sVplusE escape12.1 escape12.2
private def escape14 := (compareLifecycleE 0 sVplusE escape13.1 escape13.2 0).1
private def escape15 := suppressSigResetKillAuth (by omega : 3 > 0) escape14.1 escape14.2
private def escape16 := lift2 (k4Kernel (by omega : 3 > 0)) escape15.1 escape15.2
private def escape17 := lift2 (writeWithBundle (by omega : 3 > 0)) escape16.1 escape16.2
private def escape18 := conserveAuth staleEscapeLeft staleEscapeRight escape17

/-- The actual prefix reaches the surviving misaligned depart view. Earlier
WAIT/GENSIG stages may change ancillary registers, so no whole-cell equality
with the isolated CLEAN/MOVE test is assumed. -/
private theorem escape7_view :
    escapeView escape7 = (.some 0 0, .depart, false, .bot, false) := by
  rfl

/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape8_view : escapeView escape8 = escapeView escape7 := by rfl
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape9_view : escapeView escape9 = escapeView escape8 := by rfl
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape10_view : escapeView escape10 = escapeView escape9 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape11_view : escapeView escape11 = escapeView escape10 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape12_view : escapeView escape12 = escapeView escape11 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape13_view : escapeView escape13 = escapeView escape12 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape14_view : escapeView escape14 = escapeView escape13 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape15_view : escapeView escape15 = escapeView escape14 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape16_view : escapeView escape16 = escapeView escape15 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape17_view : escapeView escape17 = escapeView escape16 := by rfl
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The concrete stage preserves the path/state/leader view of its preceding cut. -/
private theorem escape18_view : escapeView escape18 = escapeView escape17 := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- Factor the actual completed row into its explicit stage composition. -/
private theorem escape_row_cut : staleEscapeRow.1 = escape18 := by rfl

/-- In the actual `seamStepE` row, MOVE releases the blocking sender before
stale drop; the misaligned path survives through the remaining stages. -/
theorem staleEscape_endpoint_replay :
    staleEscapeEndpoint = (.some 0 0, .depart, false, .bot, false) := by
  change escapeView staleEscapeRow.1 = _
  rw [escape_row_cut, escape18_view, escape17_view, escape16_view,
      escape15_view, escape14_view, escape13_view, escape12_view,
      escape11_view, escape10_view, escape9_view, escape8_view,
      escape7_view]


#print axioms escape7_view
#print axioms escape8_view
#print axioms escape9_view
#print axioms escape10_view
#print axioms escape11_view
#print axioms escape12_view
#print axioms escape13_view
#print axioms escape14_view
#print axioms escape15_view
#print axioms escape16_view
#print axioms escape17_view
#print axioms escape18_view
#print axioms escape_row_cut
#print axioms staleEscape_endpoint_replay

end PPLLAuthHoleRouting

#print axioms PPLLAuthHoleRouting.firstHoleRoleE_spec
#print axioms PPLLAuthHoleRouting.firstHoleRoleE_none
#print axioms PPLLAuthHoleRouting.firstHoleRoleE_lt
#print axioms PPLLAuthHoleRouting.firstHoleRoleE_le
