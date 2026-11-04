import Leader.Wu.RaceEntrance.ReverseRaceCertificate

/-!
A finite actual-K2 counterexample to the bare fresh-start one-third shield
comparison. The recovery and attack lengths are 2 and 3 on seven cells.
A real two-edge prehistory starts from two clean gaps. The separate finite
certificate checks every raw scheduler edge and all physical registers.

The audit stops at first arrival or tagged deletion. Its success records a
protected arrival. The proved strict two-thirds bound concerns that audit;
it places no lower bound on the protocol's eventual deletion time.
-/

set_option autoImplicit false
set_option Elab.async false

open PPLLRepair LDSinkKernelC LDSinkGapCleanup LDSinkProtectedAbsorption
open LDSinkTwoGapRaceEntranceColourCoupling LDSinkTwoGapRaceEntranceLocalService

namespace LDSinkTwoGapRaceEntranceReverseRace

open FiniteUniformStoppingTree LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapReachInvariant Certificate

/-! The input is the actual two-edge successor of two clean real gaps.
All three finite prefixes are checked against the imported gap predicates. -/

/-- The literal scheduler prehistory, with no state reset. -/
def prehistory : List (Fin 7) := [2, 5]

def physicalRun (C : Config) (es : List (Fin 7)) : Config := es.foldl physicalStep C

private def history (t : Fin 3) : Config :=
  if t = 0 then seed else if t = 1 then physicalStep seed 2 else initial

private def witnessGap (g : Fin 2) : GapFrame 7 :=
  if g = 0 then frame.recovery else frame.attack

private theorem finite_gap_invariant (G : GapFrame 7) (C : Config)
    (hd : G.d ≤ 3) (he : GapEndpointsPresent G C)
    (hi : ∀ k : Fin 4, 1 ≤ k.val → k.val < G.d → (C (G.pos k.val)).leader = false)
    (hs : ∀ k j : Fin 4, 1 ≤ k.val → k.val ≤ G.d →
      (C (G.pos k.val)).bullet ≠ (0 : Fin 3) → k.val ≤ j.val → j.val ≤ G.d →
      (C (G.pos j.val)).signal_B = (0 : Fin 2)) :
    GapInvariant (by decide) G C := by
  refine ⟨he, ?_, ?_, ?_⟩
  · intro k hk hkd
    exact hi ⟨k, by omega⟩ hk hkd
  · intro k _
    exact Subsingleton.elim _ _
  · intro k j hk hkd hb hkj hjd
    exact hs ⟨k, by omega⟩ ⟨j, by omega⟩ hk hkd hb hkj hjd

private theorem history_checked_00 :
    GapInvariant (by decide) (witnessGap 0) (history 0) :=
  finite_gap_invariant (witnessGap 0) (history 0) (by decide) (by unfold GapEndpointsPresent; decide) (by decide) (by decide)

private theorem history_checked_01 :
    GapInvariant (by decide) (witnessGap 1) (history 0) :=
  finite_gap_invariant (witnessGap 1) (history 0) (by decide) (by unfold GapEndpointsPresent; decide) (by decide) (by decide)

private theorem history_checked_10 :
    GapInvariant (by decide) (witnessGap 0) (history 1) :=
  finite_gap_invariant (witnessGap 0) (history 1) (by decide) (by unfold GapEndpointsPresent; decide) (by decide) (by decide)

private theorem history_checked_11 :
    GapInvariant (by decide) (witnessGap 1) (history 1) :=
  finite_gap_invariant (witnessGap 1) (history 1) (by decide) (by unfold GapEndpointsPresent; decide) (by decide) (by decide)

private theorem history_checked_20 :
    GapInvariant (by decide) (witnessGap 0) (history 2) :=
  finite_gap_invariant (witnessGap 0) (history 2) (by decide) (by unfold GapEndpointsPresent; decide) (by decide) (by decide)

private theorem history_checked_21 :
    GapInvariant (by decide) (witnessGap 1) (history 2) :=
  finite_gap_invariant (witnessGap 1) (history 2) (by decide) (by unfold GapEndpointsPresent; decide) (by decide) (by decide)

private theorem history_invariant : (t : Fin 3) → (g : Fin 2) →
    GapInvariant (by decide) (witnessGap g) (history t) :=
  (Fin.cases (Fin.cases history_checked_00 (Fin.cases history_checked_01 (fun g => g.elim0))) (Fin.cases (Fin.cases history_checked_10 (Fin.cases history_checked_11 (fun g => g.elim0))) (Fin.cases (Fin.cases history_checked_20 (Fin.cases history_checked_21 (fun g => g.elim0))) (fun t => t.elim0))))

private theorem history_gapPair (t : Fin 3) (phase : APhase) :
    GapPair (by decide) frame ⟨history t, phase⟩ :=
  ⟨history_invariant t 0, history_invariant t 1⟩

/-- Every real prefix of `[2,5]` satisfies both actual gap invariants, on
any ghost phase. No endpoint, interior, or signal-order clause is omitted. -/
theorem prehistory_gapPair (t : Fin 3) (phase : APhase) :
    GapPair (by decide) frame ⟨physicalRun seed (prehistory.take t.val), phase⟩ := by
  have he : physicalRun seed (prehistory.take t.val) = history t := by
    have hh : ∀ t : Fin 3, ∀ i : Fin 7,
        physicalRun seed (prehistory.take t.val) i = history t i := by decide
    exact funext (hh t)
  rw [he]
  exact history_gapPair t phase

/-- There are exactly the three tagged leaders throughout the real
prehistory, including the cell outside the two displayed positive sectors. -/
theorem prehistory_leader_sites (t : Fin 3) (i : Fin 7) :
    (physicalRun seed (prehistory.take t.val) i).leader = true ↔
      i = 0 ∨ i = 2 ∨ i = 5 := by
  have h : ∀ t : Fin 3, ∀ i : Fin 7,
      (physicalRun seed (prehistory.take t.val) i).leader = true ↔
        i = 0 ∨ i = 2 ∨ i = 5 := by decide
  exact h t i

/-- The initial recovery and attack sectors are both genuinely clean. -/
theorem seed_clean : CleanReady frame.recovery seed ∧ CleanReady frame.attack seed := by
  have hb : ∀ i : Fin 7, (seed i).bullet = (0 : Fin 3) := by decide
  exact ⟨⟨by decide, fun k _ _ => hb _⟩, ⟨by decide, fun k _ _ => hb _⟩⟩

theorem exact_prehistory : physicalRun seed prehistory = initial := rfl

/-- The second edge is a real outgoing FIRE from a still-clean attack gap,
and therefore supplies the imported exact fresh-shot entrance. -/
theorem initial_fresh : AttemptEntrance (by decide) frame ⟨initial, .transit⟩ := by
  have hc : CleanReady frame.attack (physicalStep seed 2) := by
    refine ⟨by decide, ?_⟩
    have hb : ∀ k : Fin 4, 1 ≤ k.val → k.val ≤ frame.attack.d →
        (physicalStep seed 2 (frame.attack.pos k.val)).bullet = (0 : Fin 3) := by decide
    intro k hk hkd
    exact hb ⟨k, by change k ≤ 3 at hkd; omega⟩ hk hkd
  have hg : GapPair (by decide) frame ⟨physicalStep seed 2, .transit⟩ :=
    history_gapPair 1 .transit
  have hf := clean_outgoing_attemptEntrance (by decide) frame
    ⟨physicalStep seed 2, .transit⟩ hg hc
  have he : attemptStepConf (by decide) frame ⟨physicalStep seed 2, .transit⟩
      (frame.attack.pos frame.attack.d) = initial := by
    rw [attemptStepConf_eq_sinkStepC]
    rfl
  simpa only [he] using hf

/-- The two real lengths have the orientation under audit; initially no
arrival or deletion has occurred and the shared leader is protected. -/
theorem initial_geometry_and_status :
    frame.recovery.d = 2 ∧ frame.attack.d = 3 ∧
    frame.recovery.d < frame.attack.d ∧
    ¬ NoResetSuccess frame initial ∧ (initial 3).bullet = (0 : Fin 3) ∧
    (initial 2).shield = true := by
  refine ⟨rfl, rfl, by decide, ?_, by decide, by decide⟩
  unfold NoResetSuccess EndpointDeleted
  decide

/-! StopNode meanings refer to actual endpoint bits and the unchanged K2
configuration. The audit has different terminal names from a deletion tree. -/

private theorem deleted_iff (C : Config) :
    NoResetSuccess frame C ↔
      (C 0).leader = false ∨ (C 2).leader = false ∨ (C 5).leader = false := by
  change ((C 2).leader = false ∨ (C 5).leader = false) ∨
      ((C 0).leader = false ∨ (C 2).leader = false) ↔ _
  constructor
  · rintro ((h | h) | (h | h))
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact .inl h
    · exact .inr (.inl h)
  · rintro (h | h | h)
    · exact .inr (.inl h)
    · exact .inl (.inl h)
    · exact .inl (.inr h)

/-- Audit success is exactly protected live arrival with all tagged leaders
still present. It is not the protocol's deletion success. -/
theorem audit_success_iff (C : Config) (e : Fin 7) :
    auditStep C e = .success ↔
      ¬ NoResetSuccess frame (physicalStep C e) ∧
      (physicalStep C e 3).bullet = (2 : Fin 3) ∧
      (physicalStep C e 2).shield = true := by
  classical
  unfold auditStep
  dsimp only
  rw [deleted_iff]
  by_cases hd : (physicalStep C e 0).leader = false ∨
      (physicalStep C e 2).leader = false ∨ (physicalStep C e 5).leader = false <;>
    by_cases hb : (physicalStep C e 3).bullet = (2 : Fin 3) <;>
    cases hs : (physicalStep C e 2).shield <;> simp [hd, hb]

/-- Audit failure includes every tagged deletion and every unshielded live
arrival; it therefore favors the proposed one-third alternative. -/
theorem audit_failure_iff (C : Config) (e : Fin 7) :
    auditStep C e = .failure ↔
      NoResetSuccess frame (physicalStep C e) ∨
      ((physicalStep C e 3).bullet = (2 : Fin 3) ∧
       (physicalStep C e 2).shield = false) := by
  classical
  unfold auditStep
  dsimp only
  rw [deleted_iff]
  by_cases hd : (physicalStep C e 0).leader = false ∨
      (physicalStep C e 2).leader = false ∨ (physicalStep C e 5).leader = false <;>
    by_cases hb : (physicalStep C e 3).bullet = (2 : Fin 3) <;>
    cases hs : (physicalStep C e 2).shield <;> simp [hd, hb]

/-- An active edge preserves precisely the physical post-configuration and
has neither reached the attack front nor deleted a tagged endpoint. -/
theorem audit_active_iff (C D : Config) (e : Fin 7) :
    auditStep C e = .active D ↔
      D = physicalStep C e ∧ ¬ NoResetSuccess frame (physicalStep C e) ∧
      (physicalStep C e 3).bullet ≠ (2 : Fin 3) := by
  unfold auditStep
  dsimp only
  rw [deleted_iff]
  by_cases hd : (physicalStep C e 0).leader = false ∨
      (physicalStep C e 2).leader = false ∨ (physicalStep C e 5).leader = false
  · simp [hd]
  · rw [if_neg hd]
    by_cases hb : (physicalStep C e 3).bullet = (2 : Fin 3)
    · rw [if_pos hb]
      cases hs : (physicalStep C e 2).shield <;> simp [hb]
    · rw [if_neg hb]
      constructor
      · intro h
        exact ⟨(StopNode.active.inj h).symm, hd, hb⟩
      · rintro ⟨rfl, _, _⟩
        rfl

/-! The finite data above carry only checked arithmetic and exact physical
rows. The following induction turns them into an original-scheduler word
count. Success in this audit means protected arrival, not deletion. -/

private def graphSum (w : Index → Nat) : Nat → Index → Nat
  | 0, i => w i
  | T + 1, i => (List.ofFn (fun e : Fin 7 => graphSum w T (next i e))).sum

private theorem graphSum_physical (w : StopNode Config → Nat) (T : Nat) (i : Index) :
    graphSum (fun j => w (state j)) T i = treeWeight auditStep w (state i) T := by
  induction T generalizing i with
  | zero => rfl
  | succ T ih =>
      simp only [graphSum, treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, rows]

private theorem value_growth (T : Nat) (i : Index) :
    7 ^ T * value i ≤ graphSum value T i := by
  induction T generalizing i with
  | zero => simp only [graphSum, Nat.pow_zero, Nat.one_mul, Nat.le_refl]
  | succ T ih =>
      rw [Nat.pow_succ, Nat.mul_assoc]
      calc
        7 ^ T * (7 * value i) ≤
            7 ^ T * (List.ofFn (fun e : Fin 7 => value (next i e))).sum :=
          Nat.mul_le_mul_left _ (value_row i)
        _ = (List.ofFn (fun e : Fin 7 => 7 ^ T * value (next i e))).sum :=
          (ofFn_sum_mul_left _ _).symm
        _ ≤ graphSum value (T + 1) i := ofFn_sum_le _ _ (fun e => ih (next i e))

private theorem value_ceiling_graph (T : Nat) (i : Index) :
    graphSum value T i ≤ scale *
      (graphSum (fun j => successWeight (state j)) T i +
       graphSum (fun j => activeWeight (state j)) T i) := by
  induction T generalizing i with
  | zero => exact value_bound i
  | succ T ih =>
      simp only [graphSum]
      calc
        _ ≤ (List.ofFn (fun e : Fin 7 => scale *
          (graphSum (fun j => successWeight (state j)) T (next i e) +
           graphSum (fun j => activeWeight (state j)) T (next i e)))).sum :=
          ofFn_sum_le _ _ (fun e => ih (next i e))
        _ = _ := by rw [ofFn_sum_mul_left, ofFn_sum_add]

private def serviceCaps : Nat → Nat × Nat
  | 0 => (1, 1)
  | T + 1 => (6 * (serviceCaps T).1, 6 * (serviceCaps T).2 + (serviceCaps T).1)

private def activeCap (T : Nat) (i : Index) : Nat :=
  if remaining i = 1 then (serviceCaps T).1
  else if remaining i = 2 then (serviceCaps T).2 else 0

private theorem split_two_values (f : Fin 7 → Nat) (u v : Nat) :
    (List.ofFn (fun e => if f e = 1 then u else if f e = 2 then v else 0)).sum =
      u * (List.ofFn (fun e => if f e = 1 then 1 else 0)).sum +
      v * (List.ofFn (fun e => if f e = 2 then 1 else 0)).sum := by
  calc
    _ = (List.ofFn (fun e => u * (if f e = 1 then 1 else 0) +
          v * (if f e = 2 then 1 else 0))).sum := by
      apply ofFn_sum_eq
      intro e
      by_cases h1 : f e = 1
      · simp [h1]
      · by_cases h2 : f e = 2 <;> simp [h1, h2]
    _ = _ := by rw [ofFn_sum_add, ofFn_sum_mul_left, ofFn_sum_mul_left]

private theorem histogram_linear (r c1 c2 u v : Nat) (hr : r ≤ 2)
    (h1 : c1 ≤ if r = 1 then 6 else if r = 2 then 1 else 0)
    (h2 : c2 ≤ if r = 2 then 6 else 0) :
    u * c1 + v * c2 ≤ if r = 1 then 6 * u else if r = 2 then 6 * v + u else 0 := by
  have hw := Nat.add_le_add (Nat.mul_le_mul_left u h1) (Nat.mul_le_mul_left v h2)
  have he : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases he with rfl | rfl | rfl <;>
    simpa [Nat.mul_comm, Nat.add_comm] using hw

private theorem active_cap_row (T : Nat) (i : Index) :
    (List.ofFn (fun e : Fin 7 => activeCap T (next i e))).sum ≤ activeCap (T + 1) i := by
  have hh := service_histogram i
  unfold activeCap
  rw [split_two_values]
  exact histogram_linear (remaining i) _ _ (serviceCaps T).1 (serviceCaps T).2
    (remaining_bound i) hh.1 hh.2

private theorem active_ceiling (T : Nat) (i : Index) :
    activeCount auditStep (state i) T ≤ activeCap T i := by
  induction T generalizing i with
  | zero =>
      have hb := remaining_bound i
      have he : remaining i = 0 ∨ remaining i = 1 ∨ remaining i = 2 := by omega
      change activeWeight (state i) ≤ _
      rw [active_remaining]
      rcases he with he | he | he <;> simp [he, activeCap, serviceCaps]
  | succ T ih =>
      change (List.ofFn (fun e : Fin 7 =>
        activeCount auditStep (stepNode auditStep (state i) e) T)).sum ≤ _
      calc
        _ = (List.ofFn (fun e : Fin 7 => activeCount auditStep (state (next i e)) T)).sum := by
          apply ofFn_sum_eq
          intro e
          rw [rows]
        _ ≤ (List.ofFn (fun e : Fin 7 => activeCap T (next i e))).sum :=
          ofFn_sum_le _ _ (fun e => ih (next i e))
        _ ≤ _ := active_cap_row T i

private theorem physical_value_flow (T : Nat) (i : Index) :
    7 ^ T * value i ≤ scale *
      (successCount auditStep (state i) T + activeCount auditStep (state i) T) := by
  have h := Nat.le_trans (value_growth T i) (value_ceiling_graph T i)
  rw [graphSum_physical successWeight T i, graphSum_physical activeWeight T i] at h
  exact h

private theorem subtract_active (v c s a : Nat) (hv : v ≤ s + a) (ha : a ≤ c) :
    v - c ≤ s := by omega

private theorem complementary_count (N a s f : Nat)
    (hp : a + s + f = N) (hm : 2 * N < 3 * s) : 3 * (f + a) < N := by omega

set_option maxRecDepth 4096 in
/-- A checked lower bound on protected first-arrival words of length 28.
Every outside edge and every tagged deletion is included in the audit. -/
theorem protected_arrival_mass_lower :
    315424255379213285525511 ≤ successCount auditStep (.active initial) 28 := by
  have hflow := physical_value_flow 28 2
  change scale * value 2 ≤ scale *
    (successCount auditStep (state 2) 28 + activeCount auditStep (state 2) 28) at hflow
  have hv := Nat.le_of_mul_le_mul_left hflow (by decide : 0 < scale)
  have ha := active_ceiling 28 2
  have hc : activeCap 28 2 = 6 ^ 28 + 28 * 6 ^ 27 := by decide
  have ha' : activeCount auditStep (state 2) 28 ≤ 6 ^ 28 + 28 * 6 ^ 27 :=
    Nat.le_trans ha (Nat.le_of_eq hc)
  rw [initial_state] at ha'
  rw [initial_state] at hv
  have hm : value 2 - (6 ^ 28 + 28 * 6 ^ 27) ≤
      successCount auditStep (.active initial) 28 :=
    subtract_active _ _ _ _ hv ha'
  exact hm

/-- The bare fresh-start claim assigning at least one third to unshielded
arrival or earlier deletion is contradicted by this actual finite audit. -/
theorem protected_arrival_mass_gt_two_thirds :
    2 * 7 ^ 28 < 3 * successCount auditStep (.active initial) 28 := by
  have hnum : 2 * 7 ^ 28 < 3 * 315424255379213285525511 := by decide
  exact Nat.lt_of_lt_of_le hnum (Nat.mul_le_mul_left 3 protected_arrival_mass_lower)

/-- Even charging every unfinished word to the favorable alternative leaves
strictly less than one third after 28 original raw scheduler interactions. -/
theorem favorable_or_unfinished_mass_lt_one_third :
    3 * (failureCount auditStep (.active initial) 28 +
      activeCount auditStep (.active initial) 28) < 7 ^ 28 := by
  have hp := node_count_partition auditStep (.active initial) 28
  have hm := protected_arrival_mass_gt_two_thirds
  exact complementary_count _ _ _ _ hp hm

private theorem success_count_step (T : Nat) (x : StopNode Config) :
    7 * successCount auditStep x T ≤ successCount auditStep x (T + 1) := by
  induction T generalizing x with
  | zero =>
      cases x with
      | active C => exact Nat.zero_le _
      | success =>
          simp only [successCount, treeWeight, stepNode, successWeight,
            FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_one, Nat.le_refl]
      | failure =>
          simp only [successCount, treeWeight, stepNode, successWeight,
            FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero, Nat.le_refl]
  | succ T ih =>
      change 7 * (List.ofFn (fun e : Fin 7 =>
        successCount auditStep (stepNode auditStep x e) T)).sum ≤
          (List.ofFn (fun e : Fin 7 =>
            successCount auditStep (stepNode auditStep x e) (T + 1))).sum
      rw [← ofFn_sum_mul_left]
      exact ofFn_sum_le _ _ (fun e => ih (stepNode auditStep x e))

private theorem success_padding (B U : Nat) (x : StopNode Config) :
    7 ^ U * successCount auditStep x B ≤ successCount auditStep x (B + U) := by
  induction U with
  | zero => simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.le_refl]
  | succ U ih =>
      rw [Nat.pow_succ]
      calc
        _ = 7 * (7 ^ U * successCount auditStep x B) := by ac_rfl
        _ ≤ 7 * successCount auditStep x (B + U) := Nat.mul_le_mul_left 7 ih
        _ ≤ _ := success_count_step (B + U) x

private theorem rotate_mul (a b c : Nat) : a * (b * c) = c * (a * b) := by ac_rfl

/-- Absorbing the first outcome makes the contradiction persist at every
longer finite horizon. This is a statement about the arrival audit only. -/
theorem protected_arrival_mass_gt_two_thirds_padded (U : Nat) :
    2 * 7 ^ (28 + U) < 3 * successCount auditStep (.active initial) (28 + U) := by
  rw [Nat.pow_add]
  calc
    _ = 7 ^ U * (2 * 7 ^ 28) := rotate_mul 2 (7 ^ 28) (7 ^ U)
    _ < 7 ^ U * (3 * successCount auditStep (.active initial) 28) :=
      Nat.mul_lt_mul_of_pos_left protected_arrival_mass_gt_two_thirds
        (Nat.pow_pos (by decide))
    _ = 3 * (7 ^ U * successCount auditStep (.active initial) 28) :=
      Nat.mul_left_comm _ _ _
    _ ≤ _ := Nat.mul_le_mul_left 3 (success_padding 28 U (.active initial))

theorem favorable_or_unfinished_mass_lt_one_third_padded (U : Nat) :
    3 * (failureCount auditStep (.active initial) (28 + U) +
      activeCount auditStep (.active initial) (28 + U)) < 7 ^ (28 + U) := by
  have hp := node_count_partition auditStep (.active initial) (28 + U)
  have hm := protected_arrival_mass_gt_two_thirds_padded U
  exact complementary_count _ _ _ _ hp hm

end LDSinkTwoGapRaceEntranceReverseRace
