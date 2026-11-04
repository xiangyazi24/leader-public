import Leader.Wu.Elimination.SinkTwoGapSuccessorFootprint


open PPLL PPLLRepair FiniteUniformStoppingTree
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapServiceRank LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs LDSinkTwoGapEpochCost LDSinkTwoGapEpochLaws
  LDSinkTwoGapEpochKernel LDSinkTwoGapEpochSuccessor LDSinkTwoGapNoResetKernel
  LDSinkTwoGapAttemptResidual
open Classical


namespace LDSinkTwoGapAttemptCells


set_option autoImplicit false


noncomputable section


variable {n ψ : Nat}


/-! ## Small stage interfaces


Each primitive below is inspected on arbitrary input records. No proof
simplifies an unfolded composite kernel or changes a resource limit.
-/


/-- Exactly the alternatives that disable FIRE at a cell. -/
def Quiet (s : AgentState ψ) : Prop :=
  s.leader = false ∨ s.signal_B = (0 : Fin 2)


private theorem fireL_fires (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = (1 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hψ l r).1 =
      { l with bullet := (2 : Fin 3), shield := true, signal_B := (0 : Fin 2) } := by
  change
    (if l.leader = true ∧ l.signal_B = (1 : Fin 2) then
      { l with bullet := (2 : Fin 3), shield := true, signal_B := (0 : Fin 2) } else l) = _
  rw [if_pos ⟨hl, hs⟩]


private theorem fireR_fires (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.leader = true) (hs : r.signal_B = (1 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hψ l r).2 =
      { r with bullet := (1 : Fin 3), shield := false, signal_B := (0 : Fin 2) } := by
  change
    (if r.leader = true ∧ r.signal_B = (1 : Fin 2) then
      { r with bullet := (1 : Fin 3), shield := false, signal_B := (0 : Fin 2) } else r) = _
  rw [if_pos ⟨hr, hs⟩]


private theorem not_protected_follower (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false) :
    ¬ ProtectedGuard hψ l r := by
  intro hg
  have h := (protectedGuard_input_leaders hψ l r hg).1
  rw [hl] at h
  cases h


private theorem not_protected_right_zero (hψ : ψ > 0)
    (l r : AgentState ψ) (hq : Quiet r)
    (hb : r.bullet = (0 : Fin 3)) :
    ¬ ProtectedGuard hψ l r := by
  intro hg
  have h := hg.2.2.2
  rw [fire_right_eq hψ l r hq, hb] at h
  exact (by decide : (0 : Fin 3) ≠ (2 : Fin 3)) h


/-- This is only the unchanged SIGNAL/dummy suffix, not a new transition. -/
private def finishCells (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  dummyBulletSink
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2)


/-- Definitional staging identity; no composite kernel is simplified. -/
private theorem r7_stages (hψ : ψ > 0) (l r : AgentState ψ) :
    sinkKernel hψ l r =
      finishCells (nextLabel hψ l)
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ (nextLabel hψ l)
          (eliminateLeadersNoCollisionFire hψ l r).1
          (eliminateLeadersNoCollisionFire hψ l r).2) := by
  rfl


private theorem move_zero_cells (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hb : r.bullet = (0 : Fin 3)) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r = (l, r) := by
  have hz : ¬ r.bullet.val > 0 := by
    rw [hb]
    decide
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  simp only [hz, false_and, if_false]


private theorem move_leader_left_bullet_cells (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = true) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).1.bullet =
      l.bullet := by
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  by_cases hp : r.bullet.val > 0
  · rw [if_pos ⟨hp, hl⟩]
    repeat (first | rfl | split)
  · simp only [hp, false_and, if_false]


/-- Applied to an arbitrary post-FIRE responder, including a fresh dummy. -/
private theorem move_follower_right_zero_cells (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = false) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).2.bullet =
      (0 : Fin 3) := by
  have hn : ¬ (r.bullet.val > 0 ∧ l.leader = true) := by
    intro h
    have hbad := h.2
    rw [hl] at hbad
    cases hbad
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  rw [if_neg hn]
  by_cases hp : r.bullet.val > 0
  · rw [if_pos ⟨hp, hl⟩]
    repeat (first | rfl | split)
  · have hn' : ¬ (r.bullet.val > 0 ∧ l.leader = false) := by
      intro h
      exact hp h.1
    rw [if_neg hn']
    apply Fin.ext
    change r.bullet.val = 0
    omega


private theorem move_transfer_cells (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = false)
    (hp : r.bullet.val > 0) (ha : r.label = nl) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r =
      ({ l with bullet := r.bullet, signal_B := (0 : Fin 2) },
       { r with bullet := (0 : Fin 3) }) := by
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  simp [hl, hp, ha]


private theorem move_left_signal_zero_cells (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hs : l.signal_B = (0 : Fin 2)) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).1.signal_B =
      (0 : Fin 2) := by
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | exact hs | rfl | split)


private theorem signal_right_bullet_cells (nl : Fin ψ)
    (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.bullet =
      r.bullet := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  dsimp only
  repeat (first | rfl | split)


private theorem signal_right_zero_cells (nl : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = false)
    (hs : l.signal_B = (0 : Fin 2)) (ht : r.signal_B = (0 : Fin 2)) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.signal_B =
      (0 : Fin 2) := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  split
  · split
    · rfl
    · have hlt : ¬ l.leader = true := by
        intro h
        rw [hl] at h
        cases h
      simp only [if_neg hlt, hs, ht] <;>
        (apply Fin.ext; rfl)
  · exact ht


private theorem dummy_left_stable_cells (q : AgentState ψ × AgentState ψ)
    (hb : q.1.bullet = (0 : Fin 3) ∨ q.1.bullet = (2 : Fin 3)) :
    (dummyBulletSink q).1.bullet = q.1.bullet := by
  rcases hb with hb | hb <;>
    (unfold dummyBulletSink
     dsimp only
     repeat (first | rfl | (split <;> simp_all)))


private theorem dummy_right_stable_cells (q : AgentState ψ × AgentState ψ)
    (hb : q.2.bullet = (0 : Fin 3) ∨ q.2.bullet = (2 : Fin 3)) :
    (dummyBulletSink q).2.bullet = q.2.bullet := by
  rcases hb with hb | hb <;>
    (unfold dummyBulletSink
     dsimp only
     repeat (first | rfl | (split <;> simp_all)))


private theorem dummy_signals_cells (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.signal_B = q.1.signal_B ∧
    (dummyBulletSink q).2.signal_B = q.2.signal_B := by
  constructor <;>
    (unfold dummyBulletSink
     dsimp only
     repeat (first | rfl | split))


private theorem finish_left_bullet (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ)
    (hb : q.1.bullet = (0 : Fin 3) ∨ q.1.bullet = (2 : Fin 3)) :
    (finishCells nl q).1.bullet = q.1.bullet := by
  exact dummy_left_stable_cells
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2) hb


private theorem finish_right_bullet (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ)
    (hb : q.2.bullet = (0 : Fin 3) ∨ q.2.bullet = (2 : Fin 3)) :
    (finishCells nl q).2.bullet = q.2.bullet := by
  have he := signal_right_bullet_cells nl q.1 q.2
  have hs :
      (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).2.bullet =
          (0 : Fin 3) ∨
      (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).2.bullet =
          (2 : Fin 3) := by
    rw [he]
    exact hb
  exact (dummy_right_stable_cells
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2) hs).trans he


private theorem finish_left_signal (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (finishCells nl q).1.signal_B = q.1.signal_B := by
  exact (dummy_signals_cells
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2)).1


private theorem finish_right_signal_zero (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ)
    (hl : q.1.leader = false)
    (hs : q.1.signal_B = (0 : Fin 2)) (ht : q.2.signal_B = (0 : Fin 2)) :
    (finishCells nl q).2.signal_B = (0 : Fin 2) := by
  exact (dummy_signals_cells
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2)).2.trans
      (signal_right_zero_cells nl q.1 q.2 hl hs ht)


/-! ## R7 field rows, composed without a composite simplification -/


private theorem r7_quiet_left_stable (hψ : ψ > 0) (l r : AgentState ψ)
    (hlq : Quiet l) (hrq : Quiet r)
    (hb : l.bullet = (0 : Fin 3) ∨ l.bullet = (2 : Fin 3))
    (hrb : r.bullet = (0 : Fin 3)) :
    (sinkKernel hψ l r).1.bullet = l.bullet := by
  rw [r7_stages, fire_left_eq hψ l r hlq, fire_right_eq hψ l r hrq,
    move_zero_cells hψ (nextLabel hψ l) l r hrb]
  exact finish_left_bullet (nextLabel hψ l) (l, r) hb


private theorem r7_leader_left_stable (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = (0 : Fin 2))
    (hb : l.bullet = (0 : Fin 3) ∨ l.bullet = (2 : Fin 3)) :
    (sinkKernel hψ l r).1.bullet = l.bullet := by
  rw [r7_stages, fire_left_eq hψ l r (Or.inr hs)]
  let r0 := (eliminateLeadersNoCollisionFire hψ l r).2
  let q := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hψ (nextLabel hψ l) l r0
  change (finishCells (nextLabel hψ l) q).1.bullet = l.bullet
  have hm : q.1.bullet = l.bullet :=
    move_leader_left_bullet_cells hψ (nextLabel hψ l) l r0 hl
  have hq : q.1.bullet = (0 : Fin 3) ∨ q.1.bullet = (2 : Fin 3) := by
    rw [hm]
    exact hb
  exact (finish_left_bullet (nextLabel hψ l) q hq).trans hm


private theorem r7_right_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hq : Quiet r) (hb : r.bullet = (0 : Fin 3)) :
    (sinkKernel hψ l r).2.bullet = (0 : Fin 3) := by
  rw [r7_stages, fire_right_eq hψ l r hq,
    move_zero_cells hψ (nextLabel hψ l)
      (eliminateLeadersNoCollisionFire hψ l r).1 r hb]
  exact (finish_right_bullet (nextLabel hψ l)
    ((eliminateLeadersNoCollisionFire hψ l r).1, r) (Or.inl hb)).trans hb


private theorem r7_follower_right_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (sinkKernel hψ l r).2.bullet = (0 : Fin 3) := by
  rw [r7_stages, fire_left_eq hψ l r (Or.inl hl)]
  let r0 := (eliminateLeadersNoCollisionFire hψ l r).2
  let q := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hψ (nextLabel hψ l) l r0
  change (finishCells (nextLabel hψ l) q).2.bullet = (0 : Fin 3)
  have hz : q.2.bullet = (0 : Fin 3) :=
    move_follower_right_zero_cells hψ (nextLabel hψ l) l r0 hl
  exact (finish_right_bullet (nextLabel hψ l) q (Or.inl hz)).trans hz


private theorem r7_transfer_live (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) (hrq : Quiet r)
    (hb : r.bullet = (2 : Fin 3)) (ha : r.label = nextLabel hψ l) :
    (sinkKernel hψ l r).1.bullet = (2 : Fin 3) ∧
      (sinkKernel hψ l r).2.bullet = (0 : Fin 3) := by
  have hp : r.bullet.val > 0 := by rw [hb]; decide
  rw [r7_stages, fire_left_eq hψ l r (Or.inl hl),
    fire_right_eq hψ l r hrq, move_transfer_cells hψ (nextLabel hψ l) l r hl hp ha]
  constructor
  · exact (finish_left_bullet (nextLabel hψ l) _ (Or.inr hb)).trans hb
  · exact finish_right_bullet (nextLabel hψ l) _ (Or.inl rfl)


private theorem r7_shooter_left_signal (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = (1 : Fin 2)) :
    (sinkKernel hψ l r).1.signal_B = (0 : Fin 2) := by
  have h0 : (eliminateLeadersNoCollisionFire hψ l r).1.signal_B =
      (0 : Fin 2) := by
    rw [fireL_fires hψ l r hl hs]
  rw [r7_stages]
  have h1 := move_left_signal_zero_cells hψ (nextLabel hψ l)
    (eliminateLeadersNoCollisionFire hψ l r).1
    (eliminateLeadersNoCollisionFire hψ l r).2 h0
  exact (finish_left_signal (nextLabel hψ l) _).trans h1


/-! ## K2 dispatch: protected equation or the named R7 row -/


/-- With both FIRE calls disabled and both bullets zero, the left stays zero. -/
theorem pair_quiet_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hlq : Quiet l) (hrq : Quiet r)
    (hlb : l.bullet = (0 : Fin 3)) (hrb : r.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (0 : Fin 3) := by
  rw [kernelC_eq_of_not_protected hψ l r
    (not_protected_right_zero hψ l r hrq hrb)]
  exact (r7_quiet_left_stable hψ l r hlq hrq (Or.inl hlb) hrb).trans hlb


/-- With no incoming bullet and no FIRE, the resident live bullet survives. -/
theorem pair_left_live_empty_right (hψ : ψ > 0) (l r : AgentState ψ)
    (hlq : Quiet l) (hrq : Quiet r)
    (hlb : l.bullet = (2 : Fin 3)) (hrb : r.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (2 : Fin 3) := by
  rw [kernelC_eq_of_not_protected hψ l r
    (not_protected_right_zero hψ l r hrq hrb)]
  exact (r7_quiet_left_stable hψ l r hlq hrq (Or.inr hlb) hrb).trans hlb


/-- A quiet leader does not acquire a bullet from its responder. -/
theorem pair_leader_left_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = (0 : Fin 2))
    (hb : l.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (0 : Fin 3) := by
  by_cases hg : ProtectedGuard hψ l r
  · rw [sinkKernelC_protected_initiator hψ l r hg,
      fire_left_eq hψ l r (Or.inr hs)]
    exact hb
  · rw [kernelC_eq_of_not_protected hψ l r hg]
    exact (r7_leader_left_stable hψ l r hl hs (Or.inl hb)).trans hb


/-- Neither MOVE at a leader nor the suffix erases its own live bullet. -/
theorem pair_leader_left_live (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = (0 : Fin 2))
    (hb : l.bullet = (2 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (2 : Fin 3) := by
  by_cases hg : ProtectedGuard hψ l r
  · rw [sinkKernelC_protected_initiator hψ l r hg,
      fire_left_eq hψ l r (Or.inr hs)]
    exact hb
  · rw [kernelC_eq_of_not_protected hψ l r hg]
    exact (r7_leader_left_stable hψ l r hl hs (Or.inr hb)).trans hb


/-- A quiet zero responder cannot acquire a bullet. -/
theorem pair_right_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hq : Quiet r) (hb : r.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) := by
  rw [kernelC_eq_of_not_protected hψ l r
    (not_protected_right_zero hψ l r hq hb)]
  exact r7_right_zero hψ l r hq hb


/-- The arbitrary post-FIRE responder is cleared by follower MOVE. -/
theorem pair_follower_right_zero (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) := by
  rw [kernelC_eq_of_not_protected hψ l r (not_protected_follower hψ l r hl)]
  exact r7_follower_right_zero hψ l r hl


/-- Right FIRE is disabled before the live transfer is read. -/
theorem pair_transfer_live (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) (hrq : Quiet r)
    (hb : r.bullet = (2 : Fin 3))
    (halign : r.label = nextLabel hψ l) :
    (sinkKernelC hψ l r).1.bullet = (2 : Fin 3) ∧
      (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) := by
  rw [kernelC_eq_of_not_protected hψ l r (not_protected_follower hψ l r hl)]
  exact r7_transfer_live hψ l r hl hrq hb halign


/-- A victim with an incoming live follower either dies or absorbs while shielded. -/
theorem pair_victim_live (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hb : r.bullet = (2 : Fin 3)) :
    (sinkKernelC hψ l r).1.leader = false ∨
      ((sinkKernelC hψ l r).1.leader = true ∧
       (sinkKernelC hψ l r).1.shield = true ∧
       (sinkKernelC hψ l r).2.bullet = (0 : Fin 3)) := by
  by_cases hg : ProtectedGuard hψ l r
  · have hi := sinkKernelC_protected_initiator hψ l r hg
    have hp := sinkKernelC_protected hψ l r hg
    refine Or.inr ⟨?_, ?_, hp.1⟩
    · rw [hi]
      exact hg.1
    · rw [hi]
      exact hg.2.1
  · have hs0 : l.signal_B = (0 : Fin 2) := by
      apply Fin.ext
      have hn1 : l.signal_B.val ≠ 1 := by
        intro hv
        have hs1 : l.signal_B = (1 : Fin 2) := Fin.ext hv
        apply hg
        unfold ProtectedGuard
        rw [fireL_fires hψ l r hl hs1, fire_right_eq hψ l r (Or.inl hr)]
        exact ⟨hl, rfl, hr, hb⟩
      have hbound := l.signal_B.isLt
      omega
    have hsh : l.shield = false := by
      cases he : l.shield with
      | false => rfl
      | true =>
          apply False.elim
          apply hg
          unfold ProtectedGuard
          rw [fire_left_eq hψ l r (Or.inr hs0),
            fire_right_eq hψ l r (Or.inl hr)]
          exact ⟨hl, he, hr, hb⟩
    apply Or.inl
    rw [kernelC_eq_of_not_protected hψ l r hg]
    exact sinkKernel_kill hψ l r hl hsh hs0 hr hb


/-- FIRE clears the initiator signal; the remaining stages preserve zero. -/
theorem pair_shooter_left_signal (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = (1 : Fin 2)) :
    (sinkKernelC hψ l r).1.signal_B = (0 : Fin 2) := by
  by_cases hg : ProtectedGuard hψ l r
  · rw [sinkKernelC_protected_initiator hψ l r hg, fireL_fires hψ l r hl hs]
  · rw [kernelC_eq_of_not_protected hψ l r hg]
    exact r7_shooter_left_signal hψ l r hl hs


/-- Right FIRE writes a dummy, then aligned MOVE clears both signal positions. -/
theorem pair_shooter_right_signals (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) (hr : r.leader = true)
    (_hlb : l.bullet = (0 : Fin 3)) (_hrb : r.bullet = (0 : Fin 3))
    (hs : r.signal_B = (1 : Fin 2))
    (halign : r.label = nextLabel hψ l) :
    (sinkKernelC hψ l r).1.signal_B = (0 : Fin 2) ∧
      (sinkKernelC hψ l r).2.signal_B = (0 : Fin 2) := by
  rw [kernelC_eq_of_not_protected hψ l r (not_protected_follower hψ l r hl),
    r7_stages, fire_left_eq hψ l r (Or.inl hl), fireR_fires hψ l r hr hs]
  rw [move_transfer_cells hψ (nextLabel hψ l) l
    { r with bullet := (1 : Fin 3), shield := false, signal_B := (0 : Fin 2) }
    hl (by change (1 : Nat) > 0; decide) halign]
  constructor
  · exact finish_left_signal (nextLabel hψ l) _
  · exact finish_right_signal_zero (nextLabel hψ l) _ hl rfl rfl


/-! ## Ring geometry and projections -/


private theorem head_ne (G : GapFrame n) (e : Fin n) :
    G.ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  have hd := G.hd
  have hdn := G.hdn
  by_cases ha : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at hv
    omega


private theorem at_left (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e e =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).1 := by
  simp [sinkStepC, updatePair]


private theorem at_right (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e (G.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).2 := by
  have hh := head_ne G e
  simp [sinkStepC, updatePair, hh, Ne.symm hh]


private theorem edge_of_head (G : GapFrame n) (e : Fin n) (k : Nat)
    (hk : 1 ≤ k) (he : G.ring.rightNeighbor e = G.pos k) :
    e = G.pos (k - 1) := by
  have h : G.ring.rightNeighbor e = G.ring.rightNeighbor (G.pos (k - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel hk] using he
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = ((G.pos (k - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (G.pos (k - 1)).isLt
  by_cases ha : e.val + 1 < n <;> by_cases hb : (G.pos (k - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hh : (G.pos (k - 1)).val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega


private theorem live_ne_zero {b : Fin 3} (hb : b = (2 : Fin 3)) :
    b ≠ (0 : Fin 3) := by
  rw [hb]
  decide


/-! ## Active-domain consequences -/


theorem old_bullet_unique (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (u v : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d)
    (hv : 0 < v) (hvd : v ≤ F.attack.d)
    (hbu : (x.1.conf (F.attack.pos u)).bullet ≠ (0 : Fin 3))
    (hbv : (x.1.conf (F.attack.pos v)).bullet ≠ (0 : Fin 3)) : u = v := by
  obtain ⟨t, _, _, _, huniq⟩ := x.2.tag.shot
  exact (huniq u hu hud hbu).trans (huniq v hv hvd hbv).symm


theorem attack_shooter_signal_zero (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) :
    (x.1.conf (F.attack.pos F.attack.d)).signal_B = (0 : Fin 2) := by
  obtain ⟨t, ht, htd, hb, _⟩ := x.2.tag.shot
  exact x.2.attack.2.2.2 t F.attack.d ht htd
    (live_ne_zero hb) htd (Nat.le_refl _)


theorem attack_cell_quiet (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (u : Nat) (hu : 0 < u) (hud : u ≤ F.attack.d) :
    Quiet (x.1.conf (F.attack.pos u)) := by
  by_cases he : u = F.attack.d
  · subst u
    exact Or.inr (attack_shooter_signal_zero hψ F x)
  · exact Or.inl (x.2.attack.2.1 u hu (by omega))


/-! ## Bullet provenance and uniqueness -/


theorem post_bullet_origin (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (u : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d)
    (hb : (postConf hψ F x.1 e (F.attack.pos u)).bullet ≠ (0 : Fin 3)) :
    (x.1.conf (F.attack.pos u)).bullet ≠ (0 : Fin 3) ∨
      (u < F.attack.d ∧ e = F.attack.pos u ∧
       (x.1.conf (F.attack.pos (u + 1))).bullet ≠ (0 : Fin 3)) := by
  by_cases hz : (x.1.conf (F.attack.pos u)).bullet = (0 : Fin 3)
  · by_cases hl : F.attack.pos u = e
    · subst e
      by_cases he : u = F.attack.d
      · subst u
        have ho := pair_leader_left_zero hψ
          (x.1.conf (F.attack.pos F.attack.d))
          (x.1.conf (F.attack.ring.rightNeighbor (F.attack.pos F.attack.d)))
          x.2.attack.1.2 (attack_shooter_signal_zero hψ F x) hz
        apply False.elim
        apply hb
        rw [postConf_eq_attack, at_left]
        exact ho
      · have hul : u < F.attack.d := by omega
        by_cases hrz : (x.1.conf (F.attack.pos (u + 1))).bullet = (0 : Fin 3)
        · have ho := pair_quiet_zero hψ
            (x.1.conf (F.attack.pos u)) (x.1.conf (F.attack.pos (u + 1)))
            (attack_cell_quiet hψ F x u hu hud)
            (attack_cell_quiet hψ F x (u + 1) (by omega) (by omega)) hz hrz
          apply False.elim
          apply hb
          rw [postConf_eq_attack, at_left, gap_rightNeighbor_pos]
          exact ho
        · exact Or.inr ⟨hul, rfl, hrz⟩
    · by_cases hr : F.attack.pos u = F.attack.ring.rightNeighbor e
      · have hq : Quiet (x.1.conf (F.attack.ring.rightNeighbor e)) := by
          rw [← hr]
          exact attack_cell_quiet hψ F x u hu hud
        have hz' : (x.1.conf (F.attack.ring.rightNeighbor e)).bullet =
            (0 : Fin 3) := by
          rw [← hr]
          exact hz
        have ho := pair_right_zero hψ (x.1.conf e)
          (x.1.conf (F.attack.ring.rightNeighbor e)) hq hz'
        apply False.elim
        apply hb
        rw [postConf_eq_attack, hr, at_right]
        exact ho
      · apply False.elim
        apply hb
        rw [postConf_eq_attack, sinkStepC_other hψ F.attack x.1.conf e
          (F.attack.pos u) hl hr]
        exact hz
  · exact Or.inl hz


/-- A positive responder beyond position one has an interior follower initiator. -/
theorem post_responder_zero (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (u : Nat)
    (hu : 1 < u) (hud : u ≤ F.attack.d)
    (he : F.attack.ring.rightNeighbor e = F.attack.pos u) :
    (postConf hψ F x.1 e (F.attack.pos u)).bullet = (0 : Fin 3) := by
  have he' := edge_of_head F.attack e u (by omega) he
  have hl : (x.1.conf e).leader = false := by
    rw [he']
    exact x.2.attack.2.1 (u - 1) (by omega) (by omega)
  rw [postConf_eq_attack, ← he, at_right]
  exact pair_follower_right_zero hψ (x.1.conf e)
    (x.1.conf (F.attack.ring.rightNeighbor e)) hl


/-- Uniqueness of all nonzero sector bullets, including dummy bullets. -/
theorem post_bullet_unique (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (u v : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d)
    (hv : 0 < v) (hvd : v ≤ F.attack.d)
    (hbu : (postConf hψ F x.1 e (F.attack.pos u)).bullet ≠ (0 : Fin 3))
    (hbv : (postConf hψ F x.1 e (F.attack.pos v)).bullet ≠ (0 : Fin 3)) :
    u = v := by
  rcases post_bullet_origin hψ F x e u hu hud hbu with hou | hou
  · rcases post_bullet_origin hψ F x e v hv hvd hbv with hov | hov
    · exact old_bullet_unique hψ F x u v hu hud hv hvd hou hov
    · rcases hov with ⟨hvl, hev, hov⟩
      have huv := old_bullet_unique hψ F x u (v + 1)
        hu hud (by omega) (by omega) hou hov
      have hhead : F.attack.ring.rightNeighbor e = F.attack.pos u := by
        rw [hev, gap_rightNeighbor_pos, ← huv]
      exact (hbu (post_responder_zero hψ F x e u (by omega) hud hhead)).elim
  · rcases hou with ⟨hul, heu, hou⟩
    rcases post_bullet_origin hψ F x e v hv hvd hbv with hov | hov
    · have huv := old_bullet_unique hψ F x (u + 1) v
        (by omega) (by omega) hv hvd hou hov
      have hhead : F.attack.ring.rightNeighbor e = F.attack.pos v := by
        rw [heu, gap_rightNeighbor_pos, huv]
      exact (hbv (post_responder_zero hψ F x e v (by omega) hvd hhead)).elim
    · rcases hov with ⟨hvl, _hev, hov⟩
      have huv := old_bullet_unique hψ F x (u + 1) (v + 1)
        (by omega) (by omega) (by omega) (by omega) hou hov
      omega


/-! ## The victim edge cannot continue with a live tag -/


theorem victim_edge_is_terminal (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F)
    (hb : (x.1.conf (F.attack.pos 1)).bullet = (2 : Fin 3)) :
    NoResetSuccess F (postConf hψ F x.1 (F.attack.pos 0)) ∨
      NoResetAbsorbedAt F x.1 (F.attack.pos 0)
        (postConf hψ F x.1 (F.attack.pos 0)) := by
  have hd := F.attack.hd
  have hr : (x.1.conf (F.attack.pos 1)).leader = false :=
    x.2.attack.2.1 1 (by omega) (by omega)
  have hp := pair_victim_live hψ
    (x.1.conf (F.attack.pos 0)) (x.1.conf (F.attack.pos 1))
    x.2.attack.1.1 hr hb
  have hleft :
      postConf hψ F x.1 (F.attack.pos 0) (F.attack.pos 0) =
        (sinkKernelC hψ (x.1.conf (F.attack.pos 0))
          (x.1.conf (F.attack.pos 1))).1 := by
    rw [postConf_eq_attack, at_left, gap_rightNeighbor_pos]
  have hright :
      postConf hψ F x.1 (F.attack.pos 0) (F.attack.pos 1) =
        (sinkKernelC hψ (x.1.conf (F.attack.pos 0))
          (x.1.conf (F.attack.pos 1))).2 := by
    rw [postConf_eq_attack]
    have h := at_right hψ F.attack x.1.conf (F.attack.pos 0)
    simpa only [gap_rightNeighbor_pos, Nat.zero_add] using h
  rcases hp with hkill | ⟨hleader, hshield, hclear⟩
  · apply Or.inl
    apply Or.inl
    apply Or.inl
    rw [hleft]
    exact hkill
  · apply Or.inr
    refine ⟨x.2.tag.parked_iff.mpr hb, rfl, hb, x.2.attack.1.1, ?_, ?_, ?_⟩
    · rw [hright]
      exact hclear
    · rw [hleft]
      exact hshield
    · rw [hleft]
      exact hleader


theorem liveTouched_K2 (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (t : Nat)
    (ht : 0 < t) (htd : t ≤ F.attack.d)
    (hb : (x.1.conf (F.attack.pos t)).bullet = (2 : Fin 3))
    (hTouch : Touched F.attack e (F.attack.pos t))
    (hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e)) :
    ∃ u : Nat, 0 < u ∧ u ≤ t ∧
      (postConf hψ F x.1 e (F.attack.pos u)).bullet = (2 : Fin 3) := by
  rcases hTouch with hleft | hright
  · subst e
    refine ⟨t, ht, Nat.le_refl _, ?_⟩
    by_cases htdEq : t = F.attack.d
    · subst t
      rw [postConf_eq_attack, at_left]
      exact pair_leader_left_live hψ
        (x.1.conf (F.attack.pos F.attack.d))
        (x.1.conf (F.attack.ring.rightNeighbor (F.attack.pos F.attack.d)))
        x.2.attack.1.2 (attack_shooter_signal_zero hψ F x) hb
    · have htl : t < F.attack.d := by omega
      have hrz : (x.1.conf (F.attack.pos (t + 1))).bullet = (0 : Fin 3) := by
        by_cases hz : (x.1.conf (F.attack.pos (t + 1))).bullet = (0 : Fin 3)
        · exact hz
        · have hbad := old_bullet_unique hψ F x t (t + 1)
            ht htd (by omega) (by omega) (live_ne_zero hb) hz
          omega
      rw [postConf_eq_attack, at_left, gap_rightNeighbor_pos]
      exact pair_left_live_empty_right hψ
        (x.1.conf (F.attack.pos t)) (x.1.conf (F.attack.pos (t + 1)))
        (attack_cell_quiet hψ F x t ht htd)
        (attack_cell_quiet hψ F x (t + 1) (by omega) (by omega)) hb hrz
  · have he := edge_of_head F.attack e t (by omega) hright.symm
    by_cases ht1 : t = 1
    · have he0 : e = F.attack.pos 0 := by simpa only [ht1] using he
      have hb1 : (x.1.conf (F.attack.pos 1)).bullet = (2 : Fin 3) := by
        simpa only [ht1] using hb
      rw [he0] at hs ha
      rcases victim_edge_is_terminal hψ F x hb1 with h | h
      · exact (hs h).elim
      · exact (ha h).elim
    · have ht1 : 1 ≤ t := by omega
      have hleftFollower : (x.1.conf (F.attack.pos (t - 1))).leader = false :=
        x.2.attack.2.1 (t - 1) (by omega) (by omega)
      have halign : (x.1.conf (F.attack.pos t)).label =
          nextLabel hψ (x.1.conf (F.attack.pos (t - 1))) := by
        simpa only [Nat.sub_add_cancel ht1] using
          x.2.attack.2.2.1 (t - 1) (by omega)
      have hp := pair_transfer_live hψ
        (x.1.conf (F.attack.pos (t - 1))) (x.1.conf (F.attack.pos t))
        hleftFollower (attack_cell_quiet hψ F x t ht htd) hb halign
      refine ⟨t - 1, by omega, by omega, ?_⟩
      rw [he, postConf_eq_attack, at_left, gap_rightNeighbor_pos,
        Nat.sub_add_cancel ht1]
      exact hp.1


theorem noDuplicateTouched_K2 (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (u v : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d)
    (hv : 0 < v) (hvd : v ≤ F.attack.d)
    (hbu : (postConf hψ F x.1 e (F.attack.pos u)).bullet ≠ (0 : Fin 3))
    (hbv : (postConf hψ F x.1 e (F.attack.pos v)).bullet ≠ (0 : Fin 3))
    (_hTouch : Touched F.attack e (F.attack.pos u) ∨
      Touched F.attack e (F.attack.pos v))
    (_hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (_ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e)) : u = v := by
  exact post_bullet_unique hψ F x e u v hu hud hv hvd hbu hbv


/-! ## Clean-pre recovery signal coherence -/


theorem clean_gap_signal_touched (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ G C) (hClean : CleanReady G C)
    (k j : Nat) (hk : 0 < k) (hkd : k ≤ G.d)
    (hb : (sinkStepC hψ G C e (G.pos k)).bullet ≠ (0 : Fin 3))
    (hkj : k ≤ j) (hjd : j ≤ G.d)
    (hTouch : Touched G e (G.pos k)) :
    (sinkStepC hψ G C e (G.pos j)).signal_B = (0 : Fin 2) := by
  have hd := G.hd
  rcases hTouch with hleft | hright
  · subst e
    by_cases hke : k = G.d
    · subst k
      have hje : j = G.d := by omega
      subst j
      rw [at_left]
      exact pair_shooter_left_signal hψ (C (G.pos G.d))
        (C (G.ring.rightNeighbor (G.pos G.d))) hi.1.2 hClean.1
    · have hkl : k < G.d := by omega
      have hl : (C (G.pos k)).leader = false := hi.2.1 k hk hkl
      have hlb : (C (G.pos k)).bullet = (0 : Fin 3) := hClean.2 k hk hkd
      have hrb : (C (G.pos (k + 1))).bullet = (0 : Fin 3) :=
        hClean.2 (k + 1) (by omega) (by omega)
      by_cases hke' : k + 1 = G.d
      · have hr : (C (G.pos (k + 1))).leader = true := by
          rw [hke']
          exact hi.1.2
        have hrs : (C (G.pos (k + 1))).signal_B = (1 : Fin 2) := by
          rw [hke']
          exact hClean.1
        have hp := pair_shooter_right_signals hψ
          (C (G.pos k)) (C (G.pos (k + 1))) hl hr hlb hrb hrs
          (hi.2.2.1 k hkl)
        by_cases hjk : j = k
        · subst j
          rw [at_left, gap_rightNeighbor_pos]
          exact hp.1
        · have hjnext : j = k + 1 := by omega
          subst j
          have hrightEq :
              sinkStepC hψ G C (G.pos k) (G.pos (k + 1)) =
                (sinkKernelC hψ (C (G.pos k)) (C (G.pos (k + 1)))).2 := by
            simpa only [gap_rightNeighbor_pos] using
              at_right hψ G C (G.pos k)
          rw [hrightEq]
          exact hp.2
      · have hrl : (C (G.pos (k + 1))).leader = false :=
          hi.2.1 (k + 1) (by omega) (by omega)
        have hz := pair_quiet_zero hψ (C (G.pos k)) (C (G.pos (k + 1)))
          (Or.inl hl) (Or.inl hrl) hlb hrb
        apply False.elim
        apply hb
        rw [at_left, gap_rightNeighbor_pos]
        exact hz
  · have he := edge_of_head G e k (by omega) hright.symm
    apply False.elim
    apply hb
    rw [hright, at_right]
    by_cases hk1 : k = 1
    · have hr : (C (G.ring.rightNeighbor e)).leader = false := by
        rw [← hright]
        exact hi.2.1 k hk (by omega)
      have hrb : (C (G.ring.rightNeighbor e)).bullet = (0 : Fin 3) := by
        rw [← hright]
        exact hClean.2 k hk hkd
      exact pair_right_zero hψ (C e) (C (G.ring.rightNeighbor e))
        (Or.inl hr) hrb
    · have hl : (C e).leader = false := by
        rw [he]
        exact hi.2.1 (k - 1) (by omega) (by omega)
      exact pair_follower_right_zero hψ (C e) (C (G.ring.rightNeighbor e)) hl


theorem cleanRecoverySignal_K2 (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n)
    (hClean : CleanReady F.recovery x.1.conf)
    (_hNotClean : ¬ CleanReady F.recovery (postConf hψ F x.1 e))
    (_hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (_ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e))
    (k j : Nat) (hk : 0 < k) (hkd : k ≤ F.recovery.d)
    (hb : (postConf hψ F x.1 e (F.recovery.pos k)).bullet ≠ (0 : Fin 3))
    (hkj : k ≤ j) (hjd : j ≤ F.recovery.d)
    (hTouch : Touched F.recovery e (F.recovery.pos k)) :
    (postConf hψ F x.1 e (F.recovery.pos j)).signal_B = (0 : Fin 2) := by
  rw [postConf_eq_recovery] at hb ⊢
  exact clean_gap_signal_touched hψ F.recovery x.1.conf e x.2.recovery
    hClean k j hk hkd hb hkj hjd hTouch


/-! ## Assemble the unchanged interfaces -/


theorem attemptCellResidual_K2 (hψ : ψ > 0) (F : TwoGapFrame n) :
    AttemptCellResidual hψ F := by
  exact ⟨liveTouched_K2 hψ F, noDuplicateTouched_K2 hψ F,
    cleanRecoverySignal_K2 hψ F⟩


theorem attemptResidual_K2 (hψ : ψ > 0) (F : TwoGapFrame n) :
    AttemptResidual hψ F := by
  exact attemptResidual_of_cells hψ F (attemptCellResidual_K2 hψ F)


theorem attemptLaws_K2 (hψ : ψ > 0) (F : TwoGapFrame n) :
    AttemptLaws hψ F := by
  exact attemptLaws_of_residual hψ F (attemptResidual_K2 hψ F)


theorem attempt_cost_le_K2 (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (T : Nat) :
    truncatedActiveCostNumerator
        (attemptStep hψ F (attemptLaws_K2 hψ F).continuation) (.active x) T ≤
      n ^ T * (n * 16 * (F.recovery.d + F.attack.d)) := by
  exact attempt_cost_le_of_laws hψ F (attemptLaws_K2 hψ F) x T


end


end LDSinkTwoGapAttemptCells


#print axioms LDSinkTwoGapAttemptCells.pair_quiet_zero
#print axioms LDSinkTwoGapAttemptCells.pair_left_live_empty_right
#print axioms LDSinkTwoGapAttemptCells.pair_leader_left_zero
#print axioms LDSinkTwoGapAttemptCells.pair_leader_left_live
#print axioms LDSinkTwoGapAttemptCells.pair_right_zero
#print axioms LDSinkTwoGapAttemptCells.pair_follower_right_zero
#print axioms LDSinkTwoGapAttemptCells.pair_transfer_live
#print axioms LDSinkTwoGapAttemptCells.pair_victim_live
#print axioms LDSinkTwoGapAttemptCells.pair_shooter_left_signal
#print axioms LDSinkTwoGapAttemptCells.pair_shooter_right_signals
#print axioms LDSinkTwoGapAttemptCells.attack_shooter_signal_zero
#print axioms LDSinkTwoGapAttemptCells.post_bullet_origin
#print axioms LDSinkTwoGapAttemptCells.post_bullet_unique
#print axioms LDSinkTwoGapAttemptCells.victim_edge_is_terminal
#print axioms LDSinkTwoGapAttemptCells.liveTouched_K2
#print axioms LDSinkTwoGapAttemptCells.noDuplicateTouched_K2
#print axioms LDSinkTwoGapAttemptCells.clean_gap_signal_touched
#print axioms LDSinkTwoGapAttemptCells.cleanRecoverySignal_K2
#print axioms LDSinkTwoGapAttemptCells.attemptCellResidual_K2
#print axioms LDSinkTwoGapAttemptCells.attemptResidual_K2
#print axioms LDSinkTwoGapAttemptCells.attemptLaws_K2
#print axioms LDSinkTwoGapAttemptCells.attempt_cost_le_K2
