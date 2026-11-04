import Leader.Wu.Elimination.SinkUnifiedCell
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy

/-!
# Output safety of the actual K2 elimination row

K2 has zero-label leader egress across the incoming label cut. Consequently
the literal label-path clause of `OutputSafeConfig` is not closed in general.
The counterexample below uses two agents; the positive results distinguish
literal peacefulness from the label-free shield/signal condition needed by
this row. All transitions remain the existing K2 transition.
-/

namespace K2OutputSafety

open PPLL LDSinkKernelC LDSinkGapCleanup LDSinkProtectedAbsorption
  LDSinkBoundedKernel PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoGlobal PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthOutputLegitimacy PPLLResearchFormulation
  StateBoundUnifiedCell

open PPLLRepair hiding eraseConfig

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ n : Nat}

/-- The actual K2 row on an arbitrary directed ring. Unlike `sinkStepC`, this
definition needs no interleader-gap placement, so it also covers two agents. -/
def rawStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n → AgentState ψ :=
  updatePair C e (ring.rightNeighbor e)
    (sinkKernelC hψ (C e) (C (ring.rightNeighbor e)))

/-- The ring-only presentation is the existing gap-indexed step verbatim. -/
theorem rawStep_eq_sinkStepC (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    rawStep hψ F.ring C e = sinkStepC hψ F C e := rfl

/-! ## Smallest nontrivial-ring obstruction to literal output legitimacy -/

/-- A canonical two-agent safe labeling, with a peaceful live bullet at its
shielded label-zero leader. The incoming edge is the only label cut. -/
def cutPair (i : Fin 2) : AgentState 3 :=
  if i = 0 then { outputCore (n := 2) (by decide) i with
    bullet := 2, shield := true }
  else outputCore (n := 2) (by decide) i

/-- The live bullet starts peacefully at distance zero; all four existing
output-safety conditions hold before the K2 interaction. -/
theorem cutPair_safe : OutputSafeConfig (by decide) ⟨by decide⟩ cutPair := by
  refine
    { unique_leader := ?_
      leader_label_zero := ?_
      no_nonpeaceful_bullet := ?_
      no_free_barrier := ?_ }
  · unfold hasUniqueLeader
    decide
  · decide
  · intro i hi
    have hi0 : i = 0 := by
      rcases fin2_cases i with h | h
      · exact h
      · subst i
        exact False.elim ((by decide : (cutPair 1).bullet ≠ 2) hi)
    subst i
    apply peacefulBullet_zero
    all_goals decide
  · unfold noFreeBarrier isBarrier
    decide

/-- On edge `1 → 0`, label-zero egress puts the live bullet at label one,
across a nonconsecutive edge. Its compulsory first peaceful edge is false. -/
theorem cutPair_not_safe_after :
    ¬ OutputSafeConfig (by decide) ⟨by decide⟩
      (rawStep (by decide) ⟨by decide⟩ cutPair 1) := by
  intro hs
  have hp := hs.no_nonpeaceful_bullet 1 (by decide)
  obtain ⟨_, d, _, _, _, _, hlab⟩ := hp
  have h := hlab 0 (Nat.zero_le d)
  have hv := congrArg Fin.val h
  change 0 = (1 + 1) % 3 at hv
  omega

/-- The same defect is reachable from the existing canonical bullet-free
safe witness. The first three interactions arm and fire the leader; the
fourth transports its live bullet across the incoming cut. -/
theorem canonical_two_agent_escape :
    ¬ OutputSafeConfig (by decide) ⟨by decide⟩
      (run (rawStep (ψ := 3) (by decide) ⟨by decide⟩)
        (outputCore (n := 2) (by decide)) [0, 1, 0, 1]) := by
  intro hs
  have hp := hs.no_nonpeaceful_bullet 1 (by decide)
  obtain ⟨_, d, _, _, _, _, hlab⟩ := hp
  have h := hlab 0 (Nat.zero_le d)
  have hv := congrArg Fin.val h
  change 0 = (1 + 1) % 3 at hv
  omega

/-! ## Alignment and the precise post-Algorithm-15 cleanup -/

/-- Every physical edge has consecutive labels, including the incoming
leader edge. This is an explicit strengthening of the existing safe set. -/
def CyclicLabels (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i, (C (ring.rightNeighbor i)).label =
    ⟨((C i).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩

private theorem fire_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.label = l.label ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.label = r.label ∧
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  unfold eliminateLeadersNoCollisionFire
  repeat (first | exact ⟨rfl, rfl, rfl, rfl⟩ | split)

private theorem move_frame (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove nl l r).1.label = l.label ∧
    (eliminateLeadersNoCollisionMove nl l r).2.label = r.label := by
  unfold eliminateLeadersNoCollisionMove
  repeat (first | exact ⟨rfl, rfl⟩ | split)

/-- With an aligned input edge, the extra egress and leader-sink guards add
no behavior. The remaining K2 changes are protected absorption and dummy
removal, applied to the checked no-collision Algorithm-15 result. -/
theorem aligned_kernel (hψ : 0 < ψ) (l r : AgentState ψ)
    (ha : r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    letI : Decidable (ProtectedGuard hψ l r) := Classical.propDecidable _
    sinkKernelC hψ l r =
      let q := eliminateLeadersNoCollision hψ l r
      if ProtectedGuard hψ l r then
        (q.1, { q.2 with bullet := 0, signal_B := 1 })
      else dummyBulletSink q := by
  classical
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let f := eliminateLeadersNoCollisionFire hψ l r
  have hf := fire_frame hψ l r
  have hfa : f.2.label = nl := hf.2.1.trans ha
  by_cases hg : ProtectedGuard hψ l r
  · rw [if_pos hg, sinkKernelC_protected_eq hψ l r hg,
      eliminateLeadersNoCollision_eq_staged]
    change f.1.leader = true ∧ f.1.shield = true ∧
      f.2.leader = false ∧ f.2.bullet = 2 at hg
    have hm : eliminateLeadersNoCollisionMove nl f.1 f.2 = f := by
      simp [eliminateLeadersNoCollisionMove, hg.1, hg.2.1, hg.2.2.2]
    change (f.1, { f.2 with bullet := 0, signal_B := 1 }) = _
    change _ = ((eliminateLeadersNoCollisionSignal nl
      (eliminateLeadersNoCollisionMove nl f.1 f.2).1
      (eliminateLeadersNoCollisionMove nl f.1 f.2).2).1,
      { (eliminateLeadersNoCollisionSignal nl
        (eliminateLeadersNoCollisionMove nl f.1 f.2).1
        (eliminateLeadersNoCollisionMove nl f.1 f.2).2).2 with
          bullet := 0, signal_B := 1 })
    rw [hm]
    simp [eliminateLeadersNoCollisionSignal, hfa, hg.2.2.2]
  · rw [if_neg hg, kernelC_eq_of_not_protected hψ l r hg]
    have hm := eliminateLeadersNoCollisionZeroLeaderEgressMove_eq_of_successor_aligned
      hψ nl f.1 f.2 hfa
    have hl := move_frame nl f.1 f.2
    have hma : (eliminateLeadersNoCollisionMove nl f.1 f.2).2.label = nl :=
      hl.2.trans hfa
    unfold sinkKernel
    rw [eliminateLeadersNoCollision_eq_staged]
    change dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink nl
      (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl f.1 f.2).1
      (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl f.1 f.2).2) =
      dummyBulletSink (eliminateLeadersNoCollisionSignal nl
        (eliminateLeadersNoCollisionMove nl f.1 f.2).1
        (eliminateLeadersNoCollisionMove nl f.1 f.2).2)
    rw [hm]
    simp only [eliminateLeadersNoCollisionSignalLeaderSink,
      eliminateLeadersNoCollisionSignal, hma, true_or, if_true]

/-! ## Removing traffic just after the unique leader -/

private theorem safe_of_fields (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → AgentState ψ) (hC : OutputSafeConfig hψ ring C)
    (hl : ∀ i, (D i).leader = (C i).leader)
    (ha : ∀ i, (D i).label = (C i).label)
    (hp : noNonPeacefulBullet hψ ring D) : OutputSafeConfig hψ ring D := by
  refine
    { unique_leader := ?_
      leader_label_zero := ?_
      no_nonpeaceful_bullet := hp
      no_free_barrier := ?_ }
  · obtain ⟨p, hlead, honly⟩ := hC.unique_leader
    refine ⟨p, ?_, ?_⟩
    · change (D p).leader = true
      exact (hl p).trans hlead
    · intro i hi
      apply honly i
      exact (hl i).symm.trans hi
  · intro i hi
    exact (ha i).trans (hC.leader_label_zero i ((hl i).symm.trans hi))
  · intro i
    dsimp only
    intro hi
    change (D (ring.rightNeighbor i)).leader = true
    rw [hl]
    apply hC.no_free_barrier i
    simpa only [isBarrier, ha] using hi

/-- Clearing a responder bullet and changing its signal after the unique
leader cannot damage another live bullet's peaceful interval. Such an
interval cannot cross the successor of its target unless it starts there;
the changed responder no longer carries a live bullet. -/
theorem peaceful_after_cleanup (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → AgentState ψ) (hC : OutputSafeConfig hψ ring C) (e : Fin n)
    (hl : ∀ i, (D i).leader = (C i).leader)
    (ha : ∀ i, (D i).label = (C i).label)
    (hs : ∀ i, (D i).shield = (C i).shield)
    (hb : ∀ i, (D i).bullet = 2 → (C i).bullet = 2)
    (hz : ∀ i, (D i).signal_B = (C i).signal_B ∨
      (i = ring.rightNeighbor e ∧ (C e).leader = true ∧
        (D (ring.rightNeighbor e)).bullet ≠ 2)) :
    noNonPeacefulBullet hψ ring D := by
  intro start hnew
  obtain ⟨_, d, hd, ht, hshield, hsignals, hlabels⟩ :=
    hC.no_nonpeaceful_bullet start (hb start hnew)
  refine ⟨hnew, d, hd, ?_, ?_, ?_, ?_⟩
  · exact (hl _).trans ht
  · exact (hs _).trans hshield
  · intro k hk
    let m := cwPos ring start k
    change (D m).signal_B = 0
    rcases hz m with heq | ⟨hm, he, hclear⟩
    · exact heq.trans (hsignals k hk)
    · exfalso
      have hstart : start ≠ ring.rightNeighbor e := by
        intro h
        exact hclear (h ▸ hnew)
      obtain ⟨k0, hk0, hpos⟩ := interval_predecessor ring start e k hm hstart
      obtain ⟨p, _, honly⟩ := hC.unique_leader
      have htarget : cwPos ring start d = e := (honly _ ht).trans (honly e he).symm
      have hdEq := cwPos_bounded_unique ring start e d hd htarget
      have hkEq := cwPos_bounded_unique ring start e k0 (by omega) hpos
      omega
  · intro k hk
    change (D (cwPos ring start (k + 1))).label =
      ⟨((D (cwPos ring start k)).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
    rw [ha, ha]
    exact hlabels k hk

private theorem noCollisionStep_safe (hψ : 0 < ψ) (hn : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : OutputSafeConfig hψ ring C) (e : Fin n) :
    OutputSafeConfig hψ ring (noCollisionStep hψ ring C e) :=
  safe_of_fields hψ ring C _ hC
    (noCollisionStep_leader_eq hψ ring C hC e)
    (noCollisionStep_label_eq hψ ring C e)
    (noNonPeacefulBullet_preserved_noCollisionStep hψ hn ring C hC e)

/-- On a fully consecutive ring K2 preserves the exact existing safe set.
The proof first uses checked Algorithm-15 peacefulness, then proves that
both concrete cleanup branches satisfy the interval erasure lemma. -/
theorem rawStep_outputSafe_of_cyclic (hψ : 0 < ψ) (hn : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : OutputSafeConfig hψ ring C) (hc : CyclicLabels hψ ring C)
    (e : Fin n) : OutputSafeConfig hψ ring (rawStep hψ ring C e) := by
  classical
  let r := ring.rightNeighbor e
  let q := eliminateLeadersNoCollision hψ (C e) (C r)
  let B := noCollisionStep hψ ring C e
  let D := rawStep hψ ring C e
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hB := noCollisionStep_safe hψ hn ring C hC e
  have hk := aligned_kernel hψ (C e) (C r) (hc e)
  have hleft : (sinkKernelC hψ (C e) (C r)).1 = q.1 := by
    rw [hk]
    dsimp only
    split
    · rfl
    · exact dummyBulletSink_left_eq q
  have hright :
      (sinkKernelC hψ (C e) (C r)).2.leader = q.2.leader ∧
      (sinkKernelC hψ (C e) (C r)).2.label = q.2.label ∧
      (sinkKernelC hψ (C e) (C r)).2.shield = q.2.shield ∧
      ((sinkKernelC hψ (C e) (C r)).2.bullet = 2 → q.2.bullet = 2) ∧
      ((sinkKernelC hψ (C e) (C r)).2.signal_B = q.2.signal_B ∨
        (q.1.leader = true ∧ (sinkKernelC hψ (C e) (C r)).2.bullet ≠ 2)) := by
    rw [hk]
    dsimp only
    split
    · rename_i hg
      have hlead := (protectedGuard_input_leaders hψ (C e) (C r) hg).1
      have hq := noCollision_leaders_eq_of_paperSafe hψ ring C hC e
      have hqlead : q.1.leader = true := hq.1.trans hlead
      simp [hqlead, q]
    · unfold dummyBulletSink
      dsimp only
      split <;> simp [q]
  have hleaders : ∀ i, (D i).leader = (B i).leader := by
    intro i
    simp only [D, B, rawStep, noCollisionStep, updatePair]
    split
    · exact congrArg AgentState.leader hleft
    · split
      · exact hright.1
      · rfl
  have hlabels : ∀ i, (D i).label = (B i).label := by
    intro i
    simp only [D, B, rawStep, noCollisionStep, updatePair]
    split
    · exact congrArg AgentState.label hleft
    · split
      · exact hright.2.1
      · rfl
  apply safe_of_fields hψ ring B D hB hleaders hlabels
  apply peaceful_after_cleanup hψ ring B D hB e hleaders hlabels
  · intro i
    simp only [D, B, rawStep, noCollisionStep, updatePair]
    split
    · exact congrArg AgentState.shield hleft
    · split
      · exact hright.2.2.1
      · rfl
  · intro i hi
    simp only [D, B, rawStep, noCollisionStep, updatePair] at hi ⊢
    split at hi
    · rename_i h
      rw [if_pos h]
      exact (congrArg AgentState.bullet hleft).symm.trans hi
    · rename_i h
      rw [if_neg h]
      split at hi
      · rename_i h'
        rw [if_pos h']
        exact hright.2.2.2.1 hi
      · rename_i h'
        rw [if_neg h']
        exact hi
  · intro i
    by_cases hie : i = e
    · left
      subst i
      change (updatePair C e r _ e).signal_B = (updatePair C e r _ e).signal_B
      rw [updatePair_initiator, updatePair_initiator]
      exact congrArg AgentState.signal_B hleft
    · by_cases hir : i = r
      · rcases hright.2.2.2.2 with heq | ⟨hlead, hb⟩
        · left
          change (updatePair C e r _ i).signal_B = (updatePair C e r _ i).signal_B
          rw [hir, updatePair_responder _ _ _ _ hne,
            updatePair_responder _ _ _ _ hne]
          exact heq
        · right
          refine ⟨hir, ?_, ?_⟩
          · change (updatePair C e r _ e).leader = true
            rw [updatePair_initiator]
            exact hlead
          · change (updatePair C e r _ r).bullet ≠ 2
            rw [updatePair_responder _ _ _ _ hne]
            exact hb
      · left
        change (updatePair C e r _ i).signal_B = (updatePair C e r _ i).signal_B
        rw [updatePair_other _ _ _ _ _ hie hir,
          updatePair_other _ _ _ _ _ hie hir]

/-! ## Exact shield/signal observation on arbitrary label moduli -/

/-- Keep the four physical leader/bullet/shield/signal fields and replace
labels by the singleton label type. This is an observation used in the proof;
the actual transition and its stored labels are never changed. -/
def signalView (u : AgentState ψ) : AgentState 1 :=
  PeaceView.toState
    { leader := u.leader
      label := 0
      shield := u.shield
      bullet := u.bullet
      signal_B := u.signal_B }

private def signalPair (q : AgentState ψ × AgentState ψ) :
    AgentState 1 × AgentState 1 := (signalView q.1, signalView q.2)

/-- The pointwise observation retains the actual location of every leader
and every live bullet. -/
def signalConfig (C : Fin n → AgentState ψ) : Fin n → AgentState 1 :=
  fun i => signalView (C i)

private theorem signal_fire (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (eliminateLeadersNoCollisionFire hψ l r) =
      eliminateLeadersNoCollisionFire (by decide) (signalView l) (signalView r) := by
  by_cases hl : l.leader = true ∧ l.signal_B = 1 <;>
    by_cases hr : r.leader = true ∧ r.signal_B = 1 <;>
      simp [eliminateLeadersNoCollisionFire, signalPair, signalView,
        PeaceView.toState, hl, hr]

private theorem signal_move (hψ : 0 < ψ) (nl : Fin ψ) (l r : AgentState ψ)
    (ha : r.label = nl ∨ (r.leader = true ∧ r.label = ⟨0, hψ⟩)) :
    signalPair (absorbProtectedMove hψ nl l r) =
      absorbProtectedMove (by decide) 0 (signalView l) (signalView r) := by
  by_cases hp : l.leader = true ∧ l.shield = true ∧ r.leader = false ∧ r.bullet = 2 <;>
    by_cases h1 : 0 < r.bullet.val ∧ l.leader = true <;>
      by_cases hk : r.bullet = 2 ∧ l.shield = false <;>
        by_cases h2 : 0 < r.bullet.val ∧ l.leader = false <;>
          simp [absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
            signalPair, signalView, PeaceView.toState, ha, hp, h1, hk, h2] <;>
            cases hl : l.leader <;> simp_all <;> split <;> simp_all

private theorem signal_signal (nl : Fin ψ) (l r : AgentState ψ)
    (ha : r.label = nl ∨ l.leader = true ∨ r.leader = true) :
    signalPair (eliminateLeadersNoCollisionSignalLeaderSink nl l r) =
      eliminateLeadersNoCollisionSignalLeaderSink 0 (signalView l) (signalView r) := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  simp only [signalPair, signalView, PeaceView.toState, ha, true_or, if_true]
  repeat (first | rfl | split) <;> simp_all

private theorem signal_dummy (q : AgentState ψ × AgentState ψ) :
    signalPair (dummyBulletSink q) = dummyBulletSink (signalPair q) := by
  by_cases hp : q.1.leader = true ∧ q.2.leader = false ∧ q.2.bullet = 1 <;>
    simp [dummyBulletSink, signalPair, signalView, PeaceView.toState, hp]

private theorem absorb_frame (hψ : 0 < ψ) (nl : Fin ψ) (l r : AgentState ψ) :
    (absorbProtectedMove hψ nl l r).2.label = r.label ∧
    (absorbProtectedMove hψ nl l r).2.leader = r.leader := by
  unfold absorbProtectedMove eliminateLeadersNoCollisionZeroLeaderEgressMove
  repeat (first | exact ⟨rfl, rfl⟩ | split)

/-- No-free-barrier and zero leader labels make every edge operationally
passable to K2, including its explicit leader-egress exception. The four
physical safety fields therefore simulate the singleton-label K2 row exactly. -/
theorem signal_kernel (hψ : 0 < ψ) (l r : AgentState ψ)
    (ha : r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ ∨
      (r.leader = true ∧ r.label = ⟨0, hψ⟩)) :
    signalPair (sinkKernelC hψ l r) =
      sinkKernelC (by decide) (signalView l) (signalView r) := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let f := eliminateLeadersNoCollisionFire hψ l r
  let m := absorbProtectedMove hψ nl f.1 f.2
  have hf := fire_frame hψ l r
  have hfa : f.2.label = nl ∨ (f.2.leader = true ∧ f.2.label = ⟨0, hψ⟩) := by
    change (eliminateLeadersNoCollisionFire hψ l r).2.label = nl ∨ _
    rw [hf.2.1, hf.2.2.2]
    exact ha
  have hmf := absorb_frame hψ nl f.1 f.2
  have hma : m.2.label = nl ∨ m.1.leader = true ∨ m.2.leader = true := by
    rcases hfa with h | h
    · exact Or.inl (hmf.1.trans h)
    · exact Or.inr (Or.inr (hmf.2.trans h.1))
  have hf' := signal_fire hψ l r
  have hm' := signal_move hψ nl f.1 f.2 hfa
  have hs' := signal_signal nl m.1 m.2 hma
  change signalPair (dummyBulletSink
    (eliminateLeadersNoCollisionSignalLeaderSink nl m.1 m.2)) = _
  rw [signal_dummy, hs']
  change dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink 0
    (signalPair m).1 (signalPair m).2) = _
  rw [hm']
  change dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink 0
    (absorbProtectedMove (by decide) 0 (signalPair f).1 (signalPair f).2).1
    (absorbProtectedMove (by decide) 0 (signalPair f).1 (signalPair f).2).2) = _
  rw [hf']
  unfold sinkKernelC
  have hz : (⟨((signalView l).label.val + 1) % 1, Nat.mod_lt _ (by decide)⟩ : Fin 1) = 0 :=
    Fin.ext (Nat.mod_one _)
  rw [hz]

/-- K2 preserves every stored label on every input, independently of safety. -/
theorem rawStep_label (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n) :
    (rawStep hψ ring C e i).label = (C i).label := by
  have hq := kernelC_labels hψ (C e) (C (ring.rightNeighbor e))
  unfold rawStep updatePair
  split
  · rename_i h
    subst i
    exact hq.1
  · split
    · rename_i _ h
      subst i
      exact hq.2
    · rfl

/-- The pointwise leader output, including its location, is preserved on
the literal safe set when the ring is cyclically labeled. -/
theorem rawStep_leader_of_cyclic (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : OutputSafeConfig hψ ring C)
    (hc : CyclicLabels hψ ring C) (e i : Fin n) :
    (rawStep hψ ring C e i).leader = (C i).leader := by
  classical
  let q := eliminateLeadersNoCollision hψ (C e) (C (ring.rightNeighbor e))
  have heq := aligned_kernel hψ (C e) (C (ring.rightNeighbor e)) (hc e)
  have hf := noCollision_leaders_eq_of_paperSafe hψ ring C hC e
  have hpair :
      (sinkKernelC hψ (C e) (C (ring.rightNeighbor e))).1.leader = q.1.leader ∧
      (sinkKernelC hψ (C e) (C (ring.rightNeighbor e))).2.leader = q.2.leader := by
    rw [heq]
    dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · unfold dummyBulletSink
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
  unfold rawStep updatePair
  split
  · rename_i h
    subst i
    exact hpair.1.trans hf.1
  · split
    · rename_i _ h
      subst i
      exact hpair.2.trans hf.2
    · rfl

/-- The singleton label type satisfies every cyclic label equation. -/
theorem cyclicLabels_one (ring : DirectedRing n) (C : Fin n → AgentState 1) :
    CyclicLabels (by decide) ring C := by
  intro i
  apply Fin.ext
  simp only [Nat.mod_one]
  have h := (C (ring.rightNeighbor i)).label.isLt
  omega

/-- A useful closed strengthening of literal `OutputSafeConfig`: all four
original fields plus fully consecutive labels. No closure is assumed. -/
theorem outputSafe_cyclic_step (hψ : 0 < ψ) (hn : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : OutputSafeConfig hψ ring C ∧ CyclicLabels hψ ring C) (e : Fin n) :
    OutputSafeConfig hψ ring (rawStep hψ ring C e) ∧
      CyclicLabels hψ ring (rawStep hψ ring C e) := by
  refine ⟨rawStep_outputSafe_of_cyclic hψ hn ring C hC.1 hC.2 e, ?_⟩
  intro i
  simpa only [rawStep_label] using hC.2 i

/-- The four physical path conditions, together with the actual zero leader
label and actual no-free-barrier geometry. This reuses `OutputSafeConfig`
on the explicitly defined observation, and contains no future/closure field.
It admits the genuine nondivisible-label egress states excluded by literal
peacefulness. Thus it is a different invariant, not a renamed old safe set. -/
def RowSafe (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  OutputSafeConfig (by decide) ring (signalConfig C) ∧
    (∀ i, (C i).isLeader → (C i).label = ⟨0, hψ⟩) ∧
    noFreeBarrier hψ ring C

/-- Every literal output-safe input satisfies the physical K2 invariant.
Only its label-path condition is forgotten, not any shield or signal fact. -/
theorem rowSafe_of_outputSafe (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : OutputSafeConfig hψ ring C) :
    RowSafe hψ ring C := by
  refine ⟨?_, hC.leader_label_zero, hC.no_free_barrier⟩
  refine
    { unique_leader := hC.unique_leader
      leader_label_zero := ?_
      no_nonpeaceful_bullet := ?_
      no_free_barrier := ?_ }
  · intro i _
    rfl
  · intro i hi
    obtain ⟨_, d, hd, ht, hs, hz, _⟩ := hC.no_nonpeaceful_bullet i hi
    refine ⟨hi, d, hd, ht, hs, hz, ?_⟩
    intro k _
    exact Subsingleton.elim _ _
  · intro i
    dsimp only
    intro hi
    exact False.elim (hi (Subsingleton.elim _ _))

private theorem compatible_edge (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C) (e : Fin n) :
    (C (ring.rightNeighbor e)).label =
        ⟨((C e).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ ∨
      ((C (ring.rightNeighbor e)).leader = true ∧
        (C (ring.rightNeighbor e)).label = ⟨0, hψ⟩) := by
  by_cases hr : (C (ring.rightNeighbor e)).leader = true
  · exact Or.inr ⟨hr, hC.2.1 _ hr⟩
  · exact Or.inl (successor_label_of_noFreeBarrier_of_right_not_leader
      hψ ring C hC.2.2 e hr)

/-- One actual K2 interaction is one interaction in the observed signal
system, at exactly the same edge, without a stutter or scheduler change. -/
theorem signal_rawStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C) (e : Fin n) :
    signalConfig (rawStep hψ ring C e) =
      rawStep (by decide) ring (signalConfig C) e := by
  have hq := signal_kernel hψ (C e) (C (ring.rightNeighbor e))
    (compatible_edge hψ ring C hC e)
  funext i
  simp only [signalConfig, rawStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- Actual leader bits are unchanged under the physical K2 invariant. -/
theorem rawStep_leader (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C) (e i : Fin n) :
    (rawStep hψ ring C e i).leader = (C i).leader := by
  have hproj := congrFun (signal_rawStep hψ ring C hC e) i
  have hlead := congrArg AgentState.leader hproj
  exact hlead.trans (rawStep_leader_of_cyclic (by decide) ring (signalConfig C)
    hC.1 (cyclicLabels_one ring (signalConfig C)) e i)

/-- Every K2 edge preserves the complete physical invariant on every
nontrivial ring, with no divisibility, gap, cleanup, or reachability premise. -/
theorem rowSafe_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C) (e : Fin n) :
    RowSafe hψ ring (rawStep hψ ring C e) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [signal_rawStep hψ ring C hC e]
    exact rawStep_outputSafe_of_cyclic (by decide) hn ring (signalConfig C)
      hC.1 (cyclicLabels_one ring (signalConfig C)) e
  · intro i hi
    rw [rawStep_label]
    exact hC.2.1 i ((rawStep_leader hψ ring C hC e i).symm.trans hi)
  · intro i
    dsimp only
    intro hbar
    change (rawStep hψ ring C e (ring.rightNeighbor i)).leader = true
    rw [rawStep_leader hψ ring C hC]
    apply hC.2.2 i
    simpa only [isBarrier, rawStep_label] using hbar

/-- K2 preserves the physical invariant for every finite scheduler word. -/
theorem rowSafe_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C) (es : List (Fin n)) :
    RowSafe hψ ring (run (rawStep hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (rowSafe_step hψ hn ring C hC e)

/-- Every future finite K2 word preserves the whole original output vector,
not merely the existence or count of leaders. -/
theorem raw_run_output (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C)
    (es : List (Fin n)) (i : Fin n) :
    (run (rawStep hψ ring) C es i).leader = (C i).leader := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
      exact (ih _ (rowSafe_step hψ hn ring C hC e)).trans
        (rawStep_leader hψ ring C hC e i)

/-- The canonical existing safe configuration witnesses nonemptiness for
every positive label modulus and every nonempty ring. -/
theorem rowSafe_inhabited (hψ : 0 < ψ) (ring : DirectedRing n) :
    RowSafe hψ ring (outputCore hψ) :=
  rowSafe_of_outputSafe hψ ring _ (outputCore_safe hψ ring)

/-! ## Exact finite-carrier semantics and all-word consequences -/

variable {κ : Nat}

/-- The actual bounded K2 transition, packaged with its physical leader bit.
This package adds no stored field and has no population-size parameter. -/
def boundedProtocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := BoundedAgentState ψ κ
  Y := Bool
  transition := boundedKernel hψ
  output := fun q => q.leader

/-- The actual counted UCell elimination row and its existing output map. -/
def unifiedProtocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := UCell ψ κ
  Y := Bool
  transition := LDSinkUnifiedFinite.eliminationRow hψ
  output := LDSinkUnifiedFinite.output

/-- The bounded population-protocol interaction erases to one raw K2 edge
on every ring, including rings too small to carry a `GapFrame`. -/
theorem bounded_erase_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → BoundedAgentState ψ κ) (e : Fin n) :
    eraseConfig ((boundedProtocol hψ κ).step ring C e) =
      rawStep hψ ring (eraseConfig C) e := by
  have hq := erase_boundedKernel hψ (C e) (C (ring.rightNeighbor e))
  funext i
  simp only [eraseConfig, PopulationProtocol.step, boundedProtocol, rawStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- The UCell population-protocol interaction has the same one-edge legacy
projection as the existing `LDSinkUnifiedFinite.step`. -/
theorem unified_legacy_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    LDSinkUnifiedFinite.legacyConfig ((unifiedProtocol hψ κ).step ring C e) =
      (boundedProtocol hψ κ).step ring (LDSinkUnifiedFinite.legacyConfig C) e := by
  funext i
  simp only [LDSinkUnifiedFinite.legacyConfig, PopulationProtocol.step,
    unifiedProtocol, boundedProtocol, LDSinkUnifiedFinite.eliminationRow]
  split <;> first | rfl | (split <;> rfl)

/-- Real row closure on the bounded carrier, using the proved raw invariant. -/
theorem bounded_rowSafe_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → BoundedAgentState ψ κ) (hC : RowSafe hψ ring (eraseConfig C))
    (e : Fin n) :
    RowSafe hψ ring (eraseConfig ((boundedProtocol hψ κ).step ring C e)) := by
  rw [bounded_erase_step]
  exact rowSafe_step hψ hn ring _ hC e

/-- Real row closure on UCell; all controller states and traffic tags are
unrestricted, because elimination frames them exactly. -/
theorem unified_rowSafe_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hC : RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)))
    (e : Fin n) :
    RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig
      ((unifiedProtocol hψ κ).step ring C e))) := by
  rw [unified_legacy_step]
  exact bounded_rowSafe_step hψ hn ring _ hC e

/-- Each bounded interaction preserves every output bit under RowSafe. -/
theorem bounded_step_output (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → BoundedAgentState ψ κ) (hC : RowSafe hψ ring (eraseConfig C))
    (e i : Fin n) :
    ((boundedProtocol hψ κ).step ring C e i).leader = (C i).leader := by
  have h := congrFun (bounded_erase_step hψ ring C e) i
  exact (congrArg AgentState.leader h).trans (rawStep_leader hψ ring _ hC e i)

/-- Each UCell interaction preserves the existing physical output map. -/
theorem unified_step_output (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hC : RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)))
    (e i : Fin n) :
    LDSinkUnifiedFinite.output ((unifiedProtocol hψ κ).step ring C e i) =
      LDSinkUnifiedFinite.output (C i) := by
  have h := congrFun (unified_legacy_step hψ ring C e) i
  exact (congrArg BoundedAgentState.leader h).trans
    (bounded_step_output hψ ring _ hC e i)

/-- RowSafe is a proved closed predicate of the actual finite bounded row. -/
theorem bounded_closed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (boundedProtocol hψ κ) ring
      (fun C => RowSafe hψ ring (eraseConfig C)) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact bounded_rowSafe_step hψ hn ring C hC e

/-- RowSafe is a proved closed predicate of the actual UCell elimination
row. This is the local compatibility obligation for a future dispatcher. -/
theorem unified_closed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (unifiedProtocol hψ κ) ring
      (fun C => RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C))) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact unified_rowSafe_step hψ hn ring C hC e

/-- Actual bounded K2 satisfies the existing semantic safety definition:
unique output now and the identical pointwise output in every reachable future. -/
theorem bounded_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → BoundedAgentState ψ κ) (hC : RowSafe hψ ring (eraseConfig C)) :
    PopulationProtocol.IsSafe (boundedProtocol hψ κ) ring C id := by
  apply isSafe_of_operational_legitimacy (boundedProtocol hψ κ) ring id
    (fun C => RowSafe hψ ring (eraseConfig C)) (bounded_closed hψ hn ring)
  · intro D hD
    exact hD.1.unique_leader
  · intro D hD E hstep i
    obtain ⟨e, rfl⟩ := hstep
    exact bounded_step_output hψ ring D hD e i
  · exact hC

/-- Actual UCell elimination satisfies the existing semantic safety
definition, with no controller-coherence or saturation restriction. -/
theorem unified_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hC : RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C))) :
    PopulationProtocol.IsSafe (unifiedProtocol hψ κ) ring C id := by
  apply isSafe_of_operational_legitimacy (unifiedProtocol hψ κ) ring id
    (fun C => RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)))
    (unified_closed hψ hn ring)
  · intro D hD
    exact hD.1.unique_leader
  · intro D hD E hstep i
    obtain ⟨e, rfl⟩ := hstep
    exact unified_step_output hψ ring D hD e i
  · exact hC

/-- The existing bounded word runner stays in the proved invariant and
preserves all leader outputs. Its scheduler word is used without alteration. -/
theorem bounded_run_safe_output (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → BoundedAgentState ψ κ) (hC : RowSafe hψ F.ring (eraseConfig C))
    (es : List (Fin n)) :
    RowSafe hψ F.ring (eraseConfig (run (boundedStep hψ F) C es)) ∧
      ∀ i, (run (boundedStep hψ F) C es i).leader = (C i).leader := by
  have hn : 1 < n := by have := F.hd; have := F.hdn; omega
  constructor
  · rw [erase_run]
    exact rowSafe_run hψ hn F.ring _ hC es
  · intro i
    have h := congrFun (erase_run hψ F C es) i
    exact (congrArg AgentState.leader h).trans (raw_run_output hψ hn F.ring _ hC es i)

/-- The existing UCell word runner preserves RowSafe and every output for
every scheduler word, on the already counted finite carrier. -/
theorem unified_run_safe_output (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → UCell ψ κ)
    (hC : RowSafe hψ F.ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)))
    (es : List (Fin n)) :
    RowSafe hψ F.ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig
      (run (LDSinkUnifiedFinite.step hψ F) C es))) ∧
      ∀ i, LDSinkUnifiedFinite.output (run (LDSinkUnifiedFinite.step hψ F) C es i) =
        LDSinkUnifiedFinite.output (C i) := by
  have hb := bounded_run_safe_output hψ F (LDSinkUnifiedFinite.legacyConfig C) hC es
  constructor
  · rw [LDSinkUnifiedFinite.legacy_run]
    exact hb.1
  · intro i
    have h := congrFun (LDSinkUnifiedFinite.legacy_run hψ F C es) i
    exact (congrArg BoundedAgentState.leader h).trans (hb.2 i)

/-- The already verified canonical raw state, reified with the exact finite
domain constructor. All numeric bounds κ, including zero, are admitted. -/
def boundedCanonical (hψ : 0 < ψ) (κ : Nat) (i : Fin n) :
    BoundedAgentState ψ κ :=
  BoundedAgentState.ofDomain (outputCore hψ i) (outputCore_domain hψ i)

theorem erase_boundedCanonical (hψ : 0 < ψ) (κ : Nat) :
    eraseConfig (boundedCanonical (n := n) hψ κ) = outputCore hψ := by
  funext i
  exact BoundedAgentState.erase_ofDomain _ _

/-- An explicit safe legacy state with every UCell controller independently
arbitrary. Thus no hidden control-state coherence is used by the safety proof. -/
def unifiedCanonical (hψ : 0 < ψ) (κ : Nat)
    (control : Fin n → ShortGapUnifiedNode.UNode) (i : Fin n) : UCell ψ κ :=
  ⟨boundedCanonical hψ κ i, control i⟩

theorem unifiedCanonical_rowSafe (hψ : 0 < ψ) (κ : Nat) (ring : DirectedRing n)
    (control : Fin n → ShortGapUnifiedNode.UNode) :
    RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig
      (unifiedCanonical hψ κ control))) := by
  change RowSafe hψ ring (eraseConfig (boundedCanonical hψ κ))
  rw [erase_boundedCanonical]
  exact rowSafe_inhabited hψ ring

/-- In particular, every original output-safe UCell input has safe output
under every future K2 interaction, even when literal peacefulness later fails. -/
theorem outputSafe_unified_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hC : OutputSafeConfig hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C))) :
    PopulationProtocol.IsSafe (unifiedProtocol hψ κ) ring C id :=
  unified_isSafe hψ hn ring C (rowSafe_of_outputSafe hψ ring _ hC)

/-! ## The exact original predicate on its strengthened cyclic domain -/

/-- Cyclic labels recover literal peacefulness from the physical invariant.
This identifies exactly what the singleton-label observation discarded. -/
theorem outputSafe_of_rowSafe_cyclic (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hψ ring C)
    (hc : CyclicLabels hψ ring C) : OutputSafeConfig hψ ring C := by
  refine
    { unique_leader := hC.1.unique_leader
      leader_label_zero := hC.2.1
      no_nonpeaceful_bullet := ?_
      no_free_barrier := hC.2.2 }
  intro i hi
  obtain ⟨_, d, hd, ht, hs, hz, _⟩ := hC.1.no_nonpeaceful_bullet i hi
  refine ⟨hi, d, hd, ht, hs, hz, ?_⟩
  intro k _
  change (C (cwPos ring i (k + 1))).label =
    ⟨((C (cwPos ring i k)).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  rw [cwPos_succ]
  exact hc (cwPos ring i k)

/-- The strengthened original safe set is closed under all raw K2 words. -/
theorem outputSafe_cyclic_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (hC : OutputSafeConfig hψ ring C ∧ CyclicLabels hψ ring C)
    (es : List (Fin n)) :
    OutputSafeConfig hψ ring (run (rawStep hψ ring) C es) ∧
      CyclicLabels hψ ring (run (rawStep hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (outputSafe_cyclic_step hψ hn ring C hC e)

/-- The strengthened original safe set is closed under the existing UCell
runner. This is exact finite-carrier closure of all four original fields. -/
theorem unified_outputSafe_cyclic_run (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → UCell ψ κ)
    (hC : OutputSafeConfig hψ F.ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)) ∧
      CyclicLabels hψ F.ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)))
    (es : List (Fin n)) :
    let D := eraseConfig (LDSinkUnifiedFinite.legacyConfig
      (run (LDSinkUnifiedFinite.step hψ F) C es))
    OutputSafeConfig hψ F.ring D ∧ CyclicLabels hψ F.ring D := by
  dsimp only
  rw [LDSinkUnifiedFinite.legacy_run, erase_run]
  exact outputSafe_cyclic_run hψ (by have := F.hd; have := F.hdn; omega)
    F.ring _ hC es

/-- Fully consecutive labels necessarily restrict the ring arithmetic.
The general RowSafe and semantic safety theorems do not use this restriction. -/
theorem cyclicLabels_requires_dvd (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hc : CyclicLabels hψ ring C) : ψ ∣ n :=
  dvd_of_all_successor_labels hψ ring C hc

/-- Whenever ψ divides the population size, the existing canonical witness
has fully consecutive labels, including its incoming leader edge. -/
theorem canonical_cyclic_of_dvd (hψ : 0 < ψ) (ring : DirectedRing n)
    (hdvd : ψ ∣ n) : CyclicLabels hψ ring (outputCore hψ) := by
  intro i
  apply Fin.ext
  change (i.val + 1) % n % ψ = (i.val % ψ + 1) % ψ
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact (mod_succ_eq i.val ψ).symm

/-- Nonemptiness of the exact strengthened safe set throughout its full
arithmetic regime, using the original canonical raw witness. -/
theorem outputSafe_cyclic_inhabited (hψ : 0 < ψ) (ring : DirectedRing n)
    (hdvd : ψ ∣ n) :
    OutputSafeConfig hψ ring (outputCore hψ) ∧
      CyclicLabels hψ ring (outputCore hψ) :=
  ⟨outputCore_safe hψ ring, canonical_cyclic_of_dvd hψ ring hdvd⟩

/-- The strengthened exact safe set has an existing canonical witness for
each ring when the label modulus is one. -/
theorem outputSafe_cyclic_inhabited_one (ring : DirectedRing n) :
    OutputSafeConfig (by decide) ring (outputCore (ψ := 1) (by decide)) ∧
      CyclicLabels (by decide) ring (outputCore (ψ := 1) (by decide)) :=
  ⟨outputCore_safe (by decide) ring, cyclicLabels_one ring _⟩

/-! ## Minimal gap-carrier counterexample and explicit finite inhabitants -/

/-- Three is the smallest ring size admitted by the existing GapFrame type. -/
def cutFrame : GapFrame 3 := ⟨⟨by decide⟩, 0, 2, by decide, by decide⟩

/-- The corresponding smallest-modulus nondivisible labeling is `0,1,0`.
The unique leader at zero holds a peaceful live bullet and its shield. -/
def cutTriple (i : Fin 3) : AgentState 2 :=
  if i = 0 then { outputCore (n := 3) (by decide) i with bullet := 2, shield := true }
  else outputCore (n := 3) (by decide) i

theorem cutTriple_safe : OutputSafeConfig (by decide) cutFrame.ring cutTriple := by
  refine
    { unique_leader := ?_
      leader_label_zero := ?_
      no_nonpeaceful_bullet := ?_
      no_free_barrier := ?_ }
  · unfold hasUniqueLeader
    decide
  · decide
  · intro i hi
    have hi0 : i = 0 := by
      rcases fin3_cases i with h | h | h
      · exact h
      · subst i
        exact False.elim ((by decide : (cutTriple 1).bullet ≠ 2) hi)
      · subst i
        exact False.elim ((by decide : (cutTriple 2).bullet ≠ 2) hi)
    subst i
    apply peacefulBullet_zero
    all_goals decide
  · unfold noFreeBarrier isBarrier
    decide

/-- The exact existing `sinkStepC`, with a real GapFrame, violates the old
peaceful label condition on edge `2 → 0` while retaining the unique leader. -/
theorem cutTriple_not_safe_after :
    ¬ OutputSafeConfig (by decide) cutFrame.ring
      (sinkStepC (by decide) cutFrame cutTriple 2) := by
  intro hs
  have hp := hs.no_nonpeaceful_bullet 2 (by decide)
  obtain ⟨_, d, _, _, _, _, hlab⟩ := hp
  have hv := congrArg Fin.val (hlab 0 (Nat.zero_le d))
  change 0 = (0 + 1) % 2 at hv
  omega

/-- The same three-agent failure occurs from the existing unarmed canonical
witness, without a forged bullet: four interactions prepare a live shot,
and the fifth moves it across the cut. -/
theorem canonical_three_agent_escape :
    ¬ OutputSafeConfig (by decide) cutFrame.ring
      (run (sinkStepC (ψ := 2) (by decide) cutFrame)
        (outputCore (n := 3) (by decide)) [0, 1, 2, 0, 2]) := by
  intro hs
  have hp := hs.no_nonpeaceful_bullet 2 (by decide)
  obtain ⟨_, d, _, _, _, _, hlab⟩ := hp
  have hv := congrArg Fin.val (hlab 0 (Nat.zero_le d))
  change 0 = (0 + 1) % 2 at hv
  omega

private theorem cutTriple_domain (i : Fin 3) : (cutTriple i).inProtocolDomain 0 := by
  unfold cutTriple
  split <;> exact outputCore_domain (ψ := 2) (κ := 0) (by decide) i

/-- A concrete controller value for nonemptiness only. The theorems above
permit every controller and do not test or reset this value. -/
private def witnessControl : ShortGapUnifiedNode.UNode :=
  { core := ⟨ShortGapCaptureCommitRows.emptyRaw, false, .capturing, .unreserved, .none⟩
    bridge := none
    payload := none
    splice := .inactive
    witness := .none
    flush := .none
    traffic := .empty }

/-- The three-agent raw counterexample encoded in the actual counted carrier,
with every unbounded legacy field reified at κ = 0. -/
def finiteCut (i : Fin 3) : UCell 2 0 :=
  ⟨BoundedAgentState.ofDomain (cutTriple i) (cutTriple_domain i), witnessControl⟩

private theorem erase_finiteCut :
    eraseConfig (LDSinkUnifiedFinite.legacyConfig finiteCut) = cutTriple := by
  funext i
  exact BoundedAgentState.erase_ofDomain (cutTriple i) (cutTriple_domain i)

/-- An actual one-interaction UCell counterexample to closure of the old
OutputSafeConfig, with smallest possible GapFrame ring and modulus two. -/
theorem finiteCut_counterexample :
    OutputSafeConfig (by decide) cutFrame.ring
      (eraseConfig (LDSinkUnifiedFinite.legacyConfig finiteCut)) ∧
    ¬ OutputSafeConfig (by decide) cutFrame.ring
      (eraseConfig (LDSinkUnifiedFinite.legacyConfig
        (LDSinkUnifiedFinite.step (by decide) cutFrame finiteCut 2))) := by
  constructor
  · rw [erase_finiteCut]
    exact cutTriple_safe
  · rw [LDSinkUnifiedFinite.legacy_step, erase_boundedStep, erase_finiteCut]
    exact cutTriple_not_safe_after

/-- The true physical invariant still holds after the counterexample step;
literal label-path failure does not mean loss of semantic output safety. -/
theorem finiteCut_after_isSafe :
    PopulationProtocol.IsSafe (unifiedProtocol (by decide) 0) cutFrame.ring
      (LDSinkUnifiedFinite.step (by decide) cutFrame finiteCut 2) id := by
  apply unified_isSafe (by decide) (by decide) cutFrame.ring
  change RowSafe (by decide) cutFrame.ring
    (eraseConfig (LDSinkUnifiedFinite.legacyConfig
      ((unifiedProtocol (by decide) 0).step cutFrame.ring finiteCut 2)))
  apply unified_rowSafe_step (by decide) (by decide) cutFrame.ring
  exact rowSafe_of_outputSafe (by decide) cutFrame.ring _ finiteCut_counterexample.1

/-- A concrete finite inhabitant exists for all positive ψ, all κ, and all
nonempty rings; there is no carried producer or coherence premise. -/
theorem unified_inhabited (hψ : 0 < ψ) (κ : Nat) (ring : DirectedRing n) :
    ∃ C : Fin n → UCell ψ κ,
      RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)) :=
  ⟨unifiedCanonical hψ κ (fun _ => witnessControl),
    unifiedCanonical_rowSafe hψ κ ring _⟩

/-- The actual counted K2 row has a nonempty proved closed safe set, and
every member satisfies the existing semantic leader-election safety notion.
Other dispatcher rows must preserve this concrete predicate and output vector. -/
theorem unified_capstone (hψ : 0 < ψ) (κ : Nat) (hn : 1 < n) (ring : DirectedRing n) :
    (∃ C : Fin n → UCell ψ κ,
      RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C))) ∧
    PopulationProtocol.ClosedPred (unifiedProtocol hψ κ) ring
      (fun C => RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C))) ∧
    (∀ C : Fin n → UCell ψ κ,
      RowSafe hψ ring (eraseConfig (LDSinkUnifiedFinite.legacyConfig C)) →
      PopulationProtocol.IsSafe (unifiedProtocol hψ κ) ring C id) :=
  ⟨unified_inhabited hψ κ ring, unified_closed hψ hn ring,
    fun C hC => unified_isSafe hψ hn ring C hC⟩

end K2OutputSafety

#print axioms K2OutputSafety.cutPair_safe
#print axioms K2OutputSafety.cutPair_not_safe_after
#print axioms K2OutputSafety.canonical_two_agent_escape
#print axioms K2OutputSafety.finiteCut_counterexample
#print axioms K2OutputSafety.canonical_three_agent_escape
#print axioms K2OutputSafety.rowSafe_step
#print axioms K2OutputSafety.unified_closed
#print axioms K2OutputSafety.unified_run_safe_output
#print axioms K2OutputSafety.unified_outputSafe_cyclic_run
#print axioms K2OutputSafety.outputSafe_cyclic_inhabited
#print axioms K2OutputSafety.unified_capstone
#print axioms K2OutputSafety.outputSafe_unified_isSafe
#print axioms K2OutputSafety.finiteCut_after_isSafe
