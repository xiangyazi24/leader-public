import Leader.Wu.Comparison.HistoryIntegrated

/-!
# Algorithm-7 comparison-wave obstruction

Wu's Algorithm 7 independently reinitializes every label-zero initiator to
`congest` before processing its lock/return state machine. Under stable directed
label adjacency, the forward wave can create `lock` only at label zero; when
that lock next initiates, line 1 destroys it before the branch that could create
`compare1`. The literal transition therefore cannot bootstrap
`compare1`, `compare2`, or `path2` from a clean generated carrier.

This module separates two facts. The source lane proves a structural invariant
of literal `cmpUpdate` and lifts it through every finite CMP_UPDATE-only
schedule. The repair lane proves that `cmpUpdateNoSourceRearm` is even more
inert on completed `.depart` carriers. Neither result is promoted to a theorem
about all of Algorithm 1, whose other stages may inject arbitrary comparison
states from a self-stabilizing input.
-/

namespace PPLLComparisonWaveObstruction

open PPLL PPLLRepair PPLLResearchFormulation

/-- No return-wave state or path2 control has yet been created at one agent. -/
def ComparisonWaveAbsent (s : AgentState ψ) : Prop :=
  s.state ≠ .compare1 ∧ s.state ≠ .compare2 ∧ s.path2 = none

/-- Every lock produced by the forward wave is located at label zero. -/
def LockAtZero (s : AgentState ψ) : Prop :=
  s.state = .lock → s.label.val = 0

/-- The responder carries the cyclic successor label of the initiator. -/
def LabelsAdvance (hψ : ψ > 0) (l r : AgentState ψ) : Prop :=
  r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩

set_option maxHeartbeats 1000000 in
/-- Literal CMP_UPDATE preserves the pre-comparison region when labels advance
on the directed edge. The proof follows every printed branch. The only new
lock comes from a terminal congest initiator, whose successor label is zero;
line 1 makes every label-zero lock unavailable to the compare1 branch. -/
theorem cmpUpdate_preserves_comparisonWaveAbsent
    (hψ : ψ > 0) (hψone : ψ > 1) (l r : AgentState ψ)
    (hadj : LabelsAdvance hψ l r)
    (hl : ComparisonWaveAbsent l) (hr : ComparisonWaveAbsent r)
    (hllock : LockAtZero l) (hrlock : LockAtZero r) :
    let q := cmpUpdate hψ l r
    ComparisonWaveAbsent q.1 ∧ ComparisonWaveAbsent q.2 ∧
      LockAtZero q.1 ∧ LockAtZero q.2 := by
  have hmodOne : 1 % ψ = 1 := Nat.mod_eq_of_lt hψone
  have hsubadd : ψ - 1 + 1 = ψ := by omega
  have hmodWrap : (ψ - 1 + 1) % ψ = 0 := by
    rw [hsubadd, Nat.mod_self]
  unfold cmpUpdate cmpUpdatePropagate cmpUpdateSetPath2
    ComparisonWaveAbsent LockAtZero LabelsAdvance at *
  dsimp only
  split <;> rename_i hstart
  all_goals repeat' first | split | constructor
  all_goals simp_all [Fin.ext_iff]
  all_goals omega

/-- Algorithm 7 never changes either endpoint label. -/
theorem cmpUpdate_label_frame (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := cmpUpdate hψ l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  unfold cmpUpdate cmpUpdatePropagate cmpUpdateSetPath2
  dsimp only
  repeat (first | constructor | rfl | split)

/-- Configuration surface on which the literal Algorithm-7 obstruction is
inductive: every cell is pre-comparison, locks sit at zero, and every directed
edge has cyclic successor labels. -/
def CmpConfigInvariant (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  (∀ i, ComparisonWaveAbsent (C i) ∧ LockAtZero (C i)) ∧
    (∀ i, LabelsAdvance hψ (C i) (C (ring.rightNeighbor i)))

/-- One literal CMP_UPDATE edge preserves the global obstruction. Label
preservation handles all edges adjacent to the two updated positions uniformly,
including the one-agent first-output convention. -/
theorem cmpUpdate_step_preserves
    (hψ : ψ > 0) (hψone : ψ > 1) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : CmpConfigInvariant hψ ring C)
    (e : Fin n) :
    CmpConfigInvariant hψ ring (stepConfig ring (cmpUpdate hψ) C e) := by
  let j := ring.rightNeighbor e
  let q := cmpUpdate hψ (C e) (C j)
  have hpair := cmpUpdate_preserves_comparisonWaveAbsent
    hψ hψone (C e) (C j) (hC.2 e)
      (hC.1 e).1 (hC.1 j).1 (hC.1 e).2 (hC.1 j).2
  change ComparisonWaveAbsent q.1 ∧ ComparisonWaveAbsent q.2 ∧
    LockAtZero q.1 ∧ LockAtZero q.2 at hpair
  have hlabels := cmpUpdate_label_frame hψ (C e) (C j)
  change q.1.label = (C e).label ∧ q.2.label = (C j).label at hlabels
  have hcell : ∀ k, ComparisonWaveAbsent
      (stepConfig ring (cmpUpdate hψ) C e k) ∧
        LockAtZero (stepConfig ring (cmpUpdate hψ) C e k) := by
    intro k
    by_cases hke : k = e
    · subst k
      simpa [stepConfig, j, q] using ⟨hpair.1, hpair.2.2.1⟩
    · by_cases hkj : k = j
      · have hje : j ≠ e := by
          intro hbad
          exact hke (hkj.trans hbad)
        simpa [stepConfig, j, q, hke, hkj, hje] using
          ⟨hpair.2.1, hpair.2.2.2⟩
      · simpa [stepConfig, j, hke, hkj] using hC.1 k
  have hlabelFrame : ∀ k,
      (stepConfig ring (cmpUpdate hψ) C e k).label = (C k).label := by
    intro k
    by_cases hke : k = e
    · subst k
      simpa [stepConfig, j, q] using hlabels.1
    · by_cases hkj : k = j
      · have hje : j ≠ e := by
          intro hbad
          exact hke (hkj.trans hbad)
        simpa [stepConfig, j, q, hke, hkj, hje] using hlabels.2
      · simp [stepConfig, j, hke, hkj]
  refine ⟨hcell, ?_⟩
  intro i
  have hadj := hC.2 i
  unfold LabelsAdvance at hadj ⊢
  calc
    (stepConfig ring (cmpUpdate hψ) C e
        (ring.rightNeighbor i)).label =
        (C (ring.rightNeighbor i)).label :=
      hlabelFrame (ring.rightNeighbor i)
    _ = ⟨((C i).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ := hadj
    _ = ⟨((stepConfig ring (cmpUpdate hψ) C e i).label.val + 1) % ψ,
          Nat.mod_lt _ hψ⟩ := by
      apply Fin.ext
      exact congrArg (fun x : Fin ψ => (x.val + 1) % ψ)
        (hlabelFrame i).symm

/-- Every finite CMP_UPDATE-only schedule preserves the comparison-wave
obstruction. This is structural schedule induction, not finite enumeration. -/
theorem cmpUpdate_schedule_preserves
    (hψ : ψ > 0) (hψone : ψ > 1) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : CmpConfigInvariant hψ ring C)
    (s : DetSchedule n) :
    CmpConfigInvariant hψ ring
      (applySchedule ring (cmpUpdate hψ) C s) := by
  induction s generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      simp only [applySchedule]
      exact ih _ (cmpUpdate_step_preserves hψ hψone ring C hC e)

/-! ## Non-vacuous ψ=2 clean carrier -/

private def cleanCmp0 : AgentState 2 :=
  { PPLLCounterexample.state2 0 false .depart with path := .some 0 0 }

private def cleanCmp1 : AgentState 2 :=
  { PPLLCounterexample.state2 1 false .depart with path := .some 1 0 }

private abbrev cleanCmpRing : DirectedRing 2 := ⟨by omega⟩

private def cleanCmpConfig : Fin 2 → AgentState 2
  | ⟨0, _⟩ => cleanCmp0
  | ⟨1, _⟩ => cleanCmp1

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · exact .inl (Fin.ext hi)
  · exact .inr (Fin.ext hi)

/-- The structural invariant has a concrete completed-carrier inhabitant. -/
theorem cleanCmpConfig_invariant :
    CmpConfigInvariant (by omega : 2 > 0) cleanCmpRing cleanCmpConfig := by
  constructor
  · intro i
    rcases fin2_cases i with rfl | rfl <;>
      simp [cleanCmpConfig, cleanCmp0, cleanCmp1,
        PPLLCounterexample.state2, ComparisonWaveAbsent, LockAtZero]
  · intro i
    rcases fin2_cases i with rfl | rfl <;>
      simp [LabelsAdvance, cleanCmpConfig,
        DirectedRing.rightNeighbor, cleanCmp0, cleanCmp1,
        PPLLCounterexample.state2]

/-- No finite literal CMP_UPDATE schedule from the clean ψ=2 carrier can create
a comparison state or path2 at either ring position. -/
theorem cleanCmpConfig_never_creates_comparison
    (s : DetSchedule 2) (i : Fin 2) :
    ComparisonWaveAbsent
      (applySchedule cleanCmpRing (cmpUpdate (by omega)) cleanCmpConfig s i) := by
  exact (cmpUpdate_schedule_preserves (by omega) (by omega)
    cleanCmpRing cleanCmpConfig cleanCmpConfig_invariant s).1 i |>.1

/-! ## The no-source-rearm repair is inert on completed carriers -/

/-- On two completed departing components, repaired CMP_UPDATE is exactly the
identity; present paths cannot compensate for the disabled state wave. -/
theorem cmpUpdateNoSourceRearm_depart_identity
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.state = .depart) (hr : r.state = .depart)
    (_hlpath2 : l.path2 = none) :
    cmpUpdateNoSourceRearm hψ l r = (l, r) := by
  cases hpath : l.path <;>
    simp [cmpUpdateNoSourceRearm, cmpUpdatePropagate,
      cmpUpdateSetPath2, hl, hr, hpath]

/-- Full repaired COMPARE is also identity when both completed path components
are present and neither endpoint has path2 control. -/
theorem compareSigNoSourceRearm_depart_identity
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.state = .depart) (hr : r.state = .depart)
    (hlpath : l.path ≠ .bot) (hrpath : r.path ≠ .bot)
    (hlpath2 : l.path2 = none) (hrpath2 : r.path2 = none) :
    compareSigNoSourceRearm hψ l r = (l, r) := by
  cases hpl : l.path with
  | bot => exact (hlpath hpl).elim
  | some leftLabel leftBit =>
      cases hpr : r.path with
      | bot => exact (hrpath hpr).elim
      | some rightLabel rightBit =>
          have hcmp := cmpUpdateNoSourceRearm_depart_identity
            hψ l r hl hr hlpath2
          simp [compareSigNoSourceRearm, compareSigInit, hpl, hpr,
            hcmp, compareSigDispatch, hlpath2, hrpath2]

end PPLLComparisonWaveObstruction
