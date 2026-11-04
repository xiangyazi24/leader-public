import Leader.AAFJ.ElectionTheorem


set_option autoImplicit false
set_option Elab.async false


namespace AAFJPK.FairExecutionWitness


open PopulationProtocol.GlobalFairness


private theorem hk2 : 0 < 2 := by
  decide


def ring3 : DirectedRing 3 :=
  ⟨by decide⟩


private structure Snapshot where
  s0 : State 2
  s1 : State 2
  s2 : State 2
deriving DecidableEq, Repr


private def st
    (bullet leader : Bool) (label : Fin 2)
    (probe phase : Bool) : State 2 where
  bullet := bullet
  leader := leader
  label := label
  probe := probe
  phase := phase


private def snap (s0 s1 s2 : State 2) : Snapshot :=
  ⟨s0, s1, s2⟩


private def configOf (q : Snapshot) : Fin 3 → State 2 :=
  fun i =>
    if i = (0 : Fin 3) then q.s0
    else if i = (1 : Fin 3) then q.s1
    else q.s2


private def snapshotOf (C : Fin 3 → State 2) : Snapshot :=
  ⟨C 0, C 1, C 2⟩


private theorem fin3_cases (i : Fin 3) :
    i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    omega
  rcases h with h0 | h1 | h2
  · left
    exact Fin.ext h0
  · right
    left
    exact Fin.ext h1
  · right
    right
    exact Fin.ext h2


private theorem configOf_snapshotOf (C : Fin 3 → State 2) :
    configOf (snapshotOf C) = C := by
  funext i
  rcases fin3_cases i with rfl | rfl | rfl <;>
    simp [configOf, snapshotOf]


private def snapshotStep (q : Snapshot) (e : Fin 3) : Snapshot :=
  snapshotOf ((protocol 2 hk2).step ring3 (configOf q) e)


private theorem configOf_snapshotStep (q : Snapshot) (e : Fin 3) :
    configOf (snapshotStep q e) =
      (protocol 2 hk2).step ring3 (configOf q) e := by
  simpa [snapshotStep] using
    configOf_snapshotOf ((protocol 2 hk2).step ring3 (configOf q) e)


/-- The concrete start configuration from the question. -/
def S : Fin 3 → State 2 :=
  configOf
    (snap
      (st false false 1 false true)
      (st true false 0 false true)
      (st false true 1 false true))


/-- The supplied 254-letter closed walk. -/
def W : List (Fin 3) :=
  [0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 0, 2, 1, 2, 1, 2, 0, 0, 1, 0, 2, 0, 0, 1, 1, 2, 0, 2, 1, 2, 1, 2, 0, 0, 1, 1, 2, 1, 2, 0, 2, 1, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 1, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 1, 0, 1, 1, 2, 1, 1, 2, 0, 2, 1, 1, 2, 0, 2, 1, 0, 1, 1, 2, 1, 1, 2, 0, 2, 1, 0, 1, 0, 1, 1, 2, 2, 0, 2, 2, 0, 1, 0, 1, 1, 2, 2, 0, 2, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 1, 1, 0, 2, 1, 1, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 1, 1, 0, 2, 1, 1, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 2, 0, 1, 1, 2, 0, 1, 0, 1, 1, 2, 0, 1]


set_option maxRecDepth 4096 in
private theorem W_length : W.length = 254 := by
  rfl


/-!
The 42 snapshots below are exactly the distinct configurations encountered
along W, in first-appearance order.  The phase-id table has one entry for each
of the 254 scheduler positions.  Keeping equality on this finite snapshot
carrier avoids any DecidableEq assumption for function-valued configurations.
-/
private def componentStates : List Snapshot := [
  snap (st false false 1 false true) (st true false 0 false true) (st false true 1 false true),
  snap (st true false 1 false true) (st false false 0 false true) (st false true 1 false true),
  snap (st true false 1 false true) (st true false 0 false true) (st false true 1 false true),
  snap (st false false 0 false false) (st false false 0 false true) (st false true 1 false true),
  snap (st false false 0 false true) (st false false 0 true true) (st false true 1 false true),
  snap (st false false 0 false true) (st true false 0 false true) (st false true 1 false true),
  snap (st false false 0 false true) (st false false 1 false false) (st false true 1 false true),
  snap (st false false 0 false true) (st false false 1 false true) (st false true 1 false true),
  snap (st false false 0 false true) (st false false 1 false true) (st false true 0 false false),
  snap (st false false 0 false true) (st true false 1 false true) (st false true 0 false false),
  snap (st true false 0 false true) (st false false 1 false true) (st false true 0 false false),
  snap (st true false 0 false true) (st true false 1 false true) (st false true 0 false false),
  snap (st true false 0 true true) (st false false 1 false true) (st false true 0 false true),
  snap (st true false 0 false true) (st false false 1 true true) (st false true 0 false true),
  snap (st true false 0 false true) (st true false 1 false true) (st false true 0 false true),
  snap (st true false 0 false true) (st false false 1 false true) (st false true 0 false true),
  snap (st false false 1 false false) (st true false 1 false true) (st false true 0 false true),
  snap (st false false 1 false true) (st true false 1 true true) (st false true 0 false true),
  snap (st false false 1 false true) (st true false 1 false true) (st false true 0 false true),
  snap (st false false 1 false true) (st false false 0 false false) (st false true 0 false true),
  snap (st false false 1 false true) (st false false 0 false true) (st false true 0 false true),
  snap (st false false 1 false true) (st false false 0 false true) (st false true 1 false false),
  snap (st false false 1 false true) (st true false 0 false true) (st false true 1 false false),
  snap (st true false 1 false true) (st false false 0 false true) (st false true 1 false false),
  snap (st true false 1 false true) (st true false 0 false true) (st false true 1 false false),
  snap (st true false 1 true true) (st false false 0 false true) (st false true 1 false true),
  snap (st true false 1 false true) (st false false 0 true true) (st false true 1 false true),
  snap (st false false 0 false false) (st true false 0 false true) (st false true 1 false true),
  snap (st false false 0 false true) (st true false 0 true true) (st false true 1 false true),
  snap (st false false 0 true true) (st false false 1 false true) (st false true 0 false true),
  snap (st false false 0 false true) (st false false 1 true true) (st false true 0 false true),
  snap (st false false 0 false true) (st true false 1 false true) (st false true 0 false true),
  snap (st false false 1 false false) (st false false 1 false true) (st false true 0 false true),
  snap (st false false 1 false true) (st false false 1 true true) (st false true 0 false true),
  snap (st false false 1 true true) (st false false 0 false true) (st false true 1 false true),
  snap (st false false 1 false true) (st false false 0 true true) (st false true 1 false true),
  snap (st false false 0 true true) (st true false 1 false true) (st false true 0 false true),
  snap (st false false 1 false false) (st false false 1 true true) (st false true 0 false true),
  snap (st false false 1 true true) (st true false 0 false true) (st false true 1 false true),
  snap (st false false 0 false false) (st false false 0 true true) (st false true 1 false true),
  snap (st true false 0 true true) (st true false 1 false true) (st false true 0 false true),
  snap (st true false 1 true true) (st true false 0 false true) (st false true 1 false true)
]


private theorem componentStates_length : componentStates.length = 42 := by
  rfl


private def componentState (i : Fin 42) : Snapshot :=
  componentStates.get
    ⟨i.val, by
      rw [componentStates_length]
      exact i.isLt⟩


private def phaseIds : List (Fin 42) :=
  [0, 1, 1, 2, 1, 3, 4, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 10, 11, 10, 12, 13, 13, 14, 15, 15, 14, 14, 16, 17, 17, 18, 19, 19, 20, 20, 21, 21, 22, 23, 23, 24, 23, 25, 26, 26, 2, 2, 27, 28, 28, 5, 5, 5, 6, 6, 7, 7, 8, 29, 30, 30, 31, 15, 32, 33, 33, 18, 18, 18, 19, 19, 20, 20, 21, 34, 35, 35, 0, 0, 27, 27, 27, 28, 28, 5, 6, 7, 8, 9, 9, 36, 13, 37, 33, 33, 18, 19, 20, 21, 22, 22, 38, 26, 39, 4, 4, 5, 6, 7, 8, 29, 36, 36, 36, 13, 37, 16, 16, 16, 17, 17, 18, 19, 20, 21, 34, 38, 38, 38, 26, 39, 27, 28, 5, 6, 7, 8, 29, 29, 30, 37, 37, 33, 18, 19, 20, 21, 34, 34, 35, 39, 39, 4, 5, 6, 7, 8, 9, 10, 11, 11, 40, 13, 14, 15, 32, 16, 17, 18, 19, 20, 21, 22, 23, 24, 24, 41, 26, 2, 1, 3, 27, 28, 5, 6, 7, 8, 9, 10, 12, 40, 40, 40, 13, 14, 15, 32, 32, 33, 18, 19, 20, 21, 22, 23, 25, 41, 41, 41, 26, 2, 1, 3, 3, 4, 5, 6, 7, 8, 9, 10, 12, 12, 13, 37, 33, 18, 19, 20, 21, 22, 23, 25, 25, 26, 39, 4, 5, 6, 7, 8, 29, 30, 31, 31, 16, 17, 18, 19, 20, 21, 34, 35]


set_option maxRecDepth 4096 in
private theorem phaseIds_length : phaseIds.length = 254 := by
  rfl


private def phaseId (i : Fin 254) : Fin 42 :=
  phaseIds.get
    ⟨i.val, by
      rw [phaseIds_length]
      exact i.isLt⟩


private def phaseSnapshot (i : Fin 254) : Snapshot :=
  componentState (phaseId i)


private def phaseLetter (i : Fin 254) : Fin 3 :=
  W.get
    ⟨i.val, by
      rw [W_length]
      exact i.isLt⟩


private def nextPhase (i : Fin 254) : Fin 254 :=
  ⟨(i.val + 1) % 254, Nat.mod_lt _ (by decide)⟩


private def phaseIndex (t : Nat) : Fin 254 :=
  ⟨t % 254, Nat.mod_lt _ (by decide)⟩


/-- The infinite periodic trajectory. -/
def cyc (t : Nat) : Fin 3 → State 2 :=
  configOf (phaseSnapshot (phaseIndex t))


private theorem phaseIndex_succ (t : Nat) :
    phaseIndex (t + 1) = nextPhase (phaseIndex t) := by
  apply Fin.ext
  change (t + 1) % 254 = (t % 254 + 1) % 254
  rw [Nat.add_mod]


private theorem phase_zero_is_S : cyc 0 = S := by
  rfl


private theorem phase_step_snapshot :
    ∀ i : Fin 254,
      snapshotStep (phaseSnapshot i) (phaseLetter i) =
        phaseSnapshot (nextPhase i) := by
  decide +kernel


/-- For each snapshot id `k` and letter `e`, the first position of `W` whose snapshot id is
`k` and whose letter is `e` (computed from `phaseIds` and `W`; checked by `coverWitness_spec`). -/
private def coverTable : List (List Nat) := [
  [0, 78, 79], [1, 2, 4], [3, 46, 47], [5, 181, 213], [6, 7, 105], [8, 51, 52], [9, 10, 54],
  [11, 12, 56], [13, 14, 58], [15, 89, 90], [16, 17, 19], [18, 160, 161], [20, 190, 222],
  [21, 22, 92], [23, 26, 27], [24, 25, 63], [28, 117, 118], [29, 30, 120], [31, 67, 68],
  [32, 33, 70], [34, 35, 72], [36, 37, 74], [38, 100, 101], [39, 40, 42], [41, 175, 176],
  [43, 206, 233], [44, 45, 103], [48, 80, 81], [49, 50, 83], [59, 111, 138], [60, 61, 140],
  [62, 244, 245], [64, 166, 197], [65, 66, 94], [75, 126, 148], [76, 77, 150], [91, 112, 113],
  [93, 116, 141], [102, 127, 128], [104, 131, 151], [162, 191, 192], [177, 207, 208]
]

private def coverWitness (k : Fin 42) (e : Fin 3) : Fin 254 :=
  ⟨((coverTable.getD k.val []).getD e.val 0) % 254, Nat.mod_lt _ (by decide)⟩

/-- The table is correct: 126 lookups, instead of searching all 254 positions for each of
the 254 positions and comparing snapshots (about 150 s for each letter). -/
private theorem coverWitness_spec :
    ∀ k : Fin 42, ∀ e : Fin 3,
      phaseId (coverWitness k e) = k ∧ phaseLetter (coverWitness k e) = e := by
  decide +kernel

/-- A snapshot occurs with every letter: whether position `j` serves position `i` depends only
on the snapshot id, so the witness is read from `coverWitness`. -/
private theorem phase_pair_cover (i : Fin 254) (e : Fin 3) :
    ∃ j : Fin 254,
      phaseSnapshot j = phaseSnapshot i ∧ phaseLetter j = e := by
  obtain ⟨h1, h2⟩ := coverWitness_spec (phaseId i) e
  exact ⟨coverWitness (phaseId i) e, by unfold phaseSnapshot; rw [h1], h2⟩


private theorem phase_step_config (i : Fin 254) :
    (protocol 2 hk2).step ring3
        (configOf (phaseSnapshot i)) (phaseLetter i) =
      configOf (phaseSnapshot (nextPhase i)) := by
  exact (configOf_snapshotStep (phaseSnapshot i) (phaseLetter i)).symm.trans
    (congrArg configOf (phase_step_snapshot i))


private theorem phase_successor_in_cycle (i : Fin 254) (e : Fin 3) :
    ∃ j : Fin 254,
      (protocol 2 hk2).step ring3
          (configOf (phaseSnapshot i)) e =
        configOf (phaseSnapshot j) := by
  obtain ⟨j, hstate, hedge⟩ := phase_pair_cover i e
  refine ⟨nextPhase j, ?_⟩
  have h1 : (protocol 2 hk2).step ring3
        (configOf (phaseSnapshot i)) e =
      (protocol 2 hk2).step ring3
        (configOf (phaseSnapshot j)) (phaseLetter j) := by
    rw [← hstate, ← hedge]
  exact h1.trans (phase_step_config j)


private theorem phase_occursInfinitelyOften (j : Fin 254) :
    PopulationProtocol.GlobalFairness.OccursInfinitelyOften
      cyc (configOf (phaseSnapshot j)) := by
  intro cutoff
  let t := 254 * cutoff + j.val
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    omega
  · have hmod : t % 254 = j.val := by
      dsimp [t]
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt j.isLt]
    have hidx : phaseIndex t = j := by
      apply Fin.ext
      exact hmod
    change configOf (phaseSnapshot (phaseIndex t)) =
      configOf (phaseSnapshot j)
    rw [hidx]


/-- Every consecutive pair of cyc is a literal Protocol-6 one-step move. -/
theorem cyc_legal :
    PopulationProtocol.GlobalFairness.InfiniteExecution
      (protocol 2 (by decide)) ring3 cyc := by
  intro t
  refine ⟨phaseLetter (phaseIndex t), ?_⟩
  change cyc (t + 1) =
    (protocol 2 hk2).step ring3 (cyc t)
      (phaseLetter (phaseIndex t))
  show configOf (phaseSnapshot (phaseIndex (t + 1))) =
    (protocol 2 hk2).step ring3
      (configOf (phaseSnapshot (phaseIndex t))) (phaseLetter (phaseIndex t))
  rw [phaseIndex_succ]
  exact (phase_step_config (phaseIndex t)).symm


/-- Every configuration that occurs on cyc recurs after every cutoff. -/
theorem cyc_occursInfinitelyOften
    {x : Fin 3 → State 2}
    (hx : ∃ t : Nat, cyc t = x) :
    PopulationProtocol.GlobalFairness.OccursInfinitelyOften cyc x := by
  obtain ⟨t, ht⟩ := hx
  have hphase := phase_occursInfinitelyOften (phaseIndex t)
  have heq :
      configOf (phaseSnapshot (phaseIndex t)) = x := by
    simpa [cyc] using ht
  rw [← heq]
  exact hphase


/-- The periodic walk is globally fair in the AAFJ result-state sense. -/
theorem cyc_globalFair :
    PopulationProtocol.GlobalFairness.GlobalFair
      (protocol 2 (by decide)) ring3 cyc := by
  intro state next hstep hinfinite
  obtain ⟨e, hnext⟩ := hstep
  obtain ⟨t, _, ht⟩ := hinfinite 0
  let i := phaseIndex t
  have hstate :
      state = configOf (phaseSnapshot i) := by
    exact ht.symm
  obtain ⟨j, hsucc⟩ := phase_successor_in_cycle i e
  have hnextPhase :
      next = configOf (phaseSnapshot j) := by
    rw [hnext, hstate]
    exact hsucc
  rw [hnextPhase]
  exact phase_occursInfinitelyOften j


/-- Hence the global-fairness hypothesis used by the paper theorem is inhabited. -/
theorem exists_globallyFairExecution :
    ∃ exec : Nat → (Fin 3 → State 2),
      PopulationProtocol.GlobalFairness.GloballyFairExecution
        (protocol 2 (by decide)) ring3 exec := by
  exact ⟨cyc, ⟨cyc_legal, cyc_globalFair⟩⟩


private theorem odd3 : AAFJPaper9.OddRing 3 := by
  refine ⟨by decide, 1, ?_⟩
  decide


/-- Theorem 9.3 is non-vacuous on the explicit globally fair n=3 execution. -/
theorem paperTheorem9_3_nonvacuous :
    ∃ t : Nat, ∃ ell : Fin 3,
      ∀ s : Nat, t ≤ s →
        AAFJPaper9.PaperCleanForLeader
          (by decide) ring3 ell (cyc s) := by
  have hexec :
      PopulationProtocol.GlobalFairness.GloballyFairExecution
        (protocol 2 (by decide)) ring3 cyc :=
    ⟨cyc_legal, cyc_globalFair⟩
  obtain ⟨t, ell, hstable⟩ :=
    AAFJPaper9Complete.paperTheorem9_3 odd3 ring3 hexec
  refine ⟨t, ell, ?_⟩
  intro s hts
  exact (hstable s hts).1


#print axioms cyc_legal
#print axioms cyc_occursInfinitelyOften
#print axioms cyc_globalFair
#print axioms exists_globallyFairExecution
#print axioms paperTheorem9_3_nonvacuous


end AAFJPK.FairExecutionWitness
