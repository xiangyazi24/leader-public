import Leader.Wu.Seal.SweepProtocol

/-!
# Positive existential landing for the seal-sweep overlay

Weak edge fairness does not force the serialized behavior of the overlay, as
shown by the paired-double-cover obstruction.  This file proves the matching
positive existential result.  From any all-closed configuration with at least
one current leader, choose adjacent closed leader pairs while they exist.  Each
chosen interaction preserves every seal and removes exactly the responder
leader.  The process stops at either one leader or at a separated multi-leader
word, where the accepted clockwise serializer applies.

The resulting schedule reaches Definition-1 safety in at most
`n + leaderCount C - 2` interactions, hence at most `2*n - 2`.  These are
existential scheduler bounds.  No universal weak-fair convergence claim is
made, and no statement is transferred back to the unmodified `P_partial`
transition.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepPositiveLandingSol

open PPLL PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact finite leader count -/

/- `Finset` is not part of this repository's dependency-free Lean core stack.
We therefore use the extensionally equivalent `List.ofFn` sum over every
member of `Fin n`, as the existing physical-rank modules do. -/

private def sealSweepBitsCount {m : Nat} (bits : Fin m → Bool) : Nat :=
  (List.ofFn (fun i => if bits i then 1 else 0)).sum

private theorem sealSweepBitsCount_succ {m : Nat}
    (bits : Fin (m + 1) → Bool) :
    sealSweepBitsCount bits =
      (if bits 0 then 1 else 0) +
        sealSweepBitsCount (fun i : Fin m => bits i.succ) := by
  unfold sealSweepBitsCount
  rw [List.ofFn_succ, List.sum_cons]

private theorem sealSweepBitsCount_eq_zero_iff {m : Nat}
    (bits : Fin m → Bool) :
    sealSweepBitsCount bits = 0 ↔ ∀ i, bits i = false := by
  induction m with
  | zero => simp [sealSweepBitsCount]
  | succ m ih =>
      rw [sealSweepBitsCount_succ]
      constructor
      · intro hcount
        have hzero : bits 0 = false := by
          cases hbit : bits 0 <;> simp_all
        have htailCount :
            sealSweepBitsCount (fun i : Fin m => bits i.succ) = 0 := by
          simp [hzero] at hcount
          omega
        have htail :=
          (ih (fun i : Fin m => bits i.succ)).1 htailCount
        intro i
        cases i using Fin.cases with
        | zero => exact hzero
        | succ i => exact htail i
      · intro hall
        have hzero : bits 0 = false := hall 0
        have htail : ∀ i : Fin m, bits i.succ = false :=
          fun i => hall i.succ
        rw [(ih (fun i : Fin m => bits i.succ)).2 htail]
        simp [hzero]

private theorem sealSweepBitsCount_unique_iff {m : Nat}
    (bits : Fin m → Bool) :
    sealSweepBitsCount bits = 1 ↔
      ∃ root : Fin m,
        bits root = true ∧
          ∀ i : Fin m, bits i = true → i = root := by
  induction m with
  | zero => simp [sealSweepBitsCount]
  | succ m ih =>
      rw [sealSweepBitsCount_succ]
      constructor
      · intro hcount
        cases hzero : bits 0
        · have htailCount :
              sealSweepBitsCount (fun i : Fin m => bits i.succ) = 1 := by
            simpa [hzero] using hcount
          obtain ⟨root, hroot, honly⟩ :=
            (ih (fun i : Fin m => bits i.succ)).1 htailCount
          refine ⟨root.succ, hroot, ?_⟩
          intro i hi
          cases i using Fin.cases with
          | zero => simp [hzero] at hi
          | succ i => exact congrArg Fin.succ (honly i hi)
        · have htailZero :
              sealSweepBitsCount (fun i : Fin m => bits i.succ) = 0 := by
            simp [hzero] at hcount
            omega
          refine ⟨0, hzero, ?_⟩
          intro i hi
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              have htailFalse :=
                (sealSweepBitsCount_eq_zero_iff
                  (fun j : Fin m => bits j.succ)).1 htailZero
              simp [htailFalse i] at hi
      · rintro ⟨root, hroot, honly⟩
        cases root using Fin.cases with
        | zero =>
            have htailFalse : ∀ i : Fin m, bits i.succ = false := by
              intro i
              cases h : bits i.succ
              · rfl
              · exact False.elim
                  (Fin.succ_ne_zero i (honly i.succ h))
            have htailZero :
                sealSweepBitsCount (fun i : Fin m => bits i.succ) = 0 := by
              exact (sealSweepBitsCount_eq_zero_iff
                (fun i : Fin m => bits i.succ)).2 htailFalse
            simp [hroot, htailZero]
        | succ root =>
            have hzero : bits 0 = false := by
              cases h : bits 0
              · rfl
              · exact False.elim
                  (Fin.succ_ne_zero root (honly 0 h).symm)
            have htailUnique :
                ∃ r : Fin m,
                  bits r.succ = true ∧
                    ∀ i : Fin m, bits i.succ = true → i = r := by
              refine ⟨root, hroot, ?_⟩
              intro i hi
              exact Fin.succ_inj.mp (honly i.succ hi)
            have htailCount :
                sealSweepBitsCount (fun i : Fin m => bits i.succ) = 1 :=
              (ih (fun i : Fin m => bits i.succ)).2 htailUnique
            simp [hzero, htailCount]

private theorem sealSweepBitsCount_exists_two {m : Nat}
    (bits : Fin m → Bool)
    (hcount : 2 ≤ sealSweepBitsCount bits) :
    ∃ i j : Fin m,
      i ≠ j ∧ bits i = true ∧ bits j = true := by
  induction m with
  | zero => simp [sealSweepBitsCount] at hcount
  | succ m ih =>
      rw [sealSweepBitsCount_succ] at hcount
      cases hzero : bits 0
      · have htail :
            2 ≤ sealSweepBitsCount (fun i : Fin m => bits i.succ) := by
          simpa [hzero] using hcount
        obtain ⟨i, j, hij, hi, hj⟩ :=
          ih (fun k : Fin m => bits k.succ) htail
        exact ⟨i.succ, j.succ, fun h => hij (Fin.succ_inj.mp h), hi, hj⟩
      · have htailPositive :
            0 < sealSweepBitsCount (fun i : Fin m => bits i.succ) := by
          simp [hzero] at hcount
          omega
        have htailExists : ∃ i : Fin m, bits i.succ = true := by
          apply Classical.byContradiction
          intro hnone
          have hfalse : ∀ i : Fin m, bits i.succ = false := by
            intro i
            cases h : bits i.succ
            · rfl
            · exact False.elim (hnone ⟨i, h⟩)
          have hzeroCount :
              sealSweepBitsCount (fun i : Fin m => bits i.succ) = 0 := by
            exact (sealSweepBitsCount_eq_zero_iff
              (fun i : Fin m => bits i.succ)).2 hfalse
          omega
        obtain ⟨i, hi⟩ := htailExists
        exact ⟨0, i.succ,
          fun h => Fin.succ_ne_zero i h.symm, hzero, hi⟩

private theorem sealSweepBitsCount_single_drop {m : Nat}
    (before after : Fin m → Bool) (victim : Fin m)
    (hbefore : before victim = true)
    (hafter : after victim = false)
    (hother : ∀ i : Fin m, i ≠ victim → after i = before i) :
    sealSweepBitsCount after + 1 = sealSweepBitsCount before := by
  induction m with
  | zero => exact Fin.elim0 victim
  | succ m ih =>
      rw [sealSweepBitsCount_succ, sealSweepBitsCount_succ]
      cases victim using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin m => after i.succ) =
                fun i : Fin m => before i.succ := by
            funext i
            exact hother i.succ (Fin.succ_ne_zero i)
          rw [hbefore, hafter, htail]
          simp only [Bool.false_eq_true, eq_self, if_false, if_true,
            Nat.zero_add]
          change
            sealSweepBitsCount (fun i : Fin m => before i.succ) + 1 =
              1 + sealSweepBitsCount (fun i : Fin m => before i.succ)
          omega
      | succ victim =>
          have hhead : after 0 = before 0 :=
            hother 0 (fun h => Fin.succ_ne_zero victim h.symm)
          have htail := ih
            (fun i : Fin m => before i.succ)
            (fun i : Fin m => after i.succ)
            victim hbefore hafter
            (fun i hi => hother i.succ (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

/-- Exact current leader count. -/
def sealSweepLeaderCount
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  (List.ofFn
    (fun i : Fin n => if sweepLockLeader (C i) then 1 else 0)).sum

private theorem sealSweepLeaderCount_eq_bitsCount
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepLeaderCount C =
      sealSweepBitsCount (fun i => sweepLockLeader (C i)) := by
  rfl

theorem sealSweepLeaderCount_le
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepLeaderCount C ≤ n := by
  induction n with
  | zero => simp [sealSweepLeaderCount]
  | succ n ih =>
      rw [sealSweepLeaderCount, List.ofFn_succ, List.sum_cons]
      have htail := ih (C := fun i : Fin n => C i.succ)
      unfold sealSweepLeaderCount at htail
      have htail' :
          (List.ofFn (fun i : Fin n =>
            if sweepLockLeader (C i.succ) then 1 else 0)).sum ≤ n := by
        simpa using htail
      split <;> omega

@[simp] theorem sealSweep_isLeaderOutput_iff
    (u : SealSweepState psi kappa tau) :
    isLeaderOutput ((P_partialSealSweepProtocol psi kappa tau).output u) =
        true ↔
      sweepLockLeader u = true := by
  cases h : sweepLockLeader u <;>
    simp [P_partialSealSweepProtocol, h, isLeaderOutput]

/-- Count one is exactly the repository's current unique-output predicate. -/
theorem sealSweep_unique_iff_leaderCount_eq_one
    (C : SealSweepConfig n psi kappa tau) :
    UniqueLeaderOutput
        (P_partialSealSweepProtocol psi kappa tau) n C isLeaderOutput ↔
      sealSweepLeaderCount C = 1 := by
  constructor
  · rintro ⟨root, hroot, honly⟩
    rw [sealSweepLeaderCount_eq_bitsCount]
    apply (sealSweepBitsCount_unique_iff
      (fun i => sweepLockLeader (C i))).2
    refine ⟨root, (sealSweep_isLeaderOutput_iff (C root)).1 hroot, ?_⟩
    intro i hi
    apply honly i
    exact (sealSweep_isLeaderOutput_iff (C i)).2 hi
  · intro hcount
    rw [sealSweepLeaderCount_eq_bitsCount] at hcount
    obtain ⟨root, hroot, honly⟩ :=
      (sealSweepBitsCount_unique_iff
        (fun i => sweepLockLeader (C i))).1 hcount
    refine ⟨root, ?_, ?_⟩
    · exact (sealSweep_isLeaderOutput_iff (C root)).2 hroot
    · intro i hi
      exact honly i ((sealSweep_isLeaderOutput_iff (C i)).1 hi)

/-- At least two counted sites give two distinct leader outputs. -/
theorem sealSweep_hasTwo_of_two_le_leaderCount
    (C : SealSweepConfig n psi kappa tau)
    (hcount : 2 ≤ sealSweepLeaderCount C) :
    HasTwoLeaderOutputs
      (P_partialSealSweepProtocol psi kappa tau) isLeaderOutput C := by
  rw [sealSweepLeaderCount_eq_bitsCount] at hcount
  obtain ⟨i, j, hij, hi, hj⟩ :=
    sealSweepBitsCount_exists_two
      (fun k => sweepLockLeader (C k)) hcount
  refine ⟨i, j, hij, ?_, ?_⟩
  · exact (sealSweep_isLeaderOutput_iff (C i)).2 hi
  · exact (sealSweep_isLeaderOutput_iff (C j)).2 hj

/-! ## One exact adjacent closed-leader collision -/

def SealSweepAdjacentLeaders
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) : Prop :=
  sweepLockLeader (C e) = true ∧
    sweepLockLeader (C (ring.rightNeighbor e)) = true

/-- A selected adjacent closed-leader interaction preserves all seals and
removes exactly the responder from the finite leader set. -/
theorem sealSweep_adjacentCollision_step
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (e : Fin n) (hadj : SealSweepAdjacentLeaders ring C e) :
    let D := localStep ring P_partialSealSweep C e
    SealSweepAllClosed D ∧
      sealSweepLeaderCount D + 1 = sealSweepLeaderCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair : P_partialSealSweep (C e) (C j) =
      (((C e).1, true), (clearMinimalLockLeader (C j).1, true)) :=
    P_partialSealSweep_twoClosedLeaders
      (C e) (C j) hadj.1 (hclosed e)
        (by simpa [j] using hadj.2) (hclosed j)
  let D := localStep ring P_partialSealSweep C e
  have hDe : D e = ((C e).1, true) := by
    simp [D, localStep, j, hpair]
  have hDj : D j = (clearMinimalLockLeader (C j).1, true) := by
    simp [D, localStep, j, hpair, hje]
  have hDother : ∀ i : Fin n, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, localStep, j, hpair, hie, hij]
  have hDeq : D e = C e := by
    exact hDe.trans (Prod.ext rfl (hclosed e).symm)
  have hDclosed : SealSweepAllClosed D := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDe]
    · by_cases hij : i = j
      · subst i
        rw [hDj]
      · rw [hDother i hie hij]
        exact hclosed i
  have hjBefore : sweepLockLeader (C j) = true := by
    simpa [j] using hadj.2
  have hjAfter : sweepLockLeader (D j) = false := by
    rw [hDj]
    exact clearMinimalLockLeader_leader (C j).1
  have hleaderOther : ∀ i : Fin n, i ≠ j →
      sweepLockLeader (D i) = sweepLockLeader (C i) := by
    intro i hij
    by_cases hie : i = e
    · subst i
      rw [hDeq]
    · rw [hDother i hie hij]
  constructor
  · exact hDclosed
  · rw [sealSweepLeaderCount_eq_bitsCount,
      sealSweepLeaderCount_eq_bitsCount]
    exact sealSweepBitsCount_single_drop
      (fun i => sweepLockLeader (C i))
      (fun i => sweepLockLeader (D i))
      j hjBefore hjAfter hleaderOther

/-! ## Repeated collision normalization -/

/-- Repeated actual overlay interactions reach either a unique leader or a
separated positive multi-leader state.  The accounting identity says that
every prefix interaction removed exactly one leader. -/
theorem sealSweep_collisionNormalization
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hpositive : 0 < sealSweepLeaderCount C) :
    ∃ pre : DetSchedule n,
      let D := runLocalSchedule ring P_partialSealSweep C pre
      SealSweepAllClosed D ∧
        0 < sealSweepLeaderCount D ∧
        sealSweepLeaderCount D + pre.length = sealSweepLeaderCount C ∧
        (UniqueLeaderOutput
            (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput ∨
          (2 ≤ sealSweepLeaderCount D ∧
            SweepResetNoAdjacentLeaders ring D)) := by
  classical
  have hnormalize : ∀ k : Nat,
      ∀ X : SealSweepConfig n psi kappa tau,
        sealSweepLeaderCount X = k →
        SealSweepAllClosed X →
        0 < sealSweepLeaderCount X →
        ∃ pre : DetSchedule n,
          let D := runLocalSchedule ring P_partialSealSweep X pre
          SealSweepAllClosed D ∧
            0 < sealSweepLeaderCount D ∧
            sealSweepLeaderCount D + pre.length =
              sealSweepLeaderCount X ∧
            (UniqueLeaderOutput
                (P_partialSealSweepProtocol psi kappa tau)
                n D isLeaderOutput ∨
              (2 ≤ sealSweepLeaderCount D ∧
                SweepResetNoAdjacentLeaders ring D)) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro X hXcount hXclosed hXpositive
        by_cases hunique : UniqueLeaderOutput
            (P_partialSealSweepProtocol psi kappa tau) n X isLeaderOutput
        · refine ⟨[], ?_, ?_, ?_, Or.inl ?_⟩
          · exact hXclosed
          · exact hXpositive
          · simp [runLocalSchedule]
          · exact hunique
        by_cases hnoAdjacent : SweepResetNoAdjacentLeaders ring X
        · have hneOne : sealSweepLeaderCount X ≠ 1 := by
            intro hone
            exact hunique
              ((sealSweep_unique_iff_leaderCount_eq_one X).2 hone)
          have htwo : 2 ≤ sealSweepLeaderCount X := by omega
          refine ⟨[], ?_, ?_, ?_, Or.inr ⟨htwo, ?_⟩⟩
          · exact hXclosed
          · exact hXpositive
          · simp [runLocalSchedule]
          · exact hnoAdjacent
        · have hadjExists : ∃ e : Fin n,
              SealSweepAdjacentLeaders ring X e := by
            apply Classical.byContradiction
            intro hnone
            apply hnoAdjacent
            intro e he
            apply hnone
            exact ⟨e, he⟩
          obtain ⟨e, hadj⟩ := hadjExists
          have hneOne : sealSweepLeaderCount X ≠ 1 := by
            intro hone
            exact hunique
              ((sealSweep_unique_iff_leaderCount_eq_one X).2 hone)
          have htwo : 2 ≤ sealSweepLeaderCount X := by omega
          have hn : 1 < n := by
            have hle := sealSweepLeaderCount_le X
            omega
          let Y := localStep ring P_partialSealSweep X e
          have hstep := sealSweep_adjacentCollision_step
            ring hn X hXclosed e hadj
          change SealSweepAllClosed Y ∧
            sealSweepLeaderCount Y + 1 = sealSweepLeaderCount X at hstep
          have hYpositive : 0 < sealSweepLeaderCount Y := by omega
          have hYlt : sealSweepLeaderCount Y < k := by omega
          obtain ⟨tail, htailClosed, htailPositive,
              htailCount, htailTerminal⟩ :=
            ih (sealSweepLeaderCount Y) hYlt Y rfl hstep.1 hYpositive
          refine ⟨e :: tail, ?_, ?_, ?_, ?_⟩
          · exact htailClosed
          · exact htailPositive
          · change
              sealSweepLeaderCount
                  (runLocalSchedule ring P_partialSealSweep Y tail) +
                  (tail.length + 1) =
                sealSweepLeaderCount X
            omega
          · exact htailTerminal
  exact hnormalize (sealSweepLeaderCount C) C rfl hclosed hpositive

/-! ## Landing at semantic safety -/

/-- State-dependent positive landing bound. -/
theorem sealSweep_allClosedPositive_reaches_isSafe_stateBound
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hpositive : 0 < sealSweepLeaderCount C) :
    ∃ word : DetSchedule n,
      word.length ≤ n + sealSweepLeaderCount C - 2 ∧
      PopulationProtocol.Reachable
        (P_partialSealSweepProtocol psi kappa tau) ring C
        (runLocalSchedule ring P_partialSealSweep C word) ∧
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealSweep C word)
        isLeaderOutput := by
  obtain ⟨pre, hDclosed, hDpositive, hcount, hterminal⟩ :=
    sealSweep_collisionNormalization ring C hclosed hpositive
  let D := runLocalSchedule ring P_partialSealSweep C pre
  change SealSweepAllClosed D at hDclosed
  change 0 < sealSweepLeaderCount D at hDpositive
  change sealSweepLeaderCount D + pre.length =
    sealSweepLeaderCount C at hcount
  change UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput ∨
    (2 ≤ sealSweepLeaderCount D ∧
      SweepResetNoAdjacentLeaders ring D) at hterminal
  rcases hterminal with hDunique | ⟨hDtwo, hDnoAdjacent⟩
  · refine ⟨pre, ?_,
      P_partialSealSweep_runLocalSchedule_reachable ring C pre, ?_⟩
    · have hDone : sealSweepLeaderCount D = 1 :=
        (sealSweep_unique_iff_leaderCount_eq_one D).1 hDunique
      have hle := sealSweepLeaderCount_le C
      omega
    · exact allClosedUnique_isSafe ring D hDclosed hDunique
  · have hDhasTwo : HasTwoLeaderOutputs
        (P_partialSealSweepProtocol psi kappa tau) isLeaderOutput D :=
      sealSweep_hasTwo_of_two_le_leaderCount D hDtwo
    have hDstart : SealSweepSeparatedStart ring D :=
      ⟨hDclosed, hDnoAdjacent, hDhasTwo⟩
    obtain ⟨seed, htailLength, htailReach,
        hEclosed, hEunique⟩ :=
      separatedStart_serialized_escape ring D hDstart
    let tail := clockwiseEdgeSchedule ring seed n
    have hEsafe : PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealSweep D tail)
        isLeaderOutput :=
      allClosedUnique_isSafe ring _ hEclosed hEunique
    refine ⟨pre ++ tail, ?_,
      P_partialSealSweep_runLocalSchedule_reachable ring C (pre ++ tail), ?_⟩
    · simp only [List.length_append]
      change tail.length = n at htailLength
      omega
    · have hrun :
          runLocalSchedule ring P_partialSealSweep C (pre ++ tail) =
            runLocalSchedule ring P_partialSealSweep D tail := by
          rw [PPLLSchedulerBlocks.runLocalSchedule_append]
      have hsafeEq := congrArg
        (fun X : SealSweepConfig n psi kappa tau =>
          PopulationProtocol.IsSafe
            (P_partialSealSweepProtocol psi kappa tau) ring X
            isLeaderOutput)
        hrun
      exact Eq.mpr hsafeEq hEsafe

/-- Uniform consequence: the exact count is at most the number of sites. -/
theorem sealSweep_allClosedPositive_reaches_isSafe_two_mul_sub_two
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hpositive : 0 < sealSweepLeaderCount C) :
    ∃ word : DetSchedule n,
      word.length ≤ 2 * n - 2 ∧
      PopulationProtocol.Reachable
        (P_partialSealSweepProtocol psi kappa tau) ring C
        (runLocalSchedule ring P_partialSealSweep C word) ∧
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealSweep C word)
        isLeaderOutput := by
  obtain ⟨word, hlength, hreach, hsafe⟩ :=
    sealSweep_allClosedPositive_reaches_isSafe_stateBound
      ring C hclosed hpositive
  refine ⟨word, ?_, hreach, hsafe⟩
  have hle := sealSweepLeaderCount_le C
  omega

end PPartialSealSweepPositiveLandingSol
end PPLLCompleteMultiLeaderCleanup
