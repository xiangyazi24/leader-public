import Leader.Wu.PartialProtocol.RawLiftBoolResetNoGo
import Leader.Wu.Seal.BirthBarrierShortBlocks

/-!
# A table-breaking factor-sixteen reset on the R97 full shift

This module gives a positive counterpart to R100 on its narrowest source
class.  The carrier is R94's factor-eight state together with one outer reset
bit.  Whenever either physical endpoint belongs to R97's raw follower
alphabet, both endpoints are overwritten by one authorized R94 zero-start
state whose physical payload lies outside that alphabet.  Otherwise the rule
executes the exact R94 transition and clears both outer reset bits.

A clockwise word of at most `n` interactions overwrites every site of an R97
full shift, regardless of all forged lock, seal, birth, and outer reset bits.
The chosen payload is invariant under R94 except for its leader field, so it
never re-enters the raw alphabet.  On the resulting closed payload-restricted
restart domain, erasure therefore simulates R94 for every subsequent word.

This is not an arbitrary-carrier repair.  States outside the raw alphabet and
outside the payload-restricted R94 domain receive no entry theorem here.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialFactorSixteenResetEntrySol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPLLClosedDomainSchedulerAmplificationSol
open PPLLExpiringComparisonRepair
open PPartialMinimalLockRepairSol PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol PPartialSealSweepIidBirthRepairSol
open PPartialSealSweepIidBirthComplexitySol
open PPartialRawLiftBoolResetNoGoSol

set_option autoImplicit false

variable {n : Nat}

/-! ## Executable reset rule -/

/-- Propositional equality presentation of R97's four-state alphabet. -/
def RawZeroAlphabetEq (u : RawZeroAlphabetState) : Prop :=
  u = rawZeroClosedN ∨ u = rawZeroClosedR ∨
    u = rawZeroClosedH ∨ u = rawZeroClosedRH

instance rawZeroAlphabetEqDecidable (u : RawZeroAlphabetState) :
    Decidable (RawZeroAlphabetEq u) := by
  unfold RawZeroAlphabetEq
  infer_instance

theorem rawZeroAlphabetEq_iff (u : RawZeroAlphabetState) :
    RawZeroAlphabetEq u ↔ InRawZeroAlphabet u := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact .ofN
    · exact .ofR
    · exact .ofH
    · exact .ofRH
  · intro hu
    cases hu with
    | ofN => exact Or.inl rfl
    | ofR => exact Or.inr (Or.inl rfl)
    | ofH => exact Or.inr (Or.inr (Or.inl rfl))
    | ofRH => exact Or.inr (Or.inr (Or.inr rfl))

/-- The physical reset payload.  Its nonempty comparison-path field makes it
definitionally distinct from all four R97 states. -/
def factorSixteenResetMinimal : MinimalLockState 1 0 0 :=
  (rawZeroHomogeneousDeletionState, false)

/-- One authorized R94 all-armed, all-closed follower state. -/
def factorSixteenResetInner : IidBirthState 1 0 0 :=
  ((clearMinimalLockLeader factorSixteenResetMinimal, true), true)

/-- The outer bit is cleared at the reset target. -/
def factorSixteenResetKernel : FactorSixteenState :=
  (factorSixteenResetInner, false)

@[simp] theorem factorSixteenResetKernel_raw :
    factorSixteenRaw factorSixteenResetKernel =
      rawZeroHomogeneousDeletionState := by
  rfl

theorem rawZeroHomogeneousDeletion_not_in_alphabet :
    ¬ InRawZeroAlphabet rawZeroHomogeneousDeletionState := by
  intro h
  cases h <;> decide

theorem factorSixteenResetKernel_not_raw :
    ¬ InRawZeroAlphabet (factorSixteenRaw factorSixteenResetKernel) := by
  simpa using rawZeroHomogeneousDeletion_not_in_alphabet

/-- Reset on every pair touching the R97 alphabet; otherwise run the exact
R94 transition and normalize the outer bits to `false`. -/
def P_partialFactorSixteenReset
    (l r : FactorSixteenState) :
    FactorSixteenState × FactorSixteenState :=
  if RawZeroAlphabetEq (factorSixteenRaw l) ∨
      RawZeroAlphabetEq (factorSixteenRaw r) then
    (factorSixteenResetKernel, factorSixteenResetKernel)
  else
    let q := P_partialSealIidBirth l.1 r.1
    ((q.1, false), (q.2, false))

/-- The reset bit remains observationally silent. -/
def P_partialFactorSixteenResetProtocol : PopulationProtocol where
  Q := FactorSixteenState
  Y := LeaderOutput
  transition := P_partialFactorSixteenReset
  output := fun s =>
    if sweepLockLeader s.1.1 then .leader else .follower

theorem P_partialFactorSixteenReset_of_left_raw
    (l r : FactorSixteenState)
    (hl : InRawZeroAlphabet (factorSixteenRaw l)) :
    P_partialFactorSixteenReset l r =
      (factorSixteenResetKernel, factorSixteenResetKernel) := by
  simp [P_partialFactorSixteenReset,
    (rawZeroAlphabetEq_iff _).2 hl]

theorem P_partialFactorSixteenReset_of_right_raw
    (l r : FactorSixteenState)
    (hr : InRawZeroAlphabet (factorSixteenRaw r)) :
    P_partialFactorSixteenReset l r =
      (factorSixteenResetKernel, factorSixteenResetKernel) := by
  simp [P_partialFactorSixteenReset,
    (rawZeroAlphabetEq_iff _).2 hr]

/-- Every forged uniform control slice changes every raw/raw table entry and
both physical outputs leave the raw alphabet. -/
theorem factorSixteenReset_breaks_every_raw_pair_on_every_control
    (l r : RawZeroAlphabetState)
    (hl : InRawZeroAlphabet l) (hr : InRawZeroAlphabet r)
    (leftControl rightControl : FactorSixteenControl) :
    P_partialFactorSixteenReset
        (factorSixteenEmbed l leftControl)
        (factorSixteenEmbed r rightControl) =
      (factorSixteenResetKernel, factorSixteenResetKernel) ∧
    ¬ InRawZeroAlphabet (factorSixteenRaw factorSixteenResetKernel) := by
  constructor
  · exact P_partialFactorSixteenReset_of_left_raw _ _ (by simpa using hl)
  · exact factorSixteenResetKernel_not_raw

/-! ## The payload invariant needed for exact post-entry simulation -/

/-- Erase the seal and birth bits and clear only the leader field.  R94 keeps
this endpoint-local payload invariant. -/
def iidBirthResetPayload (u : IidBirthState 1 0 0) :
    MinimalLockState 1 0 0 :=
  clearMinimalLockLeader u.1.1

@[simp] theorem clearMinimalLockLeader_idem
    (u : MinimalLockState 1 0 0) :
    clearMinimalLockLeader (clearMinimalLockLeader u) =
      clearMinimalLockLeader u := by
  rcases u with ⟨u, lockBit⟩
  rfl

@[simp] theorem clearMinimalLockLeader_setIidBirthLeader
    (u : MinimalLockState 1 0 0) :
    clearMinimalLockLeader (setIidBirthLeader u) =
      clearMinimalLockLeader u := by
  rcases u with ⟨u, lockBit⟩
  rfl

/-- R91's seal transition preserves each endpoint's leader-cleared payload. -/
theorem sealSweep_resetPayload
    (l r : SealSweepState 1 0 0) :
    let q := P_partialSealSweep l r
    clearMinimalLockLeader q.1.1 = clearMinimalLockLeader l.1 ∧
      clearMinimalLockLeader q.2.1 = clearMinimalLockLeader r.1 := by
  rcases l with ⟨l, leftSeal⟩
  rcases r with ⟨r, rightSeal⟩
  cases leftSeal <;> cases rightSeal <;>
    cases hl : minimalLockLeader l <;>
    cases hr : minimalLockLeader r <;>
    simp [P_partialSealSweep, sweepLockLeader, hl, hr]

/-- The complete R94 transition preserves the same endpoint-local payload. -/
theorem iidBirth_resetPayload
    (l r : IidBirthState 1 0 0) :
    let q := P_partialSealIidBirth l r
    iidBirthResetPayload q.1 = iidBirthResetPayload l ∧
      iidBirthResetPayload q.2 = iidBirthResetPayload r := by
  unfold P_partialSealIidBirth
  split
  · split
    · exact sealSweep_resetPayload l.1 r.1
    · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨clearMinimalLockLeader_setIidBirthLeader l.1.1, rfl⟩
      · exact ⟨rfl, rfl⟩

private theorem rawZeroAlphabet_minimal_ne_reset
    (physical : RawZeroAlphabetState)
    (hraw : InRawZeroAlphabet physical) (lockBit : Bool) :
    clearMinimalLockLeader (physical, lockBit) ≠
      factorSixteenResetMinimal := by
  cases hraw <;> cases lockBit <;> decide

/-- The reset payload cannot have one of the four raw physical projections. -/
theorem iidBirthResetPayload_not_raw
    (u : IidBirthState 1 0 0)
    (hu : iidBirthResetPayload u = factorSixteenResetMinimal) :
    ¬ InRawZeroAlphabet u.1.1.1 := by
  rcases u with ⟨⟨⟨physical, lockBit⟩, sealBit⟩, birthBit⟩
  change clearMinimalLockLeader (physical, lockBit) =
    factorSixteenResetMinimal at hu
  intro hraw
  exact rawZeroAlphabet_minimal_ne_reset physical hraw lockBit hu

/-- Away from the raw alphabet the new rule is definitionally the lifted R94
transition, independently of the forged outer bits. -/
theorem P_partialFactorSixteenReset_of_payload
    (l r : FactorSixteenState)
    (hl : iidBirthResetPayload l.1 = factorSixteenResetMinimal)
    (hr : iidBirthResetPayload r.1 = factorSixteenResetMinimal) :
    P_partialFactorSixteenReset l r =
      let q := P_partialSealIidBirth l.1 r.1
      ((q.1, false), (q.2, false)) := by
  have hlRaw : ¬ RawZeroAlphabetEq (factorSixteenRaw l) := by
    intro h
    exact iidBirthResetPayload_not_raw l.1 hl
      ((rawZeroAlphabetEq_iff _).1 h)
  have hrRaw : ¬ RawZeroAlphabetEq (factorSixteenRaw r) := by
    intro h
    exact iidBirthResetPayload_not_raw r.1 hr
      ((rawZeroAlphabetEq_iff _).1 h)
  simp [P_partialFactorSixteenReset, hlRaw, hrRaw]

/-- Erase only the prospective reset bit. -/
def factorSixteenResetErase (C : FactorSixteenConfig n) :
    IidBirthConfig n 1 0 0 :=
  fun i => (C i).1

/-- The closed post-reset state class: R94's restart domain, all outer bits
cleared, and the concrete reset payload retained at every endpoint. -/
def FactorSixteenResetReady (C : FactorSixteenConfig n) : Prop :=
  IidBirthDomain (factorSixteenResetErase C) ∧
    (∀ i : Fin n, (C i).2 = false) ∧
    ∀ i : Fin n, iidBirthResetPayload (C i).1 =
      factorSixteenResetMinimal

/-- On the ready domain, erasure commutes with one local step. -/
theorem factorSixteenResetErase_localStep_ready
    (ring : DirectedRing n) (C : FactorSixteenConfig n)
    (hC : FactorSixteenResetReady C) (e : Fin n) :
    factorSixteenResetErase
        (localStep ring P_partialFactorSixteenReset C e) =
      localStep ring P_partialSealIidBirth
        (factorSixteenResetErase C) e := by
  let j := ring.rightNeighbor e
  let q := P_partialSealIidBirth (C e).1 (C j).1
  have hpair : P_partialFactorSixteenReset (C e) (C j) =
      ((q.1, false), (q.2, false)) := by
    simpa [q] using P_partialFactorSixteenReset_of_payload
      (C e) (C j) (hC.2.2 e) (hC.2.2 j)
  funext i
  by_cases hie : i = e
  · subst i
    simp [factorSixteenResetErase, localStep, j, hpair, q]
  · by_cases hij : i = j
    · subst i
      simp [factorSixteenResetErase, localStep, j, hie, hpair, q]
    · simp [factorSixteenResetErase, localStep, j, hie, hij, hpair, q]

/-- The payload-restricted R94 restart domain is closed under the new rule. -/
theorem factorSixteenResetReady_localStep
    (ring : DirectedRing n) (C : FactorSixteenConfig n)
    (hC : FactorSixteenResetReady C) (e : Fin n) :
    FactorSixteenResetReady
      (localStep ring P_partialFactorSixteenReset C e) := by
  let j := ring.rightNeighbor e
  let q := P_partialSealIidBirth (C e).1 (C j).1
  let D := localStep ring P_partialFactorSixteenReset C e
  have hpair : P_partialFactorSixteenReset (C e) (C j) =
      ((q.1, false), (q.2, false)) := by
    simpa [q] using P_partialFactorSixteenReset_of_payload
      (C e) (C j) (hC.2.2 e) (hC.2.2 j)
  have hpayload := iidBirth_resetPayload (C e).1 (C j).1
  change iidBirthResetPayload q.1 = iidBirthResetPayload (C e).1 ∧
    iidBirthResetPayload q.2 = iidBirthResetPayload (C j).1 at hpayload
  refine ⟨?_, ?_, ?_⟩
  · rw [factorSixteenResetErase_localStep_ready ring C hC e]
    exact iidBirthDomain_localStepClosed ring
      (factorSixteenResetErase C) hC.1 e
  · intro i
    by_cases hie : i = e
    · subst i
      simp [D, localStep, j, hpair]
    · by_cases hij : i = j
      · subst i
        simp [D, localStep, j, hie, hpair]
      · simpa [D, localStep, j, hie, hij] using hC.2.1 i
  · intro i
    by_cases hie : i = e
    · subst i
      simp only [D, localStep, if_pos, j, hpair, Prod.fst]
      exact hpayload.1.trans (hC.2.2 e)
    · by_cases hij : i = j
      · subst i
        simp only [D, localStep, j, if_neg hie, if_pos, hpair, Prod.snd]
        exact hpayload.2.trans (hC.2.2 j)
      · simpa [D, localStep, j, hie, hij] using hC.2.2 i

/-- Ready executions stay ready and erase to the exact R94 execution for every
finite scheduler word. -/
theorem factorSixteenResetReady_run_simulation
    (ring : DirectedRing n) (C : FactorSixteenConfig n)
    (hC : FactorSixteenResetReady C) (word : DetSchedule n) :
    let D := runLocalSchedule ring P_partialFactorSixteenReset C word
    FactorSixteenResetReady D ∧
      factorSixteenResetErase D =
        runLocalSchedule ring P_partialSealIidBirth
          (factorSixteenResetErase C) word := by
  induction word generalizing C with
  | nil => exact ⟨hC, rfl⟩
  | cons e rest ih =>
      simp only [runLocalSchedule]
      let C₁ := localStep ring P_partialFactorSixteenReset C e
      have hC₁ : FactorSixteenResetReady C₁ :=
        factorSixteenResetReady_localStep ring C hC e
      obtain ⟨hD, herase⟩ := ih C₁ hC₁
      refine ⟨hD, ?_⟩
      rw [herase]
      exact congrArg
        (fun X => runLocalSchedule ring P_partialSealIidBirth X rest)
        (factorSixteenResetErase_localStep_ready ring C hC e)

/-! ## Uniform entry from the R97 full shift -/

/-- Every physical projection belongs to R97's four-state raw alphabet.  All
four inner control bits and the new outer bit remain completely arbitrary. -/
def FactorSixteenRawFullShift (C : FactorSixteenConfig n) : Prop :=
  ∀ i : Fin n, InRawZeroAlphabet (factorSixteenRaw (C i))

/-- The prefix invariant for the clockwise overwrite word: the visited
segment is the reset kernel, and every still-unvisited clockwise offset is
still raw. -/
def FactorSixteenRawSweepPrefix
    (ring : DirectedRing n) (root : Fin n) (steps : Nat)
    (C : FactorSixteenConfig n) : Prop :=
  (∀ k : Nat, 0 < steps → k ≤ steps →
      C (cwPos ring root k) = factorSixteenResetKernel) ∧
    ∀ k : Nat, steps < k → k < n →
      InRawZeroAlphabet (factorSixteenRaw (C (cwPos ring root k)))

private theorem cwPos_ne_of_ne_below_factorSixteenReset
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

/-- The first `steps` clockwise edges overwrite precisely a growing prefix.
The responder of each edge is still raw, so forged control bits never affect
the overwrite. -/
theorem factorSixteenRawFullShift_clockwise_prefix
    (ring : DirectedRing n) (C : FactorSixteenConfig n)
    (hC : FactorSixteenRawFullShift C) (root : Fin n)
    (steps : Nat) (hlt : steps < n) :
    FactorSixteenRawSweepPrefix ring root steps
      (runLocalSchedule ring P_partialFactorSixteenReset C
        (clockwiseEdgeSchedule ring root steps)) := by
  induction steps with
  | zero =>
      constructor
      · intro k hpos
        omega
      · intro k _hk _hkn
        simpa [clockwiseEdgeSchedule, runLocalSchedule] using
          hC (cwPos ring root k)
  | succ s ih =>
      let D := runLocalSchedule ring P_partialFactorSixteenReset C
        (clockwiseEdgeSchedule ring root s)
      let e := cwPos ring root s
      let j := ring.rightNeighbor e
      let E := localStep ring P_partialFactorSixteenReset D e
      have hslt : s < n := by omega
      have hprev := ih hslt
      change FactorSixteenRawSweepPrefix ring root s D at hprev
      have hjpos : j = cwPos ring root (s + 1) := by
        simpa [j, e, Nat.add_assoc] using
          (cwPos_succ ring root s).symm
      have hjraw : InRawZeroAlphabet (factorSixteenRaw (D j)) := by
        rw [hjpos]
        exact hprev.2 (s + 1) (by omega) hlt
      have hpair : P_partialFactorSixteenReset (D e) (D j) =
          (factorSixteenResetKernel, factorSixteenResetKernel) :=
        P_partialFactorSixteenReset_of_right_raw _ _ hjraw
      have hnTwo : 1 < n := by omega
      have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hnTwo e
      have hEe : E e = factorSixteenResetKernel := by
        simp [E, localStep, j, hpair]
      have hEj : E j = factorSixteenResetKernel := by
        simp [E, localStep, j, hje, hpair]
      have hunchanged (i : Fin n) (hie : i ≠ e) (hij : i ≠ j) :
          E i = D i := by
        simp [E, localStep, j, hie, hij]
      have hrun :
          runLocalSchedule ring P_partialFactorSixteenReset C
              (clockwiseEdgeSchedule ring root (s + 1)) = E := by
        change runLocalSchedule ring P_partialFactorSixteenReset C
            (clockwiseEdgeSchedule ring root s ++ [e]) = E
        rw [PPLLSchedulerBlocks.runLocalSchedule_append]
        rfl
      rw [hrun]
      constructor
      · intro k _hpos hk
        by_cases hknew : k = s + 1
        · subst k
          rw [← hjpos]
          exact hEj
        · have hkprev : k ≤ s := by omega
          by_cases hkcurrent : k = s
          · subst k
            simpa [e] using hEe
          · have hklt : k < n := by omega
            have hke : cwPos ring root k ≠ e := by
              simpa [e] using
                cwPos_ne_of_ne_below_factorSixteenReset
                  ring root hklt hslt hkcurrent
            have hkj : cwPos ring root k ≠ j := by
              rw [hjpos]
              exact cwPos_ne_of_ne_below_factorSixteenReset
                ring root hklt hlt hknew
            rw [hunchanged (cwPos ring root k) hke hkj]
            exact hprev.1 k (by omega) hkprev
      · intro k hk hkn
        have hke : cwPos ring root k ≠ e := by
          simpa [e] using
            cwPos_ne_of_ne_below_factorSixteenReset
              ring root hkn hslt (by omega)
        have hkj : cwPos ring root k ≠ j := by
          rw [hjpos]
          exact cwPos_ne_of_ne_below_factorSixteenReset
            ring root hkn hlt (by omega)
        rw [hunchanged (cwPos ring root k) hke hkj]
        exact hprev.2 k (by omega) hkn

/-- On a nontrivial ring, the length-`n-1` clockwise word overwrites the
entire forged R97 full shift by the one reset kernel. -/
theorem factorSixteenRawFullShift_reaches_allKernel_of_one_lt
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FactorSixteenConfig n) (hC : FactorSixteenRawFullShift C) :
    ∃ word : DetSchedule n,
      word.length = n - 1 ∧
      runLocalSchedule ring P_partialFactorSixteenReset C word =
        (fun _ => factorSixteenResetKernel) := by
  let root : Fin n := ⟨0, ring.hn⟩
  let word := clockwiseEdgeSchedule ring root (n - 1)
  let D := runLocalSchedule ring P_partialFactorSixteenReset C word
  have hprefix := factorSixteenRawFullShift_clockwise_prefix
    ring C hC root (n - 1) (by omega)
  change FactorSixteenRawSweepPrefix ring root (n - 1) D at hprefix
  have hall : D = (fun _ => factorSixteenResetKernel) := by
    funext i
    let k := cwDist ring root i
    have hklt : k < n := cwDist_lt ring root i
    have hki : cwPos ring root k = i := cwPos_cwDist ring root i
    have hkBound : k ≤ n - 1 := by omega
    rw [← hki]
    exact hprefix.1 k (by omega) hkBound
  exact ⟨word, clockwiseEdgeSchedule_length ring root (n - 1), hall⟩

/-- The one-agent self-edge also overwrites its unique raw state. -/
theorem factorSixteenRawFullShift_reaches_allKernel_of_eq_one
    (ring : DirectedRing n) (hn : n = 1)
    (C : FactorSixteenConfig n) (hC : FactorSixteenRawFullShift C) :
    ∃ word : DetSchedule n,
      word.length = 1 ∧
      runLocalSchedule ring P_partialFactorSixteenReset C word =
        (fun _ => factorSixteenResetKernel) := by
  let root : Fin n := ⟨0, ring.hn⟩
  refine ⟨[root], rfl, ?_⟩
  simp only [runLocalSchedule, List.nil_eq]
  funext i
  have hir : i = root := by
    apply Fin.ext
    omega
  subst i
  have hjr : ring.rightNeighbor root = root := by
    apply Fin.ext
    omega
  have hpair := P_partialFactorSixteenReset_of_left_raw
    (C root) (C (ring.rightNeighbor root)) (hC root)
  rw [hjr] at hpair
  simp [localStep, hjr, hpair]

/-- The reset kernel is exactly R94's authorized uniform zero start after
outer-bit erasure. -/
theorem factorSixteenResetKernel_ready
    (ring : DirectedRing n) :
    FactorSixteenResetReady
      (n := n) (fun _ => factorSixteenResetKernel) := by
  refine ⟨?_, ?_, ?_⟩
  · exact iidBirthUniformZeroStart_domain factorSixteenResetMinimal
  · intro i
    rfl
  · intro i
    exact clearMinimalLockLeader_idem factorSixteenResetMinimal

/-- Uniform bounded entry promised for R97: every forged full shift reaches
the closed R94-simulating restart domain in at most `n` interactions. -/
theorem factorSixteenRawFullShift_reaches_resetReady
    (ring : DirectedRing n) (C : FactorSixteenConfig n)
    (hC : FactorSixteenRawFullShift C) :
    ∃ word : DetSchedule n,
      word.length ≤ n ∧
      FactorSixteenResetReady
        (runLocalSchedule ring P_partialFactorSixteenReset C word) := by
  by_cases hn : n = 1
  · obtain ⟨word, hlen, hrun⟩ :=
      factorSixteenRawFullShift_reaches_allKernel_of_eq_one ring hn C hC
    refine ⟨word, ?_, ?_⟩
    · omega
    · rw [hrun]
      exact factorSixteenResetKernel_ready ring
  · have hnTwo : 1 < n := by
      have hnPos := ring.hn
      omega
    obtain ⟨word, hlen, hrun⟩ :=
      factorSixteenRawFullShift_reaches_allKernel_of_one_lt
        ring hnTwo C hC
    refine ⟨word, ?_, ?_⟩
    · omega
    · rw [hrun]
      exact factorSixteenResetKernel_ready ring

/-! ## Exact boundary of this candidate -/

/-- A non-raw committed closed follower on which both the reset guard and the
R94 birth guard are false. -/
def factorSixteenUncoveredFixedState : FactorSixteenState :=
  ((((rawZeroHomogeneousDeletionState, false), true), false), false)

@[simp] theorem factorSixteenUncoveredFixedState_not_raw :
    ¬ InRawZeroAlphabet
      (factorSixteenRaw factorSixteenUncoveredFixedState) := by
  exact rawZeroHomogeneousDeletion_not_in_alphabet

@[simp] theorem factorSixteenUncoveredFixedState_transition :
    P_partialFactorSixteenReset factorSixteenUncoveredFixedState
      factorSixteenUncoveredFixedState =
        (factorSixteenUncoveredFixedState,
          factorSixteenUncoveredFixedState) := by
  rfl

@[simp] theorem factorSixteenUncoveredFixedState_output :
    isLeaderOutput
      (P_partialFactorSixteenResetProtocol.output
        factorSixteenUncoveredFixedState) = false := by
  rfl

/-- Thus the rule is not an arbitrary-carrier repair: the homogeneous
non-raw carrier configuration remains a zero-output fixed point under every
finite word. -/
theorem factorSixteenUncoveredFixedState_no_finite_safe
    (ring : DirectedRing n) :
    ¬ ∃ word : DetSchedule n,
      PopulationProtocol.IsSafe P_partialFactorSixteenResetProtocol ring
        (runLocalSchedule ring P_partialFactorSixteenReset
          (fun _ => factorSixteenUncoveredFixedState) word)
        isLeaderOutput := by
  apply pointwiseClass_no_finite_safe
    P_partialFactorSixteenResetProtocol ring isLeaderOutput
    (fun q => q = factorSixteenUncoveredFixedState)
  · intro l r hl hr
    subst l
    subst r
    exact ⟨rfl, rfl⟩
  · intro q hq
    subst q
    exact factorSixteenUncoveredFixedState_output
  · intro i
    rfl

#print axioms factorSixteenReset_breaks_every_raw_pair_on_every_control
#print axioms factorSixteenResetReady_run_simulation
#print axioms factorSixteenRawFullShift_reaches_resetReady
#print axioms factorSixteenUncoveredFixedState_no_finite_safe

end PPartialFactorSixteenResetEntrySol
end PPLLCompleteMultiLeaderCleanup
