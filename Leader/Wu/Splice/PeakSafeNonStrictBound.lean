import Leader.Wu.Splice.CheckStructuralCensus
import Leader.Wu.Birth.SpatialSourceSpliceFixture
import Leader.Wu.WriteSeq.Relocation

set_option autoImplicit false
set_option Elab.async false

namespace ZZPeakSafeLE

open PPLL
open BirthPhaseCohortDesign
open B9CheckStructuralCensus
open BirthSpatialSourceSpliceCounterexample

variable {n psi kappa tau : Nat}

/-! `Leader/Wu/Splice/CheckStructuralCensus.lean:93-109`, with the single requested
change `(groups + 1) * psi < n` to `(groups + 1) * psi ≤ n`. -/

def LeaderDelimitedSegmentAt'
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (leader : Fin n) (groups : Nat) : Prop :=
  let endpoint := groupOffset ring leader ((groups + 1) * psi)
  (rawAt C leader).leader = true ∧
    (rawAt C leader).label = ⟨0, hpsi⟩ ∧
    (groups + 1) * psi ≤ n ∧
    (rawAt C endpoint).leader = true ∧
    (rawAt C endpoint).label = ⟨0, hpsi⟩ ∧
    (∀ d, 0 < d → d < (groups + 1) * psi →
      (rawAt C (groupOffset ring leader d)).leader = false) ∧
    (∀ d, d < (groups + 1) * psi →
      (rawAt C (groupOffset ring leader d)).label =
        ⟨d % psi, Nat.mod_lt d hpsi⟩)

/-! `Leader/Wu/Splice/CheckStructuralCensus.lean:115-126`, using the primed segment
predicate and otherwise unchanged. -/

def leader_delimited_peak_safe'
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  (∀ leader,
      (rawAt C leader).leader = true →
        ∃ groups, LeaderDelimitedSegmentAt' hpsi ring C leader groups) ∧
    ∀ leader groups,
      LeaderDelimitedSegmentAt' hpsi ring C leader groups →
        SegmentPeakWord (leaderSegmentWord ring C leader groups)

/-! Local public copies of the two elementary offset facts used below.
The same calculations occur privately in
`Leader/Wu/WallSweep/ShieldCircuitFull.lean:83-96`. -/

theorem groupOffset_zero_eq_le
    (ring : DirectedRing n) (start : Fin n) :
    groupOffset ring start 0 = start := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt start.isLt]

theorem groupOffset_n_eq_le
    (ring : DirectedRing n) (start : Fin n) :
    groupOffset ring start n = start := by
  apply Fin.ext
  simp [groupOffset, Nat.add_mod_right,
    Nat.mod_eq_of_lt start.isLt]

/-! `Leader/Wu/WriteSeq/Relocation.lean:17-45` gives injectivity of bounded
clockwise offsets. -/

theorem groupOffset_ne_self_of_pos_lt_le
    (ring : DirectedRing n) (start : Fin n) {d : Nat}
    (hd : 0 < d) (hdn : d < n) :
    groupOffset ring start d ≠ start := by
  have hne :=
    PPLLWriteSeqRelocation.groupOffset_ne_of_lt
      ring start hdn ring.hn (by omega : d ≠ 0)
  rw [groupOffset_zero_eq_le ring start] at hne
  exact hne

/-! Corrected implication.

The bare implication from `isStableIDSequence` is false because that predicate
is not a uniqueness predicate (`Leader/Wu/Safety/SafeConfig.lean:473-482`). The full
cycle additionally forces `psi ∣ n`. The final premise is the constructive
certificate demanded by the inductive target
(`Leader/Wu/ShortGap/SegmentPeakMerge.lean:24-31`); the existing trailing-zero theorem only
supplies its pairwise consequence. -/

theorem leader_delimited_peak_safe'_of_stableID
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (hstable :
      isStableIDSequence hpsi ring (fun i => rawAt C i))
    (hunique :
      hasUniqueLeader n (fun i => rawAt C i))
    (hdiv : psi ∣ n)
    (hrulerPeak :
      SegmentPeakWord
        ((List.range (n / psi - 1)).map
          (fun j => trailingZeros (j + 1)))) :
    leader_delimited_peak_safe' hpsi ring C := by
  obtain ⟨root, hrootLeaderB, hrootLabel, hlabels, hgroups⟩ :=
    hstable
  obtain ⟨unique, _huniqueLeader, huniqueOnly⟩ := hunique

  have hrootLeader : (rawAt C root).leader = true := by
    simpa only [AgentState.isLeader] using hrootLeaderB

  have root_unique :
      ∀ i : Fin n, (rawAt C i).isLeader → i = root :=
    fun i hi =>
      (huniqueOnly i hi).trans
        (huniqueOnly root hrootLeaderB).symm

  have hpsi_le_n : psi ≤ n :=
    Nat.le_of_dvd ring.hn hdiv

  have hquot_pos : 0 < n / psi :=
    Nat.div_pos hpsi_le_n hpsi

  have hcycle : (n / psi - 1 + 1) * psi = n := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n / psi)]
    exact Nat.div_mul_cancel hdiv

  constructor
  · intro leader hleader
    have hleaderB : (rawAt C leader).isLeader := by
      simpa only [AgentState.isLeader] using hleader
    have hleaderRoot := root_unique leader hleaderB
    subst leader
    refine ⟨n / psi - 1, ?_⟩
    unfold LeaderDelimitedSegmentAt'
    dsimp only
    rw [hcycle, groupOffset_n_eq_le ring root]
    refine ⟨hrootLeader, hrootLabel, by omega,
      hrootLeader, hrootLabel, ?_, ?_⟩
    · intro d hd hdn
      have hne :=
        groupOffset_ne_self_of_pos_lt_le ring root hd hdn
      cases hvalue :
          (rawAt C (groupOffset ring root d)).leader
      · rfl
      · have hleadB :
            (rawAt C (groupOffset ring root d)).isLeader := by
          change (rawAt C (groupOffset ring root d)).leader = true
          exact hvalue
        exact (hne (root_unique _ hleadB)).elim
    · intro d hdn
      simpa only [groupOffset] using hlabels d hdn

  · intro leader groups hseg
    unfold LeaderDelimitedSegmentAt' at hseg
    dsimp only at hseg

    have hleaderB : (rawAt C leader).isLeader := by
      simpa only [AgentState.isLeader] using hseg.1
    have hleaderRoot := root_unique leader hleaderB
    subst leader

    have hstepsPos : 0 < (groups + 1) * psi :=
      Nat.mul_pos (by omega) hpsi
    have hstepsLe : (groups + 1) * psi ≤ n :=
      hseg.2.2.1
    have hendLeaderB :
        (rawAt C
          (groupOffset ring root ((groups + 1) * psi))).isLeader := by
      simpa only [AgentState.isLeader] using hseg.2.2.2.1
    have hendRoot :
        groupOffset ring root ((groups + 1) * psi) = root :=
      root_unique _ hendLeaderB

    have hstepsEq : (groups + 1) * psi = n := by
      by_cases hlt : (groups + 1) * psi < n
      · have hne :=
          groupOffset_ne_self_of_pos_lt_le
            ring root hstepsPos hlt
        exact (hne hendRoot).elim
      · omega

    have hquotEq : n / psi = groups + 1 := by
      rw [← hstepsEq, Nat.mul_comm (groups + 1) psi]
      exact Nat.mul_div_cancel_left (groups + 1) hpsi

    have hgroupsEq : groups = n / psi - 1 := by
      omega
    rw [hgroupsEq]

    have hword :
        leaderSegmentWord ring C root (n / psi - 1) =
          (List.range (n / psi - 1)).map
            (fun j => trailingZeros (j + 1)) := by
      unfold leaderSegmentWord
      apply List.map_congr_left
      intro j hj
      have hjlt : j < n / psi - 1 :=
        List.mem_range.mp hj
      have hg := hgroups (j + 1) (by omega) (by omega)
      simpa only [groupOffset] using hg

    rw [hword]
    exact hrulerPeak

/-! Concrete constructive certificate for the fixture word.
`SegmentPeakWord` is inductive (`Leader/Wu/ShortGap/SegmentPeakMerge.lean:24-31`), so the
proof deliberately uses `pivot`, not an invented theorem name. -/

theorem ruler1_peak : SegmentPeakWord [0] := by
  exact SegmentPeakWord.pivot [] [] 0
    .empty .empty (by simp) (by simp)

theorem ruler3_peak : SegmentPeakWord [0, 1, 0] := by
  simpa using
    (SegmentPeakWord.pivot [0] [0] 1
      ruler1_peak ruler1_peak (by simp) (by simp))

theorem ruler7_peak :
    SegmentPeakWord [0, 1, 0, 2, 0, 1, 0] := by
  simpa using
    (SegmentPeakWord.pivot
      [0, 1, 0] [0, 1, 0] 2
      ruler3_peak ruler3_peak (by simp) (by simp))

theorem ruler15_peak :
    SegmentPeakWord
      [0, 1, 0, 2, 0, 1, 0, 3,
       0, 1, 0, 2, 0, 1, 0] := by
  simpa using
    (SegmentPeakWord.pivot
      [0, 1, 0, 2, 0, 1, 0]
      [0, 1, 0, 2, 0, 1, 0]
      3 ruler7_peak ruler7_peak (by simp) (by simp))

/-! Kernel evaluation checks that groups 1 through 15 have exactly the
displayed trailing-zero word (`Leader/Wu/Safety/SafeConfig.lean:119-168`). -/

theorem ruler15_trailingZeros_peak :
    SegmentPeakWord
      ((List.range (32 / 2 - 1)).map
        (fun j => trailingZeros (j + 1))) := by
  have hword :
      ((List.range (32 / 2 - 1)).map
        (fun j => trailingZeros (j + 1))) =
        [0, 1, 0, 2, 0, 1, 0, 3,
         0, 1, 0, 2, 0, 1, 0] := by
    decide +kernel
  rw [hword]
  exact ruler15_peak

/-! `initial_erase` is the exact bridge supplied at
`Leader/Wu/Birth/SpatialSourceSpliceFixture.lean:46-48`. -/

theorem initial_rawAt_point (i : Fin 32) :
    rawAt initial i = initialCore i := by
  change (initial i).core.core.erase = initialCore i
  exact congrFun initial_erase i

theorem initial_rawAt_eq :
    (fun i => rawAt initial i) = initialCore := by
  funext i
  exact initial_rawAt_point i

/-! Exact requested witness: n=32, psi=2, leader=30, groups=15.
The proof uses the already-proved stable ruler and unique-leader fields rather
than unavailable finite interval case splitting. -/

theorem initial_segment15' :
    LeaderDelimitedSegmentAt'
      twoPositive ringThirtyTwo initial (30 : Fin 32) 15 := by
  have hstable :
      isStableIDSequence twoPositive ringThirtyTwo
        (fun i => rawAt initial i) := by
    rw [initial_rawAt_eq]
    exact initial_ruler

  have hunique :
      hasUniqueLeader 32 (fun i => rawAt initial i) := by
    rw [initial_rawAt_eq]
    have h := initial_paperSafe.unique_leader
    rw [initial_erase] at h
    exact h

  obtain ⟨root, hrootLeaderB, hrootLabel, hlabels, _hgroups⟩ :=
    hstable
  obtain ⟨unique, _huniqueLeaderB, huniqueOnly⟩ := hunique

  have h30LeaderB :
      (rawAt initial (30 : Fin 32)).isLeader := by
    rw [initial_rawAt_point]
    change (initialCore (30 : Fin 32)).leader = true
    decide +kernel

  have hrootEq : root = (30 : Fin 32) :=
    (huniqueOnly root hrootLeaderB).trans
      (huniqueOnly (30 : Fin 32) h30LeaderB).symm
  subst root

  have hrootLeader :
      (rawAt initial (30 : Fin 32)).leader = true := by
    simpa only [AgentState.isLeader] using hrootLeaderB

  unfold LeaderDelimitedSegmentAt'
  dsimp only
  have hcycle : (15 + 1) * 2 = 32 := by omega
  rw [hcycle, groupOffset_n_eq_le ringThirtyTwo (30 : Fin 32)]
  refine ⟨hrootLeader, hrootLabel, by omega,
    hrootLeader, hrootLabel, ?_, ?_⟩
  · intro d hd hdn
    have hne :=
      groupOffset_ne_self_of_pos_lt_le
        ringThirtyTwo (30 : Fin 32) hd hdn
    cases hvalue :
        (rawAt initial
          (groupOffset ringThirtyTwo (30 : Fin 32) d)).leader
    · rfl
    · have hleadB :
          (rawAt initial
            (groupOffset ringThirtyTwo (30 : Fin 32) d)).isLeader := by
        change
          (rawAt initial
            (groupOffset ringThirtyTwo (30 : Fin 32) d)).leader = true
        exact hvalue
      have heq :
          groupOffset ringThirtyTwo (30 : Fin 32) d =
            (30 : Fin 32) :=
        (huniqueOnly _ hleadB).trans
          (huniqueOnly (30 : Fin 32) h30LeaderB).symm
      exact (hne heq).elim
  · intro d hdn
    simpa only [groupOffset] using hlabels d hdn

/-! Full primed safety of the actual physical fixture. Uniqueness comes from
`initial_paperSafe`, stable IDs from `initial_ruler`, divisibility is `2 ∣ 32`,
and the word certificate is the four-level pivot proof above. -/

theorem initial_leader_delimited_peak_safe' :
    leader_delimited_peak_safe'
      twoPositive ringThirtyTwo initial := by
  have hstable :
      isStableIDSequence twoPositive ringThirtyTwo
        (fun i => rawAt initial i) := by
    rw [initial_rawAt_eq]
    exact initial_ruler

  have hunique :
      hasUniqueLeader 32 (fun i => rawAt initial i) := by
    rw [initial_rawAt_eq]
    have h := initial_paperSafe.unique_leader
    rw [initial_erase] at h
    exact h

  exact leader_delimited_peak_safe'_of_stableID
    twoPositive ringThirtyTwo initial
    hstable hunique (by decide +kernel) ruler15_trailingZeros_peak

#print axioms ZZPeakSafeLE.groupOffset_zero_eq_le
#print axioms ZZPeakSafeLE.groupOffset_n_eq_le
#print axioms ZZPeakSafeLE.groupOffset_ne_self_of_pos_lt_le
#print axioms ZZPeakSafeLE.leader_delimited_peak_safe'_of_stableID
#print axioms ZZPeakSafeLE.ruler1_peak
#print axioms ZZPeakSafeLE.ruler3_peak
#print axioms ZZPeakSafeLE.ruler7_peak
#print axioms ZZPeakSafeLE.ruler15_peak
#print axioms ZZPeakSafeLE.ruler15_trailingZeros_peak
#print axioms ZZPeakSafeLE.initial_rawAt_point
#print axioms ZZPeakSafeLE.initial_rawAt_eq
#print axioms ZZPeakSafeLE.initial_segment15'
#print axioms ZZPeakSafeLE.initial_leader_delimited_peak_safe'

end ZZPeakSafeLE
