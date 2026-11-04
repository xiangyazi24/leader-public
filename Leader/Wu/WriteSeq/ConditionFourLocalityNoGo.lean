import Leader.Wu.WriteSeq.LifecycleObstructions
import Leader.Wu.Safety.NoCheckBirthConditionFourRegression

/-!
# Pair-locality obstruction for corrected condition 4

R35's scheduled pair cannot reveal whether flipping its terminal flag completes
a globally free overwriting signal.  This module constructs a second `ψ=3,
n=9` PaperSafe configuration that is identical to R35 at scheduled endpoints
7 and 8, but changes only the remote position-6 flag from one to zero.  The
packaged protocol therefore executes exactly the same local interaction.  R35's
output violates condition 4, while the remote-zero twin's output still has no
complete flag-one signal and satisfies condition 4.

The separation does not say every pair-local repair is impossible: a local gate
can conservatively reject the shared pair in both contexts.  It proves that no
pair-local rule can be *exact* for literal condition 4 from `PaperSafeConfig`
alone.  Preserving intended progress while rejecting R35 requires a stronger
global/neighbor-chain lifecycle invariant or additional physically validated
context.
-/

namespace PPLLWriteConditionFourLocalityNoGo

open PPLL PPLLNoCheckBirthRepair
  PPLLExpiringComparisonRepair PPLLAuthorizedComparisonRepair
  PPLLNoCheckBirthPhysicalConditionOne
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionThreeProtocol
  PPLLNoCheckBirthConditionFourRegression

set_option linter.defProp false

private theorem finNineCases (i : Fin 9) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by
    omega
  rcases h with h | h | h | h | h | h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (.inl (Fin.ext h))))
  · exact .inr (.inr (.inr (.inr (.inl (Fin.ext h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (Fin.ext h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (Fin.ext h)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (Fin.ext h))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (Fin.ext h))))))))

/-- Remote-zero twin of R35. Only position 6 changes, and only its path3 flag
from one to zero. -/
def conditionFourTwinCore (i : Fin 9) : AgentState 3 :=
  if i.val = 6 then
    { conditionFourCoreConfig i with path3 := some ⟨0, 0, 0⟩ }
  else conditionFourCoreConfig i

/-- The twin preserves every field read by conditions 1--3. -/
theorem twinPeaceView (i : Fin 9) :
    PeaceView.ofState (conditionFourTwinCore i) =
      PeaceView.ofState (conditionFourCoreConfig i) := by
  unfold conditionFourTwinCore
  split <;> rfl

/-- The twin also preserves all stable-ID bits. -/
theorem twinBit (i : Fin 9) :
    (conditionFourTwinCore i).bit = (conditionFourCoreConfig i).bit := by
  unfold conditionFourTwinCore
  split <;> rfl

private theorem twinBulletZero (i : Fin 9) :
    (conditionFourTwinCore i).bullet = ⟨0, by omega⟩ := by
  rcases finNineCases i with h | h | h | h | h | h | h | h | h <;>
    subst i <;> decide

/-- Every twin state lies in the same exact finite domain. -/
theorem twinDomain (i : Fin 9) :
    (conditionFourTwinCore i).inProtocolDomain 10 := by
  by_cases h6 : i.val = 6
  · have hi : i = 6 := Fin.ext h6
    subst i
    rw [AgentState.inProtocolDomain]
    have hold := conditionFourCore_inProtocolDomain (6 : Fin 9)
    rw [AgentState.inProtocolDomain] at hold
    have hval : (6 : Fin 9).val = 6 := rfl
    exact ⟨hold.1, hold.2.1, hold.2.2.1,
      by simp [conditionFourTwinCore, hval],
      hold.2.2.2.2.1, hold.2.2.2.2.2⟩
  · simpa [conditionFourTwinCore, h6] using
      conditionFourCore_inProtocolDomain i

/-- Exact finite reification with the same authorization/timer values as R35. -/
def conditionFourTwinFinite (i : Fin 9) : ExpiringAgentState 3 10 0 :=
  ⟨⟨BoundedAgentState.ofDomain (conditionFourTwinCore i) (twinDomain i), false⟩,
    ⟨0, by omega⟩⟩

/-- Exact packaged successor on the same scheduled edge as R35. -/
def conditionFourTwinAfter : Fin 9 → ExpiringAgentState 3 10 0 :=
  (noCheckBirthProtocol hThree 10 0).step ringNine
    conditionFourTwinFinite conditionFourEdge

/-- Finite erasure recovers the displayed twin. -/
theorem eraseTwin :
    eraseExpiringConfig conditionFourTwinFinite = conditionFourTwinCore := by
  funext i
  change BoundedAgentState.erase
    (BoundedAgentState.ofDomain (conditionFourTwinCore i) (twinDomain i)) = _
  exact BoundedAgentState.erase_ofDomain _ _

private theorem twinUnique : hasUniqueLeader 9 conditionFourTwinCore := by
  obtain ⟨lp, hlp, honly⟩ := conditionFourCore_paperSafe.unique_leader
  refine ⟨lp, ?_, ?_⟩
  · unfold AgentState.isLeader at hlp ⊢
    exact (congrArg PeaceView.leader (twinPeaceView lp)).trans hlp
  · intro i hi
    apply honly i
    unfold AgentState.isLeader at hi ⊢
    exact (congrArg PeaceView.leader (twinPeaceView i)).symm.trans hi

private theorem twinNoBullet :
    noNonPeacefulBullet hThree ringNine conditionFourTwinCore := by
  intro i hlive
  have hz := congrArg Fin.val (twinBulletZero i)
  have hv := congrArg Fin.val hlive
  change (conditionFourTwinCore i).bullet.val = 0 at hz
  change (conditionFourTwinCore i).bullet.val = 2 at hv
  omega

private theorem twinStable :
    isStableIDSequence hThree ringNine conditionFourTwinCore := by
  obtain ⟨lp, hlp, hzero, hlabels, hgroups⟩ :=
    conditionFourCore_paperSafe.stable_id_sequence
  refine ⟨lp, ?_, ?_, ?_, ?_⟩
  · unfold AgentState.isLeader at hlp ⊢
    exact (congrArg PeaceView.leader (twinPeaceView lp)).trans hlp
  · exact (congrArg PeaceView.label (twinPeaceView lp)).trans hzero
  · intro k hk
    exact (congrArg PeaceView.label
      (twinPeaceView ⟨(lp.val + k) % 9,
        Nat.mod_lt _ ringNine.hn⟩)).trans (hlabels k hk)
  · intro i hi hbound
    calc
      groupID ringNine.hn conditionFourTwinCore
          ⟨(lp.val + i * 3) % 9, Nat.mod_lt _ ringNine.hn⟩ =
        groupID ringNine.hn conditionFourCoreConfig
          ⟨(lp.val + i * 3) % 9, Nat.mod_lt _ ringNine.hn⟩ := by
            simp only [groupID, twinBit]
      _ = trailingZeros i := hgroups i hi hbound

private theorem twinPathThree :
    (conditionFourTwinCore 3).path3 = none := by
  rfl

private theorem twinPathSix :
    (conditionFourTwinCore 6).path3 = some ⟨0, 0, 0⟩ := by
  rfl

private theorem twinNoFree :
    noFreeOverwritingSignal hThree ringNine conditionFourTwinCore := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  have hi12 : i = 1 ∨ i = 2 := by omega
  rcases hi12 with h | h
  · subst i
    obtain ⟨_, haligned⟩ := hfree.1
    obtain ⟨p, hp, _⟩ := haligned 0 (by omega)
    change (conditionFourTwinCore 3).path3 = some p at hp
    rw [twinPathThree] at hp
    contradiction
  · subst i
    obtain ⟨_, haligned⟩ := hfree.1
    obtain ⟨p, hp, _, _, hflag⟩ := haligned 0 (by omega)
    change (conditionFourTwinCore 6).path3 = some p at hp
    rw [twinPathSix] at hp
    cases hp
    simp at hflag

/-- The remote-zero input still satisfies all five paper fields. -/
theorem twinPaperSafe :
    PaperSafeConfig hThree ringNine conditionFourTwinCore where
  unique_leader := twinUnique
  no_nonpeaceful_bullet := twinNoBullet
  no_free_barrier :=
    noFreeBarrier_of_stableID hThree ringNine _ twinStable
  no_free_overwriting_signal := twinNoFree
  stable_id_sequence := twinStable

/-- Every raw position other than the remote flag site is unchanged. -/
theorem twinOnlyDiffersAtSix :
    ∀ i : Fin 9, i ≠ 6 →
      conditionFourTwinCore i = conditionFourCoreConfig i := by
  intro i hi
  unfold conditionFourTwinCore
  rw [if_neg]
  intro hval
  exact hi (Fin.ext hval)

/-- R35 and its twin are byte-for-byte equal at the scheduled raw endpoints. -/
theorem twinScheduledPairEq :
    conditionFourTwinCore 7 = conditionFourCoreConfig 7 ∧
      conditionFourTwinCore 8 = conditionFourCoreConfig 8 := by
  decide

/-- The exact finite authorization/timer states also agree at both scheduled
endpoints; the packaged transition receives byte-for-byte identical inputs. -/
theorem twinScheduledFinitePairEq :
    conditionFourTwinFinite 7 = conditionFourFiniteConfig 7 ∧
      conditionFourTwinFinite 8 = conditionFourFiniteConfig 8 := by
  decide

/-- The identical finite local inputs produce identical finite endpoint outputs
under the same packaged transition. -/
theorem twinAfterScheduledPairEq :
    conditionFourTwinAfter 7 = conditionFourFiniteAfter 7 ∧
      conditionFourTwinAfter 8 = conditionFourFiniteAfter 8 := by
  decide

/-- The remote flag remains zero after the disjoint scheduled interaction. -/
theorem twinAfterPaths :
    let D := eraseExpiringConfig conditionFourTwinAfter
    (D 3).path3 = none ∧ (D 6).path3 = some ⟨0, 0, 0⟩ := by
  decide

/-- Consequently the twin output has no complete flag-one free signal. -/
theorem twinAfterNoFree :
    noFreeOverwritingSignal hThree ringNine
      (eraseExpiringConfig conditionFourTwinAfter) := by
  let D := eraseExpiringConfig conditionFourTwinAfter
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  have hi12 : i = 1 ∨ i = 2 := by omega
  have hp := twinAfterPaths
  rcases hi12 with h | h
  · subst i
    obtain ⟨_, haligned⟩ := hfree.1
    obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
    change (D 3).path3 = some p at hpath
    rw [hp.1] at hpath
    contradiction
  · subst i
    obtain ⟨_, haligned⟩ := hfree.1
    obtain ⟨p, hpath, _, _, hflag⟩ := haligned 0 (by omega)
    change (D 6).path3 = some p at hpath
    rw [hp.2] at hpath
    cases hpath
    simp at hflag

/-- **Pair-locality separation for condition 4.** Both exact finite inputs are
PaperSafe and present the same scheduled endpoint pair. The same packaged local
interaction violates condition 4 in R35 but preserves it in the remote-zero
twin. -/
theorem conditionFour_pair_locality_separation :
    PaperSafeConfig hThree ringNine
      (eraseExpiringConfig conditionFourFiniteConfig) ∧
    PaperSafeConfig hThree ringNine
      (eraseExpiringConfig conditionFourTwinFinite) ∧
    (∀ i : Fin 9, i ≠ 6 →
      conditionFourTwinCore i = conditionFourCoreConfig i) ∧
    conditionFourTwinCore 7 = conditionFourCoreConfig 7 ∧
    conditionFourTwinCore 8 = conditionFourCoreConfig 8 ∧
    conditionFourTwinFinite 7 = conditionFourFiniteConfig 7 ∧
    conditionFourTwinFinite 8 = conditionFourFiniteConfig 8 ∧
    conditionFourTwinAfter 7 = conditionFourFiniteAfter 7 ∧
    conditionFourTwinAfter 8 = conditionFourFiniteAfter 8 ∧
    ¬noFreeOverwritingSignal hThree ringNine
      (eraseExpiringConfig conditionFourFiniteAfter) ∧
    noFreeOverwritingSignal hThree ringNine
      (eraseExpiringConfig conditionFourTwinAfter) := by
  refine ⟨?_, ?_, twinOnlyDiffersAtSix,
    twinScheduledPairEq.1, twinScheduledPairEq.2,
    twinScheduledFinitePairEq.1, twinScheduledFinitePairEq.2,
    twinAfterScheduledPairEq.1, twinAfterScheduledPairEq.2,
    ?_, twinAfterNoFree⟩
  · rw [erase_conditionFourFiniteConfig]
    exact conditionFourCore_paperSafe
  · rw [eraseTwin]
    exact twinPaperSafe
  · exact noCheckBirthProtocol_conditionFour_counterexample.2

end PPLLWriteConditionFourLocalityNoGo
