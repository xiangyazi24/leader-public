import Leader.L3.Grant.BlockPrefixPair

/-!
G16 block-renewal handoff. This module recovers the *buffered*
spatial witness that was erased from the result type of
bankTrialBufferedSpatialPreGrantFrozen, constructs a carrier family,
and instantiates the previously merged C.17 inequality.

C.18/C.19 and the expected
hitting-time theorem are NOT claimed.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Select one genuine cold carrier for each member of a Nodup
root list. The root projection remains injective, and every
carrier has the original physical configuration. -/
theorem grantBlockRenewalChooseCarriers
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    ∀ selected : List (Fin n),
      selected.Nodup →
      (∀ root : Fin n, root ∈ selected →
        ∃ x : Counter.ResetClockBankColdCarrier
            (q := ceilLogTwo n) ring root,
          x.val = C) →
      ∃ family : List (GrantBlockFamilyMember ring),
        family.Nodup ∧
        family.length = selected.length ∧
        (∀ member, member ∈ family →
          member.1 ∈ selected ∧ member.2.val = C) ∧
        (∀ left, left ∈ family →
          ∀ right, right ∈ family →
            left ≠ right → left.1 ≠ right.1) := by
  intro selected
  induction selected with
  | nil =>
      intro _ _
      refine ⟨[], by simp, rfl, ?_, ?_⟩
      · intro member hm
        cases hm
      · intro left hl right hr hne
        cases hl
  | cons root tail ih =>
      intro hnodup hcarriers
      have hnot : root ∉ tail :=
        (List.nodup_cons.mp hnodup).1
      have htail : tail.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have htailCarriers :
          ∀ other : Fin n, other ∈ tail →
            ∃ x : Counter.ResetClockBankColdCarrier
                (q := ceilLogTwo n) ring other,
              x.val = C := by
        intro other hm
        exact hcarriers other (List.mem_cons_of_mem root hm)
      obtain ⟨family, hfamilyNodup, hlength,
          hmember, hdistinct⟩ :=
        ih htail htailCarriers
      obtain ⟨carrier, hcarrier⟩ :=
        hcarriers root List.mem_cons_self
      have hheadNot :
          (⟨root, carrier⟩ : GrantBlockFamilyMember ring) ∉
            family := by
        intro hm
        exact hnot (hmember ⟨root, carrier⟩ hm).1
      refine ⟨(⟨root, carrier⟩ :
          GrantBlockFamilyMember ring) :: family,
        ?_, ?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr
          ⟨hheadNot, hfamilyNodup⟩
      · simp only [List.length_cons, hlength]
      · intro member hm
        rcases List.mem_cons.mp hm with heq | htailMem
        · cases heq
          exact ⟨List.mem_cons_self, hcarrier⟩
        · obtain ⟨hroot, hC⟩ := hmember member htailMem
          exact ⟨List.mem_cons_of_mem root hroot, hC⟩
      · intro left hl right hr hne
        rcases List.mem_cons.mp hl with hleft | hleft
        · cases hleft
          rcases List.mem_cons.mp hr with hright | hright
          · cases hright
            exact False.elim (hne rfl)
          · intro heq
            have heq' : root = right.1 := heq
            have hroot : root ∈ tail := by
              rw [heq']
              exact (hmember right hright).1
            exact hnot hroot
        · rcases List.mem_cons.mp hr with hright | hright
          · cases hright
            intro heq
            have heq' : left.1 = root := heq
            have hroot : root ∈ tail := by
              rw [← heq']
              exact (hmember left hleft).1
            exact hnot hroot
          · exact hdistinct left hleft right hright hne

/-- Keep the exact C.17 min/Bonferroni inequality in a named
interface, without replacing the original scheduler mass by
a physical GRANT-hit mass. -/
def GrantBlockRenewalFrozenLower
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (family : List (GrantBlockFamilyMember ring))
    (R T W : Nat) : Prop :=
  min
    ((grantBlockFamilyScale n * 8 ^ R) * n ^ T)
    (2 * (family.length *
      (((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R)) *
        n ^ T))) ≤
    4 * (grantBlockFamilyScale n * 8 ^ R) *
      grantBlockFamilyFrozenOrG18Mass ring C family T W +
    2 * (grantBlockFamilyScale n * 8 ^ R) *
      (family.length *
        grantBlockFamilyFrozenOrG18Mass ring C family T W)

/-- Reconstruct the C.9--C.10 selection from its buffered
source, then obtain each cold carrier via the same C.15
constructor used by bankTrialBufferedSpatialPreGrantFrozen.
The preserved rear-buffer witness is needed by C.17. -/
theorem grantBlockRenewalSpatialFrozenLower
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (C : HeadlineConfiguration n)
    (hpurified : headlinePurified ring C)
    (hnotready : ¬ headlineGrantReady ring C)
    (hdensity : defects ring C * defects ring C ≤ 4 * n)
    (R L T W : Nat)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T) :
    ∃ family : List (GrantBlockFamilyMember ring),
      family.Nodup ∧
      489 * n <
        1000 * family.length *
          ((compileAdvice (ceilLogTwo n)).b + 2) ∧
      GrantBlockRenewalFrozenLower ring C family R T W := by
  obtain ⟨selected, hselectedNodup, hbuffered,
      hdisjoint, hcount⟩ :=
    (headlineGrantSpatialSupportBridgeProved ring)
      C R hsize hradius.1 hradius.2 hdensity
  have hselection :
      BankTrialBufferedSelectionAtBlockEntrance
        (q := ceilLogTwo n) ring C selected :=
    bankTrialBufferedSelectionBeforeGrant
      ring C R selected hpurified hnotready hbuffered
  have hcarriers :
      ∀ root : Fin n, root ∈ selected →
        ∃ x : Counter.ResetClockBankColdCarrier
            (q := ceilLogTwo n) ring root,
          x.val = C := by
    intro root hr
    obtain ⟨x, hC, _, _⟩ :=
      bankTrialBufferedSelectedFrozenNoDefect
        ring C selected hsp hselection root hr
    exact ⟨x, hC⟩
  obtain ⟨family, hfamilyNodup, hlength,
      hmember, hdistinct⟩ :=
    grantBlockRenewalChooseCarriers
      ring C selected hselectedNodup hcarriers
  have hfamily :
      ∀ member, member ∈ family →
        member.1 ∈ selected := by
    intro member hm
    exact (hmember member hm).1
  have hcommon :
      ∀ member, member ∈ family →
        member.2.val = C := by
    intro member hm
    exact (hmember member hm).2
  have hfamilyBuffered :
      ∀ member, member ∈ family →
        HeadlineGrantBufferedCounter ring C R member.1 := by
    intro member hm
    exact hbuffered member.1 (hfamily member hm)
  have hcountFamily :
      489 * n <
        1000 * family.length *
          ((compileAdvice (ceilLogTwo n)).b + 2) := by
    rw [hlength]
    exact hcount
  have hcross : W ≤ R * n / 8 := by
    rw [hW]
    exact Nat.le_refl _
  have hbound : GrantBlockRenewalFrozenLower
      ring C family R T W :=
    grantBlockFamilyFrozenBlockLower
      ring hn hsp hw hlarge C hpurified
      selected hdisjoint family hfamilyNodup
      hfamily hdistinct hcommon R L T W R
      hradius hW hL hWT hbudget
      hfamilyBuffered hcross
  exact ⟨family, hfamilyNodup, hcountFamily, hbound⟩

/-- Opaque-Nat C.18 arithmetic *interface*: only the cutoff
hypothesis (not yet obtained from the actual compiler
parameters) is needed to turn the C.17 min bound into a
positive event mass. No powers are expanded in the tactic. -/
theorem grantBlockRenewalOpaqueMinCutoff
    (M S N A U E : Nat)
    (hS : 0 < S)
    (hfamily :
      min (S * N) (2 * (M * A)) ≤
        4 * S * U + 2 * S * (M * U))
    (hcutoff :
      ((4 + 2 * M) * S) * E ≤
        min (S * N) (2 * (M * A))) :
    E ≤ U := by
  have hfactor :
      4 * S * U + 2 * S * (M * U) =
        ((4 + 2 * M) * S) * U := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
  have hpos : 0 < (4 + 2 * M) * S :=
    Nat.mul_pos (by omega) hS
  have hscaled :
      ((4 + 2 * M) * S) * E ≤
        ((4 + 2 * M) * S) * U := by
    calc
      ((4 + 2 * M) * S) * E ≤
        min (S * N) (2 * (M * A)) := hcutoff
      _ ≤ 4 * S * U + 2 * S * (M * U) := hfamily
      _ = ((4 + 2 * M) * S) * U := hfactor
  exact Nat.le_of_mul_le_mul_left hscaled hpos

/-- Original physical word association, without referring to
the private helper in GrantBlockSurrogateFrozen. -/
private theorem grantBlockRenewalPhysicalWordAppend
    {n q : Nat} (ring : DirectedRing n) :
    ∀ (pre suffix : List (Fin n))
      (C : Counter.Config q n),
      Counter.Word ring (pre ++ suffix) C =
        Counter.Word ring suffix (Counter.Word ring pre C) := by
  intro pre
  induction pre with
  | nil =>
      intro suffix C
      rfl
  | cons edge rest ih =>
      intro suffix C
      change Counter.Word ring (rest ++ suffix)
          ((protocol q).step ring C edge) =
        Counter.Word ring suffix
          (Counter.Word ring rest
            ((protocol q).step ring C edge))
      exact ih suffix _

/-- The exact physical classification currently obtainable
from a frozen hit. The third disjunct is an actual first BANK
success with no proved implication to a GRANT-ready physical
cut. The first disjunct is a genuine G18 prefix hit. -/
theorem grantBlockRenewalFrozenHitClassification
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
    (W : Nat) (word : List (Fin n))
    (hhit :
      grantBlockFrozenProxyHit
        ring member (word.take W) = true) :
    GrantBlockSurrogateG18HitWithin
        ring member.2.val W word ∨
      GrantBlockFirstDefectFailure
        ring member.1 member.2.val (word.take W) ∨
      GrantBlockFirstBankFailure
        ring member.1 member.2.val (word.take W) := by
  rcases grantBlockFrozenHitFirstFailureCases
      ring hsp member W word hhit with hg | hd | hb
  · obtain ⟨pre, edge, suffix, hword, hpost⟩ :=
      grantBlockG18FirstGrantFailureReady
        ring hn member.2.val hp member.1
        (word.take W) hg
    left
    refine ⟨pre ++ [edge], suffix, ?_, ?_⟩
    · rw [hword]
      simp only [List.append_assoc, List.singleton_append]
    · have hstate :
          Counter.Word ring (pre ++ [edge]) member.2.val =
            headlinePhysicalNext ring
              (Counter.Word ring pre member.2.val) edge := by
        rw [grantBlockRenewalPhysicalWordAppend
          ring pre [edge] member.2.val]
        rfl
      rw [hstate]
      exact hpost
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr hb)

end L3

#print axioms L3.grantBlockRenewalChooseCarriers
#print axioms L3.grantBlockRenewalSpatialFrozenLower
#print axioms L3.grantBlockRenewalOpaqueMinCutoff
#print axioms L3.grantBlockRenewalFrozenHitClassification
