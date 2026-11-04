import Leader.L3.Grant.BlockFrozenRecoveryRenewal
import Leader.L3.Grant.BlockFrozenAmplification
import Leader.L3.Grant.BlockRenewal

/-!
# G16: the C.17 family rate on the actual C.9--C.10 family

`grantBlockFrozenDirectExplicitRate` needs the support-disjointness data of
the family and, for each member, the frozen local clock.  Here both come from
the C.9--C.10 selection: the selection supplies disjoint supports and buffered
roots, `grantBlockRenewalChooseCarriers` supplies one cold carrier per
selected root, and `grantBlockFrozenLocalColdClockOfBuffered` supplies the
frozen clock of every buffered member with no premise beyond the clock's own.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The C.17 family rate on the family built from the C.9--C.10 selection,
with no local-clock hypothesis.  The family is the selected roots, each with
the entrance configuration `C` as carrier; every member is buffered at radius
`R`; the count `489 n < 1000 |family| (b+2)` is the C.10 density, and the
roots are distinct so `|family| ≤ n`.

Consumer: `grantBlockFamilyBlockMassLower` (the C.18--C.19 block bound). -/
theorem grantBlockFamilyRateOnSelection
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
      (∀ member, member ∈ family →
        member.2.val = C ∧
        HeadlineGrantBufferedCounter ring C R member.1) ∧
      489 * n <
        1000 * family.length *
          ((compileAdvice (ceilLogTwo n)).b + 2) ∧
      family.length ≤ n ∧
      grantBlockFrozenDirectRateNumerator
          ring C family.length R W * n ^ T ≤
        grantBlockFrozenDirectRateDenominator n R *
          grantBlockFamilyFrozenOrG18Mass
            ring C family T W := by
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
      ∀ member, member ∈ family → member.1 ∈ selected :=
    fun member hm => (hmember member hm).1
  have hbufferedMembers :
      ∀ member, member ∈ family →
        member.2.val = C ∧
        HeadlineGrantBufferedCounter ring C R member.1 := by
    intro member hm
    refine ⟨(hmember member hm).2, hbuffered member.1 (hfamily member hm)⟩
  have hlocal :
      ∀ member, member ∈ family →
        GrantBlockFrozenLocalColdClock ring member R L T W := by
    intro member hm
    have hb : HeadlineGrantBufferedCounter ring member.2.val R
        member.1 := by
      rw [(hmember member hm).2]
      exact hbuffered member.1 (hfamily member hm)
    exact grantBlockFrozenLocalColdClockOfBuffered
      ring member R hb R L T W
  refine ⟨family, hfamilyNodup, hbufferedMembers, ?_, ?_, ?_⟩
  · rw [hlength]
    exact hcount
  · rw [hlength]
    have hle : selected.length ≤ (List.finRange n).length :=
      List.Nodup.length_le_of_subset hselectedNodup (by
        intro x _
        exact List.mem_finRange x)
    rw [List.length_finRange] at hle
    exact hle
  · exact grantBlockFrozenDirectExplicitRate
      ring hn hsp hw hlarge C selected hdisjoint family
      hfamilyNodup hfamily hdistinct R L T W hradius hW hL hWT
      hbudget hlocal

end L3

#print axioms L3.grantBlockFamilyRateOnSelection
