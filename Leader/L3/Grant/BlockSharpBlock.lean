import Leader.L3.Grant.BlockSharpUnion
import Leader.L3.Grant.BlockFamilyHitting

/-!
# G18: C.17--C.19 with the sharp union, and the block renewal at ratio `4/17`

`GrantBlockSharpUnion.lean` gives `2047 min(B S, Λ) ≤ 2048 B U`.  With it the
family rate on the C.9--C.10 family loses only the factor `2047/2048`, and the
block success probability is at least `(4/17) W / Q`,
`Q = (b+2)(8b+13) 2^K`; the Lean ratio is `0.2389` against the paper's
`0.2387`.  The block renewal of `GrantBlockFamilyHitting.lean` then gives the
expected hitting time `(17 Q + 3)/4`.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: `grantBlockSharpFamilyRate`. -/
private theorem sharpFamilySum {α : Type} (family : List α)
    (f : α → Nat) (A B : Nat)
    (h : ∀ member, member ∈ family → A ≤ B * f member) :
    family.length * A ≤ B * (family.map f).sum := by
  induction family with
  | nil => simp
  | cons x rest ih =>
      have hx : A ≤ B * f x := h x List.mem_cons_self
      have ht : rest.length * A ≤ B * (rest.map f).sum :=
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul, Nat.mul_add] at *
      omega

/-- **The sharp family rate on the actual C.9--C.10 family.**  The family is
built as in `grantBlockFamilyRateOnSelection`; the union step is the sharp
C.17, so the rate carries the factor `2047/2048` instead of the coarse `1/4`
of `min(N, 2S) ≤ 4U`.

Consumer: `grantBlockSharpBlockMassLower`. -/
theorem grantBlockSharpFamilyRate
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
      2047 * (family.length *
        (((8 ^ R) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ R)) * n ^ T)) ≤
        2048 * ((grantBlockFamilyScale n * 8 ^ R) *
          grantBlockFamilyFrozenOrG18Mass ring C family T W) := by
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
  have hlen : family.length ≤ n := by
    rw [hlength]
    have hle : selected.length ≤ (List.finRange n).length :=
      List.Nodup.length_le_of_subset hselectedNodup (by
        intro x _
        exact List.mem_finRange x)
    rw [List.length_finRange] at hle
    exact hle
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
  have hper : ∀ member, member ∈ family →
      (((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R)) * n ^ T) ≤
      (grantBlockFamilyScale n * 8 ^ R) *
        grantBlockEventMass n T
          (fun x word =>
            grantBlockFrozenProxyHit ring x (word.take W)) member := by
    intro member hm
    have h := grantBlockFrozenDirectMarginalOfLocalClock
      ring member C R L T W hn hsp hw hlarge hradius hW hL hWT
      hbudget (hlocal member hm)
    unfold GrantBlockFrozenDirectMarginal at h
    rw [grantBlockFrozenEventMassEq ring member T W]
    exact h
  have hsum := sharpFamilySum family
    (grantBlockEventMass n T
      (fun x word =>
        grantBlockFrozenProxyHit ring x (word.take W)))
    (((8 ^ R) * (51279921 * W) -
      2 * grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ R)) * n ^ T)
    (grantBlockFamilyScale n * 8 ^ R) hper
  -- the cap `2048 Λ ≤ B n^T`
  have hcapD : 2048 * (family.length *
      ((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R))) ≤
      grantBlockFamilyScale n * 8 ^ R := by
    have hsm := grantCutoffsFrozenUnionSmallness n R W family.length
      hn hsp hradius hW hlen
    have hD : (8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R) ≤
        (8 ^ R) * (51279921 * W) := Nat.sub_le _ _
    have h1 : 2048 * (family.length *
        ((8 ^ R) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ R))) ≤
        2048 * (family.length * ((8 ^ R) * (51279921 * W))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD)
    have e : 2048 * (family.length * ((8 ^ R) * (51279921 * W))) =
        102559842 * (8 ^ R *
          (1024 * family.length * W)) := by
      have h2 : (2048 : Nat) * 51279921 = 102559842 * 1024 := by decide
      calc
        _ = (2048 * 51279921) * (8 ^ R * (family.length * W)) := by
          ac_rfl
        _ = (102559842 * 1024) * (8 ^ R * (family.length * W)) := by
          rw [h2]
        _ = _ := by ac_rfl
    have h3 : 102559842 * (8 ^ R * (1024 * family.length * W)) ≤
        102559842 * (8 ^ R * ((8 * (compileAdvice (ceilLogTwo n)).b + 13)
          * n * 2 ^ (compileAdvice (ceilLogTwo n)).K)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsm)
    have h4 : 102559842 * (8 ^ R * ((8 * (compileAdvice (ceilLogTwo n)).b
        + 13) * n * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ≤
        grantBlockFamilyScale n * 8 ^ R := by
      unfold grantBlockFamilyScale
      have e2 : 104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
          n * 2 ^ (compileAdvice (ceilLogTwo n)).K * 8 ^ R =
          104857600 * (8 ^ R * ((8 * (compileAdvice (ceilLogTwo n)).b
            + 13) * n * 2 ^ (compileAdvice (ceilLogTwo n)).K)) := by
        ac_rfl
      rw [e2]
      exact Nat.mul_le_mul_right _ (by decide)
    omega
  have hB : 0 < grantBlockFamilyScale n * 8 ^ R := by
    unfold grantBlockFamilyScale
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
      (by decide) (by omega)) (by omega)) (Nat.two_pow_pos _))
      (Nat.pow_pos (by decide))
  have hcap : 2048 * (family.length *
      (((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R)) * n ^ T)) ≤
      (grantBlockFamilyScale n * 8 ^ R) * n ^ T := by
    have h := Nat.mul_le_mul_right (n ^ T) hcapD
    have e1 : 2048 * (family.length *
        (((8 ^ R) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ R)) * n ^ T)) =
        2048 * (family.length *
          ((8 ^ R) * (51279921 * W) -
            2 * grantBlockFamilyScale n *
              (Density.N (badSet ring C) * 3 ^ R))) * n ^ T := by
      ac_rfl
    rw [e1]
    exact h
  have hsharp := grantBlockFrozenFamilySharpUnion ring (by omega)
    selected hdisjoint family hfamilyNodup hfamily hdistinct T W hWT
    (grantBlockFamilyScale n * 8 ^ R)
    (family.length *
      (((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R)) * n ^ T))
    hB hcap
  rw [Nat.min_eq_right hsum] at hsharp
  have hU := grantBlockFamilyFrozenUnionLeG18Target ring C family T W
  refine ⟨family, hfamilyNodup, ?_, ?_, hlen, ?_⟩
  · intro member hm
    refine ⟨(hmember member hm).2, hbuffered member.1 (hfamily member hm)⟩
  · rw [hlength]
    exact hcount
  · have h2 := Nat.mul_le_mul_left (grantBlockFamilyScale n * 8 ^ R) hU
    have h3 := Nat.mul_le_mul_left 2048 h2
    exact Nat.le_trans hsharp h3

/-! ### Arithmetic -/

/-- `Y <= 2^R` gives `Y 3^R <= 8^R`.

Consumer: `grantBlockSharpBlockMassLower`. -/
private theorem sharpPowSmall (R Y : Nat) (hY : Y ≤ 2 ^ R) :
    Y * 3 ^ R ≤ 8 ^ R :=
  calc
    Y * 3 ^ R ≤ 2 ^ R * 3 ^ R := Nat.mul_le_mul_right _ hY
    _ = (2 * 3) ^ R := (Nat.mul_pow 2 3 R).symm
    _ ≤ 8 ^ R := Nat.pow_le_pow_left (by decide) R

/-- Consumer: `famSharpCoreArith`. -/
private theorem famSharpLin (m1 m2 m3 g : Nat)
    (h1 : 2047 * m1 ≤ 2048 * g + 2048 * m2) (h2 : m1 + 2 * m2 = m3)
    (h3 : 65536 * m2 ≤ m3) :
    1023 * m3 ≤ 1024 * g := by
  omega

/-- The sharp rate against the crossing term.

Consumer: `grantBlockSharpBlockMassLower`. -/
private theorem famSharpCoreArith
    (S E P X M Nt G Or : Nat) (hE : 0 < E)
    (hrate : 2047 * (M * ((E * P - 2 * S * X) * Nt)) ≤
      2048 * ((S * E) * Or))
    (hcross : E * Or ≤ E * G + M * (X * Nt))
    (s1 : 65536 * (S * X) ≤ E * P) :
    1023 * (M * P) * Nt ≤ 1024 * (S * G) := by
  have hscaled := Nat.mul_le_mul_left (2048 * S) hcross
  have hrate' : 2047 * (M * ((E * P - 2 * S * X) * Nt)) ≤
      2048 * (S * (E * G)) + 2048 * (M * (S * X) * Nt) := by
    have hEq : 2048 * ((S * E) * Or) = 2048 * S * (E * Or) := by
      ac_rfl
    have hEq2 : 2048 * S * (E * G + M * (X * Nt)) =
        2048 * (S * (E * G)) + 2048 * (M * (S * X) * Nt) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    calc
      _ ≤ 2048 * ((S * E) * Or) := hrate
      _ = 2048 * S * (E * Or) := hEq
      _ ≤ 2048 * S * (E * G + M * (X * Nt)) := hscaled
      _ = _ := hEq2
  have hq : 2 * S * X ≤ E * P := by
    have e : 2 * S * X = 2 * (S * X) := Nat.mul_assoc _ _ _
    omega
  have hD : (E * P - 2 * S * X) + 2 * (S * X) = E * P := by
    have e : 2 * S * X = 2 * (S * X) := Nat.mul_assoc _ _ _
    rw [← e]
    exact Nat.sub_add_cancel hq
  have hident : M * (E * P - 2 * S * X) * Nt +
      2 * (M * (S * X) * Nt) = M * (E * P) * Nt := by
    have := congrArg (fun z => M * z * Nt) hD
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] at this ⊢
    exact this
  have hbig : 65536 * (M * (S * X) * Nt) ≤ M * (E * P) * Nt := by
    have hm := Nat.mul_le_mul_right (M * Nt) s1
    have e1 : 65536 * (M * (S * X) * Nt) = 65536 * (S * X) * (M * Nt) := by
      ac_rfl
    have e2 : M * (E * P) * Nt = E * P * (M * Nt) := by ac_rfl
    rw [e1, e2]
    exact hm
  have hlin := famSharpLin
    (M * (E * P - 2 * S * X) * Nt)
    (M * (S * X) * Nt) (M * (E * P) * Nt) (S * (E * G))
    (by
      have e : M * ((E * P - 2 * S * X) * Nt) =
          M * (E * P - 2 * S * X) * Nt := (Nat.mul_assoc _ _ _).symm
      rw [e] at hrate'
      exact hrate')
    hident hbig
  have e4 : 1023 * (M * (E * P) * Nt) = E * (1023 * (M * P) * Nt) := by
    ac_rfl
  have e5 : 1024 * (S * (E * G)) = E * (1024 * (S * G)) := by ac_rfl
  rw [e4, e5] at hlin
  exact Nat.le_of_mul_le_mul_left hlin hE

/-- The density bound and the first case to the constant `4/17`.

Consumer: `grantBlockSharpBlockMassLower`. -/
private theorem famSharpConstants
    (M n w f K2 W Nt G : Nat) (hn : 0 < n)
    (hM : 489 * n < 1000 * M * w)
    (h : 1023 * (M * (51279921 * W)) * Nt ≤
      1024 * (104857600 * f * n * K2 * G)) :
    4 * W * Nt ≤ 17 * (w * f * K2) * G := by
  have h1 : (1023 * 51279921 * W * Nt) * (489 * n) ≤
      (1023 * 51279921 * W * Nt) * (1000 * M * w) :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hM)
  have h2 : (1023 * 51279921 * W * Nt) * (1000 * M * w) =
      1000 * w * (1023 * (M * (51279921 * W)) * Nt) := by ac_rfl
  have h3 : 1000 * w * (1023 * (M * (51279921 * W)) * Nt) ≤
      1000 * w * (1024 * (104857600 * f * n * K2 * G)) :=
    Nat.mul_le_mul_left _ h
  have h4 : n * (1023 * 489 * 51279921 * (W * Nt)) ≤
      n * (1000 * 1024 * 104857600 * (w * f * K2 * G)) := by
    have e1 : n * (1023 * 489 * 51279921 * (W * Nt)) =
        (1023 * 51279921 * W * Nt) * (489 * n) := by ac_rfl
    have e2 : n * (1000 * 1024 * 104857600 * (w * f * K2 * G)) =
        1000 * w * (1024 * (104857600 * f * n * K2 * G)) := by ac_rfl
    rw [e1, e2]
    exact Nat.le_trans h1 (h2 ▸ h3)
  have h5 := Nat.le_of_mul_le_mul_left h4 hn
  have e6 : 4 * W * Nt = 4 * (W * Nt) := Nat.mul_assoc _ _ _
  have e7 : 17 * (w * f * K2) * G = 17 * (w * f * K2 * G) :=
    Nat.mul_assoc _ _ _
  rw [e6, e7]
  omega

/-- Consumer: `grantBlockSharpBlockMassLower`. -/
private theorem famSharpSmallScale
    (b K R n N : Nat) (hsq : n * n ≤ 2 ^ K) (hN : N ≤ 4 * n)
    (hR : 45 + (8 * b + 13) + K + K ≤ R) :
    65536 * (104857600 * (8 * b + 13) * n * 2 ^ K) * N ≤ 2 ^ R := by
  have hf : 8 * b + 13 ≤ 2 ^ (8 * b + 13) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  have hc : 65536 * 104857600 * 4 ≤ 2 ^ 45 := by decide
  calc
    65536 * (104857600 * (8 * b + 13) * n * 2 ^ K) * N ≤
        65536 * (104857600 * (8 * b + 13) * n * 2 ^ K) * (4 * n) :=
      Nat.mul_le_mul_left _ hN
    _ = (65536 * 104857600 * 4) * (8 * b + 13) * (n * n) * 2 ^ K := by
      ac_rfl
    _ ≤ 2 ^ 45 * 2 ^ (8 * b + 13) * 2 ^ K * 2 ^ K :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hc hf) hsq) (Nat.le_refl _)
    _ = 2 ^ (45 + (8 * b + 13) + K + K) := by
      rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    _ ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) hR

/-- **C.19 with the sharp union.**  At every purified, density-good,
grant-not-ready entrance,

`4 W n^T ≤ 17 Q * (G18 hit mass)`,  `Q = (b+2)(8b+13) 2^K`,

that is, the block success probability is at least `(4/17) W/Q`.

Consumer: `grantBlockSharpBlockFailure` (the block renewal). -/
theorem grantBlockSharpBlockMassLower
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
    4 * W * n ^ T ≤
      17 * grantBlockEntranceCoefficient n *
        grantBlockSurrogateG18HitMass ring C T W := by
  obtain ⟨family, _, hmem, hcount, hlen, hrate⟩ :=
    grantBlockSharpFamilyRate ring hn hsp hw hlarge C
      hpurified hnotready hdensity R L T W hsize hradius hW hL
      hWT hbudget
  have hcross := grantBlockFamilyOrG18CrossingBound ring hn hsp C
    hpurified family (fun m hm => (hmem m hm).1) R T W
    (fun m hm => (hmem m hm).2) hWT (Nat.le_of_eq hW)
  obtain ⟨hres, _, hRn⟩ :=
    grantCutoffsCompiledRadiusReserves n R hn hsp hradius
  have hsq := grantCutoffsPopulationSquareFitsHeads n hn
  have hn0 : 0 < n := by omega
  have hN : Density.N (badSet ring C) ≤ 4 * n :=
    Nat.le_trans (Nat.le_mul_self (defects ring C)) hdensity
  have hWpos : 256 ≤ W := by
    rw [hW]
    generalize R * n = z at hRn ⊢
    omega
  have hexp : 45 + (8 * (compileAdvice (ceilLogTwo n)).b + 13) +
      (compileAdvice (ceilLogTwo n)).K +
      (compileAdvice (ceilLogTwo n)).K ≤ R := by
    have hQ : 32 * ((compileAdvice (ceilLogTwo n)).K + 2) ≤
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hSmallScale := famSharpSmallScale
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).K R n
    (Density.N (badSet ring C)) hsq hN hexp
  have hE : 0 < 8 ^ R := Nat.pow_pos (by decide : 0 < 8)
  have s1 : 65536 * (grantBlockFamilyScale n *
      (Density.N (badSet ring C) * 3 ^ R)) ≤
      8 ^ R * (51279921 * W) := by
    have h1 := sharpPowSmall R _ hSmallScale
    have e : 65536 * (grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ R)) =
        65536 * (104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)
          * n * 2 ^ (compileAdvice (ceilLogTwo n)).K) *
          Density.N (badSet ring C) * 3 ^ R := by
      unfold grantBlockFamilyScale
      ac_rfl
    rw [e]
    have hP : 8 ^ R ≤ 8 ^ R * (51279921 * W) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact Nat.le_trans h1 hP
  have hcore := famSharpCoreArith (grantBlockFamilyScale n) (8 ^ R)
    (51279921 * W) (Density.N (badSet ring C) * 3 ^ R)
    family.length (n ^ T) (grantBlockSurrogateG18HitMass ring C T W)
    (grantBlockFamilyFrozenOrG18Mass ring C family T W)
    hE hrate hcross s1
  have hmain := famSharpConstants family.length n
    ((compileAdvice (ceilLogTwo n)).b + 2)
    (8 * (compileAdvice (ceilLogTwo n)).b + 13)
    (2 ^ (compileAdvice (ceilLogTwo n)).K) W (n ^ T)
    (grantBlockSurrogateG18HitMass ring C T W) hn0 hcount
    (by
      unfold grantBlockFamilyScale at hcore
      exact hcore)
  exact hmain

end L3

#print axioms L3.grantBlockSharpFamilyRate
#print axioms L3.grantBlockSharpBlockMassLower
