import Leader.Wu.Entrance.FinalRowNonRecovery

set_option autoImplicit false
set_option Elab.async false

namespace FinalCandidateR2C
namespace FinalCandidateR2C

variable {ψ κ τ : Nat}

/-- Executable mirror of the malformed-SWEEP Prop. -/
def finalMalformedActiveSweepB
    (l r : P ψ κ τ) : Bool :=
  decide (r.ctl.tok ≠ .seek) &&
    decide (l.ctl.tok = .sweep) &&
      !R2Coherence.successorB l r

/-- Executable mirror of the malformed-RELEASE Prop. -/
def finalMalformedActiveReleaseB
    (l r : P ψ κ τ) : Bool :=
  decide (r.ctl.tok ≠ .seek) &&
    decide (l.ctl.tok ≠ .sweep) &&
      decide (r.ctl.tok ≠ .commit) &&
        decide (l.ctl.tok = .release) &&
          !R2Coherence.successorB l r

/-- Executable mirror of the token-free MIXED Prop. -/
def finalTokenFreeMixedB
    (l r : P ψ κ τ) : Bool :=
  decide (l.ctl.tok = .none) &&
    decide (r.ctl.tok = .none) &&
      !decide (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) &&
        !decide (l.ctl.mark = .open ∧ r.ctl.mark = .open)

/-- Named sister-family sublane: both endpoints are exactly closing/none. -/
def finalTokenFreeUniformClosing
    (l r : P ψ κ τ) : Prop :=
  l.ctl.mark = .closing ∧ l.ctl.tok = .none ∧
    r.ctl.mark = .closing ∧ r.ctl.tok = .none

/-- Executable mirror of the uniform-closing sublane. -/
def finalTokenFreeUniformClosingB
    (l r : P ψ κ τ) : Bool :=
  decide (l.ctl.mark = .closing) &&
    decide (l.ctl.tok = .none) &&
      decide (r.ctl.mark = .closing) &&
        decide (r.ctl.tok = .none)

private theorem or_not_iff_imp_not
    {A B : Prop} [Decidable A] :
    (¬ A ∨ ¬ B) ↔ (A → ¬ B) := by
  constructor
  · intro h hA
    rcases h with hNA | hNB
    · exact (hNA hA).elim
    · exact hNB
  · intro h
    rcases Decidable.em A with hA | hNA
    · exact Or.inr (h hA)
    · exact Or.inl hNA

@[simp] theorem finalMalformedActiveSweepB_true_iff
    (l r : P ψ κ τ) :
    finalMalformedActiveSweepB l r = true ↔
      finalMalformedActiveSweep l r := by
  simp [finalMalformedActiveSweepB, finalMalformedActiveSweep, and_assoc]

@[simp] theorem finalMalformedActiveReleaseB_true_iff
    (l r : P ψ κ τ) :
    finalMalformedActiveReleaseB l r = true ↔
      finalMalformedActiveRelease l r := by
  simp [finalMalformedActiveReleaseB, finalMalformedActiveRelease, and_assoc]

@[simp] theorem finalTokenFreeMixedB_true_iff
    (l r : P ψ κ τ) :
    finalTokenFreeMixedB l r = true ↔
      finalTokenFreeMixed l r := by
  simp [finalTokenFreeMixedB, finalTokenFreeMixed, and_assoc, not_and,
    or_not_iff_imp_not]

@[simp] theorem finalTokenFreeUniformClosingB_true_iff
    (l r : P ψ κ τ) :
    finalTokenFreeUniformClosingB l r = true ↔
      finalTokenFreeUniformClosing l r := by
  simp [finalTokenFreeUniformClosingB, finalTokenFreeUniformClosing, and_assoc]

/-- Uniform closing/none is already inside the existing MIXED lane. -/
theorem finalTokenFreeUniformClosing_mixed
    (l r : P ψ κ τ)
    (h : finalTokenFreeUniformClosing l r) :
    finalTokenFreeMixed l r := by
  rcases h with ⟨hlm, hlt, hrm, hrt⟩
  refine ⟨hlt, hrt, ?_, ?_⟩
  · intro hs
    have hc : R2Coherence.Mark.closing = R2Coherence.Mark.sealed := by
      calc
        R2Coherence.Mark.closing = l.ctl.mark := hlm.symm
        _ = R2Coherence.Mark.sealed := hs.1
    cases hc
  · intro ho
    have hc : R2Coherence.Mark.closing = R2Coherence.Mark.open := by
      calc
        R2Coherence.Mark.closing = l.ctl.mark := hlm.symm
        _ = R2Coherence.Mark.open := ho.1
    cases hc

/--
Postprocess exactly the three broad lanes.  The third, MIXED, already
contains the uniform closing/none trap and sends it to `(l, startClosing r)`.
-/
def normalizeNonRecoveryOutput
    (l r : Cell ψ κ τ)
    (q : Cell ψ κ τ × Cell ψ κ τ) :
    Cell ψ κ τ × Cell ψ κ τ :=
  if finalMalformedActiveSweepB l.phys r.phys = true then
    (B9FullCarrierHost.CellP.setPhysical q.1
        (R2Coherence.startClosing l.phys),
     B9FullCarrierHost.CellP.setPhysical q.2 r.phys)
  else if finalMalformedActiveReleaseB l.phys r.phys = true then
    (B9FullCarrierHost.CellP.setPhysical q.1
        (R2Coherence.startClosing l.phys),
     B9FullCarrierHost.CellP.setPhysical q.2 r.phys)
  else if finalTokenFreeMixedB l.phys r.phys = true then
    (B9FullCarrierHost.CellP.setPhysical q.1 l.phys,
     B9FullCarrierHost.CellP.setPhysical q.2
        (R2Coherence.startClosing r.phys))
  else
    q

/-- Recovery remains exactly the accepted row; only non-recovery is normalized. -/
noncomputable def rowFinalNormalized
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ := by
  classical
  exact if FinalGarbage hψ l r then
    rowFinal hψ h2 port l r
  else
    normalizeNonRecoveryOutput l r (rowFinal hψ h2 port l r)

/-- Recovery is byte-for-byte the accepted old final-row recovery result. -/
theorem rowFinalNormalized_recovery_of_garbage
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hg : FinalGarbage hψ l r) :
    rowFinalNormalized hψ h2 port l r = recoverPair hψ l r := by
  classical
  rw [rowFinalNormalized]
  rw [if_pos hg]
  exact rowFinal_recovery_of_garbage hψ h2 port l r hg

private theorem sweepB_false_of_not_sweep
    (l r : P ψ κ τ)
    (h : ¬ finalMalformedActiveSweep l r) :
    finalMalformedActiveSweepB l r = false := by
  cases hb : finalMalformedActiveSweepB l r with
  | false => rfl
  | true =>
      exact (h ((finalMalformedActiveSweepB_true_iff l r).1 hb)).elim

private theorem releaseB_false_of_not_release
    (l r : P ψ κ τ)
    (h : ¬ finalMalformedActiveRelease l r) :
    finalMalformedActiveReleaseB l r = false := by
  cases hb : finalMalformedActiveReleaseB l r with
  | false => rfl
  | true =>
      exact (h ((finalMalformedActiveReleaseB_true_iff l r).1 hb)).elim

private theorem mixedB_false_of_not_mixed
    (l r : P ψ κ τ)
    (h : ¬ finalTokenFreeMixed l r) :
    finalTokenFreeMixedB l r = false := by
  cases hb : finalTokenFreeMixedB l r with
  | false => rfl
  | true =>
      exact (h ((finalTokenFreeMixedB_true_iff l r).1 hb)).elim

/-- Away from all three broad repair predicates, shadow row equals old row. -/
theorem rowFinalNormalized_eq_rowFinal_of_no_normalization
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hg : ¬ FinalGarbage hψ l r)
    (hs : ¬ finalMalformedActiveSweep l.phys r.phys)
    (hr : ¬ finalMalformedActiveRelease l.phys r.phys)
    (hm : ¬ finalTokenFreeMixed l.phys r.phys) :
    rowFinalNormalized hψ h2 port l r = rowFinal hψ h2 port l r := by
  classical
  have hsB := sweepB_false_of_not_sweep l.phys r.phys hs
  have hrB := releaseB_false_of_not_release l.phys r.phys hr
  have hmB := mixedB_false_of_not_mixed l.phys r.phys hm
  simp [rowFinalNormalized, normalizeNonRecoveryOutput, hg, hsB, hrB, hmB]

private theorem malformedRelease_not_malformedSweep
    (l r : P ψ κ τ)
    (h : finalMalformedActiveRelease l r) :
    ¬ finalMalformedActiveSweep l r := by
  intro hs
  unfold finalMalformedActiveRelease at h
  unfold finalMalformedActiveSweep at hs
  rcases h with ⟨_, hNotSweep, _, _, _⟩
  exact hNotSweep hs.2.1

private theorem tokenFreeMixed_not_malformedSweep
    (l r : P ψ κ τ)
    (h : finalTokenFreeMixed l r) :
    ¬ finalMalformedActiveSweep l r := by
  intro hs
  unfold finalTokenFreeMixed at h
  unfold finalMalformedActiveSweep at hs
  rcases h with ⟨hlNone, _, _, _⟩
  have ht : l.ctl.tok = .sweep := hs.2.1
  rw [hlNone] at ht
  cases ht

private theorem tokenFreeMixed_not_malformedRelease
    (l r : P ψ κ τ)
    (h : finalTokenFreeMixed l r) :
    ¬ finalMalformedActiveRelease l r := by
  intro hr
  unfold finalTokenFreeMixed at h
  unfold finalMalformedActiveRelease at hr
  rcases h with ⟨hlNone, _, _, _⟩
  rcases hr with ⟨_, _, _, hRelease, _⟩
  rw [hlNone] at hRelease
  cases hRelease

/-- The contract factored over an arbitrary final-row producer. -/
def NonRecoveryNormalizationContractFor
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (_port : Port (κ := κ) (τ := τ) hψ h2)
    (row : Cell ψ κ τ → Cell ψ κ τ →
      Cell ψ κ τ × Cell ψ κ τ) : Prop :=
  ∀ l r : Cell ψ κ τ,
    ¬ FinalGarbage hψ l r →
      (finalMalformedActiveSweep l.phys r.phys →
        let q := row l r
        q.1.phys = R2Coherence.startClosing l.phys ∧
          q.2.phys = r.phys) ∧
      (finalMalformedActiveRelease l.phys r.phys →
        let q := row l r
        q.1.phys = R2Coherence.startClosing l.phys ∧
          q.2.phys = r.phys) ∧
      (finalTokenFreeMixed l.phys r.phys →
        let q := row l r
        q.1.phys = l.phys ∧
          q.2.phys = R2Coherence.startClosing r.phys)

/-- The installed residual is exactly the old-row instance. -/
theorem rowFinal_nonRecovery_normalization_contract_is_old_instance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2) :
    rowFinal_nonRecovery_normalization_contract hψ h2 port ↔
      NonRecoveryNormalizationContractFor hψ h2 port
        (rowFinal hψ h2 port) := by
  rfl

/-- The shadow producer fully discharges the original contract. -/
theorem rowFinalNormalized_nonRecovery_normalization_contract
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2) :
    NonRecoveryNormalizationContractFor hψ h2 port
      (rowFinalNormalized hψ h2 port) := by
  intro l r hg
  constructor
  · intro hs
    classical
    have hsB : finalMalformedActiveSweepB l.phys r.phys = true :=
      (finalMalformedActiveSweepB_true_iff l.phys r.phys).2 hs
    simp [rowFinalNormalized, normalizeNonRecoveryOutput, hg, hsB]
  constructor
  · intro hr
    classical
    have hns := malformedRelease_not_malformedSweep l.phys r.phys hr
    have hsB := sweepB_false_of_not_sweep l.phys r.phys hns
    have hrB : finalMalformedActiveReleaseB l.phys r.phys = true :=
      (finalMalformedActiveReleaseB_true_iff l.phys r.phys).2 hr
    simp [rowFinalNormalized, normalizeNonRecoveryOutput, hg, hsB, hrB]
  · intro hm
    classical
    have hns := tokenFreeMixed_not_malformedSweep l.phys r.phys hm
    have hnr := tokenFreeMixed_not_malformedRelease l.phys r.phys hm
    have hsB := sweepB_false_of_not_sweep l.phys r.phys hns
    have hrB := releaseB_false_of_not_release l.phys r.phys hnr
    have hmB : finalTokenFreeMixedB l.phys r.phys = true :=
      (finalTokenFreeMixedB_true_iff l.phys r.phys).2 hm
    simp [rowFinalNormalized, normalizeNonRecoveryOutput, hg, hsB, hrB, hmB]

/-- Specialized contractual clause naming the sister fixed family. -/
def UniformClosingNormalizationContractFor
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (_port : Port (κ := κ) (τ := τ) hψ h2)
    (row : Cell ψ κ τ → Cell ψ κ τ →
      Cell ψ κ τ × Cell ψ κ τ) : Prop :=
  ∀ l r : Cell ψ κ τ,
    ¬ FinalGarbage hψ l r →
    finalTokenFreeUniformClosing l.phys r.phys →
      let q := row l r
      q.1.phys = l.phys ∧
        q.2.phys = R2Coherence.startClosing r.phys

/-- Explicit extension: original contract plus the named uniform-closing case. -/
def NonRecoveryNormalizationContractForWithUniformClosing
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (row : Cell ψ κ τ → Cell ψ κ τ →
      Cell ψ κ τ × Cell ψ κ τ) : Prop :=
  NonRecoveryNormalizationContractFor hψ h2 port row ∧
    UniformClosingNormalizationContractFor hψ h2 port row

/-- Uniform closing is discharged by the already-proved MIXED clause. -/
theorem rowFinalNormalized_uniformClosing_normalization_contract
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2) :
    UniformClosingNormalizationContractFor hψ h2 port
      (rowFinalNormalized hψ h2 port) := by
  intro l r hg hc
  have hm := finalTokenFreeUniformClosing_mixed l.phys r.phys hc
  have hbase :=
    rowFinalNormalized_nonRecovery_normalization_contract hψ h2 port
  exact (hbase l r hg).2.2 hm

/-- The normalized producer discharges the explicit extended contract. -/
theorem rowFinalNormalized_nonRecovery_normalization_contract_with_uniformClosing
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2) :
    NonRecoveryNormalizationContractForWithUniformClosing hψ h2 port
      (rowFinalNormalized hψ h2 port) := by
  exact ⟨rowFinalNormalized_nonRecovery_normalization_contract hψ h2 port,
    rowFinalNormalized_uniformClosing_normalization_contract hψ h2 port⟩

/-- A non-garbage closing/none pair cannot be a fixed point of the normalized row. -/
theorem rowFinalNormalized_uniformClosing_not_identity
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hg : ¬ FinalGarbage hψ l r)
    (hc : finalTokenFreeUniformClosing l.phys r.phys) :
    rowFinalNormalized hψ h2 port l r ≠ (l, r) := by
  intro heq
  have hout :=
    rowFinalNormalized_uniformClosing_normalization_contract
      hψ h2 port l r hg hc
  have hright :
      (rowFinalNormalized hψ h2 port l r).2.phys = r.phys :=
    congrArg (fun q : Cell ψ κ τ × Cell ψ κ τ => q.2.phys) heq
  have hstart : R2Coherence.startClosing r.phys = r.phys :=
    hout.2.symm.trans hright
  have ht := congrArg (fun u : P ψ κ τ => u.ctl.tok) hstart
  rcases hc with ⟨_, _, _, hrt⟩
  have hbad : R2Coherence.Token.seek = R2Coherence.Token.none := by
    simpa [R2Coherence.startClosing, R2Coherence.setControl, hrt] using ht
  cases hbad

end FinalCandidateR2C
end FinalCandidateR2C
