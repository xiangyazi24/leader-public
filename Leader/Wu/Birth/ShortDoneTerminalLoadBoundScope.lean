import Leader.Wu.Birth.ShortDoneTerminalLoadBound

namespace BirthShortDoneTerminalLoadBoundScopeAudit

open PPLL PPLLResearchFormulation
open PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneParticipationLoadBound
open BirthShortDoneFixedSiteConsumer
open BirthShortDoneTerminalFixedSite
open BirthShortDoneTerminalLoadBound
open FixedSpanRenewalPayload FiniteUniformStoppingTree

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ width κ τ T Q : Nat}

private def ring8 : DirectedRing 8 := ⟨by decide⟩

private def zeroTimer {ψ κ τ : Nat} (u : Local ψ κ τ) : Local ψ κ τ :=
  ⟨u.core, ⟨0, by omega⟩⟩

/-- Exactly one selected site is fresh; every other physical timer is zero. -/
def mixed8one (i : Fin 8) : Local 2 2 2 :=
  let u := BirthCheckParametricWait.familyInitial 2 false false i
  if i = (0 : Fin 8) then u else zeroTimer u

theorem mixed8one_frame :
    (mixed8one (0 : Fin 8)).stall.val = 2 ∧
      ∀ j : Fin 8, j ≠ 0 → (mixed8one j).stall.val = 0 := by
  constructor
  · simp [mixed8one, BirthCheckParametricWait.familyInitial, freshStall]
  · intro j hj
    simp [mixed8one, zeroTimer, hj]

/-- Exactly the two listed sites are fresh; all six unlisted timers are zero. -/
def mixed8two (i : Fin 8) : Local 2 2 2 :=
  let u := BirthCheckParametricWait.familyInitial 2 false false i
  if i = (0 : Fin 8) ∨ i = (1 : Fin 8) then u else zeroTimer u

theorem mixed8two_frame :
    (mixed8two (0 : Fin 8)).stall.val = 2 ∧
      (mixed8two (1 : Fin 8)).stall.val = 2 ∧
      ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → (mixed8two j).stall.val = 0 := by
  constructor
  · simp [mixed8two, BirthCheckParametricWait.familyInitial, freshStall]
  constructor
  · simp [mixed8two, BirthCheckParametricWait.familyInitial, freshStall]
  · intro j h0 h1
    simp [mixed8two, zeroTimer, h0, h1]

/-- `hscale` is not by itself a nonvacuity certificate: above the horizon the
source binomial coefficient is literally zero. -/
theorem hscale_can_have_zero_factor (Q n : Nat) :
    Q * (chooseCount 2 3 * 2 ^ 3) ≤ n ^ 3 := by
  simp [chooseCount]

/-- In that above-horizon case the terminal bad-event mass is also zero; the
vacuous arithmetic premise therefore hides no positive probability claim. -/
theorem terminal_mass_zero_above_horizon
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (i : Fin n) (T : Nat)
    (hT : T < τ + 1) (hfresh : (C i).stall.val = τ) :
    terminalZeroServiceNumerator hψ hwidth hle ring C i T = 0 := by
  have hb := terminalZeroServiceNumerator_le_overload
    (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh
  have ho := fixed_node_overload_bound hn2 ring i T (τ + 1)
  have hz := factorialMomentCap_zero_of_lt n T (τ + 1) hT
  rw [hz] at ho
  omega

/-- The witness below is genuinely on-horizon: the factorial weight is eight,
not zero. -/
theorem order3_factor_exact : chooseCount 3 3 * 2 ^ 3 = 8 := by
  decide

/-- `wordSum` has the original uniform denominator: here there are exactly
`8^3 = 512` raw scheduler words, each with multiplicity one. -/
theorem terminal_raw_denominator_8_3 :
    wordSum 8 3 (fun _ : List (Fin 8) => 1) = 512 := by
  calc
    wordSum 8 3 (fun _ : List (Fin 8) => 1) = 8 ^ 3 := all_raw_words 8 3
    _ = 512 := by decide

/-- Nontrivial fixed-site witness: Q=2, T=3, tau=2.  Site zero is fresh and
all seven other timers are zero.  The scale is `2*8 <= 512`, so this is not
the above-horizon zero-factor case. -/
theorem terminal_fixed_Q2_dirty_others :
    (∀ j : Fin 8, j ≠ 0 → (mixed8one j).stall.val = 0) ∧
      2 * terminalZeroServiceNumerator
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8one (0 : Fin 8) 3 ≤ 8 ^ 3 := by
  constructor
  · exact mixed8one_frame.2
  · have hf : (mixed8one (0 : Fin 8)).stall.val = 2 := mixed8one_frame.1
    have hs : 2 * (chooseCount 3 3 * 2 ^ 3) ≤ 8 ^ 3 := by
      rw [order3_factor_exact]
      decide
    exact terminal_fixed_site_exposure_crossmul
      (n := 8) (ψ := 2) (width := 1) (κ := 2) (τ := 2)
      (by decide) (by decide) (by decide) (by decide)
      ring8 mixed8one (0 : Fin 8) 3 2 hf hs

/-- Nontrivial two-site listed witness with Q=2.  Only sites 0 and 1 are fresh;
all unlisted timers are zero.  The union charge is multiplicity-based, so the
arithmetic factor is the literal list length two: `2*2*8 <= 512`. -/
theorem terminal_list_Q2_dirty_unlisted :
    (∀ j : Fin 8, j ≠ 0 → j ≠ 1 → (mixed8two j).stall.val = 0) ∧
      2 * listedTerminalZeroServiceMass
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8two [(0 : Fin 8), (1 : Fin 8)] 3 ≤ 8 ^ 3 := by
  constructor
  · exact mixed8two_frame.2.2
  · have hf : ∀ i,
        i ∈ ([(0 : Fin 8), (1 : Fin 8)] : List (Fin 8)) →
          (mixed8two i).stall.val = 2 := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst i
        exact mixed8two_frame.1
      · subst i
        exact mixed8two_frame.2.1
    have hs :
        2 * ([(0 : Fin 8), (1 : Fin 8)] : List (Fin 8)).length *
            (chooseCount 3 3 * 2 ^ 3) ≤ 8 ^ 3 := by
      rw [order3_factor_exact]
      decide
    exact listed_terminal_exposure_crossmul
      (n := 8) (ψ := 2) (width := 1) (κ := 2) (τ := 2)
      (by decide) (by decide) (by decide) (by decide)
      ring8 mixed8two [(0 : Fin 8), (1 : Fin 8)] 3 2 hf hs

/-- Tau zero means the selected input timer is literally zero.  This theorem
asserts only the zero-input-service event, before the row runs; it makes no
claim that expiry occurs or that the output timer remains zero. -/
theorem terminal_tau0_selected_first_service
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ 0) (i : Fin n) :
    fixedSiteZeroServiceBit ring
      (BirthShortDoneTerminalHost.row hψ hwidth hle) i C [i] = 1 := by
  have hz : (C i).stall.val = 0 := by
    have hlt := (C i).stall.isLt
    omega
  simpa only [fixedSiteZeroServiceBit, if_pos rfl, if_pos hz, if_true]

/-- Tau-zero can still have a genuinely nontrivial Q=2 fixed-site exposure
bound: at n=8,T=1 the scale is `2*(1*2) <= 8`. -/
theorem terminal_tau0_Q2_bound
    (C : Fin 8 → Local 2 2 0) (i : Fin 8) :
    2 * terminalZeroServiceNumerator
      (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
      ring8 C i 1 ≤ 8 := by
  have hs : 2 * (chooseCount 1 1 * 2) ≤ 8 := by decide
  have h := terminal_tau_zero_exposure_crossmul
    (n := 8) (ψ := 2) (width := 1) (κ := 2)
    (by decide) (by decide) (by decide) (by decide)
    ring8 C i 1 2 hs
  simpa using h

/-- The n=1 alias boundary has denominator one.  If the overload is genuinely
possible (`tau<T`), any Q>1 scale premise is impossible; hence the ring-one
crossmul theorem is an exact boundary statement, not a nontrivial fractional
tail estimate. -/
theorem ring1_Qgt1_scale_impossible {τ T Q : Nat}
    (hQ : 1 < Q) (hT : τ < T) :
    ¬ Q * (if τ < T then 1 else 0) ≤ 1 ^ T := by
  have hnot : ¬ Q ≤ 1 := Nat.not_le.mpr hQ
  simpa [hT] using hnot

#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.terminal_mass_zero_above_horizon
#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.terminal_raw_denominator_8_3
#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.terminal_fixed_Q2_dirty_others
#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.terminal_list_Q2_dirty_unlisted
#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.terminal_tau0_selected_first_service
#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.terminal_tau0_Q2_bound
#print axioms BirthShortDoneTerminalLoadBoundScopeAudit.ring1_Qgt1_scale_impossible

end BirthShortDoneTerminalLoadBoundScopeAudit
