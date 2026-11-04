import Leader.Wu.Elimination.SinkTwoGapRestartClosure


open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
open LDSinkGapCleanupBound LDTwoGapFrame
open LDSinkTwoGapEpochKernel LDSinkTwoGapEpochSuccessor
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant LDSinkTwoGapRestartClosure


namespace LDSinkTwoGapRestartDischarge


set_option autoImplicit false


noncomputable section


variable {n ψ : Nat}


/-- Any concrete witness satisfying the premises of the broadened boundary
field but violating its conclusion refutes that residual outright. -/
theorem restart_signal_residual_false_of_witness
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (G : GapFrame n)
    (hG : G = F.recovery ∨ G = F.attack)
    (hx : GapPair hψ F x)
    (hcase : ¬ AInvariant hψ F x ∨
      attemptStepRaw hψ F x e = .failure)
    (hs : ¬ NoResetSuccess F (attemptStepConf hψ F x e))
    (hc0 : CleanReady G x.conf)
    (hc1 : ¬ CleanReady G (attemptStepConf hψ F x e))
    (hbad : ¬ GapSignalBelowBullets G
      (attemptStepConf hψ F x e)) :
    ¬ RestartCleanBoundarySignalResidual hψ F := by
  intro hB
  exact hbad (hB.signal x e G hG hx hcase hs hc0 hc1)


/-- If all `m` raw-rank children are at most `r` and one is strictly below
`r`, their finite-uniform sum leaves one unit of Bellman slack. -/
theorem sum_slack_restart {m r : Nat} (f : Fin m → Nat)
    (hle : ∀ e, f e ≤ r) (hlt : ∃ e, f e < r) :
    1 + (List.ofFn f).sum ≤ m * r := by
  induction m with
  | zero =>
      rcases hlt with ⟨e, _⟩
      exact Fin.elim0 e
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      rcases hlt with ⟨e, he⟩
      cases e using Fin.cases with
      | zero =>
          have htail :
              (List.ofFn (fun i : Fin m => f i.succ)).sum ≤ m * r := by
            calc
              (List.ofFn (fun i : Fin m => f i.succ)).sum ≤
                  (List.ofFn (fun _ : Fin m => r)).sum := by
                    apply ofFn_sum_le
                    intro i
                    exact hle i.succ
              _ = m * r := FiniteUniformStoppingTree.ofFn_sum_const m r
          have hhead : f 0 + 1 ≤ r := by omega
          omega
      | succ i =>
          have htail :
              1 + (List.ofFn (fun j : Fin m => f j.succ)).sum ≤
                m * r :=
            ih (fun j : Fin m => f j.succ)
              (fun j => hle j.succ) ⟨i, he⟩
          have hhead : f 0 ≤ r := hle 0
          omega


/-- Generic conversion from raw rank laws to the scheduler-scaled entrance
Bellman inequality. -/
theorem entrance_bellman_of_rank_laws_restart
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hle : ∀ e : Fin n,
      rawStoppedR F (entranceStep hψ F x e) ≤ R F x)
    (hlt : ∃ e : Fin n,
      rawStoppedR F (entranceStep hψ F x e) < R F x) :
    n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hψ F x e))).sum ≤
        n * entrancePotential F (.active x) := by
  let f : Fin n → Nat :=
    fun e => rawStoppedR F (entranceStep hψ F x e)
  have hraw : 1 + (List.ofFn f).sum ≤ n * R F x :=
    sum_slack_restart f (fun e => hle e) (by
      obtain ⟨e, he⟩ := hlt
      exact ⟨e, he⟩)
  have hp : ∀ z : StopNode (AState n ψ),
      entrancePotential F z = n * rawStoppedR F z := by
    intro z
    cases z <;> rfl
  have hsum :
      (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum =
        n * (List.ofFn f).sum := by
    calc
      (List.ofFn (fun e : Fin n =>
          entrancePotential F (entranceStep hψ F x e))).sum =
          (List.ofFn (fun e : Fin n => n * f e)).sum :=
        ofFn_sum_eq _ _ (fun e => hp (entranceStep hψ F x e))
      _ = n * (List.ofFn f).sum := ofFn_sum_mul_left n f
  calc
    n + (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum =
        n * (1 + (List.ofFn f).sum) := by
      rw [hsum, Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * R F x) := Nat.mul_le_mul_left n hraw
    _ = n * entrancePotential F (.active x) := rfl


/-- On a physical two-gap state whose attack gap has not reached `GapDoneC`,
the one-gap C5 law gives pointwise nonincrease without using the tag. -/
theorem entrance_nonincrease_of_gapPair_not_done
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hx : GapPair hψ F x)
    (hn : ¬ GapDoneC F.attack x.conf) (e : Fin n) :
    rawStoppedR F (entranceStep hψ F x e) ≤ R F x := by
  classical
  have hw : W F (attemptStepConf hψ F x e) ≤ W F x.conf := by
    unfold W
    rw [attemptStepConf_eq_sinkStepC]
    exact LDSinkGapCleanupBound.gapWC_step_le'
      hψ F.attack x.conf hx.attack hn e
  have hr := R_advance_le F x (attemptStepConf hψ F x e) hw
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · rw [entrance_normal_form, if_pos hE]
    exact Nat.zero_le _
  · rw [entrance_normal_form, if_neg hE]
    change R F (advanceAState F x (attemptStepConf hψ F x e)) ≤ R F x
    exact hr


/-- On the same non-done subdomain, the unconditional one-gap strict C5 edge
lifts to a strict raw entrance edge. -/
theorem entrance_strictDrop_of_gapPair_not_done
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hx : GapPair hψ F x)
    (hn : ¬ GapDoneC F.attack x.conf) :
    ∃ e : Fin n,
      rawStoppedR F (entranceStep hψ F x e) < R F x := by
  classical
  obtain ⟨e, he⟩ := LDSinkGapCleanupBound.exists_gapWC_step_lt'
    hψ F.attack x.conf hx.attack hn
  have hw : W F (attemptStepConf hψ F x e) < W F x.conf := by
    unfold W
    rw [attemptStepConf_eq_sinkStepC]
    exact he
  have hr := R_advance_lt F x (attemptStepConf hψ F x e) hw
  refine ⟨e, ?_⟩
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · rw [entrance_normal_form, if_pos hE]
    exact R_pos F x
  · rw [entrance_normal_form, if_neg hE]
    change R F (advanceAState F x (attemptStepConf hψ F x e)) < R F x
    exact hr


/-- W-a is valid exactly on the C5 active domain. The tag object is not used;
its old `not_done` field was only a source of this premise. -/
theorem entrance_bellman_of_gapPair_not_done
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hx : GapPair hψ F x)
    (hn : ¬ GapDoneC F.attack x.conf) :
    n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hψ F x e))).sum ≤
        n * entrancePotential F (.active x) := by
  exact entrance_bellman_of_rank_laws_restart hψ F x
    (entrance_nonincrease_of_gapPair_not_done hψ F x hx hn)
    (entrance_strictDrop_of_gapPair_not_done hψ F x hx hn)


/-- Generic arithmetic obstruction to the original all-`GapPair` Bellman
field. If the current rank is one and every entrance child stays active, the
positive running cost cannot be paid. -/
theorem entrance_bellman_fails_of_unit_rank_all_active
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hR : R F x = 1)
    (hactive : ∀ e : Fin n,
      ∃ y : AState n ψ, entranceStep hψ F x e = .active y) :
    ¬ (n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hψ F x e))).sum ≤
        n * entrancePotential F (.active x)) := by
  intro hbell
  have hn : 0 < n := by
    have hp := (F.attack.pos 0).isLt
    omega
  have hchild : ∀ e : Fin n,
      n ≤ entrancePotential F (entranceStep hψ F x e) := by
    intro e
    obtain ⟨y, hy⟩ := hactive e
    rw [hy]
    change n ≤ n * R F y
    have hry := R_pos F y
    have hone : 1 ≤ R F y := by omega
    have hm := Nat.mul_le_mul_left n hone
    simpa only [Nat.mul_one] using hm
  have hsum :
      n * n ≤ (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum := by
    have hs := ofFn_sum_le
      (fun _ : Fin n => n)
      (fun e : Fin n => entrancePotential F (entranceStep hψ F x e))
      hchild
    rw [FiniteUniformStoppingTree.ofFn_sum_const] at hs
    exact hs
  have hcurrent : entrancePotential F (.active x) = n := by
    change n * R F x = n
    rw [hR, Nat.mul_one]
  rw [hcurrent] at hbell
  omega


/-- The unit-rank/all-active pattern above is enough to refute the original
residual whenever it occurs at a `GapPair` state outside `AInvariant`. -/
theorem restart_entrance_bellman_residual_false_of_witness
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hx : GapPair hψ F x) (hout : ¬ AInvariant hψ F x)
    (hR : R F x = 1)
    (hactive : ∀ e : Fin n,
      ∃ y : AState n ψ, entranceStep hψ F x e = .active y) :
    ¬ RestartEntranceBellmanResidual hψ F := by
  intro hB
  exact entrance_bellman_fails_of_unit_rank_all_active
    hψ F x hR hactive (hB.bellman x hx hout)


/-- One-field quantitative replacement for the false seeking-state Bellman
claim. A witness is a corrected global entrance potential with a uniform
`GapPair` start bound. Its seeking part must prepay rearm/FIRE; the proved
non-done and tracking laws may be reused in constructing it. -/
structure RestartSeekingPotentialResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) (B : Nat) : Prop where
  witness :
    ∃ V : StopNode (AState n ψ) → Nat,
      NatBellmanSuperSolution (entranceStep hψ F) 1 V ∧
      ∀ x : AState n ψ, GapPair hψ F x → V (.active x) ≤ B


/--
Strongest statewise conclusion supported by the current rank plus one corrected
seeking-potential witness.


* The fixed-frame numerical rank bound still needs only `GapPair`.
* On `¬ GapDoneC F.attack x.conf`, the existing `entrancePotential` satisfies
  Bellman with no tag premise.
* `RestartSeekingPotentialResidual hψ F B` supplies a corrected global Bellman
  potential covering the done/seeking states.


The `hB` argument is retained for compatibility with the compiled restart
closure, but Task 1 shows that its broadened all-`GapPair` field is not
instantiable without strengthening the seed/domain by clean-FIRE signal-tail
coherence.


Exact remaining distance to state-uniform `1/32` block mass: prove that
structural coherence on the corrected physical restart domain, and construct
the witness below with
`B = 16 * n * (F.recovery.d + F.attack.d)`.
Then the half-mass entrance horizon remains `2*B = 32*n*(a+b)`, and the
existing serial tail gives the unchanged total horizon
`32*n*(a+b) + 4*n`. For a larger proved bound `B`, the corresponding total
horizon is `2*B + 4*n`.
-/
theorem restart_uniform_bellman
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (_hB : RestartCleanBoundarySignalResidual hψ F)
    (B : Nat) (hQ : RestartSeekingPotentialResidual hψ F B)
    (x : AState n ψ) (hx : GapPair hψ F x) :
    R F x ≤ 16 * (F.recovery.d + F.attack.d) ∧
    (¬ GapDoneC F.attack x.conf →
      n + (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum ≤
          n * entrancePotential F (.active x)) ∧
    ∃ V : StopNode (AState n ψ) → Nat,
      NatBellmanSuperSolution (entranceStep hψ F) 1 V ∧
      V (.active x) ≤ B := by
  have hr := R_le hψ F x hx.recovery hx.attack
  refine ⟨hr, ?_, ?_⟩
  · intro hn
    exact entrance_bellman_of_gapPair_not_done hψ F x hx hn
  · obtain ⟨V, hV, hbound⟩ := hQ.witness
    exact ⟨V, hV, hbound x hx⟩


#print axioms restart_signal_residual_false_of_witness
#print axioms sum_slack_restart
#print axioms entrance_bellman_of_rank_laws_restart
#print axioms entrance_nonincrease_of_gapPair_not_done
#print axioms entrance_strictDrop_of_gapPair_not_done
#print axioms entrance_bellman_of_gapPair_not_done
#print axioms entrance_bellman_fails_of_unit_rank_all_active
#print axioms restart_entrance_bellman_residual_false_of_witness
#print axioms restart_uniform_bellman


end


end LDSinkTwoGapRestartDischarge
