import Leader.Wu.RaceEntrance.FreshService

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant
open LDSinkGapServiceRank LDSinkGapCleanupBound LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceLocalService LDSinkTwoGapRaceEntranceFreshService

namespace LDSinkTwoGapRaceEntranceBirthBudget

variable {n psi : Nat}

/-!
The physical fresh-shot stopping target admits a real renewal budget.
Work is `2*d+1+gapWC`, where `d` is the attack length.  Away from clean
states, C5 supplies service.  At a clean state, outgoing FIRE succeeds,
incoming FIRE raises the cleanup rank by at most `2*d`, and neutral edges
keep that rank zero.  The two competing FIRE rows pay the new-shot cost
in their exact finite sum.  No nonrenewable reset pool is assumed.

The target is fresh-shot birth or physical deletion, not `RaceReady`.
The closed carrier stores only the already-proved physical gap invariant;
its transition erases exactly to the raw `freshStep` on every scheduler edge.
-/

abbrev BirthState (hpsi : psi > 0) (F : TwoGapFrame n) :=
  { b : AState n psi // GapPair hpsi F b }

private theorem gapPair_after_not_fresh (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n)
    (hn : ¬ FreshOrDeleted hpsi F (attemptStepConf hpsi F z.val e)) :
    GapPair hpsi F (postState hpsi F z.val e) := by
  classical
  apply LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    z.val e (postState hpsi F z.val e) z.property
  rw [physicalBlockStep_normal_form, if_neg (fun h => hn (.inr h))]

noncomputable def birthStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) : StopNode (BirthState hpsi F) := by
  classical
  exact if h : FreshOrDeleted hpsi F (attemptStepConf hpsi F z.val e) then .success
    else .active ⟨postState hpsi F z.val e, gapPair_after_not_fresh hpsi F z e h⟩

def eraseBirth (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (BirthState hpsi F) → StopNode (AState n psi)
  | .active z => .active z.val
  | .success => .success
  | .failure => .failure

theorem birthStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) (e : Fin n) :
    eraseBirth hpsi F (stepNode (birthStep hpsi F) x e) =
      stepNode (freshStep hpsi F) (eraseBirth hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      by_cases hs : FreshOrDeleted hpsi F (attemptStepConf hpsi F z.val e) <;>
        simp [stepNode, birthStep, freshStep, hs, eraseBirth]

private theorem treeWeight_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (AState n psi) → Nat)
    (x : StopNode (BirthState hpsi F)) (T : Nat) :
    treeWeight (birthStep hpsi F) (fun y => w (eraseBirth hpsi F y)) x T =
      treeWeight (freshStep hpsi F) w (eraseBirth hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, birthStep_erases]

theorem successCount_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) (T : Nat) :
    successCount (birthStep hpsi F) x T =
      successCount (freshStep hpsi F) (eraseBirth hpsi F x) T := by
  have hw : (fun y => successWeight (eraseBirth hpsi F y)) = successWeight := by
    funext y
    cases y <;> rfl
  simpa only [successCount, hw] using treeWeight_erases hpsi F successWeight x T

def birthBase (F : TwoGapFrame n) : Nat := 2 * F.attack.d + 1

noncomputable def birthWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (BirthState hpsi F) → Nat
  | .active z => birthBase F + gapWC F.attack z.val.conf
  | .success => 0
  | .failure => 0

noncomputable def birthPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (BirthState hpsi F)) : Nat := n * birthWork hpsi F x

private theorem child_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) :
    birthWork hpsi F (birthStep hpsi F z e) ≤
      birthBase F + gapWC F.attack (attemptStepConf hpsi F z.val e) := by
  classical
  unfold birthStep
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

private theorem child_work_le_bound (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) :
    birthWork hpsi F (birthStep hpsi F z e) ≤ birthBase F + 2 * F.attack.d := by
  classical
  unfold birthStep
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hg := gapPair_after_not_fresh hpsi F z e hn
    exact Nat.add_le_add_left (gapWC_le_two_d hpsi F.attack _ hg.attack) _

private theorem outgoing_work_zero (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : CleanReady F.attack z.val.conf) :
    birthWork hpsi F (birthStep hpsi F z (outgoingPort F)) = 0 := by
  classical
  have hs : FreshOrDeleted hpsi F
      (attemptStepConf hpsi F z.val (outgoingPort F)) :=
    .inl (clean_outgoing_attemptEntrance hpsi F z.val z.property hc)
  simp [birthStep, hs, birthWork]

private theorem neutral_work_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : CleanReady F.attack z.val.conf) (e : Fin n)
    (ho : e ≠ outgoingPort F) (hi : e ≠ incomingPort F) :
    birthWork hpsi F (birthStep hpsi F z e) ≤ birthBase F := by
  classical
  unfold birthStep
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hclean := (clean_neutral hpsi F z.val z.property hc e ho hi
      (fun h => hn (.inr h))).2
    have hd : GapDoneC F.attack (attemptStepConf hpsi F z.val e) := .inl hclean
    change birthBase F + gapWC F.attack (attemptStepConf hpsi F z.val e) ≤ _
    simp [gapWC, hd]

private theorem sum_spike (n : Nat) : ∀ (a : Fin n) (v : Nat),
    (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero => intro a; exact a.elim0
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht : (List.ofFn (fun i : Fin n =>
            if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0) (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- The extra `2*d+1` pays the exact clean-to-dummy reset in average. -/
private theorem clean_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : CleanReady F.attack z.val.conf) :
    1 + (List.ofFn (fun e : Fin n => birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
  classical
  let f := fun e : Fin n => birthWork hpsi F (birthStep hpsi F z e)
  have hports : outgoingPort F ≠ incomingPort F := (firingPorts F).ab
  have hrow : ∀ e : Fin n,
      f e + (if e = outgoingPort F then birthBase F else 0) ≤
        birthBase F + (if e = incomingPort F then 2 * F.attack.d else 0) := by
    intro e
    by_cases ho : e = outgoingPort F
    · subst e
      simp [f, outgoing_work_zero hpsi F z hc, hports]
    · by_cases hi : e = incomingPort F
      · simpa [f, ho, hi, hports.symm] using child_work_le_bound hpsi F z (incomingPort F)
      · simpa [ho, hi, f] using neutral_work_le hpsi F z hc e ho hi
  have hsum := ofFn_sum_le _ _ hrow
  rw [ofFn_sum_add, ofFn_sum_add, sum_spike, sum_spike,
    FiniteUniformStoppingTree.ofFn_sum_const] at hsum
  have hzero : gapWC F.attack z.val.conf = 0 := by
    have hd : GapDoneC F.attack z.val.conf := .inl hc
    simp [gapWC, hd]
  change 1 + _ ≤ n * (birthBase F + gapWC F.attack z.val.conf)
  rw [hzero, Nat.add_zero]
  dsimp only [f, birthBase] at hsum ⊢
  omega

private theorem nonclean_work_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (hc : ¬ CleanReady F.attack z.val.conf) :
    1 + (List.ofFn (fun e : Fin n => birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
  have hn : ¬ GapDoneC F.attack z.val.conf := by
    rintro (hd | hl | hr)
    · exact hc hd
    · have he := z.property.attack.1.1
      rw [he] at hl
      cases hl
    · have he := z.property.attack.1.2
      rw [he] at hr
      cases hr
  have hmono : ∀ e : Fin n,
      birthWork hpsi F (birthStep hpsi F z e) ≤ birthWork hpsi F (.active z) := by
    intro e
    have h1 := child_work_le hpsi F z e
    have h2 := gapWC_step_le' hpsi F.attack z.val.conf z.property.attack hn e
    change _ ≤ birthBase F + gapWC F.attack z.val.conf
    exact Nat.le_trans h1 (Nat.add_le_add_left h2 _)
  obtain ⟨e, he⟩ := exists_gapWC_step_lt' hpsi F.attack z.val.conf z.property.attack hn
  have hdrop : birthWork hpsi F (birthStep hpsi F z e) + 1 ≤
      birthWork hpsi F (.active z) := by
    have hb := child_work_le hpsi F z e
    change _ ≤ birthBase F + gapWC F.attack z.val.conf
    change gapWC F.attack (attemptStepConf hpsi F z.val e) < _ at he
    omega
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => birthWork hpsi F (birthStep hpsi F z e))
    (birthWork hpsi F (.active z)) e hmono hdrop
  omega

theorem birth_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (birthStep hpsi F) 1 (birthPotential hpsi F) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hrow : 1 + (List.ofFn (fun e : Fin n =>
      birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * birthWork hpsi F (.active z) := by
    by_cases hc : CleanReady F.attack z.val.conf
    · exact clean_work_row hpsi F z hc
    · exact nonclean_work_row hpsi F z hc
  change 1 * n + (List.ofFn (fun e : Fin n =>
    n * birthWork hpsi F (birthStep hpsi F z e))).sum ≤
      n * (n * birthWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hrow
  simpa only [Nat.mul_add, Nat.mul_one] using hs

theorem birth_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (birthStep hpsi F) (.active z) T ≤
      n ^ T * (n * (4 * F.attack.d + 1)) := by
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (birthStep hpsi F) 1 (birthPotential hpsi F) (birth_bellman hpsi F) (.active z) T
  have hr := gapWC_le_two_d hpsi F.attack z.val.conf z.property.attack
  have hp : birthPotential hpsi F (.active z) ≤ n * (4 * F.attack.d + 1) := by
    apply Nat.mul_le_mul_left
    change 2 * F.attack.d + 1 + gapWC F.attack z.val.conf ≤ _
    omega
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem birth_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) : birthStep hpsi F z e ≠ .failure := by
  classical
  unfold birthStep
  split <;> intro he <;> cases he

/-- Uniform half mass for real fresh-shot birth or deletion, from any
physical gap pair, including all reactivation states and phase values. -/
theorem fresh_birth_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    n ^ (2 * n * (4 * F.attack.d + 1)) ≤
      2 * successCount (freshStep hpsi F) (.active b)
        (2 * n * (4 * F.attack.d + 1)) := by
  let z : BirthState hpsi F := ⟨b, hg⟩
  let T := 2 * n * (4 * F.attack.d + 1)
  have hp : 0 < T := by
    have hn := F.attack.ring.hn
    dsimp only [T]
    exact Nat.mul_pos (Nat.mul_pos (by decide) hn) (by omega)
  have hc := birth_truncated_cost hpsi F z T
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (birthStep hpsi F) (.active z) hp (by decide : 0 < 1)
    (num := n * (4 * F.attack.d + 1))
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (birthStep hpsi F) (birth_no_failure hpsi F) z T
  have hparts := node_count_partition (birthStep hpsi F) (.active z) T
  have hs : n ^ T ≤ 2 * successCount (birthStep hpsi F) (.active z) T := by omega
  rw [successCount_erases] at hs
  exact hs

end LDSinkTwoGapRaceEntranceBirthBudget

#print axioms LDSinkTwoGapRaceEntranceBirthBudget.birthStep_erases
#print axioms LDSinkTwoGapRaceEntranceBirthBudget.birth_bellman
#print axioms LDSinkTwoGapRaceEntranceBirthBudget.birth_truncated_cost
#print axioms LDSinkTwoGapRaceEntranceBirthBudget.fresh_birth_half
