import Leader.Wu.Elimination.Ledger

set_option autoImplicit false

namespace EliminationLedgerInstance

open EliminationLedger

/-!
# Concrete constant adapters for the elimination ledger

The imported ledger intentionally uses a local mirror of the repository
stopping-tree carrier.  This file therefore proves the physical arithmetic at
a Nat-valued block-cost interface, then supplies the exact adapter to the
ledger's `TwoGapDeletionSpec` when that interface is instantiated by the ledger
mirror cost.

For the real protocol use

  span F = F.recovery.d + F.attack.d.

A real `TwoGapFrame n` consists of two legal `GapFrame n` values, the shared
endpoint equality, and `recovery.d + attack.d < n`.  The current legal gap
carrier has minimum distance 2.  `FrameChoiceSpec.construct` below isolates the
only physical geometry statement not whose exact Lean signature was supplied:
construct the frame from a proof-selected cyclic adjacent pair.
-/

/-! ## 1. R6: candidate construction versus universal applicability -/

/-- Numerical conditions needed by the current two-gap frame geometry.  The
shared endpoint equality is geometric and is carried by `buildsFrame`. -/
def LegalPair (n a b : Nat) : Prop :=
  2 ≤ a ∧ 2 ≤ b ∧ a + b < n

/-- The only non-arithmetic bridge from a selected adjacent pair to a frame.
For the real specialization, `Frame = TwoGapFrame n`, `selectedPair` is the
cyclic pair selected by `minimalTripleChoice`, and `buildsFrame` means that the
two `GapFrame`s are exactly those adjacent gaps and satisfy `shared`. -/
structure FrameChoiceSpec (EState Frame : Type) (n : Nat)
    (span : Frame → Nat) where
  selectedPair : EState → Nat → Nat → Prop
  buildsFrame : EState → Nat → Nat → Frame → Prop
  span_eq : ∀ {e a b F}, buildsFrame e a b F → span F = a + b
  construct : ∀ {e a b}, selectedPair e a b → LegalPair n a b →
    ∃ F, buildsFrame e a b F

/-- A candidate already contains a genuinely constructed legal frame. -/
def candidate {EState Frame : Type} {n : Nat} {span : Frame → Nat}
    (B : FrameChoiceSpec EState Frame n span)
    (e : EState) (F : Frame) : Prop :=
  ∃ a b, B.selectedPair e a b ∧ B.buildsFrame e a b F

/-- Nat-valued form of the real physical block-cost theorem. -/
def BlockCostSpec {S Frame : Type} (n : Nat)
    (cost : Frame → S → Nat → Nat) (span : Frame → Nat) : Prop :=
  ∀ F x T,
    cost F x T ≤ n ^ T * episodePhi n (span F)

/-- `applicable` contains no choice-specific condition: the episode theorem is
available on this frame. -/
def applicable {EState S Frame : Type} (n : Nat)
    (cost : Frame → S → Nat → Nat) (span : Frame → Nat)
    (_e : EState) (F : Frame) : Prop :=
  ∀ x T,
    cost F x T ≤ n ^ T * episodePhi n (span F)

/-- A selected legal pair produces a ledger candidate. -/
theorem candidate_of_selected_legal
    {EState Frame : Type} {n : Nat} {span : Frame → Nat}
    (B : FrameChoiceSpec EState Frame n span)
    {e : EState} {a b : Nat}
    (hSelected : B.selectedPair e a b)
    (hLegal : LegalPair n a b) :
    ∃ F, candidate B e F ∧ span F = a + b := by
  obtain ⟨F, hBuild⟩ := B.construct hSelected hLegal
  refine ⟨F, ?_, B.span_eq hBuild⟩
  exact ⟨a, b, hSelected, hBuild⟩

/-- R6 proper collapses: universal applicability ignores how the frame was
selected. -/
theorem r6_collapsed
    {EState S Frame : Type} {n : Nat} {span : Frame → Nat}
    (B : FrameChoiceSpec EState Frame n span)
    (cost : Frame → S → Nat → Nat)
    (hE : BlockCostSpec n cost span) :
    ∀ {e F}, candidate B e F → applicable n cost span e F := by
  intro e F _hCandidate
  exact hE F

/-- This is the exact shape consumed by the batching seam after
`minimalTripleChoice` supplies `hSelected` and `hCharge`, and the physical
frame builder supplies legality. -/
theorem minimal_choice_to_ledger_choice
    {EState S Frame : Type} {n m : Nat} {span : Frame → Nat}
    (B : FrameChoiceSpec EState Frame n span)
    (cost : Frame → S → Nat → Nat)
    (hE : BlockCostSpec n cost span)
    {e : EState} {a b : Nat}
    (hSelected : B.selectedPair e a b)
    (hLegal : LegalPair n a b)
    (hCharge : m * (a + b) ≤ 2 * n) :
    ∃ F, candidate B e F ∧ applicable n cost span e F ∧
      m * span F ≤ 2 * n := by
  obtain ⟨F, hCandidate, hSpan⟩ :=
    candidate_of_selected_legal B hSelected hLegal
  refine ⟨F, hCandidate, r6_collapsed B cost hE hCandidate, ?_⟩
  rw [hSpan]
  exact hCharge

/-- With at least three leaders, legal minimum gap lengths plus the pigeonhole
charge imply the `TwoGapFrame.length_lt` numerical condition. -/
theorem legalPair_of_charge_three
    {n m a b : Nat}
    (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hCharge : m * (a + b) ≤ 2 * n) :
    LegalPair n a b := by
  refine ⟨ha, hb, ?_⟩
  have h3m : 3 * (a + b) ≤ m * (a + b) :=
    Nat.mul_le_mul_right (a + b) hm
  have h3 : 3 * (a + b) ≤ 2 * n :=
    Nat.le_trans h3m hCharge
  clear hCharge h3m hm m
  omega

/-- The pigeonhole charge alone does not imply the minimum legal gap length. -/
theorem minimal_charge_does_not_force_gap_min :
    2 * (1 + 1) ≤ 2 * 5 ∧ ¬ (2 ≤ 1) := by
  decide

/-- Even with both lengths at least two, the two-leader case can consume the
whole ring, so the charge alone does not imply `length_lt`. -/
theorem two_leader_charge_does_not_force_length_lt :
    2 * (2 + 4) ≤ 2 * 6 ∧ ¬ (2 + 4 < 6) := by
  decide

/-! ## 2. Exact E constants and division-free charge -/

/-- Normalize the compiled two-gap constant. -/
theorem episodePhi_expanded (n s : Nat) :
    episodePhi n s = 2048 * n * s + 256 * n := by
  unfold episodePhi
  calc
    2 * 32 * (32 * n * s + 4 * n) =
        (2 * 32 * 32) * n * s + (2 * 32 * 4) * n := by
      rw [Nat.mul_add]
      ac_rfl
    _ = 2048 * n * s + 256 * n := by
      rw [show 2 * 32 * 32 = 2048 by decide,
        show 2 * 32 * 4 = 256 by decide]

/-- Exact adapter for `two_gap_deletion_cost_wired` at the Nat-valued cost
interface.  Instantiate `cost F x T` by the real
`truncatedActiveCostNumerator (physicalBlockStep hpsi F) (.active x) T`;
then the supplied theorem discharges `hWired` verbatim for every legal `F`. -/
theorem blockCostSpec_of_wired_bound
    {S Frame : Type} {n : Nat}
    (cost : Frame → S → Nat → Nat) (span : Frame → Nat)
    (hWired : ∀ F x T,
      cost F x T ≤
        n ^ T * (2 * 32 * (32 * n * span F + 4 * n))) :
    BlockCostSpec n cost span := by
  intro F x T
  change cost F x T ≤
    n ^ T * (2 * 32 * (32 * n * span F + 4 * n))
  exact hWired F x T

/-- Adapter from the Nat-valued interface to the abstract piece E when the
cost is the ledger mirror cost. -/
theorem ledger_twoGapDeletionSpec_of_blockCost
    {S Frame : Type} {n : Nat}
    (blockStep : Frame → S → Fin n → EliminationLedger.StopNode S)
    (span : Frame → Nat)
    (hCost : BlockCostSpec n
      (fun F x T =>
        EliminationLedger.truncatedActiveCostNumerator
          (blockStep F) (.active x) T)
      span) :
    ∀ F, EliminationLedger.TwoGapDeletionSpec blockStep span F := by
  intro F x T
  exact hCost F x T

/-- Pigeonhole charge with no Nat division. -/
theorem episodePhi_charge
    {n m s : Nat} (hCharge : m * s ≤ 2 * n) :
    m * episodePhi n s ≤
      4096 * (n ^ 2) + 256 * n * m := by
  have hScaled :
      2048 * n * (m * s) ≤ 2048 * n * (2 * n) :=
    Nat.mul_le_mul_left (2048 * n) hCharge
  calc
    m * episodePhi n s =
        m * (2048 * n * s + 256 * n) := by
      rw [episodePhi_expanded]
    _ = 2048 * n * (m * s) + 256 * n * m := by
      rw [Nat.mul_add]
      ac_rfl
    _ ≤ 2048 * n * (2 * n) + 256 * n * m :=
      Nat.add_le_add_right hScaled _
    _ = (2048 * 2) * (n * n) + 256 * n * m := by
      ac_rfl
    _ = 4096 * (n * n) + 256 * n * m := by
      rw [show 2048 * 2 = 4096 by decide]
    _ = 4096 * (n ^ 2) + 256 * n * m := by
      have hsq : n ^ 2 = n * n := by
        simp [Nat.pow_succ]
      rw [← hsq]

/-- The same division-free charge at the physical cost-numerator level. -/
theorem blockCost_charge
    {S Frame : Type} {n m : Nat}
    (cost : Frame → S → Nat → Nat) (span : Frame → Nat)
    (hCost : BlockCostSpec n cost span)
    (F : Frame) (x : S) (T : Nat)
    (hCharge : m * span F ≤ 2 * n) :
    m * cost F x T ≤
      n ^ T * (4096 * (n ^ 2) + 256 * n * m) := by
  calc
    m * cost F x T ≤
        m * (n ^ T * episodePhi n (span F)) :=
      Nat.mul_le_mul_left m (hCost F x T)
    _ = n ^ T * (m * episodePhi n (span F)) := by
      ac_rfl
    _ ≤ n ^ T * (4096 * (n ^ 2) + 256 * n * m) :=
      Nat.mul_le_mul_left (n ^ T) (episodePhi_charge hCharge)

/-! ## 3. R5 turns a span-weight constant B into C = 2048*B+256 -/

/-- The exact arithmetic implication requested from R5. -/
theorem episode_to_telescope_coefficient
    {EState : Type} (n B : Nat)
    (next : EState → EState → Prop)
    (episodeBound span : EState → EState → Nat)
    (w : EState → Nat)
    (hRaw : ∀ {x y}, next x y →
      episodeBound x y ≤ 2048 * n * span x y + 256 * n)
    (hSpan : ∀ {x y}, next x y →
      span x y ≤ B * ((w x - w y) + 1))
    {x y : EState} (hxy : next x y) :
    episodeBound x y ≤
      ((2048 * B + 256) * n) * ((w x - w y) + 1) := by
  let q := (w x - w y) + 1
  have hq : 1 ≤ q := by
    dsimp [q]
    omega
  have hSpan' : span x y ≤ B * q := hSpan hxy
  have hMain :
      2048 * n * span x y ≤ 2048 * n * (B * q) :=
    Nat.mul_le_mul_left (2048 * n) hSpan'
  have hBase : 256 * n ≤ 256 * n * q := by
    have h := Nat.mul_le_mul_left (256 * n) hq
    simpa using h
  calc
    episodeBound x y ≤
        2048 * n * span x y + 256 * n := hRaw hxy
    _ ≤ 2048 * n * (B * q) + 256 * n * q :=
      Nat.add_le_add hMain hBase
    _ = ((2048 * B + 256) * n) * q := by
      simp only [Nat.add_mul]
      ac_rfl

/-- Full telescope-step packaging once R5 also supplies monotonicity of the
merge-stable weight and strict phase decrease. -/
theorem r5_step_of_span_weight
    {EState : Type} (n B : Nat)
    (next : EState → EState → Prop)
    (episodeBound span : EState → EState → Nat)
    (w phase : EState → Nat)
    (hMono : ∀ {x y}, next x y → w y ≤ w x)
    (hPhase : ∀ {x y}, next x y → phase y < phase x)
    (hRaw : ∀ {x y}, next x y →
      episodeBound x y ≤ 2048 * n * span x y + 256 * n)
    (hSpan : ∀ {x y}, next x y →
      span x y ≤ B * ((w x - w y) + 1)) :
    ∀ {x y}, next x y →
      w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤
        ((2048 * B + 256) * n) * ((w x - w y) + 1) := by
  intro x y hxy
  refine ⟨hMono hxy, hPhase hxy, ?_⟩
  exact episode_to_telescope_coefficient n B next episodeBound span w
    hRaw hSpan hxy

/-- Visible per-round coefficient after R5 provides `B`. -/
theorem roundPhi_with_B (n B : Nat) :
    roundPhi n (2048 * B + 256) =
      (4096 * B + 512) * (n ^ 2) := by
  unfold roundPhi
  have hCoeff : 2 * (2048 * B + 256) = 4096 * B + 512 := by
    omega
  rw [hCoeff]

/-- Visible total coefficient for `k` batching rounds. -/
theorem eliminationPhi_with_B (n B k : Nat) :
    eliminationPhi n (2048 * B + 256) k =
      (4096 * B + 512) * (n ^ 2) * k := by
  unfold eliminationPhi
  have hCoeff : 2 * (2048 * B + 256) = 4096 * B + 512 := by
    omega
  rw [hCoeff]

/-- Bound form of the per-round equality. -/
theorem per_round_bound_with_B
    {total n B : Nat}
    (h : total ≤ roundPhi n (2048 * B + 256)) :
    total ≤ (4096 * B + 512) * (n ^ 2) := by
  rw [roundPhi_with_B n B] at h
  exact h

/-- Bound form of the final `k`-round equality. -/
theorem total_bound_with_B
    {total n B k : Nat}
    (h : total ≤ eliminationPhi n (2048 * B + 256) k) :
    total ≤ (4096 * B + 512) * (n ^ 2) * k := by
  rw [eliminationPhi_with_B n B k] at h
  exact h

end EliminationLedgerInstance

#print axioms EliminationLedgerInstance.candidate_of_selected_legal
#print axioms EliminationLedgerInstance.r6_collapsed
#print axioms EliminationLedgerInstance.minimal_choice_to_ledger_choice
#print axioms EliminationLedgerInstance.legalPair_of_charge_three
#print axioms EliminationLedgerInstance.minimal_charge_does_not_force_gap_min
#print axioms EliminationLedgerInstance.two_leader_charge_does_not_force_length_lt
#print axioms EliminationLedgerInstance.episodePhi_expanded
#print axioms EliminationLedgerInstance.blockCostSpec_of_wired_bound
#print axioms EliminationLedgerInstance.ledger_twoGapDeletionSpec_of_blockCost
#print axioms EliminationLedgerInstance.episodePhi_charge
#print axioms EliminationLedgerInstance.blockCost_charge
#print axioms EliminationLedgerInstance.episode_to_telescope_coefficient
#print axioms EliminationLedgerInstance.r5_step_of_span_weight
#print axioms EliminationLedgerInstance.roundPhi_with_B
#print axioms EliminationLedgerInstance.eliminationPhi_with_B
#print axioms EliminationLedgerInstance.per_round_bound_with_B
#print axioms EliminationLedgerInstance.total_bound_with_B
