import Leader.Wu.ShortGap.ChoiceRestart

/-!
# Two-sided denial receipts for the short-gap rearm service

This file refines the macro rearm of `Leader/Wu/ShortGap/ChoiceRestart.lean` by
one honest step.  It is an **intermediate two-sided quotient**, not a literal
radius-one protocol.

After a candidate-free uniform round every logical root owns one rearm
obligation.  In the intended protocol a gap returns a denial to **both** of
its endpoints, and a root may rearm only after it has received the denial of
its counterclockwise gap `(i-1, i)` and the denial of its clockwise gap
`(i, i+1)` — two separate receipts.  Candidate endpoints never enter the
rearm service.  Here a root carries two receipt bits:

* `rightReceipt i` — the current denial of the clockwise gap has reached root
  `i` through its outgoing port (scheduler edge `P.root i`);
* `leftReceipt i` — the current denial of the counterclockwise gap has reached
  root `i` through its incoming port (the scheduler edge `e` with
  `rightNeighbor e = P.root i`).

Each receipt bit means only "the current denial of that gap has reached this
endpoint port".  One physical scheduler edge serves its tail root through the
outgoing port and its head root through the incoming port at once; for a gap
of physical length `1` the delivery edge coincides with the comparison edge,
so adjacent gaps sharing a root are served by a shared edge counted once, and
adjacent roots are never treated as independent.

**Not modelled here:** the transport of declarations across a gap of physical
length `> 1`, currentness/staleness authentication of receipts, erasure of
forged declarations or receipts, and serializer/abort obligations.  No claim
about complete leader stabilization or final complexity is made; the bound
below is the two-sided quotient's rearm reset potential `R = 2*n*m` composed
with the already proved balanced restart interface.
-/

namespace ShortGapTwoDenialRearm

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapChoiceRestart

set_option autoImplicit false

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

private theorem rightNeighbor_leftNeighbor
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-! ## Two-sided receipt state -/

/-- Receipt state of the two-sided rearm service.  `participating` is fixed
by the step: candidate endpoints are not participating, and on the uniform
all-denial word every root participates. -/
structure TwoDenialState (m : Nat) where
  participating : Fin m → Bool
  rightReceipt : Fin m → Bool
  leftReceipt : Fin m → Bool
  hasPending : ∃ i, participating i = true ∧
    (rightReceipt i = false ∨ leftReceipt i = false)

/-- Missing receipts of one root: `0`, `1`, or `2` for a participating root,
`0` for a non-participating root. -/
def missingWeight {m : Nat}
    (participating rightReceipt leftReceipt : Fin m → Bool) (i : Fin m) :
    Nat :=
  if participating i then
    (if rightReceipt i then 0 else 1) + (if leftReceipt i then 0 else 1)
  else 0

/-- Total number of missing receipts over participating roots. -/
def missingCount {m : Nat}
    (participating rightReceipt leftReceipt : Fin m → Bool) : Nat :=
  (List.ofFn (missingWeight participating rightReceipt leftReceipt)).sum

theorem missingWeight_le_two {m : Nat}
    (participating rightReceipt leftReceipt : Fin m → Bool) (i : Fin m) :
    missingWeight participating rightReceipt leftReceipt i ≤ 2 := by
  simp only [missingWeight]
  split
  · split <;> split <;> omega
  · omega

/-- Scheduler edge `edge` delivers the clockwise-gap denial to its tail root
through that root's outgoing port. -/
def deliverRight {n m : Nat} (P : Placement n m)
    (rightReceipt : Fin m → Bool) (edge : Fin n) : Fin m → Bool :=
  fun i => if P.root i = edge then true else rightReceipt i

/-- Scheduler edge `edge` delivers the counterclockwise-gap denial to its head
root through that root's incoming port. -/
def deliverLeft {n m : Nat} (P : Placement n m)
    (leftReceipt : Fin m → Bool) (edge : Fin n) : Fin m → Bool :=
  fun i => if P.root i = P.physicalRing.rightNeighbor edge then true
    else leftReceipt i

/-- Receipt bits of non-participating roots are updated as well; they carry
zero weight, so this choice is irrelevant for the potential. -/
theorem deliverRight_root {n m : Nat} (P : Placement n m)
    (rightReceipt : Fin m → Bool) (i : Fin m) :
    deliverRight P rightReceipt (P.root i) i = true := by
  simp [deliverRight]

theorem deliverLeft_rightNeighbor {n m : Nat} (P : Placement n m)
    (leftReceipt : Fin m → Bool) (edge : Fin n) (j : Fin m)
    (hj : P.root j = P.physicalRing.rightNeighbor edge) :
    deliverLeft P leftReceipt edge j = true := by
  simp [deliverLeft, hj]

/-- Receipts are never withdrawn by a step. -/
theorem deliverRight_mono {n m : Nat} (P : Placement n m)
    (rightReceipt : Fin m → Bool) (edge : Fin n) (i : Fin m)
    (h : rightReceipt i = true) :
    deliverRight P rightReceipt edge i = true := by
  simp only [deliverRight]
  split <;> simp [h]

theorem deliverLeft_mono {n m : Nat} (P : Placement n m)
    (leftReceipt : Fin m → Bool) (edge : Fin n) (i : Fin m)
    (h : leftReceipt i = true) :
    deliverLeft P leftReceipt edge i = true := by
  simp only [deliverLeft]
  split <;> simp [h]

/-! ## Shared-edge two-sided service -/

/-- **Short gap, shared edge.**  If root `j` sits at the physical right
neighbour of root `i` (a gap of physical length `1`), then the single
scheduler edge `P.root i` delivers the clockwise receipt to `i` and the
counterclockwise receipt to `j` in one atomic step. -/
theorem shortGap_edge_delivers_both {n m : Nat} (P : Placement n m)
    (rightReceipt leftReceipt : Fin m → Bool) (i j : Fin m)
    (hshort : P.root j = P.physicalRing.rightNeighbor (P.root i)) :
    deliverRight P rightReceipt (P.root i) i = true ∧
      deliverLeft P leftReceipt (P.root i) j = true :=
  ⟨deliverRight_root P rightReceipt i,
    deliverLeft_rightNeighbor P leftReceipt (P.root i) j hshort⟩

/-- The incoming port of a root is the scheduler edge whose head is the
root; on a nontrivial ring it differs from the outgoing port. -/
theorem incomingEdge_ne_outgoingEdge {n m : Nat} (P : Placement n m)
    (hn : 1 < n) (i : Fin m) :
    P.physicalRing.leftNeighbor (P.root i) ≠ P.root i :=
  fun h => Placement.root_ne_incomingEdge P hn i h.symm

/-- Any edge delivering the counterclockwise receipt to root `i` differs from
the edge delivering its clockwise receipt.  Hence a root needs two distinct
scheduler edges to complete, unless one of them is shared with a neighbour. -/
theorem leftDeliveryEdge_ne_root {n m : Nat} (P : Placement n m)
    (hn : 1 < n) (i : Fin m) (edge : Fin n)
    (hedge : P.physicalRing.rightNeighbor edge = P.root i) :
    edge ≠ P.root i := by
  intro h
  rw [h] at hedge
  exact rightNeighbor_ne P.physicalRing hn (P.root i) hedge

/-- The incoming port really delivers the counterclockwise receipt. -/
theorem deliverLeft_incomingEdge {n m : Nat} (P : Placement n m)
    (leftReceipt : Fin m → Bool) (i : Fin m) :
    deliverLeft P leftReceipt (P.physicalRing.leftNeighbor (P.root i)) i =
      true := by
  apply deliverLeft_rightNeighbor
  rw [rightNeighbor_leftNeighbor]

/-! ## Potential monotonicity -/

private theorem missingWeight_step_le {n m : Nat} (P : Placement n m)
    (participating rightReceipt leftReceipt : Fin m → Bool) (edge : Fin n)
    (i : Fin m) :
    missingWeight participating (deliverRight P rightReceipt edge)
        (deliverLeft P leftReceipt edge) i ≤
      missingWeight participating rightReceipt leftReceipt i := by
  simp only [missingWeight, deliverRight, deliverLeft]
  by_cases hp : participating i = true <;>
    by_cases h1 : P.root i = edge <;>
    by_cases h2 : P.root i = P.physicalRing.rightNeighbor edge <;>
    by_cases hr : rightReceipt i = true <;>
    by_cases hl : leftReceipt i = true <;>
    simp [hp, h1, h2, hr, hl] <;> (first | omega | (split <;> omega))

/-- A scheduler edge never creates missing receipts. -/
theorem missingCount_step_le {n m : Nat} (P : Placement n m)
    (participating rightReceipt leftReceipt : Fin m → Bool) (edge : Fin n) :
    missingCount participating (deliverRight P rightReceipt edge)
        (deliverLeft P leftReceipt edge) ≤
      missingCount participating rightReceipt leftReceipt :=
  ofFn_sum_le _ _
    (missingWeight_step_le P participating rightReceipt leftReceipt edge)

/-- The outgoing port of a participating root missing its clockwise receipt
strictly lowers the missing count. -/
theorem missingCount_step_root_lt {n m : Nat} (P : Placement n m)
    (participating rightReceipt leftReceipt : Fin m → Bool) (i : Fin m)
    (hpart : participating i = true) (hmiss : rightReceipt i = false) :
    missingCount participating (deliverRight P rightReceipt (P.root i))
        (deliverLeft P leftReceipt (P.root i)) <
      missingCount participating rightReceipt leftReceipt := by
  apply ofFn_sum_lt_of_single_lt _ _ i
  · exact missingWeight_step_le P participating rightReceipt leftReceipt
      (P.root i)
  · simp only [missingWeight, deliverRight, deliverLeft, hpart, hmiss]
    by_cases hl : leftReceipt i = true <;> simp [hl] <;>
      (first | omega | (split <;> omega))

/-- The incoming port of a participating root missing its counterclockwise
receipt strictly lowers the missing count. -/
theorem missingCount_step_left_lt {n m : Nat} (P : Placement n m)
    (participating rightReceipt leftReceipt : Fin m → Bool) (i : Fin m)
    (edge : Fin n) (hedge : P.physicalRing.rightNeighbor edge = P.root i)
    (hpart : participating i = true) (hmiss : leftReceipt i = false) :
    missingCount participating (deliverRight P rightReceipt edge)
        (deliverLeft P leftReceipt edge) <
      missingCount participating rightReceipt leftReceipt := by
  apply ofFn_sum_lt_of_single_lt _ _ i
  · exact missingWeight_step_le P participating rightReceipt leftReceipt edge
  · simp only [missingWeight, deliverRight, deliverLeft, hpart, hmiss, hedge]
    by_cases hout : P.root i = edge <;>
      by_cases hr : rightReceipt i = true <;> simp [hout, hr]

/-! ## Stopped step and Bellman certificate -/

/-- The two-sided rearm service stops only when no participating root is
missing a receipt.  It never fails. -/
noncomputable def twoDenialStep {n m : Nat} (P : Placement n m) :
    TwoDenialState m → Fin n → StopNode (TwoDenialState m) :=
  fun state edge =>
    let right := deliverRight P state.rightReceipt edge
    let left := deliverLeft P state.leftReceipt edge
    if hnext : ∃ i, state.participating i = true ∧
        (right i = false ∨ left i = false) then
      .active ⟨state.participating, right, left, hnext⟩
    else .success

def twoDenialPotential {n m : Nat} :
    StopNode (TwoDenialState m) → Nat
  | .active state =>
      n * missingCount state.participating state.rightReceipt
        state.leftReceipt
  | .success => 0
  | .failure => 0

private theorem twoDenialPotential_step_le {n m : Nat} (P : Placement n m)
    (state : TwoDenialState m) (edge : Fin n) :
    twoDenialPotential (n := n) (twoDenialStep P state edge) ≤
      n * missingCount state.participating
        (deliverRight P state.rightReceipt edge)
        (deliverLeft P state.leftReceipt edge) := by
  classical
  simp only [twoDenialStep]
  split <;> simp [twoDenialPotential]

/-- Exact child-sum inequality: some scheduler edge strictly lowers the
missing count, and none raises it. -/
theorem missingCount_step_childSum {n m : Nat} (P : Placement n m)
    (state : TwoDenialState m) :
    1 + (List.ofFn (fun edge : Fin n =>
      missingCount state.participating
        (deliverRight P state.rightReceipt edge)
        (deliverLeft P state.leftReceipt edge))).sum ≤
      n * missingCount state.participating state.rightReceipt
        state.leftReceipt := by
  obtain ⟨i, hpart, hmiss⟩ := state.hasPending
  have hexists : ∃ edge : Fin n,
      missingCount state.participating
        (deliverRight P state.rightReceipt edge)
        (deliverLeft P state.leftReceipt edge) <
      missingCount state.participating state.rightReceipt
        state.leftReceipt := by
    rcases hmiss with hright | hleft
    · exact ⟨P.root i, missingCount_step_root_lt P _ _ _ i hpart hright⟩
    · exact ⟨P.physicalRing.leftNeighbor (P.root i),
        missingCount_step_left_lt P _ _ _ i _
          (rightNeighbor_leftNeighbor P.physicalRing (P.root i))
          hpart hleft⟩
  obtain ⟨edge, hlt⟩ := hexists
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n => missingCount state.participating
      (deliverRight P state.rightReceipt edge)
      (deliverLeft P state.leftReceipt edge))
    (fun _ : Fin n => missingCount state.participating state.rightReceipt
      state.leftReceipt) edge
    (fun edge => missingCount_step_le P _ _ _ edge) hlt
  rw [ofFn_sum_const] at hsumlt
  omega

/-- The two-sided receipt service has expected work at most `n` times the
number of initially missing receipts. -/
theorem twoDenial_natBellmanSuperSolution {n m : Nat} (P : Placement n m) :
    NatBellmanSuperSolution (twoDenialStep P) 1
      (twoDenialPotential (n := n)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := missingCount_step_childSum P state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        twoDenialPotential (n := n) (twoDenialStep P state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          missingCount state.participating
            (deliverRight P state.rightReceipt edge)
            (deliverLeft P state.leftReceipt edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          twoDenialPotential (n := n) (twoDenialStep P state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          n * missingCount state.participating
            (deliverRight P state.rightReceipt edge)
            (deliverLeft P state.leftReceipt edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact twoDenialPotential_step_le P state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          missingCount state.participating
            (deliverRight P state.rightReceipt edge)
            (deliverLeft P state.leftReceipt edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        twoDenialPotential (n := n) (twoDenialStep P state edge))).sum ≤
      n + n * (List.ofFn (fun edge : Fin n =>
        missingCount state.participating
          (deliverRight P state.rightReceipt edge)
          (deliverLeft P state.leftReceipt edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
        missingCount state.participating
          (deliverRight P state.rightReceipt edge)
          (deliverLeft P state.leftReceipt edge))).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * missingCount state.participating state.rightReceipt
        state.leftReceipt) := hscaled
    _ = n * twoDenialPotential (n := n) (.active state) := rfl

theorem twoDenialStep_ne_failure {n m : Nat} (P : Placement n m) :
    ∀ state edge, twoDenialStep P state edge ≠ .failure := by
  classical
  intro state edge
  simp only [twoDenialStep]
  split <;> simp

/-! ## Uniform all-denial start -/

/-- After a candidate-free uniform round every root participates and no
denial receipt has been delivered yet. -/
def allPendingTwoDenialState {m : Nat} (hm : 0 < m) : TwoDenialState m :=
  ⟨fun _ => true, fun _ => false, fun _ => false,
    ⟨⟨0, hm⟩, rfl, Or.inl rfl⟩⟩

@[simp] theorem missingCount_allPending {m : Nat} :
    missingCount (fun _ : Fin m => true) (fun _ => false) (fun _ => false) =
      2 * m := by
  have hweight : missingWeight (fun _ : Fin m => true) (fun _ => false)
      (fun _ => false) = fun _ => 2 := by
    funext i
    simp [missingWeight]
  rw [missingCount, hweight, ofFn_sum_const, Nat.mul_comm]

@[simp] theorem twoDenialPotential_allPending {n m : Nat} (hm : 0 < m) :
    twoDenialPotential (n := n) (.active (allPendingTwoDenialState hm)) =
      n * (2 * m) := by
  simp [twoDenialPotential, allPendingTwoDenialState]

/-! ## Relation to the macro pending flag -/

/-- The macro pending flag of `Leader/Wu/ShortGap/ChoiceRestart.lean` is the
"both receipts present" abstraction of the two-sided state: a participating
root is pending iff it still misses at least one receipt, and its macro weight
is at most its missing-receipt weight. -/
theorem pendingCount_le_missingCount {m : Nat}
    (participating rightReceipt leftReceipt : Fin m → Bool) :
    pendingCount (fun i => participating i &&
        !(rightReceipt i && leftReceipt i)) ≤
      missingCount participating rightReceipt leftReceipt := by
  apply ofFn_sum_le
  intro i
  simp only [missingWeight]
  by_cases hp : participating i = true <;>
    by_cases hr : rightReceipt i = true <;>
    by_cases hl : leftReceipt i = true <;> simp [hp, hr, hl]

/-! ## Composition with the balanced candidate restart -/

/-- Two-sided receipt implementation of the candidate rearm interface. -/
noncomputable def twoDenialCandidateRearmSpec
    {n m : Nat} (P : Placement n m) (hm : 0 < m) :
    CandidateRearmSpec n where
  State := TwoDenialState m
  step := twoDenialStep P
  start := allPendingTwoDenialState hm
  potential := twoDenialPotential (n := n)
  bellman := twoDenial_natBellmanSuperSolution P
  noFailure := twoDenialStep_ne_failure P

/-- Complete two-sided candidate process: bare incidence choice, charged
two-receipt rearm, and repetition until the first persistent candidate. -/
noncomputable def twoDenialCandidateRestartStep
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (hm : 0 < m) :=
  (twoDenialCandidateRearmSpec P hm).restartStep ring P hm

private theorem four_budget (n m : Nat) :
    4 * (n * m) = 2 * (n * m) + n * (2 * m) := by
  rw [Nat.mul_left_comm n 2 m]
  omega

/-- Repeated two-sided candidate rounds have expected work at most `4*n*m`:
two copies pay for the balanced candidate round and two pay for the two
denial receipts of every root. -/
theorem twoDenialCandidateRestart_truncatedCost_le
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (T : Nat) :
    truncatedActiveCostNumerator
        (twoDenialCandidateRestartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (4 * (n * m)) := by
  have hcost :=
    (twoDenialCandidateRearmSpec P (by omega)).allRace_truncatedCost_le
      ring hm P hn T
  simp only [twoDenialCandidateRestartStep, twoDenialCandidateRearmSpec,
    twoDenialPotential_allPending] at hcost ⊢
  rw [four_budget]
  exact hcost

/-- Exact reciprocal success tail for the complete two-sided process. -/
theorem twoDenialCandidateRestart_success_one_minus_inv_factor
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) :
    (factor - 1) * n ^ (factor * (4 * (n * m))) ≤
      factor * successCount
        (twoDenialCandidateRestartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (4 * (n * m))) := by
  have hsuccess :=
    CandidateRearmSpec.allRace_success_one_minus_inv_factor
      (twoDenialCandidateRearmSpec P (by omega)) ring hm P hn
      (factor := factor)
  simp only [twoDenialCandidateRestartStep, twoDenialCandidateRearmSpec,
    twoDenialPotential_allPending] at hsuccess ⊢
  rw [four_budget]
  exact hsuccess

#print axioms shortGap_edge_delivers_both
#print axioms missingCount_step_root_lt
#print axioms missingCount_step_left_lt
#print axioms twoDenial_natBellmanSuperSolution
#print axioms pendingCount_le_missingCount
#print axioms twoDenialCandidateRestart_truncatedCost_le
#print axioms twoDenialCandidateRestart_success_one_minus_inv_factor

end ShortGapTwoDenialRearm
