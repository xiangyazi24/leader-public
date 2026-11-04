import Leader.Wu.Birth.SmallRingTwoAgentWidthObstruction

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthSmallRingN2NoGo

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthShortDoneTerminalFirstHit
open BirthShortDoneTerminalNoHitCount
open FixedSpanRenewalPayload FiniteUniformStoppingTree
open Q11497FeasibilityAudit

private theorem hOne : 0 < (1 : Nat) := by omega
private theorem hOneLe : (1 : Nat) ≤ 1 := by omega

/-- The small-ring route uses width `min 2 psi`, so the legal n = 2 tuple is
`(psi,width,kappa,tau) = (1,1,2,32)`. -/
theorem routed_n2_parameters :
    psiChoice 2 = 1 ∧
      Nat.min 2 (psiChoice 2) = 1 ∧
      kappaChoice 2 = 2 ∧
      tauChoice 2 = 32 := by
  decide

abbrev Cell := ExpiringAgentState 1 2 32

/-- Common metadata core of the closed family.  The only free metadata bit is
`h_field`; there is no leader, probe, comparison, path, or birth machinery. -/
def baseCore (h : Bool) : BoundedAgentState 1 2 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := true
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := 0
  h_field := h
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Initiator-role cell. -/
def L (h : Bool) (s : Fin 33) : Cell :=
  ⟨⟨baseCore h, false⟩, s⟩

/-- Responder-role cell. -/
def R (h : Bool) (s : Fin 33) : Cell :=
  ⟨⟨{ baseCore h with reset := true, write_state := .depart }, false⟩, s⟩

/-- Literal expiry map on this family: zero refreshes to 32; otherwise one unit
is spent. -/
def tick (s : Fin 33) : Fin 33 :=
  if hz : s.val = 0 then
    freshStall 32
  else
    ⟨s.val - 1, by omega⟩

/-! The literal row is expensive only when one `decide` is asked to prove the
entire quantified family.  Split first on the two Boolean parameters, then on
the 33 closed stall values.  Each kernel decision below is therefore one
closed host-row equality. -/

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_LR_false_false (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (L false s) (R false s) =
      (L (!false) (tick s), R false (tick s)) := by
  revert s; decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_LR_false_true (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (L false s) (R true s) =
      (L (!false) (tick s), R false (tick s)) := by
  revert s; decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_LR_true_false (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (L true s) (R false s) =
      (L (!true) (tick s), R true (tick s)) := by
  revert s; decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_LR_true_true (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (L true s) (R true s) =
      (L (!true) (tick s), R true (tick s)) := by
  revert s; decide

/-- First literal row identity from the current terminal host. -/
theorem row_LR :
    ∀ (hL hR : Bool) (s : Fin 33),
      BirthShortDoneTerminalHost.row hOne hOne hOneLe
          (L hL s) (R hR s) =
        (L (!hL) (tick s), R hL (tick s)) := by
  intro hL hR s
  cases hL <;> cases hR
  · exact row_LR_false_false s
  · exact row_LR_false_true s
  · exact row_LR_true_false s
  · exact row_LR_true_true s

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_RL_false_false (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (R false s) (L false s) =
      (L (!false) (tick s), R false (tick s)) := by
  revert s; decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_RL_false_true (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (R false s) (L true s) =
      (L (!false) (tick s), R false (tick s)) := by
  revert s; decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_RL_true_false (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (R true s) (L false s) =
      (L (!true) (tick s), R false (tick s)) := by
  revert s; decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
private theorem row_RL_true_true (s : Fin 33) :
    BirthShortDoneTerminalHost.row hOne hOne hOneLe
        (R true s) (L true s) =
      (L (!true) (tick s), R false (tick s)) := by
  revert s; decide

/-- Second literal row identity from the current terminal host. -/
theorem row_RL :
    ∀ (hR hL : Bool) (s : Fin 33),
      BirthShortDoneTerminalHost.row hOne hOne hOneLe
          (R hR s) (L hL s) =
        (L (!hR) (tick s), R false (tick s)) := by
  intro hR hL s
  cases hR <;> cases hL
  · exact row_RL_false_false s
  · exact row_RL_false_true s
  · exact row_RL_true_false s
  · exact row_RL_true_true s

/-- The unique directed two-site ring. -/
def ring2 : DirectedRing 2 := ⟨by omega⟩

theorem ring2_right_zero : ring2.rightNeighbor (0 : Fin 2) = 1 := by
  apply Fin.ext
  rfl

theorem ring2_right_one : ring2.rightNeighbor (1 : Fin 2) = 0 := by
  apply Fin.ext
  rfl

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

/-- Orientation with site 0 carrying the L-role cell. -/
def configLR (hL hR : Bool) (s : Fin 33) : Fin 2 → Cell :=
  Fin.cases (L hL s) (fun _ => R hR s)

/-- Orientation with site 0 carrying the R-role cell. -/
def configRL (hL hR : Bool) (s : Fin 33) : Fin 2 → Cell :=
  Fin.cases (R hR s) (fun _ => L hL s)

/-! The four scheduler-edge cases.  These use only the two certified row
identities above and the literal `PopulationProtocol.step`. -/

/-- `Fin.cases` at the literal `1 : Fin 2` (definitional; added in the local repair). -/
@[simp] private theorem fin2_cases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    (Fin.cases a f (1 : Fin 2) : α) = f 0 := rfl

theorem step_LR_zero (hL hR : Bool) (s : Fin 33) :
    BirthShortDoneTerminalConsumer.step hOne hOne hOneLe
        ring2 (configLR hL hR s) 0 =
      configLR (!hL) hL (tick s) := by
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [BirthShortDoneTerminalConsumer.step,
      BirthShortDoneTerminalConsumer.protocol, PopulationProtocol.step,
      configLR, ring2_right_zero, row_LR]

theorem step_LR_one (hL hR : Bool) (s : Fin 33) :
    BirthShortDoneTerminalConsumer.step hOne hOne hOneLe
        ring2 (configLR hL hR s) 1 =
      configRL (!hR) false (tick s) := by
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [BirthShortDoneTerminalConsumer.step,
      BirthShortDoneTerminalConsumer.protocol, PopulationProtocol.step,
      configLR, configRL, ring2_right_one, row_RL]

theorem step_RL_zero (hL hR : Bool) (s : Fin 33) :
    BirthShortDoneTerminalConsumer.step hOne hOne hOneLe
        ring2 (configRL hL hR s) 0 =
      configLR (!hR) false (tick s) := by
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [BirthShortDoneTerminalConsumer.step,
      BirthShortDoneTerminalConsumer.protocol, PopulationProtocol.step,
      configLR, configRL, ring2_right_zero, row_RL]

theorem step_RL_one (hL hR : Bool) (s : Fin 33) :
    BirthShortDoneTerminalConsumer.step hOne hOne hOneLe
        ring2 (configRL hL hR s) 1 =
      configRL (!hL) hL (tick s) := by
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [BirthShortDoneTerminalConsumer.step,
      BirthShortDoneTerminalConsumer.protocol, PopulationProtocol.step,
      configLR, configRL, ring2_right_one, row_LR]

/-- The 2 orientations × 2 L-bits × 2 R-bits × 33 stall values: 264 codes. -/
def InFamily (C : Fin 2 → Cell) : Prop :=
  ∃ hL hR : Bool, ∃ s : Fin 33,
    C = configLR hL hR s ∨ C = configRL hL hR s

/-- Closure under either of the two scheduler edges. -/
theorem InFamily.step {C : Fin 2 → Cell}
    (hC : InFamily C) (e : Fin 2) :
    InFamily
      (BirthShortDoneTerminalConsumer.step hOne hOne hOneLe ring2 C e) := by
  rcases hC with ⟨hL, hR, s, hC | hC⟩
  · subst C
    rcases fin2_cases e with rfl | rfl
    · exact ⟨!hL, hL, tick s, Or.inl (step_LR_zero hL hR s)⟩
    · exact ⟨!hR, false, tick s, Or.inr (step_LR_one hL hR s)⟩
  · subst C
    rcases fin2_cases e with rfl | rfl
    · exact ⟨!hR, false, tick s, Or.inl (step_RL_zero hL hR s)⟩
    · exact ⟨!hL, hL, tick s, Or.inr (step_RL_one hL hR s)⟩

/-- The same closure packaged in the repository's protocol interface. -/
theorem family_closedPred :
    PopulationProtocol.ClosedPred
      (BirthShortDoneTerminalConsumer.protocol hOne hOne hOneLe 2 32)
      ring2 InFamily := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  simpa [BirthShortDoneTerminalConsumer.step] using hC.step e

/-- Every member of the family is literally leaderless. -/
theorem InFamily.leaderless {C : Fin 2 → Cell} (hC : InFamily C) :
    Leaderless C := by
  rcases hC with ⟨hL, hR, s, hC | hC⟩ <;> subst C
  · intro i
    rcases fin2_cases i with rfl | rfl <;>
      simp [configLR, L, R, baseCore]
  · intro i
    rcases fin2_cases i with rfl | rfl <;>
      simp [configRL, L, R, baseCore]

/-- Consequently every prefix of every original scheduler word remains
leaderless. -/
theorem family_leaderlessAlong
    (C : Fin 2 → Cell) (hC : InFamily C) (word : List (Fin 2)) :
    LeaderlessAlong hOne hOne hOneLe ring2 C word := by
  induction word generalizing C with
  | nil =>
      exact hC.leaderless
  | cons e es ih =>
      change Leaderless C ∧
        LeaderlessAlong hOne hOne hOneLe ring2
          (BirthShortDoneTerminalConsumer.step hOne hOne hOneLe ring2 C e) es
      exact ⟨hC.leaderless, ih _ (hC.step e)⟩

/-- The physical no-hit indicator is identically one on this class. -/
theorem family_physicalNoHitBit_eq_one
    (C : Fin 2 → Cell) (hC : InFamily C) (word : List (Fin 2)) :
    physicalNoHitBit hOne hOne hOneLe ring2 C word = 1 := by
  classical
  unfold physicalNoHitBit
  rw [if_pos (family_leaderlessAlong C hC word)]

/-- Hence every one of the `2^T` original scheduler words is a no-hit word. -/
theorem family_physicalNoHit_wordSum
    (C : Fin 2 → Cell) (hC : InFamily C) (T : Nat) :
    wordSum 2 T (physicalNoHitBit hOne hOne hOneLe ring2 C) = 2 ^ T := by
  rw [← rawWord_sum 2 T
    (physicalNoHitBit hOne hOne hOneLe ring2 C)]
  calc
    (List.ofFn (fun j : Fin (2 ^ T) =>
      physicalNoHitBit hOne hOne hOneLe ring2 C
        (rawWord 2 T j))).sum =
        (List.ofFn (fun _ : Fin (2 ^ T) => 1)).sum := by
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro j
      exact family_physicalNoHitBit_eq_one C hC (rawWord 2 T j)
    _ = 2 ^ T := by
      rw [FiniteUniformStoppingTree.ofFn_sum_const]
      simp

/-- One concrete member is enough to refute the wrapper's universal first-hit
requirement, for every proposed choice of horizons and post-hit mass. -/
def seed : Fin 2 → Cell :=
  configLR false false 0

theorem seed_mem : InFamily seed :=
  ⟨false, false, 0, Or.inl rfl⟩

theorem seed_leaderless : Leaderless seed :=
  seed_mem.leaderless

/-- At the routed n = 2 tuple, `SmallRingBirthPhaseBound` is impossible.  Its
first-horizon clause would require `2 * 2^T ≤ 2^T`, while `2^T > 0`. -/
theorem smallRingBirthPhaseBound_n2_fails
    (firstHorizon postHorizon postMass : Nat) :
    ¬ BirthSmallRingWrapper.SmallRingBirthPhaseBound
      hOne hOne hOneLe ring2 seed
      firstHorizon postHorizon postMass := by
  intro h
  rcases h with ⟨_hn2, _hn3, _h0, hfirst, _hpost⟩
  have hsum :=
    family_physicalNoHit_wordSum seed seed_mem firstHorizon
  rw [hsum] at hfirst
  have hp : 0 < 2 ^ firstHorizon := Nat.pow_pos (by omega)
  omega

end BirthSmallRingN2NoGo

#print axioms BirthSmallRingN2NoGo.row_LR
#print axioms BirthSmallRingN2NoGo.row_RL
#print axioms BirthSmallRingN2NoGo.InFamily.step
#print axioms BirthSmallRingN2NoGo.family_closedPred
#print axioms BirthSmallRingN2NoGo.family_leaderlessAlong
#print axioms BirthSmallRingN2NoGo.family_physicalNoHit_wordSum
#print axioms BirthSmallRingN2NoGo.smallRingBirthPhaseBound_n2_fails
