import Leader.Wu.Coherence.StrandedPriorityRow
import Leader.Wu.Coherence.FairCycleRingSix

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZV32Protocol

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31

variable {n : Nat}

theorem h3V32 : 0 < 3 := by decide
theorem h23V32 : 2 ≤ 3 := by decide

/-- Priority V3.2 protocol: stranded normalization is the first row branch. -/
def protocolV32 : PopulationProtocol where
  Q := Cell 3 3 48
  Y := Bool
  transition := ZZRowV32.rowV32
  output := fun u => (raw u).leader

/-- Scheduler lift of the priority V3.2 row. -/
def stepV32 (ring : DirectedRing n)
    (C : FC n 3 3 48) (e : Fin n) : FC n 3 3 48 :=
  protocolV32.step ring C e

@[simp] theorem protocolV32_transition :
    protocolV32.transition = ZZRowV32.rowV32 := by
  rfl

/-- The new stranded branch is definitionally first. -/
theorem rowV32_eq_normalize_of_stranded
    (l r : Cell 3 3 48)
    (h : ZZStrandedNormalizerV32.StrandedTokenV3 l r) :
    ZZRowV32.rowV32 l r =
      ZZStrandedNormalizerV32.normalizeStrandedV3 l r := by
  simp [ZZRowV32.rowV32, h]

/-- Outside the stranded family, V3.2 delegates exactly to V3.1. -/
theorem rowV32_eq_rowV3_of_not_stranded
    (l r : Cell 3 3 48)
    (h : ¬ ZZStrandedNormalizerV32.StrandedTokenV3 l r) :
    ZZRowV32.rowV32 l r =
      rowV3 h3V32 (by decide : 0 < 2) h23V32 l r := by
  simp [ZZRowV32.rowV32, h]

/-- Exact token-free compatibility at scheduler-step level. -/
theorem stepV32_tokenFree_eq_stepV3
    (ring : DirectedRing n) (C : FC n 3 3 48) (e : Fin n)
    (hl : (C e).ctl.tok = .none)
    (hr : (C (ring.rightNeighbor e)).ctl.tok = .none) :
    stepV32 ring C e =
      stepV3 h3V32 h23V32 ring C e := by
  have hrow :
      ZZRowV32.rowV32 (C e) (C (ring.rightNeighbor e)) =
        rowV3 h3V32 (by decide : 0 < 2) h23V32
          (C e) (C (ring.rightNeighbor e)) :=
    ZZRowV32.rowV32_tokenFree_eq_rowV3
      (C e) (C (ring.rightNeighbor e)) hl hr
  funext i
  unfold stepV32 stepV3
  change
    (if i = e then
       (ZZRowV32.rowV32
         (C e) (C (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
       (ZZRowV32.rowV32
         (C e) (C (ring.rightNeighbor e))).2
     else C i) =
    (if i = e then
       (rowV3 h3V32 (by decide : 0 < 2) h23V32
         (C e) (C (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
       (rowV3 h3V32 (by decide : 0 < 2) h23V32
         (C e) (C (ring.rightNeighbor e))).2
     else C i)
  rw [hrow]

/-! ## Qualitative target for the compiled n=6 carrier -/

/-- Every current output is follower. -/
def LeaderlessV32 {m : Nat} (C : FC m 3 3 48) : Prop :=
  ∀ i : Fin m, (raw (C i)).leader = false

/-- A finite word is fair-for-repetition iff every ring letter occurs. -/
def FairWord {m : Nat} (w : List (Fin m)) : Prop :=
  ∀ e : Fin m, e ∈ w

/-- Leaderlessness at the start, after every service, and at the final state. -/
def LeaderlessAlongV32 {m : Nat} (ring : DirectedRing m) :
    FC m 3 3 48 → List (Fin m) → Prop
  | C, [] => LeaderlessV32 C
  | C, e :: es =>
      LeaderlessV32 C ∧
        LeaderlessAlongV32 ring (stepV32 ring C e) es

def ring6V32 : DirectedRing 6 := ⟨by decide⟩

/--
Exact qualitative target for campaign row 3.7 on the compiled V3.2 carrier.
A nonempty period which contains every edge, stays leaderless at every prefix,
and returns to its start would yield a fair infinite leaderless execution by
repetition.
-/
def NoFairLeaderlessPeriodicOrbitV32Compiled : Prop :=
  ∀ (C : FC 6 3 3 48) (w : List (Fin 6)),
    w ≠ [] →
    FairWord w →
    LeaderlessAlongV32 ring6V32 C w →
    w.foldl (stepV32 ring6V32) C ≠ C

/-! ## Literal physical family used by the compiled V3.1 witness -/

private def cleanPhys (lab : Fin 3) : R2.Cell 3 3 48 :=
  let b : BoundedAgentState 3 3 :=
    { leader := false
      probe := false
      phase := false
      bit := false
      wait := true
      state := .none
      path := .bot
      reset := false
      carry := false
      count := 0
      label := lab
      h_field := false
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
      signal_ws := false }
  ⟨⟨⟨b, false⟩,
      PPLLExpiringComparisonRepair.freshStall 48⟩, 0⟩

private def labAt (i : Fin 6) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ h3V32⟩

private def ctlS  : ControlV3 := ⟨.sealed,     .none⟩
private def ctlR  : ControlV3 := ⟨.releasing, .none⟩
private def ctlRr : ControlV3 := ⟨.releasing, .release⟩
private def ctlRs : ControlV3 := ⟨.releasing, .scrubL⟩
private def ctlC  : ControlV3 := ⟨.closing,    .none⟩
private def ctlCq : ControlV3 := ⟨.closing,    .seek⟩
private def ctlCw : ControlV3 := ⟨.closing,    .sweep⟩
private def ctlCc : ControlV3 := ⟨.closing,    .commit⟩

private def ctlAt6
    (c0 c1 c2 c3 c4 c5 : ControlV3)
    (i : Fin 6) : ControlV3 :=
  match i.val with
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3
  | 4 => c4
  | _ => c5

private def cfg6
    (c0 c1 c2 c3 c4 c5 : ControlV3) : FC 6 3 3 48 :=
  fun i => ⟨cleanPhys (labAt i), ctlAt6 c0 c1 c2 c3 c4 c5 i⟩

private theorem fin6_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = 1 ∨ i = 2 ∨
      i = 3 ∨ i = 4 ∨ i = 5 := by
  have hi : i.val < 6 := i.isLt
  have hv :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases hv with h | h | h | h | h | h
  · left
    apply Fin.ext
    omega
  · right; left
    apply Fin.ext
    omega
  · right; right; left
    apply Fin.ext
    omega
  · right; right; right; left
    apply Fin.ext
    omega
  · right; right; right; right; left
    apply Fin.ext
    omega
  · right; right; right; right; right
    apply Fin.ext
    omega

private theorem cfg_ext6
    {C D : FC 6 3 3 48}
    (h0 : C 0 = D 0) (h1 : C 1 = D 1)
    (h2 : C 2 = D 2) (h3 : C 3 = D 3)
    (h4 : C 4 = D 4) (h5 : C 5 = D 5) : C = D := by
  funext i
  rcases fin6_cases i with h | h | h | h | h | h
  · subst i; exact h0
  · subst i; exact h1
  · subst i; exact h2
  · subst i; exact h3
  · subst i; exact h4
  · subst i; exact h5

@[simp] private theorem cfg6_leaderless
    (c0 c1 c2 c3 c4 c5 : ControlV3) :
    LeaderlessV32 (cfg6 c0 c1 c2 c3 c4 c5) := by
  intro i
  rcases fin6_cases i with h | h | h | h | h | h
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl

/-- Same anchor as `ZZV31FairCycleA.cycleC`. -/
def compiledBaseC : FC 6 3 3 48 :=
  cfg6 ctlR ctlR ctlRs ctlR ctlR ctlRs

/-! Two explicit boundary repairs. -/
private def cB2 := cfg6 ctlR  ctlR ctlC  ctlCq ctlR ctlRs
private def cB5 := cfg6 ctlCq ctlR ctlC  ctlCq ctlR ctlC

/-! First 3-cell traversal after the repaired boundaries. -/
private def cA1 := cfg6 ctlC  ctlCq ctlC  ctlCq ctlR ctlC
private def cA2 := cfg6 ctlCw ctlC  ctlC  ctlCq ctlR ctlC
private def cA3 := cfg6 ctlC  ctlCw ctlC  ctlCq ctlR ctlC
private def cA4 := cfg6 ctlC  ctlC  ctlCc ctlCq ctlR ctlC
private def cA5 := cfg6 ctlC  ctlCc ctlS  ctlCq ctlR ctlC
private def cA6 := cfg6 ctlS  ctlS  ctlS   ctlCq ctlR ctlC
private def cA7 := cfg6 ctlRr ctlS  ctlS   ctlCq ctlR ctlC
private def cA8 := cfg6 ctlR  ctlRr ctlS   ctlCq ctlR ctlC
private def cA9 := cfg6 ctlR  ctlR  ctlRs  ctlCq ctlR ctlC

/-! Second 3-cell traversal. -/
private def cD1 := cfg6 ctlR ctlR ctlRs ctlC  ctlCq ctlC
private def cD2 := cfg6 ctlR ctlR ctlRs ctlCw ctlC  ctlC
private def cD3 := cfg6 ctlR ctlR ctlRs ctlC  ctlCw ctlC
private def cD4 := cfg6 ctlR ctlR ctlRs ctlC  ctlC  ctlCc
private def cD5 := cfg6 ctlR ctlR ctlRs ctlC  ctlCc ctlS
private def cD6 := cfg6 ctlR ctlR ctlRs ctlS  ctlS  ctlS
private def cD7 := cfg6 ctlR ctlR ctlRs ctlRr ctlS  ctlS
private def cD8 := cfg6 ctlR ctlR ctlRs ctlR  ctlRr ctlS

/-! Boundary 2 and boundary 5 both take the new stranded branch. -/
private theorem step_boundary2 :
    stepV32 ring6V32 compiledBaseC 2 = cB2 := by
  apply cfg_ext6 <;> rfl

private theorem step_boundary5 :
    stepV32 ring6V32 cB2 5 = cB5 := by
  apply cfg_ext6 <;> rfl

/-- The first repaired boundary is genuinely non-stuttering. -/
theorem compiled_boundary2_moves :
    stepV32 ring6V32 compiledBaseC 2 ≠ compiledBaseC := by
  rw [step_boundary2]
  intro h
  have ht := congrArg
    (fun C : FC 6 3 3 48 => (C (2 : Fin 6)).ctl.tok) h
  change TokenV3.none = TokenV3.scrubL at ht
  cases ht

/-!
The first letter of the following nine-letter block is also stranded, because
boundary 5 has changed position 0 from `.none` to `.seek`.
-/
private theorem step_a0 :
    stepV32 ring6V32 cB5 0 = cA1 := by
  apply cfg_ext6 <;> rfl

private theorem step_a1 :
    stepV32 ring6V32 cA1 0 = cA2 := by
  apply cfg_ext6 <;> rfl

private theorem step_a2 :
    stepV32 ring6V32 cA2 0 = cA3 := by
  apply cfg_ext6 <;> rfl

private theorem step_a3 :
    stepV32 ring6V32 cA3 1 = cA4 := by
  apply cfg_ext6 <;> rfl

private theorem step_a4 :
    stepV32 ring6V32 cA4 1 = cA5 := by
  apply cfg_ext6 <;> rfl

private theorem step_a5 :
    stepV32 ring6V32 cA5 0 = cA6 := by
  apply cfg_ext6 <;> rfl

private theorem step_a6 :
    stepV32 ring6V32 cA6 0 = cA7 := by
  apply cfg_ext6 <;> rfl

private theorem step_a7 :
    stepV32 ring6V32 cA7 0 = cA8 := by
  apply cfg_ext6 <;> rfl

private theorem step_a8 :
    stepV32 ring6V32 cA8 1 = cA9 := by
  apply cfg_ext6 <;> rfl

/-!
The first letter of the second nine-letter block is likewise newly stranded;
after it, the remaining eight letters delegate through the ordinary V3.1 wave.
-/
private theorem step_d0 :
    stepV32 ring6V32 cA9 3 = cD1 := by
  apply cfg_ext6 <;> rfl

private theorem step_d1 :
    stepV32 ring6V32 cD1 3 = cD2 := by
  apply cfg_ext6 <;> rfl

private theorem step_d2 :
    stepV32 ring6V32 cD2 3 = cD3 := by
  apply cfg_ext6 <;> rfl

private theorem step_d3 :
    stepV32 ring6V32 cD3 4 = cD4 := by
  apply cfg_ext6 <;> rfl

private theorem step_d4 :
    stepV32 ring6V32 cD4 4 = cD5 := by
  apply cfg_ext6 <;> rfl

private theorem step_d5 :
    stepV32 ring6V32 cD5 3 = cD6 := by
  apply cfg_ext6 <;> rfl

private theorem step_d6 :
    stepV32 ring6V32 cD6 3 = cD7 := by
  apply cfg_ext6 <;> rfl

private theorem step_d7 :
    stepV32 ring6V32 cD7 3 = cD8 := by
  apply cfg_ext6 <;> rfl

private theorem step_d8 :
    stepV32 ring6V32 cD8 4 = compiledBaseC := by
  apply cfg_ext6 <;> rfl

/-- Exactly the compiled V3.1 fair scheduler word. -/
def compiledFairPeriod : List (Fin 6) :=
  [2, 5] ++
    [0, 0, 0, 1, 1, 0, 0, 0, 1] ++
    [3, 3, 3, 4, 4, 3, 3, 3, 4]

/-- Despite the repaired boundary, the full period still closes. -/
theorem v32_compiled_fair_cycle :
    compiledFairPeriod.foldl (stepV32 ring6V32) compiledBaseC =
      compiledBaseC := by
  simp [compiledFairPeriod, List.foldl,
    step_boundary2, step_boundary5,
    step_a0, step_a1, step_a2, step_a3, step_a4,
    step_a5, step_a6, step_a7, step_a8,
    step_d0, step_d1, step_d2, step_d3, step_d4,
    step_d5, step_d6, step_d7, step_d8]

theorem compiledFairPeriod_fair : FairWord compiledFairPeriod := by
  intro e
  rcases fin6_cases e with h | h | h | h | h | h
  · subst e; simp [compiledFairPeriod]
  · subst e; simp [compiledFairPeriod]
  · subst e; simp [compiledFairPeriod]
  · subst e; simp [compiledFairPeriod]
  · subst e; simp [compiledFairPeriod]
  · subst e; simp [compiledFairPeriod]

/-! Small structural helpers: no global trace simp is needed below. -/
private theorem leaderless_nil
    (C : FC 6 3 3 48) (hC : LeaderlessV32 C) :
    LeaderlessAlongV32 ring6V32 C [] := by
  simpa [LeaderlessAlongV32] using hC

private theorem leaderless_cons
    (C D : FC 6 3 3 48) (e : Fin 6) (w : List (Fin 6))
    (hC : LeaderlessV32 C)
    (hstep : stepV32 ring6V32 C e = D)
    (hrest : LeaderlessAlongV32 ring6V32 D w) :
    LeaderlessAlongV32 ring6V32 C (e :: w) := by
  change LeaderlessV32 C ∧
    LeaderlessAlongV32 ring6V32 (stepV32 ring6V32 C e) w
  constructor
  · exact hC
  · rw [hstep]
    exact hrest

/-- Every state on the concrete 20-service trace remains leaderless. -/
theorem compiledFairPeriod_leaderless :
    LeaderlessAlongV32 ring6V32 compiledBaseC compiledFairPeriod := by
  have t20 : LeaderlessAlongV32 ring6V32 compiledBaseC [] := by
    exact leaderless_nil compiledBaseC (by simp [compiledBaseC])
  have t19 : LeaderlessAlongV32 ring6V32 cD8 [4] := by
    exact leaderless_cons cD8 compiledBaseC 4 []
      (by simp [cD8]) step_d8 t20
  have t18 : LeaderlessAlongV32 ring6V32 cD7 [3, 4] := by
    exact leaderless_cons cD7 cD8 3 [4]
      (by simp [cD7]) step_d7 t19
  have t17 : LeaderlessAlongV32 ring6V32 cD6 [3, 3, 4] := by
    exact leaderless_cons cD6 cD7 3 [3, 4]
      (by simp [cD6]) step_d6 t18
  have t16 : LeaderlessAlongV32 ring6V32 cD5 [3, 3, 3, 4] := by
    exact leaderless_cons cD5 cD6 3 [3, 3, 4]
      (by simp [cD5]) step_d5 t17
  have t15 : LeaderlessAlongV32 ring6V32 cD4 [4, 3, 3, 3, 4] := by
    exact leaderless_cons cD4 cD5 4 [3, 3, 3, 4]
      (by simp [cD4]) step_d4 t16
  have t14 : LeaderlessAlongV32 ring6V32 cD3 [4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cD3 cD4 4 [4, 3, 3, 3, 4]
      (by simp [cD3]) step_d3 t15
  have t13 : LeaderlessAlongV32 ring6V32 cD2 [3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cD2 cD3 3 [4, 4, 3, 3, 3, 4]
      (by simp [cD2]) step_d2 t14
  have t12 : LeaderlessAlongV32 ring6V32 cD1
      [3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cD1 cD2 3 [3, 4, 4, 3, 3, 3, 4]
      (by simp [cD1]) step_d1 t13
  have t11 : LeaderlessAlongV32 ring6V32 cA9
      [3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA9 cD1 3 [3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA9]) step_d0 t12
  have t10 : LeaderlessAlongV32 ring6V32 cA8
      [1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA8 cA9 1 [3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA8]) step_a8 t11
  have t9 : LeaderlessAlongV32 ring6V32 cA7
      [0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA7 cA8 0
      [1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA7]) step_a7 t10
  have t8 : LeaderlessAlongV32 ring6V32 cA6
      [0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA6 cA7 0
      [0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA6]) step_a6 t9
  have t7 : LeaderlessAlongV32 ring6V32 cA5
      [0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA5 cA6 0
      [0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA5]) step_a5 t8
  have t6 : LeaderlessAlongV32 ring6V32 cA4
      [1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA4 cA5 1
      [0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA4]) step_a4 t7
  have t5 : LeaderlessAlongV32 ring6V32 cA3
      [1, 1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA3 cA4 1
      [1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA3]) step_a3 t6
  have t4 : LeaderlessAlongV32 ring6V32 cA2
      [0, 1, 1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA2 cA3 0
      [1, 1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA2]) step_a2 t5
  have t3 : LeaderlessAlongV32 ring6V32 cA1
      [0, 0, 1, 1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cA1 cA2 0
      [0, 1, 1, 0, 0, 0, 1, 3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cA1]) step_a1 t4
  have t2 : LeaderlessAlongV32 ring6V32 cB5
      [0, 0, 0, 1, 1, 0, 0, 0, 1,
       3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cB5 cA1 0
      [0, 0, 1, 1, 0, 0, 0, 1,
       3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cB5]) step_a0 t3
  have t1 : LeaderlessAlongV32 ring6V32 cB2
      [5, 0, 0, 0, 1, 1, 0, 0, 0, 1,
       3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons cB2 cB5 5
      [0, 0, 0, 1, 1, 0, 0, 0, 1,
       3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [cB2]) step_boundary5 t2
  have t0 : LeaderlessAlongV32 ring6V32 compiledBaseC
      [2, 5, 0, 0, 0, 1, 1, 0, 0, 0, 1,
       3, 3, 3, 4, 4, 3, 3, 3, 4] := by
    exact leaderless_cons compiledBaseC cB2 2
      [5, 0, 0, 0, 1, 1, 0, 0, 0, 1,
       3, 3, 3, 4, 4, 3, 3, 3, 4]
      (by simp [compiledBaseC]) step_boundary2 t1
  simpa [compiledFairPeriod] using t0

/-- The desired qualitative V3.2 no-period target is false for this wrapper. -/
theorem noFairLeaderlessPeriodicOrbitV32Compiled_false :
    ¬ NoFairLeaderlessPeriodicOrbitV32Compiled := by
  intro h
  have hne := h compiledBaseC compiledFairPeriod
    (by simp [compiledFairPeriod])
    compiledFairPeriod_fair
    compiledFairPeriod_leaderless
  exact hne v32_compiled_fair_cycle

#print axioms ZZV32Protocol.stepV32_tokenFree_eq_stepV3
#print axioms ZZV32Protocol.compiled_boundary2_moves
#print axioms ZZV32Protocol.compiledFairPeriod_leaderless
#print axioms ZZV32Protocol.v32_compiled_fair_cycle
#print axioms ZZV32Protocol.noFairLeaderlessPeriodicOrbitV32Compiled_false

end ZZV32Protocol
