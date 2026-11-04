import Leader.Wu.ZeroDivisible.LockCycleRepairs

/-! Exact B-state preservation by the original comparison lifecycle. -/

namespace PPLLAstraR5CompareB

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
open PPLLPostElectionGuard PPLLFableDesignR1
open PPLLAstraDesign2 PPLLAstraDesign3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

def HeadState (s : MainState) : Prop :=
  s = .lock ∨ s = .compare1

def MidState (s : MainState) : Prop :=
  s = .depart ∨ s = .lock ∨ s = .compare1

def PenState (s : MainState) : Prop :=
  s = .equal ∨ MidState s

/-- Role classification by the path/physical role index.
Under 4 <= ψ these cases are disjoint. -/
def BState (ψ k : Nat) (s : MainState) : Prop :=
  if k = 0 then
    HeadState s
  else if k + 1 = ψ then
    s = .compare2
  else if k + 2 = ψ then
    PenState s
  else
    MidState s

@[simp] theorem bState_zero {ψ : Nat} {s : MainState} :
    BState ψ 0 s ↔ HeadState s := by
  simp [BState]

theorem bState_terminal {ψ k : Nat} {s : MainState}
    (h0 : k ≠ 0) (ht : k + 1 = ψ) :
    BState ψ k s ↔ s = .compare2 := by
  simp [BState, h0, ht]

theorem bState_penultimate {ψ k : Nat} {s : MainState}
    (h0 : k ≠ 0) (ht : k + 1 ≠ ψ) (hp : k + 2 = ψ) :
    BState ψ k s ↔ PenState s := by
  simp [BState, h0, ht, hp]

theorem bState_ordinary {ψ k : Nat} {s : MainState}
    (h0 : k ≠ 0) (ht : k + 1 ≠ ψ) (hp : k + 2 ≠ ψ) :
    BState ψ k s ↔ MidState s := by
  simp [BState, h0, ht, hp]

/-! ## Projection facts: arbitrary raw tokens are harmless to these fields -/

private def frameView {ψ : Nat} (u : AgentState ψ) :=
  (u.label, u.path)

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem frame_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    frameView (if p then a else b) =
      if p then frameView a else frameView b := by
  split <;> rfl

private theorem maintain_frame {ψ : Nat} (l r : AgentState ψ) :
    frameView (maintain l r).1 = frameView l ∧
    frameView (maintain l r).2 = frameView r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr, fst_ite, snd_ite, frame_ite]
  all_goals repeat (split <;> simp_all [frameView])
  all_goals grind

private theorem completeWave_frame {ψ : Nat} (l r : AgentState ψ) :
    frameView (completeWave l r).1 = frameView l ∧
    frameView (completeWave l r).2 = frameView r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [completeWave, hl, hr, fst_ite, snd_ite, frame_ite, frameView] <;>
    repeat (first | split) <;> simp_all [frameView]

private theorem wave_frame {ψ : Nat} (l r : AgentState ψ) :
    frameView (wave l r).1 = frameView l ∧
    frameView (wave l r).2 = frameView r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [wave, hl, hr, fst_ite, snd_ite, frame_ite, frameView] <;>
    repeat (first | split) <;> simp_all [frameView]

private theorem dropStray_frame {ψ : Nat} (l r : AgentState ψ) :
    frameView (dropStray l r).1 = frameView l ∧
    frameView (dropStray l r).2 = frameView r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, fst_ite, snd_ite, frame_ite, frameView] <;>
    repeat (first | split) <;> simp_all [frameView]

private theorem landBackward_frame {ψ : Nat} (u : AgentState ψ) :
    frameView (landBackward u) = frameView u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landBackward, hp, ht, frame_ite, frameView] <;>
    repeat (split <;> simp_all [frameView])
  all_goals grind

private theorem landForward_frame {ψ : Nat} (κ : Nat) (u : AgentState ψ) :
    frameView (landForward κ false true u) = frameView u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht, frame_ite, frameView] <;>
    repeat (split <;> simp_all [frameView])
  all_goals grind

private theorem compare_frame {ψ : Nat} (κ : Nat)
    (l r : AgentState ψ) :
    frameView (compareLifecycle κ l r).1 = frameView l ∧
    frameView (compareLifecycle κ l r).2 = frameView r := by
  simp only [compareLifecycle, landBackward_frame, landForward_frame,
    (dropStray_frame _ _).1, (dropStray_frame _ _).2,
    (wave_frame _ _).1, (wave_frame _ _).2,
    (completeWave_frame _ _).1, (completeWave_frame _ _).2,
    (maintain_frame _ _).1, (maintain_frame _ _).2]
  cases hp : l.path <;>
    simp [hp, frame_ite, frameView] <;>
    repeat (split <;> simp_all [frameView])

/-- compareLifecycle never changes physical labels or main paths. -/
theorem compareLifecycle_frame {ψ : Nat} (κ : Nat)
    (l r : AgentState ψ) :
    (compareLifecycle κ l r).1.path = l.path ∧
    (compareLifecycle κ l r).2.path = r.path ∧
    (compareLifecycle κ l r).1.label = l.label ∧
    (compareLifecycle κ l r).2.label = r.label := by
  have h := compare_frame κ l r
  simp only [frameView, Prod.mk.injEq] at h
  exact ⟨h.1.2, h.2.2, h.1.1, h.2.1⟩

/-! Token cleanup/landing can mutate path2 and leader, but not MainState. -/

@[simp] private theorem dropStray_left_state {ψ : Nat}
    (l r : AgentState ψ) :
    (dropStray l r).1.state = l.state := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr] <;>
    repeat (first | split) <;> simp_all

@[simp] private theorem dropStray_right_state {ψ : Nat}
    (l r : AgentState ψ) :
    (dropStray l r).2.state = r.state := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr] <;>
    repeat (first | split) <;> simp_all

@[simp] private theorem landBackward_state {ψ : Nat}
    (u : AgentState ψ) :
    (landBackward u).state = u.state := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landBackward, hp, ht] <;>
    repeat (split <;> simp_all)
  all_goals grind

@[simp] private theorem landForward_state {ψ : Nat}
    (κ : Nat) (u : AgentState ψ) :
    (landForward κ false true u).state = u.state := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht] <;>
    repeat (split <;> simp_all)
  all_goals grind

private def waveCore {ψ : Nat} (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := maintain l r
  let q := completeWave q.1 q.2
  wave q.1 q.2

/-- On a full initiator path, the MainState output is exactly the output of
maintain; completeWave; wave. Raw path2 fields disappear from the state proof. -/
private theorem compare_state_eq_core {ψ pl pb : Nat} (κ : Nat)
    (l r : AgentState ψ) (hp : l.path = .some pl pb) :
    (compareLifecycle κ l r).1.state = (waveCore l r).1.state ∧
    (compareLifecycle κ l r).2.state = (waveCore l r).2.state := by
  simp [compareLifecycle, waveCore, hp]

/-! ## Four local source calculations -/

/-- Physical/path role 0 -> 1. A head never releases to depart. -/
private theorem waveCore_head_mid {ψ bL bR : Nat}
    (h4 : 4 ≤ ψ) (l r : AgentState ψ)
    (hpL : l.path = .some 0 bL)
    (hpR : r.path = .some 1 bR)
    (hL : HeadState l.state) (hR : MidState r.state) :
    HeadState (waveCore l r).1.state ∧
    MidState (waveCore l r).2.state := by
  have hpred : (1 + ψ - 1) % ψ = 0 := by
    have he : 1 + ψ - 1 = ψ := by omega
    rw [he, Nat.mod_self]
  have h0last : (0 : Nat) ≠ ψ - 1 := by omega
  have h1last : (1 : Nat) ≠ ψ - 1 := by omega
  rcases hL with hL | hL <;>
    rcases hR with hR | hR | hR <;>
    simp [waveCore, maintain, completeWave, wave,
      hpL, hpR, hL, hR, HeadState, MidState,
      lockedState, lockerState, waveState,
      hpred, h0last, h1last] <;> omega

/-- Nonboundary successor with both endpoints in ordinary locked/depart states. -/
private theorem waveCore_mid_mid {ψ j bL bR : Nat}
    (hj2 : j + 2 < ψ) (l r : AgentState ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some (j + 1) bR)
    (hL : MidState l.state) (hR : MidState r.state) :
    MidState (waveCore l r).1.state ∧
    MidState (waveCore l r).2.state := by
  have hj : j < ψ := by omega
  have hpred : (j + 1 + ψ - 1) % ψ = j := by
    have he : j + 1 + ψ - 1 = j + ψ := by omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hj]
  have hpred2 : (j + ψ) % ψ = j := by
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hj]
  have hjlast : j ≠ ψ - 1 := by omega
  have hr0 : j + 1 ≠ 0 := by omega
  have hrlast : j + 1 ≠ ψ - 1 := by omega
  rcases hL with hL | hL | hL <;>
    rcases hR with hR | hR | hR <;>
    simp [waveCore, maintain, completeWave, wave,
      hpL, hpR, hL, hR, MidState,
      lockedState, lockerState, waveState,
      hpred, hpred2, hjlast, hr0, hrlast] <;> omega

/-- Delicate ordinary -> penultimate-equal case.
A locked/C1 initiator is unsupported by an equal successor and releases to depart. -/
private theorem waveCore_mid_equal {ψ j bL bR : Nat}
    (hj2 : j + 2 < ψ) (l r : AgentState ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some (j + 1) bR)
    (hL : MidState l.state) (hR : r.state = .equal) :
    MidState (waveCore l r).1.state ∧
    (waveCore l r).2.state = .equal := by
  have hj : j < ψ := by omega
  have hpred : (j + 1 + ψ - 1) % ψ = j := by
    have he : j + 1 + ψ - 1 = j + ψ := by omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hj]
  have hpred2 : (j + ψ) % ψ = j := by
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hj]
  have hjlast : j ≠ ψ - 1 := by omega
  have hr0 : j + 1 ≠ 0 := by omega
  have hrlast : j + 1 ≠ ψ - 1 := by omega
  rcases hL with hL | hL | hL <;>
    simp [waveCore, maintain, completeWave, wave,
      hpL, hpR, hL, hR, MidState,
      lockedState, lockerState, waveState,
      hpred, hpred2, hjlast, hr0, hrlast] <;> omega

/-- Penultimate -> terminal. Lock is acknowledged to C1; C2 remains terminal. -/
private theorem waveCore_pen_terminal {ψ j bL bR : Nat}
    (h4 : 4 ≤ ψ) (hp : j + 2 = ψ)
    (l r : AgentState ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some (j + 1) bR)
    (hL : PenState l.state) (hR : r.state = .compare2) :
    PenState (waveCore l r).1.state ∧
    (waveCore l r).2.state = .compare2 := by
  have hjlast : j ≠ ψ - 1 := by omega
  have hrlast : j + 1 = ψ - 1 := by omega
  rcases hL with hL | hL
  · simp [waveCore, maintain, completeWave, wave,
      hpL, hpR, hL, hR, PenState, MidState,
      lockedState, lockerState, waveState,
      hjlast, hrlast] <;> omega
  · rcases hL with hL | hL | hL <;>
      simp [waveCore, maintain, completeWave, wave,
        hpL, hpR, hL, hR, PenState, MidState,
        lockedState, lockerState, waveState,
        hjlast, hrlast] <;> omega

/-- Cyclic last -> 0. The head remains locked because C2 is a locker. -/
private theorem waveCore_terminal_head {ψ j bL bR : Nat}
    (h4 : 4 ≤ ψ) (ht : j + 1 = ψ)
    (l r : AgentState ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some 0 bR)
    (hL : l.state = .compare2) (hR : HeadState r.state) :
    (waveCore l r).1.state = .compare2 ∧
    HeadState (waveCore l r).2.state := by
  have hjlast : j = ψ - 1 := by omega
  have hpred : (0 + ψ - 1) % ψ = j := by
    have he : 0 + ψ - 1 = ψ - 1 := by omega
    rw [he, Nat.mod_eq_of_lt (by omega)]
    omega
  have hpred2 : (ψ - 1) % ψ = j := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hmod : (ψ - 1) % ψ = ψ - 1 := Nat.mod_eq_of_lt (by omega)
  rcases hR with hR | hR <;>
    simp [waveCore, maintain, completeWave, wave,
      hpL, hpR, hL, hR, HeadState,
      lockedState, lockerState, waveState,
      hjlast, hpred, hpred2, hmod] <;> grind

/-! ## Unified B-state closure -/

/-- Minimal source theorem. No hypothesis mentions AgentState.label,
leader, path2, token action/position/label/bit, or any ancillary register. -/
theorem compareLifecycle_BState
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (κ : Nat) (l r : AgentState ψ)
    (hj : j < ψ)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ k r.state) :
    let q := compareLifecycle κ l r
    BState ψ j q.1.state ∧
    BState ψ k q.2.state ∧
    q.1.path = l.path ∧ q.2.path = r.path ∧
    q.1.label = l.label ∧ q.2.label = r.label := by
  dsimp only
  have hf := compareLifecycle_frame κ l r
  have hc := compare_state_eq_core κ l r hpL
  by_cases h0 : j = 0
  · subst j
    have h1lt : 1 < ψ := by omega
    simp only [Nat.zero_add, Nat.mod_eq_of_lt h1lt] at hk
    subst k
    have h2 : 1 + 1 ≠ ψ := by omega
    have h3 : 1 + 2 ≠ ψ := by omega
    have hL : HeadState l.state := bState_zero.mp hBL
    have hR : MidState r.state :=
      (bState_ordinary (k := 1) (by omega) h2 h3).mp hBR
    have hs := waveCore_head_mid h4 l r hpL hpR hL hR
    have hoL : HeadState (compareLifecycle κ l r).1.state := by
      rw [hc.1]
      exact hs.1
    have hoR : MidState (compareLifecycle κ l r).2.state := by
      rw [hc.2]
      exact hs.2
    exact ⟨bState_zero.mpr hoL,
      (bState_ordinary (k := 1) (by omega) h2 h3).mpr hoR,
      hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
  · by_cases ht : j + 1 = ψ
    · rw [ht, Nat.mod_self] at hk
      subst k
      have hL : l.state = .compare2 :=
        (bState_terminal h0 ht).mp hBL
      have hR : HeadState r.state := bState_zero.mp hBR
      have hs := waveCore_terminal_head h4 ht l r hpL hpR hL hR
      have hoL : (compareLifecycle κ l r).1.state = .compare2 := by
        rw [hc.1]
        exact hs.1
      have hoR : HeadState (compareLifecycle κ l r).2.state := by
        rw [hc.2]
        exact hs.2
      exact ⟨(bState_terminal h0 ht).mpr hoL,
        bState_zero.mpr hoR,
        hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
    · by_cases hp : j + 2 = ψ
      · have hj1lt : j + 1 < ψ := by omega
        rw [Nat.mod_eq_of_lt hj1lt] at hk
        subst k
        have hr0 : j + 1 ≠ 0 := by omega
        have hrt : (j + 1) + 1 = ψ := by omega
        have hL : PenState l.state :=
          (bState_penultimate h0 ht hp).mp hBL
        have hR : r.state = .compare2 :=
          (bState_terminal hr0 hrt).mp hBR
        have hs := waveCore_pen_terminal h4 hp l r hpL hpR hL hR
        have hoL : PenState (compareLifecycle κ l r).1.state := by
          rw [hc.1]
          exact hs.1
        have hoR : (compareLifecycle κ l r).2.state = .compare2 := by
          rw [hc.2]
          exact hs.2
        exact ⟨(bState_penultimate h0 ht hp).mpr hoL,
          (bState_terminal hr0 hrt).mpr hoR,
          hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
      · have hj2lt : j + 2 < ψ := by omega
        have hj1lt : j + 1 < ψ := by omega
        rw [Nat.mod_eq_of_lt hj1lt] at hk
        subst k
        have hL : MidState l.state :=
          (bState_ordinary h0 ht hp).mp hBL
        have hr0 : j + 1 ≠ 0 := by omega
        have hrt : (j + 1) + 1 ≠ ψ := by omega
        by_cases hrp : (j + 1) + 2 = ψ
        · have hRP : PenState r.state :=
            (bState_penultimate hr0 hrt hrp).mp hBR
          rcases hRP with hReq | hRM
          · have hs := waveCore_mid_equal hj2lt l r hpL hpR hL hReq
            have hoL : MidState (compareLifecycle κ l r).1.state := by
              rw [hc.1]
              exact hs.1
            have hoR : PenState (compareLifecycle κ l r).2.state := by
              rw [hc.2]
              exact Or.inl hs.2
            exact ⟨(bState_ordinary h0 ht hp).mpr hoL,
              (bState_penultimate hr0 hrt hrp).mpr hoR,
              hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
          · have hs := waveCore_mid_mid hj2lt l r hpL hpR hL hRM
            have hoL : MidState (compareLifecycle κ l r).1.state := by
              rw [hc.1]
              exact hs.1
            have hoR : PenState (compareLifecycle κ l r).2.state := by
              rw [hc.2]
              exact Or.inr hs.2
            exact ⟨(bState_ordinary h0 ht hp).mpr hoL,
              (bState_penultimate hr0 hrt hrp).mpr hoR,
              hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
        · have hRM : MidState r.state :=
            (bState_ordinary hr0 hrt hrp).mp hBR
          have hs := waveCore_mid_mid hj2lt l r hpL hpR hL hRM
          have hoL : MidState (compareLifecycle κ l r).1.state := by
            rw [hc.1]
            exact hs.1
          have hoR : MidState (compareLifecycle κ l r).2.state := by
            rw [hc.2]
            exact hs.2
          exact ⟨(bState_ordinary h0 ht hp).mpr hoL,
            (bState_ordinary hr0 hrt hrp).mpr hoR,
            hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

/-- Physical/own-path wrapper. The physical label hypotheses are used only
to certify the role interpretation; compareLifecycle itself does not read them. -/
theorem compareLifecycle_BState_own
    {ψ j bL bR : Nat}
    (h4 : 4 ≤ ψ) (κ : Nat) (l r : AgentState ψ)
    (hlabL : l.label.val = j)
    (hlabR : r.label.val = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some ((j + 1) % ψ) bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ ((j + 1) % ψ) r.state) :
    let q := compareLifecycle κ l r
    BState ψ j q.1.state ∧
    BState ψ ((j + 1) % ψ) q.2.state ∧
    q.1.path = l.path ∧ q.2.path = r.path ∧
    q.1.label = l.label ∧ q.2.label = r.label ∧
    q.1.label.val = j ∧
    q.2.label.val = (j + 1) % ψ := by
  have hj : j < ψ := by
    have hlt := l.label.isLt
    omega
  have h := compareLifecycle_BState
    h4 κ l r hj rfl hpL hpR hBL hBR
  dsimp only at h ⊢
  rcases h with ⟨hsL, hsR, hpLo, hpRo, hlLo, hlRo⟩
  refine ⟨hsL, hsR, hpLo, hpRo, hlLo, hlRo, ?_, ?_⟩
  · rw [hlLo, hlabL]
  · rw [hlRo, hlabR]

#check compareLifecycle_frame
#check compareLifecycle_BState
#check compareLifecycle_BState_own
#print axioms compareLifecycle_frame
#print axioms compareLifecycle_BState
#print axioms compareLifecycle_BState_own

end PPLLAstraR5CompareB
