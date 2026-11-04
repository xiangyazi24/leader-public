import Leader.Wu.ZeroDivisible.CompareTokenFrame
import Leader.Wu.ZeroDivisible.MiddleCutWaveExact

/-!
# Exact C1/C2 wave frame through the R5 comparison prefix

The input is stronger than the B-state frame: each physical role is exactly
C1, except the terminal role which is exactly C2.  Under full own-labelled
successor paths, maintain/completeWave/wave are whole-record identity.  The
wrap edge additionally needs one live path2 token to disable R1 re-emission.
-/

namespace PPLLAstraR5CompareWaveExact

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
open PPLLPostElectionGuard PPLLFableDesignR1
open PPLLAstraDesign2 PPLLAstraDesign3
open PPLLAstraR5CompareTokenFrame PPLLAstraR5SelectedWave

set_option autoImplicit false

/-- Exact prepared-wave state at physical role j. -/
def WaveState (ψ j : Nat) (s : MainState) : Prop :=
  s = (if j + 1 = ψ then MainState.compare2 else MainState.compare1)

/-- Internal exact-wave successor rows are completely inert through
maintain/completeWave/wave.  The right endpoint may be either C1 or the
terminal C2. -/
private theorem internal_beforeDrop_eq
    {ψ j bL bR : Nat}
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hj1 : j + 1 < ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some (j + 1) bR)
    (hL : l.state = .compare1)
    (hR : r.state = .compare1 ∨ r.state = .compare2) :
    beforeDrop l r = (l,r) := by
  have hjlast : j ≠ ψ - 1 := by omega
  have hsucc0 : j + 1 ≠ 0 := by omega
  have hpred : (j + 1 + ψ - 1) % ψ = j := by
    have heq : j + 1 + ψ - 1 = j + ψ := by omega
    rw [heq, Nat.add_mod, Nat.mod_eq_of_lt hj, Nat.mod_self,
      Nat.add_zero, Nat.mod_eq_of_lt hj]
  have hp :
      let q := maintain l r
      completeWave q.1 q.2 = (l,r) := by
    rcases hR with hR | hR <;>
      simp [maintain, completeWave, hpL, hpR, hL, hR,
        lockedState, lockerState, waveState,
        hjlast, hsucc0, hpred, Nat.mod_eq_of_lt hj] <;>
      grind
  dsimp [beforeDrop]
  rw [hp]
  rcases hR with hR | hR <;>
    simp [wave, hpL, hpR, hL, hR,
      lockedState, lockerState, hjlast, hsucc0]

/-- At the terminal/head wrap, exact C2/C1 is also inert through maintenance
and completion.  A live token disables the only remaining wave branch:
boundary re-emission. -/
private theorem wrap_beforeDrop_eq
    {ψ bL bR : Nat}
    (h4 : 4 ≤ ψ)
    (l r : AgentState ψ)
    (hpL : l.path = .some (ψ - 1) bL)
    (hpR : r.path = .some 0 bR)
    (hL : l.state = .compare2)
    (hR : r.state = .compare1)
    (ht : HasToken (l,r)) :
    beforeDrop l r = (l,r) := by
  have hp :
      let q := maintain l r
      completeWave q.1 q.2 = (l,r) := by
    simp [maintain, completeWave, hpL, hpR, hL, hR,
      lockedState, lockerState, waveState,
      Nat.mod_eq_of_lt (show ψ - 1 < ψ by omega)] <;>
      grind
  dsimp [beforeDrop]
  rw [hp]
  exact wave_eq_of_selected_cut (by omega) (l,r)
    ⟨bL, hpL⟩ ⟨bR, hpR⟩
    ⟨hL, Or.inr hR⟩ ht

/-- Exact prepared C1/C2 successor rows make the literal
maintain/completeWave/wave prefix whole-record identity.  No follower,
resident-bit, token-action, or ancillary-field assumptions are used.
Only the wrap edge requires token occupancy, to block re-emission. -/
theorem beforeDrop_exact
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hWL : WaveState ψ j l.state)
    (hWR : WaveState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    beforeDrop l r = (l,r) := by
  by_cases hw : j + 1 = ψ
  · have hjlast : j = ψ - 1 := by omega
    have hk0 : k = 0 := by
      rw [hk, hw, Nat.mod_self]
    have hL : l.state = .compare2 := by
      simpa [WaveState, hw] using hWL
    have hkterm : k + 1 ≠ ψ := by omega
    have hR : r.state = .compare1 := by
      simpa [WaveState, hkterm] using hWR
    have hpL' : l.path = .some (ψ - 1) bL := by
      simpa [hjlast] using hpL
    have hpR' : r.path = .some 0 bR := by
      simpa [hk0] using hpR
    exact wrap_beforeDrop_eq h4 l r hpL' hpR' hL hR
      (hboundary hw)
  · have hj1 : j + 1 < ψ := by omega
    have hk' : k = j + 1 := by
      rw [hk, Nat.mod_eq_of_lt hj1]
    have hL : l.state = .compare1 := by
      simpa [WaveState, hw] using hWL
    have hR : r.state = .compare1 ∨ r.state = .compare2 := by
      by_cases ht : k + 1 = ψ
      · right
        simpa [WaveState, ht] using hWR
      · left
        simpa [WaveState, ht] using hWR
    have hpR' : r.path = .some (j + 1) bR := by
      simpa [hk'] using hpR
    exact internal_beforeDrop_eq l r hj hj1 hpL hpR' hL hR

/-- dropStray modifies only path2. -/
theorem dropStray_states {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).1.state = l.state ∧
    (dropStray l r).2.state = r.state := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr] <;>
    repeat (first | split <;> simp_all)

/-- landBackward may rewrite/delete path2, but never changes MainState. -/
theorem landBackward_state {ψ : Nat} (u : AgentState ψ) :
    (landBackward u).state = u.state := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp [landBackward, ht, hp] <;>
    repeat (split <;> simp_all)
  all_goals grind

/-- landForward may rewrite leader/path2, but never changes MainState. -/
theorem landForward_state {ψ : Nat}
    (κ : Nat) (detect eqBirth : Bool) (u : AgentState ψ) :
    (landForward κ detect eqBirth u).state = u.state := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp [landForward, ht, hp] <;>
    repeat (split <;> simp_all)
  all_goals grind

/-- On the exact wave input, actual compareLifecycle is exactly dropStray
followed by the two R1 landers. -/
theorem compareLifecycle_exact
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ)
    (κ : Nat)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hWL : WaveState ψ j l.state)
    (hWR : WaveState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    compareLifecycle κ l r =
      (landBackward (dropStray l r).1,
       landForward κ false true (dropStray l r).2) := by
  have hpre := beforeDrop_exact
    (ψ:=ψ) (j:=j) (k:=k) (bL:=bL) (bR:=bR)
    h4 l r hj hk hpL hpR hWL hWR hboundary
  unfold PPLLAstraDesign3.compareLifecycle
  rw [hpL]
  change
    (let q := beforeDrop l r
     let q := dropStray q.1 q.2
     (landBackward q.1, landForward κ false true q.2)) =
      (landBackward (dropStray l r).1,
       landForward κ false true (dropStray l r).2)
  rw [hpre]

/-- Consequently the actual comparison lifecycle preserves both exact input
MainState values.  The conclusion does not claim leader/path2 preservation. -/
theorem compareLifecycle_states_carried
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ)
    (κ : Nat)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hWL : WaveState ψ j l.state)
    (hWR : WaveState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    let q := compareLifecycle κ l r
    q.1.state = l.state ∧ q.2.state = r.state := by
  have heq := compareLifecycle_exact
    (ψ:=ψ) (j:=j) (k:=k) (bL:=bL) (bR:=bR)
    h4 κ l r hj hk hpL hpR hWL hWR hboundary
  rw [heq]
  have hd := dropStray_states l r
  exact
    ⟨(landBackward_state (dropStray l r).1).trans hd.1,
     (landForward_state κ false true (dropStray l r).2).trans hd.2⟩

/-- Physical-label wrapper consumed by the whole service-row wave frame.
All wave-state premises refer to the actual own-labelled endpoint roles. -/
theorem compareLifecycle_states
    {ψ bL bR : Nat} (h4 : 4 ≤ ψ) (κ : Nat)
    (l r : AgentState ψ)
    (succ : r.label.val = (l.label.val + 1) % ψ)
    (pl : l.path = .some l.label.val bL)
    (pr : r.path = .some r.label.val bR)
    (hL : PPLLAstraR5MiddleWaveExact.WaveExact ψ l.label.val l.state)
    (hR : PPLLAstraR5MiddleWaveExact.WaveExact ψ r.label.val r.state)
    (hboundary : l.label.val + 1 = ψ → HasToken (l,r)) :
    (compareLifecycle κ l r).1.state = l.state ∧
    (compareLifecycle κ l r).2.state = r.state := by
  exact compareLifecycle_states_carried h4 κ l r l.label.isLt succ pl pr hL hR hboundary

/-! A concrete bounded ψ=4 terminal/head pair. -/

private def witnessCell
    (label : Fin 4) (state : MainState)
    (token : Option Path2Info) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := state, path := .some label.val 0,
    reset := false, carry := false, count := 0,
    label := label, h_field := false,
    path2 := token, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false,
    signal_ws := false }

def witnessWrapL : AgentState 4 :=
  witnessCell ⟨3, by decide⟩ .compare2 (some ⟨0, 0, 3, 2⟩)

def witnessWrapR : AgentState 4 :=
  witnessCell ⟨0, by decide⟩ .compare1 none

/-- The hypotheses are simultaneously satisfiable inside the declared bounded
protocol domain; this is the physical 3→0 wrap and the left slot is occupied. -/
theorem witness_wrap_premises :
    AgentState.inProtocolDomain 2 witnessWrapL ∧
    AgentState.inProtocolDomain 2 witnessWrapR ∧
    witnessWrapL.path = .some 3 0 ∧
    witnessWrapR.path = .some 0 0 ∧
    WaveState 4 3 witnessWrapL.state ∧
    WaveState 4 0 witnessWrapR.state ∧
    HasToken (witnessWrapL,witnessWrapR) := by
  simp [witnessWrapL, witnessWrapR, witnessCell,
    AgentState.inProtocolDomain, WaveState, HasToken]

theorem witness_wrap_beforeDrop :
    beforeDrop witnessWrapL witnessWrapR =
      (witnessWrapL,witnessWrapR) := by
  apply beforeDrop_exact
    (ψ:=4) (j:=3) (k:=0) (bL:=0) (bR:=0)
    (h4:=by decide)
  · decide
  · decide
  · rfl
  · rfl
  · simp [WaveState, witnessWrapL, witnessCell]
  · simp [WaveState, witnessWrapR, witnessCell]
  · intro _
    exact Or.inl (by simp [witnessWrapL, witnessCell])

#check @beforeDrop_exact
#check @compareLifecycle_exact
#check @compareLifecycle_states
#check @witness_wrap_premises
#check @witness_wrap_beforeDrop

#print axioms beforeDrop_exact
#print axioms dropStray_states
#print axioms landBackward_state
#print axioms landForward_state
#print axioms compareLifecycle_exact
#print axioms compareLifecycle_states
#print axioms witness_wrap_premises
#print axioms witness_wrap_beforeDrop

end PPLLAstraR5CompareWaveExact
