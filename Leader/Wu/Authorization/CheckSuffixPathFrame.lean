import Leader.Wu.Authorization.ProvenanceMarks

/-!
Exact endpoint main-path frames for the CHECK-to-lifecycle suffix.
These statements quantify over raw states and arbitrary configuration. They
preserve `core.path` even when CHECK or forward landing creates a leader.
They make no generator or population-reachability assertion.
-/

set_option autoImplicit false
namespace PPLLAuthCheckSuffixPathFrame

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
variable {ψ : Nat}

theorem fst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
theorem snd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
theorem core_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    (if p then a else b).core = if p then a.core else b.core := by split <;> rfl
theorem path_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl

theorem orphan_path (u : AgentState ψ) : (normalizeOrphan u).path = u.path := by
  cases h : u.path <;> simp [normalizeOrphan, h, path_ite']
theorem carrier_path (u : AgentState ψ) : (normalizeCarrier u).path = u.path := by
  cases h : u.path <;> simp [normalizeCarrier, releaseCongest, h, path_ite']
theorem checkReady_path (u : AgentState ψ) : (checkSigSetReadyGuarded u).path = u.path := by
  cases h : u.path <;> simp [checkSigSetReadyGuarded, checkSigSetReady, h, path_ite']
theorem checkL_path (hψ : ψ > 0) (u : AgentState ψ) : (checkSigCheckL hψ u).path = u.path := by
  unfold checkSigCheckL; split <;> simp [path_ite']
theorem checkR_path (hψ : ψ > 0) (l r : AgentState ψ) : (checkSigCheckR hψ l r).path = r.path := by
  unfold checkSigCheckR; split <;> simp [path_ite']
theorem result_path (u : AgentState ψ) : (checkSigSetResult u).path = u.path := by
  simp [checkSigSetResult, path_ite']
theorem disStart_path (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappearStartL hψ l r).1.path = l.path ∧ (disappearStartL hψ l r).2.path = r.path := by
  simp [disappearStartL, fst_ite, snd_ite, path_ite']
theorem disCarry_path (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappearCarry hψ l r).1.path = l.path ∧ (disappearCarry hψ l r).2.path = r.path := by
  simp [disappearCarry, fst_ite, snd_ite, path_ite']
theorem releaseSuffix_path (l r : AgentState ψ) :
    (releaseReadySuffix l r).1.path = l.path ∧ (releaseReadySuffix l r).2.path = r.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, path_ite']
theorem ackTail_path (l r : AgentState ψ) :
    (ackTail l r).1.path = l.path ∧ (ackTail l r).2.path = r.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, path_ite']
theorem dropStray_path (l r : AgentState ψ) :
    (dropStray l r).1.path = l.path ∧ (dropStray l r).2.path = r.path := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, fst_ite, snd_ite, path_ite']
theorem landBackward_path (u : AgentState ψ) : (landBackward u).path = u.path := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward, hp, ht, path_ite']
/-- Forward equality birth changes leader and token fields, retaining the main path. -/
theorem landForward_path (κ : Nat) (u : AgentState ψ) : (landForward κ false true u).path = u.path := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward, hp, ht, path_ite']

local macro "ppll_path_close" : tactic => `(tactic| first
      | exact ⟨rfl, rfl⟩ | rfl
      | (simp only [AuthState.withCore, AuthState.dropP2, AuthState.setState, AuthState.lineage,
          checkReady_path, checkL_path, checkR_path, result_path, landBackward_path,
          landForward_path, and_self, and_true, true_and];
         first | done | rfl | exact ⟨rfl, rfl⟩))
local macro "ppll_path_split" : tactic =>
  `(tactic| ((repeat' (first | ppll_path_close | (dsimp only) | split)) <;> ppll_path_close))

theorem issue_path (u : AuthState ψ) : (issue u).core.path = u.core.path := by
  unfold issue; ppll_path_split
theorem readyAuth_path (u : AuthState ψ) : (readyAuth u).core.path = u.core.path := by
  unfold readyAuth; ppll_path_split
theorem landBackwardAuth_path (u : AuthState ψ) : (landBackwardAuth u).core.path = u.core.path := by
  unfold landBackwardAuth; ppll_path_split
theorem landForwardAuth_path (κ : Nat) (u : AuthState ψ) : (landForwardAuth κ u).core.path = u.core.path := by
  unfold landForwardAuth; ppll_path_split
theorem validate_path (l r : AuthState ψ) :
    (validateCheck l r).1.core.path = l.core.path ∧ (validateCheck l r).2.core.path = r.core.path := by
  unfold validateCheck demote; ppll_path_split

theorem lift2_path (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path) (l r : AuthState ψ) :
    (lift2 f l r).1.core.path = l.core.path ∧ (lift2 f l r).2.core.path = r.core.path :=
  hf l.core r.core
theorem lift2Life_path (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path) (l r : AuthState ψ) :
    (lift2Life f l r).1.core.path = l.core.path ∧ (lift2Life f l r).2.core.path = r.core.path := by
  have h := hf l.core r.core
  unfold lift2Life; dsimp only
  constructor <;> split <;> simp only [h]
theorem liftLife_path (f : AgentState ψ → AgentState ψ) (hf : ∀ a, (f a).path = a.path)
    (u : AuthState ψ) : (liftLife f u).core.path = u.core.path := by
  unfold liftLife; dsimp only; split <;> exact hf u.core

/-- CHECK preserves both main paths, including its terminal leader assignment. -/
theorem checkSource_path (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    (checkSourceAuth hψ c l r).1.core.path = l.core.path ∧
      (checkSourceAuth hψ c l r).2.core.path = r.core.path := by
  simp only [checkSourceAuth, fst_ite, snd_ite, core_ite, path_ite', issue_path, readyAuth_path,
    validate_path, AuthState.withCore, AuthState.lineage, checkL_path, checkR_path,
    checkReady_path, ite_self, and_self]
/-- DISAPPEAR changes lottery, state and token fields while retaining both main paths. -/
theorem disappear_path (hψ : ψ > 0) (l r : AuthState ψ) :
    (disappearAuth hψ l r).1.core.path = l.core.path ∧ (disappearAuth hψ l r).2.core.path = r.core.path := by
  have h1 := lift2_path (disappearStartL hψ) (disStart_path hψ)
  have h2 := lift2_path (disappearCarry hψ) (disCarry_path hψ)
  unfold disappearAuth; dsimp only
  split <;> simp only [h2, h1, true_and, and_self] <;> ppll_path_close
/-- Lifecycle normalization and ready-suffix release preserve both main paths. -/
theorem repair_path (l r : AuthState ψ) :
    (repairAuth l r).1.core.path = l.core.path ∧ (repairAuth l r).2.core.path = r.core.path := by
  have hc : ∀ a : AgentState ψ, (normalizeCarrier (normalizeOrphan a)).path = a.path :=
    fun a => (carrier_path _).trans (orphan_path a)
  have hl := liftLife_path _ hc
  have hr := lift2Life_path (ψ := ψ) releaseReadySuffix releaseSuffix_path
  have ha : ∀ a b : AuthState ψ, (ackTailAuth a b).1.core.path = a.core.path ∧
      (ackTailAuth a b).2.core.path = b.core.path := by
    intro a b; unfold ackTailAuth; split
    · exact lift2_path ackTail ackTail_path a b
    · exact ⟨rfl, rfl⟩
  simp only [repairAuth, ha, hr, hl, and_self]
theorem maintain_path (l r : AuthState ψ) :
    (maintainAuth l r).1.core.path = l.core.path ∧ (maintainAuth l r).2.core.path = r.core.path := by
  unfold maintainAuth; ppll_path_split
theorem completeWave_path (l r : AuthState ψ) :
    (completeWaveAuth l r).1.core.path = l.core.path ∧ (completeWaveAuth l r).2.core.path = r.core.path := by
  unfold completeWaveAuth; ppll_path_split
theorem wave_path (l r : AuthState ψ) :
    (waveAuth l r).1.core.path = l.core.path ∧ (waveAuth l r).2.core.path = r.core.path := by
  unfold waveAuth; ppll_path_split
/-- Comparison maintenance and both token landings preserve both main paths. -/
theorem compare_path (κ : Nat) (l r : AuthState ψ) :
    (compareLifecycleAuth κ l r).1.core.path = l.core.path ∧
      (compareLifecycleAuth κ l r).2.core.path = r.core.path := by
  have hd := lift2_path (ψ := ψ) dropStray dropStray_path
  unfold compareLifecycleAuth; dsimp only
  split
  all_goals (try split)
  all_goals simp only [landBackwardAuth_path, landForwardAuth_path, hd, wave_path,
    completeWave_path, maintain_path, AuthState.setState, and_self]

/-- The original four stages, generalized over the protocol configuration. -/
def checkSuffixC (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := checkSourceAuth hψ c l r
  let q := disappearAuth hψ q.1 q.2
  let q := repairAuth q.1 q.2
  compareLifecycleAuth κ q.1 q.2

/-- The literal four-stage suffix preserves each endpoint main path without premises. -/
theorem checkSuffixC_path (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    (checkSuffixC hψ κ c l r).1.core.path = l.core.path ∧
      (checkSuffixC hψ κ c l r).2.core.path = r.core.path := by
  unfold checkSuffixC; dsimp only
  have h1 := checkSource_path hψ c l r
  generalize checkSourceAuth hψ c l r = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have h2 := disappear_path hψ l1 r1
  generalize disappearAuth hψ l1 r1 = q2 at h2 ⊢
  obtain ⟨l2, r2⟩ := q2
  have h3 := repair_path l2 r2
  generalize repairAuth l2 r2 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 := compare_path κ l3 r3
  exact ⟨h4.1.trans (h3.1.trans (h2.1.trans h1.1)),
    h4.2.trans (h3.2.trans (h2.2.trans h1.2))⟩

/-- A pathless initiator remains pathless throughout the suffix. -/
theorem checkSuffixC_left_hole (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (hl : l.core.path = .bot) :
    (checkSuffixC hψ κ c l r).1.core.path = .bot :=
  (checkSuffixC_path hψ κ c l r).1.trans hl

#print axioms checkSuffixC_path
#print axioms checkSuffixC_left_hole

end PPLLAuthCheckSuffixPathFrame
