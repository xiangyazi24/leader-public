import Leader.Wu.Authorization.MoveHole
import Leader.Wu.Authorization.CheckSuffixPathFrame
import Leader.Wu.Authorization.GenerationDrain

/-!
# Main-path holes after the actual CLEAN cut

The original pipeline cannot refill both endpoints after its actual CLEAN cut
has a main-path hole. This is cut persistence, not a theorem that GENSIG
preserves an input hole. The literal cut is defined below and factored by rfl.

Q73 supplies the raw stage frames. The T2--T7 proof uses the opaque-pair shape
compiled in TerminalReady, generalized here to every cfg. MoveHole remains
compiled internal support; its standalone main scanner is unresolved. This
new assembly requires its own full verification before acceptance.
-/

set_option autoImplicit false

namespace PPLLAuthCheckPostCleanHole

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState
open PPLLAuthFPairHole

variable {ψ : Nat}

private theorem fst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem path_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem core_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    (if p then a else b).core = if p then a.core else b.core := by
  split <;> rfl

private theorem pairHole_of_paths
    (q : AuthState ψ × AuthState ψ) (l r : AuthState ψ)
    (hp : q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path)
    (h : PairHole (l, r)) : PairHole q := by
  unfold PairHole at h ⊢
  rw [hp.1, hp.2]
  exact h

private theorem clearCmpAuth_path' (u : AuthState ψ) :
    (clearCmpAuth u).core.path = .bot := by
  simp [clearCmpAuth, PPLLPostElectionGuard.clearCmp]

private theorem lift2_paths
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) :
    (lift2 f l r).1.core.path = l.core.path ∧
      (lift2 f l r).2.core.path = r.core.path :=
  hf l.core r.core

private theorem lift2Life_paths
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) :
    (lift2Life f l r).1.core.path = l.core.path ∧
      (lift2Life f l r).2.core.path = r.core.path := by
  have h := hf l.core r.core
  unfold lift2Life
  dsimp only
  constructor <;> split <;> simp only [h]

private theorem liftLife_path
    (f : AgentState ψ → AgentState ψ)
    (hf : ∀ a, (f a).path = a.path) (u : AuthState ψ) :
    (liftLife f u).core.path = u.core.path := by
  unfold liftLife
  dsimp only
  split <;> exact hf u.core

private theorem lift2_pairHole_of_paths
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) (h : PairHole (l, r)) :
    PairHole (lift2 f l r) :=
  pairHole_of_paths _ l r (lift2_paths f hf l r) h

private theorem releaseSource_paths (hψ : ψ > 0) (l r : AgentState ψ) :
    (releaseSource hψ l r).1.path = l.path ∧
      (releaseSource hψ l r).2.path = r.path := by
  simp [releaseSource, fst_ite, snd_ite, path_ite]

private theorem release_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (lift2Life (releaseSource hψ) l r) :=
  pairHole_of_paths _ l r
    (lift2Life_paths (releaseSource hψ) (releaseSource_paths hψ) l r) h

private theorem eliminateSig_left_path (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.path = l.path := by
  simp [eliminateSig, fst_ite, path_ite]

private theorem eliminateSig_right_bot (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.path = .bot) :
    (eliminateSig hψ l r).2.path = .bot := by
  simp [eliminateSig, snd_ite, path_ite, hr]

private theorem eliminate_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (lift2 (eliminateSig hψ) l r) := by
  unfold PairHole at h ⊢
  rcases h with hl | hr
  · left
    change (eliminateSig hψ l.core r.core).1.path = .bot
    exact (eliminateSig_left_path hψ l.core r.core).trans hl
  · right
    change (eliminateSig hψ l.core r.core).2.path = .bot
    exact eliminateSig_right_bot hψ l.core r.core hr

private theorem dropStale_bot (u : AgentState ψ) (h : u.path = .bot) :
    (dropStale u).path = .bot := by
  simp [dropStale, h]

private theorem liftLife_dropStale_bot (u : AuthState ψ)
    (h : u.core.path = .bot) :
    (liftLife dropStale u).core.path = .bot := by
  unfold liftLife
  dsimp only
  split <;> exact dropStale_bot u.core h

private theorem dropStale_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (liftLife dropStale l, liftLife dropStale r) := by
  unfold PairHole at h ⊢
  rcases h with hl | hr
  · exact Or.inl (liftLife_dropStale_bot l hl)
  · exact Or.inr (liftLife_dropStale_bot r hr)

private theorem preCheckReset_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (preCheckResetAuth l r) := by
  unfold PairHole at h ⊢
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · left
    simp [preCheckResetAuth, clearCmpAuth_path', core_ite, path_ite, hl]
  · right
    simp [preCheckResetAuth, clearCmpAuth_path', core_ite, path_ite, hr]

private theorem orphan_path_local (u : AgentState ψ) :
    (normalizeOrphan u).path = u.path := by
  cases h : u.path <;> simp [normalizeOrphan, h, path_ite]

private theorem carrier_path_local (u : AgentState ψ) :
    (normalizeCarrier u).path = u.path := by
  cases h : u.path <;>
    simp [normalizeCarrier, releaseCongest, h, path_ite]

private theorem normalizeReady_path_local (u : AgentState ψ) :
    (normalizeReady u).path = u.path := by
  cases h : u.path <;>
    simp [normalizeReady, path_ite, orphan_path_local, carrier_path_local, h]

private theorem normalizeReady_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (liftLife normalizeReady l, liftLife normalizeReady r) :=
  pairHole_of_paths _ l r
    ⟨liftLife_path normalizeReady normalizeReady_path_local l,
      liftLife_path normalizeReady normalizeReady_path_local r⟩ h

private theorem checkSuffix_pairHole
    (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (h : PairHole (l, r)) :
    PairHole (PPLLAuthCheckSuffixPathFrame.checkSuffixC hψ κ c l r) :=
  pairHole_of_paths _ l r
    (PPLLAuthCheckSuffixPathFrame.checkSuffixC_path hψ κ c l r) h

private theorem suppressStart_paths (l r : AgentState ψ) :
    (suppressSigStart l r).1.path = l.path ∧
      (suppressSigStart l r).2.path = r.path := by
  simp [suppressSigStart, fst_ite, snd_ite, path_ite]

private theorem suppressMove_paths (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.path = l.path ∧
      (suppressSigMoveReset l r).2.path = r.path := by
  simp [suppressSigMoveReset, fst_ite, snd_ite, path_ite]

private theorem suppressTerminal_paths (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.path = l.path ∧
      (suppressSigTerminal hψ l r).2.path = r.path := by
  simp [suppressSigTerminal, fst_ite, snd_ite, path_ite]

private theorem suppressEcho_paths (l r : AgentState ψ) :
    (suppressSigEcho l r).1.path = l.path ∧
      (suppressSigEcho l r).2.path = r.path := by
  simp [suppressSigEcho, fst_ite, snd_ite, path_ite]

private theorem suppressFinish_paths (l r : AgentState ψ) :
    (suppressSigFinish l r).1.path = l.path ∧
      (suppressSigFinish l r).2.path = r.path := by
  simp [suppressSigFinish, fst_ite, snd_ite, path_ite]

private def killReset (u : AuthState ψ) : AuthState ψ :=
  if u.core.reset_cmd then clearCmpAuth u else u

private theorem killReset_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (killReset l, killReset r) := by
  unfold PairHole at h ⊢
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · left
    simp [killReset, clearCmpAuth_path', core_ite, path_ite, hl]
  · right
    simp [killReset, clearCmpAuth_path', core_ite, path_ite, hr]

private def suppressFactored (hψ : ψ > 0) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q0 := lift2 suppressSigStart l r
  let q0k := (killReset q0.1, killReset q0.2)
  let q1 := lift2 suppressSigMoveReset q0k.1 q0k.2
  let q1k := (killReset q1.1, killReset q1.2)
  let q2 := lift2 (suppressSigTerminal hψ) q1k.1 q1k.2
  let q3 := lift2 suppressSigEcho q2.1 q2.2
  lift2 suppressSigFinish q3.1 q3.2

private theorem suppressFactored_eq (hψ : ψ > 0) (l r : AuthState ψ) :
    suppressSigResetKillAuth hψ l r = suppressFactored hψ l r := by
  rfl

private theorem suppress_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (suppressSigResetKillAuth hψ l r) := by
  rw [suppressFactored_eq]
  let q0 := lift2 suppressSigStart l r
  have h0 : PairHole q0 :=
    lift2_pairHole_of_paths suppressSigStart suppressStart_paths l r h
  let q0k := (killReset q0.1, killReset q0.2)
  have h0k : PairHole q0k := killReset_pairHole q0.1 q0.2 h0
  let q1 := lift2 suppressSigMoveReset q0k.1 q0k.2
  have h1 : PairHole q1 :=
    lift2_pairHole_of_paths suppressSigMoveReset suppressMove_paths q0k.1 q0k.2 h0k
  let q1k := (killReset q1.1, killReset q1.2)
  have h1k : PairHole q1k := killReset_pairHole q1.1 q1.2 h1
  let q2 := lift2 (suppressSigTerminal hψ) q1k.1 q1k.2
  have h2 : PairHole q2 :=
    lift2_pairHole_of_paths (suppressSigTerminal hψ) (suppressTerminal_paths hψ)
      q1k.1 q1k.2 h1k
  let q3 := lift2 suppressSigEcho q2.1 q2.2
  have h3 : PairHole q3 :=
    lift2_pairHole_of_paths suppressSigEcho suppressEcho_paths q2.1 q2.2 h2
  let q4 := lift2 suppressSigFinish q3.1 q3.2
  have h4 : PairHole q4 :=
    lift2_pairHole_of_paths suppressSigFinish suppressFinish_paths q3.1 q3.2 h3
  exact h4

private def kernelWriteAuth (hψ : ψ > 0) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := lift2 (k4Kernel hψ) l r
  lift2 (writeWithBundle hψ) q.1 q.2

private theorem kernelWrite_paths (hψ : ψ > 0) (l r : AuthState ψ) :
    (kernelWriteAuth hψ l r).1.core.path = l.core.path ∧
      (kernelWriteAuth hψ l r).2.core.path = r.core.path := by
  have hw := PPLLAuthGenDrain.suffix_WF hψ l.core r.core
  unfold PPLLAuthGenDrain.WFrame.WF at hw
  unfold kernelWriteAuth
  simp only [PPLLAuthF.lift2]
  exact ⟨hw.1.2.1, hw.2.2.1⟩

private theorem kernelWrite_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (kernelWriteAuth hψ l r) :=
  pairHole_of_paths _ l r (kernelWrite_paths hψ l r) h

private theorem conserve_pairHole
    (originalL originalR : AuthState ψ) (q : AuthState ψ × AuthState ψ)
    (h : PairHole q) :
    PairHole (conserveAuth originalL originalR q) := by
  unfold PairHole at h ⊢
  cases hL : originalL.core.leader <;> cases hR : originalR.core.leader <;>
    cases hA : q.1.core.leader <;> cases hB : q.2.core.leader <;>
    simp_all [conserveAuth, conserve, hL, hR, hA, hB, replacement,
      clearCmpAuth, PPLLPostElectionGuard.clearCmp]

/-- Literal T2--T7 cut: release, eliminate, MOVE, stale drop, reset precheck,
and normalizeReady. The proof abstracts each raw pair before composing frames. -/
private def afterCleanToNormalize (hp : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp c q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

private theorem afterCleanToNormalize_pairHole (hp : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : PairHole (l,r)) : PairHole (afterCleanToNormalize hp c l r) := by
  unfold afterCleanToNormalize
  have h2 := release_pairHole hp l r h
  generalize lift2Life (releaseSource hp) l r = q2 at h2 ⊢
  rcases q2 with ⟨l2,r2⟩
  dsimp only at h2 ⊢
  have h3 := eliminate_pairHole hp l2 r2 h2
  generalize lift2 (eliminateSig hp) l2 r2 = q3 at h3 ⊢
  rcases q3 with ⟨l3,r3⟩
  dsimp only at h3 ⊢
  have h4 : PairHole (moveSourceAuth hp c l3 r3) :=
    PPLLAuthFPairHole.moveSourceAuth_pairHole hp c l3 r3 h3
  generalize moveSourceAuth hp c l3 r3 = q4 at h4 ⊢
  rcases q4 with ⟨l4,r4⟩
  dsimp only at h4 ⊢
  have h5 := dropStale_pairHole l4 r4 h4
  have h6 := preCheckReset_pairHole (liftLife dropStale l4) (liftLife dropStale r4) h5
  generalize preCheckResetAuth (liftLife dropStale l4) (liftLife dropStale r4) = q6 at h6 ⊢
  rcases q6 with ⟨l6,r6⟩
  exact normalizeReady_pairHole l6 r6 h6

/-- Final reset suppression, kernel/WRITE and conservation tail on raw inputs. -/
private def finalTail (hp : ψ > 0) (originalL originalR l r : AuthState ψ) :=
  let q := suppressSigResetKillAuth hp l r
  let q := kernelWriteAuth hp q.1 q.2
  conserveAuth originalL originalR q

private theorem finalTail_pairHole (hp : ψ > 0)
    (originalL originalR l r : AuthState ψ) (h : PairHole (l,r)) :
    PairHole (finalTail hp originalL originalR l r) := by
  unfold finalTail
  have h12 := suppress_pairHole hp l r h
  generalize suppressSigResetKillAuth hp l r = q12 at h12 ⊢
  rcases q12 with ⟨l12,r12⟩
  change PairHole (conserveAuth originalL originalR (kernelWriteAuth hp l12 r12))
  have h14 := kernelWrite_pairHole hp l12 r12 h12
  generalize kernelWriteAuth hp l12 r12 = q14 at h14 ⊢
  exact conserve_pairHole originalL originalR q14 h14

/-- Raw CHECK-to-final cut, separated to keep proof composition opaque. -/
private def afterNormalizeToFinal (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (originalL originalR l r : AuthState ψ) :=
  let q := PPLLAuthCheckSuffixPathFrame.checkSuffixC hp κ c l r
  finalTail hp originalL originalR q.1 q.2

private theorem afterNormalizeToFinal_pairHole (hp : ψ > 0) (κ : Nat)
    (c : PPLLAuthF.Cfg) (originalL originalR l r : AuthState ψ)
    (h : PairHole (l,r)) :
    PairHole (afterNormalizeToFinal hp κ c originalL originalR l r) := by
  unfold afterNormalizeToFinal
  have hs := checkSuffix_pairHole hp κ c l r h
  generalize PPLLAuthCheckSuffixPathFrame.checkSuffixC hp κ c l r = q at hs ⊢
  rcases q with ⟨a,b⟩
  exact finalTail_pairHole hp originalL originalR a b hs

/-- Literal original suffix beginning immediately after CLEAN. Original inputs
are used only by final conservation; all cfg and raw states are unrestricted. -/
def afterCleanToFinal
    (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (originalL originalR a b : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := afterCleanToNormalize hψ c a b
  afterNormalizeToFinal hψ κ c originalL originalR q.1 q.2

/-- A raw post-CLEAN pair hole survives the original full suffix. No follower,
reset, token, state, or mark hypotheses are imposed. -/
theorem afterCleanToFinal_pairHole
    (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (originalL originalR a b : AuthState ψ)
    (h : PairHole (a, b)) :
    PairHole (afterCleanToFinal hψ κ c originalL originalR a b) := by
  unfold afterCleanToFinal
  have h7 := afterCleanToNormalize_pairHole hψ c a b h
  generalize afterCleanToNormalize hψ c a b = q7 at h7 ⊢
  rcases q7 with ⟨l7,r7⟩
  exact afterNormalizeToFinal_pairHole hψ κ c originalL originalR l7 r7 h7

/-- The exact cut in pipeline immediately after pPsiProbeWall + GENSIG + CLEAN. -/
def postCleanCut
    (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2 (pPsiProbeWall hψ) l r
  let q := genSigAuth hψ κ q.1 q.2
  cleanSourceAuth hψ c q.1 q.2

/-- Definitional factorization of the original PPLLAuthF.pipeline at postCleanCut. -/
theorem pipeline_factor_postClean
    (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) :
    PPLLAuthF.pipeline hψ κ c l r =
      let q := postCleanCut hψ κ c l r
      afterCleanToFinal hψ κ c l r q.1 q.2 := by
  rfl

/-- Thin actual-pipeline corollary: GENSIG is before the premise, not inside
an unconditional hole theorem. -/
theorem pipeline_pairHole_of_postClean
    (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ)
    (h : PairHole (postCleanCut hψ κ c l r)) :
    PairHole (PPLLAuthF.pipeline hψ κ c l r) := by
  rw [pipeline_factor_postClean]
  let q := postCleanCut hψ κ c l r
  change PairHole (afterCleanToFinal hψ κ c l r q.1 q.2)
  exact afterCleanToFinal_pairHole hψ κ c l r q.1 q.2 h

#print axioms PPLLAuthCheckPostCleanHole.afterCleanToFinal_pairHole
#print axioms PPLLAuthCheckPostCleanHole.pipeline_pairHole_of_postClean

end PPLLAuthCheckPostCleanHole
