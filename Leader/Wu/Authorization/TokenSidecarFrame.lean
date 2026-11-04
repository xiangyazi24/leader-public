import Leader.Wu.Authorization.ProvenanceMarks
import Leader.Wu.Authorization.ResetDrain
import Leader.Wu.Authorization.GenerationDrain

/-!
# Token-sidecar transport after the comparison prefix

On an original follower pair with both reset flags clear, the complete AuthF
row retains both token scope/mark pairs from `beforeSuppressAuth`. The claim
includes stale sidecars when path2 is empty; token occupancy is a separate
coordinate supplied by the accepted `pipeline_FV` frame.

The four original-input premises disable suppression reset kills and the
conservation replacement. Without them, clearCmpAuth may reset the scope to
line and the mark to zero. A feasible entrance exists already at psi=1 with
both cells follower/reset-free and arbitrary remaining fields. No generator
reachability or unconditional raw-state frame is asserted.
-/

namespace PPLLAuthTokenSidecarFrame

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF

set_option autoImplicit false

abbrev TokenSidecar {ψ : Nat} (u : AuthState ψ) : P2Scope × ProvColor :=
  (u.path2_scope, u.path2_mark)

/-- The literal ORIGINAL suffix after beforeElimination: K4, WRITE, then
conservation against the original pair. -/
def rawSuffix {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ)
    (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2 (k4Kernel hψ) q.1 q.2
  let q := lift2 (writeWithBundle hψ) q.1 q.2
  conserveAuth l r q

theorem pipeline_eq_rawSuffix {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PPLLAuthF.pipeline hψ κ c l r =
      rawSuffix hψ l r (PPLLAuthF.beforeElimination hψ κ c l r) := rfl

/-- Algorithm 14 keeps the token sidecars when its reset-kill sites are
disabled. No core.path2 occupancy premise is used. -/
theorem suppress_tokenSidecar {ψ : Nat} (hψ : ψ > 0) (a b : AuthState ψ)
    (ha : a.core.leader = false)
    (ha' : a.core.reset_cmd = false) (hb' : b.core.reset_cmd = false) :
    TokenSidecar (suppressSigResetKillAuth hψ a b).1 = TokenSidecar a ∧
    TokenSidecar (suppressSigResetKillAuth hψ a b).2 = TokenSidecar b := by
  simp only [suppressSigResetKillAuth, lift2, suppressSigStart, suppressSigMoveReset,
    suppressSigTerminal, suppressSigFinish, suppressSigEcho]
  simp only [ha, ha', hb', Bool.false_eq_true, ite_false, and_false]
  (repeat' split) <;> simp_all [TokenSidecar]

/-- K4/WRITE are sidecar-transparent lift2 stages. Original follower/follower
also disables conserveAuth's responder replacement. -/
theorem rawSuffix_tokenSidecar {ψ : Nat} (hψ : ψ > 0)
    (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false) :
    TokenSidecar (rawSuffix hψ l r q).1 = TokenSidecar q.1 ∧
    TokenSidecar (rawSuffix hψ l r q).2 = TokenSidecar q.2 := by
  simp [rawSuffix, conserveAuth, lift2, hl, hr, TokenSidecar]

/-- Exact missing sidecar companion to PPLLAuthGenDrain.pipeline_FV. -/
theorem pipeline_tokenSidecar {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hl' : l.core.reset_cmd = false) (hr' : r.core.reset_cmd = false) :
    TokenSidecar (PPLLAuthF.pipeline hψ κ c l r).1 =
      TokenSidecar (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).1 ∧
    TokenSidecar (PPLLAuthF.pipeline hψ κ c l r).2 =
      TokenSidecar (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).2 := by
  have hpf := PPLLAuthResetDrain.prefix_facts hψ κ c l r
  dsimp only at hpf
  obtain ⟨b1, -, b3, -, b5, -, -⟩ := hpf
  have hs := suppress_tokenSidecar hψ
    (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).1
    (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).2
    (b5.trans hl) (b1.trans hl') (b3.trans hr')
  rw [← PPLLAuthResetDrain.beforeElimination_eq] at hs
  have hx := rawSuffix_tokenSidecar hψ l r
    (PPLLAuthF.beforeElimination hψ κ c l r) hl hr
  rw [pipeline_eq_rawSuffix]
  exact ⟨hx.1.trans hs.1, hx.2.trans hs.2⟩

private theorem lineSidecar_of_eq {ψ : Nat} (u v : AuthState ψ)
    (γ : ProvColor) (h : TokenSidecar u = TokenSidecar v)
    (hs : v.path2_scope = .line) (hm : v.path2_mark = γ) :
    u.path2_scope = .line ∧ u.path2_mark = γ := by
  exact ⟨(congrArg Prod.fst h).trans hs, (congrArg Prod.snd h).trans hm⟩

/-- Convenient left-endpoint line-sidecar lift for A4/A6/A5 cuts.
Use pipeline_FV separately when core.path2 occupancy is also needed. -/
theorem pipeline_left_lineSidecar {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hl' : l.core.reset_cmd = false) (hr' : r.core.reset_cmd = false)
    (γ : ProvColor)
    (hs : (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).1.path2_scope = .line)
    (hm : (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).1.path2_mark = γ) :
    (PPLLAuthF.pipeline hψ κ c l r).1.path2_scope = .line ∧
    (PPLLAuthF.pipeline hψ κ c l r).1.path2_mark = γ := by
  exact lineSidecar_of_eq (PPLLAuthF.pipeline hψ κ c l r).1
    (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).1 γ
    (pipeline_tokenSidecar hψ κ c l r hl hr hl' hr').1 hs hm

/-- Right-endpoint version. -/
theorem pipeline_right_lineSidecar {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hl' : l.core.reset_cmd = false) (hr' : r.core.reset_cmd = false)
    (γ : ProvColor)
    (hs : (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).2.path2_scope = .line)
    (hm : (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).2.path2_mark = γ) :
    (PPLLAuthF.pipeline hψ κ c l r).2.path2_scope = .line ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.path2_mark = γ := by
  exact lineSidecar_of_eq (PPLLAuthF.pipeline hψ κ c l r).2
    (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).2 γ
    (pipeline_tokenSidecar hψ κ c l r hl hr hl' hr').2 hs hm

#print axioms PPLLAuthTokenSidecarFrame.pipeline_tokenSidecar
#print axioms PPLLAuthTokenSidecarFrame.pipeline_left_lineSidecar
#print axioms PPLLAuthTokenSidecarFrame.pipeline_right_lineSidecar

end PPLLAuthTokenSidecarFrame
