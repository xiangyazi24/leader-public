import Leader.Wu.ZeroDivisible.CheckRepair

set_option autoImplicit false

/-!
# Generic local facts for the round-five CHECK repair

These statements concern arbitrary raw agent records, not a fixed finite
seed. The exchange theorem is explicitly a movement/consumer/CHECK-cut
theorem. It is not a whole-pipeline routing or liveness theorem.
-/

namespace PPLLAstraR5LocalProofs

open PPLL PPLLBirthPatch PPLLBirthPatchM2 PPLLFableDesignR1
open PPLLAstraR5Repair

/-- Either repair preserves the entire record when its existing token is
an action in the control range. No ancillary-field premises are needed. -/
theorem setResult_preserves_control {ψ : Nat} (c : PPLLAstraR5Repair.Cfg)
    (u : AgentState ψ) (t : Path2Info)
    (ht : u.path2 = some t) (hlo : 3 ≤ t.action) (hhi : t.action ≤ 6) :
    setResult c u = u := by
  simp [setResult, preserveToken, ht, hlo, hhi]

/-- The broad comparator preserves every occupied token, including A1/A2. -/
theorem broad_preserves_occupied {ψ : Nat} (u : AgentState ψ) (t : Path2Info)
    (ht : u.path2 = some t) :
    setResult { selective := false } u = u := by
  simp [setResult, preserveToken, ht]

/-- Both guards agree with the original result writer on an empty slot. -/
theorem empty_uses_original {ψ : Nat} (c : PPLLAstraR5Repair.Cfg) (u : AgentState ψ)
    (ht : u.path2 = none) :
    setResult c u = checkSigSetResult u := by
  simp [setResult, preserveToken, ht]

/-- The old broad probe's literal two guarded assignments. -/
def oldBroadResult {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  let u := if u.state = .larger ∧ u.path2 = none then
    { u with path2 := some ⟨0, 0, 0, 4⟩ } else u
  if u.state = .less ∧ u.path2 = none then
    { u with path2 := some ⟨0, 0, 0, 6⟩ } else u

/-- Literal old selective predicate, retained solely for the compatibility proof. -/
def oldPreserveControl {ψ : Nat} (u : AgentState ψ) : Bool :=
  match u.path2 with
  | none => false
  | some p => 3 ≤ p.action && p.action ≤ 6

/-- The old selective probe's literal two guarded assignments. -/
def oldSelectiveResult {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  let u := if u.state = .larger ∧ !oldPreserveControl u then
    { u with path2 := some ⟨0, 0, 0, 4⟩ } else u
  if u.state = .less ∧ !oldPreserveControl u then
    { u with path2 := some ⟨0, 0, 0, 6⟩ } else u

/-- The new broad writer equals the old probe writer on every raw record. -/
theorem broad_eq_old {ψ : Nat} (u : AgentState ψ) :
    setResult { selective := false } u = oldBroadResult u := by
  cases hs : u.state <;> cases ht : u.path2 <;>
    simp [setResult, preserveToken, oldBroadResult, checkSigSetResult, hs, ht]

/-- The new selective writer equals the old probe writer on every raw record. -/
theorem selective_eq_old {ψ : Nat} (u : AgentState ψ) :
    setResult { selective := true } u = oldSelectiveResult u := by
  cases ht : u.path2 with
  | none =>
    cases hs : u.state <;>
      simp [setResult, preserveToken, oldSelectiveResult, oldPreserveControl,
        checkSigSetResult, hs, ht]
  | some t =>
    by_cases hlo : 3 ≤ t.action <;> by_cases hhi : t.action ≤ 6 <;>
      cases hs : u.state <;>
      simp [setResult, preserveToken, oldSelectiveResult, oldPreserveControl,
        checkSigSetResult, hs, ht, hlo, hhi]

/-- A result write changes no main state or main carrier. -/
theorem setResult_main_frame {ψ : Nat} (c : PPLLAstraR5Repair.Cfg) (u : AgentState ψ) :
    (setResult c u).state = u.state ∧
    (setResult c u).path = u.path ∧
    (setResult c u).label = u.label := by
  unfold setResult
  split
  · exact ⟨rfl, rfl, rfl⟩
  · unfold checkSigSetResult
    split <;> simp_all
    split <;> simp_all

/-- Canonical control payload used by CHECK and the disposal stages. -/
def control (a : Nat) : Path2Info := ⟨0, 0, 0, a⟩

private theorem ready_larger {ψ : Nat} (u : AgentState ψ)
    (hs : u.state = .larger) : checkSigSetReadyGuarded u = u := by
  unfold checkSigSetReadyGuarded controlPending
  simp only [hs, reduceCtorEq, or_self, ↓reduceIte]
  unfold checkSigSetReady
  cases u.path <;> simp [hs]

private theorem ready_less {ψ : Nat} (u : AgentState ψ)
    (hs : u.state = .less) : checkSigSetReadyGuarded u = u := by
  unfold checkSigSetReadyGuarded controlPending
  simp only [hs, reduceCtorEq, or_self, ↓reduceIte]
  unfold checkSigSetReady
  cases u.path <;> simp [hs]

/-- At a CHECK entrance, stale opposite verdicts retain their present
control records for either repair, for every choice of the other fields. -/
theorem checkSource_stale_controls {ψ : Nat} (hψ : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) (tl tr : Path2Info)
    (hl : l.state = .larger) (hr : r.state = .less)
    (hlt : l.path2 = some tl) (hrt : r.path2 = some tr)
    (hll : 3 ≤ tl.action) (hlh : tl.action ≤ 6)
    (hrl : 3 ≤ tr.action) (hrh : tr.action ≤ 6) :
    PPLLAstraR5Repair.checkSource hψ c l r = (l, r) := by
  have hrlg := ready_larger l hl
  have hrls := ready_less r hr
  have hsl := setResult_preserves_control c l tl hlt hll hlh
  have hsr := setResult_preserves_control c r tr hrt hrl hrh
  unfold PPLLAstraR5Repair.checkSource
  simp only [hl, hr, waveState, reduceCtorEq, or_self, ↓reduceIte, hrlg, hrls]
  have he : PPLLAstraR5Repair.releaseEqual hψ l r = l := by
    unfold PPLLAstraR5Repair.releaseEqual
    cases l.path <;> cases r.path <;> simp [hl, hr]
  rw [he]
  have hc : checkSigCheckL hψ l = l := by
    unfold checkSigCheckL
    cases l.path with
    | bot => rfl
    | some j b => cases j <;> simp [hl]
  rw [hc]
  have hcr : checkSigCheckR hψ l r = r := by
    unfold checkSigCheckR
    cases r.path <;> simp [hl]
  rw [hcr, hsl, hsr]
  simp [hr]

/-- All adjacent interior stale A4/A6 pairs swap at the actual mover and
survive the consumers and repaired CHECK. This is a stage-cut class theorem,
not a complete-pipeline escape: prefix/suffix and later delivery remain
separate obligations. -/
theorem interior_exchange_survives_check {ψ : Nat} (hψ : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ)
    (hl : l.state = .larger) (hr : r.state = .less)
    (hlt : l.path2 = some (control 4))
    (hrt : r.path2 = some (control 6))
    (hl0 : l.label.val ≠ 0) (hll : l.label.val ≠ ψ - 1)
    (hr0 : r.label.val ≠ 0) (hrl : r.label.val ≠ ψ - 1)
    (_hnext : r.label.val = l.label.val + 1) :
    let q := moveTokens l r
    let q := (sigMoveApplyControlConsume hψ q.1,
              sigMoveApplyControlConsume hψ q.2)
    PPLLAstraR5Repair.checkSource hψ c q.1 q.2 =
      ({ l with path2 := some (control 6) },
       { r with path2 := some (control 4) }) := by
  have hm : moveTokens l r =
      ({ l with path2 := some (control 6) },
       { r with path2 := some (control 4) }) := by
    simp [moveTokens, hlt, hrt, canMoveR, canMoveL, control, dec, hll, hr0]
  simp only [hm]
  have hlf : l.label ≠ (⟨0, hψ⟩ : Fin ψ) := by
    intro h
    exact hl0 (congrArg Fin.val h)
  have hrf : r.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro h
    exact hrl (congrArg Fin.val h)
  simp only [sigMoveApplyControlConsume, control]
  simp only [hlf, hrf, Nat.reduceEqDiff, false_and,
    and_false, or_false, false_or, ↓reduceIte]
  exact checkSource_stale_controls hψ c
    { l with path2 := some (control 6) } { r with path2 := some (control 4) }
    (control 6) (control 4) hl hr rfl rfl
    (by decide) (by decide) (by decide) (by decide)

/-- A rightmost A4 advances through either possible slot in a suffix with
no other A4 and no token kinds besides A4/A6. This is the actual mover,
before any destination consumer. -/
theorem a4_moves_through_empty_or_a6 {ψ : Nat} (l r : AgentState ψ)
    (hlt : l.path2 = some (control 4))
    (hrt : r.path2 = none ∨ r.path2 = some (control 6))
    (hl : l.label.val ≠ ψ - 1) (hr : r.label.val ≠ 0) :
    (moveTokens l r).2.path2 = some (control 4) := by
  rcases hrt with hrt | hrt <;>
    simp [moveTokens, hlt, hrt, canMoveR, canMoveL, control, dec, hl, hr]

/-- Candidate E releases every aligned equal/terminal-C2 instance of its
geometric guard, with all other fields arbitrary. -/
theorem terminal_c2_releases_equal {ψ : Nat} (hψ : 0 < ψ)
    (l r : AgentState ψ) (ll lb rl rb : Nat)
    (hl : l.state = .equal) (hr : r.state = .compare2)
    (hlt : l.path = .some ll lb) (hrt : r.path = .some rl rb)
    (hla : aligned l) (hra : aligned r)
    (hlast : r.label = ⟨ψ - 1, by omega⟩) (hn : ll + 1 = rl) :
    PPLLAstraR5Repair.releaseEqual hψ l r = { l with state := .depart } := by
  simp [PPLLAstraR5Repair.releaseEqual, hl, hr, hlt, hrt, hla, hra, hlast, hn]

end PPLLAstraR5LocalProofs

#check @PPLLAstraR5LocalProofs.setResult_preserves_control
#check @PPLLAstraR5LocalProofs.checkSource_stale_controls
#check @PPLLAstraR5LocalProofs.interior_exchange_survives_check
#check @PPLLAstraR5LocalProofs.a4_moves_through_empty_or_a6
#check @PPLLAstraR5LocalProofs.terminal_c2_releases_equal
#check @PPLLAstraR5Repair.pipeline_nonempty
#print axioms PPLLAstraR5LocalProofs.setResult_preserves_control
#print axioms PPLLAstraR5LocalProofs.broad_preserves_occupied
#print axioms PPLLAstraR5LocalProofs.empty_uses_original
#print axioms PPLLAstraR5LocalProofs.broad_eq_old
#print axioms PPLLAstraR5LocalProofs.selective_eq_old
#print axioms PPLLAstraR5LocalProofs.setResult_main_frame
#print axioms PPLLAstraR5LocalProofs.checkSource_stale_controls
#print axioms PPLLAstraR5LocalProofs.interior_exchange_survives_check
#print axioms PPLLAstraR5LocalProofs.a4_moves_through_empty_or_a6
#print axioms PPLLAstraR5LocalProofs.terminal_c2_releases_equal
#print axioms PPLLAstraR5Repair.pipeline_nonempty
