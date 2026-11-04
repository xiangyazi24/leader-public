import Leader.Wu.Comparison.WaveObstruction
import Leader.Wu.Protocol.DomainClosure
import Leader.Wu.Protocol.FiniteState

/-!
# Executable moved-carrier comparison repair

T9 and T18 impose two independent physical requirements. A completed signal
must not compare against its own source merely because it is still aligned at
label zero; after a real group crossing it must be able to start comparison.
And the fresh-start assignment must not overwrite an already active lock or
return wave.

This module defines a separately named research protocol. Each agent carries
one counted Boolean attached only to payload-zero `path`: it records whether
that trailing component has crossed a physically observed stable terminal-to-
zero edge. GENSIG birth and every path replacement clear it; SIGMOVE is the only
stage that can set it; CMP_UPDATE consumes it on sight. The field is ordinary
executable state, so arbitrary initialization may forge it. The positive
results below concern transition behavior and canonical lifecycle preservation,
not unproved authentication of arbitrary initial values.
-/

namespace PPLLAuthorizedComparisonRepair

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain

/-- Audit-level executable state for the moved-carrier repair. `path0Crossed`
is meaningful only when `core.path` is a payload-zero component. -/
structure AuthorizedAgentState (ψ : Nat) where
  core : AgentState ψ
  path0Crossed : Bool
  deriving DecidableEq, Repr

/-- Canonicalize authorization: absent and nonzero path components cannot carry
permission to start a fresh comparison wave. -/
def normalizePermit (s : AgentState ψ) (permit : Bool) : Bool :=
  match s.path with
  | .some 0 _ => permit
  | _ => false

/-- Fail-closed update for a stage that may create, clear, or replace `path`.
Only an exactly retained physical path can retain its old authorization. -/
def reconcilePermit (old : AuthorizedAgentState ψ) (out : AgentState ψ) : Bool :=
  if out.path = old.core.path then normalizePermit out old.path0Crossed
  else false

/-- Pair adapter for stages that have no special authorization-creation event. -/
def authorizedReconcile
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := f l.core r.core
  (⟨q.1, reconcilePermit l q.1⟩,
    ⟨q.2, reconcilePermit r q.2⟩)

/-- A stable local label edge in the current physical pair. -/
def stableSuccessor (hψ : ψ > 0)
    (l r : AgentState ψ) : Bool :=
  decide (r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)

/-- The physical edge is the stable terminal-to-zero group boundary. -/
def stableWrap (hψ : ψ > 0) (l r : AgentState ψ) : Bool :=
  stableSuccessor hψ l r &&
    decide (l.label = ⟨ψ - 1, by omega⟩)

/-- Algorithm 2 with fail-closed authorization under any label repair. A marker
survives only if the endpoint label and path both survive exactly. -/
def authorizedPPsi (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := pPsi hψ l.core r.core
  let lp := if q.1.label = l.core.label then reconcilePermit l q.1 else false
  let rp := if q.2.label = r.core.label then reconcilePermit r q.2 else false
  (⟨q.1, lp⟩, ⟨q.2, rp⟩)

/-- Saturated GENSIG birth/replacement clears authorization; retained old paths
preserve it through `reconcilePermit`. -/
def authorizedGenSig (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (genSigSaturated hψ κ) l r

/-- CLEAN_SIG clears authorization exactly when it clears/replaces the path. -/
def authorizedCleanSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (cleanSig hψ) l r

/-- ELIMINATE_SIG clears authorization with the eliminated path. -/
def authorizedEliminateSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (eliminateSig hψ) l r

/-- Detect the exact Algorithm-10 path transfer in the already-computed physical
result. This executable Boolean is a transition event, not ghost history. -/
def pathMovedRight (l r outL outR : AgentState ψ) : Bool :=
  decide (l.path ≠ .bot) && decide (r.path = .bot) &&
    decide (outL.path = .bot) && decide (outR.path = l.path)

/-- SIGMOVE carries authorization with payload zero. A stable terminal-to-zero
transfer sets the bit; a malformed transfer or any nonzero payload clears it. -/
def authorizedSigMove (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := sigMove hψ l.core r.core
  if _hmoved : pathMovedRight l.core r.core q.1 q.2 = true then
    let receiverPermit := match l.core.path with
      | .some 0 _ =>
          if stableSuccessor hψ l.core r.core then
            l.path0Crossed || stableWrap hψ l.core r.core
          else false
      | _ => false
    (⟨q.1, false⟩, ⟨q.2, normalizePermit q.2 receiverPermit⟩)
  else
    (⟨q.1, reconcilePermit l q.1⟩,
      ⟨q.2, reconcilePermit r q.2⟩)

/-- CHECK does not move `path`; reconciliation merely normalizes malformed
standalone authorization. -/
def authorizedCheckSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (checkSig hψ) l r

/-- DISAPPEAR changes comparison control but not path movement. -/
def authorizedDisappear (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (disappear hψ) l r

/-- States belonging to an in-flight Algorithm-7 wave must never be reset by a
fresh moved-carrier start. -/
def comparisonActive : MainState → Bool
  | .congest | .lock | .compare1 | .compare2 => true
  | _ => false

/-- A fresh state wave is authorized only for a moved payload-zero component at
label zero. This executable guard consumes a counted bit; it never inspects a
proof-only source mark. -/
def freshComparisonStart (hψ : ψ > 0)
    (u : AuthorizedAgentState ψ) : Bool :=
  match u.core.path with
  | .some 0 _ => decide (u.core.label = ⟨0, hψ⟩) && u.path0Crossed
  | _ => false

/-- Return-priority state propagation. A return wave is converted at the
terminal boundary and otherwise moves left before any forward-wave branch can
overwrite it; the remaining forward branches retain their printed assignments. -/
def cmpUpdateReturnPriority (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .compare1 then
    ({ l with state := .compare2 }, r)
  else if r.state = .compare1 ∨ r.state = .compare2 then
    ({ l with state := r.state }, r)
  else if l.label = ⟨ψ - 1, by omega⟩ ∧ l.state = .congest then
    (l, { r with state := .lock })
  else if r.label = ⟨ψ - 1, by omega⟩ ∧ l.state = .lock then
    (l, { r with state := .compare1 })
  else if l.state = .congest ∨ l.state = .lock then
    (l, { r with state := l.state })
  else (l, r)

/-- Executable Algorithm-7 repair. Authorization is consumed whenever a
payload-zero carrier presents it, even if an active state prevents a fresh
start, so a forged bit cannot be reused indefinitely on the same carrier. -/
def authorizedCmpUpdate (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := .congest }
  else l.core
  let q := cmpUpdateReturnPriority hψ lCore r.core
  let lOut := cmpUpdateSetPath2 hψ q.1
  let lPermit := if allowed then false else normalizePermit lOut l.path0Crossed
  (⟨lOut, lPermit⟩,
    ⟨q.2, normalizePermit q.2 r.path0Crossed⟩)

/-- Full Algorithm-6 repair with path-presence dispatch unchanged. -/
def authorizedCompareSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  match l0.core.path with
  | .bot => (l0, r)
  | .some _ _ =>
    match r.core.path with
    | .bot => (l0, r)
    | .some _ _ =>
      let q := authorizedCmpUpdate hψ l0 r
      let out := compareSigDispatch hψ q.1.core q.2.core
      (⟨out.1, normalizePermit out.1 q.1.path0Crossed⟩,
        ⟨out.2, normalizePermit out.2 q.2.path0Crossed⟩)

private theorem cmpUpdateReturnPriority_leaders_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := cmpUpdateReturnPriority hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  unfold cmpUpdateReturnPriority
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_leader_eq (hψ : ψ > 0)
    (u : AgentState ψ) :
    (cmpUpdateSetPath2 hψ u).leader = u.leader := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

/-- The authorized return-priority comparison kernel frames both leaders. -/
theorem authorizedCmpUpdate_leaders_eq (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedCmpUpdate hψ l r
    q.1.core.leader = l.core.leader ∧
      q.2.core.leader = r.core.leader := by
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := .congest }
  else l.core
  let q := cmpUpdateReturnPriority hψ lCore r.core
  have hlCore : lCore.leader = l.core.leader := by
    unfold lCore
    split <;> rfl
  have hq := cmpUpdateReturnPriority_leaders_eq hψ lCore r.core
  exact ⟨(cmpUpdateSetPath2_leader_eq hψ q.1).trans
      (hq.1.trans hlCore), hq.2⟩

/-- Authorized COMPARE changes only comparison/path controls and permission;
it never changes either leader bit. -/
theorem authorizedCompareSig_leaders_eq (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedCompareSig hψ l r
    q.1.core.leader = l.core.leader ∧
      q.2.core.leader = r.core.leader := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : lCore.leader = l.core.leader := by
    unfold lCore compareSigInit
    split <;> rfl
  unfold authorizedCompareSig
  dsimp only
  split
  · exact ⟨hinit, rfl⟩
  · split
    · exact ⟨hinit, rfl⟩
    · let q := authorizedCmpUpdate hψ l0 r
      have hq := authorizedCmpUpdate_leaders_eq hψ l0 r
      have hout := PPLLVerify.compareSigDispatch_leaders_eq
        hψ q.1.core q.2.core
      exact ⟨hout.1.trans (hq.1.trans hinit),
        hout.2.trans hq.2⟩

/-- Authorized Algorithm-1 prefix through SIGMOVE. -/
def authorizedBeforeCheck (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := authorizedPPsi hψ l r
  let q := authorizedGenSig hψ κ q.1 q.2
  let q := authorizedCleanSig hψ q.1 q.2
  let q := authorizedEliminateSig hψ q.1 q.2
  authorizedSigMove hψ q.1 q.2

/-- Authorized prefix through the repaired COMPARE stage. -/
def authorizedBeforeSuppress (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := authorizedBeforeCheck hψ κ l r
  let q := authorizedCheckSig hψ q.1 q.2
  let q := authorizedDisappear hψ q.1 q.2
  authorizedCompareSig hψ q.1 q.2

/-- Full separately named audit transition. Every non-comparison stage keeps its
old physical semantics; only authorization maintenance and Algorithm 7 differ. -/
def ppllAuthorizedRepair (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := authorizedBeforeSuppress hψ κ l r
  let q := authorizedReconcile (suppressSig hψ) q.1 q.2
  let q := authorizedReconcile (eliminateLeadersNoCollision hψ) q.1 q.2
  authorizedReconcile (writeSeq hψ) q.1 q.2

/-! ## Numeric-domain closure and finite physical carrier -/

/-- Changing only `MainState` preserves Algorithm 1's declared numeric domain. -/
theorem setState_inProtocolDomain (s : AgentState ψ)
    (hs : s.inProtocolDomain κ) (state : MainState) :
    ({ s with state := state } : AgentState ψ).inProtocolDomain κ := by
  exact hs

/-- Return-priority propagation changes only comparison state and therefore
preserves the numeric domain on both endpoints. -/
theorem cmpUpdateReturnPriority_inProtocolDomain
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := cmpUpdateReturnPriority hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  unfold cmpUpdateReturnPriority
  split
  · exact ⟨setState_inProtocolDomain l hl .compare2, hr⟩
  · split
    · exact ⟨setState_inProtocolDomain l hl r.state, hr⟩
    · split
      · exact ⟨hl, setState_inProtocolDomain r hr .lock⟩
      · split
        · exact ⟨hl, setState_inProtocolDomain r hr .compare1⟩
        · split
          · exact ⟨hl, setState_inProtocolDomain r hr l.state⟩
          · exact ⟨hl, hr⟩

/-- The executable Algorithm-7 repair preserves every declared numeric range. -/
theorem authorizedCmpUpdate_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedCmpUpdate hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := .congest }
  else l.core
  have hlCore : lCore.inProtocolDomain κ := by
    dsimp only [lCore]
    split
    · exact setState_inProtocolDomain l.core hl .congest
    · exact hl
  let q0 := cmpUpdateReturnPriority hψ lCore r.core
  have hq0 := cmpUpdateReturnPriority_inProtocolDomain
    hψ lCore r.core hlCore hr
  change q0.1.inProtocolDomain κ ∧ q0.2.inProtocolDomain κ at hq0
  exact ⟨cmpUpdateSetPath2_inProtocolDomain hψ q0.1 hq0.1, hq0.2⟩

/-- The full authorized Algorithm 6 preserves the numeric domain. -/
theorem authorizedCompareSig_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedCompareSig hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  unfold authorizedCompareSig
  dsimp only
  let lCore := compareSigInit l.core
  have hlCore := compareSigInit_inProtocolDomain l.core hl
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  change l0.core.inProtocolDomain κ at hlCore
  cases hlpath : l0.core.path with
  | bot => exact ⟨hlCore, hr⟩
  | some leftLabel leftBit =>
      cases hrpath : r.core.path with
      | bot => exact ⟨hlCore, hr⟩
      | some rightLabel rightBit =>
          let q0 := authorizedCmpUpdate hψ l0 r
          have hq0 := authorizedCmpUpdate_inProtocolDomain
            hψ l0 r hlCore hr
          change q0.1.core.inProtocolDomain κ ∧
            q0.2.core.inProtocolDomain κ at hq0
          exact compareSigDispatch_inProtocolDomain hψ
            q0.1.core q0.2.core hq0.1 hq0.2

/-- Reconciliation changes only authorization around an already domain-closed
physical stage. -/
theorem authorizedReconcile_inProtocolDomain
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ)
    (hf : let q := f l.core r.core
      q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ) :
    let q := authorizedReconcile f l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  exact hf

/-- Algorithm 2 plus fail-closed authorization preserves the numeric domain. -/
theorem authorizedPPsi_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedPPsi hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  exact pPsi_inProtocolDomain hψ l.core r.core hl hr

/-- Specialized SIGMOVE authorization has exactly the old domain-closed core. -/
theorem authorizedSigMove_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedSigMove hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  have hcore := sigMove_inProtocolDomain hψ l.core r.core hl hr
  unfold authorizedSigMove
  dsimp only
  split <;> exact hcore

/-- The authorized prefix through SIGMOVE is numeric-domain closed. -/
theorem authorizedBeforeCheck_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedBeforeCheck hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedPPsi hψ l r
  have h0 := authorizedPPsi_inProtocolDomain hψ l r hl hr
  change q0.1.core.inProtocolDomain κ ∧ q0.2.core.inProtocolDomain κ at h0
  let q1 := authorizedGenSig hψ κ q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain
    (genSigSaturated hψ κ) q0.1 q0.2
    (genSigSaturated_inProtocolDomain hψ q0.1.core q0.2.core h0.1 h0.2)
  change q1.1.core.inProtocolDomain κ ∧ q1.2.core.inProtocolDomain κ at h1
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (cleanSig hψ) q1.1 q1.2
    (cleanSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  change q2.1.core.inProtocolDomain κ ∧ q2.2.core.inProtocolDomain κ at h2
  let q3 := authorizedEliminateSig hψ q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateSig hψ) q2.1 q2.2
    (eliminateSig_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)
  change q3.1.core.inProtocolDomain κ ∧ q3.2.core.inProtocolDomain κ at h3
  change
    let q := authorizedSigMove hψ q3.1 q3.2
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ
  exact authorizedSigMove_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2

attribute [local irreducible] authorizedBeforeCheck

/-- The authorized prefix through COMPARE is numeric-domain closed. -/
theorem authorizedBeforeSuppress_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedBeforeSuppress hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedBeforeCheck hψ κ l r
  have h0 := authorizedBeforeCheck_inProtocolDomain hψ κ l r hl hr
  change q0.1.core.inProtocolDomain κ ∧ q0.2.core.inProtocolDomain κ at h0
  let q1 := authorizedCheckSig hψ q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain
    (checkSig hψ) q0.1 q0.2
    (checkSig_inProtocolDomain hψ q0.1.core q0.2.core h0.1 h0.2)
  change q1.1.core.inProtocolDomain κ ∧ q1.2.core.inProtocolDomain κ at h1
  let q2 := authorizedDisappear hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (disappear hψ) q1.1 q1.2
    (disappear_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  change q2.1.core.inProtocolDomain κ ∧ q2.2.core.inProtocolDomain κ at h2
  change
    let q := authorizedCompareSig hψ q2.1 q2.2
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ
  exact authorizedCompareSig_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2

attribute [local irreducible] authorizedBeforeSuppress

/-- The full authorized audit transition is closed on Algorithm 1's declared
numeric ranges. Authorization is an extra finite Boolean, not hidden in those
old field bounds. -/
theorem ppllAuthorizedRepair_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := ppllAuthorizedRepair hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedBeforeSuppress hψ κ l r
  have h0 := authorizedBeforeSuppress_inProtocolDomain hψ κ l r hl hr
  change q0.1.core.inProtocolDomain κ ∧ q0.2.core.inProtocolDomain κ at h0
  let q1 := authorizedReconcile (suppressSig hψ) q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain
    (suppressSig hψ) q0.1 q0.2
    (suppressSig_inProtocolDomain hψ q0.1.core q0.2.core h0.1 h0.2)
  change q1.1.core.inProtocolDomain κ ∧ q1.2.core.inProtocolDomain κ at h1
  let q2 := authorizedReconcile (eliminateLeadersNoCollision hψ) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollision hψ) q1.1 q1.2
    (eliminateLeadersNoCollision_inProtocolDomain
      hψ q1.1.core q1.2.core h1.1 h1.2)
  change q2.1.core.inProtocolDomain κ ∧ q2.2.core.inProtocolDomain κ at h2
  change
    let q := authorizedReconcile (writeSeq hψ) q2.1 q2.2
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ
  exact authorizedReconcile_inProtocolDomain (writeSeq hψ) q2.1 q2.2
    (writeSeq_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)

/-- Finite-by-construction physical state for the executable authorization
repair. -/
structure AuthorizedBoundedAgentState (ψ κ : Nat) where
  core : BoundedAgentState ψ κ
  path0Crossed : Bool
  deriving DecidableEq, Repr

/-- Erase the finite carrier into its audit-level executable state. -/
def AuthorizedBoundedAgentState.erase
    (s : AuthorizedBoundedAgentState ψ κ) : AuthorizedAgentState ψ :=
  ⟨s.core.erase, s.path0Crossed⟩

attribute [local irreducible] ppllAuthorizedRepair

/-- Total transition on the finite authorized carrier. -/
def authorizedBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := ppllAuthorizedRepair hψ κ l.erase r.erase
  let hq := ppllAuthorizedRepair_inProtocolDomain hψ κ l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Finite transition erases exactly to the separately named authorized audit
transition. It does not claim erasure to Wu's or the old integrated transition. -/
theorem erase_authorizedBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := authorizedBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) = ppllAuthorizedRepair hψ κ l.erase r.erase := by
  let q := ppllAuthorizedRepair hψ κ l.erase r.erase
  let hq := ppllAuthorizedRepair_inProtocolDomain hψ κ l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Packaged finite population protocol for the executable repair. -/
def authorizedBoundedProtocol (hψ : ψ > 0) (κ : Nat) : PopulationProtocol where
  Q := AuthorizedBoundedAgentState ψ κ
  Y := LeaderOutput
  transition := authorizedBoundedTransition hψ κ
  output := fun s => if s.core.leader then .leader else .follower

/-! ## One-step authorization normalization -/

/-- The executable marker is structurally well formed only on a payload-zero
path component. This does not assert that the bit was historically earned. -/
def AuthorizationCanonical (u : AuthorizedAgentState ψ) : Prop :=
  u.path0Crossed = true → ∃ bit, u.core.path = .some 0 bit

/-- `normalizePermit` always produces a structurally canonical marker. -/
theorem normalizePermit_canonical (s : AgentState ψ) (permit : Bool) :
    (normalizePermit s permit = true → ∃ bit, s.path = .some 0 bit) := by
  unfold normalizePermit
  cases hpath : s.path with
  | bot => simp
  | some label bit =>
      cases label with
      | zero =>
          intro _
          exact ⟨bit, rfl⟩
      | succ label => simp

/-- Every generic reconciliation output has a canonical marker, regardless of
arbitrary input authorization values. -/
theorem authorizedReconcile_canonical
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedReconcile f l r
    AuthorizationCanonical q.1 ∧ AuthorizationCanonical q.2 := by
  let q := f l.core r.core
  change AuthorizationCanonical ⟨q.1, reconcilePermit l q.1⟩ ∧
    AuthorizationCanonical ⟨q.2, reconcilePermit r q.2⟩
  constructor
  · unfold AuthorizationCanonical reconcilePermit
    split
    · exact normalizePermit_canonical q.1 l.path0Crossed
    · simp
  · unfold AuthorizationCanonical reconcilePermit
    split
    · exact normalizePermit_canonical q.2 r.path0Crossed
    · simp

/-- One full authorized transition always removes structurally malformed
markers, because its final WRITE_SEQ reconciliation normalizes both outputs.
Historically forged `true` on an actual payload-zero path remains a separate
cleanup obligation. -/
theorem ppllAuthorizedRepair_outputs_canonical
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    let q := ppllAuthorizedRepair hψ κ l r
    AuthorizationCanonical q.1 ∧ AuthorizationCanonical q.2 := by
  unfold ppllAuthorizedRepair
  let q0 := authorizedBeforeSuppress hψ κ l r
  let q1 := authorizedReconcile (suppressSig hψ) q0.1 q0.2
  let q2 := authorizedReconcile (eliminateLeadersNoCollision hψ) q1.1 q1.2
  change
    let q := authorizedReconcile (writeSeq hψ) q2.1 q2.2
    AuthorizationCanonical q.1 ∧ AuthorizationCanonical q.2
  exact authorizedReconcile_canonical (writeSeq hψ) q2.1 q2.2

/-- Constructive exhaustive list for the counted physical carrier: the old
bounded state product one explicit Boolean. -/
def authorizedBoundedAgentState (ψ κ : Nat) :
    ExhaustiveList (AuthorizedBoundedAgentState ψ κ) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (PPLLFinite.boundedAgentState ψ κ)
      ExhaustiveList.bool)
    (fun x => ⟨x.1, x.2⟩)
    (by
      intro s
      exact ⟨(s.core, s.path0Crossed), rfl⟩)

/-- The authorization certificate is duplicate-free: its product source is
Nodup and the record constructor is injective. -/
theorem authorizedBoundedAgentState_values_nodup (ψ κ : Nat) :
    (authorizedBoundedAgentState ψ κ).values.Nodup := by
  unfold authorizedBoundedAgentState
  apply ExhaustiveList.values_nodup_mapSurjective
  · apply ExhaustiveList.values_nodup_prod
    · exact PPLLFinite.boundedAgentState_values_nodup ψ κ
    · exact ExhaustiveList.values_nodup_bool
  · intro x y h
    rcases x with ⟨xc, xp⟩
    rcases y with ⟨yc, yp⟩
    cases h
    rfl

/-- The concrete authorization certificate has exactly twice as many entries,
and duplicate-freedom now makes this an exact semantic-cardinality factor. -/
theorem authorizedBoundedAgentState_values_length (ψ κ : Nat) :
    (authorizedBoundedAgentState ψ κ).values.length =
      2 * (PPLLFinite.boundedAgentState ψ κ).values.length := by
  unfold authorizedBoundedAgentState ExhaustiveList.mapSurjective
  rw [List.length_map, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool]
  omega

/-- Every authorized bounded state has a finite index in the explicit carrier
list. -/
theorem authorizedBoundedAgentState_decode_surjective (ψ κ : Nat) :
    Function.Surjective (authorizedBoundedAgentState ψ κ).decode :=
  (authorizedBoundedAgentState ψ κ).decode_surjective

/-- Exact finite-index representation of authorized bounded states. -/
theorem authorizedBoundedAgentState_decode_bijective (ψ κ : Nat) :
    Function.Injective (authorizedBoundedAgentState ψ κ).decode ∧
      Function.Surjective (authorizedBoundedAgentState ψ κ).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (authorizedBoundedAgentState_values_nodup ψ κ),
    authorizedBoundedAgentState_decode_surjective ψ κ⟩

/-! ## Executable regression surface -/

private def authDepart0 (moved : Bool) : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with path := .some 0 0 }, moved⟩

private def authDepart1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with path := .some 1 0 }, false⟩

/-- The executable repair is genuinely different from the old T9-only patch on
a moved departing carrier; no false erasure theorem identifies them. -/
theorem authorizedCmpUpdate_differs_noSourceRearm :
    (authorizedCmpUpdate (by omega : 2 > 0)
      (authDepart0 true) authDepart1).1.core ≠
      (cmpUpdateNoSourceRearm (by omega : 2 > 0)
        (authDepart0 true).core authDepart1.core).1 := by
  decide

/-- A canonical GENSIG-style source carrier is not freshly armed. -/
theorem source_depart_not_authorized :
    authorizedCmpUpdate (by omega : 2 > 0) (authDepart0 false) authDepart1 =
      (authDepart0 false, authDepart1) := by
  decide

/-- After a real crossing marker is present, a departed payload-zero component
can start a fresh comparison and consumes the marker. -/
theorem moved_depart_starts_and_consumes :
    let q := authorizedCmpUpdate (by omega : 2 > 0)
      (authDepart0 true) authDepart1
    q.1.core.state = .congest ∧ q.2.core.state = .congest ∧
      q.1.path0Crossed = false := by
  decide

private def authLock0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .lock with path := .some 0 0 }, true⟩

private def authNeutral1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 with path := .some 1 0 }, false⟩

/-- A label-zero lock is not reinitialized; for ψ=2 it immediately launches the
return wave at the terminal responder. -/
theorem labelZero_lock_reaches_compare1 :
    let q := authorizedCmpUpdate (by omega : 2 > 0) authLock0 authNeutral1
    q.1.core.state = .lock ∧ q.2.core.state = .compare1 ∧
      q.1.path0Crossed = false := by
  decide

private def authCompare1At1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .compare1 with path := .some 1 0 }, false⟩

/-- A return wave has priority over the forward lock on the preceding edge. -/
theorem compare1_return_has_priority :
    let q := authorizedCmpUpdate (by omega : 2 > 0) authLock0 authCompare1At1
    q.1.core.state = .compare1 ∧ q.2.core.state = .compare1 := by
  decide

/-- A forged permission bit is physical and can arm once; it is consumed rather
than mistaken for proof of genuine history. Full arbitrary-state cleanup remains
a separate convergence obligation. -/
theorem forged_permission_is_consumed :
    let q := authorizedCmpUpdate (by omega : 2 > 0)
      (authDepart0 true) authDepart1
    q.1.path0Crossed = false := by
  decide

/-! ## Complete ψ=2 comparison-wave regression -/

private def authCongest0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .congest with path := .some 0 0 }, false⟩

private def authCongest1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .congest with path := .some 1 0 }, false⟩

private def authLock0Clean : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .lock with path := .some 0 0 }, false⟩

private def authCompare1At0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .compare1 with path := .some 0 0 }, false⟩

private def authCompare2At1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .compare2 with path := .some 1 0 }, false⟩

private def authPath2At0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .compare2 with
      path := .some 0 0, path2 := some ⟨0, 0, 2, 1⟩ }, false⟩

/-- The repaired state machine has a concrete non-vacuous comparison route:
fresh authorized start, terminal lock creation, compare1 launch and return,
terminal conversion to compare2, and finally label-zero path2 creation. This is
a six-step local control regression, not a scheduler convergence theorem. -/
theorem authorizedComparison_psi2_reaches_path2 :
    let q0 := authorizedCmpUpdate (by omega : 2 > 0)
      (authDepart0 true) authDepart1
    let q1 := authorizedCmpUpdate (by omega : 2 > 0) q0.2 q0.1
    let q2 := authorizedCmpUpdate (by omega : 2 > 0) q1.2 q1.1
    let q3 := authorizedCmpUpdate (by omega : 2 > 0) q2.1 q2.2
    let q4 := authorizedCmpUpdate (by omega : 2 > 0) q3.2 q3.1
    let q5 := authorizedCmpUpdate (by omega : 2 > 0) q4.2 q4.1
    q0 = (authCongest0, authCongest1) ∧
    q1 = (authCongest1, authLock0Clean) ∧
    q2 = (authLock0Clean, authCompare1At1) ∧
    q3 = (authCompare1At0, authCompare1At1) ∧
    q4 = (authCompare2At1, authCompare1At0) ∧
    q5 = (authPath2At0, authCompare2At1) := by
  decide

/-! ## Authorization birth and movement -/

private def authBirthL : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 with wait := false }, true⟩

private def authBirthR : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 1, true⟩

/-- GENSIG birth overwrites forged authorization: both newly created path
components are canonically unauthorized at their source. -/
theorem authorizedGenSig_birth_clears_forgery :
    let q := authorizedGenSig (by omega : 2 > 0) 10 authBirthL authBirthR
    q.1.core.path = .some 0 0 ∧ q.2.core.path = .some 1 0 ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  decide

private def authCrossL : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with path := .some 0 0 }, false⟩

private def authCrossR : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 0, false⟩

/-- The exact stable terminal-to-zero SIGMOVE of payload zero sets permission
at the receiver and clears it at the sender. -/
theorem authorizedSigMove_stable_wrap_sets_permission :
    let q := authorizedSigMove (by omega : 2 > 0) authCrossL authCrossR
    q.1.core.path = .bot ∧ q.1.path0Crossed = false ∧
      q.2.core.path = .some 0 0 ∧ q.2.path0Crossed = true := by
  decide

end PPLLAuthorizedComparisonRepair
