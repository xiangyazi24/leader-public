import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.ZeroDivisible.CompareBState


namespace PPLLAstraR5MiddleB
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
open PPLLPostElectionGuard PPLLFableDesignR1
open PPLLAstraDesign2 PPLLAstraDesign3 PPLLAstraR5CompareB


set_option autoImplicit false
set_option linter.unusedSimpArgs false


-- Literal suffix after preCheckReset; no alternative transition.
def AfterReset {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := (normalizeReady l, normalizeReady r)
  let q := PPLLAstraR5Repair.checkSource hp c q.1 q.2
  let q := disappear hp q.1 q.2
  repair .readyAck q.1 q.2


def Middle {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := (dropStale l, dropStale r)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  let q := PPLLAstraR5Repair.checkSource hp c q.1 q.2
  let q := disappear hp q.1 q.2
  repair .readyAck q.1 q.2


private theorem middle_factor {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) :
    Middle hp c l r =
      let q := preCheckReset (dropStale l) (dropStale r)
      AfterReset hp c q.1 q.2 := by rfl


def PairHole {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.path = .bot ∨ q.2.path = .bot


def TerminalE {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  (q.1.label.val + 1 = ψ ∧ q.1.state = .eliminate_signal) ∨
  (q.2.label.val + 1 = ψ ∧ q.2.state = .eliminate_signal)


def BOrE (ψ k : Nat) (s : MainState) : Prop :=
  BState ψ k s ∨ (k + 1 = ψ ∧ s = .eliminate_signal)


def ExactBFrame {ψ : Nat} (j k : Nat) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.label = l.label ∧ q.2.label = r.label ∧
  q.1.path = l.path ∧ q.2.path = r.path ∧
  q.1.path2 = l.path2 ∧ q.2.path2 = r.path2 ∧
  BState ψ j q.1.state ∧ BState ψ k q.2.state


private def Keep {ψ : Nat} (a b : AgentState ψ) : Prop :=
  b.label = a.label ∧ b.path = a.path ∧ b.path2 = a.path2


private theorem keep_trans {ψ : Nat} {a b d : AgentState ψ}
    (h : Keep a b) (g : Keep b d) : Keep a d :=
  ⟨g.1.trans h.1, g.2.1.trans h.2.1, g.2.2.trans h.2.2⟩


private def Safe (s : MainState) : Prop :=
  s = .depart ∨ s = .equal ∨ s = .lock ∨
  s = .compare1 ∨ s = .compare2 ∨ s = .eliminate_signal


private theorem b_safe {ψ k : Nat} {s : MainState}
    (h : BState ψ k s) : Safe s := by
  unfold BState at h
  split at h
  · simp only [HeadState] at h
    rcases h with h | h <;> simp [Safe, h]
  · split at h
    · simp [Safe, h]
    · split at h
      · simp only [PenState, MidState] at h
        rcases h with h | h | h | h <;> simp [Safe, h]
      · simp only [MidState] at h
        rcases h with h | h | h <;> simp [Safe, h]


private theorem bore_safe {ψ k : Nat} {s : MainState}
    (h : BOrE ψ k s) : Safe s := by
  rcases h with h | ⟨_, h⟩
  · exact b_safe h
  · simp [Safe, h]


private theorem safe_not_ready {s : MainState} (h : Safe s) :
    s ≠ .CHECK_ready := by
  rcases h with h | h | h | h | h | h <;> simp [h]


private theorem safe_not_toss {s : MainState} (h : Safe s) :
    s ≠ .toss := by
  rcases h with h | h | h | h | h | h <;> simp [h]


private theorem equal_role {ψ k : Nat}
    (h : BState ψ k .equal) : k + 2 = ψ := by
  by_cases h0 : k = 0
  · simp [BState, h0, HeadState] at h
  by_cases ht : k + 1 = ψ
  · simp [BState, h0, ht] at h
  by_cases hpen : k + 2 = ψ
  · exact hpen
  · simp [BState, h0, ht, hpen, MidState] at h


private theorem bore_equal_role {ψ k : Nat} {s : MainState}
    (h : BOrE ψ k s) (he : s = .equal) : k + 2 = ψ := by
  rcases h with h | ⟨_, h⟩
  · rw [he] at h
    exact equal_role h
  · simp [he] at h


private theorem terminal_cases {ψ k : Nat} {s : MainState}
    (h4 : 4 ≤ ψ) (ht : k + 1 = ψ) (h : BOrE ψ k s) :
    s = .compare2 ∨ s = .eliminate_signal := by
  rcases h with h | ⟨_, h⟩
  · left
    have h0 : k ≠ 0 := by omega
    simpa [BState, h0, ht] using h
  · exact Or.inr h


private theorem pen_depart {ψ k : Nat} (h4 : 4 ≤ ψ)
    (hpen : k + 2 = ψ) : BState ψ k .depart := by
  have h0 : k ≠ 0 := by omega
  have ht : k + 1 ≠ ψ := by omega
  simp [BState, h0, ht, hpen, PenState, MidState]


-- Factor only the actual CHECK wrapper, for small projection proofs.
private def Ready {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if waveState u.state ∨ u.state = .congest ∨ u.state = .done then u
  else checkSigSetReadyGuarded u


private def CheckTail {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := checkSigCheckL hp l
  let r := checkSigCheckR hp l r
  let l := PPLLAstraR5Repair.setResult c l
  let r := PPLLAstraR5Repair.setResult c r
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
    (l, { r with leader := true }) else (l, r)


private theorem check_factor {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) :
    PPLLAstraR5Repair.checkSource hp c l r =
      CheckTail hp c
        (PPLLAstraR5Repair.releaseEqual hp (Ready l) (Ready r))
        (Ready r) := by rfl


-- Generic main-path frames. These are valid even on reset outputs.
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl


private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl


private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl


private theorem orphan_path {ψ : Nat} (u : AgentState ψ) :
    (normalizeOrphan u).path = u.path := by
  cases h : u.path <;> simp [normalizeOrphan, h, path_ite]


private theorem carrier_path {ψ : Nat} (u : AgentState ψ) :
    (normalizeCarrier u).path = u.path := by
  cases h : u.path <;>
    simp [normalizeCarrier, releaseCongest, h, path_ite]


private theorem normalize_path {ψ : Nat} (u : AgentState ψ) :
    (normalizeReady u).path = u.path := by
  cases h : u.path <;>
    simp [normalizeReady, path_ite, orphan_path, carrier_path, h]


private theorem ready_path {ψ : Nat} (u : AgentState ψ) :
    (Ready u).path = u.path := by
  cases h : u.path <;>
    simp [Ready, checkSigSetReadyGuarded, checkSigSetReady, h, path_ite]


private theorem release_path {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) :
    (PPLLAstraR5Repair.releaseEqual hp l r).path = l.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [PPLLAstraR5Repair.releaseEqual, hl, hr, path_ite]


private theorem checkL_path {ψ : Nat} (hp : 0 < ψ) (u : AgentState ψ) :
    (checkSigCheckL hp u).path = u.path := by
  cases h : u.path with
  | bot => simp [checkSigCheckL, h]
  | some a b => cases a <;> simp [checkSigCheckL, h, path_ite]


private theorem checkR_path {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) : (checkSigCheckR hp l r).path = r.path := by
  cases h : r.path <;> simp [checkSigCheckR, h, path_ite]


private theorem result_path {ψ : Nat} (c : PPLLAstraR5Repair.Cfg) (u : AgentState ψ) :
    (PPLLAstraR5Repair.setResult c u).path = u.path := by
  simp [PPLLAstraR5Repair.setResult, checkSigSetResult, path_ite]


private theorem tail_paths {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) :
    (CheckTail hp c l r).1.path = l.path ∧
    (CheckTail hp c l r).2.path = r.path := by
  simp only [CheckTail, fst_ite, snd_ite, path_ite, result_path,
    checkL_path, checkR_path, ite_self, and_self]


private theorem check_paths {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) :
    (PPLLAstraR5Repair.checkSource hp c l r).1.path = l.path ∧
    (PPLLAstraR5Repair.checkSource hp c l r).2.path = r.path := by
  simpa only [check_factor, release_path, ready_path] using
    (tail_paths hp c
      (PPLLAstraR5Repair.releaseEqual hp (Ready l) (Ready r)) (Ready r))


private theorem disappear_paths {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) :
    (disappear hp l r).1.path = l.path ∧
    (disappear hp l r).2.path = r.path := by
  simp only [disappear_eq_staged, disappearStaged, disappearStartR,
    disappearStartL, disappearCarry, fst_ite, snd_ite, path_ite,
    ite_self, and_self]
  constructor
  · by_cases ht : l.state = MainState.toss ∧ l.label = ⟨0, hp⟩
    · by_cases hpp : l.p = true <;> simp [ht, hpp]
    · simp [ht]
  · trivial


private theorem releaseSuffix_paths {ψ : Nat} (l r : AgentState ψ) :
    (releaseReadySuffix l r).1.path = l.path ∧
    (releaseReadySuffix l r).2.path = r.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, path_ite]


private theorem ack_paths {ψ : Nat} (l r : AgentState ψ) :
    (ackTail l r).1.path = l.path ∧ (ackTail l r).2.path = r.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, path_ite]


private theorem repair_paths {ψ : Nat} (l r : AgentState ψ) :
    (repair .readyAck l r).1.path = l.path ∧
    (repair .readyAck l r).2.path = r.path := by
  simp only [repair, (ack_paths _ _).1, (ack_paths _ _).2,
    (releaseSuffix_paths _ _).1, (releaseSuffix_paths _ _).2,
    carrier_path, orphan_path, and_self]


private theorem afterReset_paths {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) :
    (AfterReset hp c l r).1.path = l.path ∧
    (AfterReset hp c l r).2.path = r.path := by
  simp only [AfterReset, (repair_paths _ _).1, (repair_paths _ _).2,
    (disappear_paths _ _ _).1, (disappear_paths _ _ _).2,
    (check_paths _ _ _ _).1, (check_paths _ _ _ _).2,
    normalize_path, and_self]


private theorem drop_own {ψ k b : Nat} (u : AgentState ψ)
    (hlab : u.label.val = k) (hp : u.path = .some k b) :
    dropStale u = u := by
  simp [dropStale, aligned, hp, hlab]


/-- Exact reset-hole characterization, with arbitrary leaders/states/tokens. -/
theorem middle_hole_iff {ψ j k bL bR : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ)
    (hl : l.label.val = j) (hr : r.label.val = k)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR) :
    PairHole (Middle hp c l r) ↔
      l.leader = true ∨ l.reset_cmd = true ∨ r.reset_cmd = true := by
  simp only [middle_factor, drop_own l hl pl, drop_own r hr pr,
    PairHole, (afterReset_paths _ _ _ _).1,
    (afterReset_paths _ _ _ _).2]
  cases ha : l.leader <;> cases hb : l.reset_cmd <;>
    cases hc : r.reset_cmd <;>
    simp [preCheckReset, clearCmp, ha, hb, hc, pl, pr]


-- Full-record identities on the six allowed B/E states.
private theorem orphan_safe {ψ : Nat} (u : AgentState ψ)
    (hs : Safe u.state) : normalizeOrphan u = u := by
  rcases hs with hs | hs | hs | hs | hs | hs <;>
    cases hp : u.path <;> simp [normalizeOrphan, hs, hp]


private theorem carrier_safe {ψ : Nat} (u : AgentState ψ)
    (hs : Safe u.state) : normalizeCarrier u = u := by
  rcases hs with hs | hs | hs | hs | hs | hs <;>
    cases hp : u.path <;>
    simp [normalizeCarrier, releaseCongest, hs, hp]


private theorem normalize_own_safe {ψ k b : Nat} (u : AgentState ψ)
    (hlab : u.label.val = k) (hp : u.path = .some k b)
    (hs : Safe u.state) : normalizeReady u = u := by
  rcases hs with hs | hs | hs | hs | hs | hs <;>
    simp [normalizeReady, normalizeOrphan, normalizeCarrier,
      releaseCongest, aligned, hp, hlab, hs]


private theorem ready_safe {ψ : Nat} (u : AgentState ψ)
    (hs : Safe u.state) : Ready u = u := by
  rcases hs with hs | hs | hs | hs | hs | hs <;>
    cases hp : u.path <;>
    simp [Ready, waveState, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, hs, hp]


private theorem checkL_safe {ψ : Nat} (hp : 0 < ψ) (u : AgentState ψ)
    (hs : Safe u.state) : checkSigCheckL hp u = u := by
  have hn := safe_not_ready hs
  cases h : u.path with
  | bot => simp [checkSigCheckL, h]
  | some a b => cases a <;> simp [checkSigCheckL, h, hn]


private theorem checkR_safe {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) (hs : Safe r.state) :
    checkSigCheckR hp l r = r := by
  have hn := safe_not_ready hs
  cases h : r.path <;> simp [checkSigCheckR, h, hn]


private theorem result_safe {ψ : Nat} (c : PPLLAstraR5Repair.Cfg) (u : AgentState ψ)
    (hs : Safe u.state) : PPLLAstraR5Repair.setResult c u = u := by
  rcases hs with hs | hs | hs | hs | hs | hs <;>
    simp [PPLLAstraR5Repair.setResult, checkSigSetResult, hs]


-- This is an output formula, not an assumed transition frame.
private def Released {ψ : Nat} (l r : AgentState ψ) : AgentState ψ :=
  if l.state = .equal ∧ r.state = .compare2 then
    { l with state := .depart } else l


private theorem released_good {ψ j : Nat} (h4 : 4 ≤ ψ)
    (l r : AgentState ψ) (h : BOrE ψ j l.state) :
    Keep l (Released l r) ∧ BOrE ψ j (Released l r).state := by
  by_cases he : l.state = .equal ∧ r.state = .compare2
  · simp only [Released, if_pos he]
    exact ⟨⟨rfl, rfl, rfl⟩,
      Or.inl (pen_depart h4 (bore_equal_role h he.1))⟩
  · simpa [Released, he, Keep] using h


private theorem release_table {ψ j k bL bR : Nat}
    (hp : 0 < ψ) (h4 : 4 ≤ ψ) (l r : AgentState ψ)
    (hl : l.label.val = j) (hr : r.label.val = k)
    (succ : k = (j + 1) % ψ)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR)
    (hL : BOrE ψ j l.state) (hR : BOrE ψ k r.state) :
    PPLLAstraR5Repair.releaseEqual hp l r = Released l r := by
  by_cases he : l.state = .equal
  · have hj : j + 2 = ψ := bore_equal_role hL he
    have hk : k = j + 1 := by
      rw [succ, Nat.mod_eq_of_lt (by omega)]
    have hkt : k + 1 = ψ := by omega
    have ht : r.label = (⟨ψ - 1, by omega⟩ : Fin ψ) := by
      apply Fin.ext
      change r.label.val = ψ - 1
      omega
    have al : aligned l = true := by simp [aligned, pl, hl]
    have ar : aligned r = true := by simp [aligned, pr, hr]
    rcases terminal_cases h4 hkt hR with hs | hs <;>
      simp [PPLLAstraR5Repair.releaseEqual, Released, pl, pr,
        al, ar, he, hs, ht, hk]
  · simp [PPLLAstraR5Repair.releaseEqual, Released, pl, pr, he]


private theorem checkTail_eq {ψ : Nat} (hp : 0 < ψ) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) (hL : Safe l.state) (hR : Safe r.state)
    (hn : ¬ (r.label = (⟨ψ-1, by omega⟩ : Fin ψ) ∧ r.state = .equal)) :
    CheckTail hp c l r = (l, r) := by
  simp only [CheckTail, checkL_safe hp l hL, checkR_safe hp l r hR,
    result_safe c l hL, result_safe c r hR, if_neg hn]


/-- The complete CHECK state table, including the penultimate release. -/
theorem checkSource_BOrE_table {ψ j k bL bR : Nat}
    (hp : 0 < ψ) (h4 : 4 ≤ ψ) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.label.val = j) (hr : r.label.val = k)
    (succ : k = (j + 1) % ψ)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR)
    (hL : BOrE ψ j l.state) (hR : BOrE ψ k r.state) :
    PPLLAstraR5Repair.checkSource hp c l r = (Released l r, r) := by
  have hn : ¬ (r.label = (⟨ψ-1, by omega⟩ : Fin ψ) ∧ r.state = .equal) := by
    rintro ⟨ht, hs⟩
    have hk := bore_equal_role hR hs
    have hv := congrArg Fin.val ht
    change r.label.val = ψ - 1 at hv
    omega
  have ha := released_good h4 l r hL
  simp only [check_factor, ready_safe l (bore_safe hL),
    ready_safe r (bore_safe hR),
    release_table hp h4 l r hl hr succ pl pr hL hR]
  exact checkTail_eq hp c (Released l r) r
    (bore_safe ha.2) (bore_safe hR) hn


/-- No toss-start is possible; the four carry branches are explicit. -/
theorem disappear_BOrE {ψ j k : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) (hr : r.label.val = k)
    (hL : BOrE ψ j l.state) (hR : BOrE ψ k r.state) :
    let q := disappear hp l r
    Keep l q.1 ∧ Keep r q.2 ∧
      BOrE ψ j q.1.state ∧ BOrE ψ k q.2.state := by
  have nl := safe_not_toss (bore_safe hL)
  have nr := safe_not_toss (bore_safe hR)
  have hd : disappear hp l r = disappearCarry hp l r := by
    simp [disappear_eq_staged, disappearStaged,
      disappearStartR, disappearStartL, nl, nr]
  by_cases hc : l.p_carry = true
  · by_cases hpr : r.p = true
    · by_cases ht : r.label = (⟨ψ-1, by omega⟩ : Fin ψ)
      · have hv := congrArg Fin.val ht
        change r.label.val = ψ - 1 at hv
        have hk : k + 1 = ψ := by omega
        have he : BOrE ψ k .eliminate_signal := Or.inr ⟨hk, rfl⟩
        simpa [hd, disappearCarry, hc, hpr, ht, Keep] using And.intro hL he
      · simpa [hd, disappearCarry, hc, hpr, ht, Keep] using And.intro hL hR
    · simpa [hd, disappearCarry, hc, hpr, Keep] using And.intro hL hR
  · simpa [hd, disappearCarry, hc, Keep] using And.intro hL hR


/-- ReadyAck is the identity on full role-correct B/E carriers. -/
theorem repair_BOrE {ψ j k bL bR : Nat} (h4 : 4 ≤ ψ)
    (l r : AgentState ψ)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR)
    (hL : BOrE ψ j l.state) (hR : BOrE ψ k r.state) :
    repair .readyAck l r = (l, r) := by
  have sl := bore_safe hL
  have sr := bore_safe hR
  have nr := safe_not_ready sr
  have hrel : releaseReadySuffix l r = (l, r) := by
    simp [releaseReadySuffix, pl, pr, nr]
  change ackTail
    (releaseReadySuffix (normalizeCarrier (normalizeOrphan l))
      (normalizeCarrier (normalizeOrphan r))).1
    (releaseReadySuffix (normalizeCarrier (normalizeOrphan l))
      (normalizeCarrier (normalizeOrphan r))).2 = (l, r)
  simp only [orphan_safe l sl, orphan_safe r sr,
    carrier_safe l sl, carrier_safe r sr, hrel]
  by_cases ht : k = ψ - 1
  · have hn : r.state ≠ .lock := by
      rcases terminal_cases h4 (by omega : k + 1 = ψ) hR with hs | hs <;>
        simp [hs]
    simp [ackTail, pl, pr, hn]
  · simp [ackTail, pl, pr, ht]


-- Normalization; exact CHECK; DISAPPEAR; exact ReadyAck.
private theorem afterReset_good {ψ j k bL bR : Nat}
    (hp : 0 < ψ) (h4 : 4 ≤ ψ) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.label.val = j) (hr : r.label.val = k)
    (succ : k = (j + 1) % ψ)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR)
    (hL : BOrE ψ j l.state) (hR : BOrE ψ k r.state) :
    let q := AfterReset hp c l r
    Keep l q.1 ∧ Keep r q.2 ∧
      BOrE ψ j q.1.state ∧ BOrE ψ k q.2.state := by
  let a := Released l r
  have ha : Keep l a ∧ BOrE ψ j a.state := released_good h4 l r hL
  have pa : a.path = .some j bL := ha.1.2.1.trans pl
  let d := disappear hp a r
  have hd : Keep a d.1 ∧ Keep r d.2 ∧
      BOrE ψ j d.1.state ∧ BOrE ψ k d.2.state :=
    disappear_BOrE hp a r hr ha.2 hR
  have pdL : d.1.path = .some j bL := hd.1.2.1.trans pa
  have pdR : d.2.path = .some k bR := hd.2.1.2.1.trans pr
  have hrep := repair_BOrE h4 d.1 d.2 pdL pdR hd.2.2.1 hd.2.2.2
  have heq : AfterReset hp c l r = d := by
    simpa only [AfterReset,
      normalize_own_safe l hl pl (bore_safe hL),
      normalize_own_safe r hr pr (bore_safe hR),
      checkSource_BOrE_table hp h4 c l r hl hr succ pl pr hL hR]
      using hrep
  dsimp only
  rw [heq]
  exact ⟨keep_trans ha.1 hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩


private theorem bool_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all


/-- Stronger entrance: allow E at either physical terminal; arbitrary leaders. -/
theorem middle_BOrE_frame {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.label.val = j) (hr : r.label.val = k)
    (succ : k = (j + 1) % ψ)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR)
    (hL : BOrE ψ j l.state) (hR : BOrE ψ k r.state) :
    let q := Middle (by omega) c l r
    PairHole q ∨ TerminalE q ∨ ExactBFrame j k l r q := by
  have hp : 0 < ψ := by omega
  change PairHole (Middle hp c l r) ∨ TerminalE (Middle hp c l r) ∨
    ExactBFrame j k l r (Middle hp c l r)
  by_cases hb : l.leader = true ∨ l.reset_cmd = true ∨ r.reset_cmd = true
  · exact Or.inl ((middle_hole_iff hp c l r hl hr pl pr).mpr hb)
  · have hlead : l.leader = false := bool_false (fun h => hb (Or.inl h))
    have hresetL : l.reset_cmd = false :=
      bool_false (fun h => hb (Or.inr (Or.inl h)))
    have hresetR : r.reset_cmd = false :=
      bool_false (fun h => hb (Or.inr (Or.inr h)))
    have hpre : preCheckReset l r = (l, r) := by
      simp [preCheckReset, hlead, hresetL, hresetR]
    have heq : Middle hp c l r = AfterReset hp c l r := by
      simp only [middle_factor, drop_own l hl pl, drop_own r hr pr, hpre]
    have hg := afterReset_good hp h4 c l r hl hr succ pl pr hL hR
    rw [← heq] at hg
    rcases hg with ⟨fL, fR, sL, sR⟩
    rcases sL with bL | ⟨tL, eL⟩
    · rcases sR with bR | ⟨tR, eR⟩
      · exact Or.inr (Or.inr
          ⟨fL.1, fR.1, fL.2.1, fR.2.1, fL.2.2, fR.2.2, bL, bR⟩)
      · apply Or.inr
        apply Or.inl
        apply Or.inr
        refine ⟨?_, eR⟩
        rw [fR.1, hr]
        exact tR
    · apply Or.inr
      apply Or.inl
      apply Or.inl
      refine ⟨?_, eL⟩
      rw [fL.1, hl]
      exact tL


/-- Priority theorem: ordinary B inputs, with no E entrance assumption. -/
theorem middle_B_frame {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hl : l.label.val = j) (hr : r.label.val = k)
    (succ : k = (j + 1) % ψ)
    (pl : l.path = .some j bL) (pr : r.path = .some k bR)
    (hL : BState ψ j l.state) (hR : BState ψ k r.state) :
    let q := Middle (by omega) c l r
    PairHole q ∨ TerminalE q ∨ ExactBFrame j k l r q := by
  exact middle_BOrE_frame h4 c l r hl hr succ pl pr (Or.inl hL) (Or.inl hR)


#check middle_hole_iff
#check checkSource_BOrE_table
#check disappear_BOrE
#check repair_BOrE
#check middle_BOrE_frame
#check middle_B_frame
#print axioms middle_hole_iff
#print axioms checkSource_BOrE_table
#print axioms disappear_BOrE
#print axioms repair_BOrE
#print axioms middle_BOrE_frame
#print axioms middle_B_frame
end PPLLAstraR5MiddleB
