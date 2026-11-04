import Leader.Wu.Birth.CheckPermitRepairLeaf
import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducer

set_option autoImplicit false

/-! # Stage 4 of the R1 single-train argument: the CHECK chain, stage by stage

For an aligned train on a segment whose string equals the train string, R1 passes `equal` from label 0 to label
psi - 1 along the internal edges, one row per edge.  This file proves the stage-level pieces for general psi.

* `checkSig_first_row`: on the (label 0, label 1) pair with both cells check-open and matching, raw CHECK
  writes `equal` on both endpoints.
* `checkSig_chain_row`: when the initiator is already `equal` at a label below psi - 1 and the responder is
  check-open and matching, raw CHECK leaves the initiator unchanged and writes `equal` on the responder.
* `compare_keeps_equal`: the action-one authorized COMPARE leaves two `equal` endpoints `equal` when the
  initiator has no fresh-start permit (always the case off label 0, and at label 0 after R1's `permitFix`)
  and neither endpoint carries a path2 signal.
* `disappear_keeps_state`: DISAPPEAR leaves both main states unchanged when neither endpoint tosses and the
  responder is not the segment terminal. -/

namespace BirthCheckChainR1

open PPLL PPLLAuthorizedComparisonRepair

variable {ψ : Nat}

/-- A check-open resident carrier: aligned path whose bit matches the cell bit, no path2 signal, and a main
state from which SetReady arms and no CHECK wrapper is suppressed. -/
structure CheckOpenMatch (u : AgentState ψ) : Prop where
  path : u.path = .some u.label.val (if u.bit then 1 else 0)
  path2 : u.path2 = none
  notDepart : u.state ≠ .depart
  notEqual : u.state ≠ .equal
  notLarger : u.state ≠ .larger
  notLess : u.state ≠ .less

private theorem checkBit_self (b : Bool) : checkBit b (if b then 1 else 0) = .equal := by
  cases b <;> rfl

theorem checkSig_first_row (hψ : ψ > 0) (l r : AgentState ψ)
    (hl0 : l.label = ⟨0, hψ⟩) (hlab : l.label.val < ψ - 1)
    (hl : CheckOpenMatch l) (hr : CheckOpenMatch r) :
    (checkSig hψ l r).1.state = .equal ∧ (checkSig hψ l r).2.state = .equal ∧
      (checkSig hψ l r).1.path2 = none ∧ (checkSig hψ l r).2.path2 = none := by
  obtain ⟨hlp, hlp2, hld, hle, hlg, hls⟩ := hl
  obtain ⟨hrp, hrp2, hrd, hre, hrg, hrs⟩ := hr
  have hl0v : l.label.val = 0 := by rw [hl0]
  have h01 : 0 < ψ - 1 := by rw [hl0v] at hlab; exact hlab
  simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigCheckR, checkSigSetResult, hlp, hrp, hlp2, hrp2,
    hld, hle, hlg, hls, hrd, hre, hrg, hrs, hl0, checkBit_self, h01]

theorem checkSig_chain_row (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.state = .equal) (hlab : l.label.val < ψ - 1)
    (hr : CheckOpenMatch r) :
    (checkSig hψ l r).1 = l ∧ (checkSig hψ l r).2.state = .equal ∧ (checkSig hψ l r).2.path2 = none ∧
      (checkSig hψ l r).2.path = r.path ∧ (checkSig hψ l r).2.label = r.label ∧
      (checkSig hψ l r).2.bit = r.bit := by
  obtain ⟨hrp, hrp2, hrd, hre, hrg, hrs⟩ := hr
  refine ⟨?_, ?_⟩
  · cases hpath : l.path with
    | bot =>
        simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigSetResult, hpath, hl]
    | some a b =>
        simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigSetResult, hpath, hl]
        split <;> simp_all
  · simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigCheckR, checkSigSetResult, hrp, hrp2, hrd, hre,
      hrg, hrs, hl, checkBit_self]
    cases hpath : l.path with
    | bot => simp [hpath, hl, hlab]
    | some a b => split <;> simp_all

/-- COMPARE (action-one dispatch) keeps two `equal` endpoints when the initiator cannot start a fresh wave. -/
theorem compare_keeps_equal (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .equal) (hr : r.core.state = .equal)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = none)
    (hperm : l.core.label ≠ ⟨0, hψ⟩ ∨ l.path0Crossed = false) :
    let q := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hfresh : freshComparisonStart hψ
      (⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩ : AuthorizedAgentState ψ)
      = false := by
    unfold freshComparisonStart normalizePermit
    simp only [compareSigInit, hlpath]
    cases a with
    | zero =>
        rcases hperm with h | h
        · simp [h]
        · simp [h]
    | succ a => rfl
  simp only [PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne]
  have hinit : compareSigInit l.core = l.core := by simp [compareSigInit, hlpath]
  simp only [hinit, hlpath, hrpath]
  rw [hinit] at hfresh
  simp only [authorizedCmpUpdate, hfresh, Bool.false_and, if_false, Bool.false_eq_true]
  simp [cmpUpdateReturnPriority, cmpUpdateSetPath2, PPLLCompleteMultiLeaderCleanup.compareSigDispatchActionOne,
    hl, hr, hlp2, hrp2, hlpath]

/-- The fields the CHECK chain reads. -/
def chainView (u : AgentState ψ) : MainState × PathInfo × Option Path2Info × Fin ψ × Bool × Bool :=
  (u.state, u.path, u.path2, u.label, u.bit, u.leader)

/-- DISAPPEAR keeps the chain view of both endpoints when neither tosses and the responder is not the
segment terminal. -/
theorem disappear_keeps_view (hψ : ψ > 0) (l r : AgentState ψ)
    (hlt : l.state ≠ .toss) (hrt : r.state ≠ .toss) (hrterm : r.label ≠ ⟨ψ - 1, by omega⟩) :
    chainView (disappear hψ l r).1 = chainView l ∧ chainView (disappear hψ l r).2 = chainView r := by
  unfold disappear chainView
  by_cases hc : l.p_carry = true <;> by_cases hp : r.p = true <;> simp [hlt, hrt, hc, hp, hrterm]

/-- The width SUPPRESS keeps the chain view when the initiator is a follower and neither endpoint holds a
reset command. -/
theorem suppress_keeps_view {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) (hll : l.leader = false) (hlr : l.reset_cmd = false) (hrr : r.reset_cmd = false) :
    chainView (BirthShortWait.suppressSigResetKillWidth hψ hwidth hle l r).1 = chainView l ∧
      chainView (BirthShortWait.suppressSigResetKillWidth hψ hwidth hle l r).2 = chainView r := by
  unfold BirthShortWait.suppressSigResetKillWidth BirthShortWait.suppressPrefix BirthShortWait.shortCountReset
    chainView
  by_cases he : r.echo = true <;>
    simp [suppressSigStart, PPLLWallSweepRepair.resetKillComparison, suppressSigMoveReset, suppressSigTerminal, suppressSigEcho,
      suppressSigFinish, hll, hlr, hrr, he]

theorem disappear_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappear hψ l r).1.reset_cmd = l.reset_cmd ∧ (disappear hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold disappear
  by_cases ht : r.state = .toss ∧ r.label = ⟨0, hψ⟩ <;> by_cases hl : l.state = .toss ∧ l.label = ⟨0, hψ⟩ <;>
    by_cases hc : l.p_carry = true <;> by_cases hp : r.p = true <;> simp [ht, hl, hc, hp] <;> split <;> simp_all

/-- The fields the post-CHECK stages must keep for the chain. -/
def postView (u : AgentState ψ) : MainState × PathInfo × Option Path2Info × Fin ψ × Bool :=
  (u.state, u.path, u.path2, u.label, u.leader)

theorem postView_of_chainView {u v : AgentState ψ} (h : chainView u = chainView v) : postView u = postView v := by
  unfold chainView at h; unfold postView
  simp only [Prod.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem postView_of_swView {u v : AgentState ψ} (h : BirthStationaryWrite.swView u = BirthStationaryWrite.swView v) :
    postView u = postView v := by
  unfold BirthStationaryWrite.swView PPLLComparisonHistory.ComparisonTrackedView.ofState at h
  unfold postView
  simp only [Prod.mk.injEq, PPLLComparisonHistory.ComparisonTrackedView.mk.injEq] at h ⊢
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.1, h.1⟩

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

/-- Post-CHECK stages of the ordinary branch keep the chain fields of two `equal` endpoints: DISAPPEAR,
action-one COMPARE (no fresh start), width SUPPRESS and the stationary writer. -/
theorem afterCheck_keeps_chain {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .equal) (hr : r.core.state = .equal)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = none)
    (hperm : l.core.label ≠ ⟨0, hψ⟩ ∨ l.path0Crossed = false)
    (hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  -- DISAPPEAR
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_keeps_view hψ l.core r.core (by rw [hl]; decide) (by rw [hr]; decide) hrterm
  have hdr := disappear_reset_cmd hψ l.core r.core
  have h0c1 : q0.1.core = (disappear hψ l.core r.core).1 := rfl
  have h0c2 : q0.2.core = (disappear hψ l.core r.core).2 := rfl
  have e1 := hd.1; have e2 := hd.2
  unfold chainView at e1 e2
  simp only [Prod.mk.injEq] at e1 e2
  have h0perm : q0.1.core.label ≠ ⟨0, hψ⟩ ∨ q0.1.path0Crossed = false := by
    rcases hperm with h | h
    · left; rw [h0c1, e1.2.2.2.1]; exact h
    · right
      show reconcilePermit l (disappear hψ l.core r.core).1 = false
      unfold reconcilePermit normalizePermit
      split
      · split <;> simp_all
      · rfl
  -- COMPARE
  have hc := compare_keeps_equal hψ q0.1 q0.2 a b c d
    (by rw [h0c1, e1.2.1]; exact hlpath) (by rw [h0c2, e2.2.1]; exact hrpath)
    (by rw [h0c1, e1.1]; exact hl) (by rw [h0c2, e2.1]; exact hr)
    (by rw [h0c1, e1.2.2.1]; exact hlp2) (by rw [h0c2, e2.2.2.1]; exact hrp2) h0perm
  -- SUPPRESS
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have hq1a : q1.1.core = q0.1.core := hc.1
  have hq1b : q1.2.core = q0.2.core := hc.2
  have hs := suppress_keeps_view hψ hwidth hle q1.1.core q1.2.core
    (by rw [hq1a, h0c1, e1.2.2.2.2.2]; exact hll) (by rw [hq1a, h0c1, hdr.1]; exact hlr)
    (by rw [hq1b, h0c2, hdr.2]; exact hrr)
  -- writer
  let q2 := BirthShortDoneCuts.authorizedSuppressWidth hψ hwidth hle q1.1 q1.2
  have hq2a : q2.1.core = (BirthShortWait.suppressSigResetKillWidth hψ hwidth hle q1.1.core q1.2.core).1 := rfl
  have hq2b : q2.2.core = (BirthShortWait.suppressSigResetKillWidth hψ hwidth hle q1.1.core q1.2.core).2 := rfl
  have hw := BirthStationaryWrite.stationaryPersistentRaw_frame hψ q2.1.core q2.2.core
  unfold BirthStationaryWrite.swPair at hw
  obtain ⟨hwa, hwb⟩ := Prod.mk.inj hw
  have hfin : BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r =
      BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2 := rfl
  have hc1 : (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).1.core =
      (BirthStationaryWrite.stationaryPersistentRaw hψ q2.1.core q2.2.core).1 := rfl
  have hc2 : (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).2.core =
      (BirthStationaryWrite.stationaryPersistentRaw hψ q2.1.core q2.2.core).2 := rfl
  have hw1 : postView (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).1.core =
      postView q2.1.core := by
    rw [hc1]; exact postView_of_swView hwa
  have hw2 : postView (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).2.core =
      postView q2.2.core := by
    rw [hc2]; exact postView_of_swView hwb
  have hs1 : postView q2.1.core = postView q1.1.core := by rw [hq2a]; exact postView_of_chainView hs.1
  have hs2 : postView q2.2.core = postView q1.2.core := by rw [hq2b]; exact postView_of_chainView hs.2
  have hd1 : postView q0.1.core = postView l.core := by rw [h0c1]; exact postView_of_chainView hd.1
  have hd2 : postView q0.2.core = postView r.core := by rw [h0c2]; exact postView_of_chainView hd.2
  rw [hfin]
  exact ⟨hw1.trans (hs1.trans (by rw [hq1a]; exact hd1)), hw2.trans (hs2.trans (by rw [hq1b]; exact hd2))⟩

/-! ## The generation prefix (P-prime wall, WAIT, GEN, CLEAN, ELIMINATE) keeps the chain view -/

/-- Fields of a chain carrier that the generation prefix must keep. -/
def genView (u : AgentState ψ) : MainState × PathInfo × Option Path2Info × Fin ψ × Bool × Bool × Bool :=
  (u.state, u.path, u.path2, u.label, u.bit, u.leader, u.reset_cmd)

def genPair (q : AgentState ψ × AgentState ψ) := (genView q.1, genView q.2)

theorem genConnect_genView (u : AgentState ψ) : genView (cleanSigGenConnect u) = genView u := by
  unfold cleanSigGenConnect
  split
  · dsimp only; split <;> split <;> rfl
  · rfl

theorem step3_genPair (l r : AgentState ψ) : genPair (cleanSigStep3 l r) = genPair (l, r) := by
  unfold cleanSigStep3
  split
  · split
    · dsimp only; split <;> rfl
    · rfl
  · rfl

theorem step4_genPair (l r : AgentState ψ) : genPair (cleanSigStep4 l r) = genPair (l, r) := by
  unfold cleanSigStep4
  split
  · split
    · dsimp only; split <;> rfl
    · rfl
  · rfl

theorem step5_genPair (hψ : 0 < ψ) (l r : AgentState ψ) : genPair (cleanSigStep5 hψ l r) = genPair (l, r) := by
  unfold cleanSigStep5
  split
  · dsimp only; split
    · split <;> rfl
    · rfl
  · rfl

theorem step6_genPair (hψ : 0 < ψ) (l r : AgentState ψ) : genPair (cleanSigStep6 hψ l r) = genPair (l, r) := by
  unfold cleanSigStep6
  split
  · dsimp only; split
    · split <;> rfl
    · rfl
  · rfl

theorem cleanApply_genView (u : AgentState ψ) (h4 : ∀ p, u.path4 = some p → p.1 ≠ -1)
    (h5 : ∀ p, u.path5 = some p → p.1 ≠ -1) : genView (cleanSigCleanApply u) = genView u := by
  unfold cleanSigCleanApply
  split
  · rfl
  · dsimp only
    cases h4' : u.path4 with
    | none =>
        cases h5' : u.path5 with
        | none => rfl
        | some q => have := h5 q h5'; simp [this, h5']
    | some q4 =>
        have hq4 := h4 q4 h4'
        cases h5' : u.path5 with
        | none => simp [hq4, h4', h5']
        | some q => have := h5 q h5'; simp [hq4, this, h4', h5']

theorem ofNat_ne_neg_one (k : Nat) : (Int.ofNat k : Int) ≠ -1 := by
  simp only [Int.ofNat_eq_natCast]; omega

/-- CLEAN keeps the chain view on an internal edge of an aligned consistent pair when the markers that GenConnect
does not overwrite are not clean commands. -/
theorem cleanSig_keeps_genView (hψ : 0 < ψ) (l r : AgentState ψ) (i bl br : Nat)
    (hlp : l.path = .some i bl) (hrp : r.path = .some (i + 1) br) (hi : i + 1 < ψ)
    (hl4 : i = 0 → ∀ p, l.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.path5 = some p → p.1 ≠ -1) :
    genPair (cleanSig hψ l r) = genPair (l, r) := by
  have hne : i ≠ ψ - 1 := by omega
  have hsub : (Int.ofNat i : Int) = Int.ofNat (i + 1) - 1 := by simp only [Int.ofNat_eq_natCast]; omega
  have hl1p : (cleanSigGenConnect l).path = .some i bl := by simp [cleanSigGenConnect, hlp]
  have hr1p : (cleanSigGenConnect r).path = .some (i + 1) br := by simp [cleanSigGenConnect, hrp]
  have hl15 : (cleanSigGenConnect l).path5 = some (Int.ofNat i, 1) := by simp [cleanSigGenConnect, hlp, hne]
  have hr14 : (cleanSigGenConnect r).path4 = some (Int.ofNat (i + 1), 1) := by simp [cleanSigGenConnect, hrp]
  have hl14 : ∀ p, (cleanSigGenConnect l).path4 = some p → p.1 ≠ -1 := by
    intro p hp
    by_cases h0 : i = 0
    · subst h0
      simp [cleanSigGenConnect, hlp, hne] at hp
      exact hl4 rfl p hp
    · simp [cleanSigGenConnect, hlp, hne, h0] at hp
      subst hp; exact ofNat_ne_neg_one i
  have hr15 : ∀ p, (cleanSigGenConnect r).path5 = some p → p.1 ≠ -1 := by
    intro p hp
    by_cases h1 : i + 1 = ψ - 1
    · simp [cleanSigGenConnect, hrp, h1] at hp
      exact hr5 p hp
    · simp [cleanSigGenConnect, hrp, h1] at hp
      subst hp; exact ofNat_ne_neg_one (i + 1)
  generalize hL : cleanSigGenConnect l = L at *
  generalize hR : cleanSigGenConnect r = R at *
  have hlv : genView L = genView l := by rw [← hL]; exact genConnect_genView l
  have hrv : genView R = genView r := by rw [← hR]; exact genConnect_genView r
  have hq3 : cleanSigStep3 L R = (L, { R with path4 := none }) := by
    unfold cleanSigStep3; rw [hr14, hl1p]; simp [ofNat_ne_neg_one]
    intro h; exact absurd h (by omega)
  have hq4 : cleanSigStep4 L { R with path4 := none } = ({ L with path5 := none }, { R with path4 := none }) := by
    unfold cleanSigStep4; rw [hl15]; simp [hr1p, ofNat_ne_neg_one, ← hsub]
  have hq5 : cleanSigStep5 hψ { L with path5 := none } { R with path4 := none } =
      ({ L with path5 := none }, { R with path4 := none }) := by
    unfold cleanSigStep5; rfl
  have hq6 : cleanSigStep6 hψ { L with path5 := none } { R with path4 := none } =
      ({ L with path5 := none }, { R with path4 := none }) := by
    unfold cleanSigStep6; rfl
  have hal : genView (cleanSigCleanApply { L with path5 := none }) = genView l := by
    rw [cleanApply_genView ({ L with path5 := none }) (fun p hp => hl14 p hp) (fun p hp => by simp at hp)]
    exact hlv
  have har : genView (cleanSigCleanApply { R with path4 := none }) = genView r := by
    rw [cleanApply_genView ({ R with path4 := none }) (fun p hp => by simp at hp) (fun p hp => hr15 p hp)]
    exact hrv
  unfold cleanSig genPair
  rw [hL, hR]
  simp only [hq3, hq4, hq5, hq6]
  exact Prod.ext hal har

theorem pPsiWall_keeps_genView (hψ : 0 < ψ) (l r : AgentState ψ)
    (hcons : r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) (hll : l.leader = false) (hrl : r.leader = false) :
    genView (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l r).1 = genView l ∧
      genView (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l r).2 = genView r := by
  unfold PPLLWallSweepRepair.pPsiLeaderResetProbeWall pPsi genView
  by_cases hp : r.probe = true <;> by_cases hc : l.reset_cmd = true <;> simp [hll, hrl, hcons, hp, hc]


theorem genPair_prepare (hψ : 0 < ψ) (l r : AgentState ψ) :
    genPair (PPLLRepair.waitSaturatedPrepare hψ l r) = genPair (l, r) := by
  unfold PPLLRepair.waitSaturatedPrepare genPair genView
  by_cases h1 : r.label = ⟨0, hψ⟩ <;> by_cases h2 : l.label = ⟨0, hψ⟩ <;> by_cases h3 : l.h_field = true <;>
    simp [h1, h2, h3]

theorem genPair_inactive {width : Nat} (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    genPair (BirthShortWaitTerminalEntryRepair.terminalInactiveClear hwidth hle l r) = genPair (l, r) := by
  unfold BirthShortWaitTerminalEntryRepair.terminalInactiveClear genPair genView
  split <;> rfl

theorem genPair_carry {width κ : Nat} (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    genPair (BirthShortWait.waitWidthCarry hwidth hle κ l r) = genPair (l, r) := by
  unfold BirthShortWait.waitWidthCarry genPair genView
  repeat (first | rfl | split)

theorem genPair_reset {width : Nat} (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    genPair (BirthShortWait.waitWidthReset hwidth hle l r) = genPair (l, r) := by
  unfold BirthShortWait.waitWidthReset genPair genView
  repeat (first | rfl | split)

theorem genPair_finish {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    genPair (BirthShortWait.waitWidthFinish hψ hwidth hle κ l r) = genPair (l, r) := by
  unfold BirthShortWait.waitWidthFinish genPair genView
  by_cases h1 : r.label = BirthShortWait.widthTerminal hwidth hle ∧ r.count = κ <;> simp only [h1, if_true, if_false]
  · by_cases h2 : l.label ≠ ⟨ψ - 1, by omega⟩ <;> simp [h2]
  · by_cases h2 : r.wait = false ∧ l.label ≠ ⟨ψ - 1, by omega⟩ <;> simp [h2]

theorem waitWidthEntry_keeps_genView {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    genPair (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ l r) = genPair (l, r) := by
  unfold BirthShortWaitTerminalEntryRepair.waitWidthEntry
  dsimp only
  rw [genPair_finish, genPair_reset, genPair_carry, genPair_inactive, genPair_prepare]

theorem genCleanAfterWait_keeps_genView (hψ : 0 < ψ) (l r : AgentState ψ) (a b : Nat)
    (hlp : l.path = .some a b) (hlpr : l.state ≠ .produce) (hldn : l.state ≠ .done)
    (hrpr : r.state ≠ .produce) (hrdn : r.state ≠ .done) :
    genPair (BirthGenerationControlRepair.genCleanAfterWait hψ l r) = genPair (l, r) := by
  unfold BirthGenerationControlRepair.genCleanAfterWait PPLLRepair.genSigSaturatedStart
    BirthGenerationControlRepair.genCleanEmit BirthGenerationControlRepair.genCleanPropagate
    PPLLRepair.genSigSaturatedFinish genPair genView
  simp [hlp, hlpr, hldn, hrpr, hrdn]

/-- ELIMINATE is the identity unless the responder carries `eliminate_signal`. -/
theorem eliminateSig_of_not_signal (hψ : 0 < ψ) (l r : AgentState ψ) (h : r.state ≠ .eliminate_signal) :
    eliminateSig hψ l r = (l, r) := by
  simp [eliminateSig, h]

/-- The two CLEAN markers, which the stages before CLEAN must also keep. -/
def markers (u : AgentState ψ) : Option (Int × Nat) × Option (Int × Nat) := (u.path4, u.path5)

theorem pPsiWall_keeps_markers (hψ : 0 < ψ) (l r : AgentState ψ) :
    markers (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l r).1 = markers l ∧
      markers (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l r).2 = markers r := by
  unfold PPLLWallSweepRepair.pPsiLeaderResetProbeWall pPsi markers
  by_cases h1 : l.leader = true <;> by_cases h2 : r.leader = true ∨ l.leader = true ∨ l.reset_cmd = true <;>
    simp only [h1, h2, if_true, if_false] <;> split <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> simp_all

def markerPair (q : AgentState ψ × AgentState ψ) := (markers q.1, markers q.2)

theorem markerPair_prepare (hψ : 0 < ψ) (l r : AgentState ψ) :
    markerPair (PPLLRepair.waitSaturatedPrepare hψ l r) = markerPair (l, r) := by
  unfold PPLLRepair.waitSaturatedPrepare markerPair markers
  by_cases h1 : r.label = ⟨0, hψ⟩ <;> by_cases h2 : l.label = ⟨0, hψ⟩ <;> by_cases h3 : l.h_field = true <;>
    simp [h1, h2, h3]

theorem markerPair_inactive {width : Nat} (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    markerPair (BirthShortWaitTerminalEntryRepair.terminalInactiveClear hwidth hle l r) = markerPair (l, r) := by
  unfold BirthShortWaitTerminalEntryRepair.terminalInactiveClear markerPair markers
  split <;> rfl

theorem markerPair_carry {width κ : Nat} (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    markerPair (BirthShortWait.waitWidthCarry hwidth hle κ l r) = markerPair (l, r) := by
  unfold BirthShortWait.waitWidthCarry markerPair markers
  repeat (first | rfl | split)

theorem markerPair_reset {width : Nat} (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    markerPair (BirthShortWait.waitWidthReset hwidth hle l r) = markerPair (l, r) := by
  unfold BirthShortWait.waitWidthReset markerPair markers
  repeat (first | rfl | split)

theorem markerPair_finish {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    markerPair (BirthShortWait.waitWidthFinish hψ hwidth hle κ l r) = markerPair (l, r) := by
  unfold BirthShortWait.waitWidthFinish markerPair markers
  by_cases h1 : r.label = BirthShortWait.widthTerminal hwidth hle ∧ r.count = κ <;> simp only [h1, if_false]
  · by_cases h2 : l.label ≠ ⟨ψ - 1, by omega⟩ <;> simp [h2]
  · by_cases h2 : r.wait = false ∧ l.label ≠ ⟨ψ - 1, by omega⟩ <;> simp [h2]

theorem waitWidthEntry_keeps_markers {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    markerPair (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ l r) = markerPair (l, r) := by
  unfold BirthShortWaitTerminalEntryRepair.waitWidthEntry
  dsimp only
  rw [markerPair_finish, markerPair_reset, markerPair_carry, markerPair_inactive, markerPair_prepare]

theorem genCleanAfterWait_keeps_markers (hψ : 0 < ψ) (l r : AgentState ψ) :
    markers (BirthGenerationControlRepair.genCleanAfterWait hψ l r).1 = markers l ∧
      markers (BirthGenerationControlRepair.genCleanAfterWait hψ l r).2 = markers r := by
  unfold BirthGenerationControlRepair.genCleanAfterWait PPLLRepair.genSigSaturatedStart
    BirthGenerationControlRepair.genCleanEmit BirthGenerationControlRepair.genCleanPropagate
    PPLLRepair.genSigSaturatedFinish markers
  constructor <;> (repeat (first | rfl | (split <;> try dsimp only)))

/-! ## The pre-CHECK prefix after generation keeps two aligned chain carriers -/

section Prefix

open PPLLResearchFormulation PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthGenerationDone BirthSingleUseReleaseRepair BirthShortDoneTerminalEntryCut

/-- A resident aligned carrier that the DONE move, reset wall and sanitizer leave alone. -/
structure Resident (hψ : 0 < ψ) (u : AgentState ψ) : Prop where
  leader : u.leader = false
  reset : u.reset_cmd = false
  path : ∃ a b, u.path = .some a b
  path2 : u.path2 = none
  notDone : u.state ≠ .done
  notDepart : u.state ≠ .depart
  notTerminalEqual : u.label ≠ ⟨ψ - 1, by omega⟩ ∨ u.state ≠ .equal

theorem doneCaptureSigMove_eq_of_resident (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : Resident hψ l) (hr : Resident hψ r) : doneCaptureSigMove hψ l r = (l, r) := by
  obtain ⟨hlL, _, ⟨la, lb, hlP⟩, hlP2, hlD, hlDp, _⟩ := hl
  obtain ⟨hrL, _, ⟨ra, rb, hrP⟩, hrP2, hrD, hrDp, _⟩ := hr
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, hlL, hrL]
  have hm : doneTransfers l r = (l, r) := by
    simp [doneTransfers, holdDoneStep1, hlD, captureStep1, hlP, hrP, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, hlP2, hrP2]
  have hw : comparisonLeaderWall l r = (l, r) := by
    simp [comparisonLeaderWall, hlL, hrL]
  have hc : singleUseControlTail hψ l r = (l, r) := by
    simp [singleUseControlTail, singleUseApplyControl, hlP2, hrP2, hrDp]
  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hm]
  dsimp only
  rw [hw]
  exact hc

/-- DONE move, reset wall and sanitizer keep the cores of two residents. -/
theorem doneBeforeCheck_cores_of_residents {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : Resident hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core)
    (hr : Resident hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core) :
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
    let d := doneBeforeCheckEntryWidth hψ hwidth hle κ l r
    d.1.core = b.1.core ∧ d.2.core = b.2.core := by
  intro b d
  let m := authorizedDoneMove hψ b.1 b.2
  have hmc := authorizedDoneMove_core hψ b.1 b.2
  rw [doneCaptureSigMove_eq_of_resident hψ _ _ hl hr] at hmc
  have hm1 : m.1.core = b.1.core := congrArg Prod.fst hmc
  have hm2 : m.2.core = b.2.core := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hl.leader) (by rw [hm1]; exact hl.reset)
      (by rw [hm2]; exact hr.reset)
  have hs : ∀ u : AuthorizedAgentState ψ, Resident hψ u.core → sanitizeAuthorizedTerminalEqual hψ u = u := by
    intro u hu
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rcases hu.notTerminalEqual with h | h <;> simp [h]
  have hd : d = sanitizeAuthorizedPair hψ (preCheckResetWall m.1 m.2) := rfl
  rw [hd, hw]
  simp only [sanitizeAuthorizedPair]
  rw [hs m.1 (by rw [hm1]; exact hl), hs m.2 (by rw [hm2]; exact hr)]
  exact ⟨hm1, hm2⟩

/-- With two residents outside toss and congest, the actual CHECK cut is raw CHECK on the generation output. -/
theorem authorizedCheckSig_cores (hψ : 0 < ψ) (x y : AuthorizedAgentState ψ) :
    (authorizedCheckSig hψ x y).1.core = (checkSig hψ x.core y.core).1 ∧
      (authorizedCheckSig hψ x y).2.core = (checkSig hψ x.core y.core).2 := ⟨rfl, rfl⟩

/-- With two residents outside toss and congest, the actual CHECK cut is raw CHECK on the generation output. -/
theorem doneThroughCheck_cores {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : Resident hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core)
    (hr : Resident hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core)
    (hlt : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.state ≠ .toss)
    (hrt : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.state ≠ .toss)
    (hlc : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.state ≠ .congest)
    (hrc : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.state ≠ .congest) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core =
        (checkSig hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core
          (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core).1 ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core =
        (checkSig hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core
          (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core).2 := by
  have hd := doneBeforeCheck_cores_of_residents hψ hwidth hle l r hl hr
  have hc : doneThroughCheckEntryWidth hψ hwidth hle κ l r =
      preserveDoneCheck hψ (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).1
        (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).2 := rfl
  rw [hc]
  generalize hbb : generationBeforeMoveEntryWidth hψ hwidth hle κ l r = b at *
  generalize hdd : doneBeforeCheckEntryWidth hψ hwidth hle κ l r = d at *
  simp only at hd
  rw [preserveDoneCheck_of_no_done hψ d.1 d.2 (by rw [hd.1]; exact hl.notDone) (by rw [hd.2]; exact hr.notDone),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ d.1 d.2 (by rw [hd.1]; exact hlt)
      (by rw [hd.2]; exact hrt),
    BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ d.1 d.2 (by rw [hd.1]; exact hlc)
      (by rw [hd.2]; exact hrc)]
  have e := authorizedCheckSig_cores hψ d.1 d.2
  rw [e.1, e.2, hd.1, hd.2]
  exact ⟨rfl, rfl⟩

theorem genPair_eq_iff {q q' : AgentState ψ × AgentState ψ} :
    genPair q = genPair q' ↔ genView q.1 = genView q'.1 ∧ genView q.2 = genView q'.2 := by
  unfold genPair; exact Iff.of_eq (Prod.mk.injEq _ _ _ _)

theorem markerPair_eq_iff {q q' : AgentState ψ × AgentState ψ} :
    markerPair q = markerPair q' ↔ markers q.1 = markers q'.1 ∧ markers q.2 = markers q'.2 := by
  unfold markerPair; exact Iff.of_eq (Prod.mk.injEq _ _ _ _)

/-- The whole generation prefix keeps the chain view of an aligned consistent follower pair. -/
theorem generation_keeps_chain {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (i bl br : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hrp : r.core.path = .some (i + 1) br) (hi : i + 1 < ψ)
    (hlpr : l.core.state ≠ .produce) (hldn : l.core.state ≠ .done)
    (hrpr : r.core.state ≠ .produce) (hrdn : r.core.state ≠ .done) (hrel : r.core.state ≠ .eliminate_signal)
    (hl4 : i = 0 → ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    genView (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core = genView l.core ∧
      genView (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core = genView r.core := by
  have hgen : generationBeforeMoveEntryWidth hψ hwidth hle κ l r =
      authorizedEliminateSig hψ
        (authorizedCleanSig hψ
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).1
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1
        (authorizedCleanSig hψ
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).1
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2 := rfl
  rw [hgen]
  generalize hA0 : PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r = A0
  have c0 : (A0.1.core, A0.2.core) = PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l.core r.core := by
    rw [← hA0]; rfl
  generalize hA1 : authorizedGenCleanEntryWidth hψ hwidth hle κ A0.1 A0.2 = A1
  have c1 : (A1.1.core, A1.2.core) = BirthGenerationControlRepair.genCleanAfterWait hψ
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ A0.1.core A0.2.core).1
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ A0.1.core A0.2.core).2 := by
    rw [← hA1]; rfl
  generalize hA2 : authorizedCleanSig hψ A1.1 A1.2 = A2
  have c2 : (A2.1.core, A2.2.core) = cleanSig hψ A1.1.core A1.2.core := by rw [← hA2]; rfl
  have c3 : ((authorizedEliminateSig hψ A2.1 A2.2).1.core, (authorizedEliminateSig hψ A2.1 A2.2).2.core) =
      eliminateSig hψ A2.1.core A2.2.core := rfl
  -- P-prime wall
  have hw := pPsiWall_keeps_genView hψ l.core r.core hcons hll hrl
  have hwm := pPsiWall_keeps_markers hψ l.core r.core
  rw [← c0] at hw hwm
  -- WAIT
  generalize hW : BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ A0.1.core A0.2.core = W at c1
  have hwt := genPair_eq_iff.1 (show genPair W = genPair (A0.1.core, A0.2.core) by
    rw [← hW]; exact waitWidthEntry_keeps_genView hψ hwidth hle _ _)
  have hwtm := markerPair_eq_iff.1 (show markerPair W = markerPair (A0.1.core, A0.2.core) by
    rw [← hW]; exact waitWidthEntry_keeps_markers hψ hwidth hle _ _)
  have v1 : genView W.1 = genView l.core := hwt.1.trans hw.1
  have v2 : genView W.2 = genView r.core := hwt.2.trans hw.2
  have m1 : markers W.1 = markers l.core := hwtm.1.trans hwm.1
  have m2 : markers W.2 = markers r.core := hwtm.2.trans hwm.2
  have v1' := v1; have v2' := v2
  unfold genView at v1' v2'; unfold markers at m1 m2
  simp only [Prod.mk.injEq] at v1' v2' m1 m2
  -- GEN
  have hg := genPair_eq_iff.1 (genCleanAfterWait_keeps_genView hψ W.1 W.2 i bl (by rw [v1'.2.1]; exact hlp)
    (by rw [v1'.1]; exact hlpr) (by rw [v1'.1]; exact hldn) (by rw [v2'.1]; exact hrpr) (by rw [v2'.1]; exact hrdn))
  have hgm := markerPair_eq_iff.1 (show markerPair (BirthGenerationControlRepair.genCleanAfterWait hψ W.1 W.2) =
      markerPair (W.1, W.2) from Prod.ext (genCleanAfterWait_keeps_markers hψ W.1 W.2).1
        (genCleanAfterWait_keeps_markers hψ W.1 W.2).2)
  rw [← c1] at hg hgm
  have g1 : genView A1.1.core = genView l.core := hg.1.trans v1
  have g2 : genView A1.2.core = genView r.core := hg.2.trans v2
  have gm1 : A1.1.core.path4 = l.core.path4 := by
    have := congrArg Prod.fst hgm.1; exact this.trans m1.1
  have gm2 : A1.2.core.path5 = r.core.path5 := by
    have := congrArg Prod.snd hgm.2; exact this.trans m2.2
  have g1' := g1; have g2' := g2
  unfold genView at g1' g2'
  simp only [Prod.mk.injEq] at g1' g2'
  -- CLEAN
  have hc := genPair_eq_iff.1 (cleanSig_keeps_genView hψ A1.1.core A1.2.core i bl br (by rw [g1'.2.1]; exact hlp)
    (by rw [g2'.2.1]; exact hrp) hi (by rw [gm1]; exact hl4) (by rw [gm2]; exact hr5))
  rw [← c2] at hc
  have k1 : genView A2.1.core = genView l.core := hc.1.trans g1
  have k2 : genView A2.2.core = genView r.core := hc.2.trans g2
  -- ELIMINATE
  have hrc : A2.2.core.state ≠ .eliminate_signal := by
    have := congrArg (fun v => v.1) k2
    simp only [genView] at this
    rw [this]; exact hrel
  have he : eliminateSig hψ A2.1.core A2.2.core = (A2.1.core, A2.2.core) :=
    eliminateSig_of_not_signal hψ A2.1.core A2.2.core hrc
  rw [he] at c3
  obtain ⟨e3a, e3b⟩ := Prod.mk.inj c3
  rw [e3a, e3b]
  exact ⟨k1, k2⟩

end Prefix

end BirthCheckChainR1
