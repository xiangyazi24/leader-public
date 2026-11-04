import Leader.Wu.Birth.CheckPermitRepairRowLift

set_option autoImplicit false

/-! # Internal non-request letters of the R1 CHECK chain

While the CHECK chain runs through an aligned train, a letter on an internal edge whose two cells are both already
`equal` must not disturb the chain.  `checkSig_equal_equal`: raw CHECK is the identity on two `equal` cells when the
responder is not the segment terminal.  `ordinary_equal_row`: the R1 ordinary branch keeps state, path, path2, label
and follower status of both endpoints of such an edge (the permit fix clears the initiator permit, so COMPARE cannot
start a fresh wave).  `r1_equal_row`: the same on the actual R1 row output, with positive stalls. -/

namespace BirthCheckChainR1Internal

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut
open BirthCheckChainR1

set_option Elab.async false

variable {ψ κ τ : Nat}

theorem checkSig_equal_equal (hψ : ψ > 0) (l r : AgentState ψ) (hl : l.state = .equal) (hr : r.state = .equal)
    (hrterm : r.label ≠ ⟨ψ - 1, by omega⟩) :
    checkSig hψ l r = (l, r) := by
  have hsl : checkSigSetReady l = l := by
    unfold checkSigSetReady; split
    · simp [hl]
    · rfl
  have hsr : checkSigSetReady r = r := by
    unfold checkSigSetReady; split
    · simp [hr]
    · rfl
  have hcl : checkSigCheckL hψ l = l := by
    unfold checkSigCheckL; split
    · simp [hl]
    · rfl
  have hcr : checkSigCheckR hψ l r = r := by
    unfold checkSigCheckR; split
    · split
      · simp [hr]
      · rfl
    · rfl
  have hrl : checkSigSetResult l = l := by simp [checkSigSetResult, hl]
  have hrr : checkSigSetResult r = r := by simp [checkSigSetResult, hr]
  unfold checkSig
  simp only [hsl, hsr, hcl, hcr, hrl, hrr]
  rw [if_neg (by intro h; exact hrterm h.1)]

/-- An internal edge with both cells `equal`: the R1 ordinary branch keeps the chain fields of both endpoints. -/
theorem ordinary_equal_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (i bl br : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hrp : r.core.path = .some (i + 1) br)
    (hlab : l.core.label.val = i) (hi : i + 1 < ψ - 1)
    (hleq : l.core.state = .equal) (hreq : r.core.state = .equal)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = none)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  intro q
  have hi' : i + 1 < ψ := by omega
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r i bl br hcons hll hrl hlp hrp hi'
    (by rw [hleq]; decide) (by rw [hleq]; decide) (by rw [hreq]; decide) (by rw [hreq]; decide)
    (by rw [hreq]; decide) hl4 hr5
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hlabne : B.1.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [lb1] at this; simp only at this; omega
  have hrlab : r.core.label.val = i + 1 := by
    rw [hcons]; show (l.core.label.val + 1) % ψ = i + 1; rw [hlab, Nat.mod_eq_of_lt hi']
  have hrne : B.2.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [lb2, hrlab] at this; simp only at this; omega
  have res1 : Resident hψ B.1.core :=
    ⟨by rw [ld1]; exact hll, by rw [rc1]; exact hlr, ⟨i, bl, by rw [p1]; exact hlp⟩, by rw [q1]; exact hlp2,
      by rw [s1, hleq]; decide, by rw [s1, hleq]; decide, Or.inl hlabne⟩
  have res2 : Resident hψ B.2.core :=
    ⟨by rw [ld2]; exact hrl, by rw [rc2]; exact hrr, ⟨i + 1, br, by rw [p2]; exact hrp⟩, by rw [q2]; exact hrp2,
      by rw [s2, hreq]; decide, by rw [s2, hreq]; decide, Or.inl hrne⟩
  have hcut := doneThroughCheck_cores (κ := κ) hψ (by decide : 0 < 2) h2 l r
    (by rw [hB]; exact res1) (by rw [hB]; exact res2)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2, hreq]; decide)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2, hreq]; decide)
  rw [hB] at hcut
  have hck := checkSig_equal_equal hψ B.1.core B.2.core (by rw [s1]; exact hleq) (by rw [s2]; exact hreq) hrne
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  rw [hck] at hc1 hc2
  have hfix : BirthCheckPermitRepair.permitFix C.1 = ⟨C.1.core, false⟩ := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1, s1, hleq]; simp
  have hac := afterCheck_keeps_chain hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 i bl (i + 1) br
    (by show C.1.core.path = _; rw [hc1, p1]; exact hlp)
    (by rw [hc2, p2]; exact hrp)
    (by show C.1.core.state = _; rw [hc1, s1]; exact hleq)
    (by rw [hc2, s2]; exact hreq)
    (by show C.1.core.path2 = _; rw [hc1, q1]; exact hlp2)
    (by rw [hc2, q2]; exact hrp2)
    (Or.inr rfl)
    (by rw [hc2]; exact hrne)
    (by show C.1.core.leader = _; rw [hc1, ld1]; exact hll)
    (by show C.1.core.reset_cmd = _; rw [hc1, rc1]; exact hlr)
    (by rw [hc2, rc2]; exact hrr)
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 = Q
    at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have pv1' := pv1; have pv2' := pv2
  unfold postView at pv1' pv2'
  simp only [Prod.mk.injEq] at pv1' pv2'
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1'.2.2.2.2, pv2'.2.2.2.2]
    show (!l.core.leader && C.1.core.leader || !r.core.leader && C.2.core.leader) = false
    rw [hc1, ld1, hll, hc2, ld2, hrl]
    rfl
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  have e1 : postView C.1.core = postView l.core := by
    unfold postView; rw [hc1, s1, p1, q1, lb1, ld1]
  have e2 : postView C.2.core = postView r.core := by
    unfold postView; rw [hc2, s2, p2, q2, lb2, ld2]
  exact ⟨pv1.trans e1, pv2.trans e2⟩

/-! ## Two check-open matching cells above label 0 -/

theorem setReady_open (u : AgentState ψ) (h : CheckOpenMatch u) :
    checkSigSetReady u = { u with state := .CHECK_ready } := by
  unfold checkSigSetReady
  rw [h.path]
  simp [h.notDepart, h.notEqual, h.notLarger, h.notLess]

theorem checkSig_open_open (hψ : ψ > 0) (l r : AgentState ψ) (hl : CheckOpenMatch l) (hr : CheckOpenMatch r)
    (hl0 : l.label ≠ ⟨0, hψ⟩) :
    checkSig hψ l r = ({ l with state := .CHECK_ready }, { r with state := .CHECK_ready }) := by
  have hsl := setReady_open l hl
  have hsr := setReady_open r hr
  have hcl : checkSigCheckL hψ { l with state := .CHECK_ready } = { l with state := .CHECK_ready } := by
    unfold checkSigCheckL
    split
    · simp [hl0]
    · rfl
  have hcr : checkSigCheckR hψ { l with state := .CHECK_ready } { r with state := .CHECK_ready } =
      { r with state := .CHECK_ready } := by
    unfold checkSigCheckR; split
    · simp
    · rfl
  unfold checkSig
  simp only [hsl, hsr, hcl, hcr]
  simp [checkSigSetResult]

theorem compare_keeps_quiet (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = none)
    (hlc : l.core.state ≠ .congest) (hlk : l.core.state ≠ .lock) (hl2 : l.core.state ≠ .compare2)
    (hr1 : r.core.state ≠ .compare1) (hr2 : r.core.state ≠ .compare2)
    (hl0 : l.core.label ≠ ⟨0, hψ⟩) :
    let q := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hfresh : freshComparisonStart hψ
      (⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩ : AuthorizedAgentState ψ)
      = false := by
    unfold freshComparisonStart normalizePermit
    simp only [compareSigInit, hlpath]
    cases a with
    | zero => simp [hl0]
    | succ a => rfl
  simp only [PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne]
  have hinit : compareSigInit l.core = l.core := by simp [compareSigInit, hlpath]
  simp only [hinit, hlpath, hrpath]
  rw [hinit] at hfresh
  simp only [authorizedCmpUpdate, hfresh, Bool.false_and, if_false, Bool.false_eq_true]
  simp [cmpUpdateReturnPriority, cmpUpdateSetPath2, PPLLCompleteMultiLeaderCleanup.compareSigDispatchActionOne,
    hlc, hlk, hl2, hr1, hr2, hlp2, hrp2, hlpath, hl0]

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

/-- Post-CHECK stages keep the chain fields of two quiet aligned cells (no comparison state, no toss, no path2) off
label 0 with a non-terminal responder. -/
theorem afterCheck_keeps_quiet {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hlt : l.core.state ≠ .toss) (hrt : r.core.state ≠ .toss)
    (hlc : l.core.state ≠ .congest) (hlk : l.core.state ≠ .lock) (hl2 : l.core.state ≠ .compare2)
    (hr1 : r.core.state ≠ .compare1) (hr2 : r.core.state ≠ .compare2)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = none)
    (hl0 : l.core.label ≠ ⟨0, hψ⟩) (hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_keeps_view hψ l.core r.core hlt hrt hrterm
  have hdr := disappear_reset_cmd hψ l.core r.core
  have h0c1 : q0.1.core = (disappear hψ l.core r.core).1 := rfl
  have h0c2 : q0.2.core = (disappear hψ l.core r.core).2 := rfl
  have e1 := hd.1; have e2 := hd.2
  unfold chainView at e1 e2
  simp only [Prod.mk.injEq] at e1 e2
  have hc := compare_keeps_quiet hψ q0.1 q0.2 a b c d
    (by rw [h0c1, e1.2.1]; exact hlpath) (by rw [h0c2, e2.2.1]; exact hrpath)
    (by rw [h0c1, e1.2.2.1]; exact hlp2) (by rw [h0c2, e2.2.2.1]; exact hrp2)
    (by rw [h0c1, e1.1]; exact hlc) (by rw [h0c1, e1.1]; exact hlk) (by rw [h0c1, e1.1]; exact hl2)
    (by rw [h0c2, e2.1]; exact hr1) (by rw [h0c2, e2.1]; exact hr2)
    (by rw [h0c1, e1.2.2.2.1]; exact hl0)
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have hq1a : q1.1.core = q0.1.core := hc.1
  have hq1b : q1.2.core = q0.2.core := hc.2
  have hs := suppress_keeps_view hψ hwidth hle q1.1.core q1.2.core
    (by rw [hq1a, h0c1, e1.2.2.2.2.2]; exact hll) (by rw [hq1a, h0c1, hdr.1]; exact hlr)
    (by rw [hq1b, h0c2, hdr.2]; exact hrr)
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

/-- An internal edge with two check-open matching cells above label 0 and a non-terminal responder: the R1
ordinary branch readies both (state `CHECK_ready`) and keeps their paths, path2, labels and follower status. -/
theorem ordinary_open_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (i : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlm : CheckOpenMatch l.core) (hrm : CheckOpenMatch r.core)
    (hlab : l.core.label.val = i) (hi0 : 1 ≤ i) (hi : i + 1 < ψ - 1)
    (hlpr : l.core.state ≠ .produce) (hldn : l.core.state ≠ .done) (hlt : l.core.state ≠ .toss)
    (hlc : l.core.state ≠ .congest)
    (hrpr : r.core.state ≠ .produce) (hrdn : r.core.state ≠ .done) (hrel : r.core.state ≠ .eliminate_signal)
    (hrt : r.core.state ≠ .toss) (hrc : r.core.state ≠ .congest)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    postView q.1.core = postView { l.core with state := .CHECK_ready } ∧
      postView q.2.core = postView { r.core with state := .CHECK_ready } := by
  intro q
  have hi' : i + 1 < ψ := by omega
  have hrlab : r.core.label.val = i + 1 := by
    rw [hcons]; show (l.core.label.val + 1) % ψ = i + 1; rw [hlab, Nat.mod_eq_of_lt hi']
  have hlp : l.core.path = .some i (if l.core.bit then 1 else 0) := by rw [hlm.path, hlab]
  have hrp : r.core.path = .some (i + 1) (if r.core.bit then 1 else 0) := by rw [hrm.path, hrlab]
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r i _ _ hcons hll hrl hlp hrp hi'
    hlpr hldn hrpr hrdn hrel (fun h => absurd h (by omega)) hr5
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hl0 : B.1.core.label ≠ ⟨0, hψ⟩ := by
    intro h; have := congrArg Fin.val h; rw [lb1, hlab] at this; simp only at this; omega
  have hrne : B.2.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [lb2, hrlab] at this; simp only at this; omega
  have res1 : Resident hψ B.1.core :=
    ⟨by rw [ld1]; exact hll, by rw [rc1]; exact hlr, ⟨i, _, by rw [p1]; exact hlp⟩, by rw [q1]; exact hlm.path2,
      by rw [s1]; exact hldn, by rw [s1]; exact hlm.notDepart, Or.inr (by rw [s1]; exact hlm.notEqual)⟩
  have res2 : Resident hψ B.2.core :=
    ⟨by rw [ld2]; exact hrl, by rw [rc2]; exact hrr, ⟨i + 1, _, by rw [p2]; exact hrp⟩, by rw [q2]; exact hrm.path2,
      by rw [s2]; exact hrdn, by rw [s2]; exact hrm.notDepart, Or.inr (by rw [s2]; exact hrm.notEqual)⟩
  have hcut := doneThroughCheck_cores (κ := κ) hψ (by decide : 0 < 2) h2 l r
    (by rw [hB]; exact res1) (by rw [hB]; exact res2)
    (by rw [hB, s1]; exact hlt) (by rw [hB, s2]; exact hrt)
    (by rw [hB, s1]; exact hlc) (by rw [hB, s2]; exact hrc)
  rw [hB] at hcut
  have hm1 : CheckOpenMatch B.1.core :=
    ⟨by rw [p1, lb1, bt1]; exact hlm.path, by rw [q1]; exact hlm.path2, by rw [s1]; exact hlm.notDepart,
      by rw [s1]; exact hlm.notEqual, by rw [s1]; exact hlm.notLarger, by rw [s1]; exact hlm.notLess⟩
  have hm2 : CheckOpenMatch B.2.core :=
    ⟨by rw [p2, lb2, bt2]; exact hrm.path, by rw [q2]; exact hrm.path2, by rw [s2]; exact hrm.notDepart,
      by rw [s2]; exact hrm.notEqual, by rw [s2]; exact hrm.notLarger, by rw [s2]; exact hrm.notLess⟩
  have hck := checkSig_open_open hψ B.1.core B.2.core hm1 hm2 hl0
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  rw [hck] at hc1 hc2
  have hfix : BirthCheckPermitRepair.permitFix C.1 = C.1 := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1]; simp
  have hac := afterCheck_keeps_quiet hψ (by decide : 0 < 2) h2 C.1 C.2 i _ (i + 1) _
    (by rw [hc1]; show B.1.core.path = _; rw [p1]; exact hlp)
    (by rw [hc2]; show B.2.core.path = _; rw [p2]; exact hrp)
    (by rw [hc1]; intro h; cases h) (by rw [hc2]; intro h; cases h) (by rw [hc1]; intro h; cases h)
    (by rw [hc1]; intro h; cases h) (by rw [hc1]; intro h; cases h) (by rw [hc2]; intro h; cases h)
    (by rw [hc2]; intro h; cases h)
    (by rw [hc1]; show B.1.core.path2 = _; rw [q1]; exact hlm.path2)
    (by rw [hc2]; show B.2.core.path2 = _; rw [q2]; exact hrm.path2)
    (by rw [hc1]; exact hl0) (by rw [hc2]; exact hrne)
    (by rw [hc1]; show B.1.core.leader = _; rw [ld1]; exact hll)
    (by rw [hc1]; show B.1.core.reset_cmd = _; rw [rc1]; exact hlr)
    (by rw [hc2]; show B.2.core.reset_cmd = _; rw [rc2]; exact hrr)
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 C.1 C.2 = Q at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have pv1' := pv1; have pv2' := pv2
  unfold postView at pv1' pv2'
  simp only [Prod.mk.injEq] at pv1' pv2'
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1'.2.2.2.2, pv2'.2.2.2.2, hc1, hc2]
    show (!l.core.leader && B.1.core.leader || !r.core.leader && B.2.core.leader) = false
    rw [ld1, hll, ld2, hrl]
    rfl
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  have e1 : postView C.1.core = postView { l.core with state := .CHECK_ready } := by
    rw [hc1]; unfold postView; show (_, B.1.core.path, B.1.core.path2, B.1.core.label, B.1.core.leader) = _
    rw [p1, q1, lb1, ld1]
  have e2 : postView C.2.core = postView { r.core with state := .CHECK_ready } := by
    rw [hc2]; unfold postView; show (_, B.2.core.path, B.2.core.path2, B.2.core.label, B.2.core.leader) = _
    rw [p2, q2, lb2, ld2]
  exact ⟨pv1.trans e1, pv2.trans e2⟩

/-! ## Internal rows on the actual R1 row output, with stall accounting -/

open K2BirthDispatcher ExpiringK2Projection K2BirthLeaderNormalize BirthSigMoveDisposalRepair
open BirthCheckPermitRepairRowLift BirthCheckPermitRepairBirth

/-- The deletion-priority path expiry lowers the stall by at most one. -/
theorem expire_stall_ge (old out : ExpiringAgentState ψ κ τ) :
    old.stall.val ≤ (deletionPriorityExpireOne τ old out).stall.val + 1 := by
  have hle := old.stall.isLt
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  by_cases h1 : deletionActive out.core.erase = true
  · rw [if_pos h1]; show old.stall.val ≤ τ + 1; omega
  · rw [if_neg h1]
    by_cases h2 : PPLLPathStallComparisonRepair.PathProgressView.ofState out.core ≠
        PPLLPathStallComparisonRepair.PathProgressView.ofState old.core
    · rw [if_pos h2]; show old.stall.val ≤ τ + 1; omega
    · rw [if_neg h2]
      by_cases h3 : old.stall.val = 0
      · rw [dif_pos h3]; show old.stall.val ≤ τ + 1; omega
      · rw [dif_neg h3]; show old.stall.val ≤ old.stall.val - 1 + 1; omega

theorem nonK2_stall (a b : ExpiringAgentState ψ κ τ) (h : nonK2 a = nonK2 b) : a.stall = b.stall := by
  have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.stall) h; exact hh

theorem normalizeLeader_stall (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) : (normalizeLeader hψ q).stall = q.stall := by
  unfold normalizeLeader; split <;> rfl

/-- The R1 row lowers each endpoint stall by at most one. -/
theorem row_stall_ge (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    l.stall.val ≤ (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1.stall.val + 1 ∧
      r.stall.val ≤ (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2.stall.val + 1 := by
  have hn := finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have e1 := nonK2_stall _ _ hn.1
  have e2 := nonK2_stall _ _ hn.2
  rw [normalizeLeader_stall] at e1 e2
  have hx1 := expire_stall_ge (prepareExpiringDisposal hψ l)
    ⟨(BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 (prepareExpiringDisposal hψ l).core
      (prepareExpiringDisposal hψ r).core).1, (prepareExpiringDisposal hψ l).stall⟩
  have hx2 := expire_stall_ge (prepareExpiringDisposal hψ r)
    ⟨(BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 (prepareExpiringDisposal hψ l).core
      (prepareExpiringDisposal hψ r).core).2, (prepareExpiringDisposal hψ r).stall⟩
  have r1 : (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1 = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 := rfl
  have r2 : (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2 = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).2 := rfl
  have ex1 : (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1 =
      deletionPriorityExpireOne τ (prepareExpiringDisposal hψ l)
        ⟨(BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 (prepareExpiringDisposal hψ l).core
          (prepareExpiringDisposal hψ r).core).1, (prepareExpiringDisposal hψ l).stall⟩ := rfl
  have ex2 : (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2 =
      deletionPriorityExpireOne τ (prepareExpiringDisposal hψ r)
        ⟨(BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 (prepareExpiringDisposal hψ l).core
          (prepareExpiringDisposal hψ r).core).2, (prepareExpiringDisposal hψ r).stall⟩ := rfl
  have pl : (prepareExpiringDisposal hψ l).stall = l.stall := rfl
  have pr : (prepareExpiringDisposal hψ r).stall = r.stall := rfl
  rw [r1, r2, e1, e2, ex1, ex2]
  rw [pl] at hx1; rw [pr] at hx2
  exact ⟨hx1, hx2⟩

theorem row_left_reset (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hlstall : l.stall.val ≠ 0) :
    (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1.core.erase.core.reset_cmd =
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).1.core.reset_cmd := by
  have heL := expiring_left_erase (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hlstall
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1
  have ho : (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1 = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 := rfl
  rw [ho]
  generalize (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 = o at hn ⊢
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at heL hn
  have hx := nonK2_fields o (normalizeLeader hψ E.1) hn
  have hr : (normalizeLeader hψ E.1).core.erase.core.reset_cmd = E.1.core.erase.core.reset_cmd := by
    unfold normalizeLeader; split <;> rfl
  exact hx.2.2.2.2.2.1.trans (hr.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.reset_cmd) heL))

/-- An internal equal-equal letter on the actual R1 row: both endpoints stay `equal` on their paths, without
path2 or reset command, with their labels, as followers; each stall drops by at most one. -/
theorem r1_equal_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (i bl br : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlp : l.core.erase.core.path = .some i bl) (hrp : r.core.erase.core.path = .some (i + 1) br)
    (hlab : l.core.erase.core.label.val = i) (hi : i + 1 < ψ - 1)
    (hleq : l.core.erase.core.state = .equal) (hreq : r.core.erase.core.state = .equal)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0) :
    let o := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    (o.1.core.erase.core.state = .equal ∧ o.1.core.erase.core.path = l.core.erase.core.path ∧
      o.1.core.erase.core.path2 = none ∧ o.1.core.erase.core.label = l.core.erase.core.label ∧
      o.1.core.erase.core.reset_cmd = false ∧ o.1.core.erase.core.leader = false ∧
      l.stall.val ≤ o.1.stall.val + 1) ∧
    (o.2.core.erase.core.state = .equal ∧ o.2.core.erase.core.path = r.core.erase.core.path ∧
      o.2.core.erase.core.path2 = none ∧ o.2.core.erase.core.label = r.core.erase.core.label ∧
      o.2.core.erase.core.reset_cmd = false ∧ o.2.core.erase.core.leader = false ∧
      r.stall.val ≤ o.2.stall.val + 1) := by
  intro o
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hleq]; decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by rw [hreq]; decide
  have hq := ordinary_equal_row hψ h2 κ l.core.erase r.core.erase i bl br hcons hll hrl hlp hrp hlab hi hleq hreq
    hlp2 hrp2 hlr hrr hl4 hr5
  have q1 := hq.1; have q2 := hq.2
  unfold postView at q1 q2
  simp only [Prod.mk.injEq] at q1 q2
  have hres := ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hll hlr hrr
  have fL := row_left_frame (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hlstall hrstall (q1.2.2.2.2.trans hll)
    (q2.2.2.2.2.trans hrl)
  have fR := row_right_frame (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hrstall (q2.2.2.2.2.trans hrl)
  have rL := row_left_reset (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hlstall
  have hs := row_stall_ge hψ h2 l r
  exact ⟨⟨fL.1.trans (q1.1.trans hleq), fL.2.1.trans q1.2.1, fL.2.2.1.trans (q1.2.2.1.trans hlp2),
      fL.2.2.2.1.trans q1.2.2.2.1, rL.trans hres.1, fL.2.2.2.2, hs.1⟩,
    ⟨fR.1.trans (q2.1.trans hreq), fR.2.1.trans q2.2.1, fR.2.2.1.trans (q2.2.2.1.trans hrp2),
      fR.2.2.2.1.trans q2.2.2.2.1, fR.2.2.2.2.1.trans hres.2, fR.2.2.2.2.2, hs.2⟩⟩

/-- An internal letter on two check-open matching cells above label 0 (non-terminal responder) on the actual R1 row:
both endpoints become `CHECK_ready` and keep path, empty path2, label, no reset command, follower; each stall drops
by at most one. -/
theorem r1_open_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (i : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlm : CheckOpenMatch l.core.erase.core) (hrm : CheckOpenMatch r.core.erase.core)
    (hlab : l.core.erase.core.label.val = i) (hi0 : 1 ≤ i) (hi : i + 1 < ψ - 1)
    (hlpr : l.core.erase.core.state ≠ .produce) (hldn : l.core.erase.core.state ≠ .done)
    (hlt : l.core.erase.core.state ≠ .toss) (hlc : l.core.erase.core.state ≠ .congest)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal)
    (hrpr : r.core.erase.core.state ≠ .produce) (hrdn : r.core.erase.core.state ≠ .done)
    (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hrt : r.core.erase.core.state ≠ .toss) (hrc : r.core.erase.core.state ≠ .congest)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0) :
    let o := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    (o.1.core.erase.core.state = .CHECK_ready ∧ o.1.core.erase.core.path = l.core.erase.core.path ∧
      o.1.core.erase.core.path2 = none ∧ o.1.core.erase.core.label = l.core.erase.core.label ∧
      o.1.core.erase.core.reset_cmd = false ∧ o.1.core.erase.core.leader = false ∧
      l.stall.val ≤ o.1.stall.val + 1) ∧
    (o.2.core.erase.core.state = .CHECK_ready ∧ o.2.core.erase.core.path = r.core.erase.core.path ∧
      o.2.core.erase.core.path2 = none ∧ o.2.core.erase.core.label = r.core.erase.core.label ∧
      o.2.core.erase.core.reset_cmd = false ∧ o.2.core.erase.core.leader = false ∧
      r.stall.val ≤ o.2.stall.val + 1) := by
  intro o
  have hq := ordinary_open_row hψ h2 κ l.core.erase r.core.erase i hcons hll hrl hlm hrm hlab hi0 hi hlpr hldn hlt
    hlc hrpr hrdn hrel hrt hrc hlr hrr hr5
  have q1 := hq.1; have q2 := hq.2
  unfold postView at q1 q2
  simp only [Prod.mk.injEq] at q1 q2
  have hres := ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hll hlr hrr
  have fL := row_left_frame (κ := κ) hψ h2 l r hlm.path2 hrm.path2 hlel hrel hlstall hrstall (q1.2.2.2.2.trans hll)
    (q2.2.2.2.2.trans hrl)
  have fR := row_right_frame (κ := κ) hψ h2 l r hlm.path2 hrm.path2 hlel hrel hrstall (q2.2.2.2.2.trans hrl)
  have rL := row_left_reset (κ := κ) hψ h2 l r hlm.path2 hrm.path2 hlel hrel hlstall
  have hs := row_stall_ge hψ h2 l r
  exact ⟨⟨fL.1.trans q1.1, fL.2.1.trans q1.2.1, fL.2.2.1.trans (q1.2.2.1.trans hlm.path2),
      fL.2.2.2.1.trans q1.2.2.2.1, rL.trans hres.1, fL.2.2.2.2, hs.1⟩,
    ⟨fR.1.trans q2.1, fR.2.1.trans q2.2.1, fR.2.2.1.trans (q2.2.2.1.trans hrm.path2),
      fR.2.2.2.1.trans q2.2.2.2.1, fR.2.2.2.2.1.trans hres.2, fR.2.2.2.2.2, hs.2⟩⟩

end BirthCheckChainR1Internal
