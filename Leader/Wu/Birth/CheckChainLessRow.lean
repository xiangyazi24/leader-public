import Leader.Wu.Birth.CheckChainLess
import Leader.Wu.Birth.CheckChainRow
import Leader.Wu.Birth.CheckPermitRepairRowLift

set_option autoImplicit false

/-! # The `less` CHECK row of a train at a smaller group, through the whole R1 row

`ordinary_less_row`: on an internal edge (label i, label i + 1) with i + 1 < psi - 1, an `equal` initiator on its
path and a responder whose carried path bit exceeds its own bit (clean registers as listed) leave, after the R1
ordinary branch, a responder in `less` holding the action-6 signal, with path, label and follower status unchanged.
`r1_less_row`: the same on the actual R1 row (expiry, leader normalization, final physical tail), with reset command
false.  The after-CHECK stages keep a `less` responder with its action-6 signal (`afterCheck_keeps_less`); the
action-one COMPARE ignores action 6 (`compare_keeps_less`).
-/

namespace BirthCheckChainR1

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut

variable {ψ : Nat}

/-- COMPARE (action-one dispatch) keeps an `equal` initiator and a `less` responder holding action 6. -/
theorem compare_keeps_less (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .equal) (hr : r.core.state = .less)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = some ⟨0, 0, 0, 6⟩)
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
    PPLLCompleteMultiLeaderCleanup.compareBitActionOne, PPLLRepair.compareBitUpdateRActionOne, compareBitUpdateL,
    hl, hr, hlp2, hrp2, hlpath]

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

theorem afterCheck_keeps_less {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .equal) (hr : r.core.state = .less)
    (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = some ⟨0, 0, 0, 6⟩)
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
  have hc := compare_keeps_less hψ q0.1 q0.2 a b c d
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


theorem ordinary_less_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (i bl pb : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hlab : l.core.label.val = i) (hi : i + 1 < ψ - 1)
    (hrp : r.core.path = .some (i + 1) pb) (hbit : (if r.core.bit then 1 else 0) < pb) (hrp2 : r.core.path2 = none)
    (hrd : r.core.state ≠ .depart) (hre : r.core.state ≠ .equal) (hrg : r.core.state ≠ .larger)
    (hrs : r.core.state ≠ .less) (hrlab : r.core.label.val = i + 1)
    (hleq : l.core.state = .equal) (hlp2 : l.core.path2 = none)
    (hrpr : r.core.state ≠ .produce) (hrdn : r.core.state ≠ .done) (hrel : r.core.state ≠ .eliminate_signal)
    (hrt : r.core.state ≠ .toss) (hrc : r.core.state ≠ .congest)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    q.2.core.state = .less ∧ q.2.core.path = r.core.path ∧ q.2.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      q.2.core.label = r.core.label ∧ q.2.core.leader = false := by
  intro q
  have hi' : i + 1 < ψ := by omega
  -- generation prefix
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r i bl _ hcons hll hrl hlp hrp hi'
    (by rw [hleq]; decide) (by rw [hleq]; decide) hrpr hrdn hrel hl4 hr5
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  -- residents and the CHECK cut
  have hlabne : B.1.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [lb1] at this; simp only at this; omega
  have hrne : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [hrlab] at this; simp only at this; omega
  have res1 : Resident hψ B.1.core :=
    ⟨by rw [ld1]; exact hll, by rw [rc1]; exact hlr, ⟨i, bl, by rw [p1]; exact hlp⟩, by rw [q1]; exact hlp2,
      by rw [s1, hleq]; decide, by rw [s1, hleq]; decide, Or.inl hlabne⟩
  have res2 : Resident hψ B.2.core :=
    ⟨by rw [ld2]; exact hrl, by rw [rc2]; exact hrr, ⟨i + 1, _, by rw [p2]; exact hrp⟩, by rw [q2]; exact hrp2,
      by rw [s2]; exact hrdn, by rw [s2]; exact hrd, Or.inr (by rw [s2]; exact hre)⟩
  have hcut := doneThroughCheck_cores (κ := κ) hψ (by decide : 0 < 2) h2 l r
    (by rw [hB]; exact res1) (by rw [hB]; exact res2)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2]; exact hrt)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2]; exact hrc)
  rw [hB] at hcut
  have hck := BirthCheckChainR1Less.checkSig_less_row hψ B.1.core B.2.core (i + 1) pb (by rw [s1]; exact hleq)
    (by rw [lb1, hlab]; omega) (by rw [p2]; exact hrp) (by rw [lb2]; exact hrlab) (by rw [s2]; exact hrd)
    (by rw [s2]; exact hre) (by rw [s2]; exact hrg) (by rw [s2]; exact hrs) (by rw [bt2]; exact hbit)
  obtain ⟨ck1, ck2, ck3, ck4, ck5⟩ := hck
  -- CHECK output
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  rw [ck1] at hc1
  -- permit fix
  have hfix : BirthCheckPermitRepair.permitFix C.1 = ⟨C.1.core, false⟩ := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1, s1, hleq]; simp
  -- post-CHECK
  have hac := afterCheck_keeps_less hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 i bl (i + 1)
    pb
    (by show C.1.core.path = _; rw [hc1, p1]; exact hlp)
    (by rw [hc2, ck4, p2]; exact hrp)
    (by show C.1.core.state = _; rw [hc1, s1]; exact hleq)
    (by rw [hc2]; exact ck2)
    (by show C.1.core.path2 = _; rw [hc1, q1]; exact hlp2)
    (by rw [hc2]; exact ck3)
    (Or.inr rfl)
    (by rw [hc2, ck5]; intro h; have := congrArg Fin.val h; rw [lb2, hrlab] at this; simp only at this; omega)
    (by show C.1.core.leader = _; rw [hc1, ld1]; exact hll)
    (by show C.1.core.reset_cmd = _; rw [hc1, rc1]; exact hlr)
    (by rw [hc2, (checkSig_r_fields hψ _ _ (by rw [lb2]; exact hrne)).1, rc2]; exact hrr)
  obtain ⟨pv1, pv2⟩ := hac
  -- birth marker
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 = Q at pv1 pv2
  unfold postView at pv1 pv2
  simp only [Prod.mk.injEq] at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1.2.2.2.2, pv2.2.2.2.2]
    show (!l.core.leader && C.1.core.leader || !r.core.leader && C.2.core.leader) = false
    rw [hc1, ld1, hll, hc2, (checkSig_r_fields hψ _ _ (by rw [lb2]; exact hrne)).2, ld2, hrl]
    rfl
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pv2.1, hc2]; exact ck2
  · rw [pv2.2.1, hc2, ck4, p2]
  · rw [pv2.2.2.1, hc2]; exact ck3
  · rw [pv2.2.2.2.1, hc2, ck5, lb2]
  · rw [pv2.2.2.2.2, hc2, (checkSig_r_fields hψ _ _ (by rw [lb2]; exact hrne)).2, ld2]; exact hrl


end BirthCheckChainR1

namespace BirthCheckPermitRepairRowLift

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair

variable {ψ κ τ : Nat}

/-- The `less` CHECK row on the actual R1 row. -/
theorem r1_less_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (i bl pb : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlp : l.core.erase.core.path = .some i bl) (hlab : l.core.erase.core.label.val = i) (hi : i + 1 < ψ - 1)
    (hrp : r.core.erase.core.path = .some (i + 1) pb) (hbit : (if r.core.erase.core.bit then 1 else 0) < pb)
    (hrp2 : r.core.erase.core.path2 = none)
    (hrd : r.core.erase.core.state ≠ .depart) (hre : r.core.erase.core.state ≠ .equal)
    (hrg : r.core.erase.core.state ≠ .larger) (hrs : r.core.erase.core.state ≠ .less)
    (hrlab : r.core.erase.core.label.val = i + 1)
    (hleq : l.core.erase.core.state = .equal) (hlp2 : l.core.erase.core.path2 = none)
    (hrpr : r.core.erase.core.state ≠ .produce) (hrdn : r.core.erase.core.state ≠ .done)
    (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hrt : r.core.erase.core.state ≠ .toss) (hrc : r.core.erase.core.state ≠ .congest)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hstall : r.stall.val ≠ 0) :
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2
    o.core.erase.core.state = .less ∧ o.core.erase.core.path = r.core.erase.core.path ∧
      o.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧ o.core.erase.core.label = r.core.erase.core.label ∧
      o.core.erase.core.reset_cmd = false ∧ o.core.erase.core.leader = false := by
  intro o
  have hc := BirthCheckChainR1.ordinary_less_row hψ h2 κ l.core.erase r.core.erase i bl pb hcons hll hrl hlp hlab hi
    hrp hbit hrp2 hrd hre hrg hrs hrlab hleq hlp2 hrpr hrdn hrel hrt hrc hlr hrr hl4 hr5
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hleq]; decide
  have hf := row_right_frame (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hstall hc.2.2.2.2
  have hres := (ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hll hlr hrr).2
  exact ⟨hf.1.trans hc.1, hf.2.1.trans hc.2.1, hf.2.2.1.trans hc.2.2.1, hf.2.2.2.1.trans hc.2.2.2.1,
    hf.2.2.2.2.1.trans hres, hf.2.2.2.2.2⟩

end BirthCheckPermitRepairRowLift
