import Leader.Wu.Birth.CheckChainStages
import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducer

set_option autoImplicit false

/-! # One intermediate row of the R1 CHECK chain, on the ordinary branch

`ordinary_chain_row`: on an internal edge (label i, label i+1) with i + 1 < psi - 1 of an aligned consistent
train, when the initiator is already `equal` and the responder is a check-open matching carrier (clean registers
as listed), the R1 ordinary branch leaves the responder `equal` with its path, label and follower status, and no
path2 signal. -/

namespace BirthCheckChainR1

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut

variable {ψ : Nat}

theorem setReady_fields (u : AgentState ψ) :
    (checkSigSetReady u).reset_cmd = u.reset_cmd ∧ (checkSigSetReady u).leader = u.leader ∧
      (checkSigSetReady u).label = u.label := by
  unfold checkSigSetReady; split
  · split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem setReady_path (u : AgentState ψ) : (checkSigSetReady u).path = u.path := by
  unfold checkSigSetReady; split
  · split <;> rfl
  · rfl

theorem checkL_fields (hψ : 0 < ψ) (u : AgentState ψ) :
    (checkSigCheckL hψ u).reset_cmd = u.reset_cmd ∧ (checkSigCheckL hψ u).leader = u.leader ∧
      (checkSigCheckL hψ u).label = u.label ∧ (checkSigCheckL hψ u).path = u.path := by
  unfold checkSigCheckL; split
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem setResult_path (u : AgentState ψ) : (checkSigSetResult u).path = u.path := by
  unfold checkSigSetResult
  by_cases h1 : u.state = .larger <;> by_cases h2 : u.state = .less <;> simp [h1, h2]

theorem checkR_fields (hψ : 0 < ψ) (l u : AgentState ψ) :
    (checkSigCheckR hψ l u).reset_cmd = u.reset_cmd ∧ (checkSigCheckR hψ l u).leader = u.leader ∧
      (checkSigCheckR hψ l u).label = u.label := by
  unfold checkSigCheckR; split
  · split
    · split <;> exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem setResult_fields (u : AgentState ψ) :
    (checkSigSetResult u).reset_cmd = u.reset_cmd ∧ (checkSigSetResult u).leader = u.leader ∧
      (checkSigSetResult u).label = u.label := by
  unfold checkSigSetResult
  by_cases h1 : u.state = .larger <;> by_cases h2 : u.state = .less <;> simp [h1, h2]

theorem checkSig_r_fields (hψ : 0 < ψ) (l r : AgentState ψ) (hlab : r.label ≠ ⟨ψ - 1, by omega⟩) :
    (checkSig hψ l r).2.reset_cmd = r.reset_cmd ∧ (checkSig hψ l r).2.leader = r.leader := by
  let x := checkSigSetResult (checkSigCheckR hψ (checkSigCheckL hψ (checkSigSetReady l)) (checkSigSetReady r))
  obtain ⟨a1, a2, a3⟩ := setResult_fields (checkSigCheckR hψ (checkSigCheckL hψ (checkSigSetReady l)) (checkSigSetReady r))
  obtain ⟨b1, b2, b3⟩ := checkR_fields hψ (checkSigCheckL hψ (checkSigSetReady l)) (checkSigSetReady r)
  obtain ⟨c1, c2, c3⟩ := setReady_fields r
  have hxl : x.label = r.label := a3.trans (b3.trans c3)
  have e : (checkSig hψ l r).2 = x := by
    unfold checkSig; dsimp only
    rw [if_neg (by intro h; exact hlab (hxl ▸ h.1))]
  rw [e]
  exact ⟨a1.trans (b1.trans c1), a2.trans (b2.trans c2)⟩

theorem checkSig_r_label (hψ : 0 < ψ) (l r : AgentState ψ) : (checkSig hψ l r).2.label = r.label := by
  obtain ⟨_, _, a3⟩ := setResult_fields (checkSigCheckR hψ (checkSigCheckL hψ (checkSigSetReady l)) (checkSigSetReady r))
  obtain ⟨_, _, b3⟩ := checkR_fields hψ (checkSigCheckL hψ (checkSigSetReady l)) (checkSigSetReady r)
  obtain ⟨_, _, c3⟩ := setReady_fields r
  unfold checkSig; dsimp only
  split
  · show (checkSigSetResult _).label = r.label
    exact a3.trans (b3.trans c3)
  · exact a3.trans (b3.trans c3)

theorem ordinary_chain_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (i bl : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hlab : l.core.label.val = i) (hi : i + 1 < ψ - 1)
    (hrm : CheckOpenMatch r.core) (hrlab : r.core.label.val = i + 1)
    (hleq : l.core.state = .equal) (hlp2 : l.core.path2 = none)
    (hrpr : r.core.state ≠ .produce) (hrdn : r.core.state ≠ .done) (hrel : r.core.state ≠ .eliminate_signal)
    (hrt : r.core.state ≠ .toss) (hrc : r.core.state ≠ .congest)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    q.2.core.state = .equal ∧ q.2.core.path = r.core.path ∧ q.2.core.path2 = none ∧
      q.2.core.label = r.core.label ∧ q.2.core.leader = false := by
  intro q
  have hi' : i + 1 < ψ := by omega
  have hrp : r.core.path = .some (i + 1) (if r.core.bit then 1 else 0) := by rw [hrm.path, hrlab]
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
    ⟨by rw [ld2]; exact hrl, by rw [rc2]; exact hrr, ⟨i + 1, _, by rw [p2]; exact hrp⟩, by rw [q2]; exact hrm.path2,
      by rw [s2]; exact hrdn, by rw [s2]; exact hrm.notDepart, Or.inr (by rw [s2]; exact hrm.notEqual)⟩
  have hcut := doneThroughCheck_cores (κ := κ) hψ (by decide : 0 < 2) h2 l r
    (by rw [hB]; exact res1) (by rw [hB]; exact res2)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2]; exact hrt)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2]; exact hrc)
  rw [hB] at hcut
  have hm2 : CheckOpenMatch B.2.core :=
    ⟨by rw [p2, lb2, bt2]; exact hrm.path, by rw [q2]; exact hrm.path2, by rw [s2]; exact hrm.notDepart,
      by rw [s2]; exact hrm.notEqual, by rw [s2]; exact hrm.notLarger, by rw [s2]; exact hrm.notLess⟩
  have hck := checkSig_chain_row hψ B.1.core B.2.core (by rw [s1]; exact hleq) (by rw [lb1, hlab]; omega) hm2
  obtain ⟨ck1, ck2, ck3, ck4, ck5, _⟩ := hck
  -- CHECK output
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  rw [ck1] at hc1
  -- permit fix
  have hfix : BirthCheckPermitRepair.permitFix C.1 = ⟨C.1.core, false⟩ := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1, s1, hleq]; simp
  -- post-CHECK
  have hac := afterCheck_keeps_chain hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 i bl (i + 1)
    (if r.core.bit then 1 else 0)
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

/-- The initiator side of raw CHECK keeps reset command, leader, label and path. -/
theorem checkSig_l_fields (hψ : 0 < ψ) (l r : AgentState ψ) :
    (checkSig hψ l r).1.reset_cmd = l.reset_cmd ∧ (checkSig hψ l r).1.leader = l.leader ∧
      (checkSig hψ l r).1.label = l.label ∧ (checkSig hψ l r).1.path = l.path := by
  have e : (checkSig hψ l r).1 = checkSigSetResult (checkSigCheckL hψ (checkSigSetReady l)) := rfl
  rw [e]
  obtain ⟨a1, a2, a3⟩ := setResult_fields (checkSigCheckL hψ (checkSigSetReady l))
  obtain ⟨b1, b2, b3, b4⟩ := checkL_fields hψ (checkSigSetReady l)
  obtain ⟨c1, c2, c3⟩ := setReady_fields l
  exact ⟨a1.trans (b1.trans c1), a2.trans (b2.trans c2), a3.trans (b3.trans c3),
    (setResult_path _).trans (b4.trans (setReady_path l))⟩

/-- The responder side of raw CHECK keeps its path. -/
theorem checkSig_r_path (hψ : 0 < ψ) (l r : AgentState ψ) : (checkSig hψ l r).2.path = r.path := by
  have hsr : ∀ u : AgentState ψ, (checkSigCheckR hψ (checkSigCheckL hψ (checkSigSetReady l)) u).path = u.path := by
    intro u; unfold checkSigCheckR; split
    · split
      · split <;> rfl
      · rfl
    · rfl
  unfold checkSig; dsimp only
  split
  · show (checkSigSetResult _).path = r.path
    rw [setResult_path, hsr, setReady_path]
  · rw [setResult_path, hsr, setReady_path]

/-- The first row of the R1 CHECK chain on the ordinary branch: on (label 0, label 1) with psi >= 3 and two
check-open matching carriers (the label-0 carrier may hold its crossing permit), both endpoints leave the row
`equal` with their paths, labels and follower status and no path2. -/
theorem ordinary_first_row (hψ : 0 < ψ) (h3 : 2 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlm : CheckOpenMatch l.core) (hlab : l.core.label.val = 0)
    (hrm : CheckOpenMatch r.core) (hrlab : r.core.label.val = 1)
    (hlpr : l.core.state ≠ .produce) (hldn : l.core.state ≠ .done) (hlt : l.core.state ≠ .toss)
    (hlc : l.core.state ≠ .congest)
    (hrpr : r.core.state ≠ .produce) (hrdn : r.core.state ≠ .done) (hrel : r.core.state ≠ .eliminate_signal)
    (hrt : r.core.state ≠ .toss) (hrc : r.core.state ≠ .congest)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hl4 : ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) (by omega) κ l r
    q.1.core.state = .equal ∧ q.1.core.path = l.core.path ∧ q.1.core.label = l.core.label ∧
      q.1.core.leader = false ∧
      q.2.core.state = .equal ∧ q.2.core.path = r.core.path ∧ q.2.core.path2 = none ∧
      q.2.core.label = r.core.label ∧ q.2.core.leader = false := by
  intro q
  have h2 : 2 ≤ ψ := by omega
  have hlp : l.core.path = .some 0 (if l.core.bit then 1 else 0) := by rw [hlm.path, hlab]
  have hrp : r.core.path = .some (0 + 1) (if r.core.bit then 1 else 0) := by rw [hrm.path, hrlab]
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r 0 _ _ hcons hll hrl hlp hrp
    (by omega) hlpr hldn hrpr hrdn hrel (fun _ => hl4) hr5
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hlne : l.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [hlab] at this; simp only at this; omega
  have hrne : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [hrlab] at this; simp only at this; omega
  have res1 : Resident hψ B.1.core :=
    ⟨by rw [ld1]; exact hll, by rw [rc1]; exact hlr, ⟨0, _, by rw [p1]; exact hlp⟩, by rw [q1]; exact hlm.path2,
      by rw [s1]; exact hldn, by rw [s1]; exact hlm.notDepart, Or.inr (by rw [s1]; exact hlm.notEqual)⟩
  have res2 : Resident hψ B.2.core :=
    ⟨by rw [ld2]; exact hrl, by rw [rc2]; exact hrr, ⟨0 + 1, _, by rw [p2]; exact hrp⟩, by rw [q2]; exact hrm.path2,
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
  have hb0 : B.1.core.label = ⟨0, hψ⟩ := by apply Fin.ext; rw [lb1, hlab]
  have hck := checkSig_first_row hψ B.1.core B.2.core hb0 (by rw [lb1, hlab]; omega) hm1 hm2
  obtain ⟨ck1, ck2, ck3, ck4⟩ := hck
  obtain ⟨lf1, lf2, lf3, lf4⟩ := checkSig_l_fields hψ B.1.core B.2.core
  obtain ⟨rf1, rf2⟩ := checkSig_r_fields hψ B.1.core B.2.core (by rw [lb2]; exact hrne)
  have rf3 := checkSig_r_path hψ B.1.core B.2.core
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  have hfix : BirthCheckPermitRepair.permitFix C.1 = ⟨C.1.core, false⟩ := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1]; simp [ck1]
  have hac := afterCheck_keeps_chain hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 0
    (if l.core.bit then 1 else 0) (0 + 1) (if r.core.bit then 1 else 0)
    (by show C.1.core.path = _; rw [hc1, lf4, p1]; exact hlp)
    (by rw [hc2, rf3, p2]; exact hrp)
    (by show C.1.core.state = _; rw [hc1]; exact ck1)
    (by rw [hc2]; exact ck2)
    (by show C.1.core.path2 = _; rw [hc1]; exact ck3)
    (by rw [hc2]; exact ck4)
    (Or.inr rfl)
    (by rw [hc2, checkSig_r_label, lb2]; exact hrne)
    (by show C.1.core.leader = _; rw [hc1, lf2, ld1]; exact hll)
    (by show C.1.core.reset_cmd = _; rw [hc1, lf1, rc1]; exact hlr)
    (by rw [hc2, rf1, rc2]; exact hrr)
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 = Q at pv1 pv2
  unfold postView at pv1 pv2
  simp only [Prod.mk.injEq] at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) (by omega) κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1.2.2.2.2, pv2.2.2.2.2]
    show (!l.core.leader && C.1.core.leader || !r.core.leader && C.2.core.leader) = false
    rw [hc1, lf2, ld1, hll, hc2, rf2, ld2, hrl]
    rfl
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Q.1.core.state = _; rw [pv1.1]; show C.1.core.state = _; rw [hc1]; exact ck1
  · show Q.1.core.path = _; rw [pv1.2.1]; show C.1.core.path = _; rw [hc1, lf4, p1]
  · show Q.1.core.label = _; rw [pv1.2.2.2.1]; show C.1.core.label = _; rw [hc1, lf3, lb1]
  · show Q.1.core.leader = _; rw [pv1.2.2.2.2]; show C.1.core.leader = _; rw [hc1, lf2, ld1]; exact hll
  · rw [pv2.1, hc2]; exact ck2
  · rw [pv2.2.1, hc2, rf3, p2]
  · rw [pv2.2.2.1, hc2]; exact ck4
  · rw [pv2.2.2.2.1, hc2, checkSig_r_label, lb2]
  · rw [pv2.2.2.2.2, hc2, rf2, ld2]; exact hrl

/-- The terminal row: when the actual CHECK cut carries a follower birth input, the R1 ordinary branch keeps the
responder leader (the permit fix changes no core field, and the post-CHECK stages and the birth marker frame the
signal pair). -/
theorem ordinary_right_leader_of_input {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (h : BirthShortDoneTerminalCheckInputSources.ActualCheckBirthInput hψ
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r)) :
    (BirthCheckPermitRepair.ordinary hψ hwidth hle κ l r).2.core.leader = true := by
  have hc : (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.leader = true := by
    unfold doneThroughCheckEntryWidth
    generalize doneBeforeCheckEntryWidth hψ hwidth hle κ l r = b at h ⊢
    have ha := BirthShortDoneTerminalCheckInputSufficiency.actualCheckBirth_of_input hψ b h
    obtain ⟨hdl, hdr, htl, htr, hcl, hcr, _hf, hout⟩ := ha
    have heq : preserveDoneCheck hψ b.1 b.2 = authorizedCheckSig hψ b.1 b.2 := by
      rw [preserveDoneCheck_of_no_done hψ b.1 b.2 hdl hdr,
        BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ b.1 b.2 htl htr,
        BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ b.1 b.2 hcl hcr]
    show (preserveDoneCheck hψ b.1 b.2).2.core.leader = true
    rw [heq]; exact hout
  unfold BirthCheckPermitRepair.ordinary
  dsimp only
  generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c at hc ⊢
  have hq := BirthShortDoneCuts.afterCheckMetadataWidth_signal hψ hwidth hle (BirthCheckPermitRepair.permitFix c.1) c.2
  generalize BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle (BirthCheckPermitRepair.permitFix c.1) c.2 = q at hq ⊢
  have hs := (K2BirthDispatcher.markBirth_signal (K2BirthDispatcher.authBirth l r q) q).trans hq
  have hl : (markLeaderBirth (K2BirthDispatcher.authBirth l r q) q).2.core.leader = c.2.core.leader :=
    congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) hs
  exact hl.trans hc

theorem checkL_setReady_of_equal (hψ : 0 < ψ) (u : AgentState ψ) (h : u.state = .equal) :
    (checkSigCheckL hψ (checkSigSetReady u)).state = .equal ∧
      (checkSigCheckL hψ (checkSigSetReady u)).label = u.label := by
  have e : checkSigSetReady u = u := by
    unfold checkSigSetReady; split
    · simp [h]
    · rfl
  rw [e]
  constructor
  · unfold checkSigCheckL; split
    · simp [h]
    · exact h
  · exact (checkL_fields hψ u).2.2.1

/-- The terminal edge of an aligned consistent train with an `equal` initiator and a matching terminal responder
presents the follower birth input at the actual CHECK cut. -/
theorem terminal_birth_input (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (i bl : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hlab : l.core.label.val = i) (hterm : i + 1 = ψ - 1)
    (hrm : CheckOpenMatch r.core) (hrlab : r.core.label.val = i + 1)
    (hleq : l.core.state = .equal) (hlp2 : l.core.path2 = none)
    (hrpr : r.core.state ≠ .produce) (hrdn : r.core.state ≠ .done) (hrel : r.core.state ≠ .eliminate_signal)
    (hrt : r.core.state ≠ .toss) (hrc : r.core.state ≠ .congest)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    BirthShortDoneTerminalCheckInputSources.ActualCheckBirthInput hψ
      (doneBeforeCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r) := by
  have hi' : i + 1 < ψ := by omega
  have hrp : r.core.path = .some (i + 1) (if r.core.bit then 1 else 0) := by rw [hrm.path, hrlab]
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r i bl _ hcons hll hrl hlp hrp hi'
    (by rw [hleq]; decide) (by rw [hleq]; decide) hrpr hrdn hrel hl4 hr5
  have hres := doneBeforeCheck_cores_of_residents (κ := κ) hψ (by decide : 0 < 2) h2 l r
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg hres
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hlne : B.1.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [lb1] at this; simp only at this; omega
  have res1 : Resident hψ B.1.core :=
    ⟨by rw [ld1]; exact hll, by rw [rc1]; exact hlr, ⟨i, bl, by rw [p1]; exact hlp⟩, by rw [q1]; exact hlp2,
      by rw [s1, hleq]; decide, by rw [s1, hleq]; decide, Or.inl hlne⟩
  have res2 : Resident hψ B.2.core :=
    ⟨by rw [ld2]; exact hrl, by rw [rc2]; exact hrr, ⟨i + 1, _, by rw [p2]; exact hrp⟩, by rw [q2]; exact hrm.path2,
      by rw [s2]; exact hrdn, by rw [s2]; exact hrm.notDepart, Or.inr (by rw [s2]; exact hrm.notEqual)⟩
  obtain ⟨d1, d2⟩ := hres res1 res2
  generalize hD : doneBeforeCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = D at d1 d2
  have hcl := checkL_setReady_of_equal hψ D.1.core (by rw [d1, s1]; exact hleq)
  unfold BirthShortDoneTerminalCheckInputSources.ActualCheckBirthInput
    BirthShortDoneTerminalCheckInputSources.CheckFollowerBirthInput
  rw [d1, d2]
  refine ⟨by rw [s1, hleq]; decide, by rw [s2]; exact hrdn, by rw [s1, hleq]; decide, by rw [s2]; exact hrt,
    by rw [s1, hleq]; decide, by rw [s2]; exact hrc, by rw [ld2]; exact hrl,
    Fin.ext (by rw [lb2, hrlab]; exact hterm), Or.inr ⟨i + 1, if r.core.bit then 1 else 0, by rw [p2]; exact hrp,
      Or.inr ⟨by rw [lb2, hrlab], by rw [s2]; exact hrm.notDepart, by rw [s2]; exact hrm.notEqual,
        by rw [s2]; exact hrm.notLarger, by rw [s2]; exact hrm.notLess⟩, ?_, ?_, ?_⟩⟩
  · rw [d1] at hcl; rw [hcl.2, lb1, hlab]; omega
  · rw [d1] at hcl; exact hcl.1
  · rw [bt2]; cases r.core.bit <;> rfl

end BirthCheckChainR1
