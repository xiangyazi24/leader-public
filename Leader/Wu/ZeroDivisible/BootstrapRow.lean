import Leader.Wu.ZeroDivisible.ServiceEntry
import Leader.Wu.ZeroDivisible.ComparisonBootstrap
import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
The cyclic terminal-to-head bootstrap interface for the actual R5 row.
`EntryFrame` supplies the prefix/hole split, `compareLifecycle_bootstrap`
supplies exact local emission, and the source-exact suffix frames the normal
output. No full-path conclusion is inferred from path counts alone.
-/

namespace PPLLAstraR5BootstrapRow

open PPLL PPLLRepair PPLLAstraR5Repair PPLLAstraDesign2 PPLLPostElectionGuard
open PPLLBirthPatch PPLLFableDesignR1

set_option autoImplicit false
attribute [local irreducible] PPLLAstraR5Repair.ServiceEntry.moveEntry

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by
  split <;> rfl

def Hole {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.path = .bot ∨ q.2.path = .bot

def BootstrapIn {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) : Prop :=
  l.leader = false ∧ r.leader = false ∧
  l.label = ⟨ψ - 1, by omega⟩ ∧ r.label = ⟨0, hp⟩ ∧
  (∃ bl : Nat, l.path = .some (ψ - 1) bl) ∧
  (∃ br : Nat, r.path = .some 0 br) ∧
  l.state = .compare2 ∧ r.state = .compare1 ∧
  l.path2 = none ∧ r.path2 = none

def BootstrapOut {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.leader = false ∧ q.2.leader = false ∧
  q.1.label = l.label ∧ q.2.label = r.label ∧
  q.1.path = l.path ∧ q.2.path = r.path ∧
  q.1.state = .compare2 ∧ q.2.state = .compare1 ∧
  q.1.path2 = some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) ∧
  q.2.path2 = none

private def BootView {ψ : Nat} (u : AgentState ψ) :=
  (u.leader, u.label, u.state, u.path, u.path2)

private def CmpView {ψ : Nat} (u : AgentState ψ) :=
  (u.label, u.state, u.path, u.path2)

/-- Public ServiceEntry suffix frame, restated as one pair-level split. -/
private theorem finish_core_or_hole {ψ : Nat} (hp : ψ > 0)
    (originalL originalR : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) :
    let z := ServiceEntry.finishCompare hp originalL originalR q
    Hole z ∨
      (CmpView z.1 = CmpView q.1 ∧
       CmpView z.2 = CmpView q.2) := by
  have hf := ServiceEntry.finishCompare_frame_or_hole hp originalL originalR q
  rcases hf.1 with hL | hL
  · exact Or.inl (Or.inl hL)
  rcases hf.2 with hR | hR
  · exact Or.inl (Or.inr hR)
  exact Or.inr ⟨hL, hR⟩

private theorem cmpView_update_path2 {ψ : Nat} (a b : AgentState ψ)
    (t : Option Path2Info) (h : CmpView a = CmpView b) :
    CmpView { a with path2 := t } = CmpView { b with path2 := t } := by
  rcases Prod.mk.inj h with ⟨hlabel, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hstate, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hpath, _⟩
  simp only [CmpView, hlabel, hstate, hpath]

private theorem compare_bootstrap_pair {ψ : Nat} (hp : ψ > 0)
    (h4 : 4 ≤ ψ) (κ : Nat) (l r : AgentState ψ)
    (hin : BootstrapIn hp l r) :
    PPLLAstraDesign3.compareLifecycle κ l r =
      ({ l with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) }, r) := by
  rcases hin with ⟨_, _, _, _, hlp, hrp, hls, hrs, hlt, hrt⟩
  exact PPLLAstraR5BootstrapCompare.compareLifecycle_bootstrap
    h4 κ l r hlp hrp hls hrs hlt hrt

/-- No suffix stage can create a leader from a leaderless comparison pair.
The two WRITE implications are the original Algorithm 16 leader-origin laws. -/
private theorem suppress_leaderless {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false) (hr : r.leader = false) :
    (suppressSigResetKill hp l r).1.leader = false ∧
    (suppressSigResetKill hp l r).2.leader = false := by
  cases h1 : l.reset_cmd <;> cases h2 : r.reset_cmd <;>
    cases h3 : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish,
      clearCmp, hl, hr, h1, h2, h3, fst_ite, snd_ite, leader_ite]

private theorem kernel_leaderless {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false) (hr : r.leader = false) :
    (k4Kernel hp l r).1.leader = false ∧
    (k4Kernel hp l r).2.leader = false := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, leader_ite, hl, hr, ite_self, and_self]

private theorem write_leaderless {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false) (hr : r.leader = false) :
    (writeWithBundle hp l r).1.leader = false ∧
    (writeWithBundle hp l r).2.leader = false := by
  have hL : (writeSeq hp l r).1.leader = false := by
    cases h : (writeSeq hp l r).1.leader
    · rfl
    · have bad := (PPLLVerify.writeSeq_new_initiator_requires_responder_leader
        hp l r h hl).1
      simp [hr] at bad
  have hR : (writeSeq hp l r).2.leader = false := by
    cases h : (writeSeq hp l r).2.leader
    · rfl
    · have bad := PPLLVerify.writeSeq_responder_leader_was_leader hp l r h
      simp [hr] at bad
  simpa [writeWithBundle, hr] using And.intro hL hR

private theorem finish_leaderless {ψ : Nat} (hp : ψ > 0)
    (originalL originalR l r : AgentState ψ)
    (hol : originalL.leader = false) (hor : originalR.leader = false)
    (hl : l.leader = false) (hr : r.leader = false) :
    (ServiceEntry.finishCompare hp originalL originalR (l,r)).1.leader = false ∧
    (ServiceEntry.finishCompare hp originalL originalR (l,r)).2.leader = false := by
  let s := suppressSigResetKill hp l r
  have hs := suppress_leaderless hp l r hl hr
  let k := k4Kernel hp s.1 s.2
  have hk := kernel_leaderless hp s.1 s.2 hs.1 hs.2
  let w := writeWithBundle hp k.1 k.2
  have hw := write_leaderless hp k.1 k.2 hk.1 hk.2
  simp only [ServiceEntry.finishCompare, conserve, hol, hor,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  exact hw

/-- The accepted comparison-cut equality realizes the exact normal output
projection, before the rest of the R5 row. -/
theorem compare_cut_normal {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (l r : AgentState ψ)
    (hin : BootstrapIn hp l r) :
    BootstrapOut l r (PPLLAstraDesign3.compareLifecycle κ l r) := by
  rcases hin with ⟨hll, hrl, _, _, hlp, hrp, hls, hrs, hlt, hrt⟩
  rw [PPLLAstraR5BootstrapCompare.compareLifecycle_bootstrap
    h4 κ l r hlp hrp hls hrs hlt hrt]
  simp [BootstrapOut, hll, hrl, hls, hrs, hrt]

/-- The actual pipeline either already ends with a hole, or the actual
`moveEntry` cut retains both original paths and its full control frame. -/
theorem entry_or_final_hole {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hin : BootstrapIn hp l r) :
    Hole (pipeline hp κ c l r) ∨
      (let q := ServiceEntry.moveEntry hp κ l r
       ServiceEntry.EntryFrame l r q ∧
       q.1.path = l.path ∧ q.2.path = r.path) := by
  rcases hin with ⟨_, _, hll, hrl, _, _, hls, hrs, _, _⟩
  have hl : l.label.val = ψ - 1 := by
    rw [hll]
  have hr : r.label.val = 0 := by
    rw [hrl]
  have h := ServiceEntry.boundary_entry_or_final_hole hp h4 κ c l r
    hl hr hls (Or.inr hrs)
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- At a full, token-free follower boundary the actual SIGMOVE stage is inert.
This remains true for either R5 CHECK guard and arbitrary ancillary fields. -/
private theorem move_bootstrap {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    PPLLFableZDiv.moveSourceF hp sourceCfg l r = (l, r) := by
  rcases hin with ⟨hll, hrl, _, _, hlp, hrp, hls, _, hlt, hrt⟩
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  simp [PPLLFableZDiv.moveSourceF, PPLLFableZDiv.sigMoveStep1F,
    PPLLFableDesignR1.moveTokens, PPLLPostElectionGuard.leaderWall,
    PPLLBirthPatch.sigMoveApplyControlConsume,
    hll, hrl, hlp, hrp, hls, hlt, hrt]

/-- The occupied C2/C1 bootstrap pair has no stale holder after SIGMOVE. -/
private theorem drop_bootstrap {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    (PPLLBirthPatchM2.dropStale l, PPLLBirthPatchM2.dropStale r) =
      (l, r) := by
  rcases hin with ⟨_, _, _, hrlab, hlp, hrp, hls, hrs, _, _⟩
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  simp [PPLLBirthPatchM2.dropStale, PPLLBirthPatchM2.blockingState,
    PPLLBirthPatchM2.aligned, hlp, hrp, hls, hrs, hrlab]

/-- A reset command deletes a comparison carrier; otherwise the pre-CHECK
reset stage leaves this follower pair unchanged. -/
private theorem precheck_bootstrap {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    Hole (PPLLPostElectionGuard.preCheckReset l r) ∨
      PPLLPostElectionGuard.preCheckReset l r = (l, r) := by
  have hll : l.leader = false := hin.1
  cases hl : l.reset_cmd <;> cases hr : r.reset_cmd <;>
    simp [PPLLPostElectionGuard.preCheckReset,
      PPLLPostElectionGuard.clearCmp, Hole, hll, hl, hr]

/-- Ready normalization does not release either occupied comparison state. -/
private theorem normalize_bootstrap {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    (PPLLAstraDesign3.normalizeReady l,
      PPLLAstraDesign3.normalizeReady r) = (l, r) := by
  rcases hin with ⟨hll, hrl, _, _, hlp, hrp, hls, hrs, _, _⟩
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  simp [PPLLAstraDesign3.normalizeReady,
    PPLLAstraDesign3.normalizeCarrier,
    PPLLAstraDesign3.normalizeOrphan,
    hlp, hrp, hls, hrs, hll, hrl]

/-- Neither Candidate-E CHECK guard writes a result or leader on the
terminal-C2/head-C1 pair with empty comparison-token slots. -/
private theorem check_bootstrap {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hin : BootstrapIn hp l r) :
    PPLLAstraR5Repair.checkSource hp c l r = (l, r) := by
  rcases hin with ⟨_, _, hllab, hrlab, hlp, hrp, hls, hrs, hlt, hrt⟩
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  have hlast : ψ - 1 ≠ 0 := by omega
  have hzero : (⟨0, hp⟩ : Fin ψ) ≠ ⟨ψ - 1, by omega⟩ := by
    intro he
    have hv : 0 = ψ - 1 := by simpa using congrArg Fin.val he
    exact hlast hv.symm
  simp [PPLLAstraR5Repair.checkSource,
    PPLLAstraR5Repair.releaseEqual,
    PPLLAstraR5Repair.setResult,
    PPLLAstraR5Repair.preserveToken,
    PPLLFableDesignR1.waveState,
    checkSigCheckL, checkSigCheckR, checkSigSetResult,
    hlp, hrp, hls, hrs, hlt, hrt, hllab, hrlab, hlast, hzero]

/-- ReadyAck repair has no applicable release or acknowledgement branch on
an occupied C2/C1 bootstrap pair. -/
private theorem repair_bootstrap {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    PPLLAstraDesign3.repair .readyAck l r = (l, r) := by
  rcases hin with ⟨hll, hrl, _, _, hlp, hrp, hls, hrs, _, _⟩
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  simp [PPLLAstraDesign3.repair,
    PPLLAstraDesign3.normalizeCarrier,
    PPLLAstraDesign3.normalizeOrphan,
    PPLLAstraDesign3.releaseReadySuffix,
    PPLLAstraDesign3.ackTail,
    hlp, hrp, hls, hrs, hll, hrl]

/-- Stale lottery carry may change `p` fields here, but the physical head
responder cannot receive terminal E, so the bootstrap interface survives. -/
private theorem disappear_bootstrap {ψ : Nat} (hp : ψ > 0)
    (h4 : 4 ≤ ψ) (l r : AgentState ψ)
    (hin : BootstrapIn hp l r) :
    BootstrapIn hp (PPLL.disappear hp l r).1
      (PPLL.disappear hp l r).2 := by
  rcases hin with ⟨hll, hrl, hllab, hrlab, hlp, hrp, hls, hrs, hlt, hrt⟩
  have hlast : ψ - 1 ≠ 0 := by omega
  have hzero : (⟨0, hp⟩ : Fin ψ) ≠ ⟨ψ - 1, by omega⟩ := by
    intro he
    have hv : 0 = ψ - 1 := by simpa using congrArg Fin.val he
    exact hlast hv.symm
  cases hc : l.p_carry <;> cases hrpbit : r.p <;>
    simp [BootstrapIn, PPLL.disappear, hll, hrl, hllab, hrlab,
      hlp, hrp, hls, hrs, hlt, hrt, hzero, hc, hrpbit]

private theorem disappear_view {ψ : Nat} (hp : ψ > 0)
    (h4 : 4 ≤ ψ) (l r : AgentState ψ)
    (hin : BootstrapIn hp l r) :
    BootView (PPLL.disappear hp l r).1 = BootView l ∧
    BootView (PPLL.disappear hp l r).2 = BootView r := by
  rcases hin with ⟨_, _, _, hrlab, _, _, hls, hrs, _, _⟩
  have hlast : ψ - 1 ≠ 0 := by omega
  have hzero : (⟨0, hp⟩ : Fin ψ) ≠ ⟨ψ - 1, by omega⟩ := by
    intro he
    have hv : 0 = ψ - 1 := by simpa using congrArg Fin.val he
    exact hlast hv.symm
  cases hc : l.p_carry <;> cases hrpbit : r.p <;>
    simp [BootView, PPLL.disappear, hrlab, hls, hrs,
      hzero, hc, hrpbit]

/-- From an occupied bootstrap pair after preCheckReset, the actual remaining
stages either leave a path hole or preserve the exact comparison projection
with the new A2 on the left and retain both follower leader bits. -/
private theorem afterPrecheck_core_or_hole {ψ : Nat} (hp : ψ > 0)
    (h4 : 4 ≤ ψ) (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (originalL originalR l r : AgentState ψ)
    (hol : originalL.leader = false) (hor : originalR.leader = false)
    (hin : BootstrapIn hp l r) :
    let z := ServiceEntry.afterPrecheck hp κ c originalL originalR l r
    Hole z ∨
      ((z.1.leader = false ∧ z.2.leader = false) ∧
       CmpView z.1 = CmpView
          { l with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) } ∧
       CmpView z.2 = CmpView r) := by
  have hn := normalize_bootstrap hp l r hin
  have hc := check_bootstrap hp h4 c l r hin
  let d := PPLL.disappear hp l r
  have hdIn := disappear_bootstrap hp h4 l r hin
  have hdView := disappear_view hp h4 l r hin
  have hr := repair_bootstrap hp d.1 d.2 hdIn
  have hcmp := compare_bootstrap_pair hp h4 κ d.1 d.2 hdIn
  have hnL : PPLLAstraDesign3.normalizeReady l = l :=
    congrArg Prod.fst hn
  have hnR : PPLLAstraDesign3.normalizeReady r = r :=
    congrArg Prod.snd hn
  have hr' : PPLLAstraDesign3.repair .readyAck
      (PPLL.disappear hp l r).1 (PPLL.disappear hp l r).2 =
      PPLL.disappear hp l r := by
    simpa only [d] using hr
  have hcmp' : PPLLAstraDesign3.compareLifecycle κ
      (PPLL.disappear hp l r).1 (PPLL.disappear hp l r).2 =
      ({ (PPLL.disappear hp l r).1 with
        path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) },
       (PPLL.disappear hp l r).2) := by
    simpa only [d] using hcmp
  have heq : ServiceEntry.afterPrecheck hp κ c originalL originalR l r =
      ServiceEntry.finishCompare hp originalL originalR
        ({ d.1 with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) }, d.2) := by
    simp only [ServiceEntry.afterPrecheck, hnL, hnR, hc, hr', hcmp',
      Prod.fst, Prod.snd]
    rfl
  rw [heq]
  rcases finish_core_or_hole hp originalL originalR
      ({ d.1 with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) }, d.2)
    with hh | hf
  · exact Or.inl hh
  · right
    have hfin := finish_leaderless hp originalL originalR
      { d.1 with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) }
      d.2 hol hor hdIn.1 hdIn.2.1
    have hd1 : CmpView d.1 = CmpView l :=
      congrArg Prod.snd hdView.1
    have hd2 : CmpView d.2 = CmpView r :=
      congrArg Prod.snd hdView.2
    exact ⟨hfin, hf.1.trans (cmpView_update_path2 d.1 l _ hd1),
      hf.2.trans hd2⟩

/-- An occupied `EntryFrame` transports the bootstrap premises to the actual
MOVE cut, with no restriction on fields that changed in WAIT or CLEAN. -/
private theorem entryFrame_bootstrap {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) (q : AgentState ψ × AgentState ψ)
    (hin : BootstrapIn hp l r)
    (hf : ServiceEntry.EntryFrame l r q)
    (hpaths : q.1.path = l.path ∧ q.2.path = r.path) :
    BootstrapIn hp q.1 q.2 := by
  rcases hin with ⟨hll, hrl, hllab, hrlab, hlp, hrp, hls, hrs, hlt, hrt⟩
  rcases hf with ⟨fllab, frlab, fll, frl, fls, frs, flt, frt, _, _⟩
  refine ⟨fll.trans hll, frl.trans hrl,
    fllab.trans hllab, frlab.trans hrlab, ?_, ?_,
    fls.trans hls, frs.trans hrs, flt.trans hlt, frt.trans hrt⟩
  · rcases hlp with ⟨bl, hlp⟩
    exact ⟨bl, hpaths.1.trans hlp⟩
  · rcases hrp with ⟨br, hrp⟩
    exact ⟨br, hpaths.2.trans hrp⟩

/-- The verified prefix/hole split, strengthened by exact actual SIGMOVE
identity on the occupied branch. -/
theorem move_cut_or_final_hole {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    Hole (pipeline hp κ c l r) ∨
      (let q := ServiceEntry.moveEntry hp κ l r
       BootstrapIn hp q.1 q.2 ∧
       PPLLFableZDiv.moveSourceF hp sourceCfg q.1 q.2 = q ∧
       ServiceEntry.EntryFrame l r q ∧
       q.1.path = l.path ∧ q.2.path = r.path) := by
  rcases entry_or_final_hole hp h4 κ c l r hin with hh | hf
  · exact Or.inl hh
  · right
    let q := ServiceEntry.moveEntry hp κ l r
    change ServiceEntry.EntryFrame l r q ∧
      q.1.path = l.path ∧ q.2.path = r.path at hf
    have hq : BootstrapIn hp q.1 q.2 :=
      entryFrame_bootstrap hp l r q hin hf.1 hf.2
    exact ⟨hq, move_bootstrap hp q.1 q.2 hq, hf.1, hf.2⟩

private theorem postMove_core_or_hole {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (originalL originalR l r : AgentState ψ)
    (hol : originalL.leader = false) (hor : originalR.leader = false)
    (hin : BootstrapIn hp l r) :
    let z := ServiceEntry.postMove hp κ c originalL originalR l r
    Hole z ∨
      ((z.1.leader = false ∧ z.2.leader = false) ∧
       CmpView z.1 = CmpView
          { l with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) } ∧
       CmpView z.2 = CmpView r) := by
  have hd := drop_bootstrap hp l r hin
  have hdL : PPLLBirthPatchM2.dropStale l = l := congrArg Prod.fst hd
  have hdR : PPLLBirthPatchM2.dropStale r = r := congrArg Prod.snd hd
  rcases precheck_bootstrap hp l r hin with hh | he
  · left
    have h := ServiceEntry.afterPrecheck_pairHole hp κ c
      originalL originalR
      (PPLLPostElectionGuard.preCheckReset l r).1
      (PPLLPostElectionGuard.preCheckReset l r).2 hh
    dsimp only [ServiceEntry.postMove]
    rw [hdL, hdR]
    exact h
  · have h := afterPrecheck_core_or_hole hp h4 κ c originalL originalR l r hol hor hin
    have heL : (PPLLPostElectionGuard.preCheckReset l r).1 = l :=
      congrArg Prod.fst he
    have heR : (PPLLPostElectionGuard.preCheckReset l r).2 = r :=
      congrArg Prod.snd he
    dsimp only [ServiceEntry.postMove]
    rw [hdL, hdR, heL, heR]
    exact h

/- The actual R5 row either creates a path hole or has the exact comparison
projection with the new canonical A2 at the terminal endpoint, and stays
leaderless. -/
theorem pipeline_core_or_hole {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    Hole (pipeline hp κ c l r) ∨
      (((pipeline hp κ c l r).1.leader = false ∧
        (pipeline hp κ c l r).2.leader = false) ∧
       CmpView (pipeline hp κ c l r).1 = CmpView
          { l with path2 := some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) } ∧
       CmpView (pipeline hp κ c l r).2 = CmpView r) := by
  rcases move_cut_or_final_hole hp h4 κ c l r hin with hh | hf
  · exact Or.inl hh
  let q := ServiceEntry.moveEntry hp κ l r
  have hq : BootstrapIn hp q.1 q.2 := hf.1
  have hm : PPLLFableZDiv.moveSourceF hp sourceCfg q.1 q.2 = q := hf.2.1
  have hpst := postMove_core_or_hole hp h4 κ c l r q.1 q.2 hin.1 hin.2.1 hq
  have heq : pipeline hp κ c l r =
      ServiceEntry.postMove hp κ c l r q.1 q.2 := by
    rw [ServiceEntry.pipeline_factor]
    rw [ServiceEntry.afterEntry_eq_postMove]
    exact congrArg (fun m : AgentState ψ × AgentState ψ =>
      ServiceEntry.postMove hp κ c l r m.1 m.2) hm
  rw [heq]
  rcases hpst with hh | hproj
  · exact Or.inl hh
  · right
    have hframe := hf.2.2
    have hleft : CmpView q.1 = CmpView l := by
      rcases hframe.1 with ⟨hlab, _, _, _, hs, _, ht, _, _, _⟩
      simp only [CmpView, Prod.mk.injEq]
      exact ⟨hlab, hs, hframe.2.1, ht⟩
    have hright : CmpView q.2 = CmpView r := by
      rcases hframe.1 with ⟨_, hrab, _, _, _, hrs, _, hrt, _, _⟩
      simp only [CmpView, Prod.mk.injEq]
      exact ⟨hrab, hrs, hframe.2.2, hrt⟩
    exact ⟨hproj.1, hproj.2.1.trans (cmpView_update_path2 q.1 l _ hleft),
      hproj.2.2.trans hright⟩

/-- The full-row bootstrap interface for either R5 guard. Arbitrary ancillary
fields and carried payload bits are allowed. A reset/CLEAN path deletion is
recorded as an explicit hole, while the occupied branch emits terminal A2. -/
theorem pipeline_bootstrap_or_hole {ψ : Nat} (hp : ψ > 0) (h4 : 4 ≤ ψ)
    (κ : Nat) (c : PPLLAstraR5Repair.Cfg)
    (l r : AgentState ψ) (hin : BootstrapIn hp l r) :
    Hole (pipeline hp κ c l r) ∨
      BootstrapOut l r (pipeline hp κ c l r) := by
  rcases pipeline_core_or_hole hp h4 κ c l r hin with hh | hf
  · exact Or.inl hh
  right
  have hl : (pipeline hp κ c l r).1.label = l.label ∧
      (pipeline hp κ c l r).1.state = l.state ∧
      (pipeline hp κ c l r).1.path = l.path ∧
      (pipeline hp κ c l r).1.path2 =
        some (PPLLAstraR5BootstrapCompare.canonicalA2 ψ) := by
    simpa only [CmpView, Prod.mk.injEq] using hf.2.1
  have hr : (pipeline hp κ c l r).2.label = r.label ∧
      (pipeline hp κ c l r).2.state = r.state ∧
      (pipeline hp κ c l r).2.path = r.path ∧
      (pipeline hp κ c l r).2.path2 = r.path2 := by
    simpa only [CmpView, Prod.mk.injEq] using hf.2.2
  rcases hin with ⟨_, _, _, _, _, _, hls, hrs, _, hrt⟩
  exact ⟨hf.1.1, hf.1.2, hl.1, hr.1, hl.2.2.1, hr.2.2.1,
    hl.2.1.trans hls, hr.2.1.trans hrs,
    hl.2.2.2, hr.2.2.2.trans hrt⟩

/-- A bounded, occupied instance shows that the normal branch is realized. -/
private def witnessCell (label : Fin 4) (state : MainState) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := state, path := .some label.val 0,
    reset := false, carry := false, count := 0,
    label := label, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

private def witnessLeft : AgentState 4 := witnessCell 3 .compare2
private def witnessRight : AgentState 4 := witnessCell 0 .compare1

theorem witness_bounded_bootstrap :
    BootstrapIn (by decide : 4 > 0) witnessLeft witnessRight ∧
    AgentState.inProtocolDomain 2 witnessLeft ∧
    AgentState.inProtocolDomain 2 witnessRight := by
  constructor
  · refine ⟨rfl, rfl, rfl, rfl, ⟨0, rfl⟩, ⟨0, rfl⟩,
      rfl, rfl, rfl, rfl⟩
  · constructor <;>
      simp [AgentState.inProtocolDomain, witnessLeft, witnessRight, witnessCell]

set_option maxRecDepth 2048 in
theorem witness_normal_broad :
    BootstrapOut witnessLeft witnessRight
      (pipeline (by decide : 4 > 0) 2 { selective := false }
        witnessLeft witnessRight) := by
  unfold BootstrapOut
  decide

set_option maxRecDepth 2048 in
theorem witness_normal_selective :
    BootstrapOut witnessLeft witnessRight
      (pipeline (by decide : 4 > 0) 2 { selective := true }
        witnessLeft witnessRight) := by
  unfold BootstrapOut
  decide

#check @compare_cut_normal
#check @entry_or_final_hole
#check @move_bootstrap
#check @drop_bootstrap
#check @precheck_bootstrap
#check @normalize_bootstrap
#check @check_bootstrap
#check @repair_bootstrap
#check @disappear_bootstrap
#check @disappear_view
#check @finish_core_or_hole
#check @afterPrecheck_core_or_hole
#check @move_cut_or_final_hole
#check @postMove_core_or_hole
#check @pipeline_core_or_hole
#check @pipeline_bootstrap_or_hole
#check @witness_bounded_bootstrap
#check @witness_normal_broad
#check @witness_normal_selective
#print axioms compare_cut_normal
#print axioms entry_or_final_hole
#print axioms move_bootstrap
#print axioms drop_bootstrap
#print axioms precheck_bootstrap
#print axioms normalize_bootstrap
#print axioms check_bootstrap
#print axioms repair_bootstrap
#print axioms disappear_bootstrap
#print axioms disappear_view
#print axioms finish_core_or_hole
#print axioms afterPrecheck_core_or_hole
#print axioms move_cut_or_final_hole
#print axioms postMove_core_or_hole
#print axioms pipeline_core_or_hole
#print axioms pipeline_bootstrap_or_hole
#print axioms witness_bounded_bootstrap
#print axioms witness_normal_broad
#print axioms witness_normal_selective

end PPLLAstraR5BootstrapRow
