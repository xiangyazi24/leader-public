import Leader.Wu.Birth.ShortDoneTerminalCapEndpointWitness

namespace BirthShortDoneTerminalCapGeneralR2

open PPLL PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthGenerationControlRepair BirthGenerationDone
open BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1
open BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection
  K2BirthLeaderNormalize BirthShortDoneCuts

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide

/-- Positive form of the literal repaired pre-Finish cap test. -/
def AtCapEntry2 (kappa : Nat) (l r : AgentState 2) : Prop :=
  let s := preFinishEntry2 h2 hle2 kappa l r
  s.2.label = widthTerminal h2 hle2 /\ s.2.count = kappa


/-- The literal repaired width-two Finish shape on a positive cap row. -/
theorem waitWidthEntry2_of_atCap
    (kappa : Nat) (l r : AgentState 2)
    (hab : r.label =
      ⟨(l.label.val + 1) % 2, Nat.mod_lt _ h2⟩)
    (hcap : AtCapEntry2 kappa l r) :
    let w := waitWidthEntry h2 h2 hle2 kappa l r
    w.1.label = 0 /\ w.2.label = 1 /\
      w.1.wait = false /\ w.2.wait = true /\
      w.2.count = kappa := by
  let s := preFinishEntry2 h2 hle2 kappa l r
  change s.2.label = widthTerminal h2 hle2 /\ s.2.count = kappa at hcap

  have hlabels : s.1.label = l.label /\ s.2.label = r.label := by
    unfold s preFinishEntry2
    simp [waitSaturatedPrepare, terminalInactiveClear,
      waitWidthCarry, waitWidthReset]

  have hterm : widthTerminal h2 hle2 = (1 : Fin 2) := by
    apply Fin.ext
    rfl

  have hr1 : r.label = 1 :=
    hlabels.2.symm.trans (hcap.1.trans hterm)

  have hl0 : l.label = 0 := by
    have hfin : l.label = 0 ∨ l.label = 1 := by
      have h : l.label.val = 0 ∨ l.label.val = 1 := by omega
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hfin with hl | hl
    · exact hl
    · exfalso
      have hv := congrArg Fin.val hab
      simpa [hl, hr1] using hv

  have hs0 : s.1.label = 0 := hlabels.1.trans hl0
  have hsne : s.1.label ≠ (⟨2 - 1, by omega⟩ : Fin 2) := by
    intro ht
    have hv := congrArg Fin.val (hs0.symm.trans ht)
    simpa using hv

  unfold waitWidthEntry
  change
    let p := waitSaturatedPrepare h2 l r
    let e := terminalInactiveClear h2 hle2 p.1 p.2
    let c := waitWidthCarry h2 hle2 kappa e.1 e.2
    let t := waitWidthReset h2 hle2 c.1 c.2
    let w := waitWidthFinish h2 h2 hle2 kappa t.1 t.2
    w.1.label = 0 /\ w.2.label = 1 /\
      w.1.wait = false /\ w.2.wait = true /\
      w.2.count = kappa
  change
    let w := waitWidthFinish h2 h2 hle2 kappa s.1 s.2
    w.1.label = 0 /\ w.2.label = 1 /\
      w.1.wait = false /\ w.2.wait = true /\
      w.2.count = kappa
  simp [waitWidthFinish, hcap.1, hcap.2, hterm, hs0, hsne]


/-- Proof-only spelling of the actual ordinary metadata tail from the post-WAIT cut. -/
def postWaitDone2
    (a b d e : Registers 2) (pa pb : Bool) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let g := genCleanAfterWait h2 (cell d) (cell e)
  let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
  let q2 := authorizedEliminateSig h2 q1.1 q1.2
  let q3 := authorizedDoneMove h2 q2.1 q2.2
  let q4 :=
    PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair h2
      (PPLLWallSweepPreCheckResetRepair.preCheckResetWall q3.1 q3.2)
  let q5 := preserveDoneCheck h2 q4.1 q4.2
  let q6 := afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
    (authBirth ⟨cell a, pa⟩ ⟨cell b, pb⟩ q6) q6


/-- Only the fields needed by the cap-tail proof.  CLEAN may alter `path`,
    `path4`, `path5`, and other cleanup material; those are deliberately not
    part of this view. -/
private structure CapView2 where
  label : Fin 2
  count : Nat
  wait : Bool
  leader : Bool
  resetCmd : Bool
  state : MainState
  path2 : Option Path2Info


private def capView2 (u : AgentState 2) : CapView2 :=
  ⟨u.label, u.count, u.wait, u.leader, u.reset_cmd, u.state, u.path2⟩


private def leftCapView2 (d : Registers 2) : CapView2 :=
  ⟨d.label, d.count, true, false, false, .depart, none⟩


private def rightCapView2 (e : Registers 2) : CapView2 :=
  ⟨e.label, e.count, true, false, false, .depart, none⟩


/-- Exact seven-field image of the cap-row GEN suffix.  No case split on the
    two arbitrary data bits is needed because the bits occur only inside the
    newly written `path`, which is outside `CapView2`. -/
private theorem genAfterWait_capView2
    (d e : Registers 2)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let g := genCleanAfterWait h2 (cell d) (cell e)
    capView2 g.1 = leftCapView2 d /\
      capView2 g.2 = rightCapView2 e := by
  simp [genCleanAfterWait, genSigSaturatedStart, genCleanEmit,
    genCleanPropagate, genSigSaturatedFinish,
    capView2, leftCapView2, rightCapView2,
    cell, hd, he, hwd, hwe]


/-! CLEAN is factored exactly as its source stages.  Each leaf below is tiny:
    it proves only that one CLEAN primitive is invisible to `CapView2`. -/


private theorem cleanGenConnect_capView2 (u : AgentState 2) :
    capView2 (cleanSigGenConnect u) = capView2 u := by
  unfold cleanSigGenConnect capView2
  split <;> simp


private theorem cleanStep3_capView2 (l r : AgentState 2) :
    let q := cleanSigStep3 l r
    capView2 q.1 = capView2 l /\ capView2 q.2 = capView2 r := by
  unfold cleanSigStep3 capView2
  repeat (first | constructor | rfl | split)


private theorem cleanStep4_capView2 (l r : AgentState 2) :
    let q := cleanSigStep4 l r
    capView2 q.1 = capView2 l /\ capView2 q.2 = capView2 r := by
  unfold cleanSigStep4 capView2
  repeat (first | constructor | rfl | split)


private theorem cleanStep5_capView2 (l r : AgentState 2) :
    let q := cleanSigStep5 h2 l r
    capView2 q.1 = capView2 l /\ capView2 q.2 = capView2 r := by
  unfold cleanSigStep5 capView2
  repeat (first | constructor | rfl | split)


private theorem cleanStep6_capView2 (l r : AgentState 2) :
    let q := cleanSigStep6 h2 l r
    capView2 q.1 = capView2 l /\ capView2 q.2 = capView2 r := by
  unfold cleanSigStep6 capView2
  repeat (first | constructor | rfl | split)


private theorem cleanApply_capView2 (u : AgentState 2) :
    capView2 (cleanSigCleanApply u) = capView2 u := by
  cases hp : u.path with
  | bot =>
      simp [cleanSigCleanApply, hp, capView2]
  | some pathLabel pathBit =>
      cases hp4 : u.path4 with
      | none =>
          cases hp5 : u.path5 with
          | none =>
              simp [cleanSigCleanApply, hp, hp4, hp5, capView2]
          | some p5 =>
              rcases p5 with ⟨label5, bit5⟩
              simp [cleanSigCleanApply, hp, hp4, hp5, capView2]
      | some p4 =>
          rcases p4 with ⟨label4, bit4⟩
          cases hp5 : u.path5 with
          | none =>
              simp [cleanSigCleanApply, hp, hp4, hp5, capView2]
          | some p5 =>
              rcases p5 with ⟨label5, bit5⟩
              simp [cleanSigCleanApply, hp, hp4, hp5, capView2]


private theorem cleanSig_capView2 (l r : AgentState 2) :
    let q := cleanSig h2 l r
    capView2 q.1 = capView2 l /\ capView2 q.2 = capView2 r := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  let q1 := cleanSigStep3 l0 r0
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 h2 q2.1 q2.2
  let q4 := cleanSigStep6 h2 q3.1 q3.2


  have h0L : capView2 l0 = capView2 l :=
    cleanGenConnect_capView2 l
  have h0R : capView2 r0 = capView2 r :=
    cleanGenConnect_capView2 r


  have h1 := cleanStep3_capView2 l0 r0
  change capView2 q1.1 = capView2 l0 /\
    capView2 q1.2 = capView2 r0 at h1


  have h2' := cleanStep4_capView2 q1.1 q1.2
  change capView2 q2.1 = capView2 q1.1 /\
    capView2 q2.2 = capView2 q1.2 at h2'


  have h3 := cleanStep5_capView2 q2.1 q2.2
  change capView2 q3.1 = capView2 q2.1 /\
    capView2 q3.2 = capView2 q2.2 at h3


  have h4 := cleanStep6_capView2 q3.1 q3.2
  change capView2 q4.1 = capView2 q3.1 /\
    capView2 q4.2 = capView2 q3.2 at h4


  have hL : capView2 q4.1 = capView2 l :=
    h4.1.trans (h3.1.trans (h2'.1.trans (h1.1.trans h0L)))
  have hR : capView2 q4.2 = capView2 r :=
    h4.2.trans (h3.2.trans (h2'.2.trans (h1.2.trans h0R)))


  change
    capView2 (cleanSigCleanApply q4.1) = capView2 l /\
      capView2 (cleanSigCleanApply q4.2) = capView2 r
  exact ⟨(cleanApply_capView2 q4.1).trans hL,
    (cleanApply_capView2 q4.2).trans hR⟩


/-- `authorizedReconcile` does not alter the raw cores computed by CLEAN. -/
private theorem authorizedClean_capView2
    (l r : AuthorizedAgentState 2) :
    let q := authorizedCleanSig h2 l r
    capView2 q.1.core = capView2 l.core /\
      capView2 q.2.core = capView2 r.core := by
  change
    capView2 (cleanSig h2 l.core r.core).1 = capView2 l.core /\
      capView2 (cleanSig h2 l.core r.core).2 = capView2 r.core
  exact cleanSig_capView2 l.core r.core


/-- On this prefix the responder is `.depart`, so Algorithm 9's only active
    outer branch is impossible.  Authorization may be normalized, but the two
    physical cores are exact. -/
private theorem authorizedEliminate_of_right_depart2
    (l r : AuthorizedAgentState 2)
    (hr : r.core.state = .depart) :
    let q := authorizedEliminateSig h2 l r
    q.1.core = l.core /\ q.2.core = r.core := by
  change
    (eliminateSig h2 l.core r.core).1 = l.core /\
      (eliminateSig h2 l.core r.core).2 = r.core
  simp [eliminateSig, hr]


/-- First reusable post-WAIT certificate for the repaired DONE host.
    This stops exactly after authorized ELIMINATE. -/
theorem postWaitDone2_gen_clean_eliminate_frame
    (d e : Registers 2)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let g := genCleanAfterWait h2 (cell d) (cell e)
    let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
    let q2 := authorizedEliminateSig h2 q1.1 q1.2
    q2.1.core.label = 0 /\
      q2.2.core.label = 1 /\
      q2.2.core.count = e.count /\
      q2.1.core.wait = true /\
      q2.2.core.wait = true /\
      q2.1.core.leader = false /\
      q2.2.core.leader = false /\
      q2.1.core.reset_cmd = false /\
      q2.2.core.reset_cmd = false /\
      q2.1.core.state = .depart /\
      q2.2.core.state = .depart /\
      q2.1.core.path2 = none /\
      q2.2.core.path2 = none := by
  let g := genCleanAfterWait h2 (cell d) (cell e)
  let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
  let q2 := authorizedEliminateSig h2 q1.1 q1.2


  have hg := genAfterWait_capView2 d e hd he hwd hwe
  change capView2 g.1 = leftCapView2 d /\
    capView2 g.2 = rightCapView2 e at hg


  have hc := authorizedClean_capView2
    (⟨g.1, false⟩ : AuthorizedAgentState 2)
    (⟨g.2, false⟩ : AuthorizedAgentState 2)
  change capView2 q1.1.core = capView2 g.1 /\
    capView2 q1.2.core = capView2 g.2 at hc


  have hq1L : capView2 q1.1.core = leftCapView2 d :=
    hc.1.trans hg.1
  have hq1R : capView2 q1.2.core = rightCapView2 e :=
    hc.2.trans hg.2


  have hq1Rdepart : q1.2.core.state = .depart := by
    have h := congrArg CapView2.state hq1R
    simpa [capView2, rightCapView2] using h


  have helim := authorizedEliminate_of_right_depart2
    q1.1 q1.2 hq1Rdepart
  change q2.1.core = q1.1.core /\ q2.2.core = q1.2.core at helim


  have hL : capView2 q2.1.core = leftCapView2 d := by
    rw [helim.1]
    exact hq1L
  have hR : capView2 q2.2.core = rightCapView2 e := by
    rw [helim.2]
    exact hq1R


  have hlLabel := congrArg CapView2.label hL
  have hrLabel := congrArg CapView2.label hR
  have hrCount := congrArg CapView2.count hR
  have hlWait := congrArg CapView2.wait hL
  have hrWait := congrArg CapView2.wait hR
  have hlLeader := congrArg CapView2.leader hL
  have hrLeader := congrArg CapView2.leader hR
  have hlReset := congrArg CapView2.resetCmd hL
  have hrReset := congrArg CapView2.resetCmd hR
  have hlState := congrArg CapView2.state hL
  have hrState := congrArg CapView2.state hR
  have hlPath2 := congrArg CapView2.path2 hL
  have hrPath2 := congrArg CapView2.path2 hR


  have hlLabel0 : q2.1.core.label = 0 := by
    simpa [capView2, leftCapView2, hd] using hlLabel
  have hrLabel1 : q2.2.core.label = 1 := by
    simpa [capView2, rightCapView2, he] using hrLabel
  simpa [capView2, leftCapView2, rightCapView2, hd, he] using
    ⟨hlLabel0, hrLabel1, hrCount, hlWait, hrWait,
      hlLeader, hrLeader, hlReset, hrReset,
      hlState, hrState, hlPath2, hrPath2⟩

#print axioms BirthShortDoneTerminalCapGeneralR2.postWaitDone2_gen_clean_eliminate_frame
end BirthShortDoneTerminalCapGeneralR2
