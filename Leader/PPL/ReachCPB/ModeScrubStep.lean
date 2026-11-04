import Leader.PPL.ReachCPB.ModeCapped
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.TransitionFacts


set_option maxErrors 1000


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


private def modeScrubEraseLocal {psi kappa : Nat}
    (q : PPL.State psi kappa) : PPL.State psi kappa :=
  { q with mode := false }


/-- Field-wise equality used only after DetermineMode.  Keeping this as a
projection relation avoids ever asking Lean to normalize equality of the two
dependent-if pairs returned by DetermineMode. -/
private def modeScrubFieldEq
    {psi kappa : Nat}
    (a b : PPL.State psi kappa) : Prop :=
  And (a.leader = b.leader)
    (And (a.id = b.id)
      (And (a.dist = b.dist)
        (And (a.last = b.last)
          (And (a.tokenB = b.tokenB)
            (And (a.tokenW = b.tokenW)
              (And (a.mode = b.mode)
                (And (a.clock = b.clock)
                  (And (a.signalR = b.signalR)
                    (And (a.hits = b.hits)
                      (And (a.bullet = b.bullet)
                        (And (a.shield = b.shield)
                          (a.signalB = b.signalB))))))))))))


private theorem modeScrubFieldEq_eq
    {psi kappa : Nat}
    {a b : PPL.State psi kappa}
    (h : modeScrubFieldEq a b) :
    a = b := by
  unfold modeScrubFieldEq at h
  rcases h with
    ⟨hleader, hid, hdist, hlast, htokenB, htokenW,
      hmode, hclock, hsignalR, hhits, hbullet, hshield, hsignalB⟩
  cases a
  cases b
  simp only at hleader hid hdist hlast htokenB htokenW hmode hclock hsignalR hhits hbullet hshield hsignalB
  subst hleader hid hdist hlast htokenB htokenW hmode hclock hsignalR hhits hbullet hshield hsignalB
  rfl


/-- DetermineMode ignores the incoming stored mode bit.  This is deliberately
proved field-wise.  The two calls are never equated as pairs.


The proof unfolds the common leader branch and all shared guards.  If a
dependent capped-hit branch remains in a field goal, it splits that guard
explicitly before closing the resulting field equalities. -/
private theorem modeScrub_determineMode_fields
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d :=
      PPL.determineMode l r
    let e :=
      PPL.determineMode
        (modeScrubEraseLocal l)
        (modeScrubEraseLocal r)
    And
      (modeScrubFieldEq d.1 e.1)
      (modeScrubFieldEq d.2 e.2) := by
  dsimp only
  cases hlead : l.leader <;>
  simp only [PPL.determineMode, hlead, modeScrubEraseLocal] <;>
  unfoldFinishModes <;>
  (repeat' (split <;> try dsimp only <;>
    try simp_all [modeScrubEraseLocal])) <;>
  unfold modeScrubFieldEq <;>
  (repeat' apply And.intro) <;>
  first
    | rfl
    | (by_cases hhit : Nat.min (r.hits.val + 1) psi = psi <;> simp_all)
    | simp_all


/-- Endpoint equalities reconstructed only after all fields have been proved
equal.  In particular there is still no theorem equating the DetermineMode
pairs. -/
private theorem modeScrub_determineMode_endpoints
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    And
      ((PPL.determineMode l r).1 =
        (PPL.determineMode
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r)).1)
      ((PPL.determineMode l r).2 =
        (PPL.determineMode
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r)).2) := by
  have h :=
    modeScrub_determineMode_fields l r
  dsimp only at h
  exact
    And.intro
      (modeScrubFieldEq_eq h.1)
      (modeScrubFieldEq_eq h.2)


/-- The public line-6 guard has the same truth value after mode erasure. -/
private theorem modeScrub_line6Guard_erase
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    Iff
      (PPL.createLeaderLine6Guard hpsi l r)
      (PPL.createLeaderLine6Guard hpsi
        (modeScrubEraseLocal l)
        (modeScrubEraseLocal r)) := by
  have hd :=
    modeScrub_determineMode_endpoints l r
  unfold PPL.createLeaderLine6Guard
  dsimp only
  rw [hd.1, hd.2]


/-- Split the dependent public guard before rewriting its inputs. -/
private theorem modeScrub_line6_erase
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.createLeaderThroughLine6 hpsi l r =
      PPL.createLeaderThroughLine6 hpsi
        (modeScrubEraseLocal l)
        (modeScrubEraseLocal r) := by
  have hd :=
    modeScrub_determineMode_endpoints l r
  have hg :=
    modeScrub_line6Guard_erase hpsi l r
  by_cases h :
      PPL.createLeaderLine6Guard hpsi l r
  · have h' :
        PPL.createLeaderLine6Guard hpsi
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r) :=
      hg.mp h
    simp only [PPL.createLeaderThroughLine6, h, h']
    rw [hd.1, hd.2]
  · have h' :
        ¬ PPL.createLeaderLine6Guard hpsi
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r) := by
      intro hh
      exact h (hg.mpr hh)
    simp only [PPL.createLeaderThroughLine6, h, h']
    rw [hd.1, hd.2]


/-- Algorithm 2 lines 7--9, starting at the public line-6 boundary. -/
private def modeScrubPreTokenFromLine6
    {psi kappa : Nat}
    (s : PPL.CreateLeaderAfterLine6 psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 :=
    if r0.mode = false then
      { r0 with dist := tmp }
    else
      r0
  let l1 :=
    if r1.leader = true then
      { l0 with last := true }
    else if Or (r1.dist.val = 0) (r1.dist.val = psi) then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)


/-- Algorithms 2/3/5 receive identical arguments once the field-wise
DetermineMode result has crossed line 6.  We expose only endpoint equalities,
not another pair-equality interface. -/
private theorem modeScrub_ppl_endpoint_erase
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    And
      ((PPL.ppl hpsi l r).1 =
        (PPL.ppl hpsi
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r)).1)
      ((PPL.ppl hpsi l r).2 =
        (PPL.ppl hpsi
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r)).2) := by
  let sL :=
    PPL.createLeaderThroughLine6 hpsi l r
  let sR :=
    PPL.createLeaderThroughLine6 hpsi
      (modeScrubEraseLocal l)
      (modeScrubEraseLocal r)


  let pL :=
    modeScrubPreTokenFromLine6 sL
  let pR :=
    modeScrubPreTokenFromLine6 sR


  let bL :=
    PPL.moveToken hpsi PPL.TokenKind.black
      pL.1 pL.2
  let bR :=
    PPL.moveToken hpsi PPL.TokenKind.black
      pR.1 pR.2


  let wL :=
    PPL.moveToken hpsi PPL.TokenKind.white
      bL.1 bL.2
  let wR :=
    PPL.moveToken hpsi PPL.TokenKind.white
      bR.1 bR.2


  have hs : sL = sR := by
    dsimp only [sL, sR]
    exact
      modeScrub_line6_erase hpsi l r


  have hp : pL = pR := by
    dsimp only [pL, pR]
    exact
      congrArg
        (fun s : PPL.CreateLeaderAfterLine6 psi kappa =>
          modeScrubPreTokenFromLine6 s)
        hs


  have hb : bL = bR := by
    dsimp only [bL, bR]
    exact
      congrArg
        (fun q :
            PPL.State psi kappa × PPL.State psi kappa =>
          PPL.moveToken hpsi PPL.TokenKind.black
            q.1 q.2)
        hp


  have hw : wL = wR := by
    dsimp only [wL, wR]
    exact
      congrArg
        (fun q :
            PPL.State psi kappa × PPL.State psi kappa =>
          PPL.moveToken hpsi PPL.TokenKind.white
            q.1 q.2)
        hb


  have hcL :
      PPL.createLeader hpsi l r = wL := by
    rfl


  have hcR :
      PPL.createLeader hpsi
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r) =
        wR := by
    rfl


  have hc :
      PPL.createLeader hpsi l r =
        PPL.createLeader hpsi
          (modeScrubEraseLocal l)
          (modeScrubEraseLocal r) :=
    hcL.trans (hw.trans hcR.symm)


  have hl :=
    congrArg
      (fun q :
          PPL.State psi kappa × PPL.State psi kappa =>
        (PPL.eliminateLeaders q.1 q.2).1)
      hc


  have hr :=
    congrArg
      (fun q :
          PPL.State psi kappa × PPL.State psi kappa =>
        (PPL.eliminateLeaders q.1 q.2).2)
      hc


  exact
    And.intro
      (by
        simpa only [PPL.ppl] using hl)
      (by
        simpa only [PPL.ppl] using hr)


/-- The only fact needed from finishModes for the cap certificate: a true
stored mode at the DetermineMode boundary implies that same endpoint clock is
exactly kappa.  This proves implications directly, rather than the failed
mode = (clock == kappa) pair of equalities. -/
private theorem modeScrub_determineMode_cap
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d :=
      PPL.determineMode l r
    And
      (d.1.mode = true →
        d.1.clock.val = kappa)
      (d.2.mode = true →
        d.2.clock.val = kappa) := by
  simp only [PPL.determineMode]
  repeat' (split <;> try dsimp only)
  all_goals
    unfoldFinishModes
    dsimp only
    apply And.intro
    · intro hm
      simpa using hm
    · intro hm
      simpa using hm


/-- Public post-DetermineMode seams carry the direct finishModes certificate
through Algorithms 2/3/5. -/
private theorem modeScrub_ppl_cap
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let q :=
      PPL.ppl hpsi l r
    And
      (q.1.mode = true →
        q.1.clock.val = kappa)
      (q.2.mode = true →
        q.2.clock.val = kappa) := by
  have hm :=
    PPL.Convergence.ConstructCoupling.postDetermineModeModeStable
      hpsi l r
  have hc :=
    PPL.Probability.clockSuffixPairProjection
      hpsi l r
  have hd :=
    modeScrub_determineMode_cap l r
  dsimp only at hm hc hd ⊢
  apply And.intro
  · intro hmode
    have hdm :
        (PPL.determineMode l r).1.mode = true :=
      hm.1.symm.trans hmode
    have hdcap :
        (PPL.determineMode l r).1.clock.val = kappa :=
      hd.1 hdm
    exact
      (congrArg Fin.val hc.1).trans hdcap
  · intro hmode
    have hdm :
        (PPL.determineMode l r).2.mode = true :=
      hm.2.symm.trans hmode
    have hdcap :
        (PPL.determineMode l r).2.clock.val = kappa :=
      hd.2 hdm
    exact
      (congrArg Fin.val hc.2.2.1).trans hdcap


/-- The literal one-interaction scrub relation is closed under P_PL. -/
theorem modeScrubOneStepSpec_proved :
    ModeScrubOneStepSpec := by
  unfold ModeScrubOneStepSpec
  intro n psi kappa hpsi ring C D e hrel


  let j : Fin n :=
    ring.rightNeighbor e


  let qC :
      PPL.State psi kappa × PPL.State psi kappa :=
    PPL.ppl hpsi (C e) (C j)


  let qD :
      PPL.State psi kappa × PPL.State psi kappa :=
    PPL.ppl hpsi (D e) (D j)


  have he :
      modeScrubEraseLocal (C e) =
        modeScrubEraseLocal (D e) := by
    have h :=
      (hrel e).1
    change
      modeScrubEraseLocal (C e) =
        modeScrubEraseLocal (D e)
      at h
    exact h


  have hj :
      modeScrubEraseLocal (C j) =
        modeScrubEraseLocal (D j) := by
    have h :=
      (hrel j).1
    change
      modeScrubEraseLocal (C j) =
        modeScrubEraseLocal (D j)
      at h
    exact h


  have hleftEq :
      qC.1 = qD.1 := by
    dsimp only [qC, qD]
    calc
      (PPL.ppl hpsi (C e) (C j)).1 =
          (PPL.ppl hpsi
            (modeScrubEraseLocal (C e))
            (modeScrubEraseLocal (C j))).1 :=
        (modeScrub_ppl_endpoint_erase
          hpsi (C e) (C j)).1
      _ =
          (PPL.ppl hpsi
            (modeScrubEraseLocal (D e))
            (modeScrubEraseLocal (D j))).1 := by
        rw [he, hj]
      _ = (PPL.ppl hpsi (D e) (D j)).1 :=
        (modeScrub_ppl_endpoint_erase
          hpsi (D e) (D j)).1.symm


  have hrightEq :
      qC.2 = qD.2 := by
    dsimp only [qC, qD]
    calc
      (PPL.ppl hpsi (C e) (C j)).2 =
          (PPL.ppl hpsi
            (modeScrubEraseLocal (C e))
            (modeScrubEraseLocal (C j))).2 :=
        (modeScrub_ppl_endpoint_erase
          hpsi (C e) (C j)).2
      _ =
          (PPL.ppl hpsi
            (modeScrubEraseLocal (D e))
            (modeScrubEraseLocal (D j))).2 := by
        rw [he, hj]
      _ = (PPL.ppl hpsi (D e) (D j)).2 :=
        (modeScrub_ppl_endpoint_erase
          hpsi (D e) (D j)).2.symm


  have hcapC :
      And
        (qC.1.mode = true →
          qC.1.clock.val = kappa)
        (qC.2.mode = true →
          qC.2.clock.val = kappa) := by
    dsimp only [qC]
    exact
      modeScrub_ppl_cap hpsi (C e) (C j)


  have hleft :
      ModeScrubRelState qC.1 qD.1 := by
    unfold ModeScrubRelState
    apply And.intro
    · rw [hleftEq]
    · intro hmodeD
      have hmodeC :
          qC.1.mode = true :=
        (congrArg
          (fun z : PPL.State psi kappa =>
            z.mode)
          hleftEq).trans hmodeD
      exact
        And.intro
          hmodeC
          (hcapC.1 hmodeC)


  have hright :
      ModeScrubRelState qC.2 qD.2 := by
    unfold ModeScrubRelState
    apply And.intro
    · rw [hrightEq]
    · intro hmodeD
      have hmodeC :
          qC.2.mode = true :=
        (congrArg
          (fun z : PPL.State psi kappa =>
            z.mode)
          hrightEq).trans hmodeD
      exact
        And.intro
          hmodeC
          (hcapC.2 hmodeC)


  unfold ModeScrubRel
  intro x
  by_cases hxe : x = e
  · subst x
    simpa [qC, qD, j,
      PPL.Probability.pplStep,
      PopulationProtocol.step,
      PPL.protocol, PPL.transition, hpsi]
      using hleft
  · by_cases hxj : x = j
    · subst x
      simpa [qC, qD, j,
        PPL.Probability.pplStep,
        PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hxe]
        using hright
    · simpa [j,
        PPL.Probability.pplStep,
        PopulationProtocol.step,
        PPL.protocol, hxe, hxj]
        using hrel x


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.modeScrubOneStepSpec_proved
