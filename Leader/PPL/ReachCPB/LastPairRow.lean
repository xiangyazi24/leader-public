import Leader.PPL.ReachCPB.StepLast
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.Modes.SignalLineageLocal

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Lemma 16 capped-last selected-pair row

The row is true.

The only subtlety is Algorithm 4's private helper layer.  We do not name any
private declaration.  Instead we mirror those tiny definitions locally and
use definitional equality with the public `PPL.determineMode`.  The rest of
the proof stays on public interfaces:

* `PPL.createLeaderThroughLine6` / `PPL.createLeaderLine6Guard` for
  Algorithm 2;
* `PPL.moveToken_initiator_fields` /
  `PPL.moveToken_responder_fields` for both Algorithm-3 passes;
* `PPL.Elim.otherView_eliminateLeaders_left/right` for Algorithm 5;
* the already-proved clock, mode, and reset-signal suffix projections.
-/

/-! ## Local definitional mirror of DetermineMode's private helpers -/

private def lastPairZeroFin (m : Nat) : Fin (m + 1) :=
  ⟨0, by omega⟩

private def lastPairTopFin (m : Nat) : Fin (m + 1) :=
  ⟨m, by omega⟩

private def lastPairCappedSucc
    {m : Nat} (x : Fin (m + 1)) : Fin (m + 1) :=
  ⟨Nat.min (x.val + 1) m,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private def lastPairPredFinOfPos
    {m : Nat} (x : Fin (m + 1))
    (hx : 0 < x.val) : Fin (m + 1) :=
  ⟨x.val - 1, by omega⟩

private def lastPairFinishModes
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  ({ l with mode := l.clock.val == kappa },
   { r with mode := r.clock.val == kappa })

private def lastPairDetermineMode
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let l :=
    if l.leader = true then
      { l with signalR := lastPairTopFin kappa }
    else
      l
  let l : PPL.State psi kappa :=
    { l with hits := lastPairZeroFin psi }
  let r : PPL.State psi kappa :=
    { r with hits := lastPairCappedSucc r.hits }
  if hsignal :
      Or (0 < l.signalR.val) (0 < r.signalR.val) then
    let l0 : PPL.State psi kappa :=
      { l with clock := lastPairZeroFin kappa }
    let r0 : PPL.State psi kappa :=
      { r with clock := lastPairZeroFin kappa }
    if hge : r0.signalR.val ≤ l0.signalR.val then
      have hlpos : 0 < l0.signalR.val := by
        dsimp only [l0, r0] at hge ⊢
        rcases hsignal with hl | hr
        · exact hl
        · omega
      let r1 : PPL.State psi kappa :=
        { r0 with
          signalR := l0.signalR
          hits := lastPairZeroFin psi }
      let l1 : PPL.State psi kappa :=
        { l0 with signalR := lastPairZeroFin kappa }
      let r2 :=
        if hhit : r1.hits.val = psi then
          { r1 with
            signalR :=
              lastPairPredFinOfPos l0.signalR hlpos
            hits := lastPairZeroFin psi }
        else
          r1
      lastPairFinishModes l1 r2
    else
      have hrpos : 0 < r0.signalR.val := by
        dsimp only [l0, r0] at hge ⊢
        rcases hsignal with hl | hr
        · omega
        · exact hr
      let l1 : PPL.State psi kappa :=
        { l0 with signalR := lastPairZeroFin kappa }
      let r1 :=
        if hhit : r0.hits.val = psi then
          { r0 with
            signalR :=
              lastPairPredFinOfPos r0.signalR hrpos
            hits := lastPairZeroFin psi }
        else
          r0
      lastPairFinishModes l1 r1
  else
    let r :=
      if hhit : r.hits.val = psi then
        let r : PPL.State psi kappa :=
          { r with clock := lastPairCappedSucc r.clock }
        { r with hits := lastPairZeroFin psi }
      else
        r
    lastPairFinishModes l r

private theorem lastPairDetermineMode_eq
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    PPL.determineMode l r =
      lastPairDetermineMode l r := by
  rfl

/-! ## DetermineMode on a capped leaderless zero-reset pair -/

private theorem lastPairDetermineModeCapped
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = false)
    (hlSignal : l.signalR.val = 0)
    (hrSignal : r.signalR.val = 0)
    (hlClock : l.clock.val = kappa)
    (hrClock : r.clock.val = kappa) :
    let d := PPL.determineMode l r
    And (d.1.clock.val = kappa)
      (And (d.2.clock.val = kappa)
        (And (d.1.mode = true)
          (And (d.2.mode = true)
            (And (d.1.signalR.val = 0)
              (And (d.2.signalR.val = 0)
                (And (d.1.leader = false)
                  (And (d.2.leader = false)
                    (And (d.1.dist = l.dist)
                      (And (d.2.dist = r.dist)
                        (And (d.1.last = l.last)
                          (d.2.last = r.last))))))))))) := by
  rw [lastPairDetermineMode_eq]
  have hkmin :
      Nat.min (kappa + 1) kappa = kappa :=
    Nat.min_eq_right (Nat.le_succ kappa)
  by_cases hhit :
      Nat.min (r.hits.val + 1) psi = psi
  · simp
      [lastPairDetermineMode,
        lastPairZeroFin,
        lastPairCappedSucc,
        lastPairFinishModes,
        hlLeader, hrLeader,
        hlSignal, hrSignal,
        hlClock, hrClock,
        hhit, hkmin] <;>
      omega
  · simp
      [lastPairDetermineMode,
        lastPairZeroFin,
        lastPairCappedSucc,
        lastPairFinishModes,
        hlLeader, hrLeader,
        hlSignal, hrSignal,
        hlClock, hrClock,
        hhit, hkmin] <;>
      omega

/-! ## Algorithm 2 through line 9 -/

private def lastPairLine4Tmp
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    Fin (2 * psi) :=
  let d := PPL.determineMode l r
  if d.2.leader = true then
    ⟨0, by omega⟩
  else
    ⟨(d.1.dist.val + 1) % (2 * psi),
      Nat.mod_lt _ (by omega)⟩

private theorem lastPairLine6Guard_iff
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.createLeaderLine6Guard hpsi l r ↔
      And
        ((PPL.determineMode l r).2.mode = true)
        (lastPairLine4Tmp hpsi l r ≠
          (PPL.determineMode l r).2.dist) := by
  rfl

private def lastPairPreTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s :=
    PPL.createLeaderThroughLine6 hpsi l r
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
    else if Or (r1.dist.val = 0)
        (r1.dist.val = psi) then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private theorem lastPairPreToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = false)
    (hlSignal : l.signalR.val = 0)
    (hrSignal : r.signalR.val = 0)
    (hlClock : l.clock.val = kappa)
    (hrClock : r.clock.val = kappa)
    (hDist :
      r.dist.val =
        (l.dist.val + 1) % (2 * psi)) :
    let p := lastPairPreTokenPair hpsi l r
    And (p.1.dist = l.dist)
      (And
        (p.1.last =
          if Or (r.dist.val = 0)
              (r.dist.val = psi)
          then false
          else r.last)
        (And (p.2.dist = r.dist)
          (p.2.last = r.last))) := by
  have hd :=
    lastPairDetermineModeCapped
      hpsi l r
      hlLeader hrLeader
      hlSignal hrSignal
      hlClock hrClock
  dsimp only at hd
  rcases hd with
    ⟨_hClockL, _hClockR,
      _hModeL, hModeR,
      _hSignalL, _hSignalR,
      _hLeaderL, hLeaderR,
      hDistL, hDistR,
      _hLastL, hLastR⟩
  have htmp :
      lastPairLine4Tmp hpsi l r =
        (PPL.determineMode l r).2.dist := by
    apply Fin.ext
    simp
      [lastPairLine4Tmp,
        hLeaderR, hDistL, hDistR,
        hDist]
  have hguard :
      ¬ PPL.createLeaderLine6Guard
          hpsi l r := by
    intro hg
    have hg' :=
      (lastPairLine6Guard_iff
        hpsi l r).1 hg
    exact hg'.2 htmp
  simp
    [lastPairPreTokenPair,
      PPL.createLeaderThroughLine6,
      hguard,
      hModeR, hLeaderR,
      hDistL, hDistR, hLastR]
  all_goals (split <;> simp_all)
  all_goals
    intro ha hb
    rename_i hor
    exact (hor.elim ha hb).elim

/-! ## Algorithms 3 and 5 preserve dist/last -/

private theorem lastPairMoveToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (And (q.1.last = l.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l r with
    hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId,
          PPL.birthFields]

private theorem lastPairEliminate_dist_last
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    And (q.1.dist = l.dist)
      (And (q.1.last = l.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left
      l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right
      l r
  exact
    And.intro
      (congrArg
        (fun z :
          PPL.Elim.OtherFields psi kappa =>
            z.dist) hl)
      (And.intro
        (congrArg
          (fun z :
            PPL.Elim.OtherFields psi kappa =>
              z.last) hl)
        (And.intro
          (congrArg
            (fun z :
              PPL.Elim.OtherFields psi kappa =>
                z.dist) hr)
          (congrArg
            (fun z :
              PPL.Elim.OtherFields psi kappa =>
                z.last) hr)))

private theorem lastPairCreateLeader_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = false)
    (hlSignal : l.signalR.val = 0)
    (hrSignal : r.signalR.val = 0)
    (hlClock : l.clock.val = kappa)
    (hrClock : r.clock.val = kappa)
    (hDist :
      r.dist.val =
        (l.dist.val + 1) % (2 * psi)) :
    let q := PPL.createLeader hpsi l r
    And (q.1.dist = l.dist)
      (And
        (q.1.last =
          if Or (r.dist.val = 0)
              (r.dist.val = psi)
          then false
          else r.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  let p :=
    lastPairPreTokenPair hpsi l r
  let b :=
    PPL.moveToken
      hpsi PPL.TokenKind.black
      p.1 p.2
  let w :=
    PPL.moveToken
      hpsi PPL.TokenKind.white
      b.1 b.2
  have hdef :
      PPL.createLeader hpsi l r = w := by
    rfl
  have hp :=
    lastPairPreToken_dist_last
      hpsi l r
      hlLeader hrLeader
      hlSignal hrSignal
      hlClock hrClock hDist
  have hb :=
    lastPairMoveToken_dist_last
      hpsi PPL.TokenKind.black
      p.1 p.2
  have hw :=
    lastPairMoveToken_dist_last
      hpsi PPL.TokenKind.white
      b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact
    And.intro
      (hw.1.trans
        (hb.1.trans hp.1))
      (And.intro
        (hw.2.1.trans
          (hb.2.1.trans hp.2.1))
        (And.intro
          (hw.2.2.1.trans
            (hb.2.2.1.trans hp.2.2.1))
          (hw.2.2.2.trans
            (hb.2.2.2.trans hp.2.2.2))))

private theorem lastPairPpl_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = false)
    (hlSignal : l.signalR.val = 0)
    (hrSignal : r.signalR.val = 0)
    (hlClock : l.clock.val = kappa)
    (hrClock : r.clock.val = kappa)
    (hDist :
      r.dist.val =
        (l.dist.val + 1) % (2 * psi)) :
    let q := PPL.ppl hpsi l r
    And (q.1.dist = l.dist)
      (And
        (q.1.last =
          if Or (r.dist.val = 0)
              (r.dist.val = psi)
          then false
          else r.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  let c :=
    PPL.createLeader hpsi l r
  let q :=
    PPL.eliminateLeaders c.1 c.2
  have hc :=
    lastPairCreateLeader_dist_last
      hpsi l r
      hlLeader hrLeader
      hlSignal hrSignal
      hlClock hrClock hDist
  have he :=
    lastPairEliminate_dist_last
      c.1 c.2
  have hdef :
      PPL.ppl hpsi l r = q := by
    rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact
    And.intro
      (he.1.trans hc.1)
      (And.intro
        (he.2.1.trans hc.2.1)
        (And.intro
          (he.2.2.1.trans hc.2.2.1)
          (he.2.2.2.trans hc.2.2.2)))

/-! ## Requested row -/

theorem lemma16LastPairRowSpec_proved :
    Lemma16LastPairRowSpec := by
  unfold Lemma16LastPairRowSpec
  intro psi kappa hpsi l r
  intro hlLeader hrLeader
  intro hlSignal hrSignal
  intro hlClock hrClock
  intro hDist
  have hd :=
    lastPairDetermineModeCapped
      hpsi l r
      hlLeader hrLeader
      hlSignal hrSignal
      hlClock hrClock
  dsimp only at hd
  rcases hd with
    ⟨hdClockL, hdClockR,
      hdModeL, hdModeR,
      hdSignalL, hdSignalR,
      _hdLeaderL, _hdLeaderR,
      _hdDistL, _hdDistR,
      _hdLastL, _hdLastR⟩
  have hc :=
    PPL.Probability.clockSuffixPairProjection
      hpsi l r
  have hm :=
    PPL.Convergence.ConstructCoupling.postDetermineModeModeStable
      hpsi l r
  have hs :=
    PPL.Modes.SignalLineage.postDetermineModeSignalStable
      hpsi l r
  have hdl :=
    lastPairPpl_dist_last
      hpsi l r
      hlLeader hrLeader
      hlSignal hrSignal
      hlClock hrClock hDist
  dsimp only at hc hm hs hdl
  exact
    And.intro
      ((congrArg Fin.val hc.1).trans
        hdClockL)
      (And.intro
        ((congrArg Fin.val hc.2.2.1).trans
          hdClockR)
        (And.intro
          (hm.1.trans hdModeL)
          (And.intro
            (hm.2.trans hdModeR)
            (And.intro
              ((congrArg Fin.val hs.1).trans
                hdSignalL)
              (And.intro
                ((congrArg Fin.val
                  hs.2.2.1).trans
                    hdSignalR)
                (And.intro
                  hdl.1
                  (And.intro
                    hdl.2.2.1
                    (And.intro
                      hdl.2.1
                      hdl.2.2.2))))))))

/-! ## Existing global assembly -/

theorem lemma16LastForcingCappedStepSpec_proved :
    Lemma16LastForcingCappedStepSpec :=
  lemma16LastForcingCappedStepSpec
    lemma16LastPairRowSpec_proved

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16LastPairRowSpec_proved
#print axioms PPL.Convergence.ReachCPB.lemma16LastForcingCappedStepSpec_proved

