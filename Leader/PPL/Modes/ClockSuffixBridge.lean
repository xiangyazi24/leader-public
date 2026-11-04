import Leader.PPL.Modes.StoppedClockInterfaces
import Leader.PPL.Probability.LotteryCounts
import Leader.PPL.TransitionFacts

namespace PPL.Probability

set_option autoImplicit false
set_option Elab.async false

/-- The statement consumed by the stopped-clock upper-tail argument. -/
def ClockSuffixTickLotteryBridge : Prop :=
  ∀ (n psi kappa : Nat), 3 ≤ n →
    ∀ (ring : DirectedRing n)
      (C : PPLConfig n psi kappa) (x : Fin n)
      (word : DetSchedule n),
      clockSuffixTicks ring C x word ≤
        (lotteryRun psi (lotteryOffset (C x).hits.val)
          (clockSuffixBits ring C x word)).wins

/-- Generalized induction invariant: the lottery parser's unfinished H-run is
exactly the current physical hits counter of the tracked agent. -/
def ClockLotteryInvariant
    {n psi kappa : Nat}
    (C : PPLConfig n psi kappa)
    (x : Fin n) (s : LotteryState) : Prop :=
  s.headRun = (C x).hits.val

private def clockArmedSignalVal
    {psi kappa : Nat} (q : PPL.State psi kappa) : Nat :=
  if q.leader = true then kappa else q.signalR.val

private def clockBumpedHitsVal
    {psi kappa : Nat} (q : PPL.State psi kappa) : Nat :=
  Nat.min (q.hits.val + 1) psi

private theorem rightNeighbor_ne_self_clock
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem leftNeighbor_rightNeighbor_clock
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by
      omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem rightNeighbor_leftNeighbor_clock
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by
      omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    have hlt : i.val - 1 < n := by omega
    have hleft : (i.val + n - 1) % n = i.val - 1 := by
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-- Exact Algorithm-2 prefix through line 9, just before the two token
passes.  This is definitionally the corresponding prefix of createLeader. -/
private def clockPreTokenPair
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
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
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private theorem clockLine6_clock_hits
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    s.left.clock = d.1.clock ∧ s.left.hits = d.1.hits ∧
      s.right.clock = d.2.clock ∧ s.right.hits = d.2.hits := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

private theorem clockPreTokenPair_clock_hits
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := clockPreTokenPair hpsi l r
    q.1.clock = d.1.clock ∧
      q.1.hits = d.1.hits ∧
      q.2.clock = d.2.clock ∧
      q.2.hits = d.2.hits := by
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hs := clockLine6_clock_hits hpsi l r
  have hp :
      let q := clockPreTokenPair hpsi l r
      q.1.clock = s.left.clock ∧ q.1.hits = s.left.hits ∧
        q.2.clock = s.right.clock ∧ q.2.hits = s.right.hits := by
    dsimp only [clockPreTokenPair]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  dsimp only at hs hp ⊢
  exact ⟨hp.1.trans hs.1, hp.2.1.trans hs.2.1,
    hp.2.2.1.trans hs.2.2.1, hp.2.2.2.trans hs.2.2.2⟩

private theorem moveToken_clock_hits
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    q.1.clock = l.clock ∧
      q.1.hits = l.hits ∧
      q.2.clock = r.clock ∧
      q.2.hits = r.hits := by
  exact PPL.moveToken_clock_hits hpsi kind l r

private theorem createLeader_clock_hits
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.createLeader hpsi l r
    q.1.clock = d.1.clock ∧
      q.1.hits = d.1.hits ∧
      q.2.clock = d.2.clock ∧
      q.2.hits = d.2.hits := by
  let p := clockPreTokenPair hpsi l r
  let b := PPL.moveToken hpsi .black p.1 p.2
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hdef : PPL.createLeader hpsi l r = w := by
    rfl
  have hp := clockPreTokenPair_clock_hits hpsi l r
  have hb := moveToken_clock_hits hpsi PPL.TokenKind.black p.1 p.2
  have hw := moveToken_clock_hits hpsi PPL.TokenKind.white b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact
    ⟨hw.1.trans (hb.1.trans hp.1),
      hw.2.1.trans (hb.2.1.trans hp.2.1),
      hw.2.2.1.trans (hb.2.2.1.trans hp.2.2.1),
      hw.2.2.2.trans (hb.2.2.2.trans hp.2.2.2)⟩

private theorem eliminateLeaders_clock_hits
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    q.1.clock = l.clock ∧
      q.1.hits = l.hits ∧
      q.2.clock = r.clock ∧
      q.2.hits = r.hits := by
  dsimp only
  have hl := PPL.Elim.otherView_eliminateLeaders_left l r
  have hr := PPL.Elim.otherView_eliminateLeaders_right l r
  exact ⟨congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.clock) hl,
    congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.hits) hl,
    congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.clock) hr,
    congrArg (fun z : PPL.Elim.OtherFields psi kappa => z.hits) hr⟩

/-- Pair-level physical seam used by the suffix induction.  DetermineMode is
the only part of the full P_PL interaction that can write clock or hits. -/
def ClockSuffixPairProjection : Prop :=
  ∀ {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa),
    let d := PPL.determineMode l r
    let q := PPL.ppl hpsi l r
    q.1.clock = d.1.clock ∧
      q.1.hits = d.1.hits ∧
      q.2.clock = d.2.clock ∧
      q.2.hits = d.2.hits

theorem clockSuffixPairProjection :
    ClockSuffixPairProjection := by
  intro psi kappa hpsi l r
  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc := createLeader_clock_hits hpsi l r
  have he := eliminateLeaders_clock_hits c.1 c.2
  have hdef : PPL.ppl hpsi l r = q := by
    rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact
    ⟨he.1.trans hc.1,
      he.2.1.trans hc.2.1,
      he.2.2.1.trans hc.2.2.1,
      he.2.2.2.trans hc.2.2.2⟩

private theorem pplStep_endpoint_clock_hits
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (e : Fin n) :
    let j := ring.rightNeighbor e
    let d := PPL.determineMode (C e) (C j)
    ((pplStep ring C e e).clock = d.1.clock ∧
      (pplStep ring C e e).hits = d.1.hits) ∧
    ((pplStep ring C e j).clock = d.2.clock ∧
      (pplStep ring C e j).hits = d.2.hits) := by
  dsimp only
  have hp := clockSuffixPairProjection hpsi
    (C e) (C (ring.rightNeighbor e))
  dsimp only at hp
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_clock ring (by omega) e
  constructor
  · constructor
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi] using hp.1
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi] using hp.2.1
  · constructor
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne] using hp.2.2.1
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne] using hp.2.2.2

private theorem pplStep_other_state
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (e x : Fin n)
    (hxe : x ≠ e)
    (hxr : x ≠ ring.rightNeighbor e) :
    pplStep ring C e x = C x := by
  simp [pplStep, PopulationProtocol.step, PPL.protocol, hxe, hxr]

private theorem pplStep_eq_self_of_not_paper
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : ¬ 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (e : Fin n) :
    pplStep ring C e = C := by
  funext k
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_clock ring (by omega) e
  by_cases hke : k = e
  · subst k
    simp [pplStep, PopulationProtocol.step,
      PPL.protocol, PPL.transition, hpsi]
  · by_cases hkr : k = ring.rightNeighbor e
    · subst k
      simp [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne]
    · simp [pplStep, PopulationProtocol.step,
        PPL.protocol, hke, hkr]

private theorem noReset_signal_zero
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : PPLConfig n psi kappa)
    (x e : Fin n)
    (hinc : x = e ∨ x = ring.rightNeighbor e)
    (hreset : clockResetAt ring C x e = false) :
    clockArmedSignalVal (C e) = 0 ∧
      (C (ring.rightNeighbor e)).signalR.val = 0 := by
  have hf := hreset
  unfold clockResetAt at hf
  dsimp only at hf
  change
    decide
      ((x = e ∨ x = ring.rightNeighbor e) ∧
        (0 < clockArmedSignalVal (C e) ∨
          0 < (C (ring.rightNeighbor e)).signalR.val)) = false at hf
  simp only [decide_eq_false_iff_not] at hf
  have hz :
      ¬ (0 < clockArmedSignalVal (C e) ∨
        0 < (C (ring.rightNeighbor e)).signalR.val) := by
    intro hs
    exact hf ⟨hinc, hs⟩
  constructor <;> omega

private theorem bumpedHits_eq_psi_iff
    {psi kappa : Nat} (q : PPL.State psi kappa) :
    clockBumpedHitsVal q = psi ↔
      psi ≤ q.hits.val + 1 := by
  unfold clockBumpedHitsVal
  constructor
  · intro h
    calc
      psi = clockBumpedHitsVal q := h.symm
      _ ≤ q.hits.val + 1 := by
        unfold clockBumpedHitsVal
        exact Nat.min_le_left _ _
  · intro h
    exact Nat.min_eq_right h

elab "unfoldFinishModes" : tactic => do
  let finish := Lean.mkIdent
    ((((`_private.Leader.PPL.Transition).num 0).str "PPL").str "finishModes")
  let zero := Lean.mkIdent
    ((((`_private.Leader.PPL.Transition).num 0).str "PPL").str "zeroFin")
  let capped := Lean.mkIdent
    ((((`_private.Leader.PPL.Transition).num 0).str "PPL").str "cappedSucc")
  let top := Lean.mkIdent
    ((((`_private.Leader.PPL.Transition).num 0).str "PPL").str "topFin")
  let tac ← `(tactic| unfold $finish:ident)
  Lean.Elab.Tactic.evalTactic tac
  let tac ← `(tactic| try (unfold $zero:ident))
  Lean.Elab.Tactic.evalTactic tac
  let tac ← `(tactic| try (unfold $capped:ident))
  Lean.Elab.Tactic.evalTactic tac
  let tac ← `(tactic| try (unfold $top:ident))
  Lean.Elab.Tactic.evalTactic tac

private theorem determineMode_noSignal_fields
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hl : clockArmedSignalVal l = 0)
    (hr : r.signalR.val = 0) :
    let q := PPL.determineMode l r
    q.1.clock = l.clock ∧
      q.1.hits.val = 0 ∧
      q.2.hits.val =
        (if clockBumpedHitsVal r = psi then
          0
        else
          clockBumpedHitsVal r) ∧
      (r.clock.val < q.2.clock.val →
        clockBumpedHitsVal r = psi) := by
  cases hlead : l.leader with
  | false =>
      have hls : l.signalR.val = 0 := by
        simpa [clockArmedSignalVal, hlead] using hl
      by_cases hhit : clockBumpedHitsVal r = psi
      · simp [PPL.determineMode, hlead, hls, hr,
          clockBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal] <;> omega
      · simp [PPL.determineMode, hlead, hls, hr,
          clockBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal] <;> omega
  | true =>
      have hk : kappa = 0 := by
        simpa [clockArmedSignalVal, hlead] using hl
      by_cases hhit : clockBumpedHitsVal r = psi
      · simp [PPL.determineMode, hlead, hk, hr,
          clockBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal] <;> omega
      · simp [PPL.determineMode, hlead, hk, hr,
          clockBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal] <;> omega

private theorem clockSuffixTicksAux_zero_of_not_paper
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : ¬ 2 ≤ psi)
    (ring : DirectedRing n) (x : Fin n) :
    ∀ (C : PPLConfig n psi kappa)
      (word : DetSchedule n),
      clockSuffixTicksAux ring x C word = 0 := by
  intro C word
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hreset : clockResetAt ring C x e with
      | true =>
          simp [clockSuffixTicksAux, hreset]
      | false =>
          let C' := pplStep ring C e
          have hsame :
              C' = C := by
            exact pplStep_eq_self_of_not_paper
              hn3 hpsi ring C e
          have htail := ih C
          simpa [clockSuffixTicksAux, hreset, C', hsame]
            using htail

/-- Strong induction statement.  Existing wins are carried on the left, so
the invariant composes through an arbitrary suffix without resetting the
lottery accumulator. -/
private theorem clockSuffixAux_bridge
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (x : Fin n) :
    ∀ (C : PPLConfig n psi kappa)
      (word : DetSchedule n)
      (s : LotteryState),
      ClockLotteryInvariant C x s →
      s.wins + clockSuffixTicksAux ring x C word ≤
        (lotteryRun psi s
          (clockSuffixBitsAux ring x C word)).wins := by
  intro C word s hsync
  induction word generalizing C s with
  | nil =>
      simp [clockSuffixTicksAux, clockSuffixBitsAux, lotteryRun]
  | cons e rest ih =>
      change s.headRun = (C x).hits.val at hsync
      cases hreset : clockResetAt ring C x e with
      | true =>
          simp [clockSuffixTicksAux, clockSuffixBitsAux,
            hreset, lotteryRun]
      | false =>
          let C' := pplStep ring C e
          by_cases hH : e = ring.leftNeighbor x
          · subst e
            have hrx :
                ring.rightNeighbor (ring.leftNeighbor x) = x :=
              rightNeighbor_leftNeighbor_clock ring x
            have hinc :
                x = ring.leftNeighbor x ∨
                  x = ring.rightNeighbor (ring.leftNeighbor x) :=
              Or.inr hrx.symm
            have hzeros :=
              noReset_signal_zero ring C x
                (ring.leftNeighbor x) hinc hreset
            have hright0 : (C x).signalR.val = 0 := by
              simpa [hrx] using hzeros.2
            have hdet :=
              determineMode_noSignal_fields hpsi
                (C (ring.leftNeighbor x)) (C x)
                hzeros.1 hright0
            dsimp only at hdet
            have hfull0 :=
              pplStep_endpoint_clock_hits hn3 hpsi
                ring C (ring.leftNeighbor x)
            have hfull :
                (C' x).clock =
                    (PPL.determineMode
                      (C (ring.leftNeighbor x)) (C x)).2.clock ∧
                  (C' x).hits =
                    (PPL.determineMode
                      (C (ring.leftNeighbor x)) (C x)).2.hits := by
              simpa [C', hrx] using hfull0.2
            have hhits :
                (C' x).hits.val =
                  (if clockBumpedHitsVal (C x) = psi then
                    0
                  else
                    clockBumpedHitsVal (C x)) := by
              exact
                (congrArg Fin.val hfull.2).trans hdet.2.2.1
            have htick :
                (C x).clock.val < (C' x).clock.val →
                  clockBumpedHitsVal (C x) = psi := by
              intro ht
              have hc := congrArg Fin.val hfull.1
              rw [hc] at ht
              exact hdet.2.2.2 ht
            by_cases hwin : psi ≤ s.headRun + 1
            · have hphysWin :
                  clockBumpedHitsVal (C x) = psi := by
                apply
                  (bumpedHits_eq_psi_iff (C x)).2
                simpa [hsync] using hwin
              let s' := lotteryStep psi s true
              have hsync' :
                  ClockLotteryInvariant C' x s' := by
                unfold ClockLotteryInvariant
                simp [s', lotteryStep, hwin,
                  hhits, hphysWin]
              have htail := ih C' s' hsync'
              have hsWin :
                  s'.wins = s.wins + 1 := by
                simp [s', lotteryStep, hwin]
              have htickOne :
                  (if (C x).clock.val < (C' x).clock.val
                    then 1 else 0) ≤ 1 := by
                split <;> omega
              have htotal :
                  s.wins +
                      (if (C x).clock.val < (C' x).clock.val
                        then 1 else 0) +
                      clockSuffixTicksAux ring x C' rest ≤
                    (lotteryRun psi s'
                      (clockSuffixBitsAux ring x C' rest)).wins := by
                rw [hsWin] at htail
                omega
              simpa [clockSuffixTicksAux, clockSuffixBitsAux,
                hreset, incidentBit, lotteryRun, C', s', Nat.add_assoc]
                using htotal
            · have hphysNo :
                  clockBumpedHitsVal (C x) ≠ psi := by
                intro hb
                have hle :=
                  (bumpedHits_eq_psi_iff (C x)).1 hb
                apply hwin
                simpa [hsync] using hle
              have hmin :
                  clockBumpedHitsVal (C x) =
                    (C x).hits.val + 1 := by
                unfold clockBumpedHitsVal
                apply Nat.min_eq_left
                have hlt : (C x).hits.val + 1 < psi := by
                  omega
                exact Nat.le_of_lt hlt
              have hclockNo :
                  ¬ (C x).clock.val < (C' x).clock.val := by
                intro ht
                exact hphysNo (htick ht)
              have hneq : (C x).hits.val + 1 ≠ psi := by
                omega
              have hnwin : ¬ psi ≤ (C x).hits.val + 1 := by
                omega
              let s' := lotteryStep psi s true
              have hsync' :
                  ClockLotteryInvariant C' x s' := by
                unfold ClockLotteryInvariant
                simp [s', lotteryStep, hhits, hmin, hneq, hnwin, hsync]
              have htail := ih C' s' hsync'
              have hsWin :
                  s'.wins = s.wins := by
                simp [s', lotteryStep, hwin]
              have htotal :
                  s.wins +
                      clockSuffixTicksAux ring x C' rest ≤
                    (lotteryRun psi s'
                      (clockSuffixBitsAux ring x C' rest)).wins := by
                rw [hsWin] at htail
                exact htail
              simpa [clockSuffixTicksAux, clockSuffixBitsAux,
                hreset, incidentBit, lotteryRun, C', s',
                hclockNo] using htotal
          · by_cases hT : e = x
            · subst e
              have hinc :
                  x = x ∨ x = ring.rightNeighbor x :=
                Or.inl rfl
              have hzeros :=
                noReset_signal_zero ring C x x hinc hreset
              have hdet :=
                determineMode_noSignal_fields hpsi
                  (C x) (C (ring.rightNeighbor x))
                  hzeros.1 hzeros.2
              dsimp only at hdet
              have hfull :=
                (pplStep_endpoint_clock_hits
                  hn3 hpsi ring C x).1
              have hclock :
                  (C' x).clock = (C x).clock := by
                exact hfull.1.trans hdet.1
              have hhits :
                  (C' x).hits.val = 0 := by
                exact
                  (congrArg Fin.val hfull.2).trans hdet.2.1
              let s' := lotteryStep psi s false
              have hsync' :
                  ClockLotteryInvariant C' x s' := by
                unfold ClockLotteryInvariant
                simp [s', lotteryStep, hhits]
              have htail := ih C' s' hsync'
              have hsWin :
                  s'.wins = s.wins := by
                simp [s', lotteryStep]
              have htotal :
                  s.wins +
                      clockSuffixTicksAux ring x C' rest ≤
                    (lotteryRun psi s'
                      (clockSuffixBitsAux ring x C' rest)).wins := by
                rw [hsWin] at htail
                exact htail
              simpa [clockSuffixTicksAux, clockSuffixBitsAux,
                hreset, incidentBit, hH, lotteryRun,
                C', s', hclock] using htotal
            · have hxr :
                  x ≠ ring.rightNeighbor e := by
                intro hx
                have hp :=
                  congrArg (fun y => ring.leftNeighbor y) hx
                rw [leftNeighbor_rightNeighbor_clock ring e] at hp
                exact hH hp.symm
              have hstate :
                  C' x = C x := by
                exact pplStep_other_state ring C e x
                  (fun hxe => hT hxe.symm) hxr
              have hsync' :
                  ClockLotteryInvariant C' x s := by
                unfold ClockLotteryInvariant
                rw [hstate]
                exact hsync
              have htail := ih C' s hsync'
              simpa [clockSuffixTicksAux, clockSuffixBitsAux,
                hreset, incidentBit, hH, hT, C', hstate]
                using htail

theorem clockSuffixTickLotteryBridge :
    ClockSuffixTickLotteryBridge := by
  intro n psi kappa hn3 ring C x word
  by_cases hpsi : 2 ≤ psi
  · have hsync :
        ClockLotteryInvariant C x
          (lotteryOffset (C x).hits.val) := by
      rfl
    have h :=
      clockSuffixAux_bridge hn3 hpsi ring x C word
        (lotteryOffset (C x).hits.val) hsync
    simpa [clockSuffixTicks, clockSuffixBits, lotteryOffset]
      using h
  · have hz :=
      clockSuffixTicksAux_zero_of_not_paper
        hn3 hpsi ring x C word
    unfold clockSuffixTicks
    rw [hz]
    exact Nat.zero_le _

end PPL.Probability

#print axioms PPL.Probability.clockSuffixPairProjection
#print axioms PPL.Probability.clockSuffixTickLotteryBridge
