import Leader.PPL.ReachCPB.ForcingCapped
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.TransitionFacts


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


private def foldlAndFalse (xs : List Bool) :
    xs.foldl (fun a b => a && b) false = false := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp only [List.foldl_cons]
      cases b <;> simpa using ih


private def foldlAndFalseOfMem
    (xs : List Bool)
    (hmem : false ∈ xs) :
    xs.foldl (fun a b => a && b) true = false := by
  induction xs with
  | nil =>
      simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | ht
      · subst b
        simp only [List.foldl_cons]
        exact foldlAndFalse xs
      · cases b with
        | false =>
            simp only [List.foldl_cons]
            exact foldlAndFalse xs
        | true =>
            simp only [List.foldl_cons]
            exact ih ht


private def foldlAndTrueOfAllTrue
    (xs : List Bool)
    (hall : ∀ b, b ∈ xs → b = true) :
    xs.foldl (fun a b => a && b) true = true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb : b = true := hall b (by simp)
      have ht : ∀ c, c ∈ xs → c = true := by
        intro c hc
        exact hall c (by simp [hc])
      subst b
      simpa [List.foldl_cons] using ih ht


private def allAgentsBPointwise
    {n : Nat}
    (p : Fin n → Bool)
    (h : PPL.Modes.Lemma6.allAgentsB p = true) :
    ∀ i : Fin n, p i = true := by
  intro i
  cases hi : p i with
  | true =>
      rfl
  | false =>
      have hmem : false ∈ List.ofFn p := by
        rw [List.mem_ofFn]
        exact ⟨i, hi⟩
      have hf := foldlAndFalseOfMem (List.ofFn p) hmem
      unfold PPL.Modes.Lemma6.allAgentsB at h
      rw [hf] at h
      contradiction


private def allAgentsBOfPointwise
    {n : Nat}
    (p : Fin n → Bool)
    (h : ∀ i : Fin n, p i = true) :
    PPL.Modes.Lemma6.allAgentsB p = true := by
  unfold PPL.Modes.Lemma6.allAgentsB
  apply foldlAndTrueOfAllTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  calc
    b = p i := hi.symm
    _ = true := h i


private def signalFreePointwise
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : PPL.Modes.Lemma6.signalFreeB C = true) :
    ∀ i : Fin n, (C i).signalR.val = 0 := by
  unfold PPL.Modes.Lemma6.signalFreeB at h
  intro i
  have hi :=
    allAgentsBPointwise
      (fun j : Fin n =>
        decide ((C j).signalR.val = 0)) h i
  exact of_decide_eq_true hi


private def allDetectPointwise
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : PPL.Modes.Lemma6.allDetectB C = true) :
    ∀ i : Fin n, (C i).mode = true := by
  unfold PPL.Modes.Lemma6.allDetectB at h
  intro i
  have hi :=
    allAgentsBPointwise
      (fun j : Fin n =>
        decide ((C j).mode = true)) h i
  exact of_decide_eq_true hi


private def signalFreeOfPointwise
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : ∀ i : Fin n, (C i).signalR.val = 0) :
    PPL.Modes.Lemma6.signalFreeB C = true := by
  unfold PPL.Modes.Lemma6.signalFreeB
  apply allAgentsBOfPointwise
  intro i
  simp [h i]


private def allDetectOfPointwise
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : ∀ i : Fin n, (C i).mode = true) :
    PPL.Modes.Lemma6.allDetectB C = true := by
  unfold PPL.Modes.Lemma6.allDetectB
  apply allAgentsBOfPointwise
  intro i
  simp [h i]


private def rightNeighborNeSelfStepDist
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private def determineModeDistLeader
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    And (d.1.dist = l.dist)
      (And (d.2.dist = r.dist)
        (And (d.1.leader = l.leader)
          (d.2.leader = r.leader))) := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact And.intro rfl
      (And.intro rfl
        (And.intro rfl rfl))


private def stepDistZeroFin (m : Nat) : Fin (m + 1) :=
  ⟨0, by omega⟩

private def stepDistTopFin (m : Nat) : Fin (m + 1) :=
  ⟨m, by omega⟩

private def stepDistCappedSucc {m : Nat} (x : Fin (m + 1)) : Fin (m + 1) :=
  ⟨Nat.min (x.val + 1) m, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private def stepDistPredFinOfPos
    {m : Nat} (x : Fin (m + 1)) (hx : 0 < x.val) : Fin (m + 1) :=
  ⟨x.val - 1, by omega⟩

private def stepDistFinishModes
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) : PPL.State psi kappa × PPL.State psi kappa :=
  ({ l with mode := l.clock.val == kappa },
   { r with mode := r.clock.val == kappa })

private def stepDistDetermineMode
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) : PPL.State psi kappa × PPL.State psi kappa :=
  let l :=
    if l.leader = true then
      { l with signalR := stepDistTopFin kappa }
    else
      l
  let l : PPL.State psi kappa :=
    { l with hits := stepDistZeroFin psi }
  let r : PPL.State psi kappa :=
    { r with hits := stepDistCappedSucc r.hits }
  if hsignal : Or (0 < l.signalR.val) (0 < r.signalR.val) then
    let l0 : PPL.State psi kappa :=
      { l with clock := stepDistZeroFin kappa }
    let r0 : PPL.State psi kappa :=
      { r with clock := stepDistZeroFin kappa }
    if hge : r0.signalR.val ≤ l0.signalR.val then
      have hlpos : 0 < l0.signalR.val := by
        dsimp only [l0, r0] at hge ⊢
        rcases hsignal with hl | hr
        · exact hl
        · omega
      let r1 : PPL.State psi kappa :=
        { r0 with signalR := l0.signalR, hits := stepDistZeroFin psi }
      let l1 : PPL.State psi kappa :=
        { l0 with signalR := stepDistZeroFin kappa }
      let r2 :=
        if hhit : r1.hits.val = psi then
          { r1 with
            signalR := stepDistPredFinOfPos l0.signalR hlpos
            hits := stepDistZeroFin psi }
        else
          r1
      stepDistFinishModes l1 r2
    else
      have hrpos : 0 < r0.signalR.val := by
        dsimp only [l0, r0] at hge ⊢
        rcases hsignal with hl | hr
        · omega
        · exact hr
      let l1 : PPL.State psi kappa :=
        { l0 with signalR := stepDistZeroFin kappa }
      let r1 :=
        if hhit : r0.hits.val = psi then
          { r0 with
            signalR := stepDistPredFinOfPos r0.signalR hrpos
            hits := stepDistZeroFin psi }
        else
          r0
      stepDistFinishModes l1 r1
  else
    let r :=
      if hhit : r.hits.val = psi then
        let r : PPL.State psi kappa :=
          { r with clock := stepDistCappedSucc r.clock }
        { r with hits := stepDistZeroFin psi }
      else
        r
    stepDistFinishModes l r

private theorem stepDistDetermineMode_eq
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    PPL.determineMode l r = stepDistDetermineMode l r := by
  rfl


private def determineModeCappedNoSignal
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlleader : l.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let d := PPL.determineMode l r
    And (d.1.mode = true)
      (And (d.2.mode = true)
        (And (d.1.clock.val = kappa)
          (And (d.2.clock.val = kappa)
            (And (d.1.signalR.val = 0)
              (d.2.signalR.val = 0))))) := by
  dsimp only
  have hcap :
      Nat.min (r.clock.val + 1) kappa = kappa := by
    rw [hrclock]
    exact Nat.min_eq_right (Nat.le_succ kappa)
  rw [stepDistDetermineMode_eq]
  by_cases hhit :
      Nat.min (r.hits.val + 1) psi = psi
  · simp [stepDistDetermineMode, stepDistZeroFin, stepDistTopFin,
      stepDistCappedSucc, stepDistPredFinOfPos, stepDistFinishModes,
      hlleader, hlsignal, hrsignal, hhit, hcap, hlclock, hrclock] <;> omega
  · simp [stepDistDetermineMode, stepDistZeroFin, stepDistTopFin,
      stepDistCappedSucc, stepDistPredFinOfPos, stepDistFinishModes,
      hlleader, hlsignal, hrsignal, hhit, hcap, hlclock, hrclock] <;> omega


private def line6DistMode
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    And (s.left.dist = d.1.dist)
      (And (s.right.dist = d.2.dist)
        (And (s.left.mode = d.1.mode)
          (s.right.mode = d.2.mode))) := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · exact
      And.intro rfl
        (And.intro rfl
          (And.intro rfl rfl))
  · exact
      And.intro rfl
        (And.intro rfl
          (And.intro rfl rfl))


private def moveTokenDist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields hpsi kind l r
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l r with hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId,
          PPL.birthFields]


private def eliminateLeadersDist
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    And.intro
      (congrArg
        (fun z : PPL.Elim.OtherFields psi kappa =>
          z.dist) hl)
      (congrArg
        (fun z : PPL.Elim.OtherFields psi kappa =>
          z.dist) hr)


private def createLeaderDistCapped
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlleader : l.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let q := PPL.createLeader hpsi l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  let d := PPL.determineMode l r
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hd0 := determineModeDistLeader l r
  have hd :
      And (d.1.dist = l.dist)
        (And (d.2.dist = r.dist)
          (And (d.1.leader = l.leader)
            (d.2.leader = r.leader))) := by
    simpa [d] using hd0
  have hc0 :=
    determineModeCappedNoSignal
      hpsi l r hlleader hlsignal hrsignal
      hlclock hrclock
  have hc :
      And (d.1.mode = true)
        (And (d.2.mode = true)
          (And (d.1.clock.val = kappa)
            (And (d.2.clock.val = kappa)
              (And (d.1.signalR.val = 0)
                (d.2.signalR.val = 0))))) := by
    simpa [d] using hc0
  have hs0 := line6DistMode hpsi l r
  have hs :
      And (s.left.dist = d.1.dist)
        (And (s.right.dist = d.2.dist)
          (And (s.left.mode = d.1.mode)
            (s.right.mode = d.2.mode))) := by
    simpa [d, s] using hs0
  have hsLeftDist : s.left.dist = l.dist :=
    hs.1.trans hd.1
  have hsRightDist : s.right.dist = r.dist :=
    hs.2.1.trans hd.2.1
  have hsRightMode : s.right.mode = true :=
    hs.2.2.2.trans hc.2.1
  have hsRightNotConstruct :
      s.right.mode ≠ false := by
    intro hf
    have htf : true = false :=
      hsRightMode.symm.trans hf
    cases htf
  let r0 : PPL.State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  have hr0 : r0.dist = r.dist := by
    dsimp [r0]
    rw [if_neg hsRightNotConstruct]
    exact hsRightDist
  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { s.left with last := true }
    else if
        Or (r0.dist.val = 0)
          (r0.dist.val = psi) then
      { s.left with last := false }
    else
      { s.left with last := r0.last }
  have hl0 : l0.dist = l.dist := by
    dsimp only [l0]
    split
    · simp [hsLeftDist]
    · split <;> simp [hsLeftDist]
  let b := PPL.moveToken hpsi .black l0 r0
  have hb0 :=
    moveTokenDist hpsi PPL.TokenKind.black l0 r0
  have hb :
      And (b.1.dist = l0.dist)
        (b.2.dist = r0.dist) := by
    simpa [b] using hb0
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hw0 :=
    moveTokenDist hpsi PPL.TokenKind.white b.1 b.2
  have hw :
      And (w.1.dist = b.1.dist)
        (w.2.dist = b.2.dist) := by
    simpa [w] using hw0
  have hdef :
      PPL.createLeader hpsi l r = w := by
    rfl
  rw [hdef]
  exact
    And.intro
      (hw.1.trans (hb.1.trans hl0))
      (hw.2.trans (hb.2.trans hr0))


private def pplDistCapped
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlleader : l.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let q := PPL.ppl hpsi l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc0 :=
    createLeaderDistCapped
      hpsi l r hlleader hlsignal hrsignal
      hlclock hrclock
  have hc :
      And (c.1.dist = l.dist)
        (c.2.dist = r.dist) := by
    simpa [c] using hc0
  have he0 := eliminateLeadersDist c.1 c.2
  have he :
      And (q.1.dist = c.1.dist)
        (q.2.dist = c.2.dist) := by
    simpa [q] using he0
  have hdef : PPL.ppl hpsi l r = q := by
    rfl
  rw [hdef]
  exact
    And.intro
      (he.1.trans hc.1)
      (he.2.trans hc.2)


private def pplCappedFrame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlleader : l.leader = false)
    (hlmode : l.mode = true)
    (hrmode : r.mode = true)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let q := PPL.ppl hpsi l r
    And (q.1.dist = l.dist)
      (And (q.2.dist = r.dist)
        (And (q.1.mode = l.mode)
          (And (q.2.mode = r.mode)
            (And (q.1.clock = l.clock)
              (And (q.2.clock = r.clock)
                (And (q.1.signalR = l.signalR)
                  (q.2.signalR = r.signalR))))))) := by
  let d := PPL.determineMode l r
  let q := PPL.ppl hpsi l r
  have hdet0 :=
    determineModeCappedNoSignal
      hpsi l r hlleader hlsignal hrsignal
      hlclock hrclock
  have hdet :
      And (d.1.mode = true)
        (And (d.2.mode = true)
          (And (d.1.clock.val = kappa)
            (And (d.2.clock.val = kappa)
              (And (d.1.signalR.val = 0)
                (d.2.signalR.val = 0))))) := by
    simpa [d] using hdet0
  have hdist0 :=
    pplDistCapped
      hpsi l r hlleader hlsignal hrsignal
      hlclock hrclock
  have hdist :
      And (q.1.dist = l.dist)
        (q.2.dist = r.dist) := by
    simpa [q] using hdist0
  have hm0 :=
    PPL.Convergence.ConstructCoupling.postDetermineModeModeStable
      hpsi l r
  have hm :
      And (q.1.mode = d.1.mode)
        (q.2.mode = d.2.mode) := by
    simpa [q, d] using hm0
  have hc0 :=
    PPL.Probability.clockSuffixPairProjection
      hpsi l r
  have hc :
      And (q.1.clock = d.1.clock)
        (And (q.1.hits = d.1.hits)
          (And (q.2.clock = d.2.clock)
            (q.2.hits = d.2.hits))) := by
    simpa [q, d] using hc0
  have hs0 :=
    PPL.Modes.SignalLineage.postDetermineModeSignalStable
      hpsi l r
  have hs :
      And (q.1.signalR = d.1.signalR)
        (And (q.1.hits = d.1.hits)
          (And (q.2.signalR = d.2.signalR)
            (q.2.hits = d.2.hits))) := by
    simpa [q, d] using hs0
  have hmodeLeft : q.1.mode = l.mode :=
    (hm.1.trans hdet.1).trans hlmode.symm
  have hmodeRight : q.2.mode = r.mode :=
    (hm.2.trans hdet.2.1).trans hrmode.symm
  have hclockLeft : q.1.clock = l.clock := by
    apply Fin.ext
    calc
      q.1.clock.val = d.1.clock.val :=
        congrArg Fin.val hc.1
      _ = kappa := hdet.2.2.1
      _ = l.clock.val := hlclock.symm
  have hclockRight : q.2.clock = r.clock := by
    apply Fin.ext
    calc
      q.2.clock.val = d.2.clock.val :=
        congrArg Fin.val hc.2.2.1
      _ = kappa := hdet.2.2.2.1
      _ = r.clock.val := hrclock.symm
  have hsignalLeft : q.1.signalR = l.signalR := by
    apply Fin.ext
    calc
      q.1.signalR.val = d.1.signalR.val :=
        congrArg Fin.val hs.1
      _ = 0 := hdet.2.2.2.2.1
      _ = l.signalR.val := hlsignal.symm
  have hsignalRight : q.2.signalR = r.signalR := by
    apply Fin.ext
    calc
      q.2.signalR.val = d.2.signalR.val :=
        congrArg Fin.val hs.2.2.1
      _ = 0 := hdet.2.2.2.2.2
      _ = r.signalR.val := hrsignal.symm
  exact
    And.intro hdist.1
      (And.intro hdist.2
        (And.intro hmodeLeft
          (And.intro hmodeRight
            (And.intro hclockLeft
              (And.intro hclockRight
                (And.intro hsignalLeft
                  hsignalRight))))))


private def stepFieldFrameOfPair
    {n psi kappa : Nat}
    {A : Type}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (f : PPL.State psi kappa → A)
    (hp :
      And
        (f (PPL.ppl hpsi
          (C e) (C (ring.rightNeighbor e))).1 =
            f (C e))
        (f (PPL.ppl hpsi
          (C e) (C (ring.rightNeighbor e))).2 =
            f (C (ring.rightNeighbor e)))) :
    ∀ i : Fin n,
      f
          (PopulationProtocol.step
            (PPL.protocol psi kappa) ring C e i) =
        f (C i) := by
  intro i
  have hne :
      ring.rightNeighbor e ≠ e :=
    rightNeighborNeSelfStepDist ring (by omega) e
  by_cases hie : i = e
  · subst i
    simpa [PopulationProtocol.step, PPL.protocol,
      PPL.transition, hpsi] using hp.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, PPL.protocol,
        PPL.transition, hpsi, hne] using hp.2
    · simp [PopulationProtocol.step, hie, hij]


private def stepCappedFrame
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hleader : ∀ i : Fin n, (C i).leader = false)
    (hmode : ∀ i : Fin n, (C i).mode = true)
    (hsignal : ∀ i : Fin n, (C i).signalR.val = 0)
    (hclock : ∀ i : Fin n, (C i).clock.val = kappa) :
    let D : Config n psi kappa :=
      PopulationProtocol.step
        (PPL.protocol psi kappa) ring C e
    And (∀ i : Fin n, (D i).dist = (C i).dist)
      (And (∀ i : Fin n, (D i).mode = (C i).mode)
        (And (∀ i : Fin n, (D i).clock = (C i).clock)
          (∀ i : Fin n, (D i).signalR = (C i).signalR))) := by
  dsimp only
  have hp0 :=
    pplCappedFrame hpsi
      (C e) (C (ring.rightNeighbor e))
      (hleader e)
      (hmode e)
      (hmode (ring.rightNeighbor e))
      (hsignal e)
      (hsignal (ring.rightNeighbor e))
      (hclock e)
      (hclock (ring.rightNeighbor e))
  have hp :
      And
        ((PPL.ppl hpsi
          (C e) (C (ring.rightNeighbor e))).1.dist =
            (C e).dist)
        (And
          ((PPL.ppl hpsi
            (C e) (C (ring.rightNeighbor e))).2.dist =
              (C (ring.rightNeighbor e)).dist)
          (And
            ((PPL.ppl hpsi
              (C e) (C (ring.rightNeighbor e))).1.mode =
                (C e).mode)
            (And
              ((PPL.ppl hpsi
                (C e) (C (ring.rightNeighbor e))).2.mode =
                  (C (ring.rightNeighbor e)).mode)
              (And
                ((PPL.ppl hpsi
                  (C e) (C (ring.rightNeighbor e))).1.clock =
                    (C e).clock)
                (And
                  ((PPL.ppl hpsi
                    (C e) (C (ring.rightNeighbor e))).2.clock =
                      (C (ring.rightNeighbor e)).clock)
                  (And
                    ((PPL.ppl hpsi
                      (C e) (C (ring.rightNeighbor e))).1.signalR =
                        (C e).signalR)
                    ((PPL.ppl hpsi
                      (C e) (C (ring.rightNeighbor e))).2.signalR =
                        (C (ring.rightNeighbor e)).signalR))))))) := by
    simpa using hp0
  have hdist :=
    stepFieldFrameOfPair
      hn3 hpsi ring C e
      (fun q : PPL.State psi kappa => q.dist)
      (And.intro hp.1 hp.2.1)
  have hmodeFrame :=
    stepFieldFrameOfPair
      hn3 hpsi ring C e
      (fun q : PPL.State psi kappa => q.mode)
      (And.intro hp.2.2.1 hp.2.2.2.1)
  have hclockFrame :=
    stepFieldFrameOfPair
      hn3 hpsi ring C e
      (fun q : PPL.State psi kappa => q.clock)
      (And.intro
        hp.2.2.2.2.1
        hp.2.2.2.2.2.1)
  have hsignalFrame :=
    stepFieldFrameOfPair
      hn3 hpsi ring C e
      (fun q : PPL.State psi kappa => q.signalR)
      (And.intro
        hp.2.2.2.2.2.2.1
        hp.2.2.2.2.2.2.2)
  exact
    And.intro hdist
      (And.intro hmodeFrame
        (And.intro hclockFrame
          hsignalFrame))


private def stepDistLine4Tmp
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


private def line6GuardOfBad
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlleader : l.leader = false)
    (hrleader : r.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa)
    (hbad :
      r.dist.val ≠
        (l.dist.val + 1) % (2 * psi)) :
    PPL.createLeaderLine6Guard hpsi l r := by
  have hf := determineModeDistLeader l r
  have hc :=
    determineModeCappedNoSignal
      hpsi l r hlleader hlsignal hrsignal
      hlclock hrclock
  dsimp only at hf hc
  change
    (PPL.determineMode l r).2.mode = true ∧
      (PPL.createLeaderThroughLine6 hpsi l r).tmp ≠
        (PPL.determineMode l r).2.dist
  have htmpBridge :
      stepDistLine4Tmp hpsi l r =
        (PPL.createLeaderThroughLine6 hpsi l r).tmp := by
    dsimp only [stepDistLine4Tmp, PPL.createLeaderThroughLine6]
    rfl
  refine And.intro hc.2.1 ?_
  intro heq
  have heqTmp :
      stepDistLine4Tmp hpsi l r =
        (PPL.determineMode l r).2.dist :=
    htmpBridge.trans heq
  have hv := congrArg Fin.val heqTmp
  simp [stepDistLine4Tmp, hf.2.2.2, hrleader,
    hf.1] at hv
  rw [hf.2.1] at hv
  exact hbad hv.symm


private def view4SetDist
    {psi kappa : Nat}
    (q : PPL.State psi kappa)
    (d : Fin (2 * psi)) :
    PPL.Elim.view4 { q with dist := d } =
      PPL.Elim.view4 q := by
  rfl


private def fin3CasesStepDist
    (b : Fin 3) :
    Or (b = (0 : Fin 3))
      (Or (b = (1 : Fin 3))
        (b = (2 : Fin 3))) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega


private def rowERightBornStepDist
    (l : PPL.Elim.Cell4) :
    (PPL.Elim.rowE l
      PPL.Safety.PeacefulProps.born4).2 =
        PPL.Safety.PeacefulProps.born4 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases fin3CasesStepDist lb with
    rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  simp [PPL.Safety.PeacefulProps.born4,
    PPL.Elim.rowE]


private def pplResponderLeaderOfLine6Guard
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hguard :
      PPL.createLeaderLine6Guard hpsi l r) :
    (PPL.ppl hpsi l r).2.leader = true := by
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hbirth0 :=
    PPL.createLeader_line6_birth
      hpsi l r hguard
  have hbirth :
      And (s.right.leader = true)
        (And
          (s.right.bullet = (2 : Fin 3))
          (And
            (s.right.shield = true)
            (s.right.signalB = false))) := by
    simpa [s] using hbirth0
  have hsview :
      PPL.Elim.view4 s.right =
        PPL.Safety.PeacefulProps.born4 := by
    rcases hbirth with ⟨hleader, hbullet, hshield, hsignal⟩
    simp only [PPL.Elim.view4,
      PPL.Safety.PeacefulProps.born4,
      hleader, hbullet, hshield, hsignal]
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  have hpview :
      PPL.Elim.view4 p.2 =
        PPL.Safety.PeacefulProps.born4 := by
    change
      PPL.Elim.view4
          (if s.right.mode = false then
            { s.right with dist := s.tmp }
          else
            s.right) =
        PPL.Safety.PeacefulProps.born4
    split
    · exact
        (view4SetDist s.right s.tmp).trans
          hsview
    · exact hsview
  let b :=
    PPL.moveToken hpsi
      PPL.TokenKind.black p.1 p.2
  have hb0 :=
    PPL.moveToken_view4_cases
      hpsi PPL.TokenKind.black p.1 p.2
  have hbview :
      PPL.Elim.view4 b.2 =
        PPL.Safety.PeacefulProps.born4 := by
    rcases hb0.2 with hsame | hborn
    · dsimp [b]
      exact hsame.trans hpview
    · dsimp [b]
      simpa [PPL.Safety.PeacefulProps.born4]
        using hborn
  let w :=
    PPL.moveToken hpsi
      PPL.TokenKind.white b.1 b.2
  have hw0 :=
    PPL.moveToken_view4_cases
      hpsi PPL.TokenKind.white b.1 b.2
  have hwview :
      PPL.Elim.view4 w.2 =
        PPL.Safety.PeacefulProps.born4 := by
    rcases hw0.2 with hsame | hborn
    · dsimp [w]
      exact hsame.trans hbview
    · dsimp [w]
      simpa [PPL.Safety.PeacefulProps.born4]
        using hborn
  have hcreate :
      PPL.createLeader hpsi l r = w := by
    rfl
  let c := PPL.createLeader hpsi l r
  have hcview :
      PPL.Elim.view4 c.2 =
        PPL.Safety.PeacefulProps.born4 := by
    dsimp [c]
    rw [hcreate]
    exact hwview
  let q := PPL.eliminateLeaders c.1 c.2
  have he :=
    PPL.Elim.view4_eliminateLeaders_right
      c.1 c.2
  have hqview :
      PPL.Elim.view4 q.2 =
        PPL.Safety.PeacefulProps.born4 := by
    calc
      PPL.Elim.view4 q.2 =
          (PPL.Elim.rowE
            (PPL.Elim.view4 c.1)
            (PPL.Elim.view4 c.2)).2 := by
              simpa [q] using he
      _ =
          (PPL.Elim.rowE
            (PPL.Elim.view4 c.1)
            PPL.Safety.PeacefulProps.born4).2 := by
              rw [hcview]
      _ =
          PPL.Safety.PeacefulProps.born4 :=
            rowERightBornStepDist
              (PPL.Elim.view4 c.1)
  have hleader : q.2.leader = true := by
    have hv :=
      congrArg
        (fun z : PPL.Elim.Cell4 => z.leader)
        hqview
    simpa [PPL.Elim.view4,
      PPL.Safety.PeacefulProps.born4]
      using hv
  have hdef : PPL.ppl hpsi l r = q := by
    rfl
  rw [hdef]
  exact hleader


theorem lemma16DistForcingCappedStep :
    Lemma16DistForcingCappedStepSpec := by
  unfold Lemma16DistForcingCappedStepSpec
  intro n psi kappa hn3 hpsi ring C e hready
  let D : Config n psi kappa :=
    PopulationProtocol.step
      (PPL.protocol psi kappa) ring C e
  change
    And
      (Or (PPL.CPB ring D)
        (And
          (DetectReadyCapped ring D)
          (∀ i : Fin n,
            (D i).dist = (C i).dist)))
      ((C (ring.rightNeighbor e)).dist.val ≠
          ((C e).dist.val + 1) % (2 * psi) →
        PPL.CPB ring D)
  have hpeaceC : AllLivePeaceful ring C :=
    hready.1.1
  have hleaderC :
      ∀ i : Fin n, (C i).leader = false :=
    hready.1.2.1
  have hsignalC :
      ∀ i : Fin n, (C i).signalR.val = 0 :=
    signalFreePointwise C hready.1.2.2.1
  have hmodeC :
      ∀ i : Fin n, (C i).mode = true :=
    allDetectPointwise C hready.1.2.2.2
  have hclockC :
      ∀ i : Fin n, (C i).clock.val = kappa :=
    hready.2
  have hpeaceD : AllLivePeaceful ring D := by
    simpa [D] using
      allLivePeaceful_step_closed
        hn3 hpsi ring C e hpeaceC
  have hframe0 :=
    stepCappedFrame
      hn3 hpsi ring C e
      hleaderC hmodeC hsignalC hclockC
  have hframe :
      And
        (∀ i : Fin n,
          (D i).dist = (C i).dist)
        (And
          (∀ i : Fin n,
            (D i).mode = (C i).mode)
          (And
            (∀ i : Fin n,
              (D i).clock = (C i).clock)
            (∀ i : Fin n,
              (D i).signalR = (C i).signalR))) := by
    simpa [D] using hframe0
  have hmodeD :
      ∀ i : Fin n, (D i).mode = true := by
    intro i
    calc
      (D i).mode = (C i).mode :=
        hframe.2.1 i
      _ = true := hmodeC i
  have hsignalD :
      ∀ i : Fin n, (D i).signalR.val = 0 := by
    intro i
    calc
      (D i).signalR.val = (C i).signalR.val :=
        congrArg Fin.val (hframe.2.2.2 i)
      _ = 0 := hsignalC i
  have hclockD :
      ∀ i : Fin n, (D i).clock.val = kappa := by
    intro i
    calc
      (D i).clock.val = (C i).clock.val :=
        congrArg Fin.val (hframe.2.2.1 i)
      _ = kappa := hclockC i
  have hfreeD :
      PPL.Modes.Lemma6.signalFreeB D = true :=
    signalFreeOfPointwise D hsignalD
  have hdetectD :
      PPL.Modes.Lemma6.allDetectB D = true :=
    allDetectOfPointwise D hmodeD
  have hfirst :
      Or (PPL.CPB ring D)
        (And
          (DetectReadyCapped ring D)
          (∀ i : Fin n,
            (D i).dist = (C i).dist)) := by
    by_cases hleaderD :
        ∃ i : Fin n, (D i).leader = true
    · exact
        Or.inl
          (cpb_of_allLivePeaceful_hasLeader
            ring D hpeaceD hleaderD)
    · have hleaderlessD :
          ∀ i : Fin n, (D i).leader = false := by
        intro i
        cases hi : (D i).leader with
        | false =>
            rfl
        | true =>
            exact False.elim
              (hleaderD ⟨i, hi⟩)
      have hdetectReadyD :
          DetectReady ring D :=
        And.intro hpeaceD
          (And.intro hleaderlessD
            (And.intro hfreeD hdetectD))
      have hcappedD :
          DetectReadyCapped ring D :=
        And.intro hdetectReadyD hclockD
      exact
        Or.inr
          (And.intro hcappedD hframe.1)
  have hbadBirth :
      (C (ring.rightNeighbor e)).dist.val ≠
          ((C e).dist.val + 1) % (2 * psi) →
        PPL.CPB ring D := by
    intro hbad
    let j := ring.rightNeighbor e
    have hguard :
        PPL.createLeaderLine6Guard
          hpsi (C e) (C j) := by
      apply
        line6GuardOfBad
          hpsi (C e) (C j)
          (hleaderC e)
          (hleaderC j)
          (hsignalC e)
          (hsignalC j)
          (hclockC e)
          (hclockC j)
      simpa [j] using hbad
    have hlocal :
        (PPL.ppl hpsi (C e) (C j)).2.leader =
          true :=
      pplResponderLeaderOfLine6Guard
        hpsi (C e) (C j) hguard
    have hne : j ≠ e := by
      dsimp [j]
      exact
        rightNeighborNeSelfStepDist
          ring (by omega) e
    have hDj : (D j).leader = true := by
      simpa [D, j, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne]
        using hlocal
    exact
      cpb_of_allLivePeaceful_hasLeader
        ring D hpeaceD ⟨j, hDj⟩
  exact And.intro hfirst hbadBirth


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16DistForcingCappedStep
