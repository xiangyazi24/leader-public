import Leader.PPL.ReachCPB.ForcingCapped
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Modes.SignalLineageLocal
import Leader.PPL.Modes.ClockSuffixBridge


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Lemma 16 capped Detect persistence: one literal interaction


The capped statement is true.  The repair below deliberately avoids every
private Transition.lean declaration.  DetermineMode facts are proved only by
unfolding the public caller and splitting its literal branches.
-/


/-! ## Boolean all-agent helpers -/


private def detectFoldlAndFalse
    (xs : List Bool) :
    xs.foldl (fun a b => a && b) false = false := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons]
      cases b <;> simpa using ih


private def detectFoldlAndTrueAllTrue
    (xs : List Bool)
    (h :
      xs.foldl (fun a b => a && b) true = true) :
    forall b, b ∈ xs -> b = true := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht :
              xs.foldl (fun u v => u && v) false = false :=
            detectFoldlAndFalse xs
          have hf : False := by
            rw [List.foldl_cons, ha] at h
            simp only [Bool.true_and] at h
            rw [ht] at h
            cases h
          exact hf.elim
      | true =>
          have ht :
              xs.foldl (fun u v => u && v) true = true := by
            simpa [List.foldl_cons, ha] using h
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            rfl
          · exact ih ht b hb


private def detectFoldlAndTrueOfAllTrue
    (xs : List Bool)
    (h : forall b, b ∈ xs -> b = true) :
    xs.foldl (fun a b => a && b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      have ha : a = true :=
        h a (by simp)
      have ht :
          forall b, b ∈ xs -> b = true := by
        intro b hb
        exact h b (by simp [hb])
      simpa [List.foldl_cons, ha] using ih ht


theorem detectStep_signalFree_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      PPL.Modes.Lemma6.signalFreeB C = true)
    (i : Fin n) :
    (C i).signalR.val = 0 := by
  unfold PPL.Modes.Lemma6.signalFreeB
    PPL.Modes.Lemma6.allAgentsB at h
  have hall :=
    detectFoldlAndTrueAllTrue
      (List.ofFn
        (fun j : Fin n =>
          decide ((C j).signalR.val = 0)))
      h
  have hm :
      decide ((C i).signalR.val = 0) ∈
        List.ofFn
          (fun j : Fin n =>
            decide ((C j).signalR.val = 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  exact of_decide_eq_true (hall _ hm)


theorem detectStep_signalFree_of_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      forall i : Fin n,
        (C i).signalR.val = 0) :
    PPL.Modes.Lemma6.signalFreeB C = true := by
  unfold PPL.Modes.Lemma6.signalFreeB
    PPL.Modes.Lemma6.allAgentsB
  apply detectFoldlAndTrueOfAllTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  simp [h i]


theorem detectStep_allDetect_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      PPL.Modes.Lemma6.allDetectB C = true)
    (i : Fin n) :
    (C i).mode = true := by
  unfold PPL.Modes.Lemma6.allDetectB
    PPL.Modes.Lemma6.allAgentsB at h
  have hall :=
    detectFoldlAndTrueAllTrue
      (List.ofFn
        (fun j : Fin n =>
          decide ((C j).mode = true)))
      h
  have hm :
      decide ((C i).mode = true) ∈
        List.ofFn
          (fun j : Fin n =>
            decide ((C j).mode = true)) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  exact of_decide_eq_true (hall _ hm)


theorem detectStep_allDetect_of_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      forall i : Fin n,
        (C i).mode = true) :
    PPL.Modes.Lemma6.allDetectB C = true := by
  unfold PPL.Modes.Lemma6.allDetectB
    PPL.Modes.Lemma6.allAgentsB
  apply detectFoldlAndTrueOfAllTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  simp [h i]


/-! ## DetermineMode at the cap -/


theorem detectStep_determineMode_capped
    {psi kappa : Nat}
    (_hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (hleader : l.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let d := PPL.determineMode l r
    And (d.1.clock.val = kappa)
      (And (d.2.clock.val = kappa)
        (And (d.1.mode = true)
          (And (d.2.mode = true)
            (And (d.1.signalR.val = 0)
              (d.2.signalR.val = 0))))) := by
  have hls0 :
      l.signalR = (0 : Fin (kappa + 1)) := by
    apply Fin.ext
    simpa using hlsignal
  have hrs0 :
      r.signalR = (0 : Fin (kappa + 1)) := by
    apply Fin.ext
    simpa using hrsignal
  have hcap :
      Nat.min (r.clock.val + 1) kappa = kappa := by
    rw [hrclock]
    exact Nat.min_eq_right (Nat.le_succ kappa)
  by_cases hhit :
      Nat.min (r.hits.val + 1) psi = psi
  · simp only [PPL.determineMode, hleader]
    unfoldFinishModes
    simp [hls0, hrs0, hhit, hcap, hlclock, hrclock] <;>
      omega
  · simp only [PPL.determineMode, hleader]
    unfoldFinishModes
    simp [hls0, hrs0, hhit, hcap, hlclock, hrclock] <;>
      omega


/-! ## Dist is frozen once the responder is Detect -/


private def detectStepDetermineModeDist
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    And (d.1.dist = l.dist)
      (d.2.dist = r.dist) := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact And.intro rfl rfl


theorem detectStep_moveToken_dist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
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


private def detectStepLine6DistMode
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s :=
      PPL.createLeaderThroughLine6 hpsi l r
    And (s.left.dist = d.1.dist)
      (And (s.right.dist = d.2.dist)
        (s.right.mode = d.2.mode)) := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · exact
      And.intro rfl
        (And.intro rfl rfl)
  · exact
      And.intro rfl
        (And.intro rfl rfl)


private def detectStepPreTokenPair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa ×
      PPL.State psi kappa :=
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


private def detectStepPreTokenDist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (hrmode :
      (PPL.determineMode l r).2.mode = true) :
    let p := detectStepPreTokenPair hpsi l r
    And (p.1.dist = l.dist)
      (p.2.dist = r.dist) := by
  have hd :=
    detectStepDetermineModeDist l r
  have hs :=
    detectStepLine6DistMode hpsi l r
  dsimp only at hd hs
  have hsmode :
      (PPL.createLeaderThroughLine6
        hpsi l r).right.mode = true :=
    hs.2.2.trans hrmode
  have hnot :
      (PPL.createLeaderThroughLine6
        hpsi l r).right.mode ≠ false := by
    simp [hsmode]
  have hp :
      let s :=
        PPL.createLeaderThroughLine6 hpsi l r
      let p :=
        detectStepPreTokenPair hpsi l r
      And (p.1.dist = s.left.dist)
        (p.2.dist = s.right.dist) := by
    dsimp only [detectStepPreTokenPair]
    rw [if_neg hnot]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact And.intro rfl rfl
  dsimp only at hp
  exact
    And.intro
      (hp.1.trans (hs.1.trans hd.1))
      (hp.2.trans
        (hs.2.1.trans hd.2))


private def detectStepCreateLeaderDist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (hrmode :
      (PPL.determineMode l r).2.mode = true) :
    let q := PPL.createLeader hpsi l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  let p :=
    detectStepPreTokenPair hpsi l r
  let b :=
    PPL.moveToken hpsi .black p.1 p.2
  let w :=
    PPL.moveToken hpsi .white b.1 b.2
  have hdef :
      PPL.createLeader hpsi l r = w := by
    rfl
  have hp :=
    detectStepPreTokenDist
      hpsi l r hrmode
  have hb :=
    detectStep_moveToken_dist
      hpsi PPL.TokenKind.black p.1 p.2
  have hw :=
    detectStep_moveToken_dist
      hpsi PPL.TokenKind.white b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact
    And.intro
      (hw.1.trans (hb.1.trans hp.1))
      (hw.2.trans (hb.2.trans hp.2))


private def detectStepEliminateDist
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
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
      (congrArg
        (fun z :
          PPL.Elim.OtherFields psi kappa =>
            z.dist) hr)


private def detectStepPplDist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (hrmode :
      (PPL.determineMode l r).2.mode = true) :
    let q := PPL.ppl hpsi l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  let c :=
    PPL.createLeader hpsi l r
  let q :=
    PPL.eliminateLeaders c.1 c.2
  have hc :=
    detectStepCreateLeaderDist
      hpsi l r hrmode
  have he :=
    detectStepEliminateDist c.1 c.2
  have hdef :
      PPL.ppl hpsi l r = q := by
    rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact
    And.intro
      (he.1.trans hc.1)
      (he.2.trans hc.2)


/-! ## Full pair certificate -/


theorem detectStep_ppl_capped_fields
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (hleader : l.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let q := PPL.ppl hpsi l r
    And (q.1.clock.val = kappa)
      (And (q.2.clock.val = kappa)
        (And (q.1.mode = true)
          (And (q.2.mode = true)
            (And (q.1.signalR.val = 0)
              (And (q.2.signalR.val = 0)
                (And (q.1.dist = l.dist)
                  (q.2.dist = r.dist))))))) := by
  have hd :=
    detectStep_determineMode_capped
      hpsi l r hleader
      hlsignal hrsignal
      hlclock hrclock
  dsimp only at hd
  have hc :=
    PPL.Probability.clockSuffixPairProjection
      hpsi l r
  have hm :=
    PPL.Convergence.ConstructCoupling.postDetermineModeModeStable
      hpsi l r
  have hs :=
    PPL.Modes.SignalLineage.postDetermineModeSignalStable
      hpsi l r
  dsimp only at hc hm hs
  have hdist :=
    detectStepPplDist
      hpsi l r hd.2.2.2.1
  dsimp only at hdist
  exact
    And.intro
      ((congrArg Fin.val hc.1).trans
        hd.1)
      (And.intro
        ((congrArg Fin.val hc.2.2.1).trans
          hd.2.1)
        (And.intro
          (hm.1.trans hd.2.2.1)
          (And.intro
            (hm.2.trans hd.2.2.2.1)
            (And.intro
              ((congrArg Fin.val hs.1).trans
                hd.2.2.2.2.1)
              (And.intro
                ((congrArg Fin.val
                  hs.2.2.1).trans
                    hd.2.2.2.2.2)
                (And.intro
                  hdist.1
                  hdist.2))))))


/-! ## Configuration-level assembly -/


private def detectStepRightNeighborNeSelf
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


theorem lemma16DetectPersistenceCappedStepSpec_proved :
    Lemma16DetectPersistenceCappedStepSpec := by
  unfold Lemma16DetectPersistenceCappedStepSpec
  intro n psi kappa hn3 hpsi ring C e hready


  let D : Config n psi kappa :=
    PopulationProtocol.step
      (PPL.protocol psi kappa) ring C e


  change
    Or (PPL.CPB ring D)
      (And
        (DetectReadyCapped ring D)
        (forall i : Fin n,
          (D i).dist = (C i).dist))


  unfold DetectReadyCapped at hready
  rcases hready with
    ⟨hdetect, hcap⟩
  unfold DetectReady at hdetect
  rcases hdetect with
    ⟨hpeace, hleaderless,
      hsignalFree, hallDetect⟩


  have hlsignal :
      (C e).signalR.val = 0 :=
    detectStep_signalFree_at
      C hsignalFree e
  have hrsignal :
      (C (ring.rightNeighbor e)).signalR.val = 0 :=
    detectStep_signalFree_at
      C hsignalFree
      (ring.rightNeighbor e)


  have hpair :=
    detectStep_ppl_capped_fields
      hpsi
      (C e)
      (C (ring.rightNeighbor e))
      (hleaderless e)
      hlsignal hrsignal
      (hcap e)
      (hcap (ring.rightNeighbor e))


  dsimp only at hpair
  rcases hpair with
    ⟨hclockL, hclockR,
      hmodeL, hmodeR,
      hsignalL, hsignalR,
      hdistL, hdistR⟩


  have hne :
      ring.rightNeighbor e ≠ e :=
    detectStepRightNeighborNeSelf
      hn3 ring e


  have htrans :
      PPL.transition psi kappa
          (C e) (C (ring.rightNeighbor e)) =
        PPL.ppl hpsi
          (C e) (C (ring.rightNeighbor e)) :=
    PPL.transition_eq_ppl
      hpsi
      (C e) (C (ring.rightNeighbor e))


  have hDleft :
      D e =
        (PPL.ppl hpsi
          (C e)
          (C (ring.rightNeighbor e))).1 := by
    have hleft :=
      congrArg Prod.fst htrans
    simpa [D, PopulationProtocol.step,
      PPL.protocol] using hleft


  have hDright :
      D (ring.rightNeighbor e) =
        (PPL.ppl hpsi
          (C e)
          (C (ring.rightNeighbor e))).2 := by
    have hright :=
      congrArg Prod.snd htrans
    simpa [D, PopulationProtocol.step,
      PPL.protocol, hne] using hright


  have houtside :
      forall i : Fin n,
        i ≠ e ->
        i ≠ ring.rightNeighbor e ->
        D i = C i := by
    intro i hie hir
    simpa [D, PopulationProtocol.step,
      hie, hir]


  have hclockD :
      forall i : Fin n,
        (D i).clock.val = kappa := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hclockL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hclockR
      · rw [houtside i hie hir]
        exact hcap i


  have hsignalD :
      forall i : Fin n,
        (D i).signalR.val = 0 := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hsignalL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hsignalR
      · rw [houtside i hie hir]
        exact
          detectStep_signalFree_at
            C hsignalFree i


  have hmodeD :
      forall i : Fin n,
        (D i).mode = true := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hmodeL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hmodeR
      · rw [houtside i hie hir]
        exact
          detectStep_allDetect_at
            C hallDetect i


  have hdistD :
      forall i : Fin n,
        (D i).dist = (C i).dist := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hdistL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hdistR
      · exact
          congrArg
            (fun q : PPL.State psi kappa =>
              q.dist)
            (houtside i hie hir)


  have hpeaceD :
      AllLivePeaceful ring D := by
    simpa [D] using
      allLivePeaceful_step_closed
        hn3 hpsi ring C e hpeace


  by_cases hleaderD :
      Exists fun i : Fin n =>
        (D i).leader = true
  · exact
      Or.inl
        (cpb_of_allLivePeaceful_hasLeader
          ring D hpeaceD hleaderD)
  · have hleaderlessD :
        forall i : Fin n,
          (D i).leader = false := by
      intro i
      cases hi : (D i).leader with
      | false =>
          rfl
      | true =>
          exact
            False.elim
              (hleaderD ⟨i, hi⟩)


    have hsignalFreeD :
        PPL.Modes.Lemma6.signalFreeB D = true :=
      detectStep_signalFree_of_at
        D hsignalD


    have hallDetectD :
        PPL.Modes.Lemma6.allDetectB D = true :=
      detectStep_allDetect_of_at
        D hmodeD


    have hreadyD :
        DetectReadyCapped ring D := by
      unfold DetectReadyCapped
      refine And.intro ?_ hclockD
      unfold DetectReady
      exact
        And.intro hpeaceD
          (And.intro hleaderlessD
            (And.intro
              hsignalFreeD
              hallDetectD))


    exact
      Or.inr
        (And.intro hreadyD hdistD)


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.detectStep_signalFree_at
#print axioms PPL.Convergence.ReachCPB.detectStep_signalFree_of_at
#print axioms PPL.Convergence.ReachCPB.detectStep_allDetect_at
#print axioms PPL.Convergence.ReachCPB.detectStep_allDetect_of_at
#print axioms PPL.Convergence.ReachCPB.detectStep_determineMode_capped
#print axioms PPL.Convergence.ReachCPB.detectStep_moveToken_dist
#print axioms PPL.Convergence.ReachCPB.detectStep_ppl_capped_fields
#print axioms PPL.Convergence.ReachCPB.lemma16DetectPersistenceCappedStepSpec_proved
