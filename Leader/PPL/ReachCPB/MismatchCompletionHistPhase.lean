-- Leader/PPL/ReachCPB/MismatchCompletionHistPhase.lean
import Leader.PPL.ReachCPB.MismatchCompletionHist


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


private theorem q19699_rightNeighbor_leftNeighbor
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor x) = x := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hx : x.val = 0
  · rw [hx]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by
      omega
    rw [hs, Nat.mod_self]
  · have heq : x.val + n - 1 = n + (x.val - 1) := by
      omega
    have hlt : x.val - 1 < n := by
      omega
    have hleft :
        (x.val + n - 1) % n = x.val - 1 := by
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs : x.val - 1 + 1 = x.val := by
      omega
    rw [hs, Nat.mod_eq_of_lt x.isLt]


private theorem q19699_shiftRight_zero
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftRight ring x 0 = x := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt x.isLt]


private theorem q19699_shiftRight_add
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring x a) b =
      PPL.shiftRight ring x (a + b) := by
  apply Fin.ext
  change (((x.val + a) % n + b) % n) =
    (x.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem q19699_shiftRight_one
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftRight ring x 1 = ring.rightNeighbor x := by
  rfl


private theorem q19699_shiftLeft_one
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftLeft ring x 1 = ring.leftNeighbor x := by
  apply Fin.ext
  simp only [PPL.shiftLeft, DirectedRing.leftNeighbor]
  by_cases hn1 : n = 1
  · subst n
    simp
  · have hn2 : 1 < n := by
      have hx := x.isLt
      omega
    rw [Nat.mod_eq_of_lt hn2]


private theorem q19699_shiftRight_succ
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (d : Nat) :
    PPL.shiftRight ring x (d + 1) =
      ring.rightNeighbor (PPL.shiftRight ring x d) := by
  calc
    PPL.shiftRight ring x (d + 1) =
        PPL.shiftRight ring (PPL.shiftRight ring x d) 1 :=
      (q19699_shiftRight_add ring x d 1).symm
    _ = ring.rightNeighbor (PPL.shiftRight ring x d) :=
      q19699_shiftRight_one ring (PPL.shiftRight ring x d)


private theorem q19699_shiftLeft_n
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftLeft ring x n = x := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.mod_eq_of_lt x.isLt]


private theorem q19699_scanDistance_some_hit
    {n : Nat}
    (site : Nat -> Fin n)
    (hit : Fin n -> Bool) :
    forall fuel d r,
      PPL.scanDistance site hit fuel d = some r ->
      hit (site r) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro d r h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro d r h
      cases hh : hit (site d) with
      | false =>
          have ht :
              PPL.scanDistance site hit fuel (d + 1) =
                some r := by
            simpa [PPL.scanDistance, hh] using h
          exact ih (d + 1) r ht
      | true =>
          have hdr : d = r := by
            simpa [PPL.scanDistance, hh] using h
          subst r
          exact hh


private theorem q19699_prevBorder_isBorder
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b : Fin n)
    (hb : PPL.IsBorder C b) :
    PPL.IsBorder C
      (PPL.shiftLeft ring b
        (PPL.prevBorderDistance ring C b)) := by
  cases hs :
      PPL.scanDistance
        (fun d => PPL.shiftLeft ring b d)
        (PPL.isBorderBool C) n 1 with
  | none =>
      have hdp :
          PPL.prevBorderDistance ring C b = n := by
        simp [PPL.prevBorderDistance, hs]
      rw [hdp, q19699_shiftLeft_n]
      exact hb
  | some d =>
      have hdp :
          PPL.prevBorderDistance ring C b = d := by
        simp [PPL.prevBorderDistance, hs]
      have hhit :=
        q19699_scanDistance_some_hit
          (fun q => PPL.shiftLeft ring b q)
          (PPL.isBorderBool C)
          n 1 d hs
      rw [hdp]
      unfold PPL.IsBorder
      simpa [PPL.isBorderBool] using hhit


private theorem q19699_dist_shiftRight
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hdist :
      forall i : Fin n,
        (C (ring.rightNeighbor i)).dist.val =
          ((C i).dist.val + 1) % (2 * psi))
    (k : Fin n) :
    forall d : Nat,
      (C (PPL.shiftRight ring k d)).dist.val =
        ((C k).dist.val + d) % (2 * psi) := by
  intro d
  induction d with
  | zero =>
      rw [q19699_shiftRight_zero]
      simpa using
        (Nat.mod_eq_of_lt (C k).dist.isLt).symm
  | succ d ih =>
      rw [q19699_shiftRight_succ]
      calc
        (C
            (ring.rightNeighbor
              (PPL.shiftRight ring k d))).dist.val =
            ((C (PPL.shiftRight ring k d)).dist.val + 1) %
              (2 * psi) :=
          hdist (PPL.shiftRight ring k d)
        _ =
            ((((C k).dist.val + d) % (2 * psi)) + 1) %
              (2 * psi) := by
          rw [ih]
        _ =
            ((C k).dist.val + d + 1) % (2 * psi) := by
          rw [Nat.mod_add_mod]
        _ =
            ((C k).dist.val + (d + 1)) % (2 * psi) := by
          congr 1


private theorem q19699_badBorderWitness_exists
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hready : LastReadyCapped ring C)
    (hnot : ¬ PPL.Perfect ring C) :
    exists b : Fin n, exists k : Fin n,
      exists kind : PPL.TokenKind,
        Lemma16BadBorderWitness ring C b k kind := by
  rcases hready with ⟨hdistReady, hlast⟩
  rcases hdistReady with ⟨hdetectCapped, hdist⟩
  rcases hdetectCapped with ⟨hdetect, _hclock⟩
  rcases hdetect with
    ⟨_hpeace, hleaderless, _hsignal, _hallDetect⟩


  have hEq1 :
      forall i : Fin n,
        (C i).dist.val =
          if (C i).leader = true then 0
          else
            ((C (PPL.shiftLeft ring i 1)).dist.val + 1) %
              (2 * psi) := by
    intro i
    have hp := hdist (ring.leftNeighbor i)
    rw [q19699_rightNeighbor_leftNeighbor ring i] at hp
    rw [q19699_shiftLeft_one ring i]
    simpa [hleaderless i] using hp


  let goodBorder : Fin n -> Prop :=
    fun i =>
      let dn := PPL.nextBorderDistance ring C i
      let dp := PPL.prevBorderDistance ring C i
      let nxt := PPL.shiftRight ring i dn
      let prv := PPL.shiftLeft ring i dp
      Or
        ((C i).leader = true)
        (Or
          ((C nxt).leader = true)
          (PPL.segmentIdFrom ring C i dn =
            (PPL.segmentIdFrom ring C prv dp + 1) %
              (2 ^ psi)))


  have hnot2 :
      ¬ (forall i : Fin n,
          PPL.IsBorder C i ->
            goodBorder i) := by
    intro h2
    apply hnot
    refine And.intro hEq1 ?_
    intro i hi
    simpa [goodBorder] using h2 i hi


  obtain ⟨b, hb⟩ :=
    Classical.not_forall.mp hnot2


  have hborder : PPL.IsBorder C b := by
    by_cases h : PPL.IsBorder C b
    · exact h
    · have himp :
          PPL.IsBorder C b -> goodBorder b := by
        intro hb0
        exact False.elim (h hb0)
      exact False.elim (hb himp)


  have hqnot : ¬ goodBorder b := by
    intro hq
    exact hb (fun _ => hq)


  let dn := PPL.nextBorderDistance ring C b
  let dp := PPL.prevBorderDistance ring C b
  let prv := PPL.shiftLeft ring b dp


  have hseg :
      PPL.segmentIdFrom ring C b dn ≠
        (PPL.segmentIdFrom ring C prv dp + 1) %
          (2 ^ psi) := by
    intro heq
    apply hqnot
    dsimp [goodBorder, dn, dp, prv]
    exact Or.inr (Or.inr heq)


  have hkBorder : PPL.IsBorder C prv := by
    simpa [prv, dp] using
      q19699_prevBorder_isBorder ring C b hborder


  have hformula :=
    q19699_dist_shiftRight ring C hdist prv


  unfold PPL.IsBorder at hkBorder
  rcases hkBorder with hk0 | hkpsi
  · have hCd : PPL.Cd ring prv .black C := by
      unfold PPL.Cd
      intro x
      dsimp only
      refine And.intro ?_ (hlast _)
      calc
        (C (PPL.shiftRight ring prv x.val)).dist.val =
            ((C prv).dist.val + x.val) % (2 * psi) :=
          hformula x.val
        _ =
            (x.val + PPL.tokenD' psi PPL.TokenKind.black) %
              (2 * psi) := by
          rw [hk0]
          simp [PPL.tokenD']
    refine ⟨b, prv, .black, ?_⟩
    unfold Lemma16BadBorderWitness
    refine
      And.intro hborder
        (And.intro ?_
          (And.intro hCd ?_))
    · rfl
    · simpa [dn, dp, prv] using hseg
  · have hCd : PPL.Cd ring prv .white C := by
      unfold PPL.Cd
      intro x
      dsimp only
      refine And.intro ?_ (hlast _)
      calc
        (C (PPL.shiftRight ring prv x.val)).dist.val =
            ((C prv).dist.val + x.val) % (2 * psi) :=
          hformula x.val
        _ =
            (x.val + PPL.tokenD' psi PPL.TokenKind.white) %
              (2 * psi) := by
          rw [hkpsi]
          simp [PPL.tokenD', Nat.add_comm]
    refine ⟨b, prv, .white, ?_⟩
    unfold Lemma16BadBorderWitness
    refine
      And.intro hborder
        (And.intro ?_
          (And.intro hCd ?_))
    · rfl
    · simpa [dn, dp, prv] using hseg


private theorem q19699_ghostRun_append
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (t : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (a b : DetSchedule n) :
    PPL.ghostRun hpsi ring t G (a ++ b) =
      PPL.ghostRun hpsi ring (t + a.length)
        (PPL.ghostRun hpsi ring t G a) b := by
  induction a generalizing t G with
  | nil =>
      rfl
  | cons e es ih =>
      simp only [List.cons_append,
        PPL.ghostRun, List.length_cons]
      rw [ih]
      congr 1
      omega


private theorem q19699_ghostRun_phys_eq_runPPL
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (t : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (word : DetSchedule n) :
    (PPL.ghostRun hpsi ring t G word).phys =
      PPL.Probability.runPPL ring G.phys word := by
  have h :=
    PPL.ghostRun_erases hpsi ring t G word
  simpa [PPL.eraseGhost,
    PPL.Probability.runPPL] using h


private theorem q19699_mismatch_suffix_invariant_hist
    (hProducer : Lemma16MismatchLineageHistoryProducer)
    (hStep : Lemma16MismatchCompletionStepSpecHist)
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hstart : LastReadyCapped ring C0) :
    forall
      (pre : DetSchedule n)
      (G : PPL.GhostConfig n psi kappa)
      (rest : DetSchedule n),
      G =
          PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0) pre ->
      LastReadyCapped ring G.phys ->
      Lemma16BadBorderWitness
        ring G.phys b k kind ->
      let F :=
        PPL.ghostRun hpsi ring pre.length G rest
      Or
        (PPL.CPB ring F.phys)
        (And
          (LastReadyCapped ring F.phys)
          (And
            (Lemma16BadBorderWitness
              ring F.phys b k kind)
            (forall m : PPL.LineageMeta n,
              m ∈ F.completed ->
              PPL.FreshCompletion
                (psi := psi) kind k m ->
              m ∈ G.completed))) := by
  intro pre G rest
  induction rest generalizing pre G with
  | nil =>
      intro _hcanon hready hbad
      dsimp only
      simp only [PPL.ghostRun]
      exact
        Or.inr
          (And.intro hready
            (And.intro hbad
              (fun _ hm _ => hm)))
  | cons e rest ih =>
      intro hcanon hready hbad
      subst G


      have hhistory :
          Lemma16MismatchLineageHistory
            hpsi ring C0 pre k kind :=
        hProducer hpsi ring C0 pre k kind hstart


      have hs :=
        hStep hpsi hn3 ring C0 pre
          b k kind e hhistory hready hbad
      dsimp only at hs


      rcases hs with hcpb1 | hkeep1
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring
            (PPL.ghostStep hpsi ring pre.length
              (PPL.ghostRun hpsi ring 0
                (PPL.initialGhost C0) pre) e).phys
            rest hcpb1
        have hphys :=
          q19699_ghostRun_phys_eq_runPPL
            hpsi ring (pre.length + 1)
            (PPL.ghostStep hpsi ring pre.length
              (PPL.ghostRun hpsi ring 0
                (PPL.initialGhost C0) pre) e)
            rest
        dsimp only
        refine Or.inl ?_
        change
          PPL.CPB ring
            (PPL.ghostRun hpsi ring
              (pre.length + 1)
              (PPL.ghostStep hpsi ring pre.length
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C0) pre) e)
              rest).phys
        rw [hphys]
        exact hend
      · have hready1 := hkeep1.1
        have hbad1 := hkeep1.2.1
        have hnoNew := hkeep1.2.2


        have happ :=
          q19699_ghostRun_append
            hpsi ring 0
            (PPL.initialGhost C0) pre [e]


        have hcanon1 :
            PPL.ghostStep hpsi ring pre.length
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C0) pre) e =
              PPL.ghostRun hpsi ring 0
                (PPL.initialGhost C0)
                (pre ++ [e]) := by
          symm
          simpa [PPL.ghostRun] using happ


        have ht :=
          ih
            (pre := pre ++ [e])
            (G :=
              PPL.ghostStep hpsi ring pre.length
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C0) pre) e)
            hcanon1 hready1 hbad1


        dsimp only at ht
        have hlen :
            (pre ++ [e]).length =
              pre.length + 1 := by
          simp


        dsimp only
        rcases ht with hcpbTail | hkeepTail
        · refine Or.inl ?_
          change
            PPL.CPB ring
              (PPL.ghostRun hpsi ring
                (pre.length + 1)
                (PPL.ghostStep hpsi ring pre.length
                  (PPL.ghostRun hpsi ring 0
                    (PPL.initialGhost C0) pre) e)
                rest).phys
          simpa [hlen] using hcpbTail
        · refine
            Or.inr
              (And.intro ?_
                (And.intro ?_ ?_))
          · change
              LastReadyCapped ring
                (PPL.ghostRun hpsi ring
                  (pre.length + 1)
                  (PPL.ghostStep hpsi ring pre.length
                    (PPL.ghostRun hpsi ring 0
                      (PPL.initialGhost C0) pre) e)
                  rest).phys
            simpa [hlen] using hkeepTail.1
          · change
              Lemma16BadBorderWitness ring
                (PPL.ghostRun hpsi ring
                  (pre.length + 1)
                  (PPL.ghostStep hpsi ring pre.length
                    (PPL.ghostRun hpsi ring 0
                      (PPL.initialGhost C0) pre) e)
                  rest).phys
                b k kind
            simpa [hlen] using hkeepTail.2.1
          · intro m hm hfresh
            have hm' :
                m ∈
                  (PPL.ghostRun hpsi ring
                    (pre ++ [e]).length
                    (PPL.ghostStep hpsi ring pre.length
                      (PPL.ghostRun hpsi ring 0
                        (PPL.initialGhost C0) pre) e)
                    rest).completed := by
              change
                m ∈
                  (PPL.ghostRun hpsi ring
                    (pre.length + 1)
                    (PPL.ghostStep hpsi ring pre.length
                      (PPL.ghostRun hpsi ring 0
                        (PPL.initialGhost C0) pre) e)
                    rest).completed at hm
              simpa [hlen] using hm
            have hmem1 :=
              hkeepTail.2.2 m hm' hfresh
            exact hnoNew m hmem1 hfresh


theorem lemma16MismatchCompletionHistToWitness_proved :
    Lemma16MismatchCompletionHistToWitness := by
  unfold Lemma16MismatchCompletionHistToWitness
  intro hProducer hStep
  unfold Lemma16MismatchWitnessCappedSpec
  intro n psi kappa
  intro hn3 hpsi hnpow
  intro ring C
  intro hready hnot


  obtain ⟨b, k, kind, hbad⟩ :=
    q19699_badBorderWitness_exists
      hpsi ring C hready hnot


  refine
    ⟨k, kind,
      And.intro hbad.2.2.1 ?_⟩


  intro schedule hcompletion


  have hr :=
    q19699_mismatch_suffix_invariant_hist
      hProducer hStep
      hpsi hn3 ring C b k kind hready
      []
      (PPL.initialGhost C)
      schedule
      rfl
      (by
        simpa [PPL.initialGhost] using hready)
      (by
        simpa [PPL.initialGhost] using hbad)


  dsimp only at hr
  simp only [List.length_nil] at hr
  rcases hr with hcpb | hkeep
  · have hphys :=
      q19699_ghostRun_phys_eq_runPPL
        hpsi ring 0
        (PPL.initialGhost C) schedule
    rw [hphys] at hcpb
    simpa [PPL.initialGhost] using hcpb
  · unfold PPL.HasFreshCompletion at hcompletion
    obtain ⟨m, hm, hfresh⟩ := hcompletion
    have hbase :=
      hkeep.2.2 m hm hfresh
    change
      m ∈ ([] : List (PPL.LineageMeta n)) at hbase
    simp at hbase


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionHistToWitness_proved
