import Leader.PPL.ReachCPB.Capped
import Leader.PPL.ReachCPB.Detect


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


/-!
Truth audit at main d92ef7b1.


Both target specifications remain true under the capped hypotheses.  The
remaining literal-transition work is local, not another global repair:


* the mismatch side needs one canonical-ghost single-step fact saying that a
  newly logged fresh completion at the selected bad predecessor border cannot
  occur without CPB; and
* the C_d side needs one pair-row fact saying that, under leaderless successor
  distances and zero last bits, one literal pair interaction preserves dist
  and last.


Everything else below, including extraction of the bad predecessor border,
the schedule induction, and the CdTrace assembly, is proved from the existing
public interfaces.
-/


/-! ## Cyclic geometry helpers -/


private theorem rightNeighbor_ne_self_capped
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (x : Fin n) :
    ring.rightNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : x.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : x.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem rightNeighbor_leftNeighbor_capped
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


private theorem shiftRight_zero_capped
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftRight ring x 0 = x := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt x.isLt]


private theorem shiftRight_add_capped
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring x a) b =
      PPL.shiftRight ring x (a + b) := by
  apply Fin.ext
  change (((x.val + a) % n + b) % n) =
    (x.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem shiftRight_one_capped
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftRight ring x 1 = ring.rightNeighbor x := by
  rfl


private theorem shiftLeft_one_capped
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


private theorem shiftRight_succ_capped
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (d : Nat) :
    PPL.shiftRight ring x (d + 1) =
      ring.rightNeighbor (PPL.shiftRight ring x d) := by
  calc
    PPL.shiftRight ring x (d + 1) =
        PPL.shiftRight ring (PPL.shiftRight ring x d) 1 :=
      (shiftRight_add_capped ring x d 1).symm
    _ = ring.rightNeighbor (PPL.shiftRight ring x d) :=
      shiftRight_one_capped ring (PPL.shiftRight ring x d)


private theorem shiftLeft_n_capped
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    PPL.shiftLeft ring x n = x := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.mod_eq_of_lt x.isLt]


private theorem scanDistance_some_hit_capped
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


private theorem prevBorder_isBorder_capped
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
      rw [hdp, shiftLeft_n_capped]
      exact hb
  | some d =>
      have hdp :
          PPL.prevBorderDistance ring C b = d := by
        simp [PPL.prevBorderDistance, hs]
      have hhit :=
        scanDistance_some_hit_capped
          (fun q => PPL.shiftLeft ring b q)
          (PPL.isBorderBool C)
          n 1 d hs
      rw [hdp]
      unfold PPL.IsBorder
      simpa [PPL.isBorderBool] using hhit


private theorem dist_shiftRight_capped
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
      rw [shiftRight_zero_capped]
      simpa using
        (Nat.mod_eq_of_lt (C k).dist.isLt).symm
  | succ d ih =>
      rw [shiftRight_succ_capped]
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


/-! ## A concrete bad predecessor-border witness -/


/--
The failing Perfect equation-(2) border b, together with its predecessor
border k and the selected colour whose d-coordinate starts at k.
-/
def Lemma16BadBorderWitness
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b k : Fin n)
    (kind : PPL.TokenKind) : Prop :=
  And
    (PPL.IsBorder C b)
    (And
      (k =
        PPL.shiftLeft ring b
          (PPL.prevBorderDistance ring C b))
      (And
        (PPL.Cd ring k kind C)
        (let dn := PPL.nextBorderDistance ring C b
         let dp := PPL.prevBorderDistance ring C b
         PPL.segmentIdFrom ring C b dn ≠
           (PPL.segmentIdFrom ring C k dp + 1) %
             (2 ^ psi))))


private theorem badBorderWitness_exists_capped
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
    rw [rightNeighbor_leftNeighbor_capped ring i] at hp
    rw [shiftLeft_one_capped ring i]
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
      prevBorder_isBorder_capped ring C b hborder


  have hformula :=
    dist_shiftRight_capped ring C hdist prv


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


/-! ## The one remaining mismatch single-interaction row -/


/--
Canonical-ghost completion row.


G is not arbitrary: it is exactly the ghost run from initialGhost along pre.
Starting from a capped bad predecessor pair, one literal next interaction
either reaches CPB, or preserves the capped bad-pair invariant and adds no
new selected fresh completion.  The only load-bearing branch is the final
positive target hit: the fresh payload is the add-one bit, and because the
recorded Perfect equation-(2) pair is bad, some Detect comparison fails and
Algorithm 3 line 20 performs leaderBirth before that fresh completion could
be logged without CPB.
-/
def Lemma16MismatchCompletionStepSpec : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    LastReadyCapped ring G.phys ->
    Lemma16BadBorderWitness ring G.phys b k kind ->
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    Or
      (PPL.CPB ring G'.phys)
      (And
        (LastReadyCapped ring G'.phys)
        (And
          (Lemma16BadBorderWitness
            ring G'.phys b k kind)
          (forall m : PPL.LineageMeta n,
            m ∈ G'.completed ->
            PPL.FreshCompletion
              (psi := psi) kind k m ->
            m ∈ G.completed)))


private theorem ghostRun_append_capped
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


private theorem ghostRun_phys_eq_runPPL_capped
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


private theorem mismatch_suffix_invariant
    (hStep : Lemma16MismatchCompletionStepSpec)
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (b k : Fin n)
    (kind : PPL.TokenKind) :
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

      have hs :=
        hStep hpsi hn3 ring C0 pre
          b k kind e hready hbad
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
          ghostRun_phys_eq_runPPL_capped
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
          ghostRun_append_capped
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


theorem lemma16MismatchWitnessCapped
    (hStep : Lemma16MismatchCompletionStepSpec) :
    Lemma16MismatchWitnessCappedSpec := by
  intro n psi kappa
  intro hn3 hpsi hnpow
  intro ring C
  intro hready hnot


  obtain ⟨b, k, kind, hbad⟩ :=
    badBorderWitness_exists_capped
      hpsi ring C hready hnot


  refine
    ⟨k, kind,
      And.intro hbad.2.2.1 ?_⟩


  intro schedule hcompletion


  have hr :=
    mismatch_suffix_invariant
      hStep hpsi hn3 ring C b k kind
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
      ghostRun_phys_eq_runPPL_capped
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


/-! ## C_d geometry: one literal pair row remains -/


/--
The exact pair-row statement needed by Lemma16CdGeometryStepSpec.


Under a leaderless successor-distance edge with both last bits false, the
full literal Algorithm-1 interaction preserves dist and last on both
endpoints.  DetermineMode does not write either field; Algorithm 2 has
tmp = r.dist, so line 6 cannot fire and line 8 is idempotent; line 9 writes
false; both MoveToken calls preserve these fields; Algorithm 5 also frames
them.
-/
def Lemma16CdGeometryPairStepSpec : Prop :=
  forall {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa),
    l.leader = false ->
    r.leader = false ->
    r.dist.val =
      (l.dist.val + 1) % (2 * psi) ->
    l.last = false ->
    r.last = false ->
    let q := PPL.transition psi kappa l r
    And
      (q.1.dist = l.dist)
      (And
        (q.1.last = l.last)
        (And
          (q.2.dist = r.dist)
          (q.2.last = r.last)))


private theorem pplStep_initiator_capped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    (PopulationProtocol.step
      (PPL.protocol psi kappa) ring C e) e =
      (PPL.transition psi kappa
        (C e) (C (ring.rightNeighbor e))).1 := by
  simp [PopulationProtocol.step, PPL.protocol]


private theorem pplStep_responder_capped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hne : e ≠ ring.rightNeighbor e) :
    (PopulationProtocol.step
      (PPL.protocol psi kappa) ring C e)
        (ring.rightNeighbor e) =
      (PPL.transition psi kappa
        (C e) (C (ring.rightNeighbor e))).2 := by
  have hne' :
      ring.rightNeighbor e ≠ e := by
    exact Ne.symm hne
  simp [PopulationProtocol.step, PPL.protocol,
    hne, hne']


private theorem pplStep_other_capped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    (PopulationProtocol.step
      (PPL.protocol psi kappa) ring C e) i =
      C i := by
  simp [PopulationProtocol.step, hie, hir]


theorem lemma16CdGeometryStep
    (hPair : Lemma16CdGeometryPairStepSpec) :
    Lemma16CdGeometryStepSpec := by
  intro n psi kappa
  intro hn3 hpsi
  intro ring C e
  intro hleader hdist hlast
  intro i
  dsimp only


  have hne :=
    rightNeighbor_ne_self_capped
      hn3 ring e


  have hp :=
    hPair hpsi
      (C e)
      (C (ring.rightNeighbor e))
      (hleader e)
      (hleader (ring.rightNeighbor e))
      (hdist e)
      (hlast e)
      (hlast (ring.rightNeighbor e))
  dsimp only at hp


  by_cases hie : i = e
  · subst i
    rw [pplStep_initiator_capped]
    exact
      And.intro hp.1 hp.2.1
  · by_cases hir :
        i = ring.rightNeighbor e
    · subst i
      rw [pplStep_responder_capped
        ring C e (Ne.symm hne)]
      exact
        And.intro hp.2.2.1 hp.2.2.2
    · rw [pplStep_other_capped
        ring C e i hie hir]
      exact And.intro rfl rfl


theorem lemma16CdTraceUntilSuccess_proved
    (hPair : Lemma16CdGeometryPairStepSpec) :
    Lemma16CdTraceUntilSuccessSpec :=
  lemma16CdTraceUntilSuccess
    (lemma16CdGeometryStep hPair)


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16MismatchWitnessCapped
#print axioms PPL.Convergence.ReachCPB.lemma16CdGeometryStep
#print axioms PPL.Convergence.ReachCPB.lemma16CdTraceUntilSuccess_proved
