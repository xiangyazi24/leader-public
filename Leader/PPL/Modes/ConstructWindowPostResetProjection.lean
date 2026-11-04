import Leader.PPL.Modes.ConstructWindowPostResetClockCount


/-!
# Lemma 5(ii): whole-word projection after clock resets


Truth audit.


The frozen projection is TRUE.  The two controller concerns separate:


* the encounter-cap concern is harmless: the left conjunct of
  lemma5iiPostResetClockBadB is !lemma5iiEncounterBadB, so every fixed agent
  has at most lemma5iiEncounterCap predictable incident letters on the whole
  word; with constant host and stop=false this is exactly the length of
  stoppedEncounterBits;


* a signal reset can indeed destroy literal equality between the physical
  hits field and the whole-word lottery headRun.  Equality is not needed.
  The robust invariant is lexicographic clock credit: either the lottery has
  already banked an extra completed win, or at equal completed-win credit its
  headRun dominates the physical hits counter.  A reset can only lower the
  physical side.  Consequently a later Detect boundary still forces enough
  whole-word lottery wins.


The full wordwise projection and the existing counting theorem are reduced
below to one literal single-interaction fact, Lemma5iiPostResetClockOneStep.
This residual contains no horizon, union bound, counting, reset-prefix
selection, or failure event: it is only the fixed-agent Algorithm-4
clock/hits/mode update against one H/T scheduler letter.
-/


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


private def postResetFixedBits {n : Nat}
    (ring : DirectedRing n) (x : Fin n) :
    DetSchedule n -> List Bool
  | [] => []
  | e :: rest =>
      match incidentBit ring x e with
      | none => postResetFixedBits ring x rest
      | some b => b :: postResetFixedBits ring x rest


def postResetLotteryAdvance {n : Nat}
    (psi : Nat) (ring : DirectedRing n)
    (x e : Fin n) (s : LotteryState) : LotteryState :=
  match incidentBit ring x e with
  | none => s
  | some b => lotteryStep psi s b


/-- Lexicographic domination of the physical timer by the whole-word lottery.


The second conjunct records the only mode coherence needed by the projection:
a Detect bit reached from a C_mid run is backed by a capped physical clock.
-/
def PostResetClockLotteryRel {psi : Nat} (kappa : Nat)
    (base : Nat) (q : PPL.State psi kappa)
    (s : LotteryState) : Prop :=
  And
    (Or
      (q.clock.val < base + s.wins)
      (And
        (q.clock.val = base + s.wins)
        (q.hits.val <= s.headRun)))
    (q.mode = true -> q.clock.val = kappa)


/-- Smallest remaining physical leaf.


It is a single literal interaction for one fixed agent.  Off the selected pair
both sides are unchanged.  On the initiator letter T, DetermineMode clears
hits and cannot increase clock.  On the responder letter H, one completed
physical psi-run either consumes one lottery win or is already paid by strict
lottery credit.  A signal reset lowers the physical clock, so it cannot break
the relation.  The post-DetermineMode suffix preserves clock/hits/mode.
-/
def Lemma5iiPostResetClockOneStep : Prop :=
  forall {n psi kappa : Nat},
    3 <= n ->
    2 <= psi ->
    forall (ring : DirectedRing n)
      (C : Config n psi kappa)
      (x e : Fin n)
      (base : Nat)
      (s : LotteryState),
      PostResetClockLotteryRel kappa base (C x) s ->
        PostResetClockLotteryRel kappa base
          (pplStep ring C e x)
          (postResetLotteryAdvance psi ring x e s)


private theorem postResetStoppedBitsAux_eq_fixed
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    forall (pre word : DetSchedule n),
      stoppedEncounterBitsAux ring
          (fun _ => x) (fun _ => false) pre word =
        postResetFixedBits ring x word := by
  intro pre word
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          simpa [stoppedEncounterBitsAux,
            postResetFixedBits, hb] using
            ih (pre := pre ++ [e])
      | some b =>
          simp [stoppedEncounterBitsAux,
            postResetFixedBits, hb,
            ih (pre := pre ++ [e])]


private theorem postResetStoppedBits_eq_fixed
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (word : DetSchedule n) :
    stoppedEncounterBits ring
        (fun _ => x) (fun _ => false) word =
      postResetFixedBits ring x word := by
  unfold stoppedEncounterBits
  exact postResetStoppedBitsAux_eq_fixed
    ring x [] word


private theorem postResetIncidentLetter_eq_incidentBit_isSome
    {n : Nat} (ring : DirectedRing n)
    (x e : Fin n) :
    incidentLetter ring x e =
      (incidentBit ring x e).isSome := by
  by_cases hH : e = ring.leftNeighbor x
  · simp [incidentLetter, incidentBit,
      twoEdgeLetter, hH]
  · by_cases hT : e = x
    · subst e
      simp [incidentLetter, incidentBit,
        twoEdgeLetter, hH]
    · simp [incidentLetter, incidentBit,
        twoEdgeLetter, hH, hT]


private theorem postResetFixedBits_length_eq_hitsAux
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) :
    forall (pre word : DetSchedule n),
      (postResetFixedBits ring x word).length =
        predictableHostHitsAux ring
          (fun _ => x) pre word := by
  intro pre word
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          have hil : incidentLetter ring x e = false := by
            rw [postResetIncidentLetter_eq_incidentBit_isSome]
            simp [hb]
          simpa [postResetFixedBits,
            predictableHostHitsAux, hb, hil] using
            ih (pre := pre ++ [e])
      | some b =>
          have hil : incidentLetter ring x e = true := by
            rw [postResetIncidentLetter_eq_incidentBit_isSome]
            simp [hb]
          simp [postResetFixedBits,
            predictableHostHitsAux, hb, hil,
            ih (pre := pre ++ [e]), Nat.add_comm]


private theorem postResetFixedBits_length_eq_hits
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (word : DetSchedule n) :
    (postResetFixedBits ring x word).length =
      predictableHostHits ring
        (fun _ => x) word := by
  unfold predictableHostHits
  exact postResetFixedBits_length_eq_hitsAux
    ring x [] word


private theorem postResetFixedBits_append
    {n : Nat} (ring : DirectedRing n)
    (x : Fin n) (u v : DetSchedule n) :
    postResetFixedBits ring x (u ++ v) =
      postResetFixedBits ring x u ++
        postResetFixedBits ring x v := by
  induction u with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hb : incidentBit ring x e with
      | none =>
          simp [postResetFixedBits, hb, ih]
      | some b =>
          simp [postResetFixedBits, hb, ih]


private theorem postResetLotteryRun_append
    (k : Nat) (s : LotteryState)
    (u v : List Bool) :
    lotteryRun k s (u ++ v) =
      lotteryRun k (lotteryRun k s u) v := by
  induction u generalizing s with
  | nil =>
      rfl
  | cons b rest ih =>
      simp [lotteryRun, ih]


private theorem postResetLotteryStep_wins_mono
    (k : Nat) (s : LotteryState) (b : Bool) :
    s.wins <= (lotteryStep k s b).wins := by
  cases b with
  | false =>
      simpa [lotteryStep] using
        (Nat.le_refl s.wins)
  | true =>
      by_cases hwin : k <= s.headRun + 1
      · simpa [lotteryStep, hwin] using
          (Nat.le_succ s.wins)
      · simpa [lotteryStep, hwin] using
          (Nat.le_refl s.wins)


private theorem postResetLotteryRun_wins_mono
    (k : Nat) (s : LotteryState)
    (bits : List Bool) :
    s.wins <= (lotteryRun k s bits).wins := by
  induction bits generalizing s with
  | nil =>
      exact Nat.le_refl _
  | cons b rest ih =>
      exact Nat.le_trans
        (postResetLotteryStep_wins_mono k s b)
        (by
          simpa [lotteryRun] using
            ih (s := lotteryStep k s b))


private theorem postResetRunRel
    (hstep : Lemma5iiPostResetClockOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x : Fin n) (base : Nat)
    (s : LotteryState)
    (word : DetSchedule n)
    (hrel : PostResetClockLotteryRel
      kappa base (C x) s) :
    PostResetClockLotteryRel kappa base
      (runPPL ring C word x)
      (lotteryRun psi s
        (postResetFixedBits ring x word)) := by
  induction word generalizing C s with
  | nil =>
      simpa [runPPL, runPopulationSchedule,
        postResetFixedBits, lotteryRun] using hrel
  | cons e rest ih =>
      let C' := pplStep ring C e
      let s' := postResetLotteryAdvance
        psi ring x e s
      have hnext :
          PostResetClockLotteryRel
            kappa base (C' x) s' := by
        dsimp [C', s']
        exact hstep hn3 hpsi ring C x e base s hrel
      have htail :=
        ih (C := C') (s := s') hnext
      cases hb : incidentBit ring x e with
      | none =>
          simpa [runPPL, runPopulationSchedule,
            postResetFixedBits,
            postResetLotteryAdvance,
            lotteryRun, hb, C', s', pplStep] using htail
      | some b =>
          simpa [runPPL, runPopulationSchedule,
            postResetFixedBits,
            postResetLotteryAdvance,
            lotteryRun, hb, C', s', pplStep] using htail


private theorem postResetFoldlAnd_gen :
    forall (xs : List Bool) (init : Bool),
      xs.foldl (fun a b => a && b) init = true ->
        And
          (init = true)
          (forall b, b ∈ xs -> b = true)
  | [], init, h => by
      refine And.intro (by simpa using h) ?_
      intro b hb
      simp at hb
  | a :: xs, init, h => by
      have htail :=
        postResetFoldlAnd_gen xs (init && a) h
      have hhead :
          And (init = true) (a = true) := by
        simpa using htail.1
      refine And.intro hhead.1 ?_
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb]
        exact hhead.2
      · exact htail.2 b hb


private theorem postResetFoldlAndTrue_of_allTrue
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


private theorem postResetAllAgents_true_at
    {n : Nat} (p : Fin n -> Bool)
    (h : allAgentsB p = true)
    (i : Fin n) :
    p i = true := by
  unfold allAgentsB at h
  have hall :=
    (postResetFoldlAnd_gen
      (List.ofFn p) true h).2
  apply hall (p i)
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩


private theorem postResetAllAgents_true_of
    {n : Nat} (p : Fin n -> Bool)
    (h : forall i : Fin n, p i = true) :
    allAgentsB p = true := by
  unfold allAgentsB
  apply postResetFoldlAndTrue_of_allTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  exact h i


private theorem postResetFoldlAndFalse_existsFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = false) :
    exists b, And (b ∈ xs) (b = false) := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | false =>
          exact ⟨false, And.intro (by simp) rfl⟩
      | true =>
          have ht :
              xs.foldl (fun u v => u && v) true = false := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hb⟩ := ih ht
          exact ⟨b, And.intro (by simp [hb.1]) hb.2⟩


private def postResetAllConstructB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  allAgentsB
    (fun i => decide ((C i).mode = false))


private theorem postResetAllConstruct_false_exists_detect
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : postResetAllConstructB C = false) :
    exists x : Fin n, (C x).mode = true := by
  unfold postResetAllConstructB allAgentsB at h
  obtain ⟨b, hb⟩ :=
    postResetFoldlAndFalse_existsFalse
      (List.ofFn
        (fun i : Fin n =>
          decide ((C i).mode = false))) h
  have hbmem := hb.1
  rw [List.mem_ofFn] at hbmem
  obtain ⟨x, hx⟩ := hbmem
  have hdec :
      decide ((C x).mode = false) = false :=
    hx.trans hb.2
  cases hm : (C x).mode with
  | false =>
      simp [hm] at hdec
  | true =>
      exact ⟨x, hm⟩


private theorem postResetMidAgentFields
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hmid : midPhysicalB C = true)
    (x : Fin n) :
    And
      ((C x).clock.val <= kappa / 2)
      ((C x).mode = false) := by
  have hall :
      allAgentsB
        (fun i =>
          decide ((C i).clock.val <= kappa / 2) &&
            decide ((C i).mode = false)) = true := by
    unfold midPhysicalB at hmid
    cases hl : leaderPresent C with
    | false =>
        simp [hl] at hmid
    | true =>
        simpa [hl] using hmid
  have hx :=
    postResetAllAgents_true_at _ hall x
  have hparts :=
    Bool.and_eq_true_iff.mp hx
  exact And.intro
    (of_decide_eq_true hparts.1)
    (of_decide_eq_true hparts.2)


private theorem postResetMidAllConstruct
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hmid : midPhysicalB C = true) :
    postResetAllConstructB C = true := by
  unfold postResetAllConstructB
  apply postResetAllAgents_true_of
  intro x
  have hx :=
    postResetMidAgentFields C hmid x
  simp [hx.2]


private theorem postResetConstructAlong_false_detectPrefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hstart : postResetAllConstructB C = true)
    (hfail : constructAlong ring C word = false) :
    exists pre suf x,
      And
        (word = pre ++ suf)
        ((runPPL ring C pre x).mode = true) := by
  induction word generalizing C with
  | nil =>
      have hf :
          postResetAllConstructB C = false := by
        simpa [constructAlong,
          postResetAllConstructB] using hfail
      rw [hstart] at hf
      cases hf
  | cons e rest ih =>
      have hhead :
          allAgentsB
            (fun i =>
              decide ((C i).mode = false)) = true := by
        simpa only [postResetAllConstructB] using hstart
      have htail :
          constructAlong ring
            (pplStep ring C e) rest = false := by
        simp only [constructAlong, hhead,
          Bool.true_and] at hfail
        exact hfail
      cases hnext :
          postResetAllConstructB
            (pplStep ring C e) with
      | false =>
          obtain ⟨x, hx⟩ :=
            postResetAllConstruct_false_exists_detect
              (pplStep ring C e) hnext
          refine ⟨[e], rest, x, And.intro ?_ ?_⟩
          · simp
          · simpa only [runPPL,
              runPopulationSchedule, pplStep] using hx
      | true =>
          obtain ⟨pre, suf, x, hw⟩ :=
            ih (C := pplStep ring C e)
              hnext htail
          refine ⟨e :: pre, suf, x,
            And.intro ?_ ?_⟩
          · simpa [hw.1]
          · simpa only [runPPL,
              runPopulationSchedule, pplStep] using hw.2


private theorem postResetFoldlOr_true
    (xs : List Bool) :
    xs.foldl (fun a b => a || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simpa [List.foldl_cons] using ih


private theorem postResetFoldlOrFalse_allFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a || b) false = false) :
    forall b, b ∈ xs -> b = false := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht :
              xs.foldl (fun u v => u || v) false = false := by
            simpa [List.foldl_cons, ha] using h
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · first | exact hb | exact hb.trans ha
          · exact ih ht b hb
      | true =>
          have ht :=
            postResetFoldlOr_true xs
          have hf : true = false := by
            simpa [List.foldl_cons, ha, ht] using h
          cases hf


private theorem postResetEncounterCap_of_not_bad
    {n psi : Nat} (c : Nat)
    (ring : DirectedRing n)
    (word : DetSchedule n)
    (hbad :
      lemma5iiEncounterBadB psi c ring word = false)
    (x : Fin n) :
    predictableHostHits ring (fun _ => x) word <=
      lemma5iiEncounterCap psi c := by
  unfold lemma5iiEncounterBadB at hbad
  have hall :=
    postResetFoldlOrFalse_allFalse
      (List.ofFn
        (fun y : Fin n =>
          decide
            (lemma5iiEncounterCap psi c <
              predictableHostHits
                ring (fun _ => y) word)))
      hbad
  have hx :
      decide
        (lemma5iiEncounterCap psi c <
          predictableHostHits
            ring (fun _ => x) word) = false := by
    apply hall
    rw [List.mem_ofFn]
    exact ⟨x, rfl⟩
  by_cases hlt :
      lemma5iiEncounterCap psi c <
        predictableHostHits
          ring (fun _ => x) word
  · have ht :
        decide
          (lemma5iiEncounterCap psi c <
            predictableHostHits
              ring (fun _ => x) word) = true :=
      decide_eq_true hlt
    rw [ht] at hx
    cases hx
  · omega


private theorem postResetTarget_le_of_credit
    {psi kappa c base wins : Nat}
    (hpsi : 2 <= psi)
    (hc : 3 <= c)
    (hkappa : kappa = 16 * c * psi)
    (hbase : base <= kappa / 2)
    (hcredit : kappa <= base + wins) :
    lotteryTarget psi (c - 1) + 1 <= wins := by
  let z := c * psi
  have hk : kappa = 16 * z := by
    simpa [z, Nat.mul_assoc] using hkappa
  have hhalf : kappa / 2 = 8 * z := by
    rw [hk]
    omega
  have hwin : 8 * z <= wins := by
    rw [hhalf] at hbase
    rw [hk] at hcredit
    omega
  have hcdec : c = (c - 1) + 1 := by
    omega
  have hz :
      z = (c - 1) * psi + psi := by
    dsimp [z]
    rw [hcdec, Nat.add_mul]
    simp
  have hpsi8 : 1 <= 8 * psi := by
    omega
  have ht :
      8 * (c - 1) * psi + 1 <=
        8 * z := by
    rw [hz, Nat.mul_add, Nat.mul_assoc]
    omega
  unfold lotteryTarget
  exact Nat.le_trans ht hwin


theorem lemma5iiPostResetClockProjection
    (hstep : Lemma5iiPostResetClockOneStep) :
    Lemma5iiPostResetClockProjection := by
  unfold Lemma5iiPostResetClockProjection
  intro n psi kappa c
  intro hn3 hpsi hc hkappa
  intro ring C word hmid hbad


  have henc :
      lemma5iiEncounterBadB
        psi c ring word = false := by
    cases he :
        lemma5iiEncounterBadB
          psi c ring word with
    | false =>
        rfl
    | true =>
        simp [lemma5iiPostResetClockBadB,
          he] at hbad


  have hconstruct :
      constructAlong ring C word = false := by
    cases hw : constructAlong ring C word with
    | false =>
        rfl
    | true =>
        simp [lemma5iiPostResetClockBadB,
          hw] at hbad


  have hstart :
      postResetAllConstructB C = true :=
    postResetMidAllConstruct C hmid


  obtain ⟨pre, suf, x, hwitness⟩ :=
    postResetConstructAlong_false_detectPrefix
      ring C word hstart hconstruct


  have hx0 :=
    postResetMidAgentFields C hmid x


  let s0 := lotteryOffset (C x).hits.val
  have hrel0 :
      PostResetClockLotteryRel
        kappa (C x).clock.val (C x) s0 := by
    unfold PostResetClockLotteryRel
    apply And.intro
    · apply Or.inr
      apply And.intro
      · simp [s0, lotteryOffset]
      · simp [s0, lotteryOffset]
    · intro hm
      rw [hx0.2] at hm
      cases hm


  have hpreRel :=
    postResetRunRel hstep hn3 hpsi
      ring C x (C x).clock.val s0 pre hrel0


  have hcapClock :
      (runPPL ring C pre x).clock.val = kappa :=
    hpreRel.2 hwitness.2


  have hcredit :
      kappa <=
        (C x).clock.val +
          (lotteryRun psi s0
            (postResetFixedBits ring x pre)).wins := by
    rcases hpreRel.1 with hlt | heq
    · rw [hcapClock] at hlt
      exact Nat.le_of_lt hlt
    · have h := heq.1
      rw [hcapClock] at h
      exact Nat.le_of_eq h


  have htargetPre :
      lotteryTarget psi (c - 1) + 1 <=
        (lotteryRun psi s0
          (postResetFixedBits ring x pre)).wins :=
    postResetTarget_le_of_credit
      hpsi hc hkappa hx0.1 hcredit


  have hprefFull :
      (lotteryRun psi s0
          (postResetFixedBits ring x pre)).wins <=
        (lotteryRun psi s0
          (postResetFixedBits ring x word)).wins := by
    rw [hwitness.1,
      postResetFixedBits_append,
      postResetLotteryRun_append]
    exact
      postResetLotteryRun_wins_mono
        psi
        (lotteryRun psi s0
          (postResetFixedBits ring x pre))
        (postResetFixedBits ring x suf)


  have hfullWins :
      lotteryTarget psi (c - 1) + 1 <=
        (lotteryRun psi
          (lotteryOffset (C x).hits.val)
          (stoppedEncounterBits ring
            (fun _ => x) (fun _ => false) word)).wins := by
    rw [postResetStoppedBits_eq_fixed ring x word]
    exact Nat.le_trans htargetPre hprefFull


  have hlen :
      (stoppedEncounterBits ring
        (fun _ => x) (fun _ => false) word).length <=
        lemma5iiEncounterCap psi c := by
    rw [postResetStoppedBits_eq_fixed ring x word,
      postResetFixedBits_length_eq_hits]
    exact postResetEncounterCap_of_not_bad
      c ring word henc x


  refine ⟨x, ?_⟩
  unfold lemma5iiPostResetAgentBadB
  exact decide_eq_true
    (And.intro hlen hfullWins)


theorem lemma5iiPostResetClockCount_closed
    (hstep : Lemma5iiPostResetClockOneStep) :
    Lemma5iiPostResetClockCount :=
  lemma5iiPostResetClockCount
    (lemma5iiPostResetClockProjection hstep)


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.postResetStoppedBitsAux_eq_fixed
#print axioms PPL.Modes.Lemma5.postResetStoppedBits_eq_fixed
#print axioms PPL.Modes.Lemma5.postResetIncidentLetter_eq_incidentBit_isSome
#print axioms PPL.Modes.Lemma5.postResetFixedBits_length_eq_hitsAux
#print axioms PPL.Modes.Lemma5.postResetFixedBits_length_eq_hits
#print axioms PPL.Modes.Lemma5.postResetFixedBits_append
#print axioms PPL.Modes.Lemma5.postResetLotteryRun_append
#print axioms PPL.Modes.Lemma5.postResetLotteryStep_wins_mono
#print axioms PPL.Modes.Lemma5.postResetLotteryRun_wins_mono
#print axioms PPL.Modes.Lemma5.postResetRunRel
#print axioms PPL.Modes.Lemma5.postResetFoldlAnd_gen
#print axioms PPL.Modes.Lemma5.postResetFoldlAndTrue_of_allTrue
#print axioms PPL.Modes.Lemma5.postResetAllAgents_true_at
#print axioms PPL.Modes.Lemma5.postResetAllAgents_true_of
#print axioms PPL.Modes.Lemma5.postResetFoldlAndFalse_existsFalse
#print axioms PPL.Modes.Lemma5.postResetAllConstruct_false_exists_detect
#print axioms PPL.Modes.Lemma5.postResetMidAgentFields
#print axioms PPL.Modes.Lemma5.postResetMidAllConstruct
#print axioms PPL.Modes.Lemma5.postResetConstructAlong_false_detectPrefix
#print axioms PPL.Modes.Lemma5.postResetFoldlOr_true
#print axioms PPL.Modes.Lemma5.postResetFoldlOrFalse_allFalse
#print axioms PPL.Modes.Lemma5.postResetEncounterCap_of_not_bad
#print axioms PPL.Modes.Lemma5.postResetTarget_le_of_credit
#print axioms PPL.Modes.Lemma5.lemma5iiPostResetClockProjection
#print axioms PPL.Modes.Lemma5.lemma5iiPostResetClockCount_closed
