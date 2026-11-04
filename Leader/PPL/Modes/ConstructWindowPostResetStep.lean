import Leader.PPL.Modes.ConstructWindowPostResetProjection




namespace PPL.Modes.Lemma5




set_option autoImplicit false
set_option Elab.async false




open PPL.Probability




/-!
# Lemma 5(ii): one-step post-reset clock / lottery simulation




Truth audit: the unrestricted one-step statement is true.




For an untouched agent both the physical state and lottery state are unchanged.
For an initiator letter T, DetermineMode clears physical hits and never raises
that endpoint's clock.  For a responder letter H, the only possible clock
increase is the completed-psi-hit branch; that branch raises the clock by at
most one and resets hits to zero.  This is exactly the one unit of lottery
credit obtained when H closes a lottery run.  Signal arrival only resets the
physical clock and is therefore monotone for the relation.




finishModes writes mode from the resulting clock, and the Algorithms 2/3/5
suffix preserves clock, hits, and mode.  Thus no reachability premise is
needed even on arbitrary Cartesian protocol states.
-/




private def postResetArmedSignalVal
    {psi kappa : Nat}
    (q : PPL.State psi kappa) : Nat :=
  if q.leader = true then kappa else q.signalR.val




private def postResetBumpedHitsVal
    {psi kappa : Nat}
    (q : PPL.State psi kappa) : Nat :=
  Nat.min (q.hits.val + 1) psi




/-- finishModes is the only writer of mode in DetermineMode, so either
endpoint being Detect certifies that its resulting clock is capped. -/
private theorem postResetDetermineMode_modes_capped
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.determineMode l r
    And
      (q.1.mode = true -> q.1.clock.val = kappa)
      (q.2.mode = true -> q.2.clock.val = kappa) := by
  cases hlead : l.leader with
  | false =>
      by_cases hhit :
          Nat.min (r.hits.val + 1) psi = psi
      · simp only [PPL.determineMode, hlead,
          Bool.false_eq_true, if_false]
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          try dsimp only
          apply And.intro
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
      · simp only [PPL.determineMode, hlead,
          Bool.false_eq_true, if_false]
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          try dsimp only
          apply And.intro
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
  | true =>
      by_cases hhit :
          Nat.min (r.hits.val + 1) psi = psi
      · simp only [PPL.determineMode, hlead, if_true]
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          try dsimp only
          apply And.intro
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
      · simp only [PPL.determineMode, hlead, if_true]
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          try dsimp only
          apply And.intro
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm
          · intro hm
            rw [beq_iff_eq] at hm
            exact hm




/-- In the signal branch both clocks are reset.  The responder hit counter is
either zeroed or is the bumped counter, hence is at most old hits plus one. -/
private theorem postResetDetermineMode_signal_fields
    {psi kappa : Nat}
    (l r : PPL.State psi kappa)
    (hsignal :
      Or
        (0 < postResetArmedSignalVal l)
        (0 < r.signalR.val)) :
    let q := PPL.determineMode l r
    And
      (q.1.clock.val = 0)
      (And
        (q.1.hits.val = 0)
        (And
          (q.2.clock.val = 0)
          (q.2.hits.val <= r.hits.val + 1))) := by
  have hbump :
      postResetBumpedHitsVal r <= r.hits.val + 1 := by
    unfold postResetBumpedHitsVal
    exact Nat.min_le_left _ _
  cases hlead : l.leader with
  | false =>
      have hline :
          Or (0 < l.signalR.val) (0 < r.signalR.val) := by
        simpa [postResetArmedSignalVal, hlead] using hsignal
      by_cases hhit :
          Nat.min (r.hits.val + 1) psi = psi
      · simp only [PPL.determineMode, hlead,
          Bool.false_eq_true, if_false]
        try dsimp only
        rw [dif_pos hline]
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          refine And.intro rfl
            (And.intro rfl
              (And.intro rfl ?_))
          first
          | exact Nat.zero_le _
          | exact Nat.min_le_left _ _
          | exact Nat.le_trans (Nat.le_of_eq hhit.symm)
              (Nat.min_le_left _ _)
      · simp only [PPL.determineMode, hlead,
          Bool.false_eq_true, if_false]
        try dsimp only
        rw [dif_pos hline]
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          refine And.intro rfl
            (And.intro rfl
              (And.intro rfl ?_))
          first
          | exact Nat.zero_le _
          | exact Nat.min_le_left _ _
          | exact Nat.le_trans (Nat.le_of_eq hhit.symm)
              (Nat.min_le_left _ _)
  | true =>
      have hline :
          Or (0 < kappa) (0 < r.signalR.val) := by
        simpa [postResetArmedSignalVal, hlead] using hsignal
      by_cases hhit :
          Nat.min (r.hits.val + 1) psi = psi
      · simp only [PPL.determineMode, hlead, if_true]
        try dsimp only
        split
        rotate_left
        · rename_i hneg
          exact absurd hline hneg
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          refine And.intro rfl
            (And.intro rfl
              (And.intro rfl ?_))
          first
          | exact Nat.zero_le _
          | exact Nat.min_le_left _ _
          | exact Nat.le_trans (Nat.le_of_eq hhit.symm)
              (Nat.min_le_left _ _)
      · simp only [PPL.determineMode, hlead, if_true]
        try dsimp only
        split
        rotate_left
        · rename_i hneg
          exact absurd hline hneg
        unfoldFinishModes
        simp only [hhit]
        repeat' (split <;> try dsimp only)
        all_goals
          refine And.intro rfl
            (And.intro rfl
              (And.intro rfl ?_))
          first
          | exact Nat.zero_le _
          | exact Nat.min_le_left _ _
          | exact Nat.le_trans (Nat.le_of_eq hhit.symm)
              (Nat.min_le_left _ _)




/-- In the no-signal branch the initiator clock is unchanged and its hits are
cleared.  The responder clock rises by at most one, its hits rise by at most
one, and any strict responder clock rise certifies a completed psi-run and
therefore zero resulting hits. -/
private theorem postResetDetermineMode_noSignal_fields
    {psi kappa : Nat}
    (l r : PPL.State psi kappa)
    (hl : postResetArmedSignalVal l = 0)
    (hr : r.signalR.val = 0) :
    let q := PPL.determineMode l r
    And
      (q.1.clock.val = l.clock.val)
      (And
        (q.1.hits.val = 0)
        (And
          (q.2.clock.val <= r.clock.val + 1)
          (And
            (q.2.hits.val <= r.hits.val + 1)
            (r.clock.val < q.2.clock.val ->
              And
                (psi <= r.hits.val + 1)
                (q.2.hits.val = 0))))) := by
  have hbump :
      postResetBumpedHitsVal r <= r.hits.val + 1 := by
    unfold postResetBumpedHitsVal
    exact Nat.min_le_left _ _
  have hclock :
      Nat.min (r.clock.val + 1) kappa <=
        r.clock.val + 1 := by
    exact Nat.min_le_left _ _
  cases hlead : l.leader with
  | false =>
      have hls : l.signalR.val = 0 := by
        simpa [postResetArmedSignalVal, hlead] using hl
      by_cases hhit :
          postResetBumpedHitsVal r = psi
      · simp [PPL.determineMode, hlead, hls, hr,
          postResetBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;>
          simp_all [postResetBumpedHitsVal] <;>
          omega
      · simp [PPL.determineMode, hlead, hls, hr,
          postResetBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;>
          simp_all [postResetBumpedHitsVal] <;>
          omega
  | true =>
      have hk : kappa = 0 := by
        simpa [postResetArmedSignalVal, hlead] using hl
      by_cases hhit :
          postResetBumpedHitsVal r = psi
      · simp [PPL.determineMode, hlead, hk, hr,
          postResetBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;>
          simp_all [postResetBumpedHitsVal] <;>
          omega
      · simp [PPL.determineMode, hlead, hk, hr,
          postResetBumpedHitsVal, hhit] <;>
          unfoldFinishModes <;>
          simp_all [postResetBumpedHitsVal] <;>
          omega




/-! ## Mode frame through Algorithms 2, 3, and 5 -/




private theorem postResetMoveToken_modes
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    And
      ((PPL.moveToken hpsi kind l r).1.mode = l.mode)
      ((PPL.moveToken hpsi kind l r).2.mode = r.mode) := by
  constructor
  · have h :=
      congrArg
        (fun q : PPL.State psi kappa => q.mode)
        (PPL.moveToken_initiator_fields
          hpsi kind l r)
    cases kind <;>
      simpa [PPL.eraseKindToken] using h
  · rcases
      PPL.moveToken_responder_fields
        hpsi kind l r with h | h
    · have hm :=
        congrArg
          (fun q : PPL.State psi kappa => q.mode) h
      cases kind <;>
        simpa
          [PPL.eraseKindTokenId,
            PPL.eraseKindToken] using hm
    · have hm :=
        congrArg
          (fun q : PPL.State psi kappa => q.mode) h
      cases kind <;>
        simpa
          [PPL.eraseKindTokenId,
            PPL.eraseKindToken,
            PPL.birthFields] using hm




private def postResetPreTokenModePair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
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
    else if Or (r1.dist.val = 0) (r1.dist.val = psi) then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)




private theorem postResetLine6_modes
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    And
      (s.left.mode = d.1.mode)
      (s.right.mode = d.2.mode) := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · exact And.intro rfl rfl
  · exact And.intro rfl rfl




private theorem postResetPreToken_modes
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := postResetPreTokenModePair hpsi l r
    And
      (q.1.mode = d.1.mode)
      (q.2.mode = d.2.mode) := by
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hs := postResetLine6_modes hpsi l r
  have hp :
      let q := postResetPreTokenModePair hpsi l r
      And
        (q.1.mode = s.left.mode)
        (q.2.mode = s.right.mode) := by
    dsimp only [postResetPreTokenModePair]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact And.intro rfl rfl
  dsimp only at hs hp ⊢
  exact
    And.intro
      (hp.1.trans hs.1)
      (hp.2.trans hs.2)




private theorem postResetCreateLeader_modes
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.createLeader hpsi l r
    And
      (q.1.mode = d.1.mode)
      (q.2.mode = d.2.mode) := by
  let p := postResetPreTokenModePair hpsi l r
  let b := PPL.moveToken hpsi .black p.1 p.2
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hdef : PPL.createLeader hpsi l r = w := by
    rfl
  have hp := postResetPreToken_modes hpsi l r
  have hb :=
    postResetMoveToken_modes
      hpsi PPL.TokenKind.black p.1 p.2
  have hw :=
    postResetMoveToken_modes
      hpsi PPL.TokenKind.white b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact
    And.intro
      (hw.1.trans (hb.1.trans hp.1))
      (hw.2.trans (hb.2.trans hp.2))




private theorem postResetEliminate_modes
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    And
      (q.1.mode = l.mode)
      (q.2.mode = r.mode) := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    And.intro
      (congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.mode) hl)
      (congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.mode) hr)




private theorem postResetPpl_modes
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.ppl hpsi l r
    And
      (q.1.mode = d.1.mode)
      (q.2.mode = d.2.mode) := by
  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc := postResetCreateLeader_modes hpsi l r
  have he := postResetEliminate_modes c.1 c.2
  have hdef : PPL.ppl hpsi l r = q := by
    rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact
    And.intro
      (he.1.trans hc.1)
      (he.2.trans hc.2)




/-! ## DetermineMode preserves the clock / lottery relation -/




private theorem postResetDetermineMode_left_rel
    {psi kappa : Nat}
    (l r : PPL.State psi kappa)
    (base : Nat)
    (s : LotteryState)
    (hrel :
      PostResetClockLotteryRel kappa base l s) :
    PostResetClockLotteryRel kappa base
      (PPL.determineMode l r).1
      (lotteryStep psi s false) := by
  have hm :=
    postResetDetermineMode_modes_capped l r
  dsimp only at hm
  unfold PostResetClockLotteryRel at hrel ⊢
  constructor
  · by_cases hsignal :
        Or
          (0 < postResetArmedSignalVal l)
          (0 < r.signalR.val)
    · have hf :=
        postResetDetermineMode_signal_fields
          l r hsignal
      dsimp only at hf
      rcases hf with
        ⟨hclock, hhits, _hrclock, _hrhits⟩
      by_cases hpos : 0 < base + s.wins
      · apply Or.inl
        simp [lotteryStep]
        omega
      · apply Or.inr
        constructor
        · simp [lotteryStep]
          omega
        · change
            (PPL.determineMode l r).1.hits.val <= 0
          exact Nat.le_of_eq hhits
    · have hnl :
          Not (0 < postResetArmedSignalVal l) := by
        intro h
        exact hsignal (Or.inl h)
      have hnr : Not (0 < r.signalR.val) := by
        intro h
        exact hsignal (Or.inr h)
      have hl : postResetArmedSignalVal l = 0 := by
        omega
      have hr : r.signalR.val = 0 := by
        omega
      have hf :=
        postResetDetermineMode_noSignal_fields
          l r hl hr
      dsimp only at hf
      rcases hf with
        ⟨hclock, hhits, _hrclock, _hrhits, _htick⟩
      rcases hrel.1 with hlt | heq
      · apply Or.inl
        simp [lotteryStep]
        omega
      · apply Or.inr
        constructor
        · simp [lotteryStep]
          omega
        · change
            (PPL.determineMode l r).1.hits.val <= 0
          exact Nat.le_of_eq hhits
  · intro hmode
    exact hm.1 hmode




private theorem postResetDetermineMode_right_rel
    {psi kappa : Nat}
    (l r : PPL.State psi kappa)
    (base : Nat)
    (s : LotteryState)
    (hrel :
      PostResetClockLotteryRel kappa base r s) :
    PostResetClockLotteryRel kappa base
      (PPL.determineMode l r).2
      (lotteryStep psi s true) := by
  have hm :=
    postResetDetermineMode_modes_capped l r
  dsimp only at hm
  unfold PostResetClockLotteryRel at hrel ⊢
  constructor
  · by_cases hsignal :
        Or
          (0 < postResetArmedSignalVal l)
          (0 < r.signalR.val)
    · have hf :=
        postResetDetermineMode_signal_fields
          l r hsignal
      dsimp only at hf
      rcases hf with
        ⟨_hlclock, _hlhits, hclock, hhits⟩
      by_cases hwin : psi <= s.headRun + 1
      · apply Or.inl
        simp [lotteryStep, hwin]
        omega
      · by_cases hpos : 0 < base + s.wins
        · apply Or.inl
          simp [lotteryStep, hwin]
          omega
        · have hrhits : r.hits.val <= s.headRun := by
            rcases hrel.1 with hlt | heq
            · omega
            · exact heq.2
          apply Or.inr
          constructor
          · simp [lotteryStep, hwin]
            omega
          · simp [lotteryStep, hwin]
            omega
    · have hnl :
          Not (0 < postResetArmedSignalVal l) := by
        intro h
        exact hsignal (Or.inl h)
      have hnr : Not (0 < r.signalR.val) := by
        intro h
        exact hsignal (Or.inr h)
      have hl : postResetArmedSignalVal l = 0 := by
        omega
      have hr : r.signalR.val = 0 := by
        omega
      have hf :=
        postResetDetermineMode_noSignal_fields
          l r hl hr
      dsimp only at hf
      rcases hf with
        ⟨_hlclock, _hlhits, hclock, hhits, htick⟩
      by_cases hwin : psi <= s.headRun + 1
      · rcases hrel.1 with hlt | heq
        · apply Or.inl
          simp [lotteryStep, hwin]
          omega
        · by_cases hstrict :
              (PPL.determineMode l r).2.clock.val <
                base + (s.wins + 1)
          · apply Or.inl
            simpa [lotteryStep, hwin] using hstrict
          · have heqNew :
                (PPL.determineMode l r).2.clock.val =
                  base + (s.wins + 1) := by
              omega
            have htickNow :
                r.clock.val <
                  (PPL.determineMode l r).2.clock.val := by
              omega
            have hzero := (htick htickNow).2
            apply Or.inr
            constructor
            · simpa [lotteryStep, hwin] using heqNew
            · simp [lotteryStep, hwin, hzero]
      · rcases hrel.1 with hlt | heq
        · by_cases hstrict :
              (PPL.determineMode l r).2.clock.val <
                base + s.wins
          · apply Or.inl
            simpa [lotteryStep, hwin] using hstrict
          · have heqNew :
                (PPL.determineMode l r).2.clock.val =
                  base + s.wins := by
              omega
            have htickNow :
                r.clock.val <
                  (PPL.determineMode l r).2.clock.val := by
              omega
            have hzero := (htick htickNow).2
            apply Or.inr
            constructor
            · simpa [lotteryStep, hwin] using heqNew
            · simp [lotteryStep, hwin, hzero]
        · have hnoTick :
              Not
                (r.clock.val <
                  (PPL.determineMode l r).2.clock.val) := by
            intro ht
            have hp := (htick ht).1
            apply hwin
            omega
          have hclockLe :
              (PPL.determineMode l r).2.clock.val <=
                r.clock.val := by
            omega
          by_cases hstrict :
              (PPL.determineMode l r).2.clock.val <
                base + s.wins
          · apply Or.inl
            simpa [lotteryStep, hwin] using hstrict
          · have heqNew :
                (PPL.determineMode l r).2.clock.val =
                  base + s.wins := by
              omega
            apply Or.inr
            constructor
            · simpa [lotteryStep, hwin] using heqNew
            · simp [lotteryStep, hwin]
              omega
  · intro hmode
    exact hm.2 hmode




/-! ## Transport through the rest of one literal P_PL pair step -/




private theorem postResetPpl_left_rel
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (base : Nat)
    (s : LotteryState)
    (hrel :
      PostResetClockLotteryRel kappa base l s) :
    PostResetClockLotteryRel kappa base
      (PPL.ppl hpsi l r).1
      (lotteryStep psi s false) := by
  have hd :=
    postResetDetermineMode_left_rel
      l r base s hrel
  have hp :=
    clockSuffixPairProjection hpsi l r
  have hm :=
    postResetPpl_modes hpsi l r
  dsimp only at hp hm
  unfold PostResetClockLotteryRel at hd ⊢
  rw [hp.1, hp.2.1, hm.1]
  exact hd




private theorem postResetPpl_right_rel
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa)
    (base : Nat)
    (s : LotteryState)
    (hrel :
      PostResetClockLotteryRel kappa base r s) :
    PostResetClockLotteryRel kappa base
      (PPL.ppl hpsi l r).2
      (lotteryStep psi s true) := by
  have hd :=
    postResetDetermineMode_right_rel
      l r base s hrel
  have hp :=
    clockSuffixPairProjection hpsi l r
  have hm :=
    postResetPpl_modes hpsi l r
  dsimp only at hp hm
  unfold PostResetClockLotteryRel at hd ⊢
  rw [hp.2.2.1, hp.2.2.2, hm.2]
  exact hd




/-! ## Ring geometry for the fixed-agent three-way split -/




private theorem postResetLeftNeighbor_ne_self
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 <= n)
    (i : Fin n) :
    ring.leftNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.val + n - 1) % n = i.val at hv
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 :
        (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 :
        (i.val + n - 1) % n = i.val - 1 := by
      rw [show
        i.val + n - 1 = (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega




private theorem postResetLeftNeighbor_rightNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq :
        i.val + 1 + n - 1 = n + i.val := by
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




private theorem postResetRightNeighbor_leftNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by
      omega
    rw [hs, Nat.mod_self]
  · have heq :
        i.val + n - 1 = n + (i.val - 1) := by
      omega
    have hlt : i.val - 1 < n := by
      omega
    have hleft :
        (i.val + n - 1) % n = i.val - 1 := by
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs : i.val - 1 + 1 = i.val := by
      omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]




/-- The requested unrestricted one-step leaf. -/
theorem lemma5iiPostResetClockOneStep_proved :
    Lemma5iiPostResetClockOneStep := by
  unfold Lemma5iiPostResetClockOneStep
  intro n psi kappa hn3 hpsi
  intro ring C x e base s hrel




  by_cases hH : e = ring.leftNeighbor x
  · subst e
    have hne :
        ring.leftNeighbor x ≠ x :=
      postResetLeftNeighbor_ne_self
        ring (by omega) x
    have hxne :
        x ≠ ring.leftNeighbor x := by
      intro h
      exact hne h.symm
    have hrx :
        ring.rightNeighbor
            (ring.leftNeighbor x) = x :=
      postResetRightNeighbor_leftNeighbor ring x
    have hpair :=
      postResetPpl_right_rel
        hpsi
        (C (ring.leftNeighbor x))
        (C x) base s hrel
    have hstep :
        pplStep ring C
            (ring.leftNeighbor x) x =
          (PPL.ppl hpsi
            (C (ring.leftNeighbor x))
            (C x)).2 := by
      simp [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition,
        hpsi, hne, hxne, hrx]
    rw [hstep]
    simpa [postResetLotteryAdvance,
      incidentBit] using hpair




  · by_cases hT : e = x
    · subst e
      have hxl :
          x ≠ ring.leftNeighbor x := by
        intro h
        exact
          (postResetLeftNeighbor_ne_self
            ring (by omega) x) h.symm
      have hpair :=
        postResetPpl_left_rel
          hpsi
          (C x)
          (C (ring.rightNeighbor x))
          base s hrel
      have hstep :
          pplStep ring C x x =
            (PPL.ppl hpsi
              (C x)
              (C (ring.rightNeighbor x))).1 := by
        simp [pplStep, PopulationProtocol.step,
          PPL.protocol, PPL.transition, hpsi]
      rw [hstep]
      simpa [postResetLotteryAdvance,
        incidentBit, hxl] using hpair




    · have hxr :
          x ≠ ring.rightNeighbor e := by
        intro h
        have hh :
            ring.leftNeighbor x = e := by
          calc
            ring.leftNeighbor x =
                ring.leftNeighbor
                  (ring.rightNeighbor e) := by
              rw [h]
            _ = e :=
              postResetLeftNeighbor_rightNeighbor ring e
        exact hH hh.symm
      have hxe : x ≠ e := by
        intro h
        exact hT h.symm
      have hsame :
          pplStep ring C e x = C x := by
        simp [pplStep, PopulationProtocol.step,
          PPL.protocol, hxe, hxr]
      rw [hsame]
      simpa [postResetLotteryAdvance,
        incidentBit, hH, hT] using hrel




theorem lemma5iiPostResetClockCount_proved :
    Lemma5iiPostResetClockCount :=
  lemma5iiPostResetClockCount_closed
    lemma5iiPostResetClockOneStep_proved




end PPL.Modes.Lemma5




#print axioms PPL.Modes.Lemma5.lemma5iiPostResetClockOneStep_proved
#print axioms PPL.Modes.Lemma5.lemma5iiPostResetClockCount_proved



