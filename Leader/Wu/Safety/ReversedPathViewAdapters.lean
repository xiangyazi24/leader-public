import Leader.Wu.Safety.ReversedPathPrefixFrame
import Leader.Wu.Safety.ReversedPathCleanFrame
import Leader.Wu.Safety.ReversedPathMiddleQuiet


set_option autoImplicit false
set_option Elab.async false


namespace ZZSafeN4ReversedViewAdaptersGPT


/-!
This file is deliberately only glue between the three already-proved views.


No transition is unfolded here.
No ReversedCore copy is introduced here.
All names from the imported leaves are kept namespace-qualified so their
distinct hpsi2 declarations cannot collide.
-/


/-! ## Small private equality extractors -/


private theorem prefixCellView_eq_fields
    {u v : AgentState 2}
    (h :
      ZZSafeN4ReversedPrefixGPT.prefixCellView u =
        ZZSafeN4ReversedPrefixGPT.prefixCellView v) :
    u.leader = v.leader ∧
    u.label = v.label ∧
    u.probe = v.probe ∧
    u.phase = v.phase ∧
    u.path = v.path ∧
    u.path2 = v.path2 ∧
    u.p = v.p ∧
    u.p_carry = v.p_carry ∧
    u.state = v.state ∧
    u.signal_B = v.signal_B ∧
    u.bullet = v.bullet ∧
    u.shield = v.shield ∧
    u.path4 = v.path4 ∧
    u.path5 = v.path5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.leader) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.label) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.probe) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.phase) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.path) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.path2) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.p) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.p_carry) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.state) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.signal_B) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.bullet) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.shield) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.path4) h
  · simpa [ZZSafeN4ReversedPrefixGPT.prefixCellView] using
      congrArg
        (fun z : ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.path5) h


private theorem cleanProtectedView_eq_fields
    {u v : AgentState 2}
    (h :
      ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState u =
        ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState v) :
    u.state = v.state ∧
    u.leader = v.leader ∧
    u.label = v.label ∧
    u.probe = v.probe ∧
    u.phase = v.phase ∧
    u.path2 = v.path2 ∧
    u.p = v.p ∧
    u.p_carry = v.p_carry ∧
    u.signal_B = v.signal_B ∧
    u.bullet = v.bullet ∧
    u.shield = v.shield := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.state) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.leader) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.label) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.probe) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.phase) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.path2) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.p) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.p_carry) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.signal_B) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.bullet) h
  · simpa [ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState] using
      congrArg
        (fun z : ZZSafeN4ReversedCleanGPT.CleanProtectedView => z.shield) h


/-! ## Protected predicates imply the prefix role predicates -/


theorem protected_to_ABPrefixRole
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal r) :
    ZZSafeN4ReversedPrefixGPT.ABPrefixRole l r := by
  have hl' := hl
  have hr' := hr
  rcases hl' with
    ⟨hlQuiet, hlLeader, hlProbe, hlPhase, hlSignal, hlBullet,
      hlShield, hlPath4, hlPath5⟩
  rcases hlQuiet with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr' with
    ⟨hrQuiet, hrLeader, hrProbe, hrPhase, hrSignal, hrBullet,
      hrShield, hrPath4, hrPath5⟩
  rcases hrQuiet with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact
    { leftLabel := hlLabel
      rightLabel := hrLabel
      leftProbe := hlProbe
      rightProbe := hrProbe
      leftPhase := hlPhase
      rightPhase := hrPhase
      leftPath := hlPath
      rightPath := hrPath
      leftState := hlState
      rightState := hrState }


theorem protected_to_BAPrefixRole
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit r) :
    ZZSafeN4ReversedPrefixGPT.BAPrefixRole l r := by
  have hl' := hl
  have hr' := hr
  rcases hl' with
    ⟨hlQuiet, hlLeader, hlProbe, hlPhase, hlSignal, hlBullet,
      hlShield, hlPath4, hlPath5⟩
  rcases hlQuiet with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr' with
    ⟨hrQuiet, hrLeader, hrProbe, hrPhase, hrSignal, hrBullet,
      hrShield, hrPath4, hrPath5⟩
  rcases hrQuiet with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact
    { leftLabel := hlLabel
      rightLabel := hrLabel
      leftProbe := hlProbe
      rightProbe := hrProbe
      leftPhase := hlPhase
      rightPhase := hrPhase
      leftPath := hlPath
      rightPath := hrPath
      leftState := hlState
      rightState := hrState }


/-! ## Prefix-cell view equality transports the complete protected predicates -/


private theorem AProtected_of_prefixCellView_eq
    (leaderBit : Bool) (u v : AgentState 2)
    (hview :
      ZZSafeN4ReversedPrefixGPT.prefixCellView u =
        ZZSafeN4ReversedPrefixGPT.prefixCellView v)
    (hv : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit v) :
    ZZSafeN4ReversedMiddleGPT.AProtected leaderBit u := by
  rcases prefixCellView_eq_fields hview with
    ⟨eLeader, eLabel, eProbe, ePhase, ePath, ePath2, eP, ePCarry,
      eState, eSignal, eBullet, eShield, ePath4, ePath5⟩
  rcases hv with
    ⟨hvQuiet, hvLeader, hvProbe, hvPhase, hvSignal, hvBullet,
      hvShield, hvPath4, hvPath5⟩
  rcases hvQuiet with
    ⟨hvLabel, hvPath, hvPath2, hvP, hvPCarry, hvState⟩
  refine ⟨?_, eLeader.trans hvLeader, eProbe.trans hvProbe,
    ePhase.trans hvPhase, eSignal.trans hvSignal,
    eBullet.trans hvBullet, eShield.trans hvShield, ?_,
    ePath5.trans hvPath5⟩
  · refine ⟨eLabel.trans hvLabel, ePath.trans hvPath,
      ePath2.trans hvPath2, eP.trans hvP, ePCarry.trans hvPCarry, ?_⟩
    rcases hvState with hs | hs
    · exact Or.inl (eState.trans hs)
    · exact Or.inr (eState.trans hs)
  · rcases hvPath4 with hp | hp
    · exact Or.inl (ePath4.trans hp)
    · exact Or.inr (ePath4.trans hp)


private theorem BProtected_of_prefixCellView_eq
    (bulletVal : Fin 3) (u v : AgentState 2)
    (hview :
      ZZSafeN4ReversedPrefixGPT.prefixCellView u =
        ZZSafeN4ReversedPrefixGPT.prefixCellView v)
    (hv : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal v) :
    ZZSafeN4ReversedMiddleGPT.BProtected bulletVal u := by
  rcases prefixCellView_eq_fields hview with
    ⟨eLeader, eLabel, eProbe, ePhase, ePath, ePath2, eP, ePCarry,
      eState, eSignal, eBullet, eShield, ePath4, ePath5⟩
  rcases hv with
    ⟨hvQuiet, hvLeader, hvProbe, hvPhase, hvSignal, hvBullet,
      hvShield, hvPath4, hvPath5⟩
  rcases hvQuiet with
    ⟨hvLabel, hvPath, hvPath2, hvP, hvPCarry, hvState⟩
  refine ⟨?_, eLeader.trans hvLeader, eProbe.trans hvProbe,
    ePhase.trans hvPhase, eSignal.trans hvSignal,
    eBullet.trans hvBullet, eShield.trans hvShield,
    ePath4.trans hvPath4, ?_⟩
  · exact ⟨eLabel.trans hvLabel, ePath.trans hvPath,
      ePath2.trans hvPath2, eP.trans hvP, ePCarry.trans hvPCarry,
      eState.trans hvState⟩
  · rcases hvPath5 with hp | hp
    · exact Or.inl (ePath5.trans hp)
    · exact Or.inr (ePath5.trans hp)


/-- AB pair-view transport.  Every AProtected/BProtected field, including
path4/path5 connectors, is recovered from prefixPairView equality. -/
theorem prefixPairView_transport_AB
    (leaderBit : Bool) (bulletVal : Fin 3)
    (q : AgentState 2 × AgentState 2)
    (l r : AgentState 2)
    (hview :
      ZZSafeN4ReversedPrefixGPT.prefixPairView q =
        ZZSafeN4ReversedPrefixGPT.prefixPairView (l, r))
    (hprotected :
      ZZSafeN4ReversedMiddleGPT.AProtected leaderBit l ∧
        ZZSafeN4ReversedMiddleGPT.BProtected bulletVal r) :
    ZZSafeN4ReversedMiddleGPT.AProtected leaderBit q.1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected bulletVal q.2 := by
  have hleft :
      ZZSafeN4ReversedPrefixGPT.prefixCellView q.1 =
        ZZSafeN4ReversedPrefixGPT.prefixCellView l := by
    simpa [ZZSafeN4ReversedPrefixGPT.prefixPairView] using
      congrArg
        (fun z :
          ZZSafeN4ReversedPrefixGPT.PrefixCellView ×
            ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.1)
        hview
  have hright :
      ZZSafeN4ReversedPrefixGPT.prefixCellView q.2 =
        ZZSafeN4ReversedPrefixGPT.prefixCellView r := by
    simpa [ZZSafeN4ReversedPrefixGPT.prefixPairView] using
      congrArg
        (fun z :
          ZZSafeN4ReversedPrefixGPT.PrefixCellView ×
            ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.2)
        hview
  exact
    ⟨AProtected_of_prefixCellView_eq leaderBit q.1 l hleft hprotected.1,
     BProtected_of_prefixCellView_eq bulletVal q.2 r hright hprotected.2⟩


/-- BA pair-view transport.  This is the orientation-reversed analogue. -/
theorem prefixPairView_transport_BA
    (leaderBit : Bool) (bulletVal : Fin 3)
    (q : AgentState 2 × AgentState 2)
    (l r : AgentState 2)
    (hview :
      ZZSafeN4ReversedPrefixGPT.prefixPairView q =
        ZZSafeN4ReversedPrefixGPT.prefixPairView (l, r))
    (hprotected :
      ZZSafeN4ReversedMiddleGPT.BProtected bulletVal l ∧
        ZZSafeN4ReversedMiddleGPT.AProtected leaderBit r) :
    ZZSafeN4ReversedMiddleGPT.BProtected bulletVal q.1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected leaderBit q.2 := by
  have hleft :
      ZZSafeN4ReversedPrefixGPT.prefixCellView q.1 =
        ZZSafeN4ReversedPrefixGPT.prefixCellView l := by
    simpa [ZZSafeN4ReversedPrefixGPT.prefixPairView] using
      congrArg
        (fun z :
          ZZSafeN4ReversedPrefixGPT.PrefixCellView ×
            ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.1)
        hview
  have hright :
      ZZSafeN4ReversedPrefixGPT.prefixCellView q.2 =
        ZZSafeN4ReversedPrefixGPT.prefixCellView r := by
    simpa [ZZSafeN4ReversedPrefixGPT.prefixPairView] using
      congrArg
        (fun z :
          ZZSafeN4ReversedPrefixGPT.PrefixCellView ×
            ZZSafeN4ReversedPrefixGPT.PrefixCellView => z.2)
        hview
  exact
    ⟨BProtected_of_prefixCellView_eq bulletVal q.1 l hleft hprotected.1,
     AProtected_of_prefixCellView_eq leaderBit q.2 r hright hprotected.2⟩


/-! ## CLEAN protected-view adapters -/


private theorem AProtected_of_cleanProtectedView_eq
    (leaderBit : Bool) (u v : AgentState 2)
    (hview :
      ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState u =
        ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState v)
    (hpath : u.path = .some 1 0)
    (hpath4 :
      u.path4 = none ∨
        u.path4 = some ((1 : Int), (1 : Nat)))
    (hpath5 : u.path5 = none)
    (hv : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit v) :
    ZZSafeN4ReversedMiddleGPT.AProtected leaderBit u := by
  rcases cleanProtectedView_eq_fields hview with
    ⟨eState, eLeader, eLabel, eProbe, ePhase, ePath2,
      eP, ePCarry, eSignal, eBullet, eShield⟩
  rcases hv with
    ⟨hvQuiet, hvLeader, hvProbe, hvPhase, hvSignal, hvBullet,
      hvShield, hvPath4, hvPath5⟩
  rcases hvQuiet with
    ⟨hvLabel, hvPath, hvPath2, hvP, hvPCarry, hvState⟩
  refine ⟨?_, eLeader.trans hvLeader, eProbe.trans hvProbe,
    ePhase.trans hvPhase, eSignal.trans hvSignal,
    eBullet.trans hvBullet, eShield.trans hvShield, hpath4, hpath5⟩
  refine ⟨eLabel.trans hvLabel, hpath, ePath2.trans hvPath2,
    eP.trans hvP, ePCarry.trans hvPCarry, ?_⟩
  rcases hvState with hs | hs
  · exact Or.inl (eState.trans hs)
  · exact Or.inr (eState.trans hs)


private theorem BProtected_of_cleanProtectedView_eq
    (bulletVal : Fin 3) (u v : AgentState 2)
    (hview :
      ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState u =
        ZZSafeN4ReversedCleanGPT.CleanProtectedView.ofState v)
    (hpath : u.path = .some 0 0)
    (hpath4 : u.path4 = none)
    (hpath5 :
      u.path5 = none ∨
        u.path5 = some ((0 : Int), (1 : Nat)))
    (hv : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal v) :
    ZZSafeN4ReversedMiddleGPT.BProtected bulletVal u := by
  rcases cleanProtectedView_eq_fields hview with
    ⟨eState, eLeader, eLabel, eProbe, ePhase, ePath2,
      eP, ePCarry, eSignal, eBullet, eShield⟩
  rcases hv with
    ⟨hvQuiet, hvLeader, hvProbe, hvPhase, hvSignal, hvBullet,
      hvShield, hvPath4, hvPath5⟩
  rcases hvQuiet with
    ⟨hvLabel, hvPath, hvPath2, hvP, hvPCarry, hvState⟩
  refine ⟨?_, eLeader.trans hvLeader, eProbe.trans hvProbe,
    ePhase.trans hvPhase, eSignal.trans hvSignal,
    eBullet.trans hvBullet, eShield.trans hvShield, hpath4, hpath5⟩
  exact ⟨eLabel.trans hvLabel, hpath, ePath2.trans hvPath2,
    eP.trans hvP, ePCarry.trans hvPCarry, eState.trans hvState⟩


/-- Direct AB adapter from the current clean_AB theorem to the middle
AProtected/BProtected interface.  No CLEAN transition is unfolded here. -/
theorem clean_AB_protected
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal r) :
    let q :=
      PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 l r
    ZZSafeN4ReversedMiddleGPT.AProtected leaderBit q.1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected bulletVal q.2 := by
  have hl' := hl
  have hr' := hr
  rcases hl' with
    ⟨hlQuiet, hlLeader, hlProbe, hlPhase, hlSignal, hlBullet,
      hlShield, hlPath4, hlPath5⟩
  rcases hlQuiet with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr' with
    ⟨hrQuiet, hrLeader, hrProbe, hrPhase, hrSignal, hrBullet,
      hrShield, hrPath4, hrPath5⟩
  rcases hrQuiet with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  have hc :=
    ZZSafeN4ReversedCleanGPT.clean_AB l r
      hlLabel hrLabel hlPath hrPath
      hlPath4 hlPath5 hrPath4 hrPath5
  dsimp only at hc ⊢
  rcases hc with
    ⟨hqLPath, hqRPath, hqLView, hqRView,
      hqL4, hqL5, hqR4, hqR5⟩
  exact
    ⟨AProtected_of_cleanProtectedView_eq leaderBit
        (PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 l r).1 l
        hqLView hqLPath (Or.inr hqL4) hqL5 hl,
     BProtected_of_cleanProtectedView_eq bulletVal
        (PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 l r).2 r
        hqRView hqRPath hqR4 (Or.inr hqR5) hr⟩


/-- Direct BA adapter from the current clean_BA theorem to the middle
BProtected/AProtected interface.  No CLEAN transition is unfolded here. -/
theorem clean_BA_protected
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit r) :
    let q :=
      PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 l r
    ZZSafeN4ReversedMiddleGPT.BProtected bulletVal q.1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected leaderBit q.2 := by
  have hl' := hl
  have hr' := hr
  rcases hl' with
    ⟨hlQuiet, hlLeader, hlProbe, hlPhase, hlSignal, hlBullet,
      hlShield, hlPath4, hlPath5⟩
  rcases hlQuiet with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr' with
    ⟨hrQuiet, hrLeader, hrProbe, hrPhase, hrSignal, hrBullet,
      hrShield, hrPath4, hrPath5⟩
  rcases hrQuiet with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  have hc :=
    ZZSafeN4ReversedCleanGPT.clean_BA l r
      hlLabel hrLabel hlPath hrPath
      hlPath4 hlPath5 hrPath4 hrPath5
  dsimp only at hc ⊢
  rcases hc with
    ⟨hqLPath, hqRPath, hqLView, hqRView,
      hqL4, hqL5, hqR4, hqR5⟩
  exact
    ⟨BProtected_of_cleanProtectedView_eq bulletVal
        (PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 l r).1 l
        hqLView hqLPath hqL4 (Or.inl hqL5) hl,
     AProtected_of_cleanProtectedView_eq leaderBit
        (PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 l r).2 r
        hqRView hqRPath (Or.inl hqR4) hqR5 hr⟩


end ZZSafeN4ReversedViewAdaptersGPT


#print axioms ZZSafeN4ReversedViewAdaptersGPT.protected_to_ABPrefixRole
#print axioms ZZSafeN4ReversedViewAdaptersGPT.protected_to_BAPrefixRole
#print axioms ZZSafeN4ReversedViewAdaptersGPT.prefixPairView_transport_AB
#print axioms ZZSafeN4ReversedViewAdaptersGPT.prefixPairView_transport_BA
#print axioms ZZSafeN4ReversedViewAdaptersGPT.clean_AB_protected
#print axioms ZZSafeN4ReversedViewAdaptersGPT.clean_BA_protected
