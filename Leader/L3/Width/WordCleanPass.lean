import Leader.L3.Width.WordCleanClose

/-!
# Width W clean clock, part 4: the worker pass and the renewal retry clock

Ported BankWordPass, BankWordRenewalRetry, BankWordRenewalRetryClock, BankWordPassValues and BankWordPassMonitor declarations.
Every declaration is the width port of the BANK declaration named in its
docstring (via SmallWordClean*): band premise `5 ≤ n`, start class
`WidthWordSerializerRootClass` (the fixed physical root), renewal
constants in the compiled width t; see WidthWordCleanBand.
-/

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassResponderFlag`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassIncomingDoneCompletes`, `widthWordPassPrefixStep`, `widthWordPassReadyStep`.
 Post-E flag of the responder at a selected edge, from the fixed
root: the responder is the leader iff it is the root. -/
theorem widthWordPassResponderFlag {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n) :
    (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l =
      decide (ring.rightNeighbor e = root) := by
  have hn2 : 2 ≤ n := by omega
  have hfixed := widthWordEpochFixedRootNext ring hn hsmallFive root s hs z hz e
  rcases clockPostTrichotomy ring root z.2.1 e hn2 hfixed with
    ⟨he, _, hpy⟩ | ⟨hj, _, hpy⟩ | ⟨_, hnj, _, hpy⟩
  · rw [hpy]
    have hj : ring.rightNeighbor e ≠ root := by
      rw [he]
      exact clockNeighborDifferent ring hn2 root
    simp [hj]
  · rw [hpy]
    simp [hj]
  · rw [hpy]
    simp [hnj]

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassPrefixStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassStep`. -/
theorem widthWordPassPrefixStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
        bankWordPassRank ring root z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  have hsh₀ := hsh
  have hnom := bankWordPassNominationHost ring root z w hw (Or.inl hphase)
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  have hflags := bankWordPassFlagsQuiet (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    (hN e) (hN _) hno
  obtain ⟨hfa, hfl, hfr⟩ := hflags
  have hnoroot := widthWordRenewalFrontierShapePrefixNoRoot ring root z hsmallFive hsh w hw hphase
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨htarget, hindex, hindexn, hhost, hk, hb, hc, hjv, hother⟩ := hfields
  rw [hnom]
  constructor
  · intro he
    have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]
        exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
    obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
    exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    rw [← he] at hk hb hc hjv hhost hother hnoroot
    have hne := clockNeighborDifferent ring hn2 e
    have hyfree := hother _ hne
    have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
      rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
      simp [hnoroot]
    have hsucc : ring.rightNeighbor e = L3.EWord.site ring root (w.index + 1) := by
      rw [hhost]
      exact L3.EWord.siteSuccessor ring root w.index
    by_cases hidx : w.index < (compileAdvice (ceilLogTwo n)).t
    · -- P1
      have hj : (z.2.1 e).si.j.val < (compileAdvice (ceilLogTwo n)).t := by
        rw [hjv]; exact hidx
      obtain ⟨hrow, hx, hyk, hyb, hyc, hyj, _⟩ :=
        bankWordPassPrefixAdvanceFields _ _ hfa hfl hfr hk hb hc hj hpy hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostPrefixAdvance root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hjv
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight]
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si = offSI _ := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨by rw [ht']; exact htarget, by omega, by omega,
          by rw [hh', hi', hsucc], ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; exact hyk
        · rw [hh', hsiTarget]; exact hyb
        · rw [hh', hsiTarget]; exact hyc
        · rw [hh', hsiTarget, hyj, hjv, hi']
        · intro i hi
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeOff _
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨hb', _⟩ | hs'
        · rw [hp'] at hb'; cases hb'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        generalize (n - (compileAdvice (ceilLogTwo n)).t - 1) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · -- P3
      have hidxt : w.index = (compileAdvice (ceilLogTwo n)).t := by omega
      have hj : (z.2.1 e).si.j.val = (compileAdvice (ceilLogTwo n)).t := by
        rw [hjv]; exact hidxt
      obtain ⟨hrow, hx, hy, _⟩ :=
        bankWordPassPrefixHandoffFields _ _ hfa hfl hfr hk hb hc hj hpy hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostPrefixHandoff root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hidxt
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          launchRootBack _ := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si = offSI _ := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      have hsite : ring.rightNeighbor e =
          L3.EWord.site ring root ((compileAdvice (ceilLogTwo n)).t + 1) := by
        rw [hsucc, hidxt]
      have hoff : PPL.cyclicOffset ring root (ring.rightNeighbor e) =
          (compileAdvice (ceilLogTwo n)).t + 1 := by
        rw [hsite]
        exact L3.EWord.validationSiteOffset ring root _ (by omega)
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨(compileAdvice (ceilLogTwo n)).t + 1, Nat.le_refl _, by omega,
          by rw [hi']; omega, by rw [hi']; exact Nat.le_refl _, by rw [ht']; exact hsite,
          by rw [hh', hi', Nat.sub_self, Nat.sub_zero]; exact hsite, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; rfl
        · rw [hh', hsiTarget, hi']; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [hh', ht', if_pos rfl, hsiTarget]; rfl
        · intro i hi _
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeOff _
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨_, hne'⟩ | hs'
        · exact absurd (hh'.trans ht'.symm) hne'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi', hidxt]
        have h1 : n - 1 - ((compileAdvice (ceilLogTwo n)).t + 1) =
            n - (compileAdvice (ceilLogTwo n)).t - 2 := by omega
        have h2 : n - (compileAdvice (ceilLogTwo n)).t - 1 =
            (n - (compileAdvice (ceilLogTwo n)).t - 2) + 1 := by omega
        rw [h1, h2, Nat.add_mul, Nat.one_mul]
        generalize (n - (compileAdvice (ceilLogTwo n)).t - 2) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassBackStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassStep`. -/
theorem widthWordPassBackStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .backRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
        bankWordPassRank ring root z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  have hsh₀ := hsh
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hne := clockNeighborDifferent ring hn2 e
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hipos, hit, htarget, hhost, hcur, hjv, htk, htb, hhk, hother⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hnom : bankWordPassNomination ring root z =
      L3.EWord.site ring root
        (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1) := by
    rw [bankWordPassNominationBack ring root z w hw hphase, hoff]
  have hsuccm : ring.rightNeighbor
      (L3.EWord.site ring root (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)) =
      w.host := by
    rw [hhost, L3.EWord.siteSuccessor]
    congr 1
    omega
  have hTQ' : w.host ≠ w.target → (z.2.1 w.target).si.cur = .NONE :=
    fun hne' => hTQ w hw (Or.inl ⟨hphase, hne'⟩)
  have hhostkind : w.host ≠ w.target → (z.2.1 w.host).si.kind = .OFF := by
    intro hne'
    have := hhk
    rw [if_neg hne'] at this
    exact this
  have hhostroot : w.host = w.target → (z.2.1 w.host).si.kind = .ROOT := by
    intro heq
    have := hhk
    rw [if_pos heq] at this
    exact this
  rw [hnom]
  constructor
  · intro he
    by_cases heh : e = w.host
    · by_cases hht : w.host = w.target
      · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBusySource _ _ hfa hfl hfr
          (by rw [heh]; exact hhostroot hht) (by rw [heh, hht]; exact htb)
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
      · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBackSource _ _ hfa hfl hfr
          (by rw [heh]; exact hhostkind hht) (by rw [heh]; exact hcur)
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
    · by_cases het : e = w.target
      · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBusySource _ _ hfa hfl hfr
          (by rw [het]; exact htk) (by rw [het]; exact htb)
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
      · have hxfree := hother e heh het
        obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
        have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
          by_cases hj : ring.rightNeighbor e = w.host
          · exfalso
            apply he
            apply bankWordPassRightNeighborInjective ring
            rw [hj, hsuccm]
          · by_cases hjt : ring.rightNeighbor e = w.target
            · rw [hjt, hTQ' (fun h => hj (hjt.trans h.symm))]
              exact fun h => by cases h
            · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
              exact fun h => by cases h
        obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    have hrne : ring.rightNeighbor e = w.host := by rw [he]; exact hsuccm
    have hem : e ≠ w.host := by
      rw [he, hhost]
      exact bankWordPassSiteNe ring root _ _ (by omega) (by omega) (by omega)
    have het : e ≠ w.target := by
      rw [he, htarget]
      exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
    have hxfree := hother e hem het
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hykind : (z.2.1 (ring.rightNeighbor e)).si.kind ≠ .PREFIX := by
      rw [hrne]
      by_cases hht : w.host = w.target
      · rw [hhostroot hht]; exact fun h => by cases h
      · rw [hhostkind hht]; exact fun h => by cases h
    have hycur : (z.2.1 (ring.rightNeighbor e)).si.cur = .BACK := by rw [hrne]; exact hcur
    have hyj : (z.2.1 (ring.rightNeighbor e)).si.j.val = w.index := by rw [hrne]; exact hjv
    have hsiTargetRec : ∀ hht : w.host ≠ w.target,
        (bankWordEpochNext ring root z e).2.1 w.target = z.2.1 w.target := by
      intro hht
      exact bankWordPassRemoteRecord ring root z e _ (Ne.symm het)
        (by rw [hrne]; exact Ne.symm hht)
    by_cases hi1 : 1 < w.index
    · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassBackMoveFields _ _ hfa hfl hfr hxfree hycur
        (by rw [hyj]; exact hi1) hykind
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostBackMove root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hyj
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si =
          setCursor (z.2.1 e).si .BACK (w.index - 1) false false true := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx, hyj]
      have hsiHost : ((bankWordEpochNext ring root z e).2.1 w.host).si =
          clearCursor (z.2.1 w.host).si := by
        rw [← hrne, bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      have hjval : (setCursor (z.2.1 e).si .BACK (w.index - 1) false false true).j.val =
          w.index - 1 := by
        have hlt : w.index - 1 < (compileAdvice (ceilLogTwo n)).t + 1 := by omega
        simp [setCursor, siJ, hlt]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by omega, by omega, by rw [ht']; exact htarget, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', he, hi']
          congr 1
          omega
        · rw [hh', hsiSource]; rfl
        · rw [hh', hsiSource, hi']; exact hjval
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.kind = _; rw [hht]; exact htk
          · rw [hsiTargetRec hht]; exact htk
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.busy = _; rw [hht]; exact htb
          · rw [hsiTargetRec hht]; exact htb
        · rw [hh', ht', if_neg het, hsiSource]
          show (z.2.1 e).si.kind = _
          exact hxk
        · intro i hi hit'
          rw [hh'] at hi
          rw [ht'] at hit'
          by_cases hih : i = w.host
          · subst hih
            rw [hsiHost]
            exact bankWordPassFreeClear _ (hhostkind hit')
          · rw [bankWordPassRemoteRecord ring root z e i hi (by rw [hrne]; exact hih)]
            exact hother i hih hit'
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨_, hne'⟩ | hs'
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; rfl
          · rw [hsiTargetRec hht]; exact hTQ' hht
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi']
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · have hi : w.index = 1 := by omega
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassBackInitFields _ _ hfa hfl hfr hxfree hycur
        (by rw [hyj]; exact hi) hykind
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostBackInit root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hi
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si =
          setCursor (z.2.1 e).si .SUM 0 false false true := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      have hsiHost : ((bankWordEpochNext ring root z e).2.1 w.host).si =
          clearCursor (z.2.1 w.host).si := by
        rw [← hrne, bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by omega, by rw [ht']; exact htarget, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', he, hi', hi]
          congr 1
          omega
        · rw [hh', hsiSource]; show (z.2.1 e).si.kind = _; exact hxk
        · rw [hh', hsiSource]; rfl
        · rw [hh', hsiSource, hi']; simp [setCursor, siJ]
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.kind = _; rw [hht]; exact htk
          · rw [hsiTargetRec hht]; exact htk
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.busy = _; rw [hht]; exact htb
          · rw [hsiTargetRec hht]; exact htb
        · intro i hi hit'
          rw [hh'] at hi
          rw [ht'] at hit'
          by_cases hih : i = w.host
          · subst hih
            rw [hsiHost]
            exact bankWordPassFreeClear _ (hhostkind hit')
          · rw [bankWordPassRemoteRecord ring root z e i hi (by rw [hrne]; exact hih)]
            exact hother i hih hit'
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨hb', _⟩ | _
        · rw [hp'] at hb'; cases hb'
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; rfl
          · rw [hsiTargetRec hht]; exact hTQ' hht
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi', hi]
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassSumStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassStep`. -/
theorem widthWordPassSumStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
        bankWordPassRank ring root z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  have hsh₀ := hsh
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hne := clockNeighborDifferent ring hn2 e
  have hnom := bankWordPassNominationHost ring root z w hw (Or.inr (Or.inl hphase))
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hit, htarget, hhost, hk, hc, hjv, htk, htb, hother⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hTQ' : (z.2.1 w.target).si.cur = .NONE := hTQ w hw (Or.inr hphase)
  have hht : w.host ≠ w.target := by
    rw [hhost, htarget]
    exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
  rw [hnom]
  constructor
  · intro he
    by_cases het : e = w.target
    · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBusySource _ _ hfa hfl hfr
        (by rw [het]; exact htk) (by rw [het]; exact htb)
      obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
      exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
    · have hxfree := hother e he het
      obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
      have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
        by_cases hj : ring.rightNeighbor e = w.host
        · rw [hj, hc]; exact fun h => by cases h
        · by_cases hjt : ring.rightNeighbor e = w.target
          · rw [hjt, hTQ']; exact fun h => by cases h
          · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
            exact fun h => by cases h
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
      obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
      exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    rw [← he] at hk hc hjv hhost hother hht
    have hsucc : ring.rightNeighbor e =
        L3.EWord.site ring root (k - (compileAdvice (ceilLogTwo n)).t + w.index + 1) := by
      rw [hhost]
      exact L3.EWord.siteSuccessor ring root _
    have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si =
        clearCursor (z.2.1 e).si := by
      rw [bankWordPassSourceRecord, bankWordPassPairSILeft]
      by_cases hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t
      · have hyne : ring.rightNeighbor e ≠ w.target := by
          rw [hsucc, htarget]
          exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
        exact (bankWordPassSumMoveFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidx)
          (hother _ hne hyne)).2.1
      · have hidxt : w.index + 1 = (compileAdvice (ceilLogTwo n)).t := by omega
        have hyt : ring.rightNeighbor e = w.target := by
          rw [hsucc, htarget]
          congr 1
          omega
        exact (bankWordPassSumPublishFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidxt)
          (by rw [hyt]; exact htk) (by rw [hyt]; exact htb)).2.1
    by_cases hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t
    · have hyne : ring.rightNeighbor e ≠ w.target := by
        rw [hsucc, htarget]
        exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
      have hyfree := hother _ hne hyne
      obtain ⟨hrow, hx, hyk, hyb, hyc, hyj, _⟩ :=
        bankWordPassSumMoveFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidx) hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostSumMove root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hjv
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight]
      have hT : (bankWordEpochNext ring root z e).2.1 w.target = z.2.1 w.target :=
        bankWordPassRemoteRecord ring root z e _ (Ne.symm (hht)) (Ne.symm hyne)
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by omega, by rw [ht']; exact htarget,
          by rw [hh', hi', hsucc]; congr 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget, hyk]; exact (bankWordPassFreeFields _ hyfree).1
        · rw [hh', hsiTarget]; exact hyc
        · rw [hh', hsiTarget, hyj, hjv, hi']
        · rw [ht', hT]; exact htk
        · rw [ht', hT]; exact htb
        · intro i hi hit'
          rw [hh'] at hi
          rw [ht'] at hit'
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeClear _ hk
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie hit'
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rw [ht', hT]
        exact hTQ'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi']
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · have hidxt : w.index + 1 = (compileAdvice (ceilLogTwo n)).t := by omega
      have hyt : ring.rightNeighbor e = w.target := by
        rw [hsucc, htarget]
        congr 1
        omega
      obtain ⟨hrow, hx, hyk, hyb, hyc, _⟩ :=
        bankWordPassSumPublishFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidxt)
          (by rw [hyt]; exact htk) (by rw [hyt]; exact htb)
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostSumPublish root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hyt.symm hjv
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by rw [hh', hsucc]; congr 1; omega,
          by rw [ht', hh', hyt], ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; exact hyk
        · rw [hh', hsiTarget]; exact hyb
        · rw [hh', hsiTarget]; exact hyc
        · intro i hi
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeClear _ hk
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie (by rw [← hyt]; exact hi)
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨hb', _⟩ | hs'
        · rw [hp'] at hb'; cases hb'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff]
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassReadyStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassStep`, `widthWordPassValuesReadyAllStep`. -/
theorem widthWordPassReadyStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .readyRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      (BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
        bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
          bankWordPassRank ring root z) ∨
      BankWordPassRetired ring root (bankWordEpochNext ring root z e)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  have hsh₀ := hsh
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hne := clockNeighborDifferent ring hn2 e
  have hnom := bankWordPassNominationHost ring root z w hw (Or.inr (Or.inr hphase))
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hhost, htarget, hk, hb, hc, hother⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget, hhost]
    exact L3.EWord.validationSiteOffset ring root k hkn
  rw [hnom]
  constructor
  · intro he
    have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]; exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
    obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
    exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    rw [← he] at hk hb hc hhost hother
    have hyfree := hother _ hne
    have hsucc : ring.rightNeighbor e = L3.EWord.site ring root (k + 1) := by
      rw [hhost]
      exact L3.EWord.siteSuccessor ring root k
    have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si = offSI _ := by
      rw [bankWordPassSourceRecord, bankWordPassPairSILeft]
      by_cases hkn1 : k + 1 < n
      · have hnotroot : ring.rightNeighbor e ≠ root := by
          rw [hsucc]
          have := bankWordPassSiteNe ring root (k + 1) 0 hkn1 (by omega) (by omega)
          rw [L3.EWord.siteZero] at this
          exact this
        have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
          rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
          simp [hnotroot]
        exact (bankWordPassAdvanceFields _ _ hfa hfl hfr hk hb hc hpy hyfree).2.1
      · have hkn' : k + 1 = n := by omega
        have hroot : ring.rightNeighbor e = root := by
          rw [hsucc, hkn']
          exact bankWordPassSiteWrap ring root
        have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
          rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
          simp [hroot]
        exact (bankWordPassTerminalFields _ _ hfa hfl hfr hk hb hc hpy hyfree).2.1
    by_cases hkn1 : k + 1 < n
    · left
      have hnotroot : ring.rightNeighbor e ≠ root := by
        rw [hsucc]
        have := bankWordPassSiteNe ring root (k + 1) 0 hkn1 (by omega) (by omega)
        rw [L3.EWord.siteZero] at this
        exact this
      have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
        rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
        simp [hnotroot]
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassAdvanceFields _ _ hfa hfl hfr hk hb hc hpy hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostAdvance root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          launchRootBack _ := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      have hoff' : PPL.cyclicOffset ring root (ring.rightNeighbor e) = k + 1 := by
        rw [hsucc]
        exact L3.EWord.validationSiteOffset ring root _ hkn1
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k + 1, by omega, hkn1, by rw [hi']; omega, by rw [hi']; exact Nat.le_refl _,
          by rw [ht']; exact hsucc,
          by rw [hh', hi', Nat.sub_self, Nat.sub_zero]; exact hsucc, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; rfl
        · rw [hh', hsiTarget, hi']; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [hh', ht', if_pos rfl, hsiTarget]; rfl
        · intro i hi _
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeOff _
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨_, hne'⟩ | hs'
        · exact absurd (hh'.trans ht'.symm) hne'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff', hi', hoff]
        have h1 : n - 1 - (k + 1) = n - k - 2 := by omega
        have h2 : n - 1 - k = (n - k - 2) + 1 := by omega
        rw [h1, h2, Nat.add_mul, Nat.one_mul]
        generalize (n - k - 2) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · right
      have hkn' : k + 1 = n := by omega
      have hroot : ring.rightNeighbor e = root := by
        rw [hsucc, hkn']
        exact bankWordPassSiteWrap ring root
      have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
        rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
        simp [hroot]
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassTerminalFields _ _ hfa hfl hfr hk hb hc hpy hyfree
      obtain ⟨hwnone, hcomp⟩ :=
        bankWordPassGhostTerminal root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hroot
      refine ⟨hN', ?_, ⟨{ service := z.2.2.clock + 1, worker := w }, ?_⟩, ?_⟩
      · rw [bankWordPassGhostWorker, hw]; exact hwnone
      · rw [bankWordPassGhostCompletion, hw]; exact hcomp
      · intro i
        by_cases hie : i = e
        · subst hie
          rw [hsiSource]
          exact bankWordPassFreeOff _
        · by_cases hij : i = ring.rightNeighbor e
          · subst hij
            rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
            exact hyfree
          · rw [bankWordPassRemoteRecord ring root z e i hie hij]
            exact hother i hie

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassRankWord`, `widthWordPassValuesRun`, `widthWordRetryPrefixStep`.
 The Layer G all-edges step: on every edge without a hard S1 the
pass shape is kept; a non-nominated edge keeps the trail (hence the
rank and the nomination), the nominated edge lowers the rank by one or
retires the pass with a completion receipt and every SI free.
Consumer: `widthWordPassRankWord`. -/
theorem widthWordPassStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hpass : BankWordPassShape ring root z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = z.2.2.worker) ∧
    (e = bankWordPassNomination ring root z →
      (BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
        bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
          bankWordPassRank ring root z) ∨
      BankWordPassRetired ring root (bankWordEpochNext ring root z e)) := by
  obtain ⟨hN, hsh, hTQ⟩ := hpass
  have hsh₀ := hsh
  obtain ⟨w, hw, _⟩ := hsh₀
  cases hphase : w.phase with
  | prefixRun =>
      obtain ⟨h1, h2⟩ := widthWordPassPrefixStep ring hn hsmallFive root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, fun he => Or.inl (h2 he)⟩
  | backRun =>
      obtain ⟨h1, h2⟩ := widthWordPassBackStep ring hn hsmallFive root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, fun he => Or.inl (h2 he)⟩
  | sumRun =>
      obtain ⟨h1, h2⟩ := widthWordPassSumStep ring hn hsmallFive root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, fun he => Or.inl (h2 he)⟩
  | readyRun =>
      obtain ⟨h1, h2⟩ := widthWordPassReadyStep ring hn hsmallFive root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, h2⟩

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassRankWord`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassWorkerHitsBelowQuota`.
 The rank word: along any no-hard-S1 word from a pass state, either
the pass is still on and the nominated hits are paid by the rank drop,
or the pass has completed.  Consumer: (C*) of the retry estimate
(`widthWordRenewalWorkerNominationHalf` with this nomination). -/
theorem widthWordPassRankWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n),
      BankWordEpochReachable ring root s z →
      BankWordPassShape ring root z →
      BankWordPassNoHardStart ring root z word →
      (BankWordPassShape ring root
          (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root) z word) ∧
        L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
            (bankWordPassNomination ring root) z word +
          bankWordPassRank ring root
            (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root) z word) ≤
          bankWordPassRank ring root z) ∨
      BankWordPassCompletes ring root z word := by
  intro word
  induction word with
  | nil =>
      intro z _ hpass _
      exact Or.inl ⟨hpass, by
        simp only [L3.GrantDrainEntrance.grantDrainLabelHits,
          L3.GrantDrainEntrance.grantDrainLabelRun, Nat.zero_add]
        exact Nat.le_refl _⟩
  | cons e es ih =>
      intro z hz hpass hnh
      obtain ⟨hno, hnh'⟩ := hnh
      obtain ⟨hframe, hnom⟩ := widthWordPassStep ring hn hsmallFive root s hs z hz e hpass hno
      have hz' := bankWordEpochReachableNext ring root s z hz e
      by_cases he : e = bankWordPassNomination ring root z
      · rcases hnom he with ⟨hpass', hrank⟩ | hret
        · rcases ih _ hz' hpass' hnh' with ⟨hpassEnd, hcount⟩ | hcomp
          · left
            refine ⟨hpassEnd, ?_⟩
            show (if e = bankWordPassNomination ring root z then 1 else 0) +
              L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
                (bankWordPassNomination ring root) (bankWordEpochNext ring root z e) es +
              bankWordPassRank ring root
                (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root)
                  (bankWordEpochNext ring root z e) es) ≤ _
            rw [if_pos he]
            omega
          · exact Or.inr (Or.inr hcomp)
        · exact Or.inr (Or.inl hret)
      · obtain ⟨hpass', hw'⟩ := hframe he
        have hrank := bankWordPassRankOfWorkerEq ring root z _ hw'
        rcases ih _ hz' hpass' hnh' with ⟨hpassEnd, hcount⟩ | hcomp
        · left
          refine ⟨hpassEnd, ?_⟩
          show (if e = bankWordPassNomination ring root z then 1 else 0) +
            L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
              (bankWordPassNomination ring root) (bankWordEpochNext ring root z e) es +
            bankWordPassRank ring root
              (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root)
                (bankWordEpochNext ring root z e) es) ≤ _
          rw [if_neg he]
          omega
        · exact Or.inr (Or.inr hcomp)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassLaunchRankBound`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassWorkerHitsBelowQuota`.
 The launch rank `(t+1) + (n-t-1)(2t+1)` is below `(2t+1) n`.
Consumer: (C*) with the worker quota `C n`. -/
theorem widthWordPassLaunchRankBound {n : Nat}
    (hsmallFive : 5 ≤ n) :
    ((compileAdvice (ceilLogTwo n)).t + 1) +
        (n - (compileAdvice (ceilLogTwo n)).t - 1) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) <
      (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n := by
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  generalize hT : (compileAdvice (ceilLogTwo n)).t = t at ht2 hroom
  have hsplit : (2 * t + 1) * n =
      (2 * t + 1) * (t + 1) + (2 * t + 1) * (n - t - 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hfirst : t + 1 < (2 * t + 1) * (t + 1) := by
    have hpos : 0 < t + 1 := by omega
    have := Nat.mul_lt_mul_of_pos_right (by omega : 1 < 2 * t + 1) hpos
    rw [Nat.one_mul] at this
    exact this
  rw [hsplit, Nat.mul_comm (n - t - 1) (2 * t + 1)]
  omega

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassWorkerHitsBelowQuota`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassFreshWorkerHitsBelowQuota`.
 (C*) at the pass level: from a launch state, a no-hard-S1 word that
does not complete the pass has fewer than `(2t+1) n` nominated hits.
Consumer: the worker half of the first-H retry cover. -/
theorem widthWordPassWorkerHitsBelowQuota {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpass : BankWordPassShape ring root z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun) (hindex : w.index = 0)
    (word : List (Fin n))
    (hnh : BankWordPassNoHardStart ring root z word)
    (hnc : ¬ BankWordPassCompletes ring root z word) :
    L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
        (bankWordPassNomination ring root) z word <
      (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n := by
  rcases widthWordPassRankWord ring hn hsmallFive root s hs word z hz hpass hnh with
    ⟨_, hcount⟩ | hcomp
  · rw [bankWordPassRankAtLaunch ring root z w hw hphase hindex] at hcount
    have := widthWordPassLaunchRankBound hsmallFive
    omega
  · exact absurd hcomp hnc

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassIncomingDoneCompletes`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRetryRootLeaseStep`.
 On the pass, a ROOT_IN service with a physical `done` is the
tracked A0 and produces the completion receipt: there is no stray
P0/P2/done before completion.  Consumer: the hnoStrayDone premise of
the (A*) half. -/
theorem widthWordPassIncomingDoneCompletes {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpass : BankWordPassShape ring root z) (e : Fin n)
    (hpred : ring.rightNeighbor e = root)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false)
    (hd : (bankWordEpochSelectedReceipt ring z e).worker.done = true) :
    BankWordRenewalCompleted (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  obtain ⟨hN, hsh, _⟩ := hpass
  have hsh₀ := hsh
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hd' : (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).done = true := hd
  have hclass := bankWordPassDoneClassify _ _ hfa hfl hfr hd'
  obtain ⟨w, hw, hfields⟩ := hsh
  cases hphase : w.phase with
  | prefixRun =>
      exfalso
      simp only [hphase] at hfields
      obtain ⟨_, _, _, _, hk, _, _, _, hother⟩ := hfields
      have hnoroot := widthWordRenewalFrontierShapePrefixNoRoot ring root z hsmallFive hsh₀ w hw hphase
      by_cases he : e = w.host
      · subst he
        exact hnoroot hpred
      · have hfree := bankWordPassFreeFields _ (hother e he)
        rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
        · rw [hfree.1] at hkp; cases hkp
        · rw [hfree.1] at hkr; cases hkr
  | backRun =>
      exfalso
      simp only [hphase] at hfields
      obtain ⟨k, _, _, _, _, _, _, _, _, htk, htb, hhk, hother⟩ := hfields
      by_cases he : e = w.host
      · by_cases hht : w.host = w.target
        · have hkr : (z.2.1 e).si.kind = .ROOT := by
            rw [he]; have := hhk; rw [if_pos hht] at this; exact this
          have hbusy : (z.2.1 e).si.busy = true := by rw [he, hht]; exact htb
          rcases hclass with ⟨hkp, _⟩ | ⟨_, hb, _⟩
          · rw [hkr] at hkp; cases hkp
          · rw [hbusy] at hb; cases hb
        · have hko : (z.2.1 e).si.kind = .OFF := by
            rw [he]; have := hhk; rw [if_neg hht] at this; exact this
          rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
          · rw [hko] at hkp; cases hkp
          · rw [hko] at hkr; cases hkr
      · by_cases het : e = w.target
        · have hbusy : (z.2.1 e).si.busy = true := by rw [het]; exact htb
          have hkr : (z.2.1 e).si.kind = .ROOT := by rw [het]; exact htk
          rcases hclass with ⟨hkp, _⟩ | ⟨_, hb, _⟩
          · rw [hkr] at hkp; cases hkp
          · rw [hbusy] at hb; cases hb
        · have hfree := bankWordPassFreeFields _ (hother e he het)
          rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
          · rw [hfree.1] at hkp; cases hkp
          · rw [hfree.1] at hkr; cases hkr
  | sumRun =>
      exfalso
      simp only [hphase] at hfields
      obtain ⟨k, _, _, _, _, _, hk, _, _, htk, htb, hother⟩ := hfields
      by_cases he : e = w.host
      · have hko : (z.2.1 e).si.kind = .OFF := by rw [he]; exact hk
        rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
        · rw [hko] at hkp; cases hkp
        · rw [hko] at hkr; cases hkr
      · by_cases het : e = w.target
        · have hbusy : (z.2.1 e).si.busy = true := by rw [het]; exact htb
          have hkr : (z.2.1 e).si.kind = .ROOT := by rw [het]; exact htk
          rcases hclass with ⟨hkp, _⟩ | ⟨_, hb, _⟩
          · rw [hkr] at hkp; cases hkp
          · rw [hbusy] at hb; cases hb
        · have hfree := bankWordPassFreeFields _ (hother e he het)
          rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
          · rw [hfree.1] at hkp; cases hkp
          · rw [hfree.1] at hkr; cases hkr
  | readyRun =>
      simp only [hphase] at hfields
      obtain ⟨k, _, _, _, _, hk, hb, hc, hother⟩ := hfields
      by_cases he : e = w.host
      · rw [← he] at hk hb hc hother
        have hyfree := hother _ hne
        have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
          rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
          simp [hpred]
        obtain ⟨hrow, _, _, _⟩ := bankWordPassTerminalFields _ _ hfa hfl hfr hk hb hc hpy hyfree
        obtain ⟨_, hcomp⟩ :=
          bankWordPassGhostTerminal root e (ring.rightNeighbor e)
            (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
              (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
            w hrow hno hphase he.symm hpred
        refine ⟨{ service := z.2.2.clock + 1, worker := w }, ?_⟩
        rw [bankWordPassGhostCompletion, hw]
        exact hcomp
      · exfalso
        have hfree := bankWordPassFreeFields _ (hother e he)
        rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
        · rw [hfree.1] at hkp; cases hkp
        · rw [hfree.1] at hkr; cases hkr

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassNonvalidatingAfterGenuine`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassShapeAtFreshSeed`.
 J-N immediately after ANY represented, genuinely ticketed
hard S6 (including the first one). The joined DONE ticket has an
actual earlier hard-S1 origin; its intervening nonaccepting word
carries EWord.WValidationHistory, hence a RETURN shape at the
accepting prestate. No premise of previous S6s or prior J-N is used.
Consumer: fresh-seed BankWordPassShape, then the worker (C*) bound. -/
theorem widthWordPassNonvalidatingAfterGenuine
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hg : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    BankWordPassNonvalidating
      (bankWordEpochNext ring root z e) := by
  obtain ⟨he, _, ha⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root z e hg
  subst e
  obtain ⟨ticket, child, hdone, _, _, _⟩ :=
    bankWordHardEpochGenuineJoinedStamps
      ring root (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) hg
  have hrootTicket :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
          some ticket := by
    exact hdone
  have horigin :=
    (widthWordRootDoneOriginReachable
      ring hn hsmallFive root s hs z hz) ticket hrootTicket
  obtain ⟨pre, mid, request, hstate, hreq, hzero,
    hrequested, hrequestStamp, hstartStamp, hhard, hmid⟩ :=
      horigin
  have hpre : BankWordEpochReachable ring root s
      (bankWordEpochRun ring root (bankWordEpochStart s) pre) :=
    ⟨pre, rfl⟩
  obtain ⟨g, hhistory⟩ :=
    widthWordTicketHardStartThroughWord
      ring hn hsmallFive root s hs
      (bankWordEpochRun ring root (bankWordEpochStart s) pre)
      hpre hreq hzero mid hmid
  have hdecomp :
      bankWordEpochRun ring root (bankWordEpochStart s)
          (pre ++ [root] ++ mid) =
        bankWordEpochRun ring root
          (bankWordEpochNext ring root
            (bankWordEpochRun ring root
              (bankWordEpochStart s) pre) root) mid := by
    rw [bankWordRootRunAppend, bankWordEpochRunSnoc]
  have heq :
      z = bankWordEpochRun ring root
        (bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochStart s) pre) root) mid :=
    hstate.trans hdecomp
  have hhistoryZ :
      L3.EWord.WValidationHistory ring root z.2.1 g := by
    rw [heq]
    exact hhistory
  have hshape :
      L3.EWord.ValidationShape ring root z.2.1 g :=
    L3.EWord.validationReachableShape
      ring root hhistoryZ
  have haccept :
      (serW (z.2.1 root)
        (z.2.1 (ring.rightNeighbor root))).hard.hardAccept =
          true := ha
  have hreturn :
      L3.EWord.ReturnShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · have hno :=
        L3.EWord.forwardNoAccept ring root z.2.1 g hf
      rw [haccept] at hno
      cases hno
    · exact hr
  have hclass :=
    widthWordEpochReachablePhysicalRootClass
      ring hn hsmallFive root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass root).2
  have hpost :=
    clockPostOutgoing ring root z.2.1 root
      (by omega : 2 ≤ n) hfixed rfl
  exact bankWordPassNonvalidatingOfReturnAccept
    ring (by omega) root z g hreturn hpost.1 hpost.2 haccept

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassShapeAtFreshSeed`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletedClean`, `widthWordEpochCompletedRetired`, `widthWordPassFreshWorkerHitsBelowQuota`.
 Complete Layer-G base at every actual fresh seed.
J-N comes from the causal RETURN history; physical PREFIX shape
comes from FreshShapeOnBank; TargetQuiet is vacuous for prefixRun.
Consumer: bankWordPassFreshWorkerHitsBelowQuota. -/
theorem widthWordPassShapeAtFreshSeed
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordPassShape ring root seed.1.1 := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have hNold :=
    widthWordPassNonvalidatingAfterGenuine
      ring hn hsmallFive root s hs
      pre.1 pre.2.1 e hgen
  have hN : BankWordPassNonvalidating seed.1.1 := by
    have hstate := congrArg
      (fun v : BankWordRenewalPostSOne ring root s => v.1)
      heq
    change BankWordPassNonvalidating
      (bankWordRenewalNext ring root s pre e).1 at hNold
    rw [hstate] at hNold
    exact hNold
  have hphysical :
      BankWordRenewalFrontierPhysicalShape ring root
        seed.1.1 :=
    widthWordRenewalFrontierFreshShapeOnBank
      ring root s hsmallFive hs seed
  exact ⟨hN, hphysical,
    bankWordPassFreshTargetQuiet ring root s seed⟩

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordPassFreshWorkerHitsBelowQuota`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshRetryCover`.
 Fresh-seed worker nomination quota (C*): on every physical
scheduler word without a hard S1, failure to complete the pass
forces fewer than (2t+1)n nominated worker services. The actual
seed has a prefixRun trail with index zero.
Consumer: the worker half of the R10 W first-H retry cover. -/
theorem widthWordPassFreshWorkerHitsBelowQuota
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n))
    (hnh : BankWordPassNoHardStart ring root seed.1.1 word)
    (hnc : ¬ BankWordPassCompletes ring root seed.1.1 word) :
    L3.GrantDrainEntrance.grantDrainLabelHits
        (bankWordEpochNext ring root)
        (bankWordPassNomination ring root)
        seed.1.1 word <
      (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n := by
  obtain ⟨w, hw, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness
      ring root s seed
  exact widthWordPassWorkerHitsBelowQuota
    ring hn hsmallFive root s hs seed.1.1 seed.1.2.1
    (widthWordPassShapeAtFreshSeed ring hn hsmallFive root s hs seed)
    w hw hp hi word hnh hnc

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRetryPrefixInvariantSeed`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshRetryCover`.
 The invariant at every actual fresh seed, with zero soft finishes
and zero rooted position.  Consumer: `widthWordRenewalFreshRetryCover`. -/
theorem widthWordRetryPrefixInvariantSeed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    WidthWordRetryPrefixInvariant ring root s seed.1 ∧
    (bankWordHardEpochLedger ring root seed.1.1).softFinishes = 0 ∧
    bankWordRenewalSoftRootedPosition ring root seed.1.1 = 0 := by
  have hfields :=
    bankWordRenewalFreshHardFields ring root s seed.1 seed.2
  have hsoft := widthWordRenewalSoftShapeSeed ring root s hn hsmallFive hs seed
  have hidle :=
    widthWordRenewalFrontierFreshRootIdle ring root s hn hsmallFive hs seed
  have hlease :=
    (widthWordRenewalFrontierFreshBankPrepared ring root s hsmallFive seed).2
  have hv := hfields.2.2.2
  unfold bankWordRenewalHardValid bankWordHardEpochActive at hv
  have hep : 0 < (bankWordHardEpochLedger ring root seed.1.1).hardEpochs := by
    rcases Nat.eq_zero_or_pos
        (bankWordHardEpochLedger ring root seed.1.1).hardEpochs with h0 | h0
    · rw [h0] at hv
      simp at hv
    · exact h0
  have hwd : (bankWordHardEpochLedger ring root seed.1.1).workerDone =
      false := by
    cases hw : (bankWordHardEpochLedger ring root seed.1.1).workerDone with
    | false => rfl
    | true =>
        rw [hw] at hv
        simp at hv
  refine ⟨⟨widthWordPassShapeAtFreshSeed ring hn hsmallFive root s hs seed,
    hsoft.1, hep, hwd, ?_, ?_⟩, hfields.2.1, hsoft.2⟩
  · rw [hlease, hfields.2.1, Nat.add_zero]
  · intro h
    rw [hidle] at h
    cases h.1

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRetryRootLeaseStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRetryPrefixStep`.
 The lease ledger and the spendable clause across one service of
the pass that is neither a hard S1 nor a completion.  Remote services
frame the root; ROOT_IN cannot debit the root (its only done is the
completing A0); ROOT_OUT debits exactly at soft acceptance, which is
the counted soft S6.  Consumer: `widthWordRetryPrefixStep`. -/
theorem widthWordRetryRootLeaseStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n)
    (hpass : BankWordPassShape ring root z.1)
    (hno : (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
      false)
    (hnc : ¬ BankWordRenewalCompleted (bankWordRenewalNext ring root s z e).1)
    (hfa : (serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false)
    (hfl : (serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).hard.hardLeft =
      false)
    (hfr : (serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).hard.hardRight =
      false)
    (hlease : (z.1.2.1 root).siLease.val +
        (bankWordHardEpochLedger ring root z.1).softFinishes =
      widthWordRenewalLease n)
    (hK : (z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.wphase = .CURRENT →
      0 < (z.1.2.1 root).siLease.val)
    (hf : (bankWordHardEpochLedger ring root
        (bankWordRenewalNext ring root s z e).1).softFinishes =
      (if bankWordHardEpochSoftFinish root
          (bankWordEpochSelectedReceipt ring z.1 e) = true
        then (bankWordHardEpochLedger ring root z.1).softFinishes + 1
        else (bankWordHardEpochLedger ring root z.1).softFinishes)) :
    ((bankWordRenewalNext ring root s z e).1.2.1 root).siLease.val +
        (bankWordHardEpochLedger ring root
          (bankWordRenewalNext ring root s z e).1).softFinishes =
      widthWordRenewalLease n ∧
    (((bankWordRenewalNext ring root s z e).1.2.1 root).ser.cert = .RUNNING ∧
        ((bankWordRenewalNext ring root s z e).1.2.1 root).ser.wphase =
          .CURRENT →
      0 < ((bankWordRenewalNext ring root s z e).1.2.1 root).siLease.val) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  rcases widthWordRenewalSoftOwnerFlags ring root s hn hsmallFive hs z e with
    ⟨he, hx, hy⟩ | ⟨he, hpred, hx, hy⟩ | ⟨he, hj, hx, hy⟩
  · -- ROOT_OUT at the root
    have hdone : (workerW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).done = false := by
      cases hd : (workerW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).done with
      | false => rfl
      | true =>
          exfalso
          rcases bankWordPassDoneClassify _ _ hfa hfl hfr hd with h | h
          · have h2 := h.2
            rw [hy] at h2
            cases h2
          · have h2 := h.2.2.2.1
            rw [hy] at h2
            cases h2
    rw [he] at hx hy hfa hdone
    have hrec := bankWordPassSourceRecord ring root z.1 root
    change ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val + _ = _ ∧
      (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert = .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase = .CURRENT →
        0 < ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val)
    rw [he] at hf ⊢
    rw [hrec]
    have hleaseEq :
        (pairW (z.1.2.1 root) (z.1.2.1 (ring.rightNeighbor root))).1.siLease =
          (leasePair (compileAdvice (ceilLogTwo n))
            (z.1.2.1 root).siLease
            (z.1.2.1 (ring.rightNeighbor root)).siLease
            (serW (z.1.2.1 root)
              (z.1.2.1 (ring.rightNeighbor root))).hard.hardAccept
            (serW (z.1.2.1 root)
              (z.1.2.1 (ring.rightNeighbor root))).hard.softAccept
            (workerW (z.1.2.1 root)
              (z.1.2.1 (ring.rightNeighbor root))).done).1 := rfl
    rw [hleaseEq, pairW_ser_left, hfa, hdone]
    cases hsa : (serW (z.1.2.1 root)
        (z.1.2.1 (ring.rightNeighbor root))).hard.softAccept with
    | false =>
        have hsf : bankWordHardEpochSoftFinish root
            (bankWordEpochSelectedReceipt ring z.1 root) = false := by
          simp [bankWordHardEpochSoftFinish, bankWordEpochSelectedReceipt, hsa]
        rw [hsf, if_neg (by decide)] at hf
        rw [bankWordRetryLeaseKeep, hf]
        refine ⟨hlease, ?_⟩
        intro hrc
        rcases bankWordRetryRootOutRunningCurrent _ _ hx hy hrc with hreq | hold
        · exact bankWordRetrySoftStartPositive _ _
            (by rw [he] at hno; exact hno) hx hreq
        · exact hK hold
    | true =>
        obtain ⟨hrow, hidle, hrun, _, hcur, _, _⟩ :=
          bankWordRetryRootOutSoftAccept _ _ hx hy hsa
        have hsf : bankWordHardEpochSoftFinish root
            (bankWordEpochSelectedReceipt ring z.1 root) = true := by
          have h' : ((root == root) &&
              ((serW (z.1.2.1 root) (z.1.2.1 (ring.rightNeighbor root))).row ==
                "S6") &&
              (serW (z.1.2.1 root)
                (z.1.2.1 (ring.rightNeighbor root))).hard.softAccept) = true := by
            rw [hrow, hsa]
            simp
          exact h'
        rw [hsf, if_pos rfl] at hf
        have hpos := hK ⟨hrun, hcur⟩
        rw [bankWordRetryLeaseSpend, hf]
        refine ⟨by omega, ?_⟩
        intro hrc
        rw [hidle] at hrc
        cases hrc.1
  · -- ROOT_IN: the root is the responder
    have hdone : (workerW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).done = false := by
      cases hd : (workerW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).done with
      | false => rfl
      | true =>
          exact absurd
            (widthWordPassIncomingDoneCompletes ring hn hsmallFive root s hs
              z.1 z.2.1 hpass e hpred hno hd) hnc
    have hsf : bankWordHardEpochSoftFinish root
        (bankWordEpochSelectedReceipt ring z.1 e) = false := by
      simp [bankWordHardEpochSoftFinish, bankWordEpochSelectedReceipt, he]
    rw [hsf, if_neg (by decide)] at hf
    have hrec := bankWordPassTargetRecord ring root z.1 e hne
    rw [hpred] at hrec hx hy hfa hdone
    change ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val + _ = _ ∧
      (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert = .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase = .CURRENT →
        0 < ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val)
    rw [hrec, hf]
    have hleaseEq :
        (pairW (z.1.2.1 e) (z.1.2.1 root)).2.siLease =
          (leasePair (compileAdvice (ceilLogTwo n))
            (z.1.2.1 e).siLease (z.1.2.1 root).siLease
            (serW (z.1.2.1 e) (z.1.2.1 root)).hard.hardAccept
            (serW (z.1.2.1 e) (z.1.2.1 root)).hard.softAccept
            (workerW (z.1.2.1 e) (z.1.2.1 root)).done).2 := rfl
    rw [hleaseEq, pairW_ser_right, hfa, hdone, bankWordRetryLeaseResponder]
    refine ⟨hlease, ?_⟩
    intro hrc
    exact hK (bankWordRetryRootInRunningCurrent _ _ hx hy hrc)
  · -- remote service: the root record and the counter frame
    have hsf : bankWordHardEpochSoftFinish root
        (bankWordEpochSelectedReceipt ring z.1 e) = false := by
      simp [bankWordHardEpochSoftFinish, bankWordEpochSelectedReceipt, he]
    rw [hsf, if_neg (by decide)] at hf
    have hrec := bankWordPassRemoteRecord ring root z.1 e root
      (fun h => he h.symm) (fun h => hj h.symm)
    change ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val + _ = _ ∧
      (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert = .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase = .CURRENT →
        0 < ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val)
    rw [hrec, hf]
    exact ⟨hlease, hK⟩

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRetryPrefixStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRetryPrefixWord`.
 One service of the fresh attempt before its first hard S1 that does
not complete the worker: it is not a genuine retry, the prefix invariant
persists, and the soft potential `(n-1)·finishes + position` grows by at
most the soft-nomination hit.  Consumer: `widthWordRetryPrefixWord`. -/
theorem widthWordRetryPrefixStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n)
    (hI : WidthWordRetryPrefixInvariant ring root s z)
    (hno : (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
      false)
    (hnc : ¬ BankWordRenewalCompleted (bankWordRenewalNext ring root s z e).1) :
    ¬ bankWordRenewalGenuine ring root z.1 e ∧
    WidthWordRetryPrefixInvariant ring root s (bankWordRenewalNext ring root s z e) ∧
    (n - 1) * (bankWordHardEpochLedger ring root
        (bankWordRenewalNext ring root s z e).1).softFinishes +
      bankWordRenewalSoftRootedPosition ring root
        (bankWordRenewalNext ring root s z e).1 ≤
    (n - 1) * (bankWordHardEpochLedger ring root z.1).softFinishes +
      bankWordRenewalSoftRootedPosition ring root z.1 +
      (if e = bankWordRenewalSoftRootedChosen ring root s z then 1 else 0) := by
  obtain ⟨hpass, hsoft, hep, hwd, hlease, hK⟩ := hI
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.1.2.1 e)
    (z.1.2.1 (ring.rightNeighbor e)) (hpass.1 e) (hpass.1 _) hno
  have hgen : ¬ bankWordRenewalGenuine ring root z.1 e := by
    intro hg
    unfold bankWordRenewalGenuine bankWordHardEpochGenuine at hg
    simp [wGenuineAcceptance, bankWordEpochSelectedReceipt, hfa] at hg
  have hstep := widthWordPassStep ring hn hsmallFive root s hs z.1 z.2.1 e hpass hno
  have hpass' : BankWordPassShape ring root
      (bankWordRenewalNext ring root s z e).1 := by
    by_cases hnom : e = bankWordPassNomination ring root z.1
    · rcases hstep.2 hnom with h | h
      · exact h.1
      · exact absurd h.2.2.1 hnc
    · exact (hstep.1 hnom).1
  have hsoft' :=
    (widthWordRenewalSoftShapeStep ring root s hn hsmallFive hs z e hsoft).1
  obtain ⟨hep0, hwd0, hf0⟩ :=
    bankWordRetryLedgerStep ring root s z.1 z.2.1 e hfa hnc hep hwd
  have hep' : 0 < (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).hardEpochs :=
    Nat.lt_of_lt_of_eq hep hep0.symm
  have hwd' : (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).workerDone = false := hwd0
  have hf : (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).softFinishes =
      (if bankWordHardEpochSoftFinish root
          (bankWordEpochSelectedReceipt ring z.1 e) = true
        then (bankWordHardEpochLedger ring root z.1).softFinishes + 1
        else (bankWordHardEpochLedger ring root z.1).softFinishes) := hf0
  have hLK := widthWordRetryRootLeaseStep ring hn hsmallFive root s hs z e hpass
    hno hnc hfa hfl hfr hlease hK hf
  have hhit := widthWordRenewalSoftRootedPositionHitStep
    ring root s hn hsmallFive hs z e hsoft
  refine ⟨hgen, ⟨hpass', hsoft', hep', hwd', hLK.1, hLK.2⟩,
    ?_⟩
  cases hsf : bankWordHardEpochSoftFinish root
      (bankWordEpochSelectedReceipt ring z.1 e) with
  | false =>
      rw [hsf, if_neg (by decide)] at hf
      rw [hf]
      omega
  | true =>
      rw [hsf, if_pos rfl] at hf
      have hsf' : ((e == root) &&
          ((serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).row == "S6") &&
          (serW (z.1.2.1 e)
            (z.1.2.1 (ring.rightNeighbor e))).hard.softAccept) = true := hsf
      simp only [Bool.and_eq_true, beq_iff_eq] at hsf'
      obtain ⟨⟨he, _⟩, hsa⟩ := hsf'
      rw [he] at hsa hf ⊢
      obtain ⟨hx, hy⟩ := widthWordRenewalSoftOutgoingFlags ring root s hn hsmallFive hs z
      obtain ⟨_, _, hrun, hb, hcur, hout, hchild⟩ :=
        bankWordRetryRootOutSoftAccept _ _ hx hy hsa
      have hret := bankWordRenewalFreshSoftEpisodePairing ring root s z hsoft
        hrun hb hcur hout hchild
      obtain ⟨_, hpos', hpos, _, _⟩ :=
        bankWordRenewalSoftRootOutgoingFinishStep ring root s z hn hret hx hy
      change (n - 1) * (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z.1 root)).softFinishes +
        bankWordRenewalSoftRootedPosition ring root
          (bankWordEpochNext ring root z.1 root) ≤ _
      rw [hpos', hpos]
      change (n - 1) * (bankWordHardEpochLedger ring root
          (bankWordRenewalNext ring root s z root).1).softFinishes + 0 ≤ _
      rw [hf, Nat.mul_add, Nat.mul_one]
      omega

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRetryPrefixWord`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshRetryCover`.
 Along any word from a state satisfying the prefix invariant, if
the fresh attempt has not succeeded by the end of the word, then
either no hard S1 occurred and the pass did not complete, or the soft
potential has reached L(n-1): a hard S1 reads lease zero, so all L
soft finishes were counted, each paid by n-1 soft-nominated hits.
Consumer: `widthWordRenewalFreshRetryCover`. -/
theorem widthWordRetryPrefixWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    ∀ (w : List (Fin n)) (z : BankWordRenewalPostSOne ring root s),
      WidthWordRetryPrefixInvariant ring root s z →
      bankWordAttemptUnfinished (bankWordRenewalFreshKernel ring root s)
        (.active z) w = 1 →
      (BankWordPassNoHardStart ring root z.1 w ∧
          ¬ BankWordPassCompletes ring root z.1 w) ∨
        (n - 1) * widthWordRenewalLease n ≤
          (n - 1) * (bankWordHardEpochLedger ring root z.1).softFinishes +
            bankWordRenewalSoftRootedPosition ring root z.1 +
            grantDrainLabelHits (bankWordRenewalNext ring root s)
              (bankWordRenewalSoftRootedChosen ring root s) z w := by
  intro w
  induction w with
  | nil =>
      intro z _ _
      exact Or.inl ⟨trivial, fun h => h⟩
  | cons e es ih =>
      intro z hI hU
      by_cases hhard :
          (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 = true
      · right
        have hfields := bankWordRetryHardStartFields (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e)) hhard
        have he : e = root := by
          rcases widthWordRenewalSoftOwnerFlags ring root s hn hsmallFive hs z e with
            ⟨he, _, _⟩ | ⟨_, _, hx, _⟩ | ⟨_, _, hx, _⟩
          · exact he
          · rw [hfields.1] at hx
            cases hx
          · rw [hfields.1] at hx
            cases hx
        have hzero := hfields.2
        rw [he] at hzero
        have hfL : (bankWordHardEpochLedger ring root z.1).softFinishes =
            widthWordRenewalLease n := by
          have := hI.2.2.2.2.1
          omega
        rw [hfL]
        omega
      · have hno :
            (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
              false := by
          cases hb : (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1
          · rfl
          · exact absurd hb hhard
        change bankWordAttemptUnfinished (bankWordRenewalFreshKernel ring root s)
          (bankWordRenewalFreshStep ring root s z e) es = 1 at hU
        by_cases hd : BankWordRenewalCompleted
            (bankWordRenewalNext ring root s z e).1
        · exfalso
          have hst : bankWordRenewalFreshStep ring root s z e = .success := by
            simp [bankWordRenewalFreshStep, hd]
          rw [hst] at hU
          simp [bankWordAttemptUnfinished] at hU
        · obtain ⟨hg, hI', hpot⟩ :=
            widthWordRetryPrefixStep ring hn hsmallFive root s hs z e hI hno hd
          have hst : bankWordRenewalFreshStep ring root s z e =
              .active (bankWordRenewalNext ring root s z e) := by
            simp [bankWordRenewalFreshStep, hd, hg]
          rw [hst] at hU
          rcases ih _ hI' hU with ⟨hnh, hnc⟩ | hq
          · left
            refine ⟨(And.intro hno hnh :
              BankWordPassNoHardStart ring root z.1 (e :: es)), ?_⟩
            intro hc
            rcases hc with hr | hc
            · exact hd hr.2.2.1
            · exact hnc hc
          · right
            change _ ≤ _ + _ +
              ((if e = bankWordRenewalSoftRootedChosen ring root s z then 1 else 0) +
                grantDrainLabelHits (bankWordRenewalNext ring root s)
                  (bankWordRenewalSoftRootedChosen ring root s)
                  (bankWordRenewalNext ring root s z e) es)
            omega

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshRetryCover`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshRetryEstimate`.
 The pointwise first-H cover at an actual fresh seed: an unfinished
attempt has at least L(n-1) soft-nominated hits (A*) or fewer than Cn
worker-nominated hits (C*).  Consumer:
`widthWordRenewalFreshRetryEstimate`. -/
theorem widthWordRenewalFreshRetryCover {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (w : List (Fin n)) :
    bankWordAttemptUnfinished (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) w ≤
      (if widthWordRenewalLease n * (n - 1) ≤
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            (bankWordRenewalSoftRootedChosen ring root s) seed.1 w
        then 1 else 0) +
      (if grantDrainLabelHits (bankWordRenewalNext ring root s)
            (fun v => bankWordPassNomination ring root v.1) seed.1 w <
          widthWordRenewalWorkerQuota n * n
        then 1 else 0) := by
  have hle := bankWordAttemptUnfinishedLeOne
    (bankWordRenewalFreshKernel ring root s) w (.active seed.1)
  by_cases hU : bankWordAttemptUnfinished
      (bankWordRenewalFreshKernel ring root s) (.active seed.1) w = 1
  · obtain ⟨hI, hf0, hp0⟩ :=
      widthWordRetryPrefixInvariantSeed ring hn hsmallFive root s hs seed
    rcases widthWordRetryPrefixWord ring hn hsmallFive root s hs w seed.1 hI hU with
      ⟨hnh, hnc⟩ | hq
    · have hb := widthWordPassFreshWorkerHitsBelowQuota
        ring hn hsmallFive root s hs seed w hnh hnc
      rw [← bankWordRetryHitsProjection ring root s
        (bankWordPassNomination ring root) w seed.1] at hb
      have hb' : grantDrainLabelHits (bankWordRenewalNext ring root s)
            (fun v => bankWordPassNomination ring root v.1) seed.1 w <
          widthWordRenewalWorkerQuota n * n := hb
      rw [if_pos hb']
      omega
    · rw [hf0, hp0] at hq
      have hq' : widthWordRenewalLease n * (n - 1) ≤
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            (bankWordRenewalSoftRootedChosen ring root s) seed.1 w := by
        rw [Nat.mul_comm]
        simpa using hq
      rw [if_pos hq']
      omega
  · omega

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshRetryEstimate`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshFourCostHolds`.
 R10 hfail at every actual fresh seed: four times the number of
words on which the fresh first attempt has ended in a genuine retry by
T is at most 3 n^T, for every horizon T.  This is exactly the hfail
premise of `widthWordRenewalFreshFourCostHoldsOfFailure`.
Consumer: `widthWordRenewalFreshFourCostHolds`. -/
theorem widthWordRenewalFreshRetryEstimate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    ∀ seed : BankWordRenewalFreshSeed ring root s, ∀ T,
      4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s) (.active seed.1) T ≤
        3 * n ^ T := by
  intro seed T
  have hn0 : 0 < n := by omega
  apply bankWordAttemptRetryAllHorizons _ _ (widthWordRenewalHorizon n) hn0 _ T
  apply bankWordAttemptUnionQuarter (widthWordRenewalHorizon n) _ _ _
    (widthWordRenewalFreshRetryCover ring hn hsmallFive root s hs seed)
  · rw [bankWordRenewalNominatedUpperTailLaw (bankWordRenewalNext ring root s)
      (bankWordRenewalSoftRootedChosen ring root s) seed.1
      (widthWordRenewalHorizon n) (widthWordRenewalLease n * (n - 1)) hn0]
    exact widthUpperBankBandInterruptionQuarter n hsmallFive
  · exact widthWordRenewalWorkerNominationHalf ring root s seed.1
      (fun v => bankWordPassNomination ring root v.1) hn0

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshFourCostHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochFreshCutFourCostHolds`.
 The fresh genuine completion costs at most four blocks, with no
remaining premise: hcost is `widthWordRenewalFreshAttemptCostHolds` and
hfail is `widthWordRenewalFreshRetryEstimate`.
Consumer: the 1B + 4B staging budget of the R10 W projected clock. -/
theorem widthWordRenewalFreshFourCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (4 * widthWordRenewalBlock n) :=
  widthWordRenewalFreshFourCostHoldsOfFailure ring hn hsmallFive root s hs
    (widthWordRenewalFreshRetryEstimate ring hn hsmallFive root s hs) seed T

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochFreshCutFourCostHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletionFiveCostHolds`.
 From any genuinely fresh cut the epoch process reaches the causal
worker-completion receipt within four renewal blocks, with no hfail
premise.  Consumer: `widthWordEpochCompletionFiveCostHolds`. -/
theorem widthWordEpochFreshCutFourCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hfresh : BankWordEpochFreshCut ring root s z)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordRenewalCompleted z T ≤
        n ^ T * (4 * widthWordRenewalBlock n) := by
  obtain ⟨seed, heq⟩ := hfresh
  have hcost := widthWordRenewalFreshFourCostHolds
    ring hn hsmallFive root s hs seed T
  have hmap := costNumerator_map_eq
    (bankWordRenewalNext ring root s)
    (bankWordEpochNext ring root)
    (fun v : BankWordRenewalPostSOne ring root s => v.1)
    (by intro v e; rfl)
    BankWordRenewalCompleted T seed.1
  rw [hmap] at hcost
  rw [heq] at hcost
  exact hcost

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochCompletionFiveCostHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: the SMALL clean W clock.
 A worker-completion receipt is hit within five blocks from the
represented projected W entrance: one block to the first genuine
launch (a fresh cut) and four from it, with no hfail premise.
Consumer: `bankWordProjectedClockOfCompletionBridge`. -/
theorem widthWordEpochCompletionFiveCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordRenewalCompleted
      (bankWordEpochStart s) T ≤
      n ^ T *
        ((440 * (compileAdvice (ceilLogTwo n)).t + 275) * n ^ 2) := by
  have hinit : BankWordEpochReachable ring root s
      (bankWordEpochStart s) := ⟨[], rfl⟩
  have hnot :
      ¬ BankWordEpochWorkerLaunched (bankWordEpochStart s) := by
    intro h
    obtain ⟨w, hw⟩ := h
    change (none : Option (WWorkerTrail n)) = some w at hw
    cases hw
  have hfirst : ∀ U,
      costNumerator (bankWordEpochNext ring root)
        (fun z => BankWordEpochFreshCut ring root s z ∨
          BankWordRenewalCompleted z)
        (bankWordEpochStart s) U ≤
        n ^ U * widthWordRenewalBlock n := by
    intro U
    have hentr := costNumerator_entrance_le_on
      (bankWordEpochNext ring root)
      (BankWordEpochReachable ring root s)
      BankWordEpochWorkerLaunched
      (fun z => BankWordEpochFreshCut ring root s z ∨
        BankWordRenewalCompleted z)
      (fun z hz e => bankWordEpochReachableNext ring root s z hz e)
      (fun z hz hnotz e hlaunched =>
        Or.inl (widthWordEpochFreshCutOfFirstLaunch
          ring hn hsmallFive root s hs z hz e hnotz hlaunched))
      U (bankWordEpochStart s) hinit hnot
    have hworker := widthWordEpochPostSOneWorkerClockHolds
      ring hn hsmallFive root s hs
    have hlaunch := widthWordProjectedOneEpochCostOfWorkerClock
      ring hn hsmallFive root s hs hworker U
    have hcoeff :
        8 * (compileAdvice (ceilLogTwo n)).t + 5 =
          widthWordRenewalLease n + 1 := by
      unfold widthWordRenewalLease
      omega
    rw [hcoeff] at hlaunch
    change costNumerator (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched (bankWordEpochStart s) U ≤
      n ^ U * widthWordRenewalBlock n at hlaunch
    exact Nat.le_trans hentr hlaunch
  have hsecond : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochFreshCut ring root s z →
      ∀ U, costNumerator (bankWordEpochNext ring root)
        BankWordRenewalCompleted z U ≤
        n ^ U * (4 * widthWordRenewalBlock n) := by
    intro z _ hfresh U
    exact widthWordEpochFreshCutFourCostHolds
      ring hn hsmallFive root s hs z hfresh U
  have hstage := costNumerator_stage_le_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root s)
    (BankWordEpochFreshCut ring root s)
    BankWordRenewalCompleted
    (fun z hz e => bankWordEpochReachableNext ring root s z hz e)
    (bankWordEpochStart s) hinit
    (widthWordRenewalBlock n) (4 * widthWordRenewalBlock n)
    hfirst hsecond T
  have hbudget :
      widthWordRenewalBlock n + 4 * widthWordRenewalBlock n =
        5 * widthWordRenewalBlock n := by
    calc
      widthWordRenewalBlock n + 4 * widthWordRenewalBlock n =
          (1 + 4) * widthWordRenewalBlock n := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = 5 * widthWordRenewalBlock n := rfl
  calc
    costNumerator (bankWordEpochNext ring root)
        BankWordRenewalCompleted (bankWordEpochStart s) T ≤
      n ^ T *
        (widthWordRenewalBlock n + 4 * widthWordRenewalBlock n) :=
      hstage
    _ = n ^ T * (5 * widthWordRenewalBlock n) :=
      congrArg (fun b : Nat => n ^ T * b) hbudget
    _ = n ^ T *
        ((440 * (compileAdvice (ceilLogTwo n)).t + 275) * n ^ 2) := by
      rw [widthWordRenewalFiveCoefficient]

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesBase`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletedClean`, `widthWordEpochCompletedRetired`.
 The selected genuine hard S6 really launches a physical
PREFIX at root with index zero and no completion receipt.
The OR/AND empty folds are false/true; no follower has
been published. Consumer: Layer-W induction base. -/
theorem widthWordPassValuesBase {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordPassValues ring root seed.1.1 := by
  obtain ⟨w, hw, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness
      ring root s seed
  have hphysical :=
    (widthWordRenewalFrontierFreshBankPrepared
      ring root s hsmallFive seed).1
  have hnone :=
    bankWordRenewalFreshNotCompleted ring root s seed
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv hvphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    subst v
    refine ⟨?_, ?_, ?_⟩
    · rw [hh, hi, hphysical]
      simp [cwPrefixOr, launchPrefix]
    · rw [hh, hi, hphysical]
      simp [cwPrefixAnd, launchPrefix]
    · intro k hk hle _
      rw [hi] at hle
      omega
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    exact False.elim (hphase rfl)
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    exact False.elim (hphase rfl)
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    cases hphase
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    cases hphase
  · intro hretired
    exact False.elim (hnone hretired.2.2.1)

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesAZeroStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesReadyAllStep`.
 Consumer: the QWord first-A0 completion base.
The selected READY A0 (certified by its OLD owner guards)
preserves the visible word; the last READY target accounts
for the unique final published offset n-1, and the earlier
targets plus first-window clauses supply all five static
CleanWorkerWordValues fields. The actual Layer-G retirement
witness supplies the ghost/empty-SI exit, but does not
supply any word values: those are proved here from Layer W.
This is the genuine A0 branch, not a vacuous some-worker
quantifier on the retired state. -/
theorem widthWordPassValuesAZeroStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hready : w.phase = .readyRun)
    (hhost : w.host = e)
    (hroot : ring.rightNeighbor e = root)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false)
    (hpost :
      (postW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).eY.l = true)
    (hret :
      BankWordPassRetired ring root
        (bankWordEpochNext ring root z e)) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hready] at hfields
  obtain ⟨k, _, _, _, _, hkind, hbusy, hcur, hother⟩ := hfields
  have hsourceKind : (z.2.1 e).si.kind = .ROOT := by
    rw [← hhost]
    exact hkind
  have hsourceBusy : (z.2.1 e).si.busy = false := by
    rw [← hhost]
    exact hbusy
  have hsourceCur : (z.2.1 e).si.cur = .NONE := by
    rw [← hhost]
    exact hcur
  have hfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true := by
    apply hother
    intro heq
    rw [hhost] at heq
    exact hne heq
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  obtain ⟨hrow, _, _, hselected⟩ :=
    L3.WordCertificate.generatedControlReadyAZeroOwner
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hfa hfl hfr hsourceKind hsourceBusy hsourceCur
      hpost hfree
  have hvisible :
      ∀ i : Fin n,
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i
    change
      wordVisible (phiW ring z.2.1 e) i =
        wordVisible z.2.1 i
    exact
      ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp
        hselected) i
  have hterminal :=
    bankWordPassValuesAZeroTerminalOffset
      ring root z e w hpass hw hready hhost hroot
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hready] at h
    cases h
  obtain ⟨hzeros, hnonzero, hmarkerFirst⟩ :=
    hvalues.publishedPrefix w hw hnotPrefix
  have hreadyValues :=
    hvalues.currentReady w hw hready
  rw [hterminal] at hreadyValues
  have hwordOld :
      CleanWorkerWordValues ring root z.2.1 := by
    refine {
      prefixZeros := hzeros
      firstNonzero := hnonzero
      laterNonzero := ?_
      recurrence := ?_
      markers := ?_ }
    · intro j hj
      by_cases hlast : j.val = n - 1
      · rw [hlast]
        exact hreadyValues.1
      · have hbefore :
            j.val < PPL.cyclicOffset ring root w.target := by
          rw [hterminal]
          omega
        exact
          (hvalues.earlierTargets w hw hnotPrefix j
            hj hbefore).1
    · intro j hj
      by_cases hlast : j.val = n - 1
      · rw [hlast]
        exact hreadyValues.2.1
      · have hbefore :
            j.val < PPL.cyclicOffset ring root w.target := by
          rw [hterminal]
          omega
        exact
          (hvalues.earlierTargets w hw hnotPrefix j
            hj hbefore).2.1
    · intro j hj
      by_cases hfirst :
          j.val = (compileAdvice (ceilLogTwo n)).t
      · rw [hfirst]
        calc
          cwMarker ring root z.2.1
              (compileAdvice (ceilLogTwo n)).t =
            cwPrefixAnd ring root z.2.1
              (compileAdvice (ceilLogTwo n)).t :=
                hmarkerFirst
          _ =
            (cwSumTrailing ring root z.2.1
                (compileAdvice (ceilLogTwo n)).t
                (compileAdvice (ceilLogTwo n)).t &&
              cwBit ring root z.2.1
                (compileAdvice (ceilLogTwo n)).t) :=
                  L3.WordCertificate.generatedControlPrefixAndTerminalMarker
                    ring root z.2.1
                    (by have hwidth := widthWordPassWidth hsmallFive; omega)
      · have hgt :
            (compileAdvice (ceilLogTwo n)).t < j.val := by
          omega
        by_cases hlast : j.val = n - 1
        · rw [hlast]
          exact hreadyValues.2.2
        · have hbefore :
              j.val < PPL.cyclicOffset ring root w.target := by
            rw [hterminal]
            omega
          exact
            (hvalues.earlierTargets w hw hnotPrefix j
              hgt hbefore).2.2
  have hwordNew :
      CleanWorkerWordValues ring root
        (bankWordEpochNext ring root z e).2.1 :=
    cleanWorkerWordValues_congr ring root
      (bankWordEpochNext ring root z e).2.1
      z.2.1 hvisible hwordOld
  have hnoWorker :
      (bankWordEpochNext ring root z e).2.2.worker = none :=
    hret.2.1
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro _
    exact
      ⟨hwordNew.prefixZeros, hwordNew.firstNonzero,
        hwordNew.laterNonzero, hwordNew.recurrence,
        hwordNew.markers⟩

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesPoneStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesPrefixAllStep`.
 Consumer: PREFIX/P1 arm of bankWordPassValuesAllStep.
The literal P1 selected edge moves the unique OLD prefix
from its host to the clockwise neighbor. The NEW physical
z/a accumulators are the OLD prefix OR/AND folds extended
by the OLD responder U; all OLD visited markers remain
unchanged and the new short marker is zero. The actual
ghost worker advances to index+1. No global
CleanWorkerWordValues premise is used. -/
theorem widthWordPassValuesPoneStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hhost : w.host = e)
    (hindex : w.index < (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨_, _, _, hsiteOld, hk, hb, hc, hjv, hother⟩ := hfields
  rw [hhost] at hk hb hc hjv hother
  have hfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother (ring.rightNeighbor e) hne
  have hnoRoot :
      ring.rightNeighbor e ≠ root := by
    have hnoRootHost :=
      widthWordRenewalFrontierShapePrefixNoRoot
        ring root z hsmallFive hpass.2.1 w hw hphase
    rw [hhost] at hnoRootHost
    exact hnoRootHost
  have hpost :
      (postW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
    rw [widthWordPassResponderFlag
      ring hn hsmallFive root s hs z hz e]
    simp [hnoRoot]
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hjlt :
      (z.2.1 e).si.j.val <
        (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv]
    exact hindex
  obtain ⟨hrow, _, hdestFields⟩ :=
    L3.WordCertificate.generatedControlPoneLiteralFields
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hfa hfl hfr hk hb hc hjlt hpost hfree
  obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
    bankWordPassGhostPrefixAdvance
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hjv
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hdest :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si =
        { kind := .PREFIX, busy := false, cur := .NONE,
          j := siJ (compileAdvice (ceilLogTwo n)).t
            ((z.2.1 e).si.j.val + 1),
          z := ((z.2.1 e).si.z ||
            (z.2.1 (ring.rightNeighbor e)).u),
          p := false,
          a := ((z.2.1 e).si.a &&
            (z.2.1 (ring.rightNeighbor e)).u) } := by
    rw [bankWordPassTargetRecord ring root z e hne,
      bankWordPassPairSIRight]
    exact hdestFields
  have hnextSite :
      ring.rightNeighbor e =
        L3.EWord.site ring root (w.index + 1) := by
    rw [← hhost, hsiteOld]
    exact L3.EWord.siteSuccessor ring root w.index
  have hbit :
      (z.2.1 (ring.rightNeighbor e)).u =
        cwBit ring root z.2.1 (w.index + 1) := by
    rw [hnextSite]
    rfl
  have hsourceValues := hvalues.prefixRun w hw hphase
  obtain ⟨hzold, haold, hzeros⟩ := hsourceValues
  rw [hhost] at hzold haold
  have hphysical :=
    L3.WordPhase.wordPhasePonePhysicalFields
      ring z.2.1 e hne hrow
  have hu :
      ∀ i : Fin n,
        ((bankWordEpochNext ring root z e).2.1 i).u =
          (z.2.1 i).u := by
    intro i
    change ((phiW ring z.2.1 e) i).u = (z.2.1 i).u
    exact hphysical.2.2.1 i
  have hfold :=
    L3.WordPhase.wordPhasePonePrefixFoldsCongr
      ring root
      (bankWordEpochNext ring root z e).2.1 z.2.1 hu
      (w.index + 1)
  have hznew :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.z =
        ((z.2.1 e).si.z ||
          (z.2.1 (ring.rightNeighbor e)).u) := by
    rw [hdest]
  have hanew :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.a =
        ((z.2.1 e).si.a &&
          (z.2.1 (ring.rightNeighbor e)).u) := by
    rw [hdest]
  have hor :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.z =
        cwPrefixOr ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := by
    calc
      _ =
          ((z.2.1 e).si.z ||
            (z.2.1 (ring.rightNeighbor e)).u) := hznew
      _ = (cwPrefixOr ring root z.2.1 w.index ||
          cwBit ring root z.2.1 (w.index + 1)) := by
            rw [hzold, hbit]
      _ = cwPrefixOr ring root z.2.1 (w.index + 1) :=
        (L3.WordPhase.wordPhasePoneOrSucc
          ring root z.2.1 w.index).symm
      _ = cwPrefixOr ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := hfold.1.symm
  have hand :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.a =
        cwPrefixAnd ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := by
    calc
      _ =
          ((z.2.1 e).si.a &&
            (z.2.1 (ring.rightNeighbor e)).u) := hanew
      _ = (cwPrefixAnd ring root z.2.1 w.index &&
          cwBit ring root z.2.1 (w.index + 1)) := by
            rw [haold, hbit]
      _ = cwPrefixAnd ring root z.2.1 (w.index + 1) :=
        (L3.WordPhase.wordPhasePoneAndSucc
          ring root z.2.1 w.index).symm
      _ = cwPrefixAnd ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := hfold.2.symm
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hvnew _
    have heq : v = w' :=
      Option.some.inj (hvnew.symm.trans hworkerNew)
    subst v
    refine ⟨?_, ?_, ?_⟩
    · rw [hh', hi']
      exact hor
    · rw [hh', hi']
      exact hand
    · intro k hk hle hlt
      rw [hi'] at hle
      by_cases hlast : k.val = w.index + 1
      · have hshort :
            (z.2.1 e).si.j.val + 1 <
              (compileAdvice (ceilLogTwo n)).t := by
          rw [hjv]
          omega
        have hsite :
            ring.rightNeighbor e =
              PPL.shiftRight ring root
                ((z.2.1 e).si.j.val + 1) := by
          rw [hjv]
          exact hnextSite
        have hmarker :=
          bankWordPassValuesPoneMarkerStep
            ring root z e hn hrow hshort hsite
        rw [hlast]
        simpa only [hjv] using hmarker
      · have hbefore : k.val ≤ w.index := by omega
        have hzeroOld := hzeros k hk hbefore hlt
        have hneq :
            PPL.shiftRight ring root k.val ≠
              ring.rightNeighbor e := by
          intro h
          have hEq :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root (w.index + 1) :=
            h.trans hnextSite
          have hIdx :=
            L3.EWord.validationSiteInjective
              ring root k.val (w.index + 1)
              k.isLt (by omega : w.index + 1 < n) hEq
          omega
        have hbeta := hphysical.2.2.2.1
          (PPL.shiftRight ring root k.val) hneq
        change
          ((phiW ring z.2.1 e)
            (PPL.shiftRight ring root k.val)).beta = false
        rw [hbeta]
        exact hzeroOld
  · intro v hv hnePhase
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hnePhase
    exact False.elim (hnePhase rfl)
  · intro v hv hnePhase
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hnePhase
    exact False.elim (hnePhase rfl)
  · intro v hv hsum
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hsum
    cases hsum
  · intro v hv hready
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hready
    cases hready
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesPthreeStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesPrefixAllStep`.
 Consumer: PREFIX/P3 arm of bankWordPassValuesAllStep.
The literal P3 at the terminal prefix host (offset t) is the only
visible write: U(t) gets the zero-kick and beta(t) the AND fold.
The published first window is then nonzero with marker equal to its
AND fold; the new BACK target is offset t+1, so no earlier target
exists yet. No global CleanWorkerWordValues premise is used. -/
theorem widthWordPassValuesPthreeStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hhost : w.host = e)
    (hindex : w.index = (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  have hnoRoot : ring.rightNeighbor e ≠ root := by
    have h :=
      widthWordRenewalFrontierShapePrefixNoRoot
        ring root z hsmallFive hpass.2.1 w hw hphase
    rw [hhost] at h
    exact h
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨_, _, _, hsiteOld, hk, hb, hc, hjv, hother⟩ := hfields
  rw [hhost] at hk hb hc hjv hother
  have hfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother (ring.rightNeighbor e) hne
  have hpost :
      (postW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
    rw [widthWordPassResponderFlag
      ring hn hsmallFive root s hs z hz e]
    simp [hnoRoot]
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hj :
      (z.2.1 e).si.j.val = (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv, hindex]
  obtain ⟨hrow, _, _, _⟩ :=
    bankWordPassPrefixHandoffFields _ _ hfa hfl hfr hk hb hc hj
      hpost hfree
  obtain ⟨w', hw', hp', _, ht', _⟩ :=
    bankWordPassGhostPrefixHandoff
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hindex
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  obtain ⟨_, _, huX, huY, hbX, hbY⟩ :=
    L3.WordPhase.wordPhasePthreeOwnerFields
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hrow
  obtain ⟨hzold, haold, hzeros⟩ := hvalues.prefixRun w hw hphase
  rw [hhost, hindex] at hzold haold
  have hsite : e = L3.EWord.site ring root
      (compileAdvice (ceilLogTwo n)).t := by
    rw [← hhost, hsiteOld, hindex]
  have hsrcU :
      ((bankWordEpochNext ring root z e).2.1 e).u =
        (if (z.2.1 e).si.z = false then true else (z.2.1 e).u) := by
    rw [bankWordPassSourceRecord]
    exact huX
  have hsrcB :
      ((bankWordEpochNext ring root z e).2.1 e).beta =
        (z.2.1 e).si.a := by
    rw [bankWordPassSourceRecord]
    exact hbX
  have hothers :
      ∀ i : Fin n, i ≠ e →
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i hi
    by_cases hj : i = ring.rightNeighbor e
    · subst hj
      have hrec := bankWordPassTargetRecord ring root z e hne
      unfold wordVisible
      rw [hrec]
      exact Prod.ext huY hbY
    · unfold wordVisible
      rw [bankWordPassRemoteRecord ring root z e i hi hj]
  have hlow :
      ∀ m : Nat, m < (compileAdvice (ceilLogTwo n)).t →
        cwBit ring root (bankWordEpochNext ring root z e).2.1 m =
          cwBit ring root z.2.1 m ∧
        cwMarker ring root (bankWordEpochNext ring root z e).2.1 m =
          cwMarker ring root z.2.1 m := by
    intro m hm
    have hsne : L3.EWord.site ring root m ≠ e := by
      rw [hsite]
      exact bankWordPassSiteNe ring root m _ (by omega) (by omega)
        (by omega)
    have h := hothers _ hsne
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hu : (z.2.1 e).u =
      cwBit ring root z.2.1 (compileAdvice (ceilLogTwo n)).t :=
    congrArg (fun i => (z.2.1 i).u) hsite
  have hbitT :
      cwBit ring root (bankWordEpochNext ring root z e).2.1
          (compileAdvice (ceilLogTwo n)).t =
        (if cwPrefixOr ring root z.2.1
            (compileAdvice (ceilLogTwo n)).t = false then true
         else cwBit ring root z.2.1
            (compileAdvice (ceilLogTwo n)).t) := by
    have h1 :
        cwBit ring root (bankWordEpochNext ring root z e).2.1
            (compileAdvice (ceilLogTwo n)).t =
          ((bankWordEpochNext ring root z e).2.1 e).u :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).u)
        hsite).symm
    rw [h1, hsrcU, hzold, hu]
  have hwin :=
    bankWordPassPthreeWindow ring root
      (bankWordEpochNext ring root z e).2.1 z.2.1 ht2
      (fun m hm => (hlow m hm).1) hbitT
  have hmarkT :
      cwMarker ring root (bankWordEpochNext ring root z e).2.1
          (compileAdvice (ceilLogTwo n)).t =
        cwPrefixAnd ring root (bankWordEpochNext ring root z e).2.1
          (compileAdvice (ceilLogTwo n)).t := by
    have h1 :
        cwMarker ring root (bankWordEpochNext ring root z e).2.1
            (compileAdvice (ceilLogTwo n)).t =
          ((bankWordEpochNext ring root z e).2.1 e).beta :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).beta)
        hsite).symm
    rw [h1, hsrcB, haold, hwin.2]
  have hnextSite :
      ring.rightNeighbor e = L3.EWord.site ring root
        ((compileAdvice (ceilLogTwo n)).t + 1) := by
    rw [hsite]
    exact L3.EWord.siteSuccessor ring root _
  have hoffNext :
      PPL.cyclicOffset ring root w'.target =
        (compileAdvice (ceilLogTwo n)).t + 1 := by
    rw [ht', hnextSite]
    exact L3.EWord.validationSiteOffset ring root _ (by omega)
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv' hp
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hp
    cases hp
  · intro _ _ _
    refine ⟨?_, hwin.1, hmarkT⟩
    intro k hk hlt
    rw [(hlow k.val hlt).2]
    exact hzeros k hk (by rw [hindex]; omega) hlt
  · intro v hv' _ k hk hlt
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hoffNext] at hlt
    omega
  · intro v hv' hs
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hs
    cases hs
  · intro v hv' hr
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hr
    cases hr
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesSzeroStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesSumAllStep`.
 Consumer: SUM/S0 arm of bankWordPassValuesAllStep. The SUM
cursor moves one site clockwise and its three accumulators are the
OLD folds extended by the OLD source bit at offset k-t+index (the
target offset is k). The visible word is unchanged. -/
theorem widthWordPassValuesSzeroStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hhost : w.host = e)
    (hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  have hsumOld := hvalues.sumCursor w hw hphase
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hit, htarget, hhostSite, hkind, hcur, hjv,
    _, _, hother⟩ := hfields
  rw [hhost] at hsumOld hkind hcur hjv
  have hsiteE : e = L3.EWord.site ring root
      (k - (compileAdvice (ceilLogTwo n)).t + w.index) := by
    rw [← hhost]
    exact hhostSite
  have hyne : ring.rightNeighbor e ≠ w.target := by
    rw [hsiteE, L3.EWord.siteSuccessor, htarget]
    exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
  have hyfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother _ (fun h => hne (h.trans hhost)) hyne
  have hjs :
      (z.2.1 e).si.j.val + 1 < (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv]
    exact hidx
  obtain ⟨hrow, _, _, _, _, _, _⟩ :=
    bankWordPassSumMoveFields _ _ hfa hfl hfr hkind hcur hjs hyfree
  have hacc :=
    bankWordPassSumMoveAccumulators _ _ hfa hfl hfr hkind hcur hjs
      hyfree
  have hquiet :=
    bankWordPassSumMoveQuiet _ _ hfa hfl hfr hkind hcur hjs hyfree
  obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
    bankWordPassGhostSumMove
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hjv
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hvis :
      ∀ i : Fin n,
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i
    change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
    exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hxu :
      (z.2.1 e).u =
        cwSourceBit ring root z.2.1
          (PPL.cyclicOffset ring root w.target) w.index := by
    rw [hoff]
    exact congrArg (fun i => (z.2.1 i).u) hsiteE
  have hsiTarget :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si =
        (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
    rw [bankWordPassTargetRecord ring root z e hne,
      bankWordPassPairSIRight]
  refine bankWordPassValuesQuietMove ring root z
    (bankWordEpochNext ring root z e) w w' hvalues hw hnotPrefix
    hworkerNew
    (fun h => by rw [hp'] at h; cases h)
    (fun h => by rw [hp'] at h; cases h)
    ht' hvis ?_
  intro _
  rw [hh', ht', hi', hsiTarget]
  refine ⟨?_, ?_, ?_⟩
  · rw [hacc.1, hsumOld.1, hxu,
      L3.WordCertificate.generatedControlSumOrSucc]
  · rw [hacc.2.1, hsumOld.2.1, hxu, hjv,
      L3.WordCertificate.generatedControlSumParitySucc]
  · rw [hacc.2.2, hsumOld.2.2, hxu, hjv,
      L3.WordCertificate.generatedControlSumTrailingSucc]
    by_cases h0 : w.index = 0 <;> simp [h0]

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesSoneStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesSumAllStep`.
 Consumer: SUM/S1 arm of bankWordPassValuesAllStep. The literal
S1 into the busy ROOT target (offset k) is the only visible write.
Its window [k-t, k-1] is nonzero: for k = t+1 it is the published
first window, otherwise the LFSR step from the earlier target k-1
with tap 0 set (every compiled width). Hence the published U(k)
is the parity fold and beta(k) the trailing fold, so the READY
target satisfies currentReady; all other clauses read offsets below
k and are unchanged. -/
theorem widthWordPassValuesSoneStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hhost : w.host = e)
    (hlast : w.index + 1 = (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  have hsumOld := hvalues.sumCursor w hw hphase
  obtain ⟨hzeros, hfirst, hmarkFirst⟩ :=
    hvalues.publishedPrefix w hw hnotPrefix
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, _, htarget, hhostSite, hkind, hcur, hjv,
    htk, htb, _⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  rw [hoff] at hsumOld
  rw [hhost] at hsumOld hkind hcur hjv
  have hsiteE : e = L3.EWord.site ring root
      (k - (compileAdvice (ceilLogTwo n)).t + w.index) := by
    rw [← hhost]
    exact hhostSite
  have hrnK : ring.rightNeighbor e = L3.EWord.site ring root k := by
    rw [hsiteE, L3.EWord.siteSuccessor]
    congr 1
    omega
  have hyt : ring.rightNeighbor e = w.target := by
    rw [hrnK, htarget]
  have hyk : (z.2.1 (ring.rightNeighbor e)).si.kind = .ROOT := by
    rw [hyt]
    exact htk
  have hyb : (z.2.1 (ring.rightNeighbor e)).si.busy = true := by
    rw [hyt]
    exact htb
  have hjt :
      (z.2.1 e).si.j.val + 1 = (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv]
    exact hlast
  obtain ⟨hrow, _, _, _, _, _⟩ :=
    bankWordPassSumPublishFields _ _ hfa hfl hfr hkind hcur hjt hyk hyb
  obtain ⟨huX, hbX, huY, hbY⟩ :=
    bankWordPassSumPublishVisible _ _ hfa hfl hfr hkind hcur hjt hyk hyb
  obtain ⟨w', hw', hp', hh', ht', _⟩ :=
    bankWordPassGhostSumPublish
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hyt.symm hjv
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hxu :
      (z.2.1 e).u = cwSourceBit ring root z.2.1 k w.index :=
    congrArg (fun i => (z.2.1 i).u) hsiteE
  -- the OLD window folds at full length t
  have hzt :
      ((z.2.1 e).si.z || (z.2.1 e).u) =
        cwSumOr ring root z.2.1 k (compileAdvice (ceilLogTwo n)).t := by
    rw [hsumOld.1, hxu,
      ← L3.WordCertificate.generatedControlSumOrSucc, hlast]
  have hpt :
      Bool.xor (z.2.1 e).si.p
          ((compileAdvice (ceilLogTwo n)).taps (z.2.1 e).si.j.val &&
            (z.2.1 e).u) =
        cwSumParity ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    rw [hsumOld.2.1, hxu, hjv,
      ← L3.WordCertificate.generatedControlSumParitySucc, hlast]
  have hat :
      (if (z.2.1 e).si.j.val == 0 then true
       else ((z.2.1 e).si.a && (z.2.1 e).u)) =
        cwSumTrailing ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    have hlen :
        cwSumTrailing ring root z.2.1 k
            (compileAdvice (ceilLogTwo n)).t =
          cwSumTrailing ring root z.2.1 k (w.index + 1) := by
      rw [hlast]
    rw [hlen, L3.WordCertificate.generatedControlSumTrailingSucc,
      hsumOld.2.2, hxu, hjv]
    by_cases h0 : w.index = 0 <;> simp [h0]
  -- the window is nonzero
  have htap : (compileAdvice (ceilLogTwo n)).taps 0 = true :=
    bankWordPassTapZero ht2
  have hnz :
      cwSumOr ring root z.2.1 k (compileAdvice (ceilLogTwo n)).t =
        true := by
    by_cases hk' : k = (compileAdvice (ceilLogTwo n)).t + 1
    · rw [hk', bankWordPassSumOrFirstWindow]
      exact hfirst
    · have hlt : (compileAdvice (ceilLogTwo n)).t < k - 1 := by
        omega
      have hprev :=
        hvalues.earlierTargets w hw hnotPrefix ⟨k - 1, by omega⟩ hlt
          (by rw [hoff]; exact Nat.sub_lt (by omega) (by omega))
      exact bankWordPassWindowNonzero ring root z.2.1 k (by omega)
        (by omega) htap hprev.1 hprev.2.1
  have hvval :
      (if ((z.2.1 e).si.z || (z.2.1 e).u) == false then true
       else Bool.xor (z.2.1 e).si.p
          ((compileAdvice (ceilLogTwo n)).taps (z.2.1 e).si.j.val &&
            (z.2.1 e).u)) =
        cwSumParity ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    rw [hzt, hnz, hpt] <;> simp
  -- the new visible word differs from the old one only at the target
  have hothers :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i hi
    by_cases hie : i = e
    · rw [hie]
      unfold wordVisible
      rw [bankWordPassSourceRecord]
      exact Prod.ext huX hbX
    · unfold wordVisible
      rw [bankWordPassRemoteRecord ring root z e i hie hi]
  have hlowK :
      ∀ m : Nat, m < k →
        cwBit ring root (bankWordEpochNext ring root z e).2.1 m =
          cwBit ring root z.2.1 m ∧
        cwMarker ring root (bankWordEpochNext ring root z e).2.1 m =
          cwMarker ring root z.2.1 m := by
    intro m hm
    have hsne : L3.EWord.site ring root m ≠ ring.rightNeighbor e := by
      rw [hrnK]
      exact bankWordPassSiteNe ring root m k (by omega) hkn (by omega)
    have h := hothers _ hsne
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hnewU :
      cwBit ring root (bankWordEpochNext ring root z e).2.1 k =
        cwSumParity ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    have h1 :
        cwBit ring root (bankWordEpochNext ring root z e).2.1 k =
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor e)).u :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).u)
        hrnK).symm
    rw [h1, bankWordPassTargetRecord ring root z e hne]
    exact huY.trans hvval
  have hnewB :
      cwMarker ring root (bankWordEpochNext ring root z e).2.1 k =
        (cwSumTrailing ring root z.2.1 k
            (compileAdvice (ceilLogTwo n)).t &&
          cwSumParity ring root z.2.1 k
            (compileAdvice (ceilLogTwo n)).t) := by
    have h1 :
        cwMarker ring root (bankWordEpochNext ring root z e).2.1 k =
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor e)).beta :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).beta)
        hrnK).symm
    rw [h1, bankWordPassTargetRecord ring root z e hne]
    rw [← hat, ← hvval]
    exact hbY
  -- every window below or at k reads only offsets below k
  have hsumBelow :
      ∀ j : Nat, (compileAdvice (ceilLogTwo n)).t ≤ j → j ≤ k →
        cwSumOr ring root (bankWordEpochNext ring root z e).2.1 j
            (compileAdvice (ceilLogTwo n)).t =
          cwSumOr ring root z.2.1 j (compileAdvice (ceilLogTwo n)).t ∧
        cwSumParity ring root (bankWordEpochNext ring root z e).2.1 j
            (compileAdvice (ceilLogTwo n)).t =
          cwSumParity ring root z.2.1 j
            (compileAdvice (ceilLogTwo n)).t ∧
        cwSumTrailing ring root (bankWordEpochNext ring root z e).2.1 j
            (compileAdvice (ceilLogTwo n)).t =
          cwSumTrailing ring root z.2.1 j
            (compileAdvice (ceilLogTwo n)).t := by
    intro j hj1 hj2
    apply bankWordPassSumFoldsBelow
    intro i hi
    unfold cwSourceBit
    exact (hlowK _ (by omega)).1
  have hprefixBelow :=
    bankWordPassPrefixFoldsBelow ring root
      (bankWordEpochNext ring root z e).2.1 z.2.1
      (compileAdvice (ceilLogTwo n)).t
      (fun m hm => (hlowK m (by omega)).1)
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv' hp
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hp
    cases hp
  · intro _ _ _
    refine ⟨?_, ?_, ?_⟩
    · intro m hm hlt
      rw [(hlowK m.val (by omega)).2]
      exact hzeros m hm hlt
    · rw [hprefixBelow.1]
      exact hfirst
    · rw [(hlowK (compileAdvice (ceilLogTwo n)).t (by omega)).2,
        hprefixBelow.2]
      exact hmarkFirst
  · intro v hv' _ j hj hlt
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, ht'] at hlt
    obtain ⟨a, b, c⟩ :=
      hvalues.earlierTargets w hw hnotPrefix j hj hlt
    rw [hoff] at hlt
    obtain ⟨hso, hsp, hst⟩ := hsumBelow j.val (by omega) (by omega)
    rw [hso, hsp, hst, (hlowK j.val hlt).1, (hlowK j.val hlt).2]
    exact ⟨a, b, c⟩
  · intro v hv' hs
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hs
    cases hs
  · intro v hv' _
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, ht', hoff]
    obtain ⟨hso, hsp, hst⟩ := hsumBelow k (by omega) (Nat.le_refl _)
    rw [hso, hsp, hst, hnewU, hnewB]
    exact ⟨hnz, rfl, rfl⟩
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesPrefixAllStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesAllStep`.
 PREFIX phase: the host edge is P1 or P3, every other edge is a
free-source frame. Consumer: bankWordPassValuesAllStep. -/
theorem widthWordPassValuesPrefixAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨_, hindex, _, _, _, _, hc, _, hother⟩ := hfields
  by_cases he : e = w.host
  · by_cases hidx : w.index < (compileAdvice (ceilLogTwo n)).t
    · exact widthWordPassValuesPoneStep ring hn hsmallFive root s hs z hz e w
        hpass hvalues hw hphase he.symm hidx hno
    · exact widthWordPassValuesPthreeStep ring hn hsmallFive root s hs z hz e w
        hpass hvalues hw hphase he.symm (by omega) hno
  · have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]
        exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
      (Or.inl ⟨hxk, hxc, hyc⟩)

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesBackAllStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesAllStep`.
 BACK phase: the edge into the cursor host is B0 or B1; the host,
target and free sources are frames. Consumer:
bankWordPassValuesAllStep. -/
theorem widthWordPassValuesBackAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .backRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := widthWordPassWidth hsmallFive
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hne := clockNeighborDifferent ring hn2 e
  have hTQ := hpass.2.2
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  obtain ⟨w₀, hw₀, hfields⟩ := hpass.2.1
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hipos, hit, htarget, hhost, hcur, hjv, htk, htb,
    hhk, hother⟩ := hfields
  have hsuccm :
      ring.rightNeighbor
        (L3.EWord.site ring root
          (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)) =
        w.host := by
    rw [hhost, L3.EWord.siteSuccessor]
    congr 1
    omega
  have hTQ' : w.host ≠ w.target → (z.2.1 w.target).si.cur = .NONE :=
    fun hne' => hTQ w hw (Or.inl ⟨hphase, hne'⟩)
  have hhostkind : w.host ≠ w.target → (z.2.1 w.host).si.kind = .OFF := by
    intro hne'
    have := hhk
    rw [if_neg hne'] at this
    exact this
  have hhostroot : w.host = w.target → (z.2.1 w.host).si.kind = .ROOT := by
    intro heq
    have := hhk
    rw [if_pos heq] at this
    exact this
  by_cases he : e = L3.EWord.site ring root
      (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)
  · have hrne : ring.rightNeighbor e = w.host := by
      rw [he]
      exact hsuccm
    have hem : e ≠ w.host := by
      rw [he, hhost]
      exact bankWordPassSiteNe ring root _ _ (by omega) (by omega) (by omega)
    have het : e ≠ w.target := by
      rw [he, htarget]
      exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
    have hxfree := hother e hem het
    have hykind :
        (z.2.1 (ring.rightNeighbor e)).si.kind ≠ .PREFIX := by
      rw [hrne]
      by_cases hht : w.host = w.target
      · rw [hhostroot hht]
        exact fun h => by cases h
      · rw [hhostkind hht]
        exact fun h => by cases h
    have hycur : (z.2.1 (ring.rightNeighbor e)).si.cur = .BACK := by
      rw [hrne]
      exact hcur
    have hyj : (z.2.1 (ring.rightNeighbor e)).si.j.val = w.index := by
      rw [hrne]
      exact hjv
    by_cases hi1 : 1 < w.index
    · have hj' : 1 < (z.2.1 (ring.rightNeighbor e)).si.j.val := by
        rw [hyj]
        exact hi1
      obtain ⟨hrow, _, _, _⟩ :=
        bankWordPassBackMoveFields _ _ hfa hfl hfr hxfree hycur hj' hykind
      have hquiet :=
        bankWordPassBackMoveQuiet _ _ hfa hfl hfr hxfree hycur hj' hykind
      obtain ⟨w', hw', hp', _, ht', _⟩ :=
        bankWordPassGhostBackMove
          root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hyj
      have hworkerNew :
          (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]
        exact hw'
      have hvis :
          ∀ i : Fin n,
            wordVisible (bankWordEpochNext ring root z e).2.1 i =
              wordVisible z.2.1 i := by
        intro i
        change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
        exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
      exact bankWordPassValuesQuietMove ring root z
        (bankWordEpochNext ring root z e) w w' hvalues hw hnotPrefix
        hworkerNew
        (fun h => by rw [hp'] at h; cases h)
        (fun h => by rw [hp'] at h; cases h)
        ht' hvis
        (fun h => by rw [hp'] at h; cases h)
    · have hi : w.index = 1 := by omega
      have hj' : (z.2.1 (ring.rightNeighbor e)).si.j.val = 1 := by
        rw [hyj]
        exact hi
      obtain ⟨hrow, hx, _, _⟩ :=
        bankWordPassBackInitFields _ _ hfa hfl hfr hxfree hycur hj' hykind
      have hquiet :=
        bankWordPassBackInitQuiet _ _ hfa hfl hfr hxfree hycur hj' hykind
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostBackInit
          root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hi
      have hworkerNew :
          (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]
        exact hw'
      have hvis :
          ∀ i : Fin n,
            wordVisible (bankWordEpochNext ring root z e).2.1 i =
              wordVisible z.2.1 i := by
        intro i
        change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
        exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
      have hsiSource :
          ((bankWordEpochNext ring root z e).2.1 e).si =
            setCursor (z.2.1 e).si .SUM 0 false false true := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      exact bankWordPassValuesQuietMove ring root z
        (bankWordEpochNext ring root z e) w w' hvalues hw hnotPrefix
        hworkerNew
        (fun h => by rw [hp'] at h; cases h)
        (fun h => by rw [hp'] at h; cases h)
        ht' hvis
        (fun _ => by
          rw [hh', hi', hsiSource]
          exact ⟨rfl, rfl, rfl⟩)
  · by_cases heh : e = w.host
    · by_cases hht : w.host = w.target
      · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inr (Or.inl
            ⟨by rw [heh]; exact hhostroot hht,
             by rw [heh, hht]; exact htb⟩))
      · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inr (Or.inr
            ⟨by rw [heh]; exact hhostkind hht,
             by rw [heh]; exact hcur⟩))
    · by_cases het : e = w.target
      · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inr (Or.inl
            ⟨by rw [het]; exact htk, by rw [het]; exact htb⟩))
      · have hxfree := hother e heh het
        obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
        have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
          by_cases hj : ring.rightNeighbor e = w.host
          · exfalso
            apply he
            apply bankWordPassRightNeighborInjective ring
            rw [hj, hsuccm]
          · by_cases hjt : ring.rightNeighbor e = w.target
            · rw [hjt, hTQ' (fun h => hj (hjt.trans h.symm))]
              exact fun h => by cases h
            · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
              exact fun h => by cases h
        exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inl ⟨hxk, hxc, hyc⟩)

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesSumAllStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesAllStep`.
 SUM phase: the host edge is S0 or S1; the busy target and free
sources are frames. Consumer: bankWordPassValuesAllStep. -/
theorem widthWordPassValuesSumAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hTQ' : (z.2.1 w.target).si.cur = .NONE :=
    hpass.2.2 w hw (Or.inr hphase)
  obtain ⟨w₀, hw₀, hfields⟩ := hpass.2.1
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hit, htarget, hhost, hk, hc, hjv, htk, htb,
    hother⟩ := hfields
  by_cases he : e = w.host
  · by_cases hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t
    · exact widthWordPassValuesSzeroStep ring hn hsmallFive root z e w hpass
        hvalues hw hphase he.symm hidx hno
    · exact widthWordPassValuesSoneStep ring hn hsmallFive root z e w hpass
        hvalues hw hphase he.symm (by omega) hno
  · by_cases het : e = w.target
    · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
        (Or.inr (Or.inl
          ⟨by rw [het]; exact htk, by rw [het]; exact htb⟩))
    · have hxfree := hother e he het
      obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
      have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
        by_cases hj : ring.rightNeighbor e = w.host
        · rw [hj, hc]
          exact fun h => by cases h
        · by_cases hjt : ring.rightNeighbor e = w.target
          · rw [hjt, hTQ']
            exact fun h => by cases h
          · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
            exact fun h => by cases h
      exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
        (Or.inl ⟨hxk, hxc, hyc⟩)

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesReadyAllStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesAllStep`.
 READY phase: the host edge is A1 (target below n-1) or the
completing A0 (target n-1); every other edge is a free-source frame.
Consumer: bankWordPassValuesAllStep. -/
theorem widthWordPassValuesReadyAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .readyRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  obtain ⟨w₀, hw₀, hfields⟩ := hpass.2.1
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, _, hkn, hhostSite, _, hk, hb, hc, hother⟩ := hfields
  by_cases he : e = w.host
  · have hsucc :
        ring.rightNeighbor e = L3.EWord.site ring root (k + 1) := by
      rw [he, hhostSite]
      exact L3.EWord.siteSuccessor ring root k
    by_cases hkn1 : k + 1 < n
    · have hnotroot : ring.rightNeighbor e ≠ root := by
        rw [hsucc]
        have h := bankWordPassSiteNe ring root (k + 1) 0 hkn1 (by omega)
          (by omega)
        rw [L3.EWord.siteZero] at h
        exact h
      have hpy :
          (postW (z.2.1 e)
            (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
        rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
        simp [hnotroot]
      exact bankWordPassValuesAoneStep ring hn root z e w hpass hvalues
        hw hphase he.symm hnotroot hpy hno
    · have hkn' : k + 1 = n := by omega
      have hroot : ring.rightNeighbor e = root := by
        rw [hsucc, hkn']
        exact bankWordPassSiteWrap ring root
      have hpy :
          (postW (z.2.1 e)
            (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
        rw [widthWordPassResponderFlag ring hn hsmallFive root s hs z hz e]
        simp [hroot]
      obtain ⟨hfa, hfl, hfr⟩ :=
        bankWordPassFlagsQuiet
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
      have hk' : (z.2.1 e).si.kind = .ROOT := by
        rw [he]
        exact hk
      have hb' : (z.2.1 e).si.busy = false := by
        rw [he]
        exact hb
      have hc' : (z.2.1 e).si.cur = .NONE := by
        rw [he]
        exact hc
      have hyfree :
          freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
        hother _ (fun h => hne (h.trans he.symm))
      obtain ⟨hrow, _, _, _⟩ :=
        bankWordPassTerminalFields _ _ hfa hfl hfr hk' hb' hc' hpy hyfree
      obtain ⟨hwnone, _⟩ :=
        bankWordPassGhostTerminal
          root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hroot
      have hworkerNone :
          (bankWordEpochNext ring root z e).2.2.worker = none := by
        rw [bankWordPassGhostWorker, hw]
        exact hwnone
      have hnom : e = bankWordPassNomination ring root z := by
        rw [bankWordPassNominationHost ring root z w hw
          (Or.inr (Or.inr hphase))]
        exact he
      rcases (widthWordPassReadyStep ring hn hsmallFive root s hs z hz e hpass.1
          w hw hphase hpass.2.1 hpass.2.2 hno).2 hnom with
        ⟨hsh, _⟩ | hret
      · obtain ⟨v, hv, _⟩ := hsh.2.1
        rw [hworkerNone] at hv
        cases hv
      · exact widthWordPassValuesAZeroStep ring hn hsmallFive root z e w hpass
          hvalues hw hphase he.symm hroot hno hpy hret
  · have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]
        exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
      (Or.inl ⟨hxk, hxc, hyc⟩)

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesAllStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesRun`.
 The Layer W all-edge step: on every selected edge without a
hard S1 at a reachable pass state, the word-value layer
BankWordPassValues is kept (including the retired publication at
the completing A0). The compiled widths supply tap 0 for
the S1 nonzero window (for t ≥ 18 the compiled taps are empty).
Consumer: bankWordPassValuesRun. -/
theorem widthWordPassValuesAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨w, hw, _⟩ := hpass.2.1
  cases hphase : w.phase with
  | prefixRun =>
      exact widthWordPassValuesPrefixAllStep ring hn hsmallFive root s hs z hz
        e w hpass hvalues hw hphase hno
  | backRun =>
      exact widthWordPassValuesBackAllStep ring hn hsmallFive root z e w hpass
        hvalues hw hphase hno
  | sumRun =>
      exact widthWordPassValuesSumAllStep ring hn hsmallFive root z e w hpass
        hvalues hw hphase hno
  | readyRun =>
      exact widthWordPassValuesReadyAllStep ring hn hsmallFive root s hs z hz
        e w hpass hvalues hw hphase hno

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordPassValuesRun`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletedClean`, `widthWordEpochCompletedRetired`.
 Layer G and Layer W along any no-hard-S1 word from a reachable
pass state: either the pass is still on (both layers hold at the end
and nothing completed), or the first completion is clean.
Consumer: bankWordPassCleanWordAtCompletion. -/
theorem widthWordPassValuesRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n),
      BankWordEpochReachable ring root s z →
      BankWordPassShape ring root z →
      BankWordPassValues ring root z →
      BankWordPassNoHardStart ring root z word →
      (BankWordPassShape ring root
          (L3.GrantDrainEntrance.grantDrainLabelRun
            (bankWordEpochNext ring root) z word) ∧
        BankWordPassValues ring root
          (L3.GrantDrainEntrance.grantDrainLabelRun
            (bankWordEpochNext ring root) z word) ∧
        ¬ BankWordPassCompletes ring root z word) ∨
      BankWordPassCleanCompletes ring root z word := by
  intro word
  induction word with
  | nil =>
      intro z _ hpass hvalues _
      exact Or.inl ⟨hpass, hvalues, fun h => h⟩
  | cons e es ih =>
      intro z hz hpass hvalues hnh
      obtain ⟨hno, hnh'⟩ := hnh
      have hz' := bankWordEpochReachableNext ring root s z hz e
      have hvalues' :=
        widthWordPassValuesAllStep ring hn hsmallFive root s hs z hz e
          hpass hvalues hno
      obtain ⟨hframe, hnom⟩ :=
        widthWordPassStep ring hn hsmallFive root s hs z hz e hpass hno
      have hcase :
          BankWordPassShape ring root (bankWordEpochNext ring root z e) ∨
            BankWordPassRetired ring root
              (bankWordEpochNext ring root z e) := by
        by_cases he : e = bankWordPassNomination ring root z
        · rcases hnom he with ⟨hp, _⟩ | hr
          · exact Or.inl hp
          · exact Or.inr hr
        · exact Or.inl (hframe he).1
      rcases hcase with hpass' | hret
      · have hnotret :
            ¬ BankWordPassRetired ring root
              (bankWordEpochNext ring root z e) := by
          intro hr
          obtain ⟨v, hv, _⟩ := hpass'.2.1
          rw [hr.2.1] at hv
          cases hv
        rcases ih _ hz' hpass' hvalues' hnh' with
          ⟨hend, hvend, hnc⟩ | hclean
        · left
          refine ⟨hend, hvend, ?_⟩
          intro hc
          have hc' :
              BankWordPassRetired ring root
                  (bankWordEpochNext ring root z e) ∨
                BankWordPassCompletes ring root
                  (bankWordEpochNext ring root z e) es := hc
          rcases hc' with hr | hc''
          · exact hnotret hr
          · exact hnc hc''
        · right
          exact Or.inr ⟨hnotret, hclean⟩
      · right
        exact Or.inl ⟨hret,
          (bankWordPassRetiredWordValues ring root _ hvalues' hret).1⟩

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordEpochLiveTrailStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLiveFromSeedReachable`.
 One service keeps the provenance: a fresh I0 launch starts a new
seed (the launch is genuine by ledger/ghost coherence and comes after
the first S1); otherwise the old trail continues without hard S1.
Consumer: bankWordEpochLiveFromSeedReachable. -/
theorem widthWordEpochLiveTrailStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hlive : BankWordEpochLiveFromSeed ring root s z)
    (e : Fin n) :
    BankWordEpochLiveFromSeed ring root s
      (bankWordEpochNext ring root z e) := by
  intro w' hw'
  have hw'' :
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).1 = some w' := hw'
  rcases bankWordPassGhostWorkerSomeCases _ _ _ _ _ _ _ _ w' hw'' with
    ⟨_, t, ht⟩ | ⟨_, hno, w, hw⟩
  · have hcoh :=
      (bankWordRenewalFrontierLedgerGhostCoherence
        ring root s z hz).1
    have hg : bankWordRenewalGenuine ring root z e := by
      unfold bankWordRenewalGenuine bankWordHardEpochGenuine
      change
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).isSome = true
      rw [hcoh, ht] <;> rfl
    have hone :=
      widthWordEpochSOneReachedOfGenuine ring hn hsmallFive root s hs z hz e hg
    let pre : BankWordRenewalPostSOne ring root s := ⟨z, hz, hone⟩
    let seed : BankWordRenewalFreshSeed ring root s :=
      ⟨bankWordRenewalNext ring root s pre e,
        bankWordRenewalFreshAfterGenuine ring root s pre e hg⟩
    exact ⟨seed, [], rfl, trivial, trivial⟩
  · obtain ⟨seed, word, hrun, hnh, hl⟩ := hlive w hw
    refine ⟨seed, word ++ [e], ?_, ?_, ?_⟩
    · rw [bankWordEpochRunAppend, hrun]
      rfl
    · apply bankWordPassNoHardStartSnoc ring root word seed.1.1 e hnh
      rw [hrun]
      exact hno
    · apply bankWordPassLiveSnoc ring root word seed.1.1 e hl
      rw [hrun]
      exact ⟨w', hw'⟩

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordEpochLiveFromSeedReachable`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletedClean`, `widthWordEpochCompletedRetired`.
 Every reachable epoch state satisfies the live-trail provenance.
Consumer: bankWordEpochCompletedClean. -/
theorem widthWordEpochLiveFromSeedReachable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordEpochLiveFromSeed ring root s z := by
  have hall : ∀ (word : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachable ring root s a →
      BankWordEpochLiveFromSeed ring root s a →
      BankWordEpochLiveFromSeed ring root s
        (bankWordEpochRun ring root a word) := by
    intro word
    induction word with
    | nil => intro a _ h; exact h
    | cons e es ih =>
        intro a ha h
        exact ih _ (bankWordEpochReachableNext ring root s a ha e)
          (widthWordEpochLiveTrailStep ring hn hsmallFive root s hs a ha h e)
  obtain ⟨word, hword⟩ := hz
  have hbase : BankWordEpochLiveFromSeed ring root s
      (bankWordEpochStart s) := by
    intro w hw
    cases hw
  rw [← hword]
  exact hall word (bankWordEpochStart s) ⟨[], rfl⟩ hbase

end

section
open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- Width port of `bankWordEpochCompletedClean`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordCompletionCleanWordTarget`, `widthWordCompletionFutureInvariant`, `widthWordCompletionGeneratedControl`.
 Every reachable completed state of the original projected W
epoch is the first completion of a no-hard-S1 word from an actual
fresh seed; hence (every compiled width) its visible word
satisfies CleanWorkerWordValues and every SI is free.
Consumer: the hcompletion premise of
bankWordProjectedClockOfCompletionBridge (QWord base and monitor
endpoint of BankWordProjectedTarget). -/
theorem widthWordEpochCompletedClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    CleanWorkerWordValues ring root z.2.1 ∧
      ∀ i : Fin n, freeSI (z.2.1 i).si = true := by
  obtain ⟨word, hword⟩ := hz
  obtain ⟨r, hr⟩ := hcomp
  -- split off the completing letter
  cases hrev : word.reverse with
  | nil =>
      have hnil : word = [] := List.reverse_eq_nil_iff.mp hrev
      subst hnil
      rw [← hword] at hr
      cases hr
  | cons e rest =>
      have hsplit : word = rest.reverse ++ [e] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst hsplit
      rw [bankWordEpochRunAppend] at hword
      let y := bankWordEpochRun ring root (bankWordEpochStart s)
        rest.reverse
      have hy : BankWordEpochReachable ring root s y :=
        ⟨rest.reverse, rfl⟩
      have hzy : bankWordEpochNext ring root y e = z := hword
      have hr' :
          (wWorkerReceiptStep root e (ring.rightNeighbor e)
            (y.2.2.clock + 1)
            (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e
              (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
              (y.2.2.validation e)
              (y.2.2.validation (ring.rightNeighbor e)))
            y.2.2.worker).2 = some r := by
        have h2 : (bankWordEpochNext ring root y e).2.2.completion =
            some r := by
          rw [hzy]
          exact hr
        exact h2
      obtain ⟨hnone, hno, w, hw⟩ :=
        bankWordPassGhostCompletionCases _ _ _ _ _ _ _ _ r hr'
      obtain ⟨seed, word0, hrun, hnh, hl⟩ :=
        widthWordEpochLiveFromSeedReachable ring hn hsmallFive root s hs y hy
          w hw
      have hnh' : BankWordPassNoHardStart ring root seed.1.1
          (word0 ++ [e]) := by
        apply bankWordPassNoHardStartSnoc ring root word0 seed.1.1 e hnh
        rw [hrun]
        exact hno
      have hend :
          bankWordEpochRun ring root seed.1.1 (word0 ++ [e]) = z := by
        rw [bankWordEpochRunAppend, hrun]
        exact hzy
      have hworkerNone : z.2.2.worker = none := by
        have h2 : (bankWordEpochNext ring root y e).2.2.worker = none :=
          hnone
        rw [hzy] at h2
        exact h2
      rcases widthWordPassValuesRun ring hn hsmallFive root s hs
          (word0 ++ [e]) seed.1.1 seed.1.2.1
          (widthWordPassShapeAtFreshSeed ring hn hsmallFive root s hs seed)
          (widthWordPassValuesBase ring hn hsmallFive root s hs seed) hnh' with
        ⟨hshape, _, _⟩ | hclean
      · exfalso
        rw [bankWordPassLabelRunEq, hend] at hshape
        obtain ⟨v, hv, _⟩ := hshape.2.1
        rw [hworkerNone] at hv
        cases hv
      · obtain ⟨hret, hcw⟩ :=
          bankWordPassCleanAtLastLetter ring root word0 seed.1.1 e hl hclean
        rw [hend] at hret hcw
        exact ⟨hcw, hret.2.2.2⟩

end

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthWordPassResponderFlag
#print axioms L3.RenewalReferenceClock.widthWordPassPrefixStep
#print axioms L3.RenewalReferenceClock.widthWordPassBackStep
#print axioms L3.RenewalReferenceClock.widthWordPassSumStep
#print axioms L3.RenewalReferenceClock.widthWordPassReadyStep
#print axioms L3.RenewalReferenceClock.widthWordPassStep
#print axioms L3.RenewalReferenceClock.widthWordPassRankWord
#print axioms L3.RenewalReferenceClock.widthWordPassLaunchRankBound
#print axioms L3.RenewalReferenceClock.widthWordPassWorkerHitsBelowQuota
#print axioms L3.RenewalReferenceClock.widthWordPassIncomingDoneCompletes
#print axioms L3.RenewalReferenceClock.widthWordPassNonvalidatingAfterGenuine
#print axioms L3.RenewalReferenceClock.widthWordPassShapeAtFreshSeed
#print axioms L3.RenewalReferenceClock.widthWordPassFreshWorkerHitsBelowQuota
#print axioms L3.RenewalReferenceClock.widthWordRetryPrefixInvariantSeed
#print axioms L3.RenewalReferenceClock.widthWordRetryRootLeaseStep
#print axioms L3.RenewalReferenceClock.widthWordRetryPrefixStep
#print axioms L3.RenewalReferenceClock.widthWordRetryPrefixWord
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshRetryCover
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshRetryEstimate
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshFourCostHolds
#print axioms L3.RenewalReferenceClock.widthWordEpochFreshCutFourCostHolds
#print axioms L3.RenewalReferenceClock.widthWordEpochCompletionFiveCostHolds
#print axioms L3.RenewalReferenceClock.widthWordPassValuesBase
#print axioms L3.RenewalReferenceClock.widthWordPassValuesAZeroStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesPoneStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesPthreeStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesSzeroStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesSoneStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesPrefixAllStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesBackAllStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesSumAllStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesReadyAllStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesAllStep
#print axioms L3.RenewalReferenceClock.widthWordPassValuesRun
#print axioms L3.RenewalReferenceClock.widthWordEpochLiveTrailStep
#print axioms L3.RenewalReferenceClock.widthWordEpochLiveFromSeedReachable
#print axioms L3.RenewalReferenceClock.widthWordEpochCompletedClean
