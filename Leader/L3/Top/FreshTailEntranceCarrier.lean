import Leader.L3.Top.FreshTailCohortWave

/-!
Q7c P.3 J5: source-zero sampled-atom / full-carrier coherence.

The module establishes the induction base and the selected off-pair
and D-stay rows of the entrance invariant. The general one-edge
producer, especially the U-to-D rekey and incoming D-transfer cases,
is not claimed. Consumer: topFreshTailCohortFirstGenuineWaveBase.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every physical comparison D carrying an actual source-zero
sample atom carries the unique full root identity born at the
sample service, and remains a true-tail D.
Consumer: topFreshTailCohortFirstGenuineWaveBase. -/
def TopFreshTailEntranceCarrierInvariant
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  ∀ (j : Fin (topClockSpan n))
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool),
    sigma.id.lane = .comparison →
    sigma.id.site = certSite s 0 →
    (Z.1.1 (certSite s j.val)).qOut = .D value tail →
    (Z.1.2.current (certSite s j.val)).comparison.out.atom =
      some (.sampled sigma.id) →
    (topFreshTailGenealogy ring C s Z).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true

/-- Initial D outputs are inherited, with inherited comparison
atoms, so no source-zero sampled-atom antecedent is present.
Consumer: topFreshTailCohortFirstGenuineWaveBase, induction base. -/
theorem topFreshTailEntranceCarrierInitial
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailEntranceCarrierInvariant ring C s
      ((C, digitAuditInitial (piD C)), []) := by
  unfold TopFreshTailEntranceCarrierInvariant
  intro j sigma value tail _ _ hdata hatom
  have hinitial :=
    topFreshTailAuditInitialDataOrigin
      C s j value tail hdata
  rw [hinitial.2] at hatom
  cases hatom

/-- If both endpoints of the actual service avoid a particular
source home, the physical D, its recorded comparison atom and
its FULL genealogy identity all frame. The old invariant
therefore supplies this home's next-state sample authentication.
Consumer: topFreshTailCohortFirstGenuineWaveBase, off-pair row. -/
theorem topFreshTailEntranceCarrierAwayHome
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (j : Fin (topClockSpan n))
    (hsource : certSite s j.val ≠ e)
    (htarget : certSite s j.val ≠ ring.rightNeighbor e)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hlane : sigma.id.lane = .comparison)
    (hsite : sigma.id.site = certSite s 0)
    (hdata :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .D value tail)
    (hatom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
          some (.sampled sigma.id)) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true := by
  have hpair :=
    topFreshTailCausalOffPairSlotAgreement
      ring C s Z e hqueue j hsource htarget
  have holdData :
      (Z.1.1 (certSite s j.val)).qOut = .D value tail :=
    hpair.1.symm.trans hdata
  have hatomFrame :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom := by
    change ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
      (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom
    simp only [digitAuditStep, digitGhostStep,
      if_neg hsource, if_neg htarget]
  have holdAtom :
      (Z.1.2.current (certSite s j.val)).comparison.out.atom =
        some (.sampled sigma.id) :=
    hatomFrame.symm.trans hatom
  obtain ⟨hcarrier, htail⟩ :=
    hinv j sigma value tail hlane hsite holdData holdAtom
  exact ⟨hpair.2.trans hcarrier, htail⟩

/-- An edge avoiding the entire protected source arc preserves
the whole sample/full-carrier invariant, with no assumptions
on its private QI/QO/QC labels.
Consumer: topFreshTailCohortFirstGenuineWaveBase, away-edge case. -/
theorem topFreshTailEntranceCarrierAwayStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (hsource : ∀ j : Fin (topClockSpan n),
      certSite s j.val ≠ e)
    (htarget : ∀ j : Fin (topClockSpan n),
      certSite s j.val ≠ ring.rightNeighbor e) :
    TopFreshTailEntranceCarrierInvariant ring C s
      (topFixedTraceNext ring C Z e) := by
  unfold TopFreshTailEntranceCarrierInvariant
  intro j sigma value tail hlane hsite hdata hatom
  exact topFreshTailEntranceCarrierAwayHome
    ring C s Z e hqueue hinv j (hsource j) (htarget j)
    sigma value tail hlane hsite hdata hatom

/-- A selected OLD physical D which remains a D at its own
source site retains the OLD comparison atom and the exact
full genealogy carrier (not merely its origin family).
Consumer: topFreshTailCohortFirstGenuineWaveBase,
selected-source blocked D row. -/
theorem topFreshTailEntranceCarrierSourceDataStay
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (j : Fin (topClockSpan n))
    (hsource : e = certSite s j.val)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hlane : sigma.id.lane = .comparison)
    (hsite : sigma.id.site = certSite s 0)
    (hdataOld :
      (Z.1.1 (certSite s j.val)).qOut = .D value tail)
    (hdataNew :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .D value tail)
    (hatom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
          some (.sampled sigma.id)) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true := by
  subst e
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z hqueue.trace.1 j
  have hframe :=
    topFreshTailAuditPhysicalOldSourceAtom
      ring (by omega : 2 ≤ n) C Z
      (certSite s j.val) value tail hgeom.1 hgeom.2.1
      hdataOld hdataNew
  have holdAtom :
      (Z.1.2.current (certSite s j.val)).comparison.out.atom =
        some (.sampled sigma.id) :=
    hframe.symm.trans hatom
  have hslot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z (certSite s j.val))).slots j =
      (topFreshTailGenealogy ring C s Z).slots j := by
    rw [topFreshTailCausalReplayNext]
    change
      topFreshTailGenealogyNextSlot ring C s
        (topFreshTailGenealogy ring C s Z)
        (certSite s j.val) j =
      (topFreshTailGenealogy ring C s Z).slots j
    simp [topFreshTailGenealogyNextSlot,
      hqueue.trace.2, hdataNew, hdataOld]
  obtain ⟨holdCarrier, htail⟩ :=
    hinv j sigma value tail hlane hsite hdataOld holdAtom
  exact ⟨hslot.trans holdCarrier, htail⟩

/-- The actual source-border U-to-D service constructs a
fresh carrier whose origin and birth are BOTH the service
clock, plus an authentic comparison sample at the same home.
Consumer: topFreshTailCohortFirstGenuineWaveBase,
new-sample row of the intended one-edge proof. -/
theorem topFreshTailEntranceCarrierBorderUnreadBirth
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hzero : j.val = 0)
    (hunread : (Z.1.1 e).qOut = .U) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
        some { origin := .freshBorder (Z.1.2.clock + 1),
               born := Z.1.2.clock + 1 } ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      .D (Z.1.1 e).d true ∧
    ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample
        (topFixedTraceNext ring C Z e).1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site = e ∧
      sample.id.time = Z.1.2.clock + 1 ∧
      sample.tail = true ∧
      ((topFixedTraceNext ring C Z e).1.2.current
        e).comparison.out.atom = some (.sampled sample.id) := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z hreach j
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hmarker : (Z.1.1 e).beta = true := by
    rw [hsite, hzero]
    have hh := hgeom.2.2.1
    rw [hzero] at hh
    simpa using hh
  have htrace :=
    topFreshTailGenealogyTraceReached
      ring C s Z hreach
  have hgenealogy :=
    topFreshTailCausalUnreadBorder
      ring C s (topFreshTailGenealogy ring C s Z)
      e j hsite hzero
      (by rw [htrace]; exact hunread)
      (by rw [htrace]; exact hxl)
      (by rw [htrace]; exact hyl)
  have hnewSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
        some { origin := .freshBorder (Z.1.2.clock + 1),
               born := Z.1.2.clock + 1 } := by
    rw [topFreshTailCausalReplayNext]
    rw [htrace] at hgenealogy
    exact hgenealogy
  have hphysical :=
    topFreshTailFifoUnreadSamples
      ring C Z e hxl hyl hunread
  have hnewD :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D (Z.1.1 e).d true := by
    rw [hmarker] at hphysical
    exact hphysical
  obtain ⟨sample, hrecord, hlane, hsampleSite,
    htime, _, htail, hatom⟩ :=
    topFreshTailAuditPhysicalUnreadSample
      ring C Z e hxl hyl hunread
  refine ⟨hnewSlot, hnewD, sample, hrecord, hlane,
    hsampleSite, htime, ?_, hatom⟩
  rw [hmarker] at htail
  exact htail

/-- A finite scheduler word wholly outside the protected
source arc keeps the full-carrier invariant from the raw
audit start. This is the complete off-arc fold, not the
still-open general J5 fold.
Consumer: topFreshTailCohortFirstGenuineWaveBase. -/
theorem topFreshTailEntranceCarrierAwayWord
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (haw : ∀ e : Fin n, e ∈ word →
      (∀ j : Fin (topClockSpan n), certSite s j.val ≠ e) ∧
      (∀ j : Fin (topClockSpan n),
        certSite s j.val ≠ ring.rightNeighbor e)) :
    TopFreshTailEntranceCarrierInvariant ring C s
      (topFixedTraceRun ring C word) := by
  have hfold :
      ∀ (letters : List (Fin n))
        (Z : TopFixedTraceState n),
        TopFreshTailCausalQueue ring C s Z →
        TopFreshTailEntranceCarrierInvariant ring C s Z →
        (∀ e : Fin n, e ∈ letters →
          (∀ j : Fin (topClockSpan n), certSite s j.val ≠ e) ∧
          (∀ j : Fin (topClockSpan n),
            certSite s j.val ≠ ring.rightNeighbor e)) →
        TopFreshTailEntranceCarrierInvariant ring C s
          (letters.foldl (topFixedTraceNext ring C) Z) := by
    intro letters
    induction letters with
    | nil =>
        intro Z _ hinv _
        exact hinv
    | cons e rest ih =>
        intro Z hqueue hinv haway
        have hedge := haway e (by simp)
        have hnext :=
          topFreshTailEntranceCarrierAwayStep
            ring C s Z e hqueue hinv hedge.1 hedge.2
        have hqueueNext :=
          topFreshTailCausalQueueStep
            ring C s hn hbad Z e hqueue
        have hrest :
            ∀ f : Fin n, f ∈ rest →
              (∀ j : Fin (topClockSpan n),
                certSite s j.val ≠ f) ∧
              (∀ j : Fin (topClockSpan n),
                certSite s j.val ≠ ring.rightNeighbor f) := by
          intro f hf
          exact haway f (List.mem_cons_of_mem e hf)
        change TopFreshTailEntranceCarrierInvariant ring C s
          (rest.foldl (topFixedTraceNext ring C)
            (topFixedTraceNext ring C Z e))
        exact ih (topFixedTraceNext ring C Z e)
          hqueueNext hnext hrest
  change TopFreshTailEntranceCarrierInvariant ring C s
    (word.foldl (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), []))
  exact hfold word ((C, digitAuditInitial (piD C)), [])
    (topFreshTailCausalQueueStart ring C s)
    (topFreshTailEntranceCarrierInitial ring C s) haw

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The OLD responder already holding D keeps both its comparison
atom and its full genealogy identity on a real scheduler service.
Consumer: topFreshTailEntranceCarrierStep, occupied responder row. -/
theorem topFreshTailEntranceCarrierResponderDataStay
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (j : Fin (topClockSpan n))
    (hrespond : ring.rightNeighbor e = certSite s j.val)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hlane : sigma.id.lane = .comparison)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hold : (Z.1.1 (certSite s j.val)).qOut = .D value tail)
    (hatom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
          some (.sampled sigma.id)) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true := by
  have hleader := topFreshTailFirstBorderReachedNoLeader
    ring C hl Z hqueue.trace.1
  have hkeep := topFreshTailAuditPhysicalResponderDataKeep
    ring (by omega : 2 ≤ n) C Z e value tail
    (hleader e) (hleader (ring.rightNeighbor e))
    (by rw [hrespond]; exact hold)
  have hnewD :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .D value tail := by
    rw [← hrespond]
    exact hkeep.1
  have hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom := by
    rw [← hrespond]
    exact hkeep.2
  have hslot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
      (topFreshTailGenealogy ring C s Z).slots j := by
    rw [topFreshTailCausalReplayNext]
    change topFreshTailGenealogyNextSlot ring C s
      (topFreshTailGenealogy ring C s Z) e j =
      (topFreshTailGenealogy ring C s Z).slots j
    simp [topFreshTailGenealogyNextSlot,
      hqueue.trace.2, hnewD, hold]
  obtain ⟨holdCarrier, htail⟩ :=
    hinv j sigma value tail hlane hzeroSite
      hold (hnewAtom.symm.trans hatom)
  exact ⟨hslot.trans holdCarrier, htail⟩

/-- A positive-home U-to-D service generates a comparison sample
with that home's site, which is distinct from source home zero.
Consumer: topFreshTailEntranceCarrierStep, positive U case. -/
theorem topFreshTailEntranceCarrierPositiveUnreadNotZero
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hsource : e = certSite s j.val)
    (hpositive : 0 < j.val)
    (hunread : (Z.1.1 e).qOut = .U)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        e).comparison.out.atom = some (.sampled sigma.id)) :
    False := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hreach j
  have hxl : (Z.1.1 e).l = false := by
    rw [hsource]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsource]
    exact hgeom.2.1
  obtain ⟨made, _, _, hmadeSite, _, _, _, hmadeAtom⟩ :=
    topFreshTailAuditPhysicalUnreadSample
      ring C Z e hxl hyl hunread
  have hsameId : made.id = sigma.id :=
    DigitAtom.sampled.inj
      (Option.some.inj (hmadeAtom.symm.trans hnewAtom))
  have heqSite : certSite s j.val = certSite s 0 := by
    calc
      certSite s j.val = e := hsource.symm
      _ = made.id.site := hmadeSite.symm
      _ = sigma.id.site :=
        congrArg (fun stamp : DigitStamp n => stamp.site) hsameId
      _ = certSite s 0 := hzeroSite
  have hr : 0 < topClockSpan n := by
    have hh := cert_rho_ge_three n hn
    omega
  have hident := topFreshTailCausalSourceSiteInjective
    s hn j (⟨0, hr⟩ : Fin (topClockSpan n))
    (by simpa only [Fin.val_mk] using heqSite)
  have hzero := congrArg Fin.val hident
  change j.val = 0 at hzero
  omega

/-- A real source-zero unread sample has the exact new-clock
full carrier, and any asserted sampled output atom at that
service is stamped by this same new clock.
Consumer: topFreshTailEntranceCarrierStep, zero U rekey. -/
theorem topFreshTailEntranceCarrierBorderSampleOfAtom
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hsource : e = certSite s j.val)
    (hzero : j.val = 0)
    (hunread : (Z.1.1 e).qOut = .U)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hnewD :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .D value tail)
    (hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
          some (.sampled sigma.id)) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true := by
  obtain ⟨hslot, hmadeD, made, _, _, _, hmadeTime,
    _, hmadeAtom⟩ :=
    topFreshTailEntranceCarrierBorderUnreadBirth
      ring C s hn hbad Z hreach e j hsource hzero hunread
  have hnewAtE :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D value tail := by
    have hh := hnewD
    rw [← hsource] at hh
    exact hh
  have hnewAtomAtE :
      ((topFixedTraceNext ring C Z e).1.2.current
        e).comparison.out.atom = some (.sampled sigma.id) := by
    have hh := hnewAtom
    rw [← hsource] at hh
    exact hh
  have hsameId : made.id = sigma.id :=
    DigitAtom.sampled.inj
      (Option.some.inj (hmadeAtom.symm.trans hnewAtomAtE))
  have hbornTime : Z.1.2.clock + 1 = sigma.id.time :=
    hmadeTime.symm.trans
      (congrArg (fun stamp : DigitStamp n => stamp.time) hsameId)
  have hfull :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } := by
    rw [hbornTime] at hslot
    exact hslot
  have hboth :
      OutTok.D (Z.1.1 e).d true = OutTok.D value tail :=
    hmadeD.symm.trans hnewAtE
  have ht := congrArg outT hboth
  have htail : tail = true := by
    simpa [outT] using ht.symm
  exact ⟨hfull, htail⟩

/-- Source D transport to an OLD empty positive home copies the
full old carrier, its sampled comparison atom, and its tail bit;
a source rearm U child is not the moving D.
Consumer: topFreshTailEntranceCarrierStep, D-move row. -/
theorem topFreshTailEntranceCarrierIncomingDataMove
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (i : Fin (topClockSpan n))
    (hnext : i.val + 1 < topClockSpan n)
    (hsource : e = certSite s i.val)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hlane : sigma.id.lane = .comparison)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hdata : (Z.1.1 e).qOut = .D value tail)
    (hsourceAtom :
      (Z.1.2.current e).comparison.out.atom =
        some (.sampled sigma.id))
    (htarget :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots
      (⟨i.val + 1, hnext⟩ : Fin (topClockSpan n)) =
        some { origin := .freshBorder sigma.id.time,
               born := sigma.id.time } ∧
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (i.val + 1))).qOut = .D value tail ∧
    ((topFixedTraceNext ring C Z e).1.2.current
      (certSite s (i.val + 1))).comparison.out.atom =
        some (.sampled sigma.id) ∧
    tail = true := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 i
  have hxl : (Z.1.1 e).l = false := by
    rw [hsource]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsource]
    exact hgeom.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta =
      false := by
    rw [hsource]
    have hneq : i.val + 1 ≠ topClockSpan n := by omega
    have hh := hgeom.2.2.2
    rw [if_neg hneq] at hh
    exact hh
  have hneighbor :
      ring.rightNeighbor e = certSite s (i.val + 1) := by
    rw [hsource]
    exact topFreshTailFirstBorderNeighborSite ring s i.val
  have holdData :
      (Z.1.1 (certSite s i.val)).qOut = .D value tail := by
    rw [← hsource]
    exact hdata
  have holdAtom :
      (Z.1.2.current (certSite s i.val)).comparison.out.atom =
        some (.sampled sigma.id) := by
    rw [← hsource]
    exact hsourceAtom
  obtain ⟨hcarrier, htail⟩ :=
    hinv i sigma value tail hlane hzeroSite
      holdData holdAtom
  have htrace := hqueue.trace.2
  have hslotStep :=
    topFreshTailCausalDataMoveTarget
      ring (by omega : 2 ≤ n) C s
      (topFreshTailGenealogy ring C s Z)
      e i value tail
      { origin := .freshBorder sigma.id.time,
        born := sigma.id.time }
      hnext hsource
      (by rw [htrace]; exact hdata)
      (by rw [htrace]; exact htarget)
      (by rw [htrace]; exact hxl)
      (by rw [htrace]; exact hyl)
      (by rw [htrace]; exact hyb)
      hcarrier
  have hslotNext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
        (⟨i.val + 1, hnext⟩ : Fin (topClockSpan n)) =
        some { origin := .freshBorder sigma.id.time,
               born := sigma.id.time } := by
    rw [topFreshTailCausalReplayNext]
    exact hslotStep
  have hmove := topFreshTailFifoDataMove
    ring (by omega : 2 ≤ n) C Z e
    value tail hxl hyl hdata htarget hyb
  have hnewD :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s (i.val + 1))).qOut = .D value tail := by
    rw [← hneighbor]
    exact hmove.2
  have hatomFrame := topFreshTailAuditPhysicalMoveAtom
    ring (by omega : 2 ≤ n) C Z e
    value tail hxl hyl hdata hyb htarget
  have hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s (i.val + 1))).comparison.out.atom =
        some (.sampled sigma.id) := by
    rw [← hneighbor]
    exact hatomFrame.trans hsourceAtom
  exact ⟨hslotNext, hnewD, hnewAtom, htail⟩


/-- A scheduler service initiated at source home j preserves
zero-sample/full-carrier coherence at that home. The literal
OLD output cases are: E cannot create D, U samples at its
own home (zero rekeys, positive excludes zero ID), and D
either stays with its atom and identity or departs as E/U.
Consumer: topFreshTailEntranceCarrierStep. -/
theorem topFreshTailEntranceCarrierSourceStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (j : Fin (topClockSpan n))
    (hsource : e = certSite s j.val)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hlane : sigma.id.lane = .comparison)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hnewD :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .D value tail)
    (hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
          some (.sampled sigma.id)) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hxl : (Z.1.1 e).l = false := by
    rw [hsource]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsource]
    exact hgeom.2.1
  have hnewAtE :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D value tail := by
    have hh := hnewD
    rw [← hsource] at hh
    exact hh
  cases hold : (Z.1.1 (certSite s j.val)).qOut with
  | E =>
      have hOldE : (Z.1.1 e).qOut = .E := by
        rw [hsource]
        exact hold
      by_cases hzero : j.val = 0
      · have hbirth := topFreshTailCausalBadBorderBirthStep
          ring C s hn hbad Z e hqueue j hzero hsource hOldE
        rw [hbirth.1] at hnewAtE
        cases hnewAtE
      · have hpositive : 0 < j.val := by omega
        have hempty := topFreshTailCausalBadInteriorEmptyStep
          ring C s hn hbad Z e hqueue j hpositive hsource hOldE
        rw [hempty.1] at hnewAtE
        cases hnewAtE
  | U =>
      have hOldU : (Z.1.1 e).qOut = .U := by
        rw [hsource]
        exact hold
      by_cases hzero : j.val = 0
      · exact topFreshTailEntranceCarrierBorderSampleOfAtom
          ring C s hn hbad Z hqueue.trace.1
          e j hsource hzero hOldU
          sigma value tail hnewD hnewAtom
      · have hpositive : 0 < j.val := by omega
        have hnewAtEAtom :
            ((topFixedTraceNext ring C Z e).1.2.current
              e).comparison.out.atom =
                some (.sampled sigma.id) := by
          rw [← hsource] at hnewAtom
          exact hnewAtom
        exact False.elim
          (topFreshTailEntranceCarrierPositiveUnreadNotZero
            ring C s hn hbad Z hqueue.trace.1 e j
            hsource hpositive hOldU sigma hzeroSite
            hnewAtEAtom)
  | D oldValue oldTail =>
      have hOldD : (Z.1.1 e).qOut =
          .D oldValue oldTail := by
        rw [hsource]
        exact hold
      have hpossible := topFreshTailCausalDSourceOutcomes
        ring C Z e oldValue oldTail hxl hyl hOldD
      rcases hpossible with hstay | hdeparture
      · have hboth :
            OutTok.D oldValue oldTail =
              OutTok.D value tail := hstay.symm.trans hnewAtE
        have hv : oldValue = value := by
          have hh := congrArg
            (outV (compileAdvice (ceilLogTwo n))) hboth
          simpa [outV] using hh
        have ht : oldTail = tail := by
          have hh := congrArg outT hboth
          simpa [outT] using hh
        rw [hv, ht] at hold
        exact topFreshTailEntranceCarrierSourceDataStay
          ring C s hn hbad Z e hqueue hinv
          j hsource sigma value tail hlane hzeroSite
          hold hnewD hnewAtom
      · rw [hdeparture] at hnewAtE
        cases oldTail <;> cases hnewAtE


/-- If the selected responder is a source-arc home, its OLD D
is retained, an OLD U remains U, an empty marker home stays
empty, or an empty positive home receives the full D carrier
and sampled atom from its immediate predecessor. No other
responder D is possible under the OLD first-match QO rules.
Consumer: topFreshTailEntranceCarrierStep. -/
theorem topFreshTailEntranceCarrierResponderStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ z : Fin n, (C z).l = false)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z)
    (j : Fin (topClockSpan n))
    (hincoming : ring.rightNeighbor e = certSite s j.val)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hlane : sigma.id.lane = .comparison)
    (hzeroSite : sigma.id.site = certSite s 0)
    (hnewD :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .D value tail)
    (hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
          some (.sampled sigma.id)) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder sigma.id.time,
             born := sigma.id.time } ∧
    tail = true := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hyl : (Z.1.1 (certSite s j.val)).l = false :=
    hgeom.1
  have hleader := topFreshTailFirstBorderReachedNoLeader
    ring C hl Z hqueue.trace.1
  have hxl : (Z.1.1 e).l = false := hleader e
  have hphysical := topFreshTailCausalResponderPhysicalOutput
    ring (by omega : 2 ≤ n) C Z e
  rw [hincoming] at hphysical
  cases hold : (Z.1.1 (certSite s j.val)).qOut with
  | D oldValue oldTail =>
      have hsame :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut =
              .D oldValue oldTail := by
        simpa [hxl, hyl, hold, OutTok.isE] using hphysical
      have hboth :
          OutTok.D oldValue oldTail =
            OutTok.D value tail := hsame.symm.trans hnewD
      have hv : oldValue = value := by
        have hh := congrArg
          (outV (compileAdvice (ceilLogTwo n))) hboth
        simpa [outV] using hh
      have ht : oldTail = tail := by
        have hh := congrArg outT hboth
        simpa [outT] using hh
      rw [hv, ht] at hold
      exact topFreshTailEntranceCarrierResponderDataStay
        ring C s hn hl Z e hqueue hinv j hincoming
        sigma value tail hlane hzeroSite hold hnewAtom
  | U =>
      have hsame :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .U := by
        simpa [hxl, hyl, hold, OutTok.isE] using hphysical
      rw [hsame] at hnewD
      cases hnewD
  | E =>
      by_cases hzero : j.val = 0
      · have hmarker :
            (Z.1.1 (certSite s j.val)).beta =
              true := by
          simpa [hzero] using hgeom.2.2.1
        have hsame :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s j.val)).qOut = .E := by
          simpa [hxl, hyl, hmarker, hold,
            OutTok.isD, OutTok.isE] using hphysical
        rw [hsame] at hnewD
        cases hnewD
      · have hpositive : 0 < j.val := by omega
        have hmarker :
            (Z.1.1 (certSite s j.val)).beta =
              false := by
          simpa [hzero] using hgeom.2.2.1
        have hpredecessor :=
          topFreshTailCausalIncomingPredecessor
            ring hn s j hpositive e hincoming
        cases hsourceTok : (Z.1.1 e).qOut with
        | E =>
            have hsame :
                ((topFixedTraceNext ring C Z e).1.1
                  (certSite s j.val)).qOut = .E := by
              simpa [hxl, hyl, hmarker, hold, hsourceTok,
                OutTok.isD, OutTok.isE] using hphysical
            rw [hsame] at hnewD
            cases hnewD
        | U =>
            have hsame :
                ((topFixedTraceNext ring C Z e).1.1
                  (certSite s j.val)).qOut = .E := by
              simpa [hxl, hyl, hmarker, hold, hsourceTok,
                OutTok.isD, OutTok.isE] using hphysical
            rw [hsame] at hnewD
            cases hnewD
        | D oldValue oldTail =>
            have hnewSource :
                ((topFixedTraceNext ring C Z e).1.1
                  (certSite s j.val)).qOut =
                    .D oldValue oldTail := by
              simpa [hxl, hyl, hmarker, hold, hsourceTok,
                OutTok.isD, OutTok.isE, outV, outT]
                using hphysical
            have hboth :
                OutTok.D oldValue oldTail =
                  OutTok.D value tail :=
              hnewSource.symm.trans hnewD
            have hv : oldValue = value := by
              have hh := congrArg
                (outV (compileAdvice (ceilLogTwo n))) hboth
              simpa [outV] using hh
            have ht : oldTail = tail := by
              have hh := congrArg outT hboth
              simpa [outT] using hh
            have htargetOld :
                (Z.1.1 (ring.rightNeighbor e)).qOut =
                  .E := by
              rw [hincoming]
              exact hold
            have htargetAtom :
                ((topFixedTraceNext ring C Z e).1.2.current
                  (ring.rightNeighbor e)).comparison.out.atom =
                    some (.sampled sigma.id) := by
              rw [hincoming]
              exact hnewAtom
            have hsourceAtom :
                (Z.1.2.current e).comparison.out.atom =
                  some (.sampled sigma.id) := by
              have hframe := topFreshTailAuditPhysicalMoveAtom
                ring (by omega : 2 ≤ n) C Z e oldValue oldTail
                hxl
                (by rw [hincoming]; exact hyl)
                hsourceTok
                (by rw [hincoming]; exact hmarker)
                htargetOld
              exact hframe.symm.trans htargetAtom
            have hprevBound :
                j.val - 1 < topClockSpan n := by
              have hj := j.isLt
              omega
            have hnextBound :
                j.val - 1 + 1 < topClockSpan n := by
              have hj := j.isLt
              omega
            obtain ⟨hslotMoved, _, _, htailOld⟩ :=
              topFreshTailEntranceCarrierIncomingDataMove
                ring C s hn hbad Z e hqueue hinv
                (⟨j.val - 1, hprevBound⟩ :
                  Fin (topClockSpan n))
                hnextBound
                (by change e = certSite s (j.val - 1); exact hpredecessor)
                sigma oldValue oldTail hlane hzeroSite
                hsourceTok hsourceAtom htargetOld
            have hindex :
                (⟨j.val - 1 + 1, hnextBound⟩ :
                  Fin (topClockSpan n)) = j := by
              apply Fin.ext
              change j.val - 1 + 1 = j.val
              omega
            change
              (topFreshTailGenealogy ring C s
                (topFixedTraceNext ring C Z e)).slots
                  (⟨j.val - 1 + 1, hnextBound⟩ :
                    Fin (topClockSpan n)) =
                some { origin := .freshBorder sigma.id.time,
                       born := sigma.id.time } at hslotMoved
            rw [hindex] at hslotMoved
            have htailNew : tail = true := by
              rw [← ht]
              exact htailOld
            exact ⟨hslotMoved, htailNew⟩



/-- At an actual free OLD marked terminal port, no outgoing
D survives acceptance, regardless of unrelated source QI/QC
scratch. The accepted source is U for a true tail and E
for a false tail; it is never a second output D.
Consumer: topFreshTailEntranceCarrierStep, accepted terminal
departure exclusion. -/
theorem topFreshTailEntranceCarrierAcceptedTerminalDeparture
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hdata : (Z.1.1 e).qOut = .D value tail)
    (hmarker : (Z.1.1 (ring.rightNeighbor e)).beta = true)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      (if tail then .U else .E) ∧
    ∀ (newValue : Fin (compileAdvice (ceilLogTwo n)).topA)
      (newTail : Bool),
      ((topFixedTraceNext ring C Z e).1.1 e).qOut ≠
        .D newValue newTail := by
  have hdepart := topFreshTailAuditPhysicalPortDeparts
    ring C Z e value tail hxl hyl hdata hmarker hyi hyc
  constructor
  · exact hdepart
  · intro newValue newTail hnewD
    rw [hdepart] at hnewD
    cases tail <;> cases hnewD

/-- Full one-edge preservation of the sampled source-zero
D/full-carrier invariant. Every actual selected scheduler edge
is a source service, a responder service, or off both endpoints.
The OLD QO cases are discharged by the preceding two row lemmas.
Consumer: topFreshTailEntranceCarrierRun and
topFreshTailCohortFirstGenuineWaveBase. -/
theorem topFreshTailEntranceCarrierStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hreach : topClockReached ring C Z)
    (hinv : TopFreshTailEntranceCarrierInvariant ring C s Z) :
    TopFreshTailEntranceCarrierInvariant ring C s
      (topFixedTraceNext ring C Z e) := by
  have hqueue :=
    topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  unfold TopFreshTailEntranceCarrierInvariant
  intro j sigma value tail hlane hzeroSite hdata hatom
  by_cases hsource : certSite s j.val = e
  · exact topFreshTailEntranceCarrierSourceStep
      ring C s hn hbad Z e hqueue hinv
      j hsource.symm sigma value tail hlane hzeroSite
      hdata hatom
  · by_cases htarget :
        certSite s j.val = ring.rightNeighbor e
    · exact topFreshTailEntranceCarrierResponderStep
        ring C s hn hbad hl Z e hqueue hinv
        j htarget.symm sigma value tail hlane hzeroSite
        hdata hatom
    · exact topFreshTailEntranceCarrierAwayHome
        ring C s Z e hqueue hinv j hsource htarget
        sigma value tail hlane hzeroSite hdata hatom

/-- The exact full-carrier identity of a source-zero sampled
D survives every finite concrete scheduler word, not only
off-source words. Consumer: J5 first-genuine entrance,
topFreshTailCohortFirstGenuineWaveBase. -/
theorem topFreshTailEntranceCarrierRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n)) :
    TopFreshTailEntranceCarrierInvariant ring C s
      (topFixedTraceRun ring C word) := by
  have hfold :
      ∀ (letters : List (Fin n))
        (Z : TopFixedTraceState n),
        topClockReached ring C Z →
        TopFreshTailEntranceCarrierInvariant ring C s Z →
        TopFreshTailEntranceCarrierInvariant ring C s
          (letters.foldl (topFixedTraceNext ring C) Z) := by
    intro letters
    induction letters with
    | nil =>
        intro Z _ hinv
        exact hinv
    | cons e rest ih =>
        intro Z hreach hinv
        change TopFreshTailEntranceCarrierInvariant ring C s
          (rest.foldl (topFixedTraceNext ring C)
            (topFixedTraceNext ring C Z e))
        exact ih (topFixedTraceNext ring C Z e)
          (topClockReachedNext ring C Z e hreach)
          (topFreshTailEntranceCarrierStep
            ring C s hn hbad hl Z e hreach hinv)
  change TopFreshTailEntranceCarrierInvariant ring C s
    (word.foldl (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), []))
  exact hfold word ((C, digitAuditInitial (piD C)), [])
    (by rfl)
    (topFreshTailEntranceCarrierInitial ring C s)

/-- Every reachable trace inherits the global concrete-word
full-carrier coherence, including both the sample-time origin
and the independent birth timestamp.
Consumer: topFreshTailCohortAcceptedSampleRootAtTerminal and
topFreshTailCohortFirstGenuineWaveBase. -/
theorem topFreshTailEntranceCarrierReached
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Y : TopFixedTraceState n)
    (hreached : topClockReached ring C Y) :
    TopFreshTailEntranceCarrierInvariant ring C s Y := by
  have hrun :=
    topFreshTailEntranceCarrierRun ring C s hn hbad hl Y.2
  change TopFreshTailEntranceCarrierInvariant ring C s
    (topFixedTraceRun ring C Y.2) at hrun
  rw [← hreached] at hrun
  exact hrun

end L3

#print axioms L3.topFreshTailEntranceCarrierInitial
#print axioms L3.topFreshTailEntranceCarrierAwayHome
#print axioms L3.topFreshTailEntranceCarrierAwayStep
#print axioms L3.topFreshTailEntranceCarrierSourceDataStay
#print axioms L3.topFreshTailEntranceCarrierBorderUnreadBirth
#print axioms L3.topFreshTailEntranceCarrierAwayWord
#print axioms L3.topFreshTailEntranceCarrierResponderDataStay
#print axioms L3.topFreshTailEntranceCarrierPositiveUnreadNotZero
#print axioms L3.topFreshTailEntranceCarrierBorderSampleOfAtom
#print axioms L3.topFreshTailEntranceCarrierIncomingDataMove
#print axioms L3.topFreshTailEntranceCarrierSourceStep
#print axioms L3.topFreshTailEntranceCarrierResponderStep
#print axioms L3.topFreshTailEntranceCarrierAcceptedTerminalDeparture
#print axioms L3.topFreshTailEntranceCarrierStep
#print axioms L3.topFreshTailEntranceCarrierRun
#print axioms L3.topFreshTailEntranceCarrierReached
