import Leader.L3.Top.FreshTailWaveRun

/-!
Q7c P.3 J5: history-selected cohort specification.

The OLD machine and genealogy are unchanged. Historical issue events
and packet-follow chains use actual scheduler prefixes. At the first
anchor the historical terminal parent and stationary homes are known;
the first-cohort issue history for every home is NOT yet available
from the installed barrier theorem.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- One real edge keeps the selected carrier, moves an unchanged
D into an OLD empty successor, or samples and rekeys an U at
the zero home. Consumer: TopFreshTailCohortPacketFollow. -/
noncomputable def TopFreshTailCohortPacketStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (y : Fin (topClockSpan n))
    (afterCarrier : TopFreshTailCarrier (topClockSpan n)) :
    Prop :=
  (topFreshTailGenealogy ring C s
    (topFixedTraceRun ring C word)).slots x = some carrier ∧
  (topFreshTailGenealogy ring C s
    (topFixedTraceRun ring C (word ++ [e]))).slots y =
      some afterCarrier ∧
  ((x = y ∧ afterCarrier = carrier) ∨
   (x.val + 1 < topClockSpan n ∧
    y.val = x.val + 1 ∧
    e = certSite s x.val ∧
    afterCarrier = carrier ∧
    ∃ (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      ((topFixedTraceRun ring C word).1.1 e).qOut =
        .D value tail ∧
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qOut = .E) ∨
   (x.val = 0 ∧ y = x ∧
    e = certSite s 0 ∧
    ((topFixedTraceRun ring C word).1.1 e).qOut = .U ∧
    (∃ value : Fin (compileAdvice (ceilLogTwo n)).topA,
      ((topFixedTraceRun ring C (word ++ [e])).1.1 e).qOut =
        .D value true) ∧
    afterCarrier =
      { origin := .freshBorder
          ((topFixedTraceRun ring C word).1.2.clock + 1)
        born := (topFixedTraceRun ring C word).1.2.clock + 1 }))

/-- The same logical packet is followed along the real word;
the special zero-site sample changes its full carrier but not
its issued cohort. Terminal consumption ends this chain.
Consumer: TopFreshTailCohortIssueHistory. -/
inductive TopFreshTailCohortPacketFollow
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (initialWord : List (Fin n))
    (initialSite : Fin (topClockSpan n))
    (initialCarrier : TopFreshTailCarrier (topClockSpan n)) :
    List (Fin n) →
    Fin (topClockSpan n) →
    TopFreshTailCarrier (topClockSpan n) → Prop where
  | start :
      TopFreshTailCohortPacketFollow
        ring C s initialWord initialSite initialCarrier
        initialWord initialSite initialCarrier
  | snoc
      {word : List (Fin n)}
      {x : Fin (topClockSpan n)}
      {carrier : TopFreshTailCarrier (topClockSpan n)}
      (hfollow :
        TopFreshTailCohortPacketFollow
          ring C s initialWord initialSite initialCarrier
          word x carrier)
      (e : Fin n)
      (y : Fin (topClockSpan n))
      (afterCarrier : TopFreshTailCarrier (topClockSpan n))
      (hstep :
        TopFreshTailCohortPacketStep
          ring C s word e x carrier y afterCarrier) :
      TopFreshTailCohortPacketFollow
        ring C s initialWord initialSite initialCarrier
        (word ++ [e]) y afterCarrier

/-- A literal selected D(true)-to-U source event has an OLD
full parent and the exact rearm child at the new clock.
Consumer: historical first-cohort issue induction. -/
noncomputable def TopFreshTailCohortRearmEvent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (before : List (Fin n))
    (home : Fin (topClockSpan n))
    (parent child : TopFreshTailCarrier (topClockSpan n)) :
    Prop :=
  ∃ value : Fin (compileAdvice (ceilLogTwo n)).topA,
    ((topFixedTraceRun ring C before).1.1
      (certSite s home.val)).qOut = .D value true ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceRun ring C before)).slots home =
      some parent ∧
    ((topFixedTraceRun ring C
      (before ++ [certSite s home.val])).1.1
      (certSite s home.val)).qOut = .U ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceRun ring C
        (before ++ [certSite s home.val]))).slots home =
        some child ∧
    child = topFreshTailGenealogyRearm home
      ((topFixedTraceRun ring C before).1.2.clock + 1)
      parent

/-- Issuance is a selected source event plus a literal packet
continuation. Matching freshBorder origins without a service
word is insufficient. Consumer: both cohort maps. -/
noncomputable def TopFreshTailCohortIssueHistory
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (home x : Fin (topClockSpan n))
    (parent carrier : TopFreshTailCarrier (topClockSpan n)) :
    Prop :=
  ∃ (before after : List (Fin n))
    (issued : TopFreshTailCarrier (topClockSpan n)),
    word = before ++ certSite s home.val :: after ∧
    TopFreshTailCohortRearmEvent
      ring C s before home parent issued ∧
    TopFreshTailCohortPacketFollow
      ring C s
      (before ++ [certSite s home.val]) home issued
      word x carrier

/-- q is computed from the actual chronological export count;
role=false is current q, role=true is next q+1.
The source event and packet-follow history remain explicit.
Consumer: selected current/next issued-family fields. -/
noncomputable def TopFreshTailIssuedInCohort
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (isNext : Bool) (generation : Nat)
    (home x : Fin (topClockSpan n))
    (parent carrier : TopFreshTailCarrier (topClockSpan n)) :
    Prop :=
  generation =
    (topClockConcreteExportsAfter s Z anchor.time).length /
      topClockSpan n +
      (if isNext then 1 else 0) ∧
  TopFreshTailCohortIssueHistory
    ring C s Z.2 home x parent carrier

/-- The previous completed true-tail receipt determines a
current cohort's full OLD parent. Generation zero uses the
fixed anchor; positive generations use E[q*r-1]. In all
cases the service and timestamp belong to an actual prefix.
Consumer: cohort base and terminal renewal. -/
noncomputable def TopFreshTailCohortHistoricalParent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (generation : Nat)
    (parent : TopFreshTailCarrier (topClockSpan n)) :
    Prop :=
  ∃ (before after : List (Fin n))
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n),
    Z.2 = before ++
      certSite s (topClockSpan n - 1) :: after ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceRun ring C before)).slots
      (⟨topClockSpan n - 1,
        show topClockSpan n - 1 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) =
      some parent ∧
    topFreshTailGenealogyPortExport ring C s
      (topFixedTraceRun ring C before)
      (certSite s (topClockSpan n - 1)) = some exported ∧
    exported.time = before.length + 1 ∧
    exported.tail = true ∧
    (if generation = 0 then exported = anchor else
      ∃ i : Fin
          (topClockConcreteExportsAfter s Z anchor.time).length,
        i.val = generation * topClockSpan n - 1 ∧
        exported = topClockConcreteExportAt s Z anchor.time i)

/-- Full proof-only selected current and next maps. No field of
the OLD physical machine, audit or genealogy is modified.

The current family q has actual homes 0..b, ordered by its
selected witnesses. The pending next family q+1 occupies the
stationary sites strictly behind the pinned current root.
Every occupied source belongs to exactly one selected family.
Chronological recorded samples and the actual terminal head
remain available to the permanent-cut consumer. -/
structure TopFreshTailPostAnchorCohortWave
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n) : Type where
  reached : topClockReached ring C Z
  queue : TopFreshTailCausalQueue ring C s Z
  provenance :
    TopFreshTailAuditSourceDataProvenance ring C s Z
  anchorRecorded : topClockConcreteTailAnchor s Z anchor
  allFresh :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      ∃ stamp : Nat, a.origin = .freshBorder stamp
  currentMap :
    Fin (topClockSpan n) →
      Option
        (Fin (topClockSpan n) ×
          TopFreshTailCarrier (topClockSpan n))
  nextMap :
    Fin (topClockSpan n) →
      Option (TopFreshTailCarrier (topClockSpan n))
  currentParent : TopFreshTailCarrier (topClockSpan n)
  currentParentReceipt :
    TopFreshTailCohortHistoricalParent
      ring C s hn Z anchor
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n) currentParent
  root : TopFreshTailCarrier (topClockSpan n)
  rootPosition : Fin (topClockSpan n)
  rootSelected :
    currentMap
      (⟨0, show 0 < topClockSpan n by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ : Fin (topClockSpan n)) =
      some (rootPosition, root)
  currentIssued :
    ∀ h : Fin (topClockSpan n),
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n) →
      ∃ (x : Fin (topClockSpan n))
        (a : TopFreshTailCarrier (topClockSpan n)),
        currentMap h = some (x, a) ∧
        TopFreshTailPostAnchorActiveHome
          ring C s Z h x a ∧
        TopFreshTailIssuedInCohort
          ring C s Z anchor false
          ((topClockConcreteExportsAfter
            s Z anchor.time).length / topClockSpan n)
          h x currentParent a
  currentAbsent :
    ∀ h : Fin (topClockSpan n),
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n) < h.val →
      currentMap h = none
  currentOrder :
    ∀ h i : Fin (topClockSpan n),
      h.val < i.val →
      i.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n) →
      ∀ (x y : Fin (topClockSpan n))
        (a b : TopFreshTailCarrier (topClockSpan n)),
        currentMap h = some (x, a) →
        currentMap i = some (y, b) →
        x.val < y.val
  rootKind :
    (rootPosition.val = 0 ∧
      (Z.1.1 (certSite s 0)).qOut = .U) ∨
    ∃ sample : DigitSample
        (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample Z.1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site = certSite s 0 ∧
      sample.tail = true ∧
      (Z.1.1 (certSite s rootPosition.val)).qOut =
        .D sample.value true ∧
      (Z.1.2.current
        (certSite s rootPosition.val)).comparison.out.atom =
          some (.sampled sample.id)
  nextIssued :
    ∀ j : Fin (topClockSpan n),
      j.val < rootPosition.val →
      ∃ a : TopFreshTailCarrier (topClockSpan n),
        nextMap j = some a ∧
        (topFreshTailGenealogy ring C s Z).slots j =
          some a ∧
        TopFreshTailFirstBorderHomeSlot
          ring C s Z root j ∧
        TopFreshTailIssuedInCohort
          ring C s Z anchor true
          ((topClockConcreteExportsAfter
            s Z anchor.time).length / topClockSpan n + 1)
          j j root a
  nextAbsent :
    ∀ j : Fin (topClockSpan n),
      rootPosition.val ≤ j.val → nextMap j = none
  sourceCoverage :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      (∃ h : Fin (topClockSpan n),
        currentMap h = some (j, a) ∧ nextMap j = none) ∨
      (nextMap j = some a ∧
        ∀ (h : Fin (topClockSpan n))
          (b : TopFreshTailCarrier (topClockSpan n)),
          currentMap h ≠ some (j, b))
  selectedHead :
    ∀ (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      (Z.1.1
        (certSite s (topClockSpan n - 1))).qOut =
          .D value tail →
      ∃ a : TopFreshTailCarrier (topClockSpan n),
        currentMap
          (⟨topClockSpan n - 1 -
              ((topClockConcreteExportsAfter s Z
                anchor.time).length % topClockSpan n),
            show topClockSpan n - 1 -
              ((topClockConcreteExportsAfter s Z
                anchor.time).length % topClockSpan n) <
                topClockSpan n by
                  have hr := cert_rho_ge_three n hn
                  change 3 ≤ topClockSpan n at hr
                  omega⟩ : Fin (topClockSpan n)) =
          some
            ((⟨topClockSpan n - 1,
              show topClockSpan n - 1 < topClockSpan n by
                have hr := cert_rho_ge_three n hn
                change 3 ≤ topClockSpan n at hr
                omega⟩ : Fin (topClockSpan n)), a) ∧
        (topFreshTailGenealogy ring C s Z).slots
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) =
          some a
  exportRecords :
    ∀ i : Fin (topClockConcreteExportsAfter
        s Z anchor.time).length,
      ∃ sample :
        DigitSample (compileAdvice (ceilLogTwo n)) n,
        DigitRecordedSample Z.1.2 sample ∧
        sample.id.lane = .comparison ∧
        sample.id.site =
          certSite s
            (topClockSpan n - 1 -
              (i.val % topClockSpan n)) ∧
        sample.value =
          (C (certSite s
            (topClockSpan n - 1 -
              (i.val % topClockSpan n)))).d ∧
        sample.tail =
          (if i.val % topClockSpan n = topClockSpan n - 1
            then true else false) ∧
        (topClockConcreteExportAt
          s Z anchor.time i).operand =
          some (.sampled sample.id) ∧
        (topClockConcreteExportAt
          s Z anchor.time i).value = sample.value ∧
        (topClockConcreteExportAt
          s Z anchor.time i).tail = sample.tail


/-- At a reached OLD D(true)-to-U service, the exact rearm
child occupies the OLD source and is connected to its full
parent by an actual historical selected service. This is a
local issue producer, not an all-home history collection.
Consumer: first-anchor issue-history induction and W.next. -/
theorem topFreshTailCohortRealRearmIssueStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hsource : (Z.1.1 e).qOut = .D v true)
    (hslot :
      (topFreshTailGenealogy ring C s Z).slots j =
        some parent)
    (hnewU :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U) :
    TopFreshTailCohortRearmEvent ring C s Z.2 j parent
      (topFreshTailGenealogyRearm j
        (Z.1.2.clock + 1) parent) ∧
    TopFreshTailCausalParent ring C s (Z.2 ++ [e])
      parent
      (topFreshTailGenealogyRearm j
        (Z.1.2.clock + 1) parent) := by
  have hbefore :
      topFixedTraceRun ring C Z.2 = Z :=
    hqueue.trace.1.symm
  have hafter :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hbefore]
  have hafterSite :
      topFixedTraceRun ring C
        (Z.2 ++ [certSite s j.val]) =
          topFixedTraceNext ring C Z e := by
    have hw :
        Z.2 ++ [certSite s j.val] = Z.2 ++ [e] := by
      rw [hsite]
    rw [hw]
    exact hafter
  have hghostSource :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (certSite s j.val)).qOut = .D v true := by
    rw [hqueue.trace.2, ← hsite]
    exact hsource
  have hghostNext :
      ((topFixedTraceNext ring C
        (topFreshTailGenealogy ring C s Z).trace e).1.1
          (certSite s j.val)).qOut = .U := by
    rw [hqueue.trace.2, ← hsite]
    exact hnewU
  have hslotNext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
      some (topFreshTailGenealogyRearm j
        (Z.1.2.clock + 1) parent) := by
    rw [topFreshTailCausalReplayNext]
    change topFreshTailGenealogyNextSlot
      ring C s (topFreshTailGenealogy ring C s Z) e j =
      some (topFreshTailGenealogyRearm j
        (Z.1.2.clock + 1) parent)
    unfold topFreshTailGenealogyNextSlot
    rw [hghostNext, hghostSource, hslot]
    rw [hqueue.trace.2]
    rfl
  have hservice :
      TopFreshTailCausalServiceParent
        ring C s Z.2 e parent
        (topFreshTailGenealogyRearm j
          (Z.1.2.clock + 1) parent) := by
    apply Or.inl
    refine ⟨j, v, hsite, ?_, hslot, ?_, ?_⟩
    · change
        ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
          .D v true
      rw [hqueue.trace.2]
      exact hsource
    · change
        ((topFixedTraceNext ring C
          (topFreshTailGenealogy ring C s Z).trace e).1.1
          e).qOut = .U
      rw [hqueue.trace.2]
      exact hnewU
    · first
        | exact (congrArg (fun t : TopFixedTraceState n => topFreshTailGenealogyRearm j (t.1.2.clock + 1) parent) hqueue.trace.2).symm
        | simp [topFreshTailGenealogy, hqueue.trace.2]
  constructor
  · unfold TopFreshTailCohortRearmEvent
    refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbefore, ← hsite]
      exact hsource
    · rw [hbefore]
      exact hslot
    · rw [hafterSite, ← hsite]
      exact hnewU
    · rw [hafterSite]
      exact hslotNext
    · rw [hbefore]
  · exact (topFreshTailCausalParentAppend
      ring C s Z.2 e _ _).2 (Or.inr hservice)

/-- A genuine tracked-root port exit supplies the full OLD
terminal parent, an actual historical accepted receipt,
and a correctly sampled fresh stationary carrier at every
home. Every positive home is an exact rearm carrier of this
parent; identifying the historical issue edge for *each*
home is a separate required induction.
Consumer: topFreshTailPostAnchorCohortWaveBase. -/
theorem topFreshTailCohortFirstAnchorEnvelope
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailFirstBorderHomeBarrier
        ring C s (topFixedTraceRun ring C word)
        root k sample)
    (hterminal : k.val + 1 = topClockSpan n)
    (e : Fin n) (hsite : e = certSite s k.val)
    (hyi :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qIn = .E)
    (hyc :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qCarry = .OFF) :
    ∃ anchor : DigitExport
        (compileAdvice (ceilLogTwo n)) n,
      topClockConcreteTailAnchor s
        (topFixedTraceRun ring C (word ++ [e])) anchor ∧
      anchor.time =
        (topFixedTraceRun ring C (word ++ [e])).1.2.clock ∧
      TopFreshTailCohortHistoricalParent
        ring C s hn
        (topFixedTraceRun ring C (word ++ [e]))
        anchor 0 root ∧
      (∀ j : Fin (topClockSpan n),
        ∃ a : TopFreshTailCarrier (topClockSpan n),
          TopFreshTailPostAnchorActiveHome ring C s
            (topFixedTraceRun ring C (word ++ [e]))
            j j a) ∧
      (∀ j : Fin (topClockSpan n), 0 < j.val →
        ∃ (a : TopFreshTailCarrier (topClockSpan n))
          (birth : Nat),
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
            some a ∧
          a = topFreshTailGenealogyRearm j birth root) := by
  have hexit :=
    topFreshTailFirstRootStaircaseExit
      ring C s hn hbad hl word root k sample
      hbarrier hterminal e hsite hyi hyc
  have hreach :=
    topFreshTailAuditRunReached ring C (word ++ [e])
  obtain ⟨anchor, hanchor, htime⟩ :=
    topFreshTailAuditGenuineTailAnchor
      ring C s hn
      (topFixedTraceRun ring C (word ++ [e]))
      hreach hexit.1
  have hsnoc :=
    topFreshTailFifoRunSnoc ring C word e
  have hrecordStep :
      DigitRecordedExport
        (topFixedTraceNext ring C
          (topFixedTraceRun ring C word) e).1.2
        anchor := by
    rw [← hsnoc]
    exact hanchor.1
  have htimeStep :
      anchor.time =
        (topFixedTraceRun ring C word).1.2.clock + 1 := by
    rw [hsnoc] at htime
    change anchor.time =
      (topFixedTraceRun ring C word).1.2.clock + 1 at htime
    exact htime
  have hevent :=
    topFreshTailAuditFreshPortConverse
      ring C s (topFixedTraceRun ring C word) e
      (topFreshTailAuditRunReached ring C word)
      anchor hrecordStep htimeStep
      hanchor.2.1 hanchor.2.2.1 hanchor.2.2.2.1
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hk : k.val = topClockSpan n - 1 := by
    omega
  have hport :
      e = certSite s (topClockSpan n - 1) := by
    rw [hk] at hsite
    exact hsite
  have hindex :
      k =
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            omega⟩ : Fin (topClockSpan n)) :=
    Fin.ext hk
  have hlast :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C word)).slots
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            omega⟩ : Fin (topClockSpan n)) =
        some root := by
    rw [← hindex]
    exact hbarrier.spatial.rootSlot
  have hstamp : anchor.time = word.length + 1 := by
    rw [htimeStep, topFreshTailAuditRunClock ring C word]
  have htail : anchor.tail = true :=
    hanchor.2.2.2.2.1
  have hparent :
      TopFreshTailCohortHistoricalParent
        ring C s hn
        (topFixedTraceRun ring C (word ++ [e]))
        anchor 0 root := by
    unfold TopFreshTailCohortHistoricalParent
    refine ⟨word, [], anchor, ?_, hlast, ?_,
      hstamp, htail, ?_⟩
    · rw [topFreshTailFifoRunWord, hport]
    · rw [← hport]
      exact hevent
    · simp
  refine ⟨anchor, hanchor, htime, hparent, ?_, ?_⟩
  · intro j
    exact topFreshTailPostAnchorStaircaseActiveHome
      ring C s
      (topFixedTraceRun ring C (word ++ [e]))
      root j (hexit.2.1 j)
  · intro j hj
    obtain ⟨a, hslot, _, hrear, _⟩ := hexit.2.1 j
    obtain ⟨birth, hb⟩ := hrear hj
    exact ⟨a, birth, hslot, hb⟩

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Every actual qualified comparison export in the newly
selected audit frame has precisely the selected service clock.
Consumer: first-anchor empty chronological suffix. -/
theorem topFreshTailCohortNewEntryTime
    {n : Nat} (ring : DirectedRing n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (anchorTime : Nat) (e : Fin n)
    (exported : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (hmem : exported ∈
      topFreshTailPostAnchorNewEntries
        ring s Z anchorTime e) :
    exported.time = Z.1.2.clock + 1 := by
  cases hlocal :
      (digitReceiptLane .comparison
        (topFreshTailPostAnchorCurrentFrame
          ring Z e).receipt).exported with
  | none =>
      simp [topFreshTailPostAnchorNewEntries, hlocal]
        at hmem
  | some actual =>
      by_cases hqual :
          anchorTime < actual.time ∧
          actual.source = certSite s (topClockSpan n - 1) ∧
          actual.destination = certSite s (topClockSpan n)
      · have heq : exported = actual := by
          simpa [topFreshTailPostAnchorNewEntries,
            hlocal, hqual] using hmem
        subst exported
        have hfields :=
          topFreshTailAuditLaneExportFields
            .comparison (Z.1.2.clock + 1)
            e (ring.rightNeighbor e)
            (digitLaneView .comparison
              (piD Z.1.1 e)
              (piD Z.1.1 e).word.beta)
            (digitLaneView .comparison
              (piD Z.1.1 (ring.rightNeighbor e))
              (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
            (Z.1.2.current e).comparison
            (Z.1.2.current (ring.rightNeighbor e)).comparison
            actual (by
              change
                (digitLaneReplay .comparison
                  (Z.1.2.clock + 1) e
                  (ring.rightNeighbor e)
                  (digitLaneView .comparison
                    (piD Z.1.1 e)
                    (piD Z.1.1 e).word.beta)
                  (digitLaneView .comparison
                    (piD Z.1.1 (ring.rightNeighbor e))
                    (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
                  (Z.1.2.current e).comparison
                  (Z.1.2.current
                    (ring.rightNeighbor e)).comparison).exported =
                  some actual at hlocal
              exact hlocal)
        exact hfields.1
      · simp [topFreshTailPostAnchorNewEntries,
          hlocal, hqual] at hmem

/-- The physical/audit service cannot create an export with
a time later than its own NEW clock when every OLD export
was already no later than the OLD clock. This is independent
of the packet-wave argument. Consumer: chronological J5 base. -/
theorem topFreshTailCohortExportClockBoundStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (anchorTime : Nat)
    (hbound :
      ∀ exported : DigitExport
          (compileAdvice (ceilLogTwo n)) n,
        exported ∈
          topClockConcreteExportsAfter s Z anchorTime →
        exported.time ≤ Z.1.2.clock) :
    ∀ exported : DigitExport
        (compileAdvice (ceilLogTwo n)) n,
      exported ∈
        topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchorTime →
      exported.time ≤
        (topFixedTraceNext ring C Z e).1.2.clock := by
  intro exported hmem
  rw [topFreshTailPostAnchorExportsAfterStep] at hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · have hb := hbound exported hold
    change exported.time ≤ Z.1.2.clock + 1
    omega
  · have ht :=
      topFreshTailCohortNewEntryTime
        ring s Z anchorTime e exported hnew
    change exported.time ≤ Z.1.2.clock + 1
    omega

/-- Chronological audit-export times are bounded by the
selected OLD clock through any finite continuation.
Consumer: first-anchor filter emptiness. -/
theorem topFreshTailCohortExportClockBoundFold
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    ∀ (Z : TopFixedTraceState n) (anchorTime : Nat),
      (∀ exported : DigitExport
          (compileAdvice (ceilLogTwo n)) n,
        exported ∈
          topClockConcreteExportsAfter s Z anchorTime →
        exported.time ≤ Z.1.2.clock) →
      ∀ exported : DigitExport
          (compileAdvice (ceilLogTwo n)) n,
        exported ∈
          topClockConcreteExportsAfter s
            (word.foldl (topFixedTraceNext ring C) Z)
            anchorTime →
        exported.time ≤
          (word.foldl (topFixedTraceNext ring C) Z).1.2.clock := by
  induction word with
  | nil =>
      intro Z anchorTime hbound exported hmem
      exact hbound exported hmem
  | cons edge rest ih =>
      intro Z anchorTime hbound
      change
        ∀ exported : DigitExport
            (compileAdvice (ceilLogTwo n)) n,
          exported ∈ topClockConcreteExportsAfter s
            (rest.foldl (topFixedTraceNext ring C)
              (topFixedTraceNext ring C Z edge))
            anchorTime →
          exported.time ≤
            (rest.foldl (topFixedTraceNext ring C)
              (topFixedTraceNext ring C Z edge)).1.2.clock
      exact ih (topFixedTraceNext ring C Z edge)
        anchorTime
        (topFreshTailCohortExportClockBoundStep
          ring C s Z edge anchorTime hbound)

/-- Every filtered comparison export of an actual OLD word
occurred at or before the last selected service clock.
Consumer: concrete first-anchor chronology. -/
theorem topFreshTailCohortExportClockBoundRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (anchorTime : Nat) :
    ∀ exported : DigitExport
        (compileAdvice (ceilLogTwo n)) n,
      exported ∈ topClockConcreteExportsAfter s
        (topFixedTraceRun ring C word) anchorTime →
      exported.time ≤
        (topFixedTraceRun ring C word).1.2.clock := by
  have hinitial :
      ∀ exported : DigitExport
          (compileAdvice (ceilLogTwo n)) n,
        exported ∈
          topClockConcreteExportsAfter s
            ((C, digitAuditInitial (piD C)), []) anchorTime →
        exported.time ≤
          (digitAuditInitial (piD C)).clock := by
    intro exported hmem
    unfold topClockConcreteExportsAfter at hmem
    simp [digitAuditInitial] at hmem
  exact topFreshTailCohortExportClockBoundFold
    ring C s word
    ((C, digitAuditInitial (piD C)), [])
    anchorTime hinitial

/-- At a reached fixed-public cut, filtering for a comparison
port export strictly after its own clock gives no entries.
In particular, the genuine first-anchor export does not count
as a post-anchor serial. Consumer: cohort W.base exportRecords. -/
theorem topFreshTailCohortFirstAnchorExportsEmpty
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (hreached : topClockReached ring C Z)
    (htime : anchor.time = Z.1.2.clock) :
    topClockConcreteExportsAfter s Z anchor.time = [] := by
  have hbound :=
    topFreshTailCohortExportClockBoundRun
      ring C s Z.2 anchor.time
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    hreached.symm
  rw [hrun] at hbound
  cases hlist :
      topClockConcreteExportsAfter s Z anchor.time with
  | nil =>
      rfl
  | cons exported rest =>
      have hmem :
          exported ∈
            topClockConcreteExportsAfter s Z anchor.time := by
        rw [hlist]
        simp
      have hle := hbound exported hmem
      have htest := hmem
      unfold topClockConcreteExportsAfter at htest
      have hfilter := (List.mem_filter.mp htest).2
      have hqual :
          anchor.time < exported.time ∧
          exported.source = certSite s (topClockSpan n - 1) ∧
          exported.destination = certSite s (topClockSpan n) := by
        by_cases hp :
            anchor.time < exported.time ∧
            exported.source = certSite s (topClockSpan n - 1) ∧
            exported.destination = certSite s (topClockSpan n)
        · exact hp
        · simp [hp] at hfilter
      rw [htime] at hqual
      omega


/-- A packet already issued at its real home retains its
selected issue event and continuation when a new OLD edge
leaves its full carrier in the same genealogy slot.
Consumer: all barrier frame rows and the behind-root D block. -/
theorem topFreshTailCohortIssueHistoryAppendStay
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (home x : Fin (topClockSpan n))
    (parent carrier : TopFreshTailCarrier (topClockSpan n))
    (hissue :
      TopFreshTailCohortIssueHistory
        ring C s word home x parent carrier)
    (e : Fin n)
    (hslot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C word)).slots x =
        some carrier)
    (hnext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (word ++ [e]))).slots x =
        some carrier) :
    TopFreshTailCohortIssueHistory
      ring C s (word ++ [e]) home x parent carrier := by
  unfold TopFreshTailCohortIssueHistory at hissue ⊢
  obtain ⟨before, after, issued, hword, hevent,
    hfollow⟩ := hissue
  refine ⟨before, after ++ [e], issued, ?_,
    hevent, ?_⟩
  · rw [hword]
    simp only [List.append_assoc, List.cons_append]
  · exact TopFreshTailCohortPacketFollow.snoc
      hfollow e x carrier
      ⟨hslot, hnext, Or.inl ⟨rfl, rfl⟩⟩

/-- Strengthening of the actual first-root home barrier:
every stationary home strictly behind the root carries a
selected event from this full root followed through its
actual scheduler prefix. The carrier is NOT identified by
its bare origin or merely its rearm birth time.
Consumer: topFreshTailCohortFirstAnchorAllHomeIssues. -/
structure TopFreshTailCohortIssuedBarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n) : Prop where
  barrier :
    TopFreshTailFirstBorderHomeBarrier
      ring C s (topFixedTraceRun ring C word)
      root k sample
  issueBehind :
    ∀ j : Fin (topClockSpan n), j.val < k.val →
      ∃ carrier : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C word)).slots j =
          some carrier ∧
        TopFreshTailCohortIssueHistory
          ring C s word j j root carrier

/-- At the actual sampled root birth with k=0, no home
precedes the root; the history field is vacuous. This
wraps the enhanced home-barrier initial producer.
Consumer: the history-strengthened barrier induction base. -/
theorem topFreshTailCohortIssuedBarrierAtZero
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hk : k.val = 0)
    (hbarrier :
      TopFreshTailFirstBorderHomeBarrier
        ring C s (topFixedTraceRun ring C word)
        root k sample) :
    TopFreshTailCohortIssuedBarrier
      ring C s word root k sample := by
  refine ⟨hbarrier, ?_⟩
  intro j hj
  omega

/-- For a selected edge away from every recorded issued
home, its history extends by the explicit unchanged-slot
packet-follow constructor. This is the common frame for
OLD off-pair, ahead-root, blocked-root and accepted port.
Consumer: stronger barrier row wrappers. -/
theorem topFreshTailCohortIssuedBarrierFrameStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (e : Fin n)
    (hbarrierNext :
      TopFreshTailFirstBorderHomeBarrier
        ring C s
        (topFixedTraceNext ring C
          (topFixedTraceRun ring C word) e)
        root k sample)
    (haway :
      ∀ j : Fin (topClockSpan n), j.val < k.val →
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  refine ⟨?_, ?_⟩
  · rw [topFreshTailFifoRunSnoc]
    exact hbarrierNext
  · intro j hj
    obtain ⟨carrier, hslot, hissue⟩ :=
      hbarrier.issueBehind j hj
    obtain ⟨hsource, htarget⟩ := haway j hj
    have hframe :=
      (topFreshTailCausalOffPairSlotAgreement
        ring C s (topFixedTraceRun ring C word) e
        hbarrier.barrier.spatial.queue j
        hsource htarget).2
    have hnext :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (word ++ [e]))).slots j =
          some carrier := by
      rw [topFreshTailFifoRunSnoc, hframe]
      exact hslot
    exact ⟨carrier, hnext,
      topFreshTailCohortIssueHistoryAppendStay
        ring C s word j j root carrier hissue
        e hslot hnext⟩

/-- A scheduler edge touching no source sites is harmless to
every issued-home history and to the enhanced OLD barrier.
Consumer: first-root selected history word fold (away row). -/
theorem topFreshTailCohortIssuedBarrierAwayStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (e : Fin n)
    (hsource :
      ∀ j : Fin (topClockSpan n), certSite s j.val ≠ e)
    (htarget :
      ∀ j : Fin (topClockSpan n),
        certSite s j.val ≠ ring.rightNeighbor e) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  apply topFreshTailCohortIssuedBarrierFrameStep
    ring C s word root k sample hbarrier e
    (topFreshTailFirstBorderHomeBarrierAwayStep
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier e
      hsource htarget)
  intro j _
  exact ⟨hsource j, htarget j⟩

/-- A selected source strictly ahead of the moving root
cannot touch any already issued home behind it.
Consumer: first-root selected history word fold (ahead row). -/
theorem topFreshTailCohortIssuedBarrierAheadStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (j : Fin (topClockSpan n))
    (hahead : k.val < j.val)
    (e : Fin n) (hsite : e = certSite s j.val) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  apply topFreshTailCohortIssuedBarrierFrameStep
    ring C s word root k sample hbarrier e
    (topFreshTailFirstBorderHomeBarrierAheadStep
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier j hahead e hsite)
  intro i hi
  exact topFreshTailFirstBorderEarlierSiteOffSelectedPair
    ring s hn i j (by omega) e hsite


/-- A literal selected D(true)-to-U departure starts the
issued child's real packet-follow history at its own site.
This is independent of any birth-time heuristic.
Consumer: barrier root-hop and accepted-port new-home rows. -/
theorem topFreshTailCohortIssueHistoryAtRearm
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hsource : (Z.1.1 e).qOut = .D v true)
    (hslot :
      (topFreshTailGenealogy ring C s Z).slots j =
        some parent)
    (hnewU :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U) :
    TopFreshTailCohortIssueHistory
      ring C s (Z.2 ++ [e]) j j parent
      (topFreshTailGenealogyRearm j
        (Z.1.2.clock + 1) parent) := by
  have hreal :=
    (topFreshTailCohortRealRearmIssueStep
      ring C s Z hqueue e j v parent
      hsite hsource hslot hnewU).1
  unfold TopFreshTailCohortIssueHistory
  refine ⟨Z.2, [], topFreshTailGenealogyRearm j
    (Z.1.2.clock + 1) parent, ?_, hreal, ?_⟩
  · rw [hsite]
    try rfl
  · rw [hsite]
    exact TopFreshTailCohortPacketFollow.start

/-- The real root-hop row preserves the extended
issue history: previous stationary homes are away, and the
new stationary U at departed root offset has a literal
selected rearm issue with the full tracked root as parent.
Consumer: strengthened first-root barrier word induction. -/
theorem topFreshTailCohortIssuedBarrierRootHop
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (e : Fin n)
    (hsite : e = certSite s k.val)
    (hnext : k.val + 1 < topClockSpan n)
    (hempty :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root
      (⟨k.val + 1, hnext⟩ : Fin (topClockSpan n))
      sample := by
  have hgreen :=
    topFreshTailFirstBorderHomeBarrierRootHop
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      e hsite hnext hempty
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      hbarrier.barrier.spatial.queue.trace.1 k
  have hxl :
      ((topFixedTraceRun ring C word).1.1 e).l =
        false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hyb :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).beta = false := by
    have hm := hgeom.2.2.2
    rw [if_neg (show k.val + 1 ≠ topClockSpan n by omega)]
      at hm
    rw [hsite]
    exact hm
  have hsource :
      ((topFixedTraceRun ring C word).1.1 e).qOut =
        .D sample.value true := by
    rw [hsite]
    exact hbarrier.barrier.spatial.rootData
  have hnewU :
      ((topFixedTraceNext ring C
        (topFixedTraceRun ring C word) e).1.1 e).qOut =
          .U := by
    have hmove :=
      (topFreshTailFifoDataMove ring
        (by omega : 2 ≤ n) C
        (topFixedTraceRun ring C word)
        e sample.value true
        hxl hyl hsource hempty hyb).1
    simpa only [ite_true] using hmove
  have hnewHistory :
      TopFreshTailCohortIssueHistory
        ring C s (word ++ [e]) k k root
        (topFreshTailGenealogyRearm k
          ((topFixedTraceRun ring C word).1.2.clock + 1)
          root) := by
    have hh :=
      topFreshTailCohortIssueHistoryAtRearm
        ring C s (topFixedTraceRun ring C word)
        hbarrier.barrier.spatial.queue
        e k sample.value root hsite hsource
        hbarrier.barrier.spatial.rootSlot hnewU
    rw [topFreshTailFifoRunWord] at hh
    exact hh
  have hreal :=
    (topFreshTailCohortRealRearmIssueStep
      ring C s (topFixedTraceRun ring C word)
      hbarrier.barrier.spatial.queue
      e k sample.value root hsite hsource
      hbarrier.barrier.spatial.rootSlot hnewU).1
  obtain ⟨_, _, _, _, hchildSlot, _⟩ := hreal
  have hword :
      (topFixedTraceRun ring C word).2 ++
        [certSite s k.val] = word ++ [e] := by
    rw [topFreshTailFifoRunWord, ← hsite]
  have hnewSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (word ++ [e]))).slots k =
      some (topFreshTailGenealogyRearm k
        ((topFixedTraceRun ring C word).1.2.clock + 1)
        root) := by
    rw [hword] at hchildSlot
    exact hchildSlot
  refine ⟨?_, ?_⟩
  · rw [topFreshTailFifoRunSnoc]
    exact hgreen
  · intro j hj
    by_cases hearlier : j.val < k.val
    · obtain ⟨carrier, hslot, hissue⟩ :=
        hbarrier.issueBehind j hearlier
      obtain ⟨hsourceAway, htargetAway⟩ :=
        topFreshTailFirstBorderEarlierSiteOffSelectedPair
          ring s hn j k hearlier e hsite
      have hframe :=
        (topFreshTailCausalOffPairSlotAgreement
          ring C s (topFixedTraceRun ring C word) e
          hbarrier.barrier.spatial.queue j
          hsourceAway htargetAway).2
      have hnextSlot :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots
              j = some carrier := by
        rw [topFreshTailFifoRunSnoc, hframe]
        exact hslot
      exact ⟨carrier, hnextSlot,
        topFreshTailCohortIssueHistoryAppendStay
          ring C s word j j root carrier hissue
          e hslot hnextSlot⟩
    · have heq : j = k := Fin.ext (by
        have hj2 : j.val < k.val + 1 := by first | exact hj | (simp at hj; omega)
        have hjlt := j.isLt
        omega)
      subst j
      exact ⟨topFreshTailGenealogyRearm k
        ((topFixedTraceRun ring C word).1.2.clock + 1)
        root, hnewSlot, hnewHistory⟩

/-- The root is blocked by an occupied OLD nonmarker
successor, so every previously issued stationary home
is away from the selected pair and retains its history.
Consumer: strengthened barrier blocked-root row. -/
theorem topFreshTailCohortIssuedBarrierRootOccupied
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (e : Fin n) (hsite : e = certSite s k.val)
    (hnext : k.val + 1 < topClockSpan n)
    (hoccupied :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qOut ≠ .E) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  apply topFreshTailCohortIssuedBarrierFrameStep
    ring C s word root k sample hbarrier e
    (topFreshTailFirstBorderHomeBarrierOccupiedStep
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      e hsite hnext hoccupied)
  intro j hj
  exact topFreshTailFirstBorderEarlierSiteOffSelectedPair
    ring s hn j k hj e hsite

/-- At the terminal marked comparison port, an OLD blocked
target QI/QC cannot consume the tracked root or change any
stationary-home issue history behind it.
Consumer: strengthened barrier blocked-port row. -/
theorem topFreshTailCohortIssuedBarrierPortBlocked
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (hterminal : k.val + 1 = topClockSpan n)
    (e : Fin n) (hsite : e = certSite s k.val)
    (hblocked :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qIn.isE = false ∨
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qCarry.isOff = false) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  apply topFreshTailCohortIssuedBarrierFrameStep
    ring C s word root k sample hbarrier e
    (topFreshTailFirstBorderHomeBarrierPortBlocked
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      hterminal e hsite hblocked)
  intro j hj
  exact topFreshTailFirstBorderEarlierSiteOffSelectedPair
    ring s hn j k hj e hsite


/-- When the strengthened root barrier reaches a free
terminal port, the accepted OLD true-tail root issues its
last stationary home and every earlier home keeps its
actual selected issue history. This proves the all-home
producer FROM the history-strengthened barrier; the
arbitrary-word strengthened barrier induction remains
a separate obligation. Consumer: first cohort W.base. -/
theorem topFreshTailCohortFirstAnchorAllHomeIssuesOfBarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (hterminal : k.val + 1 = topClockSpan n)
    (e : Fin n) (hsite : e = certSite s k.val)
    (hyi :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qIn = .E)
    (hyc :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qCarry = .OFF) :
    topClockGenuineTailAccepted C s
      (topFixedTraceRun ring C (word ++ [e])) ∧
    (∀ j : Fin (topClockSpan n),
      ∃ carrier : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (word ++ [e]))).slots j =
            some carrier ∧
        TopFreshTailCohortIssueHistory ring C s
          (word ++ [e]) j j root carrier) := by
  have haccepted :=
    topFreshTailAcceptedPortRootHomeStaircase
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      hterminal e hsite hyi hyc
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      hbarrier.barrier.spatial.queue.trace.1 k
  have hxl :
      ((topFixedTraceRun ring C word).1.1 e).l =
        false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hyb :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).beta = true := by
    have hm := hgeom.2.2.2
    rw [if_pos hterminal] at hm
    rw [hsite]
    exact hm
  have hsource :
      ((topFixedTraceRun ring C word).1.1 e).qOut =
        .D sample.value true := by
    rw [hsite]
    exact hbarrier.barrier.spatial.rootData
  have hnewU :
      ((topFixedTraceNext ring C
        (topFixedTraceRun ring C word) e).1.1 e).qOut =
          .U := by
    have hh :=
      topFreshTailAuditPhysicalPortDeparts
        ring C (topFixedTraceRun ring C word)
        e sample.value true hxl hyl hsource
        hyb hyi hyc
    simpa only [ite_true] using hh
  have hissueLast :
      TopFreshTailCohortIssueHistory ring C s
        (word ++ [e]) k k root
        (topFreshTailGenealogyRearm k
          ((topFixedTraceRun ring C word).1.2.clock + 1)
          root) := by
    have hh :=
      topFreshTailCohortIssueHistoryAtRearm
        ring C s (topFixedTraceRun ring C word)
        hbarrier.barrier.spatial.queue e k
        sample.value root hsite hsource
        hbarrier.barrier.spatial.rootSlot hnewU
    rw [topFreshTailFifoRunWord] at hh
    exact hh
  have hreal :=
    (topFreshTailCohortRealRearmIssueStep
      ring C s (topFixedTraceRun ring C word)
      hbarrier.barrier.spatial.queue
      e k sample.value root hsite hsource
      hbarrier.barrier.spatial.rootSlot hnewU).1
  obtain ⟨_, _, _, _, hchildSlot, _⟩ := hreal
  have hword :
      (topFixedTraceRun ring C word).2 ++
        [certSite s k.val] = word ++ [e] := by
    rw [topFreshTailFifoRunWord, ← hsite]
  have hlastSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (word ++ [e]))).slots k =
      some (topFreshTailGenealogyRearm k
        ((topFixedTraceRun ring C word).1.2.clock + 1)
        root) := by
    rw [hword] at hchildSlot
    exact hchildSlot
  have hk : k.val = topClockSpan n - 1 := by
    have hkl := k.isLt
    omega
  refine ⟨?_, ?_⟩
  · rw [topFreshTailFifoRunSnoc]
    exact haccepted.1
  · intro j
    by_cases hearlier : j.val < k.val
    · obtain ⟨carrier, hslot, hissue⟩ :=
        hbarrier.issueBehind j hearlier
      obtain ⟨hsourceAway, htargetAway⟩ :=
        topFreshTailFirstBorderEarlierSiteOffSelectedPair
          ring s hn j k hearlier e hsite
      have hframe :=
        (topFreshTailCausalOffPairSlotAgreement
          ring C s (topFixedTraceRun ring C word) e
          hbarrier.barrier.spatial.queue
          j hsourceAway htargetAway).2
      have hnextSlot :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
              some carrier := by
        rw [topFreshTailFifoRunSnoc, hframe]
        exact hslot
      exact ⟨carrier, hnextSlot,
        topFreshTailCohortIssueHistoryAppendStay
          ring C s word j j root carrier
          hissue e hslot hnextSlot⟩
    · have heq : j = k := Fin.ext (by
        have hj := j.isLt
        omega)
      subst j
      exact ⟨topFreshTailGenealogyRearm k
        ((topFixedTraceRun ring C word).1.2.clock + 1)
        root, hlastSlot, hissueLast⟩

/-- A leaderless incoming edge at a sampled root still at
position zero preserves the strengthened barrier, because
its issueBehind domain is empty. Consumer: boundary row of
the selected first-root history fold. -/
theorem topFreshTailCohortIssuedBarrierBorderIncomingAtZero
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (hkzero : k.val = 0)
    (e : Fin n)
    (hincoming :
      ring.rightNeighbor e = certSite s k.val) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  refine ⟨?_, ?_⟩
  · rw [topFreshTailFifoRunSnoc]
    exact topFreshTailFirstBorderHomeBarrierBorderIncoming
      ring C s hn hbad hl
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      hkzero e hincoming
  · intro j hj
    omega


/-- The one exceptional OLD home-zero U-to-D sample replaces
the full genealogical carrier but continues the SAME issued
home and parent history. The new child stamp comes from
the actual selected clock; a born-time comparison is not
used as a cohort label.
Consumer: history-strengthened behind-root U source row. -/
theorem topFreshTailCohortIssueHistoryAppendZeroRekey
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (zero : Fin (topClockSpan n))
    (hzero : zero.val = 0)
    (parent carrier : TopFreshTailCarrier (topClockSpan n))
    (hissue :
      TopFreshTailCohortIssueHistory
        ring C s word zero zero parent carrier)
    (e : Fin n)
    (hsite : e = certSite s zero.val)
    (hunread :
      ((topFixedTraceRun ring C word).1.1 e).qOut =
        .U)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata :
      ((topFixedTraceRun ring C (word ++ [e])).1.1 e).qOut =
        .D value true)
    (hslot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C word)).slots zero =
        some carrier)
    (hnextSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (word ++ [e]))).slots
          zero =
        some
          { origin := .freshBorder
              ((topFixedTraceRun ring C word).1.2.clock + 1)
            born :=
              (topFixedTraceRun ring C word).1.2.clock + 1 }) :
    TopFreshTailCohortIssueHistory
      ring C s (word ++ [e]) zero zero parent
      { origin := .freshBorder
          ((topFixedTraceRun ring C word).1.2.clock + 1)
        born :=
          (topFixedTraceRun ring C word).1.2.clock + 1 } := by
  unfold TopFreshTailCohortIssueHistory at hissue ⊢
  obtain ⟨before, after, issued, hword,
    hevent, hfollow⟩ := hissue
  refine ⟨before, after ++ [e], issued, ?_,
    hevent, ?_⟩
  · rw [hword]
    simp only [List.append_assoc, List.cons_append]
  · apply TopFreshTailCohortPacketFollow.snoc
      hfollow e zero
      { origin := .freshBorder
          ((topFixedTraceRun ring C word).1.2.clock + 1)
        born :=
          (topFixedTraceRun ring C word).1.2.clock + 1 }
    unfold TopFreshTailCohortPacketStep
    exact ⟨hslot, hnextSlot, Or.inr
      (Or.inr ⟨hzero, rfl, (by rw [hsite, hzero]), hunread,
        ⟨value, hdata⟩, rfl⟩)⟩


/-- The real border U sample begins the history-strengthened
root barrier with an empty issued-home segment; no artificial
parent event is required before the root has moved.
Consumer: topFreshTailCohortIssuedBarrierRootHop and barrier run. -/
theorem topFreshTailCohortIssuedBarrierInitial
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (e : Fin n)
    (hsite : e = certSite s 0)
    (hunread :
      ((topFixedTraceRun ring C word).1.1 e).qOut = .U) :
    ∃ sample : DigitSample
        (compileAdvice (ceilLogTwo n)) n,
      TopFreshTailCohortIssuedBarrier
        ring C s (word ++ [e])
        { origin := .freshBorder
            ((topFixedTraceRun ring C word).1.2.clock + 1)
          born :=
            (topFixedTraceRun ring C word).1.2.clock + 1 }
        (⟨0, show 0 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n))
        sample := by
  obtain ⟨sample, hbarrier⟩ :=
    topFreshTailFirstBorderHomeBarrierInitial
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      (topFreshTailAuditRunReached ring C word)
      e hsite hunread
  refine ⟨sample, ?_⟩
  apply topFreshTailCohortIssuedBarrierAtZero
    ring C s (word ++ [e])
    { origin := .freshBorder
        ((topFixedTraceRun ring C word).1.2.clock + 1)
      born :=
        (topFixedTraceRun ring C word).1.2.clock + 1 }
    (⟨0, show 0 < topClockSpan n by
      have hr := cert_rho_ge_three n hn
      change 3 ≤ topClockSpan n at hr
      omega⟩ : Fin (topClockSpan n))
    sample rfl
  rw [topFreshTailFifoRunSnoc]
  exact hbarrier


end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The selected OLD source behind the root keeps the same
issued-home history when D is blocked or a positive U samples.
A home-zero U sample instead follows its real zero-rekey edge.
Consumer: topFreshTailCohortIssuedBarrierBehindStep. -/
theorem topFreshTailCohortBehindSourceHistory
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (root carrier : TopFreshTailCarrier (topClockSpan n))
    (j : Fin (topClockSpan n))
    (e : Fin n)
    (hsite : e = certSite s j.val)
    (hnext : j.val + 1 < topClockSpan n)
    (hqueue : TopFreshTailCausalQueue ring C s
      (topFixedTraceRun ring C word))
    (hslot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C word)).slots j =
          some carrier)
    (hfresh : ∃ stamp : Nat,
      carrier.origin = .freshBorder stamp)
    (hissue :
      TopFreshTailCohortIssueHistory
        ring C s word j j root carrier)
    (hoccupied :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qOut ≠ .E) :
    ∃ afterCarrier : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (word ++ [e]))).slots j =
          some afterCarrier ∧
      TopFreshTailCohortIssueHistory
        ring C s (word ++ [e]) j j root afterCarrier := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      hqueue.trace.1 j
  have hxl :
      ((topFixedTraceRun ring C word).1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hnonempty :
      ((topFixedTraceRun ring C word).1.1 e).qOut ≠ .E := by
    rw [hsite]
    exact topFreshTailFirstBorderOccupiedOfCarrier
      ring C s (topFixedTraceRun ring C word)
      hqueue j carrier hslot
  cases htok : ((topFixedTraceRun ring C word).1.1 e).qOut with
  | E =>
      exact False.elim (hnonempty htok)
  | U =>
      by_cases hjzero : j.val = 0
      · have hghost :=
          topFreshTailCausalUnreadBorder
            ring C s
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C word))
            e j hsite hjzero
            (by rw [hqueue.trace.2]; exact htok)
            (by rw [hqueue.trace.2]; exact hxl)
            (by rw [hqueue.trace.2]; exact hyl)
        have hslotNext :
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C (word ++ [e]))).slots j =
              some {
                origin := .freshBorder
                  ((topFixedTraceRun ring C word).1.2.clock + 1)
                born :=
                  (topFixedTraceRun ring C word).1.2.clock + 1 } := by
          rw [topFreshTailFifoRunSnoc, topFreshTailCausalReplayNext]
          rw [hqueue.trace.2] at hghost
          exact hghost
        have hmark :
            ((topFixedTraceRun ring C word).1.1 e).beta =
              true := by
          have hm := hgeom.2.2.1
          rw [if_pos hjzero] at hm
          rw [hsite]
          exact hm
        have hsample :=
          topFreshTailFifoUnreadSamples
            ring C (topFixedTraceRun ring C word)
            e hxl hyl htok
        have hdata :
            ((topFixedTraceRun ring C (word ++ [e])).1.1 e).qOut =
              .D ((topFixedTraceRun ring C word).1.1 e).d true := by
          rw [topFreshTailFifoRunSnoc]
          rw [hmark] at hsample
          exact hsample
        refine ⟨{
            origin := .freshBorder
              ((topFixedTraceRun ring C word).1.2.clock + 1)
            born :=
              (topFixedTraceRun ring C word).1.2.clock + 1
          }, hslotNext, ?_⟩
        exact topFreshTailCohortIssueHistoryAppendZeroRekey
          ring C s word j hjzero root carrier hissue
          e hsite htok
          ((topFixedTraceRun ring C word).1.1 e).d
          hdata hslot hslotNext
      · have hjpositive : 0 < j.val := by omega
        have hghost :=
          topFreshTailCausalUnreadInterior
            ring C s
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C word))
            e j carrier hsite hjpositive
            (by rw [hqueue.trace.2]; exact htok)
            (by rw [hqueue.trace.2]; exact hxl)
            (by rw [hqueue.trace.2]; exact hyl)
            hslot
        have hslotNext :
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C (word ++ [e]))).slots j =
                some carrier := by
          rw [topFreshTailFifoRunSnoc, topFreshTailCausalReplayNext]
          exact hghost
        exact ⟨carrier, hslotNext,
          topFreshTailCohortIssueHistoryAppendStay
            ring C s word j j root carrier
            hissue e hslot hslotNext⟩
  | D value tail =>
      obtain ⟨_, hslotNew, _, _⟩ :=
        topFreshTailFirstBorderFreshOccupiedInteriorStep
          ring C s hn hbad
          (topFixedTraceRun ring C word)
          e hqueue j hnext hsite value tail
          htok hoccupied carrier hslot hfresh
      have hslotNext :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
              some carrier := by
        rw [topFreshTailFifoRunSnoc]
        exact hslotNew
      exact ⟨carrier, hslotNext,
        topFreshTailCohortIssueHistoryAppendStay
          ring C s word j j root carrier
          hissue e hslot hslotNext⟩

/-- A selected OLD responder which was occupied by U or D
retains its exact genealogy carrier. Neither the incoming
QO owner nor arbitrary QI/QC scratch may replace that byte.
Consumer: issued barrier behind-root responder home. -/
theorem topFreshTailCohortBehindResponderCarrierFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (e : Fin n)
    (i : Fin (topClockSpan n))
    (htarget : ring.rightNeighbor e = certSite s i.val)
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hslot :
      (topFreshTailGenealogy ring C s Z).slots i =
        some carrier) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots i =
        some carrier := by
  have hnonempty :=
    topFreshTailFirstBorderOccupiedOfCarrier
      ring C s Z hqueue i carrier hslot
  cases htok : (Z.1.1 (certSite s i.val)).qOut with
  | E =>
      exact False.elim (hnonempty htok)
  | U =>
      exact (topFreshTailFirstBorderIncomingUnreadFrame
        ring C s hn Z e hqueue hl i htarget
        htok carrier hslot).2
  | D value tail =>
      exact (topFreshTailFirstBorderIncomingDataFrame
        ring C s hn Z e hqueue hl i htarget
        value tail htok carrier hslot).2.1


/-- All issued homes strictly behind the moving root survive a
selected OLD source service. The served home either samples
its U (including the genuine home-zero carrier rekey) or keeps
its blocked D. An already issued responder keeps the same
carrier; all other issued homes are off the physical pair.
Consumer: first-root cohort barrier one-edge dispatcher. -/
theorem topFreshTailCohortIssuedBarrierBehindStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (j : Fin (topClockSpan n))
    (hbelow : j.val < k.val)
    (e : Fin n)
    (hsite : e = certSite s j.val) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  have hgreen :=
    topFreshTailFirstBorderHomeBarrierBehindStep
      ring C s hn hbad hl
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      j hbelow e hsite
  have hnext : j.val + 1 < topClockSpan n := by
    have hklt := k.isLt
    omega
  have hneighbor :
      ring.rightNeighbor e = certSite s (j.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite
      ring s j.val
  have hnextCarrier :
      ∃ carrier : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C word)).slots
          (⟨j.val + 1,
            show j.val + 1 < topClockSpan n by
              exact hnext⟩ : Fin (topClockSpan n)) =
          some carrier := by
    by_cases hbeforeRoot : j.val + 1 < k.val
    · obtain ⟨carrier, hslot, _⟩ :=
        hbarrier.barrier.spatial.behind
          (⟨j.val + 1,
            show j.val + 1 < topClockSpan n by
              exact hnext⟩ : Fin (topClockSpan n))
          hbeforeRoot
      exact ⟨carrier, hslot⟩
    · have heq :
          (⟨j.val + 1,
            show j.val + 1 < topClockSpan n by
              exact hnext⟩ : Fin (topClockSpan n)) = k := by
        apply Fin.ext
        have hklt := k.isLt
        show j.val + 1 = k.val
        omega
      rw [heq]
      exact ⟨root, hbarrier.barrier.spatial.rootSlot⟩
  have hoccupied :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qOut ≠ .E := by
    obtain ⟨carrier, hslot⟩ := hnextCarrier
    rw [hneighbor]
    exact topFreshTailFirstBorderOccupiedOfCarrier
      ring C s (topFixedTraceRun ring C word)
      hbarrier.barrier.spatial.queue
      (⟨j.val + 1,
        show j.val + 1 < topClockSpan n by
          exact hnext⟩ : Fin (topClockSpan n))
      carrier hslot
  refine ⟨?_, ?_⟩
  · rw [topFreshTailFifoRunSnoc]
    exact hgreen
  · intro i hi
    obtain ⟨carrier, hslot, hissue⟩ :=
      hbarrier.issueBehind i hi
    by_cases hsame : i = j
    · subst i
      obtain ⟨freshCarrier, hfreshSlot, hfresh⟩ :=
        hbarrier.barrier.spatial.behind j hbelow
      have hsameCarrier : freshCarrier = carrier :=
        Option.some.inj (hfreshSlot.symm.trans hslot)
      rw [hsameCarrier] at hfresh
      exact topFreshTailCohortBehindSourceHistory
        ring C s hn hbad word root carrier j
        e hsite hnext
        hbarrier.barrier.spatial.queue
        hslot hfresh hissue hoccupied
    · by_cases htarget :
          certSite s i.val = ring.rightNeighbor e
      · have hpostSlot :=
          topFreshTailCohortBehindResponderCarrierFrame
            ring C s hn hl
            (topFixedTraceRun ring C word)
            hbarrier.barrier.spatial.queue
            e i htarget.symm carrier hslot
        have hslotNext :
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C (word ++ [e]))).slots i =
              some carrier := by
          rw [topFreshTailFifoRunSnoc]
          exact hpostSlot
        exact ⟨carrier, hslotNext,
          topFreshTailCohortIssueHistoryAppendStay
            ring C s word i i root carrier
            hissue e hslot hslotNext⟩
      · have hsourceAway : certSite s i.val ≠ e := by
          intro hcollision
          have hindex :=
            topFreshTailCausalSourceSiteInjective
              s hn i j (hcollision.trans hsite)
          exact hsame hindex
        have hframe :=
          (topFreshTailCausalOffPairSlotAgreement
            ring C s (topFixedTraceRun ring C word)
            e hbarrier.barrier.spatial.queue
            i hsourceAway htarget).2
        have hslotNext :
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C (word ++ [e]))).slots i =
              some carrier := by
          rw [topFreshTailFifoRunSnoc, hframe]
          exact hslot
        exact ⟨carrier, hslotNext,
          topFreshTailCohortIssueHistoryAppendStay
            ring C s word i i root carrier
            hissue e hslot hslotNext⟩


/-- An incoming OLD edge from outside the source arc touches
only source home zero. The selected zero-home responder stays
with its old carrier, while every positive issued home frames
off the pair. Consumer: cohort barrier dispatcher, incoming row. -/
theorem topFreshTailCohortIssuedBarrierIncomingZero
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (hpositive : 0 < k.val)
    (e : Fin n)
    (hincoming :
      ring.rightNeighbor e = certSite s 0) :
    TopFreshTailCohortIssuedBarrier
      ring C s (word ++ [e]) root k sample := by
  have hgreen :=
    topFreshTailFirstBorderHomeBarrierIncomingZero
      ring C s hn hbad hl
      (topFixedTraceRun ring C word)
      root k sample hbarrier.barrier
      hpositive e hincoming
  have hawaySource :=
    topFreshTailFirstBorderIncomingZeroOutsideSource
      ring s hn e hincoming
  refine ⟨?_, ?_⟩
  · rw [topFreshTailFifoRunSnoc]
    exact hgreen
  · intro j hj
    obtain ⟨carrier, hslot, hissue⟩ :=
      hbarrier.issueBehind j hj
    by_cases hzero : j.val = 0
    · have htarget :
          ring.rightNeighbor e = certSite s j.val := by
        rw [hzero]
        exact hincoming
      have hpost :=
        topFreshTailCohortBehindResponderCarrierFrame
          ring C s hn hl
          (topFixedTraceRun ring C word)
          hbarrier.barrier.spatial.queue
          e j htarget carrier hslot
      have hslotNext :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
              some carrier := by
        rw [topFreshTailFifoRunSnoc]
        exact hpost
      exact ⟨carrier, hslotNext,
        topFreshTailCohortIssueHistoryAppendStay
          ring C s word j j root carrier
          hissue e hslot hslotNext⟩
    · have htargetAway :
          certSite s j.val ≠ ring.rightNeighbor e := by
        rw [hincoming]
        intro heq
        have hwidth : 0 < topClockSpan n := by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega
        have hindex :=
          topFreshTailCausalSourceSiteInjective
            s hn j
            (⟨0, hwidth⟩ : Fin (topClockSpan n))
            heq
        have hvalue := congrArg Fin.val hindex
        exact hzero hvalue
      have hframe :=
        (topFreshTailCausalOffPairSlotAgreement
          ring C s (topFixedTraceRun ring C word)
          e hbarrier.barrier.spatial.queue
          j (hawaySource j) htargetAway).2
      have hslotNext :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
              some carrier := by
        rw [topFreshTailFifoRunSnoc, hframe]
        exact hslot
      exact ⟨carrier, hslotNext,
        topFreshTailCohortIssueHistoryAppendStay
          ring C s word j j root carrier
          hissue e hslot hslotNext⟩


/-- Every actual OLD selected service either preserves the
history-strengthened moving-root barrier (possibly one
position farther right), or accepts the tracked true-tail
root and yields an actual issue-history certificate at
every final stationary source home.
Consumer: topFreshTailCohortIssuedBarrierRun. -/
theorem topFreshTailCohortIssuedBarrierEdge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (e : Fin n) :
    (∃ moved : Fin (topClockSpan n),
      TopFreshTailCohortIssuedBarrier
        ring C s (word ++ [e]) root moved sample ∧
      (moved = k ∨ moved.val = k.val + 1)) ∨
    (topClockGenuineTailAccepted C s
      (topFixedTraceRun ring C (word ++ [e])) ∧
      ∀ j : Fin (topClockSpan n),
        ∃ carrier : TopFreshTailCarrier (topClockSpan n),
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
            some carrier ∧
          TopFreshTailCohortIssueHistory
            ring C s (word ++ [e]) j j root carrier) := by
  by_cases hsource :
      ∃ j : Fin (topClockSpan n), e = certSite s j.val
  · obtain ⟨j, hsite⟩ := hsource
    by_cases hbelow : j.val < k.val
    · left
      exact ⟨k,
        topFreshTailCohortIssuedBarrierBehindStep
          ring C s hn hbad hl word root k sample
          hbarrier j hbelow e hsite,
        Or.inl rfl⟩
    · by_cases hequal : j.val = k.val
      · have hindex : j = k := Fin.ext hequal
        subst j
        by_cases hnext : k.val + 1 < topClockSpan n
        · cases htarget :
            ((topFixedTraceRun ring C word).1.1
              (ring.rightNeighbor e)).qOut with
          | E =>
              left
              exact ⟨(⟨k.val + 1,
                show k.val + 1 < topClockSpan n by
                  exact hnext⟩ : Fin (topClockSpan n)),
                topFreshTailCohortIssuedBarrierRootHop
                  ring C s hn hbad word root k sample
                  hbarrier e hsite hnext htarget,
                Or.inr rfl⟩
          | U =>
              have hoccupied :
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qOut ≠ .E := by
                intro h
                rw [htarget] at h
                cases h
              left
              exact ⟨k,
                topFreshTailCohortIssuedBarrierRootOccupied
                  ring C s hn hbad word root k sample
                  hbarrier e hsite hnext hoccupied,
                Or.inl rfl⟩
          | D value tail =>
              have hoccupied :
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qOut ≠ .E := by
                intro h
                rw [htarget] at h
                cases h
              left
              exact ⟨k,
                topFreshTailCohortIssuedBarrierRootOccupied
                  ring C s hn hbad word root k sample
                  hbarrier e hsite hnext hoccupied,
                Or.inl rfl⟩
        · have hterminal : k.val + 1 = topClockSpan n := by
            have hklt := k.isLt
            omega
          cases hinput :
              ((topFixedTraceRun ring C word).1.1
                (ring.rightNeighbor e)).qIn with
          | E =>
              cases hcarry :
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qCarry with
              | OFF =>
                  right
                  exact topFreshTailCohortFirstAnchorAllHomeIssuesOfBarrier
                    ring C s hn hbad word root k sample
                    hbarrier hterminal e hsite hinput hcarry
              | L bit err =>
                  have hblocked :
                      ((topFixedTraceRun ring C word).1.1
                        (ring.rightNeighbor e)).qIn.isE =
                          false ∨
                      ((topFixedTraceRun ring C word).1.1
                        (ring.rightNeighbor e)).qCarry.isOff =
                          false :=
                    Or.inr (by simp [hcarry, QCarry.isOff])
                  left
                  exact ⟨k,
                    topFreshTailCohortIssuedBarrierPortBlocked
                      ring C s hn hbad word root k sample
                      hbarrier hterminal e hsite hblocked,
                    Or.inl rfl⟩
          | P value tail =>
              have hblocked :
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qIn.isE =
                      false ∨
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qCarry.isOff =
                      false :=
                Or.inl (by simp [hinput, InTok.isE])
              left
              exact ⟨k,
                topFreshTailCohortIssuedBarrierPortBlocked
                  ring C s hn hbad word root k sample
                  hbarrier hterminal e hsite hblocked,
                Or.inl rfl⟩
          | S value tail =>
              have hblocked :
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qIn.isE =
                      false ∨
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qCarry.isOff =
                      false :=
                Or.inl (by simp [hinput, InTok.isE])
              left
              exact ⟨k,
                topFreshTailCohortIssuedBarrierPortBlocked
                  ring C s hn hbad word root k sample
                  hbarrier hterminal e hsite hblocked,
                Or.inl rfl⟩
          | X =>
              have hblocked :
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qIn.isE =
                      false ∨
                  ((topFixedTraceRun ring C word).1.1
                    (ring.rightNeighbor e)).qCarry.isOff =
                      false :=
                Or.inl (by simp [hinput, InTok.isE])
              left
              exact ⟨k,
                topFreshTailCohortIssuedBarrierPortBlocked
                  ring C s hn hbad word root k sample
                  hbarrier hterminal e hsite hblocked,
                Or.inl rfl⟩
      · have hahead : k.val < j.val := by omega
        left
        exact ⟨k,
          topFreshTailCohortIssuedBarrierAheadStep
            ring C s hn hbad word root k sample
            hbarrier j hahead e hsite,
          Or.inl rfl⟩
  · by_cases hincoming :
        ∃ j : Fin (topClockSpan n),
          ring.rightNeighbor e = certSite s j.val
    · obtain ⟨j, htarget⟩ := hincoming
      by_cases hjzero : j.val = 0
      · have hzeroIncoming :
            ring.rightNeighbor e = certSite s 0 := by
          rw [htarget, hjzero]
        by_cases hkzero : k.val = 0
        · left
          exact ⟨k,
            topFreshTailCohortIssuedBarrierBorderIncomingAtZero
              ring C s hn hbad hl word root k sample
              hbarrier hkzero e
              (by rw [hkzero]; exact hzeroIncoming),
            Or.inl rfl⟩
        · have hkpositive : 0 < k.val := by omega
          left
          exact ⟨k,
            topFreshTailCohortIssuedBarrierIncomingZero
              ring C s hn hbad hl word root k sample
              hbarrier hkpositive e hzeroIncoming,
            Or.inl rfl⟩
      · have hjpositive : 0 < j.val := by omega
        have hpredecessor :=
          topFreshTailCausalIncomingPredecessor
            ring hn s j hjpositive e htarget
        have hprevBound : j.val - 1 < topClockSpan n := by
          have hjlt := j.isLt
          omega
        exact False.elim (hsource
          ⟨(⟨j.val - 1, hprevBound⟩ :
              Fin (topClockSpan n)), hpredecessor⟩)
    · have hawaySource :
          ∀ j : Fin (topClockSpan n),
            certSite s j.val ≠ e := by
        intro j h
        exact hsource ⟨j, h.symm⟩
      have hawayTarget :
          ∀ j : Fin (topClockSpan n),
            certSite s j.val ≠ ring.rightNeighbor e := by
        intro j h
        exact hincoming ⟨j, h.symm⟩
      left
      exact ⟨k,
        topFreshTailCohortIssuedBarrierAwayStep
          ring C s hn hbad word root k sample
          hbarrier e hawaySource hawayTarget,
        Or.inl rfl⟩


end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Fold the history-strengthened root barrier through any
finite actual scheduler continuation, stopping at its first
selected terminal acceptance. In the accepting branch every
final home has an explicit real issue and packet-follow
history, not merely a fresh carrier equality.
Consumer: topFreshTailCohortFirstAnchorAllHomeIssues. -/
theorem topFreshTailCohortIssuedBarrierRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n)) :
    ∀ (history : List (Fin n))
      (root : TopFreshTailCarrier (topClockSpan n))
      (k : Fin (topClockSpan n))
      (sample : DigitSample
        (compileAdvice (ceilLogTwo n)) n),
      TopFreshTailCohortIssuedBarrier
        ring C s history root k sample →
      (∃ lastPosition : Fin (topClockSpan n),
        TopFreshTailCohortIssuedBarrier
          ring C s (history ++ word)
          root lastPosition sample ∧
        k.val ≤ lastPosition.val) ∨
      (∃ (front suffix : List (Fin n)) (edge : Fin n),
        word = front ++ edge :: suffix ∧
        topClockGenuineTailAccepted C s
          (topFixedTraceRun ring C
            (history ++ front ++ [edge])) ∧
        ∀ j : Fin (topClockSpan n),
          ∃ carrier : TopFreshTailCarrier (topClockSpan n),
            (topFreshTailGenealogy ring C s
              (topFixedTraceRun ring C
                (history ++ front ++ [edge]))).slots j =
              some carrier ∧
            TopFreshTailCohortIssueHistory
              ring C s (history ++ front ++ [edge])
              j j root carrier) := by
  induction word with
  | nil =>
      intro history root k sample hbarrier
      left
      refine ⟨k, ?_, Nat.le_refl _⟩
      simpa only [List.append_nil] using hbarrier
  | cons e rest ih =>
      intro history root k sample hbarrier
      rcases topFreshTailCohortIssuedBarrierEdge
          ring C s hn hbad hl history root k sample
          hbarrier e with
        ⟨moved, hbarrierNext, hstep⟩ |
        ⟨haccepted, hissued⟩
      · rcases ih (history ++ [e]) root moved sample
          hbarrierNext with
          ⟨finalPosition, hfinal, hmonotone⟩ |
          ⟨front, suffix, edge, hword, haccepted, hfinalIssued⟩
        · left
          refine ⟨finalPosition, ?_, ?_⟩
          · simpa only [List.cons_append,
              List.singleton_append, List.append_assoc, List.nil_append]
              using hfinal
          · rcases hstep with hstay | hmove
            · rw [hstay] at hmonotone
              exact hmonotone
            · omega
        · right
          refine ⟨e :: front, suffix, edge, ?_, ?_, ?_⟩
          · rw [hword]
            rfl
          · simpa only [List.cons_append,
              List.singleton_append, List.append_assoc, List.nil_append]
              using haccepted
          · simpa only [List.cons_append,
              List.singleton_append, List.append_assoc, List.nil_append]
              using hfinalIssued
      · right
        refine ⟨[], rest, e, rfl, ?_, ?_⟩
        · simpa only [List.nil_append, List.append_nil]
            using haccepted
        · simpa only [List.nil_append, List.append_nil]
            using hissued


/-- Assemble the selected first current cohort from the actual
first-anchor issue histories and stationary home certificates.
Its root sits at home zero, the next map is empty, all
chronological post-anchor exports are empty, and every
physical source carrier belongs to the selected current map.
Consumer: topFreshTailPostAnchorCohortWaveBase. -/
theorem topFreshTailCohortWaveBaseFromHomeIssues
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hreached : topClockReached ring C Z)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (hanchor : topClockConcreteTailAnchor s Z anchor)
    (htime : anchor.time = Z.1.2.clock)
    (hparent :
      TopFreshTailCohortHistoricalParent
        ring C s hn Z anchor 0 parent)
    (hhomes :
      ∀ j : Fin (topClockSpan n),
        ∃ a : TopFreshTailCarrier (topClockSpan n),
          TopFreshTailPostAnchorActiveHome
            ring C s Z j j a)
    (hissued :
      ∀ j : Fin (topClockSpan n),
        ∃ a : TopFreshTailCarrier (topClockSpan n),
          (topFreshTailGenealogy ring C s Z).slots j =
            some a ∧
          TopFreshTailCohortIssueHistory
            ring C s Z.2 j j parent a) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor) := by
  classical
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hempty :=
    topFreshTailCohortFirstAnchorExportsEmpty
      ring C s Z anchor hreached htime
  have hselected :
      ∀ j : Fin (topClockSpan n),
        ∃ a : TopFreshTailCarrier (topClockSpan n),
          (topFreshTailGenealogy ring C s Z).slots j =
            some a ∧
          TopFreshTailPostAnchorActiveHome
            ring C s Z j j a ∧
          TopFreshTailCohortIssueHistory
            ring C s Z.2 j j parent a := by
    intro j
    obtain ⟨a, hslot, hissue⟩ := hissued j
    obtain ⟨b, hactive⟩ := hhomes j
    have heq : a = b :=
      Option.some.inj (hslot.symm.trans hactive.2.1)
    rw [←heq] at hactive
    exact ⟨a, hslot, hactive, hissue⟩
  refine ⟨{
    reached := hreached
    queue := hqueue
    provenance :=
      topFreshTailAuditSourceDataReached
        ring C s hn hbad Z hreached
    anchorRecorded := hanchor
    allFresh := ?_
    currentMap := fun h =>
      some (h, Classical.choose (hselected h))
    nextMap := fun _ => none
    currentParent := parent
    currentParentReceipt := ?_
    root := Classical.choose (hselected
      (⟨0, show 0 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n)))
    rootPosition :=
      (⟨0, show 0 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n))
    rootSelected := rfl
    currentIssued := ?_
    currentAbsent := ?_
    currentOrder := ?_
    rootKind := ?_
    nextIssued := ?_
    nextAbsent := ?_
    sourceCoverage := ?_
    selectedHead := ?_
    exportRecords := ?_
  }⟩
  · intro j a hslot
    have hchosen := Classical.choose_spec (hselected j)
    have heq : a = Classical.choose (hselected j) :=
      Option.some.inj (hslot.symm.trans hchosen.1)
    rw [heq]
    obtain ⟨_, _, hfresh, _⟩ := hchosen.2.1
    exact hfresh
  · simpa only [hempty, List.length_nil, Nat.zero_div]
      using hparent
  · intro h _
    refine ⟨h, Classical.choose (hselected h),
      rfl, (Classical.choose_spec (hselected h)).2.1, ?_⟩
    unfold TopFreshTailIssuedInCohort
    exact ⟨rfl, (Classical.choose_spec (hselected h)).2.2⟩
  · intro h houtside
    have hh := h.isLt
    rw [hempty] at houtside
    simp only [List.length_nil, Nat.zero_mod,
      Nat.sub_zero] at houtside
    omega
  · intro h i hlt _ x y a b hx hy
    change
      some (h, Classical.choose (hselected h)) =
        some (x, a) at hx
    change
      some (i, Classical.choose (hselected i)) =
        some (y, b) at hy
    have hxeq : h = x :=
      congrArg Prod.fst (Option.some.inj hx)
    have hyeq : i = y :=
      congrArg Prod.fst (Option.some.inj hy)
    rw [← hxeq, ← hyeq]
    exact hlt
  · have hzero :=
      (Classical.choose_spec (hselected
        (⟨0, show 0 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)))).2.1
    obtain ⟨_, _, _, hkind⟩ := hzero
    rcases hkind with hunread |
      ⟨localSample, hdata, hrecord, hlane, hsite,
        hvalue, htail, hatom⟩
    · exact Or.inl ⟨rfl, hunread.2⟩
    · apply Or.inr
      refine ⟨localSample, hrecord, hlane,
        hsite, ?_, ?_, hatom⟩
      · simpa only [Fin.val_mk, if_true] using htail
      · rw [← hvalue] at hdata
        simpa only [Fin.val_mk, if_true] using hdata
  · intro j hj
    have hv := j.isLt
    change j.val < 0 at hj
    omega
  · intro j _
    rfl
  · intro j a hslot
    apply Or.inl
    refine ⟨j, ?_, rfl⟩
    have hchosen :=
      (Classical.choose_spec (hselected j)).1
    have heq : a = Classical.choose (hselected j) :=
      Option.some.inj (hslot.symm.trans hchosen)
    rw [heq]
  · intro value tail _
    refine ⟨Classical.choose (hselected
      (⟨topClockSpan n - 1,
        show topClockSpan n - 1 < topClockSpan n by
          omega⟩ : Fin (topClockSpan n))), ?_, ?_⟩
    · have hindex :
          (⟨topClockSpan n - 1 -
              ((topClockConcreteExportsAfter
                s Z anchor.time).length % topClockSpan n),
            show topClockSpan n - 1 -
              ((topClockConcreteExportsAfter
                s Z anchor.time).length % topClockSpan n) <
                topClockSpan n by omega⟩ :
              Fin (topClockSpan n)) =
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              omega⟩ : Fin (topClockSpan n)) := by
        apply Fin.ext
        change topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) = topClockSpan n - 1
        have hlen : (topClockConcreteExportsAfter
            s Z anchor.time).length = 0 :=
          congrArg List.length hempty
        simp only [hlen, Nat.zero_mod, Nat.sub_zero]
      rw [hindex]
    · exact (Classical.choose_spec (hselected
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            omega⟩ : Fin (topClockSpan n)))).1
  · intro i
    have hlen :
        (topClockConcreteExportsAfter
          s Z anchor.time).length = 0 := by
      rw [hempty]
      rfl
    have hi := i.isLt
    omega


/-- The actual terminal accepted service of an issue-bearing
first-root barrier establishes a genuine anchor and a
fully selected first current cohort. All selected homes
carry historical issue events and a literal packet-follow
chain from the complete OLD tracked parent; no next family
has yet been issued from the new home-zero root.
Consumer: the J5 post-anchor wave word fold. -/
theorem topFreshTailPostAnchorCohortWaveBase
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailCohortIssuedBarrier
        ring C s word root k sample)
    (hterminal : k.val + 1 = topClockSpan n)
    (e : Fin n) (hsite : e = certSite s k.val)
    (hyi :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qIn = .E)
    (hyc :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qCarry = .OFF) :
    ∃ anchor : DigitExport
        (compileAdvice (ceilLogTwo n)) n,
      topClockConcreteTailAnchor s
        (topFixedTraceRun ring C (word ++ [e])) anchor ∧
      anchor.time =
        (topFixedTraceRun ring C (word ++ [e])).1.2.clock ∧
      Nonempty (TopFreshTailPostAnchorCohortWave
        ring C s hn
        (topFixedTraceRun ring C (word ++ [e])) anchor) := by
  obtain ⟨anchor, hanchor, htime, hparent,
    hhomes, _⟩ :=
    topFreshTailCohortFirstAnchorEnvelope
      ring C s hn hbad hl word root k sample
      hbarrier.barrier hterminal e hsite hyi hyc
  obtain ⟨_, hissues⟩ :=
    topFreshTailCohortFirstAnchorAllHomeIssuesOfBarrier
      ring C s hn hbad word root k sample
      hbarrier hterminal e hsite hyi hyc
  have hqueueNext :=
    topFreshTailCausalQueueStep
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      e hbarrier.barrier.spatial.queue
  have hqueue :
      TopFreshTailCausalQueue ring C s
        (topFixedTraceRun ring C (word ++ [e])) := by
    rw [topFreshTailFifoRunSnoc]
    exact hqueueNext
  have hissued :
      ∀ j : Fin (topClockSpan n),
        ∃ a : TopFreshTailCarrier (topClockSpan n),
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (word ++ [e]))).slots j =
              some a ∧
          TopFreshTailCohortIssueHistory ring C s
            (topFixedTraceRun ring C (word ++ [e])).2
            j j root a := by
    intro j
    obtain ⟨a, hslot, hhistory⟩ := hissues j
    refine ⟨a, hslot, ?_⟩
    rw [topFreshTailFifoRunWord]
    exact hhistory
  refine ⟨anchor, hanchor, htime, ?_⟩
  exact topFreshTailCohortWaveBaseFromHomeIssues
    ring C s hn hbad
    (topFixedTraceRun ring C (word ++ [e]))
    anchor root
    (topFreshTailAuditRunReached
      ring C (word ++ [e]))
    hqueue hanchor htime hparent
    hhomes hissued


/-- Beginning with an actually selected source-border U sample,
every finite scheduler continuation either still carries the
issued-home barrier or contains a first selected genuine
tracked-root acceptance. In the latter case every source
home has the actual root-parent issue history. No
history assumptions are supplied at the start: the empty
issued segment is furnished by the OLD root birth.
Consumer: first-anchor selected cohort-wave base. -/
theorem topFreshTailCohortFirstAnchorAllHomeIssues
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (history : List (Fin n))
    (birth : Fin n)
    (hbirth : birth = certSite s 0)
    (hunread :
      ((topFixedTraceRun ring C history).1.1 birth).qOut =
        .U)
    (word : List (Fin n)) :
    (∃ (sample : DigitSample
        (compileAdvice (ceilLogTwo n)) n)
      (position : Fin (topClockSpan n)),
      TopFreshTailCohortIssuedBarrier
        ring C s ((history ++ [birth]) ++ word)
        { origin := .freshBorder
            ((topFixedTraceRun ring C history).1.2.clock + 1)
          born :=
            (topFixedTraceRun ring C history).1.2.clock + 1 }
        position sample) ∨
    (∃ (sample : DigitSample
        (compileAdvice (ceilLogTwo n)) n)
      (front suffix : List (Fin n)) (edge : Fin n),
      word = front ++ edge :: suffix ∧
      topClockGenuineTailAccepted C s
        (topFixedTraceRun ring C
          ((history ++ [birth]) ++ front ++ [edge])) ∧
      ∀ j : Fin (topClockSpan n),
        ∃ carrier : TopFreshTailCarrier (topClockSpan n),
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C
              ((history ++ [birth]) ++ front ++ [edge]))).slots j =
              some carrier ∧
          TopFreshTailCohortIssueHistory
            ring C s ((history ++ [birth]) ++ front ++ [edge])
            j j
            { origin := .freshBorder
                ((topFixedTraceRun ring C history).1.2.clock + 1)
              born :=
                (topFixedTraceRun ring C history).1.2.clock + 1 }
            carrier) := by
  obtain ⟨sample, hbarrier⟩ :=
    topFreshTailCohortIssuedBarrierInitial
      ring C s hn hbad history birth hbirth hunread
  rcases topFreshTailCohortIssuedBarrierRun
      ring C s hn hbad hl word
      (history ++ [birth])
      { origin := .freshBorder
          ((topFixedTraceRun ring C history).1.2.clock + 1)
        born :=
          (topFixedTraceRun ring C history).1.2.clock + 1 }
      (⟨0, show 0 < topClockSpan n by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ : Fin (topClockSpan n))
      sample hbarrier with
    ⟨position, hfinal, _⟩ |
    ⟨front, suffix, edge, hword, haccepted, hissued⟩
  · left
    exact ⟨sample, position, hfinal⟩
  · right
    exact ⟨sample, front, suffix, edge,
      hword, haccepted, hissued⟩

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A selected root is an actual active genealogy slot.
Consumer: J5 rows eight, ten and fourteen. -/
theorem topFreshTailCohortWaveRowEightSelectedRootSlot
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor) :
    TopFreshTailPostAnchorActiveHome ring C s Z
      (⟨0, show 0 < topClockSpan n by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ : Fin (topClockSpan n))
      W.rootPosition W.root ∧
    (topFreshTailGenealogy ring C s Z).slots W.rootPosition =
      some W.root := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  obtain ⟨x, a, hmap, hactive, _⟩ :=
    W.currentIssued
      (⟨0, show 0 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n))
      (Nat.zero_le _)
  have hpair : (x, a) = (W.rootPosition, W.root) :=
    Option.some.inj (hmap.symm.trans W.rootSelected)
  have hx : x = W.rootPosition := congrArg Prod.fst hpair
  have ha : a = W.root := congrArg Prod.snd hpair
  rw [hx, ha] at hactive
  exact ⟨hactive, hactive.2.1⟩

/-- Literal current-root true departure moves its full carrier
and gives the new next child an authenticated rearm event.
Consumer: J5 row eight map/history update. -/
theorem topFreshTailCohortWaveRowEightRootHopIssue
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots W.rootPosition =
      some (topFreshTailGenealogyRearm W.rootPosition
        (Z.1.2.clock + 1) W.root) ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots
        (⟨W.rootPosition.val + 1, hnext⟩ :
          Fin (topClockSpan n)) = some W.root ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U ∧
    TopFreshTailCohortIssueHistory ring C s
      (Z.2 ++ [e]) W.rootPosition W.rootPosition W.root
      (topFreshTailGenealogyRearm W.rootPosition
        (Z.1.2.clock + 1) W.root) := by
  have hrootSlot :=
    (topFreshTailCohortWaveRowEightSelectedRootSlot
      ring C s hn Z anchor W).2
  have hfresh := W.allFresh W.rootPosition W.root hrootSlot
  rcases W.rootKind with ⟨hk, hU⟩ |
    ⟨sample, hrecord, _, _, _, hsourceAtRoot, hatom⟩
  · rw [hsite, hk, hU] at hdata
    cases hdata
  · have hsource :
        (Z.1.1 e).qOut = .D sample.value true := by
      rw [hsite]
      exact hsourceAtRoot
    have hatomSource :
        (Z.1.2.current e).comparison.out.atom =
          some (.sampled sample.id) := by
      rw [hsite]
      exact hatom
    have hgeom :=
      topFreshTailCausalSourcePublicGeometry
        ring C s hn hbad Z W.queue.trace.1 W.rootPosition
    have hxl : (Z.1.1 e).l = false := by
      rw [hsite]
      exact hgeom.1
    have hyl :
        (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [hsite]
      exact hgeom.2.1
    have hyb :
        (Z.1.1 (ring.rightNeighbor e)).beta = false := by
      have hm := hgeom.2.2.2
      rw [if_neg (show W.rootPosition.val + 1 ≠
        topClockSpan n by omega)] at hm
      rw [hsite]
      exact hm
    have hstep := topFreshTailFirstBorderStaircaseStep
      ring C s hn hbad Z e W.rootPosition hnext hsite
      W.root hrootSlot hfresh sample hrecord hatomSource
      sample.value hsource hempty hxl hyl hyb W.queue
    have hissued :=
      topFreshTailCohortIssueHistoryAtRearm
        ring C s Z W.queue e W.rootPosition
        sample.value W.root hsite hsource hrootSlot
        hstep.2.2.1
    exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hissued⟩

/-- Occupied successor preserves the sampled selected current
home and continues the same authenticated issue history.
Consumer: J5 row nine blocked-current map frame. -/
theorem topFreshTailCohortWaveRowNineBlockedCurrent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n))
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hdata :
      (Z.1.1 e).qOut =
        .D (C (certSite s h.val)).d
          (if h.val = 0 then true else false))
    (hoccupied :
      (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) :
    TopFreshTailPostAnchorActiveHome ring C s
      (topFixedTraceNext ring C Z e) h x carrier ∧
    TopFreshTailCohortIssueHistory ring C s
      (Z.2 ++ [e]) h x W.currentParent carrier := by
  obtain ⟨oldX, oldCarrier, hmapOld, hactive, hissued⟩ :=
    W.currentIssued h hbound
  have hpair : (oldX, oldCarrier) = (x, carrier) :=
    Option.some.inj (hmapOld.symm.trans hmap)
  have hx : oldX = x := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hx, ha] at hactive hissued
  have hactiveNext :=
    topFreshTailPostAnchorActiveHomeOccupied
      ring C s hn hbad Z W.queue
      h x carrier hactive e hsite hnext hdata hoccupied
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hslotOld :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots x =
          some carrier := by
    rw [hrun]
    exact hactive.2.1
  have hslotNew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots x =
          some carrier := by
    rw [topFreshTailFifoRunSnoc, hrun]
    exact hactiveNext.2.1
  exact ⟨hactiveNext,
    topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 h x W.currentParent carrier
      hissued.2 e hslotOld hslotNew⟩

/-- Every selected stationary-next source has an occupied next
site: the successor is another next child or the pinned root.
Consumer: J5 row ten stationary next-D block. -/
theorem topFreshTailCohortWaveRowTenSuccessorOccupied
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hbehind : j.val < W.rootPosition.val)
    (e : Fin n) (hsite : e = certSite s j.val) :
    (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E := by
  have hnext : j.val + 1 < topClockSpan n := by
    have hk := W.rootPosition.isLt
    omega
  have hneighbor :
      ring.rightNeighbor e = certSite s (j.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s j.val
  rw [hneighbor]
  by_cases hbefore : j.val + 1 < W.rootPosition.val
  · obtain ⟨carrier, _, hslot, _, _⟩ :=
      W.nextIssued
        (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by simpa only [Fin.val_mk] using hbefore)
    exact topFreshTailFirstBorderOccupiedOfCarrier
      ring C s Z W.queue
      (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n))
      carrier hslot
  · have heq : j.val + 1 = W.rootPosition.val := by
      omega
    have hrootSlot :=
      (topFreshTailCohortWaveRowEightSelectedRootSlot
        ring C s hn Z anchor W).2
    rw [heq]
    exact topFreshTailFirstBorderOccupiedOfCarrier
      ring C s Z W.queue W.rootPosition W.root hrootSlot

/-- Terminal selected U samples a false-tail digit, with no
same-edge D acceptance. Consumer: J5 row eleven. -/
theorem topFreshTailCohortWaveRowElevenTerminalUnread
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n))
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hterminal : x.val + 1 = topClockSpan n)
    (hunread : (Z.1.1 e).qOut = .U) :
    ∃ nextCarrier : TopFreshTailCarrier (topClockSpan n),
      TopFreshTailPostAnchorActiveHome ring C s
        (topFixedTraceNext ring C Z e) h h nextCarrier ∧
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D (C (certSite s h.val)).d false := by
  obtain ⟨oldX, oldCarrier, hmapOld, hactive, _⟩ :=
    W.currentIssued h hbound
  have hpair : (oldX, oldCarrier) = (x, carrier) :=
    Option.some.inj (hmapOld.symm.trans hmap)
  have hx : oldX = x := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hx, ha] at hactive
  rcases hactive.2.2.2 with ⟨hhome, _⟩ |
    ⟨localSample, hdata, _, _, _, _, _, _⟩
  · have hpositive : h.val ≠ 0 := by
      have hh := hterminal
      rw [hhome] at hh
      have hr := cert_rho_ge_three n hn
      change 3 ≤ topClockSpan n at hr
      omega
    have hgeom :=
      topFreshTailCausalSourcePublicGeometry
        ring C s hn hbad Z W.queue.trace.1 h
    have hxl : (Z.1.1 e).l = false := by
      rw [hsite, hhome]
      exact hgeom.1
    have hyl :
        (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [hsite, hhome]
      exact hgeom.2.1
    have hdigit :
        (Z.1.1 e).d = (C (certSite s h.val)).d := by
      rw [hsite, hhome]
      exact topFreshTailFirstBorderReachedDigit
        ring C Z W.reached (certSite s h.val)
    have hmarker : (Z.1.1 e).beta = false := by
      have hh := hgeom.2.2.1
      rw [if_neg hpositive] at hh
      rw [hsite, hhome]
      exact hh
    obtain ⟨nextCarrier, hnextActive⟩ :=
      topFreshTailPostAnchorActiveHomeUnread
        ring C s hn hbad Z W.queue h x carrier
        hactive hhome e hsite hunread
    have hphysical :=
      topFreshTailFifoUnreadSamples
        ring C Z e hxl hyl hunread
    rw [hdigit, hmarker] at hphysical
    exact ⟨nextCarrier, hnextActive, hphysical⟩
  · rw [hsite] at hunread
    rw [hdata] at hunread
    cases hunread

/-- The blocked OLD terminal port keeps the full selected
carrier and source comparison atom; no source-side scratch
premise is used. Consumer: J5 row twelve. -/
theorem topFreshTailCohortWaveRowTwelveBlockedPortCarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D v tail)
    (hblocked :
      (Z.1.1 (ring.rightNeighbor e)).qIn.isE = false ∨
      (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff = false) :
    ∃ carrier : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n)) =
          some carrier ∧
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) =
            some carrier ∧
      ((topFixedTraceNext ring C Z e).1.2.current
        e).comparison.out.atom =
        (Z.1.2.current e).comparison.out.atom := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hterminalData :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v tail := by
    rw [hsite] at hdata
    exact hdata
  obtain ⟨carrier, _, hslot⟩ :=
    W.selectedHead v tail hterminalData
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1
      (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n))
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hmarker :
      (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    have hm := hgeom.2.2.2
    have heq :
        (topClockSpan n - 1) + 1 = topClockSpan n := by
      omega
    rw [heq] at hm
    simp at hm
    rw [hsite]
    exact hm
  have hghostTrace :
      (topFreshTailGenealogy ring C s Z).trace = Z :=
    W.queue.trace.2
  have hghostSource :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
        .D v tail := by
    rw [hghostTrace]
    exact hdata
  have hghostLeft :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).l =
        false := by
    rw [hghostTrace]
    exact hxl
  have hghostRight :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hghostTrace]
    exact hyl
  have hghostMarker :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).beta = true := by
    rw [hghostTrace]
    exact hmarker
  have hghostBlocked :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).qIn.isE = false ∨
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).qCarry.isOff = false := by
    rw [hghostTrace]
    exact hblocked
  have hslotStep := topFreshTailCausalPortBlocked
    ring C s (topFreshTailGenealogy ring C s Z)
    e (⟨topClockSpan n - 1, htop⟩ :
      Fin (topClockSpan n)) v tail carrier
    hsite hghostLeft hghostRight hghostMarker
    hghostSource hghostBlocked hslot
  have hslotNext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n)) = some carrier := by
    rw [topFreshTailCausalReplayNext]
    exact hslotStep
  have hatom := topFreshTailAuditPhysicalBlockedPortAtom
    ring C Z e v tail hxl hyl hdata hmarker hblocked
  exact ⟨carrier, hslot, hslotNext, hatom⟩

/-- Terminal D(false) is the selected current head at home b,
with its exact active-home and issue-history certificates.
Consumer: J5 row thirteen accepted-false retirement. -/
theorem topFreshTailCohortWaveRowThirteenSelectedHead
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v false) :
    ∃ carrier : TopFreshTailCarrier (topClockSpan n),
      W.currentMap
        (⟨topClockSpan n - 1 -
            ((topClockConcreteExportsAfter
              s Z anchor.time).length % topClockSpan n),
          show topClockSpan n - 1 -
            ((topClockConcreteExportsAfter
              s Z anchor.time).length % topClockSpan n) <
              topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) =
        some ((⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n)), carrier) ∧
      TopFreshTailPostAnchorActiveHome ring C s Z
        (⟨topClockSpan n - 1 -
            ((topClockConcreteExportsAfter
              s Z anchor.time).length % topClockSpan n),
          show topClockSpan n - 1 -
            ((topClockConcreteExportsAfter
              s Z anchor.time).length % topClockSpan n) <
              topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n))
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n))
        carrier ∧
      TopFreshTailIssuedInCohort ring C s Z anchor false
        ((topClockConcreteExportsAfter
          s Z anchor.time).length / topClockSpan n)
        (⟨topClockSpan n - 1 -
            ((topClockConcreteExportsAfter
              s Z anchor.time).length % topClockSpan n),
          show topClockSpan n - 1 -
            ((topClockConcreteExportsAfter
              s Z anchor.time).length % topClockSpan n) <
              topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n))
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n))
        W.currentParent carrier := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hb :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) <
        topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  obtain ⟨carrier, hheadMap, _⟩ :=
    W.selectedHead v false hterminal
  obtain ⟨x, oldCarrier, hmap, hactive, hissued⟩ :=
    W.currentIssued
      (⟨topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n),
        hb⟩ : Fin (topClockSpan n)) (Nat.le_refl _)
  have hpair :
      (x, oldCarrier) =
        ((⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)), carrier) :=
    Option.some.inj (hmap.symm.trans hheadMap)
  have hx : x = (⟨topClockSpan n - 1, htop⟩ :
      Fin (topClockSpan n)) := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hx, ha] at hactive hissued
  exact ⟨carrier, hheadMap, hactive, hissued⟩

/-- At b=0, the accepted D(true) terminal source is the same
full pinned root, and all smaller homes are issued from it.
Consumer: J5 row fourteen parent receipt and reindexing. -/
theorem topFreshTailCohortWaveRowFourteenTerminalParent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v true)
    (hbzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) = 0) :
    W.rootPosition.val = topClockSpan n - 1 ∧
    (topFreshTailGenealogy ring C s Z).slots
      (⟨topClockSpan n - 1,
        show topClockSpan n - 1 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) = some W.root ∧
    (∀ j : Fin (topClockSpan n),
      j.val < topClockSpan n - 1 →
      ∃ carrier : TopFreshTailCarrier (topClockSpan n),
        W.nextMap j = some carrier ∧
        TopFreshTailIssuedInCohort ring C s Z anchor true
          ((topClockConcreteExportsAfter
            s Z anchor.time).length / topClockSpan n + 1)
          j j W.root carrier) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hb :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) <
        topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hzero : 0 < topClockSpan n := by omega
  obtain ⟨carrier, hheadMap, _⟩ :=
    W.selectedHead v true hterminal
  have hindex :
      (⟨topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n),
        hb⟩ : Fin (topClockSpan n)) =
      (⟨0, hzero⟩ : Fin (topClockSpan n)) :=
    Fin.ext hbzero
  have hmapZero :
      W.currentMap (⟨0, hzero⟩ : Fin (topClockSpan n)) =
        some ((⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)), carrier) := by
    rw [← hindex]
    exact hheadMap
  have hpair :
      ((⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n)), carrier) =
        (W.rootPosition, W.root) :=
    Option.some.inj (hmapZero.symm.trans W.rootSelected)
  have hpos :
      W.rootPosition =
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)) :=
    (congrArg Prod.fst hpair).symm
  have hrootSlot :=
    (topFreshTailCohortWaveRowEightSelectedRootSlot
      ring C s hn Z anchor W).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hpos]
    try rfl
  · rw [hpos] at hrootSlot
    exact hrootSlot
  · intro j hj
    have hbelow : j.val < W.rootPosition.val := by
      rw [hpos]
      exact hj
    obtain ⟨carrier, hmap, _, _, hissued⟩ :=
      W.nextIssued j hbelow
    exact ⟨carrier, hmap, hissued⟩

/-- Positive-index incoming responder belongs to the unique
previous source with public nonleader endpoints.
Consumer: J5 row fifteen QI/QC owner reduction. -/
theorem topFreshTailCohortWaveRowFifteenIncomingPredecessor
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (e : Fin n)
    (hneighbor : ring.rightNeighbor e = certSite s j.val) :
    e = certSite s (j.val - 1) ∧
    (Z.1.1 e).l = false ∧
    (Z.1.1 (ring.rightNeighbor e)).l = false := by
  have hprev := topFreshTailCausalIncomingPredecessor
    ring hn s j hpositive e hneighbor
  have hbound : j.val - 1 < topClockSpan n := by
    have hj := j.isLt
    omega
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z W.queue.trace.1
    (⟨j.val - 1, hbound⟩ : Fin (topClockSpan n))
  refine ⟨hprev, ?_, ?_⟩
  · rw [hprev]
    exact hgeom.1
  · rw [hprev]
    exact hgeom.2.1

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The reached, causal, audit, anchor and fresh-origin portions of a
selected cohort wave survive any actual OLD edge. This is the common
frame for the nonreceipt source rows.
Consumer: J5 rows five, six and seven post-anchor reconstruction. -/
theorem topFreshTailCohortWaveRowFiveCommonFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n) :
    topClockReached ring C (topFixedTraceNext ring C Z e) ∧
    TopFreshTailCausalQueue ring C s
      (topFixedTraceNext ring C Z e) ∧
    TopFreshTailAuditSourceDataProvenance ring C s
      (topFixedTraceNext ring C Z e) ∧
    topClockConcreteTailAnchor s
      (topFixedTraceNext ring C Z e) anchor ∧
    (∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a →
      ∃ stamp : Nat, a.origin = .freshBorder stamp) := by
  have hqueueNext :=
    topFreshTailCausalQueueStep
      ring C s hn hbad Z e W.queue
  exact ⟨hqueueNext.trace.1, hqueueNext,
    topFreshTailAuditSourceDataReached
      ring C s hn hbad
      (topFixedTraceNext ring C Z e)
      hqueueNext.trace.1,
    topClockTailAnchorNext
      ring C s Z e anchor W.anchorRecorded,
    topFreshTailFirstBorderFreshFamilyClosedStep
      ring C s hn hbad Z W.queue W.allFresh e⟩

/-- A selected current U retains the *same* historical cohort issue
after the real local sample. At source zero the carrier is rekeyed
and the zero-rekey packet step, not a fresh issue, is appended.
At positive homes the exact carrier persists.
Consumer: J5 row five current-U successor-map certificate. -/
theorem topFreshTailCohortWaveRowFiveCurrentUnread
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (h, carrier))
    (e : Fin n)
    (hsite : e = certSite s h.val)
    (hunread : (Z.1.1 e).qOut = .U) :
    ∃ afterCarrier : TopFreshTailCarrier (topClockSpan n),
      TopFreshTailPostAnchorActiveHome ring C s
        (topFixedTraceNext ring C Z e) h h afterCarrier ∧
      TopFreshTailCohortIssueHistory ring C s
        (Z.2 ++ [e]) h h W.currentParent afterCarrier := by
  obtain ⟨x, oldCarrier, hmapOld, hactive, hissued⟩ :=
    W.currentIssued h hbound
  have hpair : (x, oldCarrier) = (h, carrier) :=
    Option.some.inj (hmapOld.symm.trans hmap)
  have hx : x = h := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hx, ha] at hactive hissued
  obtain ⟨afterCarrier, hactiveNext⟩ :=
    topFreshTailPostAnchorActiveHomeUnread
      ring C s hn hbad Z W.queue
      h h carrier hactive rfl e hsite hunread
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hrunNext :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hrun]
  have hpreSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots h =
          some carrier := by
    rw [hrun]
    exact hactive.2.1
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 h
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hghostU :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
        .U := by
    rw [W.queue.trace.2]
    exact hunread
  have hghostLeft :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).l =
        false := by
    rw [W.queue.trace.2]
    exact hxl
  have hghostRight :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).l = false := by
    rw [W.queue.trace.2]
    exact hyl
  refine ⟨afterCarrier, hactiveNext, ?_⟩
  by_cases hzero : h.val = 0
  · have hbirth :=
      topFreshTailCausalUnreadBorder
        ring C s (topFreshTailGenealogy ring C s Z)
        e h hsite hzero hghostU hghostLeft hghostRight
    rw [W.queue.trace.2] at hbirth
    have hpostSlot :
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots h =
          some {
            origin := .freshBorder (Z.1.2.clock + 1)
            born := Z.1.2.clock + 1 } := by
      rw [topFreshTailCausalReplayNext]
      exact hbirth
    have hafterEq :
        afterCarrier = {
          origin := .freshBorder (Z.1.2.clock + 1)
          born := Z.1.2.clock + 1 } := by
      have hh := hactiveNext.2.1
      rw [hpostSlot] at hh
      exact (Option.some.inj hh).symm
    have hmarker : (Z.1.1 e).beta = true := by
      have hm := hgeom.2.2.1
      rw [if_pos hzero] at hm
      rw [hsite]
      exact hm
    have hsample :=
      topFreshTailFifoUnreadSamples
        ring C Z e hxl hyl hunread
    have hdataRun :
        ((topFixedTraceRun ring C (Z.2 ++ [e])).1.1 e).qOut =
          .D (Z.1.1 e).d true := by
      rw [hrunNext]
      rw [hmarker] at hsample
      exact hsample
    have hpreUnread :
        ((topFixedTraceRun ring C Z.2).1.1 e).qOut =
          .U := by
      rw [hrun]
      exact hunread
    have hpostRun :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (Z.2 ++ [e]))).slots h =
            some {
              origin := .freshBorder (Z.1.2.clock + 1)
              born := Z.1.2.clock + 1 } := by
      rw [hrunNext]
      exact hpostSlot
    rw [hafterEq]
    have hres := topFreshTailCohortIssueHistoryAppendZeroRekey
      ring C s Z.2 h hzero W.currentParent carrier
      hissued.2 e hsite hpreUnread
      (Z.1.1 e).d hdataRun hpreSlot (by rw [hrun]; exact hpostRun)
    rw [hrun] at hres
    exact hres
  · have hpositive : 0 < h.val := by omega
    have hstay :=
      topFreshTailCausalUnreadInterior
        ring C s (topFreshTailGenealogy ring C s Z)
        e h carrier hsite hpositive
        hghostU hghostLeft hghostRight hactive.2.1
    have hpostSlot :
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots h =
            some carrier := by
      rw [topFreshTailCausalReplayNext]
      exact hstay
    have hafterEq : afterCarrier = carrier := by
      have hh := hactiveNext.2.1
      rw [hpostSlot] at hh
      exact (Option.some.inj hh).symm
    have hpostRun :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (Z.2 ++ [e]))).slots h =
            some carrier := by
      rw [hrunNext]
      exact hpostSlot
    rw [hafterEq]
    exact topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 h h W.currentParent carrier
      hissued.2 e hpreSlot hpostRun

/-- Sampling a selected next-cohort U at j behind the root preserves
its actual issue from the full pinned parent, including the
home-zero rekey. The selected successor is occupied by the
next-child/root argument, allowing the behind-source
history theorem to apply.
Consumer: J5 row six next-family successor-map certificate. -/
theorem topFreshTailCohortWaveRowSixNextUnread
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hbehind : j.val < W.rootPosition.val)
    (e : Fin n)
    (hsite : e = certSite s j.val)
    (hunread : (Z.1.1 e).qOut = .U) :
    ∃ afterCarrier : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
          some afterCarrier ∧
      TopFreshTailFirstBorderHomeSlot ring C s
        (topFixedTraceNext ring C Z e) W.root j ∧
      TopFreshTailCohortIssueHistory ring C s
        (Z.2 ++ [e]) j j W.root afterCarrier := by
  obtain ⟨carrier, _, hslot, hhome, hissued⟩ :=
    W.nextIssued j hbehind
  have hfresh := W.allFresh j carrier hslot
  have hnext : j.val + 1 < topClockSpan n := by
    have hk := W.rootPosition.isLt
    omega
  have hoccupied :=
    topFreshTailCohortWaveRowTenSuccessorOccupied
      ring C s hn Z anchor W j hbehind e hsite
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hqueueRun :
      TopFreshTailCausalQueue ring C s
        (topFixedTraceRun ring C Z.2) := by
    rw [hrun]
    exact W.queue
  have hpreSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots j =
          some carrier := by
    rw [hrun]
    exact hslot
  have hoccupiedRun :
      ((topFixedTraceRun ring C Z.2).1.1
        (ring.rightNeighbor e)).qOut ≠ .E := by
    rw [hrun]
    exact hoccupied
  obtain ⟨afterCarrier, hpostSlotRun, hpostHistory⟩ :=
    topFreshTailCohortBehindSourceHistory
      ring C s hn hbad Z.2 W.root carrier j
      e hsite hnext hqueueRun hpreSlot hfresh
      hissued.2 hoccupiedRun
  have hpostSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
          some afterCarrier := by
    rw [topFreshTailFifoRunSnoc, hrun] at hpostSlotRun
    exact hpostSlotRun
  have hhomeNext :=
    topFreshTailFirstBorderHomeSlotUnread
      ring C s hn hbad Z W.root j e
      W.queue hhome hsite hunread
  exact ⟨afterCarrier, hpostSlot, hhomeNext, hpostHistory⟩

/-- A selected positive current D(false) in an OLD empty-successor
interior row transports its exact sampled home and full carrier.
The original issued packet follows the real move edge; its parent
and historical issue are unchanged.
Consumer: J5 row seven current-map move and strict-order frame. -/
theorem topFreshTailCohortWaveRowSevenCurrentFalseMove
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n))
    (hpositive : 0 < h.val)
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n)
    (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hdata :
      (Z.1.1 e).qOut =
        .D (C (certSite s h.val)).d false)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailPostAnchorActiveHome ring C s
      (topFixedTraceNext ring C Z e)
      h (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
      carrier ∧
    TopFreshTailCohortIssueHistory ring C s
      (Z.2 ++ [e]) h
      (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
      W.currentParent carrier ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .E := by
  obtain ⟨oldX, oldCarrier, hmapOld, hactive, hissued⟩ :=
    W.currentIssued h hbound
  have hpair : (oldX, oldCarrier) = (x, carrier) :=
    Option.some.inj (hmapOld.symm.trans hmap)
  have hx : oldX = x := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hx, ha] at hactive hissued
  have hnotZero : h.val ≠ 0 := by omega
  have hdataChoice :
      (Z.1.1 e).qOut =
        .D (C (certSite s h.val)).d
          (if h.val = 0 then true else false) := by
    simpa only [if_neg hnotZero] using hdata
  have hpost :=
    topFreshTailPostAnchorActiveHomeInteriorMove
      ring C s hn hbad Z W.queue
      h x carrier hactive e hsite hnext hdataChoice hempty
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hrunNext :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hrun]
  have hpreSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots x =
          some carrier := by
    rw [hrun]
    exact hactive.2.1
  have hpostSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots
          (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) =
          some carrier := by
    rw [hrunNext]
    exact hpost.1.2.1
  have hdataRun :
      ((topFixedTraceRun ring C Z.2).1.1 e).qOut =
        .D (C (certSite s h.val)).d false := by
    rw [hrun]
    exact hdata
  have hemptyRun :
      ((topFixedTraceRun ring C Z.2).1.1
        (ring.rightNeighbor e)).qOut = .E := by
    rw [hrun]
    exact hempty
  have hissueOld :
      TopFreshTailCohortIssueHistory ring C s Z.2
        h x W.currentParent carrier := hissued.2
  have hissueNext :
      TopFreshTailCohortIssueHistory ring C s
        (Z.2 ++ [e]) h
        (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        W.currentParent carrier := by
    unfold TopFreshTailCohortIssueHistory at hissueOld ⊢
    obtain ⟨before, after, issued, hword, hevent,
      hfollow⟩ := hissueOld
    refine ⟨before, after ++ [e], issued, ?_,
      hevent, ?_⟩
    · rw [hword]
      simp only [List.append_assoc, List.cons_append]
    · apply TopFreshTailCohortPacketFollow.snoc
        hfollow e
        (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        carrier
      unfold TopFreshTailCohortPacketStep
      refine ⟨hpreSlot, hpostSlot,
        Or.inr (Or.inl ?_)⟩
      refine ⟨hnext, rfl, hsite, rfl, ?_⟩
      exact ⟨(C (certSite s h.val)).d, false,
        hdataRun, hemptyRun⟩
  have hsourceEmpty :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut = .E := by
    have hh := hpost.2
    rw [if_neg hnotZero] at hh
    exact hh
  exact ⟨hpost.1, hissueNext, hsourceEmpty⟩

end L3

namespace L3

/-- The selected current root or the already issued next child occupies
source zero. Consumer: the cohort-selected J5 marker-bootstrap row. -/
theorem topFreshTailCohortWaveRowFourZeroOccupied
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor) :
    (Z.1.1 (certSite s 0)).qOut ≠ .E := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  by_cases hkzero : W.rootPosition.val = 0
  · rcases W.rootKind with ⟨_, hunread⟩ |
      ⟨sample, _, _, _, _, hdata, _⟩
    · rw [hunread]
      intro he
      cases he
    · rw [hkzero] at hdata
      rw [hdata]
      intro he
      cases he
  · have hpositive : 0 < W.rootPosition.val := by omega
    obtain ⟨carrier, _, hslot, _, _⟩ :=
      W.nextIssued
        (⟨0, hzero⟩ : Fin (topClockSpan n))
        (by simpa only [Fin.val_mk] using hpositive)
    have hoccupied :=
      topFreshTailFirstBorderOccupiedOfCarrier
        ring C s Z W.queue
        (⟨0, hzero⟩ : Fin (topClockSpan n))
        carrier hslot
    simpa only [Fin.val_mk] using hoccupied

/-- The OLD marked-zero E bootstrap has no predecessor satisfying
the history-selected wave. Consumer: J5 row four. -/
theorem topFreshTailCohortWaveRowFourMarkerBootstrap
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s 0)
    (hsource : (Z.1.1 e).qOut = .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave ring C s hn
      (topFixedTraceNext ring C Z e) anchor) := by
  have hnot :=
    topFreshTailCohortWaveRowFourZeroOccupied
      ring C s hn Z anchor W
  have hfalse : False := hnot (by
    rw [← hsite]
    exact hsource)
  exact False.elim hfalse

/-- A reached nonmarker OLD empty source remains physically empty and
has no causal source carrier after its literal QO service. This is the
local source/coverage premise for J5 row three; it does not by itself
frame the responder or the chronological export audit. -/
theorem topFreshTailCohortWaveRowThreeNonmarkerEmptySource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (e : Fin n)
    (hsite : e = certSite s j.val)
    (hsource : (Z.1.1 e).qOut = .E) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .E ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = none := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 j
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hxb : (Z.1.1 e).beta = false := by
    have hnotzero : j.val ≠ 0 := by omega
    have hb := hgeom.2.2.1
    rw [if_neg hnotzero] at hb
    rw [hsite]
    exact hb
  have hghostXL :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).l =
        false := by
    rw [W.queue.trace.2]
    exact hxl
  have hghostYL :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).l = false := by
    rw [W.queue.trace.2]
    exact hyl
  have hghostXB :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        e).beta = false := by
    rw [W.queue.trace.2]
    exact hxb
  have hghostOut :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        e).qOut = .E := by
    rw [W.queue.trace.2]
    exact hsource
  have hlocal :=
    topFreshTailCausalNonmarkerEmpty
      ring C s (topFreshTailGenealogy ring C s Z)
      e j hsite hghostXL hghostYL hghostXB hghostOut
  have htrace :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).trace =
      topFixedTraceNext ring C Z e := by
    change
      topFixedTraceNext ring C
        (topFreshTailGenealogy ring C s Z).trace e =
      topFixedTraceNext ring C Z e
    rw [W.queue.trace.2]
  constructor
  · rw [← htrace]
    exact hlocal.1
  · rw [topFreshTailCausalReplayNext]
    exact hlocal.2

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A position-local update principle for the Type-valued selected
post-anchor cohort wave. The changed predicates are proof-only:
a row may instantiate them with its source and responder positions.
Unchanged selected entries are transported using actual OLD off-pair
physical, genealogy, and historical packet-follow lemmas. Current
ordering is checked only for pairs incident to a changed home;
coverage is checked only at changed sites. Accepted-terminal rows
additionally provide their authentic parent receipt and new export
records, which cannot follow from a spatial frame.
Consumer: J5 rows five through fifteen and the one-edge wave fold. -/
theorem topFreshTailCohortWaveUpdate
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (newCurrent : Fin (topClockSpan n) →
      Option (Fin (topClockSpan n) ×
        TopFreshTailCarrier (topClockSpan n)))
    (newNext : Fin (topClockSpan n) →
      Option (TopFreshTailCarrier (topClockSpan n)))
    (newParent newRoot : TopFreshTailCarrier (topClockSpan n))
    (newRootPosition : Fin (topClockSpan n))
    (changedSite changedCurrent changedNext :
      Fin (topClockSpan n) → Prop)
    (hsiteAway :
      ∀ j, ¬ changedSite j →
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e)
    (hcurrentOff :
      ∀ h, ¬ changedCurrent h →
        newCurrent h = W.currentMap h)
    (hnextOff :
      ∀ j, ¬ changedNext j →
        newNext j = W.nextMap j)
    (hcurrentAway :
      ∀ h x a, ¬ changedCurrent h →
        W.currentMap h = some (x, a) →
        certSite s x.val ≠ e ∧
        certSite s x.val ≠ ring.rightNeighbor e)
    (hnextAway :
      ∀ j, ¬ changedNext j →
        j.val < newRootPosition.val →
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e)
    (hcurrentEligibleOff :
      ∀ h, ¬ changedCurrent h →
        h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) →
        h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n) ∧
        newParent = W.currentParent)
    (hcurrentAbsentOff :
      ∀ h, ¬ changedCurrent h →
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) < h.val →
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n) < h.val)
    (hnextEligibleOff :
      ∀ j, ¬ changedNext j →
        j.val < newRootPosition.val →
        j.val < W.rootPosition.val ∧ newRoot = W.root)
    (hnextAbsentOff :
      ∀ j, ¬ changedNext j →
        newRootPosition.val ≤ j.val →
        W.rootPosition.val ≤ j.val)
    (hcurrentChanged :
      ∀ h, changedCurrent h →
        h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) →
        ∃ x a, newCurrent h = some (x, a) ∧
          TopFreshTailPostAnchorActiveHome
            ring C s (topFixedTraceNext ring C Z e) h x a ∧
          TopFreshTailCohortIssueHistory ring C s
            (Z.2 ++ [e]) h x newParent a)
    (hcurrentChangedAbsent :
      ∀ h, changedCurrent h →
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) < h.val →
        newCurrent h = none)
    (hnextChanged :
      ∀ j, changedNext j →
        j.val < newRootPosition.val →
        ∃ a, newNext j = some a ∧
          (topFreshTailGenealogy ring C s
            (topFixedTraceNext ring C Z e)).slots j = some a ∧
          TopFreshTailFirstBorderHomeSlot ring C s
            (topFixedTraceNext ring C Z e) newRoot j ∧
          TopFreshTailCohortIssueHistory ring C s
            (Z.2 ++ [e]) j j newRoot a)
    (hnextChangedAbsent :
      ∀ j, changedNext j →
        newRootPosition.val ≤ j.val →
        newNext j = none)
    (hcurrentOrderChanged :
      ∀ h i, changedCurrent h ∨ changedCurrent i →
        h.val < i.val →
        i.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) →
        ∀ x y a b,
          newCurrent h = some (x, a) →
          newCurrent i = some (y, b) →
          x.val < y.val)
    (hcurrentChangedSite :
      ∀ h j a, changedCurrent h →
        newCurrent h = some (j, a) → changedSite j)
    (hcurrentUnchangedSite :
      ∀ j a h, ¬ changedSite j →
        W.currentMap h = some (j, a) →
        ¬ changedCurrent h)
    (hnextUnchangedSite :
      ∀ j, ¬ changedSite j → ¬ changedNext j)
    (hsourceChanged :
      ∀ j a, changedSite j →
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots j = some a →
        (∃ h, newCurrent h = some (j, a) ∧
          newNext j = none) ∨
        (newNext j = some a ∧
          ∀ h b, newCurrent h ≠ some (j, b)))
    (hrootStable :
      ¬ changedCurrent
        (⟨0, show 0 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) →
        newRootPosition = W.rootPosition ∧ newRoot = W.root)
    (hrootChanged :
      changedCurrent
        (⟨0, show 0 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) →
        newCurrent
          (⟨0, show 0 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n)) =
          some (newRootPosition, newRoot))
    (hrootKind :
      (newRootPosition.val = 0 ∧
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s 0)).qOut = .U) ∨
      ∃ sample : DigitSample
          (compileAdvice (ceilLogTwo n)) n,
        DigitRecordedSample
          (topFixedTraceNext ring C Z e).1.2 sample ∧
        sample.id.lane = .comparison ∧
        sample.id.site = certSite s 0 ∧
        sample.tail = true ∧
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s newRootPosition.val)).qOut =
            .D sample.value true ∧
        ((topFixedTraceNext ring C Z e).1.2.current
          (certSite s newRootPosition.val)).comparison.out.atom =
            some (.sampled sample.id))
    (hparentReceipt :
      TopFreshTailCohortHistoricalParent
        ring C s hn (topFixedTraceNext ring C Z e) anchor
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length / topClockSpan n) newParent)
    (hexportOld :
      ∀ (i : Nat)
        (hiOld : i < (topClockConcreteExportsAfter s
          Z anchor.time).length)
        (hiNew : i < (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length),
        topClockConcreteExportAt s
          (topFixedTraceNext ring C Z e) anchor.time
          (⟨i, hiNew⟩ : Fin
            (topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length) =
        topClockConcreteExportAt s Z anchor.time
          (⟨i, hiOld⟩ : Fin
            (topClockConcreteExportsAfter s Z anchor.time).length))
    (hexportAdded :
      ∀ i : Fin (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length,
        (topClockConcreteExportsAfter s
          Z anchor.time).length ≤ i.val →
        ∃ sample : DigitSample
            (compileAdvice (ceilLogTwo n)) n,
          DigitRecordedSample
            (topFixedTraceNext ring C Z e).1.2 sample ∧
          sample.id.lane = .comparison ∧
          sample.id.site =
            certSite s
              (topClockSpan n - 1 -
                (i.val % topClockSpan n)) ∧
          sample.value =
            (C (certSite s
              (topClockSpan n - 1 -
                (i.val % topClockSpan n)))).d ∧
          sample.tail =
            (if i.val % topClockSpan n = topClockSpan n - 1
              then true else false) ∧
          (topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e)
            anchor.time i).operand =
              some (.sampled sample.id) ∧
          (topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e)
            anchor.time i).value = sample.value ∧
          (topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e)
            anchor.time i).tail = sample.tail) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e)
      anchor) := by
  have hr : 3 ≤ topClockSpan n :=
    cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  obtain ⟨hreachNext, hqueueNext, hprovenanceNext,
      hanchorNext, hfreshNext⟩ :=
    topFreshTailCohortWaveRowFiveCommonFrame
      ring C s hn hbad Z anchor W e
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hrunNext :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hrun]
  have hcurrentIssuedNext :
      ∀ h : Fin (topClockSpan n),
        h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) →
        ∃ x a, newCurrent h = some (x, a) ∧
          TopFreshTailPostAnchorActiveHome ring C s
            (topFixedTraceNext ring C Z e) h x a ∧
          TopFreshTailIssuedInCohort ring C s
            (topFixedTraceNext ring C Z e) anchor false
            ((topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length / topClockSpan n)
            h x newParent a := by
    intro h hbound
    by_cases hchanged : changedCurrent h
    · obtain ⟨x, a, hmap, hactive, hhistory⟩ :=
        hcurrentChanged h hchanged hbound
      refine ⟨x, a, hmap, hactive, ?_⟩
      unfold TopFreshTailIssuedInCohort
      refine ⟨rfl, ?_⟩
      change TopFreshTailCohortIssueHistory
        ring C s (Z.2 ++ [e]) h x newParent a
      exact hhistory
    · obtain ⟨holdBound, hparentEq⟩ :=
        hcurrentEligibleOff h hchanged hbound
      obtain ⟨x, a, hmapOld, hactiveOld, hissuedOld⟩ :=
        W.currentIssued h holdBound
      obtain ⟨hsourceAway, htargetAway⟩ :=
        hcurrentAway h x a hchanged hmapOld
      have hactiveNext :=
        topFreshTailPostAnchorActiveHomeAway
          ring C s Z W.queue h x a hactiveOld
          e hsourceAway htargetAway
      have holdSlot :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C Z.2)).slots x =
              some a := by
        rw [hrun]
        exact hactiveOld.2.1
      have hnewSlot :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (Z.2 ++ [e]))).slots x =
              some a := by
        rw [hrunNext]
        exact hactiveNext.2.1
      have hhistoryNext :=
        topFreshTailCohortIssueHistoryAppendStay
          ring C s Z.2 h x W.currentParent a
          hissuedOld.2 e holdSlot hnewSlot
      refine ⟨x, a, ?_, hactiveNext, ?_⟩
      · rw [hcurrentOff h hchanged]
        exact hmapOld
      · unfold TopFreshTailIssuedInCohort
        refine ⟨rfl, ?_⟩
        change TopFreshTailCohortIssueHistory
          ring C s (Z.2 ++ [e]) h x newParent a
        rw [hparentEq]
        exact hhistoryNext
  have hcurrentAbsentNext :
      ∀ h : Fin (topClockSpan n),
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) < h.val →
        newCurrent h = none := by
    intro h houtside
    by_cases hchanged : changedCurrent h
    · exact hcurrentChangedAbsent h hchanged houtside
    · rw [hcurrentOff h hchanged]
      exact W.currentAbsent h
        (hcurrentAbsentOff h hchanged houtside)
  have hcurrentOrderNext :
      ∀ h i : Fin (topClockSpan n),
        h.val < i.val →
        i.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) →
        ∀ x y a b,
          newCurrent h = some (x, a) →
          newCurrent i = some (y, b) →
          x.val < y.val := by
    intro h i hless hbound x y a b hx hy
    by_cases hchangeH : changedCurrent h
    · exact hcurrentOrderChanged h i
        (Or.inl hchangeH) hless hbound
        x y a b hx hy
    · by_cases hchangeI : changedCurrent i
      · exact hcurrentOrderChanged h i
          (Or.inr hchangeI) hless hbound
          x y a b hx hy
      · have holdBound :=
          (hcurrentEligibleOff i hchangeI hbound).1
        have hxOld : W.currentMap h = some (x, a) := by
          rw [hcurrentOff h hchangeH] at hx
          exact hx
        have hyOld : W.currentMap i = some (y, b) := by
          rw [hcurrentOff i hchangeI] at hy
          exact hy
        exact W.currentOrder h i hless holdBound
          x y a b hxOld hyOld
  have hnextIssuedNext :
      ∀ j : Fin (topClockSpan n),
        j.val < newRootPosition.val →
        ∃ a, newNext j = some a ∧
          (topFreshTailGenealogy ring C s
            (topFixedTraceNext ring C Z e)).slots j =
              some a ∧
          TopFreshTailFirstBorderHomeSlot
            ring C s (topFixedTraceNext ring C Z e)
            newRoot j ∧
          TopFreshTailIssuedInCohort ring C s
            (topFixedTraceNext ring C Z e) anchor true
            ((topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length / topClockSpan n + 1)
            j j newRoot a := by
    intro j hbelow
    by_cases hchanged : changedNext j
    · obtain ⟨a, hmap, hslot, hhome, hhistory⟩ :=
        hnextChanged j hchanged hbelow
      refine ⟨a, hmap, hslot, hhome, ?_⟩
      unfold TopFreshTailIssuedInCohort
      refine ⟨rfl, ?_⟩
      change TopFreshTailCohortIssueHistory
        ring C s (Z.2 ++ [e]) j j newRoot a
      exact hhistory
    · obtain ⟨holdBelow, hrootEq⟩ :=
        hnextEligibleOff j hchanged hbelow
      obtain ⟨a, hmapOld, hslotOld, hhomeOld, hissuedOld⟩ :=
        W.nextIssued j holdBelow
      obtain ⟨hsourceAway, htargetAway⟩ :=
        hnextAway j hchanged hbelow
      have hframe :=
        topFreshTailCausalOffPairSlotAgreement
          ring C s Z e W.queue j
          hsourceAway htargetAway
      have hslotNext :
          (topFreshTailGenealogy ring C s
            (topFixedTraceNext ring C Z e)).slots j =
              some a := by
        rw [hframe.2]
        exact hslotOld
      have hhomeNext :=
        topFreshTailFirstBorderHomeSlotAway
          ring C s Z W.root j e W.queue hhomeOld
          hsourceAway htargetAway
      have hslotRunOld :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C Z.2)).slots j =
              some a := by
        rw [hrun]
        exact hslotOld
      have hslotRunNext :
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (Z.2 ++ [e]))).slots j =
              some a := by
        rw [hrunNext]
        exact hslotNext
      have hhistoryNext :=
        topFreshTailCohortIssueHistoryAppendStay
          ring C s Z.2 j j W.root a
          hissuedOld.2 e hslotRunOld hslotRunNext
      refine ⟨a, ?_, hslotNext, ?_, ?_⟩
      · rw [hnextOff j hchanged]
        exact hmapOld
      · rw [hrootEq]
        exact hhomeNext
      · unfold TopFreshTailIssuedInCohort
        refine ⟨rfl, ?_⟩
        change TopFreshTailCohortIssueHistory
          ring C s (Z.2 ++ [e]) j j newRoot a
        rw [hrootEq]
        exact hhistoryNext
  have hnextAbsentNext :
      ∀ j : Fin (topClockSpan n),
        newRootPosition.val ≤ j.val →
        newNext j = none := by
    intro j habove
    by_cases hchanged : changedNext j
    · exact hnextChangedAbsent j hchanged habove
    · rw [hnextOff j hchanged]
      exact W.nextAbsent j
        (hnextAbsentOff j hchanged habove)
  have hrootSelectedNext :
      newCurrent (⟨0, hzero⟩ : Fin (topClockSpan n)) =
        some (newRootPosition, newRoot) := by
    by_cases hchanged :
        changedCurrent (⟨0, hzero⟩ : Fin (topClockSpan n))
    · exact hrootChanged hchanged
    · obtain ⟨hposEq, hrootEq⟩ :=
        hrootStable hchanged
      rw [hcurrentOff _ hchanged, hposEq, hrootEq]
      exact W.rootSelected
  have hsourceCoverageNext :
      ∀ j : Fin (topClockSpan n),
        ∀ a : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots j =
            some a →
        (∃ h, newCurrent h = some (j, a) ∧
          newNext j = none) ∨
        (newNext j = some a ∧
          ∀ h b, newCurrent h ≠ some (j, b)) := by
    intro j a hslotNext
    by_cases hchanged : changedSite j
    · exact hsourceChanged j a hchanged hslotNext
    · obtain ⟨hsourceAway, htargetAway⟩ :=
        hsiteAway j hchanged
      have hframe :=
        topFreshTailCausalOffPairSlotAgreement
          ring C s Z e W.queue j
          hsourceAway htargetAway
      have hslotOld :
          (topFreshTailGenealogy ring C s Z).slots j =
            some a := by
        rw [hframe.2] at hslotNext
        exact hslotNext
      have hnextUnchanged :=
        hnextUnchangedSite j hchanged
      rcases W.sourceCoverage j a hslotOld with
        ⟨h, hmapOld, hnoneOld⟩ |
        ⟨hmapOld, hdisjointOld⟩
      · have hcurrentUnchanged :=
          hcurrentUnchangedSite j a h hchanged hmapOld
        apply Or.inl
        refine ⟨h, ?_, ?_⟩
        · rw [hcurrentOff h hcurrentUnchanged]
          exact hmapOld
        · rw [hnextOff j hnextUnchanged]
          exact hnoneOld
      · apply Or.inr
        refine ⟨?_, ?_⟩
        · rw [hnextOff j hnextUnchanged]
          exact hmapOld
        · intro h b hcurNew
          by_cases hcurChanged : changedCurrent h
          · exact hchanged
              (hcurrentChangedSite h j b hcurChanged hcurNew)
          · rw [hcurrentOff h hcurChanged] at hcurNew
            exact hdisjointOld h b hcurNew
  have hselectedHeadNext :
      ∀ value : Fin (compileAdvice (ceilLogTwo n)).topA,
        ∀ tail : Bool,
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s (topClockSpan n - 1))).qOut =
            .D value tail →
        ∃ a,
          newCurrent
            (⟨topClockSpan n - 1 -
                ((topClockConcreteExportsAfter s
                  (topFixedTraceNext ring C Z e)
                  anchor.time).length % topClockSpan n),
              show topClockSpan n - 1 -
                ((topClockConcreteExportsAfter s
                  (topFixedTraceNext ring C Z e)
                  anchor.time).length % topClockSpan n) <
                  topClockSpan n by omega⟩ :
                Fin (topClockSpan n)) =
            some ((⟨topClockSpan n - 1,
              show topClockSpan n - 1 < topClockSpan n by omega⟩ :
                Fin (topClockSpan n)), a) ∧
          (topFreshTailGenealogy ring C s
            (topFixedTraceNext ring C Z e)).slots
            (⟨topClockSpan n - 1,
              show topClockSpan n - 1 < topClockSpan n by omega⟩ :
                Fin (topClockSpan n)) = some a := by
    intro value tail hdata
    have hnotEmpty :
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s (topClockSpan n - 1))).qOut ≠ .E := by
      intro he
      rw [hdata] at he
      cases he
    obtain ⟨a, hslot⟩ :=
      topFreshTailCausalOccupiedHasCarrier
        ring C s (topFixedTraceNext ring C Z e)
        hqueueNext
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)) hnotEmpty
    rcases hsourceCoverageNext
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)) a hslot with
      ⟨h, hcur, _⟩ | ⟨hnextSome, _⟩
    · have hwithin :
          h.val ≤ topClockSpan n - 1 -
            ((topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length % topClockSpan n) := by
        by_cases hle :
            h.val ≤ topClockSpan n - 1 -
              ((topClockConcreteExportsAfter s
                (topFixedTraceNext ring C Z e)
                anchor.time).length % topClockSpan n)
        · exact hle
        · have hnone := hcurrentAbsentNext h (by omega)
          rw [hnone] at hcur
          cases hcur
      have hlastBound :
          topClockSpan n - 1 -
            ((topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length % topClockSpan n) <
              topClockSpan n := by omega
      obtain ⟨x, b, hmapLast, _, _⟩ :=
        hcurrentIssuedNext
          (⟨topClockSpan n - 1 -
            ((topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length % topClockSpan n),
            hlastBound⟩ : Fin (topClockSpan n))
          (Nat.le_refl _)
      have hhomeEq :
          h.val = topClockSpan n - 1 -
            ((topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length % topClockSpan n) := by
        by_cases hstrict :
            h.val < topClockSpan n - 1 -
              ((topClockConcreteExportsAfter s
                (topFixedTraceNext ring C Z e)
                anchor.time).length % topClockSpan n)
        · have horder :=
            hcurrentOrderNext
              h
              (⟨topClockSpan n - 1 -
                ((topClockConcreteExportsAfter s
                  (topFixedTraceNext ring C Z e)
                  anchor.time).length % topClockSpan n),
                hlastBound⟩ : Fin (topClockSpan n))
              hstrict (Nat.le_refl _)
              (⟨topClockSpan n - 1, htop⟩ :
                Fin (topClockSpan n))
              x a b hcur hmapLast
          have hxBound := x.isLt
          have htopVal : (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n)).val = topClockSpan n - 1 := rfl
          omega
        · omega
      have hhomeFin :
          h =
            (⟨topClockSpan n - 1 -
              ((topClockConcreteExportsAfter s
                (topFixedTraceNext ring C Z e)
                anchor.time).length % topClockSpan n),
              hlastBound⟩ : Fin (topClockSpan n)) :=
        Fin.ext hhomeEq
      rw [hhomeFin] at hcur
      exact ⟨a, hcur, hslot⟩
    · have htopAbove :
          newRootPosition.val ≤ topClockSpan n - 1 := by
        have hk := newRootPosition.isLt
        omega
      have hnone :=
        hnextAbsentNext
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n)) htopAbove
      rw [hnone] at hnextSome
      cases hnextSome
  have hexportRecordsNext :
      ∀ i : Fin (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length,
        ∃ sample : DigitSample
            (compileAdvice (ceilLogTwo n)) n,
          DigitRecordedSample
            (topFixedTraceNext ring C Z e).1.2 sample ∧
          sample.id.lane = .comparison ∧
          sample.id.site =
            certSite s
              (topClockSpan n - 1 -
                (i.val % topClockSpan n)) ∧
          sample.value =
            (C (certSite s
              (topClockSpan n - 1 -
                (i.val % topClockSpan n)))).d ∧
          sample.tail =
            (if i.val % topClockSpan n = topClockSpan n - 1
              then true else false) ∧
          (topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e)
            anchor.time i).operand =
              some (.sampled sample.id) ∧
          (topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e)
            anchor.time i).value = sample.value ∧
          (topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e)
            anchor.time i).tail = sample.tail := by
    intro i
    by_cases hbefore :
        i.val < (topClockConcreteExportsAfter s
          Z anchor.time).length
    · obtain ⟨sample, hrecord, hlane, hsite, hvalue,
        htail, hoperand, hreceiptValue, hreceiptTail⟩ :=
        W.exportRecords
          (⟨i.val, hbefore⟩ : Fin
            (topClockConcreteExportsAfter s Z anchor.time).length)
      refine ⟨sample, ?_, hlane, hsite, hvalue,
        htail, ?_, ?_, ?_⟩
      · exact digitRecordedSampleStep
          ring (piD Z.1.1) Z.1.2 e sample hrecord
      · rw [hexportOld i.val hbefore i.isLt]
        exact hoperand
      · rw [hexportOld i.val hbefore i.isLt]
        exact hreceiptValue
      · rw [hexportOld i.val hbefore i.isLt]
        exact hreceiptTail
    · exact hexportAdded i (by omega)
  exact Nonempty.intro {
    reached := hreachNext
    queue := hqueueNext
    provenance := hprovenanceNext
    anchorRecorded := hanchorNext
    allFresh := hfreshNext
    currentMap := newCurrent
    nextMap := newNext
    currentParent := newParent
    currentParentReceipt := hparentReceipt
    root := newRoot
    rootPosition := newRootPosition
    rootSelected := hrootSelectedNext
    currentIssued := hcurrentIssuedNext
    currentAbsent := hcurrentAbsentNext
    currentOrder := hcurrentOrderNext
    rootKind := hrootKind
    nextIssued := hnextIssuedNext
    nextAbsent := hnextAbsentNext
    sourceCoverage := hsourceCoverageNext
    selectedHead := hselectedHeadNext
    exportRecords := hexportRecordsNext
  }

end L3

namespace L3

open Classical

set_option autoImplicit false

/-- Distinct issued current homes occupy distinct source positions.
Consumer: J5 row-seven changed-current ordering and off-pair frame. -/
theorem topFreshTailCohortWaveCurrentHomeDistinct
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h k : Fin (topClockSpan n)) (hne : h ≠ k)
    (x y : Fin (topClockSpan n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (hmapH : W.currentMap h = some (x, a))
    (hmapK : W.currentMap k = some (y, b)) : x ≠ y := by
  have hboundH :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) := by
    by_cases hc : h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n)
    · exact hc
    · have hz := W.currentAbsent h (by omega)
      rw [hz] at hmapH
      cases hmapH
  have hboundK :
      k.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) := by
    by_cases hc : k.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n)
    · exact hc
    · have hz := W.currentAbsent k (by omega)
      rw [hz] at hmapK
      cases hmapK
  intro hxy
  have heqval : x.val = y.val := congrArg Fin.val hxy
  by_cases hlt : h.val < k.val
  · have hord := W.currentOrder h k hlt hboundK
      x y a b hmapH hmapK
    omega
  · have hneqval : h.val ≠ k.val := by
      intro heq
      exact hne (Fin.ext heq)
    have hklt : k.val < h.val := by omega
    have hord := W.currentOrder k h hklt hboundH
      y x b a hmapK hmapH
    omega

/-- A selected current map entry is genuinely nonempty in the OLD
physical output. This follows directly from ActiveHome's U/D alternative.
Consumer: J5 row-seven empty-successor exclusion. -/
theorem topFreshTailCohortWaveCurrentHomeOccupied
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (k y : Fin (topClockSpan n))
    (b : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap k = some (y, b)) :
    (Z.1.1 (certSite s y.val)).qOut ≠ .E := by
  have hbound :
      k.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) := by
    by_cases hc : k.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n)
    · exact hc
    · have hz := W.currentAbsent k (by omega)
      rw [hz] at hmap
      cases hmap
  obtain ⟨oldY, oldCarrier, hselected, hactive, _⟩ :=
    W.currentIssued k hbound
  have hpair : (oldY, oldCarrier) = (y, b) :=
    Option.some.inj (hselected.symm.trans hmap)
  have hy : oldY = y := congrArg Prod.fst hpair
  have hb : oldCarrier = b := congrArg Prod.snd hpair
  rw [hy, hb] at hactive
  rcases hactive.2.2.2 with ⟨_, hunread⟩ |
      ⟨sample, hdata, _, _, _, _, _, _⟩
  · rw [hunread]
    intro he
    cases he
  · rw [hdata]
    intro he
    cases he

/-- The moved current packet is the only selected current home
incident to either OLD endpoint of its empty-successor row.
Consumer: J5 row-seven hcurrentAway. -/
theorem topFreshTailCohortWaveCurrentAway
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h k : Fin (topClockSpan n)) (hne : h ≠ k)
    (x y : Fin (topClockSpan n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (hmapH : W.currentMap h = some (x, a))
    (hmapK : W.currentMap k = some (y, b))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hempty : (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    certSite s y.val ≠ e ∧
      certSite s y.val ≠ ring.rightNeighbor e := by
  have hdistinct :=
    topFreshTailCohortWaveCurrentHomeDistinct
      ring C s hn Z anchor W h k hne x y a b hmapH hmapK
  constructor
  · intro hmatch
    have hyx : y = x :=
      topFreshTailCausalSourceSiteInjective s hn y x
        (hmatch.trans hsite)
    exact hdistinct hyx.symm
  · intro hmatch
    have hneighbor :
        ring.rightNeighbor e = certSite s (x.val + 1) := by
      rw [hsite]
      exact topFreshTailFirstBorderNeighborSite ring s x.val
    have hypos :
        y = (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
      topFreshTailCausalSourceSiteInjective s hn y
        (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact hmatch)
    have hoccupied :=
      topFreshTailCohortWaveCurrentHomeOccupied
        ring C s hn Z anchor W k y b hmapK
    have hoccSucc :
        (Z.1.1 (certSite s (x.val + 1))).qOut ≠ .E := by
      simpa only [hypos, Fin.val_mk] using hoccupied
    have hemptySucc :
        (Z.1.1 (certSite s (x.val + 1))).qOut = .E := by
      rw [← hneighbor]
      exact hempty
    exact hoccSucc hemptySucc

/-- The selected positive current home is strictly to the
right of the pinned root, by the zero-home ordering.
Consumer: J5 row-seven root and next-map off-pair frames. -/
theorem topFreshTailCohortWaveCurrentRootPrecedes
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n)) (hpositive : 0 < h.val)
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (x : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, a)) :
    W.rootPosition.val < x.val := by
  have hzero : 0 < topClockSpan n := by
    have hr := cert_rho_ge_three n hn
    omega
  exact W.currentOrder (⟨0, hzero⟩ : Fin (topClockSpan n))
    h (by simpa only [Fin.val_mk] using hpositive) hbound
    W.rootPosition x W.root a W.rootSelected hmap

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- On a service not leaving the selected delimiter port, no new
post-anchor comparison export is recorded. Consumer: J5 row-seven
cohort generation, current-range and receipt frames. -/
theorem topFreshTailCohortWaveNonPortExports
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hnotPort : e ≠ certSite s (topClockSpan n - 1)) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hnil :
      topFreshTailPostAnchorNewEntries ring s Z anchor.time e = [] := by
    cases hlocal :
        (digitReceiptLane .comparison
          (topFreshTailPostAnchorCurrentFrame ring Z e).receipt).exported with
    | none =>
        simp [topFreshTailPostAnchorNewEntries, hlocal]
    | some exported =>
        have hservice :
            (digitService (Z.1.2.clock + 1)
              e (ring.rightNeighbor e)
              (piD Z.1.1 e)
              (piD Z.1.1 (ring.rightNeighbor e))
              (Z.1.2.current e)
              (Z.1.2.current (ring.rightNeighbor e))).comparison.exported =
                some exported := by
          change
            (digitService (Z.1.2.clock + 1)
              e (ring.rightNeighbor e)
              (piD Z.1.1 e)
              (piD Z.1.1 (ring.rightNeighbor e))
              (Z.1.2.current e)
              (Z.1.2.current (ring.rightNeighbor e))).comparison.exported =
                some exported at hlocal
          exact hlocal
        have hcomparison :
            (digitLaneReplay .comparison (Z.1.2.clock + 1)
              e (ring.rightNeighbor e)
              (digitLaneView .comparison (piD Z.1.1 e)
                (piD Z.1.1 e).word.beta)
              (digitLaneView .comparison
                (piD Z.1.1 (ring.rightNeighbor e))
                (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
              (Z.1.2.current e).comparison
              (Z.1.2.current (ring.rightNeighbor e)).comparison).exported =
                some exported := hservice
        have hfields := topFreshTailAuditLaneExportFields
          .comparison (Z.1.2.clock + 1)
          e (ring.rightNeighbor e)
          (digitLaneView .comparison (piD Z.1.1 e)
            (piD Z.1.1 e).word.beta)
          (digitLaneView .comparison
            (piD Z.1.1 (ring.rightNeighbor e))
            (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
          (Z.1.2.current e).comparison
          (Z.1.2.current (ring.rightNeighbor e)).comparison
          exported hcomparison
        have hqual :
            ¬ (anchor.time < exported.time ∧
                exported.source = certSite s (topClockSpan n - 1) ∧
                exported.destination = certSite s (topClockSpan n)) := by
          intro hq
          exact hnotPort (hfields.2.2.1.symm.trans hq.2.1)
        simp [topFreshTailPostAnchorNewEntries, hlocal, hqual]
  rw [topFreshTailPostAnchorExportsAfterStep, hnil]
  simp only [List.append_nil]

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A parent receipt is about a previously issued actual port service.
Appending a non-port edge preserves that exact historical witness when
the filtered export list is unchanged.
Consumer: J5 row-seven hparentReceipt. -/
theorem topFreshTailCohortWaveParentReceiptAppend
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (generation : Nat)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hreceipt : TopFreshTailCohortHistoricalParent
      ring C s hn Z anchor generation parent)
    (hexports :
      topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time) :
    TopFreshTailCohortHistoricalParent ring C s hn
      (topFixedTraceNext ring C Z e) anchor generation parent := by
  unfold TopFreshTailCohortHistoricalParent at hreceipt ⊢
  obtain ⟨before, after, exported, hword, hslot,
    hport, htime, htail, hgeneration⟩ := hreceipt
  refine ⟨before, after ++ [e], exported, ?_,
    hslot, hport, htime, htail, ?_⟩
  · change Z.2 ++ [e] =
      before ++ certSite s (topClockSpan n - 1) :: (after ++ [e])
    rw [hword]
    simp only [List.cons_append, List.append_assoc]
  · by_cases hzero : generation = 0
    · rw [if_pos hzero] at hgeneration ⊢
      exact hgeneration
    · rw [if_neg hzero] at hgeneration ⊢
      obtain ⟨i, hindex, hrecord⟩ := hgeneration
      have hiNew :
          i.val < (topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e) anchor.time).length := by
        have hlength := congrArg List.length hexports
        omega
      refine ⟨⟨i.val, hiNew⟩, hindex, ?_⟩
      have hlistGet :
          ∀ {α : Type} (L M : List α) (hLM : L = M)
            (j : Nat) (hjL : j < L.length) (hjM : j < M.length),
            L[j]'hjL = M[j]'hjM := by
        intro α L M hLM j hjL hjM
        cases hLM
        rfl
      have hrecordNext :
          topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e) anchor.time
            (⟨i.val, hiNew⟩ : Fin
              (topClockConcreteExportsAfter s
                (topFixedTraceNext ring C Z e) anchor.time).length) =
          topClockConcreteExportAt s Z anchor.time i := by
        unfold topClockConcreteExportAt
        exact hlistGet _ _ hexports i.val hiNew i.isLt
      exact hrecord.trans hrecordNext.symm


/-- A non-port current false-tail hop retains strict current-home
ordering, including comparisons incident to the moved home.
Consumer: J5 row-seven hcurrentOrderChanged. -/
theorem topFreshTailCohortWaveRowSevenOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (hnext : x.val + 1 < topClockSpan n)
    (e : Fin n) (hsite : e = certSite s x.val)
    (hempty : (Z.1.1 (ring.rightNeighbor e)).qOut = .E)
    (hexports :
      topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time) :
    ∀ u v : Fin (topClockSpan n),
      u.val < v.val →
      v.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n) →
      ∀ (p q : Fin (topClockSpan n))
        (a b : TopFreshTailCarrier (topClockSpan n)),
        (fun t => if t = h then
          some ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier)
        else W.currentMap t) u =
          some (p, a) →
        (fun t => if t = h then
          some ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier)
        else W.currentMap t) v =
          some (q, b) →
        p.val < q.val := by
  intro u v huv hbound p q a b hnewU hnewV
  have holdBound :
      v.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) := by
    simpa only [hexports] using hbound
  by_cases hu : u = h
  · subst u
    have hv : v ≠ h := by
      intro heq
      subst v
      omega
    have hpairU :
        ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier) =
          (p, a) := by
      have hs : some
          ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier) =
          some (p, a) := by
        simpa only [if_pos rfl, ↓reduceIte] using hnewU
      exact Option.some.inj hs
    have hp : p.val = x.val + 1 := by
      exact (congrArg Fin.val ((Prod.mk.inj hpairU).1)).symm
    have hmapV : W.currentMap v = some (q, b) := by
      simpa only [if_neg hv] using hnewV
    have horder := W.currentOrder h v huv holdBound
      x q carrier b hmap hmapV
    have hneq :
        q.val ≠ x.val + 1 := by
      intro heq
      have hoccupied :=
        topFreshTailCohortWaveCurrentHomeOccupied
          ring C s hn Z anchor W v q b hmapV
      have hneighbor :
          ring.rightNeighbor e = certSite s (x.val + 1) := by
        rw [hsite]
        exact topFreshTailFirstBorderNeighborSite ring s x.val
      have hsiteQ : certSite s q.val = ring.rightNeighbor e := by
        rw [heq, hneighbor]
      exact hoccupied (by rw [hsiteQ]; exact hempty)
    omega
  · by_cases hv : v = h
    · subst v
      have hmapU : W.currentMap u = some (p, a) := by
        simpa only [if_neg hu] using hnewU
      have hpairV :
          ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier) =
            (q, b) := by
        have hs : some
            ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier) =
              some (q, b) := by
          simpa only [if_pos rfl, ↓reduceIte] using hnewV
        exact Option.some.inj hs
      have hq : q.val = x.val + 1 := by
        exact (congrArg Fin.val ((Prod.mk.inj hpairV).1)).symm
      have horder := W.currentOrder u h huv holdBound
        p x a carrier hmapU hmap
      omega
    · have hmapU : W.currentMap u = some (p, a) := by
        simpa only [if_neg hu] using hnewU
      have hmapV : W.currentMap v = some (q, b) := by
        simpa only [if_neg hv] using hnewV
      exact W.currentOrder u v huv holdBound
        p q a b hmapU hmapV




/-- The vacated row-seven source is empty and the newly occupied
successor belongs solely to the moving current carrier.
Consumer: hsourceChanged for J5 row seven. -/
theorem topFreshTailCohortWaveRowSevenSourceCoverage
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (hpositive : 0 < h.val)
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hdata : (Z.1.1 e).qOut =
      .D (C (certSite s h.val)).d false)
    (hempty : (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (j.val = x.val ∨ j.val = x.val + 1) →
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a →
      (∃ k, (fun t => if t = h then
          some ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier)
        else W.currentMap t) k =
        some (j, a) ∧ W.nextMap j = none) ∨
      (W.nextMap j = some a ∧
        ∀ k b, (fun t => if t = h then
          some ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier)
        else W.currentMap t) k ≠
          some (j, b)) := by
  have hmove := topFreshTailCohortWaveRowSevenCurrentFalseMove
    ring C s hn hbad Z anchor W h hbound hpositive
    x carrier hmap e hsite hnext hdata hempty
  have hqueue :
      TopFreshTailCausalQueue ring C s
        (topFixedTraceNext ring C Z e) :=
    (topFreshTailCohortWaveRowFiveCommonFrame
      ring C s hn hbad Z anchor W e).2.1
  have hsourceNone :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots x = none := by
    apply (hqueue.slot x).mp
    rw [← hsite]
    exact hmove.2.2
  have hrootBefore := topFreshTailCohortWaveCurrentRootPrecedes
    ring C s hn Z anchor W h hpositive hbound x carrier hmap
  intro j a hj hslot
  rcases hj with hjx | hjsucc
  · have heq : j = x := Fin.ext hjx
    subst j
    rw [hsourceNone] at hslot
    cases hslot
  · have heq :
        j = (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
      Fin.ext (by simpa only [Fin.val_mk] using hjsucc)
    subst j
    have hsame : a = carrier := by
      have hboth : some carrier = some a :=
        hmove.1.2.1.symm.trans hslot
      exact (Option.some.inj hboth).symm
    subst a
    apply Or.inl
    refine ⟨h, ?_, W.nextAbsent
      (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) (by
        simp only [Fin.val_mk]
        omega)⟩
    simp only [if_pos rfl, ↓reduceIte]



/-- The actual positive current false-tail move is a complete
cohort-wave transition. Consumer: J5 row-seven one-edge induction. -/
theorem topFreshTailCohortWaveStepRowSeven
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (hpositive : 0 < h.val)
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hdata : (Z.1.1 e).qOut =
      .D (C (certSite s h.val)).d false)
    (hempty : (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have hs : x =
        (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n)) :=
      topFreshTailCausalSourceSiteInjective s hn x
        (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
        (by rw [← hsite]; exact hp)
    have hv := congrArg Fin.val hs
    simp only [Fin.val_mk] at hv
    omega
  have hexports := topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort
  have hlistGet :
      ∀ {α : Type} (L M : List α) (hLM : L = M)
        (j : Nat) (hjL : j < L.length) (hjM : j < M.length),
        L[j]'hjL = M[j]'hjM := by
    intro α L M hLM j hjL hjM
    cases hLM
    rfl
  have hmove := topFreshTailCohortWaveRowSevenCurrentFalseMove
    ring C s hn hbad Z anchor W h hbound hpositive
    x carrier hmap e hsite hnext hdata hempty
  have hrootBefore := topFreshTailCohortWaveCurrentRootPrecedes
    ring C s hn Z anchor W h hpositive hbound x carrier hmap
  have hneighbor :
      ring.rightNeighbor e = certSite s (x.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s x.val
  have hrootAway :
      certSite s W.rootPosition.val ≠ e ∧
      certSite s W.rootPosition.val ≠ ring.rightNeighbor e := by
    constructor
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn W.rootPosition x (heq.trans hsite)
      have hv := congrArg Fin.val hs
      omega
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn W.rootPosition
        (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      omega
  refine topFreshTailCohortWaveUpdate ring C s hn hbad Z anchor W e
    ((fun t => if t = h then
          some ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier)
        else W.currentMap t))
    W.nextMap W.currentParent W.root W.rootPosition
    (fun j => j.val = x.val ∨ j.val = x.val + 1)
    (fun k => k = h) (fun _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: outside x and x+1 the physical pair is disjoint.
    intro j hj
    constructor
    · intro heq
      have hx := topFreshTailCausalSourceSiteInjective
        s hn j x (heq.trans hsite)
      exact hj (Or.inl (congrArg Fin.val hx))
    · intro heq
      have hx := topFreshTailCausalSourceSiteInjective
        s hn j (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      exact hj (Or.inr (by
        have hv := congrArg Fin.val hx
        simpa only [Fin.val_mk] using hv))
  · -- hcurrentOff: core conditional map retains every other map entry.
    intro k hk
    simp only [if_neg hk]
  · -- hnextOff: the stationary next map is unchanged.
    intro j _
    rfl
  · -- hcurrentAway: distinct current homes and empty destination.
    intro k y a hk hmapK
    have hne : h ≠ k := by
      intro heq
      exact hk heq.symm
    exact topFreshTailCohortWaveCurrentAway
      ring C s hn Z anchor W h k hne
      x y carrier a hmap hmapK e hsite hnext hempty
  · -- hnextAway: next homes precede the root and moved current.
    intro j _ hj
    have hlt : j.val < x.val := by omega
    constructor
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j x (heq.trans hsite)
      have hv := congrArg Fin.val hs
      omega
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      omega
  · -- hcurrentEligibleOff: cohort index unchanged; parent stays.
    intro k _ hnew
    refine ⟨?_, rfl⟩
    simpa only [hexports] using hnew
  · -- hcurrentAbsentOff: same bound on the issued home range.
    intro k _ hnew
    simpa only [hexports] using hnew
  · -- hnextEligibleOff: root and next range are unchanged.
    intro j _ hj
    exact ⟨hj, rfl⟩
  · -- hnextAbsentOff: root position is unchanged.
    intro j _ hj
    exact hj
  · -- hcurrentChanged: actual carrier move and issue history.
    intro k hk _
    subst k
    refine ⟨(⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)),
      carrier, ?_, hmove.1, hmove.2.1⟩
    simp only [if_pos rfl, ↓reduceIte]
  · -- hcurrentChangedAbsent: selected h remains in the issued range.
    intro k hk houtside
    subst k
    have hold : h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n) := by
      simpa only [hexports] using hbound
    omega
  · -- hnextChanged: no changed next entries.
    intro j hj
    cases hj
  · -- hnextChangedAbsent: no changed next entries.
    intro j hj
    cases hj
  · -- hcurrentOrderChanged: the full changed-home order lemma.
    intro u v _ huv hb p q a b hu hv
    exact topFreshTailCohortWaveRowSevenOrder
      ring C s hn Z anchor W h x carrier hmap hnext
      e hsite hempty hexports u v huv hb p q a b hu hv
  · -- hcurrentChangedSite: changed home h lands at x+1.
    intro k j a hk hm
    subst k
    have hp :
        ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier) =
          (j, a) := by
      have hh : some
          ((⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)), carrier) =
            some (j, a) := by
        simpa only [if_pos rfl, ↓reduceIte] using hm
      exact Option.some.inj hh
    have hj : j.val = x.val + 1 := by
      have hv := congrArg Fin.val (Prod.mk.inj hp).1
      simpa only [Fin.val_mk] using hv.symm
    exact Or.inr hj
  · -- hcurrentUnchangedSite: the old changed home is x.
    intro j a k hj hmapK
    intro hk
    subst k
    have hp : (x, carrier) = (j, a) :=
      Option.some.inj (hmap.symm.trans hmapK)
    have hjx : j.val = x.val :=
      congrArg Fin.val ((Prod.mk.inj hp).1.symm)
    exact hj (Or.inl hjx)
  · -- hnextUnchangedSite: changedNext is False.
    intro j _ hj
    cases hj
  · -- hsourceChanged: vacated source none, destination current.
    exact topFreshTailCohortWaveRowSevenSourceCoverage
      ring C s hn hbad Z anchor W h hbound hpositive
      x carrier hmap e hsite hnext hdata hempty
  · -- hrootStable: no root entry changes at positive current h.
    intro _
    exact ⟨rfl, rfl⟩
  · -- hrootChanged: home zero cannot equal positive home h.
    intro hk
    have hv := congrArg Fin.val hk
    simp only [Fin.val_mk] at hv
    omega
  · -- hrootKind: pinned root U/D and sample atom frame off-pair.
    have hframe := topFreshTailCausalOffPairSlotAgreement
      ring C s Z e W.queue W.rootPosition
      hrootAway.1 hrootAway.2
    rcases W.rootKind with ⟨hpos, hunread⟩ |
      ⟨sample, hrecord, hlane, hsampleSite,
        htail, hdataRoot, hatomRoot⟩
    · have hframeZero :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s 0)).qOut =
          (Z.1.1 (certSite s 0)).qOut := by
        simpa only [hpos] using hframe.1
      exact Or.inl ⟨hpos, hframeZero.trans hunread⟩
    · apply Or.inr
      refine ⟨sample, digitRecordedSampleStep
        ring (piD Z.1.1) Z.1.2 e sample hrecord,
        hlane, hsampleSite, htail,
        hframe.1.trans hdataRoot, ?_⟩
      have hatomFrame :
          ((topFixedTraceNext ring C Z e).1.2.current
            (certSite s W.rootPosition.val)).comparison.out.atom =
          (Z.1.2.current
            (certSite s W.rootPosition.val)).comparison.out.atom := by
        change
          ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
            (certSite s W.rootPosition.val)).comparison.out.atom =
          (Z.1.2.current
            (certSite s W.rootPosition.val)).comparison.out.atom
        simp only [digitAuditStep, digitGhostStep,
          if_neg hrootAway.1, if_neg hrootAway.2]
      exact hatomFrame.trans hatomRoot
  · -- hparentReceipt: historical port prefix and same generation.
    have hp := topFreshTailCohortWaveParentReceiptAppend
      ring C s hn Z anchor e
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n)
      W.currentParent W.currentParentReceipt hexports
    simpa only [hexports] using hp
  · -- hexportOld: filtered export list equality gives same records.
    intro i hiOld hiNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ hexports i hiNew hiOld
  · -- hexportAdded: no new Fin index exists if lengths agree.
    intro i hnew
    have hi := i.isLt
    have hlength := congrArg List.length hexports
    omega

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The selected stationary-next U has strictly subterminal
source offset, so its service cannot issue a port receipt.
Consumer: J5 row-six cohort index and parent-receipt frame. -/
theorem topFreshTailCohortWaveRowSixNonPort
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hbehind : j.val < W.rootPosition.val)
    (e : Fin n) (hsite : e = certSite s j.val) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have heq :=
      topFreshTailCausalSourceSiteInjective s hn j
        (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
        (by rw [← hsite]; exact hp)
    have hv := congrArg Fin.val heq
    simp only [Fin.val_mk] at hv
    have hroot := W.rootPosition.isLt
    omega
  exact topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One blocked nonterminal D service keeps every source output.
The selected source is blocked, its responder output is never
overwritten, and all other source sites are outside the pair.
Consumer: cohort-wave stay rows nine and ten. -/
theorem topFreshTailCohortWaveStayOutputs
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (W : TopFreshTailCausalQueue ring C s Z)
    (x : Fin (topClockSpan n))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D value tail)
    (hoccupied : (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) :
    ∀ j : Fin (topClockSpan n),
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
      (Z.1.1 (certSite s j.val)).qOut := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.trace.1 x
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hmarker :
      (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    have hm := hgeom.2.2.2
    rw [if_neg (show x.val + 1 ≠ topClockSpan n by omega)] at hm
    rw [hsite]
    exact hm
  have hleft :=
    topFreshTailFifoOccupiedFrame
      ring C Z e value tail hxl hyl hdata hmarker hoccupied
  have hright :
      ((topFixedTraceNext ring C Z e).1.1
        (ring.rightNeighbor e)).qOut =
      (Z.1.1 (ring.rightNeighbor e)).qOut := by
    have hf := topFreshTailCausalResponderPhysicalOutput
      ring (by omega : 2 ≤ n) C Z e
    cases hy : (Z.1.1 (ring.rightNeighbor e)).qOut with
    | E => exact False.elim (hoccupied hy)
    | U => simpa [hxl, hyl, hy, OutTok.isE] using hf
    | D v t => simpa [hxl, hyl, hy, OutTok.isE] using hf
  have hneighbor :
      ring.rightNeighbor e = certSite s (x.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s x.val
  intro j
  by_cases hjx : j = x
  · subst j
    rw [← hsite, hdata]
    exact hleft
  · by_cases hjy : j.val = x.val + 1
    · have hj : j =
          (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
        Fin.ext hjy
      subst j
      simp only [Fin.val_mk]
      rw [← hneighbor]
      exact hright
    · have hsource : certSite s j.val ≠ e := by
        intro heq
        have hsame := topFreshTailCausalSourceSiteInjective
          s hn j x (heq.trans hsite)
        exact hjx hsame
      have htarget :
          certSite s j.val ≠ ring.rightNeighbor e := by
        intro heq
        have hsame := topFreshTailCausalSourceSiteInjective
          s hn j (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
          (heq.trans hneighbor)
        have hv := congrArg Fin.val hsame
        simp only [Fin.val_mk] at hv
        exact hjy hv
      exact (topFreshTailCausalOffPairSlotAgreement
        ring C s Z e W j hsource htarget).1

/-- Unchanged physical outputs imply unchanged full genealogy
slots on a genuinely queued trace. In particular no new home
can appear at the blocked responder.
Consumer: the whole-map source-coverage clause of stay steps. -/
theorem topFreshTailCohortWaveStaySlots
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (W : TopFreshTailCausalQueue ring C s Z)
    (e : Fin n)
    (houtputs :
      ∀ j : Fin (topClockSpan n),
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut =
        (Z.1.1 (certSite s j.val)).qOut) :
    ∀ j : Fin (topClockSpan n),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
      (topFreshTailGenealogy ring C s Z).slots j := by
  intro j
  rw [topFreshTailCausalReplayNext]
  change topFreshTailGenealogyNextSlot ring C s
    (topFreshTailGenealogy ring C s Z) e j =
    (topFreshTailGenealogy ring C s Z).slots j
  unfold topFreshTailGenealogyNextSlot
  rw [W.trace.2, houtputs j]
  cases ht : (Z.1.1 (certSite s j.val)).qOut with
  | E =>
      have hnone :
          (topFreshTailGenealogy ring C s Z).slots j = none :=
        (W.slot j).mp ht
      simp only [ht, hnone]
  | U => simp only [ht]
  | D value tail => simp only [ht]

/-- The blocked-D source and its already occupied responder
preserve every OLD sampled D atom; the source uses the blocked
row, the responder uses its incoming frame, and other cells
use the physical/audit off-pair frame.
Consumer: stay rootKind and every selected active-home sample. -/
theorem topFreshTailCohortWaveStayAtoms
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (W : TopFreshTailCausalQueue ring C s Z)
    (x : Fin (topClockSpan n))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D value tail)
    (hoccupied : (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) :
    ∀ (j : Fin (topClockSpan n))
      (v : Fin (compileAdvice (ceilLogTwo n)).topA)
      (t : Bool),
      (Z.1.1 (certSite s j.val)).qOut = .D v t →
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.trace.1 x
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hmarker :
      (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    have hm := hgeom.2.2.2
    rw [if_neg (show x.val + 1 ≠ topClockSpan n by omega)] at hm
    rw [hsite]
    exact hm
  have hleft := topFreshTailAuditPhysicalBlockedInteriorAtom
    ring C Z e value tail hxl hyl hdata hmarker hoccupied
  have hneighbor :
      ring.rightNeighbor e = certSite s (x.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s x.val
  intro j v t hjdata
  by_cases hjx : j = x
  · subst j
    rw [← hsite]
    exact hleft
  · by_cases hjy : j.val = x.val + 1
    · have hj : j =
          (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
        Fin.ext hjy
      subst j
      have htarget :
          (Z.1.1 (ring.rightNeighbor e)).qOut = .D v t := by
        simpa only [Fin.val_mk, ← hneighbor] using hjdata
      have hframe :=
        topFreshTailAuditPhysicalResponderDataKeep
          ring (by omega : 2 ≤ n) C Z e v t hxl hyl htarget
      simpa only [Fin.val_mk, ← hneighbor] using hframe.2
    · have hsource : certSite s j.val ≠ e := by
        intro heq
        have hs := topFreshTailCausalSourceSiteInjective
          s hn j x (heq.trans hsite)
        exact hjx hs
      have htarget :
          certSite s j.val ≠ ring.rightNeighbor e := by
        intro heq
        have hs := topFreshTailCausalSourceSiteInjective
          s hn j (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
          (heq.trans hneighbor)
        have hv := congrArg Fin.val hs
        simp only [Fin.val_mk] at hv
        exact hjy hv
      change
        ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
          (certSite s j.val)).comparison.out.atom =
        (Z.1.2.current (certSite s j.val)).comparison.out.atom
      simp only [digitAuditStep, digitGhostStep,
        if_neg hsource, if_neg htarget]

/-- Shared blocked-D stay case, including both source maps, every
selected history, the pinned root sample, historical parent and the
unchanged non-port export list. Consumer: J5 rows nine and ten. -/
theorem topFreshTailCohortWaveStayStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (x : Fin (topClockSpan n))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D value tail)
    (hoccupied : (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have hs : x =
        (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n)) :=
      topFreshTailCausalSourceSiteInjective s hn x
        (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
        (by rw [← hsite]; exact hp)
    have hv := congrArg Fin.val hs
    simp only [Fin.val_mk] at hv
    omega
  have hexports := topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort
  have houtputs := topFreshTailCohortWaveStayOutputs
    ring C s hn hbad Z W.queue x e hsite hnext
    value tail hdata hoccupied
  have hslots := topFreshTailCohortWaveStaySlots
    ring C s Z W.queue e houtputs
  have hatoms := topFreshTailCohortWaveStayAtoms
    ring C s hn hbad Z W.queue x e hsite hnext
    value tail hdata hoccupied
  have hneighbor :
      ring.rightNeighbor e = certSite s (x.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s x.val
  have hsiteAway :
      ∀ j : Fin (topClockSpan n),
        j.val ≠ x.val → j.val ≠ x.val + 1 →
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e := by
    intro j hjx hjy
    constructor
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j x (heq.trans hsite)
      exact hjx (congrArg Fin.val hs)
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
        (heq.trans hneighbor)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      exact hjy hv
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hhistoryStay :
      ∀ home position : Fin (topClockSpan n),
        ∀ parent a : TopFreshTailCarrier (topClockSpan n),
        TopFreshTailCohortIssueHistory
          ring C s Z.2 home position parent a →
        (topFreshTailGenealogy ring C s Z).slots position =
          some a →
        TopFreshTailCohortIssueHistory
          ring C s (Z.2 ++ [e]) home position parent a := by
    intro home position parent a hissued hslot
    have hold :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C Z.2)).slots position =
          some a := by
      rw [hrun]
      exact hslot
    have hnew :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (Z.2 ++ [e]))).slots position =
          some a := by
      rw [topFreshTailFifoRunSnoc, hrun, hslots position]
      exact hslot
    exact topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 home position parent a hissued e hold hnew
  have hactiveStay :
      ∀ home position : Fin (topClockSpan n),
        ∀ a : TopFreshTailCarrier (topClockSpan n),
        TopFreshTailPostAnchorActiveHome ring C s Z
          home position a →
        TopFreshTailPostAnchorActiveHome
          ring C s (topFixedTraceNext ring C Z e)
          home position a := by
    intro home position a hactive
    obtain ⟨hle, hslot, hfresh, hkind⟩ := hactive
    refine ⟨hle, ?_, hfresh, ?_⟩
    · rw [hslots position]
      exact hslot
    · rcases hkind with ⟨hhome, hu⟩ |
        ⟨sample, hd, hs, hl, hsiteSample,
          hv, ht, ha⟩
      · exact Or.inl ⟨hhome, by
          rw [houtputs position]
          exact hu⟩
      · exact Or.inr
          ⟨sample, (houtputs position).trans hd,
            digitRecordedSampleStep
              ring (piD Z.1.1) Z.1.2 e sample hs,
            hl, hsiteSample, hv, ht,
            (hatoms position _ _ hd).trans ha⟩
  have hhomeStay :
      ∀ j : Fin (topClockSpan n),
        TopFreshTailFirstBorderHomeSlot ring C s Z W.root j →
        TopFreshTailFirstBorderHomeSlot
          ring C s (topFixedTraceNext ring C Z e) W.root j := by
    intro j hhome
    unfold TopFreshTailFirstBorderHomeSlot at hhome ⊢
    obtain ⟨a, hslot, hfresh, hparent, hkind⟩ := hhome
    refine ⟨a, ?_, hfresh, hparent, ?_⟩
    · rw [hslots j]
      exact hslot
    · rcases hkind with hu |
        ⟨sample, hd, hs, hl, hsiteSample,
          hv, ht, ha⟩
      · exact Or.inl ((houtputs j).trans hu)
      · exact Or.inr
          ⟨sample, (houtputs j).trans hd,
            digitRecordedSampleStep
              ring (piD Z.1.1) Z.1.2 e sample hs,
            hl, hsiteSample, hv, ht,
            (hatoms j _ _ hd).trans ha⟩
  have hlistGet :
      ∀ {α : Type} (L M : List α) (hLM : L = M)
        (i : Nat) (hiL : i < L.length) (hiM : i < M.length),
        L[i]'hiL = M[i]'hiM := by
    intro α L M hLM i hiL hiM
    cases hLM
    rfl
  refine topFreshTailCohortWaveUpdate ring C s hn hbad Z anchor W e
    W.currentMap W.nextMap W.currentParent W.root W.rootPosition
    (fun j => j.val = x.val ∨ j.val = x.val + 1)
    (fun k => ∃ y a,
      W.currentMap k = some (y, a) ∧
        (y.val = x.val ∨ y.val = x.val + 1))
    (fun j => j.val = x.val ∨ j.val = x.val + 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: the untouched sites lie off both endpoints.
    intro j hj
    exact hsiteAway j (fun h => hj (Or.inl h))
      (fun h => hj (Or.inr h))
  · -- hcurrentOff: current map is identical in a stay row.
    intro k _
    rfl
  · -- hnextOff: next map is identical in a stay row.
    intro j _
    rfl
  · -- hcurrentAway: all current carriers touching the pair are marked changed.
    intro k y a hk hmap
    have hyx : y.val ≠ x.val := by
      intro he
      exact hk ⟨y, a, hmap, Or.inl he⟩
    have hys : y.val ≠ x.val + 1 := by
      intro he
      exact hk ⟨y, a, hmap, Or.inr he⟩
    exact hsiteAway y hyx hys
  · -- hnextAway: both possibly touched next sites are marked changed.
    intro j hj _
    exact hsiteAway j (fun h => hj (Or.inl h))
      (fun h => hj (Or.inr h))
  · -- hcurrentEligibleOff: the port export count and parent are stable.
    intro k _ hb
    exact ⟨by simpa only [hexports] using hb, rfl⟩
  · -- hcurrentAbsentOff: the cohort range is stable.
    intro k _ hb
    simpa only [hexports] using hb
  · -- hnextEligibleOff: the pinned root is stable.
    intro j _ hj
    exact ⟨hj, rfl⟩
  · -- hnextAbsentOff: the pinned root position is stable.
    intro j _ hj
    exact hj
  · -- hcurrentChanged: a touched current source retains active and issued evidence.
    intro k _ hb
    have hbound :
        k.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) := by
      simpa only [hexports] using hb
    obtain ⟨y, a, hm, ha, hi⟩ := W.currentIssued k hbound
    exact ⟨y, a, hm, hactiveStay k y a ha,
      hhistoryStay k y W.currentParent a hi.2 ha.2.1⟩
  · -- hcurrentChangedAbsent: a touched home outside the range is absent.
    intro k _ hb
    exact W.currentAbsent k (by simpa only [hexports] using hb)
  · -- hnextChanged: the same next child keeps its slot, home and issue.
    intro j _ hj
    obtain ⟨a, hm, hs, hh, hi⟩ := W.nextIssued j hj
    exact ⟨a, hm, by rw [hslots j]; exact hs,
      hhomeStay j hh,
      hhistoryStay j j W.root a hi.2 hs⟩
  · -- hnextChangedAbsent: stationary next map is unchanged.
    intro j _ hj
    exact W.nextAbsent j hj
  · -- hcurrentOrderChanged: unchanged current map retains strict order.
    intro u v _ huv hb p q a b hu hv
    exact W.currentOrder u v huv
      (by simpa only [hexports] using hb) p q a b hu hv
  · -- hcurrentChangedSite: a touched current position lies on the pair.
    intro k j a hk hm
    obtain ⟨y, b, hmap, hy⟩ := hk
    have hp : (y, b) = (j, a) :=
      Option.some.inj (hmap.symm.trans hm)
    have hv : y.val = j.val :=
      congrArg Fin.val (Prod.mk.inj hp).1
    rcases hy with hy | hy
    · exact Or.inl (hv.symm.trans hy)
    · exact Or.inr (hv.symm.trans hy)
  · -- hcurrentUnchangedSite: an untouched physical position cannot belong to a changed home.
    intro j a k hj hm hk
    obtain ⟨y, b, hy, hpos⟩ := hk
    have hp : (y, b) = (j, a) :=
      Option.some.inj (hy.symm.trans hm)
    have hv : y.val = j.val :=
      congrArg Fin.val (Prod.mk.inj hp).1
    rcases hpos with hpos | hpos
    · exact hj (Or.inl (hv.symm.trans hpos))
    · exact hj (Or.inr (hv.symm.trans hpos))
  · -- hnextUnchangedSite: an untouched next index is not marked changed.
    intro j hj hc
    exact hj hc
  · -- hsourceChanged: every OLD slot stays owned by the same map entry.
    intro j a _ hs
    have hold :
        (topFreshTailGenealogy ring C s Z).slots j =
          some a := by
      rw [hslots j] at hs
      exact hs
    exact W.sourceCoverage j a hold
  · -- hrootStable: the selected root and its position are unchanged.
    intro _
    exact ⟨rfl, rfl⟩
  · -- hrootChanged: the zero-home entry still selects the same root.
    intro _
    exact W.rootSelected
  · -- hrootKind: the root output and its sampled atom are unchanged.
    rcases W.rootKind with ⟨hp, hu⟩ |
      ⟨sample, hs, hl, hsampleSite, ht, hd, ha⟩
    · apply Or.inl
      refine ⟨hp, ?_⟩
      have hf := houtputs W.rootPosition
      rw [hp] at hf
      exact hf.trans hu
    · apply Or.inr
      exact ⟨sample, digitRecordedSampleStep
          ring (piD Z.1.1) Z.1.2 e sample hs,
        hl, hsampleSite, ht,
        (houtputs W.rootPosition).trans hd,
        (hatoms W.rootPosition sample.value true hd).trans ha⟩
  · -- hparentReceipt: the historical port parent survives.
    have hp := topFreshTailCohortWaveParentReceiptAppend
      ring C s hn Z anchor e
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n) W.currentParent
      W.currentParentReceipt hexports
    simpa only [hexports] using hp
  · -- hexportOld: export list equality transports the dependent lookup.
    intro i hiOld hiNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ hexports i hiNew hiOld
  · -- hexportAdded: no new export index exists in a non-port stay row.
    intro i hnew
    have hi := i.isLt
    have hlength := congrArg List.length hexports
    omega

/-- A blocked issued current carrier is a stay step.
Consumer: J5 row-nine one-edge preservation. -/
theorem topFreshTailCohortWaveStepRowNine
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hdata :
      (Z.1.1 e).qOut =
        .D (C (certSite s h.val)).d
          (if h.val = 0 then true else false))
    (hoccupied :
      (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  exact topFreshTailCohortWaveStayStep
    ring C s hn hbad Z anchor W x e hsite hnext
    (C (certSite s h.val)).d
    (if h.val = 0 then true else false)
    hdata hoccupied

/-- A selected next-home D is blocked by its next child or
the current root, so its maps remain unchanged.
Consumer: J5 row-ten one-edge preservation. -/
theorem topFreshTailCohortWaveStepRowTen
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hbehind : j.val < W.rootPosition.val)
    (e : Fin n) (hsite : e = certSite s j.val)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata :
      (Z.1.1 e).qOut =
        .D value (if j.val = 0 then true else false)) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hnext : j.val + 1 < topClockSpan n := by
    have hk := W.rootPosition.isLt
    omega
  have hoccupied := topFreshTailCohortWaveRowTenSuccessorOccupied
    ring C s hn Z anchor W j hbehind e hsite
  exact topFreshTailCohortWaveStayStep
    ring C s hn hbad Z anchor W j e hsite hnext
    value (if j.val = 0 then true else false)
    hdata hoccupied

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Row fifteen, the occupied incoming-responder D subrow:
the positive responder has a real causal carrier; the unique
predecessor D is blocked by that occupied output, so the
interior shared stay step applies. U read and empty-marker
services are separately classified source rows.
Consumer: J5 incoming-responder stay subcase. -/
theorem topFreshTailCohortWaveStepRowFifteen
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (e : Fin n)
    (hneighbor : ring.rightNeighbor e = certSite s j.val)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D v tail)
    (hslot : ∃ carrier : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots j = some carrier) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  obtain ⟨hprevious, _, _⟩ :=
    topFreshTailCohortWaveRowFifteenIncomingPredecessor
      ring C s hn hbad Z anchor W j hpositive e hneighbor
  have hposition : j.val - 1 < topClockSpan n := by
    have hj := j.isLt
    omega
  have hstep : j.val - 1 + 1 < topClockSpan n := by
    have hj := j.isLt
    omega
  have hselected :
      e = certSite s
        (⟨j.val - 1, hposition⟩ : Fin (topClockSpan n)).val := by
    simp only [Fin.val_mk]
    exact hprevious
  have hoccupied :
      (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E := by
    obtain ⟨carrier, hcarrier⟩ := hslot
    rw [hneighbor]
    exact topFreshTailFirstBorderOccupiedOfCarrier
      ring C s Z W.queue j carrier hcarrier
  exact topFreshTailCohortWaveStayStep
    ring C s hn hbad Z anchor W
    (⟨j.val - 1, hposition⟩ : Fin (topClockSpan n))
    e hselected (by simpa only [Fin.val_mk] using hstep)
    v tail hdata hoccupied

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every selected current home is at or beyond the pinned root.
Consumer: J5 row-five and row-six responder classification. -/
theorem topFreshTailCohortWaveCurrentAtOrAfterRoot
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (k y : Fin (topClockSpan n))
    (b : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap k = some (y, b)) :
    W.rootPosition.val ≤ y.val := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  by_cases hkzero : k.val = 0
  · have hk : k = (⟨0, hzero⟩ : Fin (topClockSpan n)) :=
      Fin.ext hkzero
    rw [hk] at hmap
    have hpair : (W.rootPosition, W.root) = (y, b) :=
      Option.some.inj (W.rootSelected.symm.trans hmap)
    have hy : W.rootPosition = y := (Prod.mk.inj hpair).1
    rw [hy]
    exact Nat.le_refl _
  · have hbound :
        k.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) := by
      by_cases hc : k.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n)
      · exact hc
      · have hnone := W.currentAbsent k (by omega)
        rw [hnone] at hmap
        cases hmap
    have horder :=
      W.currentOrder (⟨0, hzero⟩ : Fin (topClockSpan n)) k
        (by simpa only [Fin.val_mk] using (show 0 < k.val by omega))
        hbound W.rootPosition y W.root b W.rootSelected hmap
    omega

/-- An OLD U initiator cannot overwrite an already occupied
comparison responder's output or causal carrier, even though the
responder is a selected endpoint rather than an off-pair site.
Consumer: J5 row-five/row-six current/next responder frames. -/
theorem topFreshTailCohortWaveUnreadResponderCarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (p j : Fin (topClockSpan n))
    (e : Fin n)
    (hsite : e = certSite s p.val)
    (hunread : (Z.1.1 e).qOut = .U)
    (htarget : ring.rightNeighbor e = certSite s j.val)
    (a : TopFreshTailCarrier (topClockSpan n))
    (hslot :
      (topFreshTailGenealogy ring C s Z).slots j = some a) :
    ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
      (Z.1.1 (certSite s j.val)).qOut ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = some a := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 p
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hylAt : (Z.1.1 (certSite s j.val)).l = false := by
    rw [← htarget]
    exact hyl
  have hphysical :=
    topFreshTailCausalResponderPhysicalOutput
      ring (by omega : 2 ≤ n) C Z e
  have houtput :
      ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut =
        (Z.1.1 (certSite s j.val)).qOut := by
    rw [htarget] at hphysical
    simpa [hxl, hylAt, hunread, OutTok.isD] using hphysical
  have hnonempty :
      (Z.1.1 (certSite s j.val)).qOut ≠ .E := by
    intro he
    have hnone := (W.queue.slot j).mp he
    rw [hslot] at hnone
    cases hnone
  have hnewSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a := by
    rw [topFreshTailCausalReplayNext]
    change topFreshTailGenealogyNextSlot ring C s
      (topFreshTailGenealogy ring C s Z) e j = some a
    cases hold : (Z.1.1 (certSite s j.val)).qOut with
    | E => exact False.elim (hnonempty hold)
    | U =>
        simp [topFreshTailGenealogyNextSlot,
          W.queue.trace.2, houtput, hold, hslot]
    | D value tail =>
        simp [topFreshTailGenealogyNextSlot,
          W.queue.trace.2, houtput, hold, hslot]
  exact ⟨houtput, hnewSlot⟩

/-- A source U preserves a responder D's output comparison atom,
even if the responder's QI/QC scratch is updated.
Consumer: J5 row-five/row-six selected responder histories. -/
theorem topFreshTailCohortWaveUnreadResponderDataAtom
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (p j : Fin (topClockSpan n))
    (e : Fin n)
    (hsite : e = certSite s p.val)
    (htarget : ring.rightNeighbor e = certSite s j.val)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata :
      (Z.1.1 (certSite s j.val)).qOut = .D v tail) :
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s j.val)).qOut = .D v tail ∧
    ((topFixedTraceNext ring C Z e).1.2.current
      (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 p
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hdataAt :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .D v tail := by
    rw [htarget]
    exact hdata
  have hframe :=
    topFreshTailAuditPhysicalResponderDataKeep
      ring (by omega : 2 ≤ n) C Z e v tail
      hxl hyl hdataAt
  constructor
  · rw [htarget] at hframe
    exact hframe.1
  · rw [htarget] at hframe
    exact hframe.2

/-- A source-U service preserves a selected current responder's
active physical home, its recorded comparison atom, and the full
historical issue from the unchanged parent.
Consumer: J5 rows five/six hcurrentChanged on a touched responder. -/
theorem topFreshTailCohortWaveUnreadResponderCurrent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (p : Fin (topClockSpan n))
    (e : Fin n)
    (hsite : e = certSite s p.val)
    (hunread : (Z.1.1 e).qOut = .U)
    (k y : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hbound :
      k.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (hmap : W.currentMap k = some (y, carrier))
    (htarget : ring.rightNeighbor e = certSite s y.val) :
    TopFreshTailPostAnchorActiveHome ring C s
      (topFixedTraceNext ring C Z e) k y carrier ∧
    TopFreshTailCohortIssueHistory ring C s
      (Z.2 ++ [e]) k y W.currentParent carrier := by
  obtain ⟨oldY, oldCarrier, hmapOld, hactiveOld, hissuedOld⟩ :=
    W.currentIssued k hbound
  have hpair : (oldY, oldCarrier) = (y, carrier) :=
    Option.some.inj (hmapOld.symm.trans hmap)
  have hy : oldY = y := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hy, ha] at hactiveOld hissuedOld
  have hframe :=
    topFreshTailCohortWaveUnreadResponderCarrier
      ring C s hn hbad Z anchor W p y e hsite
      hunread htarget carrier hactiveOld.2.1
  have hactiveNew :
      TopFreshTailPostAnchorActiveHome ring C s
        (topFixedTraceNext ring C Z e) k y carrier := by
    refine ⟨hactiveOld.1, hframe.2,
      hactiveOld.2.2.1, ?_⟩
    rcases hactiveOld.2.2.2 with ⟨hhome, hU⟩ |
      ⟨sample, hdata, hrecord, hlane,
        hsampleSite, hsampleValue, hsampleTail, hatom⟩
    · exact Or.inl ⟨hhome, hframe.1.trans hU⟩
    · have hdataFrame :=
        topFreshTailCohortWaveUnreadResponderDataAtom
          ring C s hn hbad Z anchor W p y e hsite
          htarget (C (certSite s k.val)).d
          (if k.val = 0 then true else false) hdata
      exact Or.inr ⟨sample, hdataFrame.1,
        digitRecordedSampleStep
          ring (piD Z.1.1) Z.1.2 e sample hrecord,
        hlane, hsampleSite, hsampleValue, hsampleTail,
        hdataFrame.2.trans hatom⟩
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hslotRun :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots y =
          some carrier := by
    rw [hrun]
    exact hactiveOld.2.1
  have hslotNextRun :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots y =
          some carrier := by
    rw [topFreshTailFifoRunSnoc, hrun]
    exact hframe.2
  exact ⟨hactiveNew,
    topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 k y W.currentParent carrier
      hissuedOld.2 e hslotRun hslotNextRun⟩

/-- On a source-U edge, an occupied stationary-next responder
keeps its full rooted home certificate, including its sample atom.
Consumer: J5 row-six hnextChanged responder arm. -/
theorem topFreshTailCohortWaveUnreadResponderHome
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (root : TopFreshTailCarrier (topClockSpan n))
    (p j : Fin (topClockSpan n))
    (e : Fin n)
    (hsite : e = certSite s p.val)
    (hunread : (Z.1.1 e).qOut = .U)
    (htarget : ring.rightNeighbor e = certSite s j.val)
    (hhome : TopFreshTailFirstBorderHomeSlot
      ring C s Z root j) :
    TopFreshTailFirstBorderHomeSlot
      ring C s (topFixedTraceNext ring C Z e) root j := by
  unfold TopFreshTailFirstBorderHomeSlot at hhome ⊢
  obtain ⟨carrier, hslot, hfresh, hparent, hkind⟩ := hhome
  have hframe :=
    topFreshTailCohortWaveUnreadResponderCarrier
      ring C s hn hbad Z anchor W p j e hsite
      hunread htarget carrier hslot
  refine ⟨carrier, hframe.2, hfresh, hparent, ?_⟩
  rcases hkind with hU |
    ⟨sample, hdata, hrecord, hlane,
      hsampleSite, hvalue, htail, hatom⟩
  · exact Or.inl (hframe.1.trans hU)
  · have hdataFrame :=
      topFreshTailCohortWaveUnreadResponderDataAtom
        ring C s hn hbad Z anchor W p j e hsite
        htarget (C (certSite s j.val)).d
        (if j.val = 0 then true else false) hdata
    exact Or.inr ⟨sample, hdataFrame.1,
      digitRecordedSampleStep
        ring (piD Z.1.1) Z.1.2 e sample hrecord,
      hlane, hsampleSite, hvalue, htail,
      hdataFrame.2.trans hatom⟩

/-- A stationary next-cohort responder of a U service keeps
the same carrier, rooted home certificate, and issue history.
Consumer: J5 row-six hnextChanged for the touched successor. -/
theorem topFreshTailCohortWaveUnreadResponderNext
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (p j : Fin (topClockSpan n))
    (hbehind : j.val < W.rootPosition.val)
    (e : Fin n)
    (hsite : e = certSite s p.val)
    (hunread : (Z.1.1 e).qOut = .U)
    (htarget : ring.rightNeighbor e = certSite s j.val) :
    ∃ a : TopFreshTailCarrier (topClockSpan n),
      W.nextMap j = some a ∧
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a ∧
      TopFreshTailFirstBorderHomeSlot ring C s
        (topFixedTraceNext ring C Z e) W.root j ∧
      TopFreshTailCohortIssueHistory ring C s
        (Z.2 ++ [e]) j j W.root a := by
  obtain ⟨carrier, hmap, hslot, hhome, hissued⟩ :=
    W.nextIssued j hbehind
  have hframe :=
    topFreshTailCohortWaveUnreadResponderCarrier
      ring C s hn hbad Z anchor W p j e hsite
      hunread htarget carrier hslot
  have hhomeNext :=
    topFreshTailCohortWaveUnreadResponderHome
      ring C s hn hbad Z anchor W W.root
      p j e hsite hunread htarget hhome
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hslotRun :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots j =
          some carrier := by
    rw [hrun]
    exact hslot
  have hslotNextRun :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots j =
          some carrier := by
    rw [topFreshTailFifoRunSnoc, hrun]
    exact hframe.2
  exact ⟨carrier, hmap, hframe.2, hhomeNext,
    topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 j j W.root carrier
      hissued.2 e hslotRun hslotNextRun⟩


/-- A selected next-family U read preserves the entire chosen cohort
wave, including an already occupied responder belonging to either
the pinned current root or the stationary next family.
Consumer: J5 row-six arm of one-edge wave preservation. -/
theorem topFreshTailCohortWaveStepRowSix
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hbehind : j.val < W.rootPosition.val)
    (e : Fin n) (hsite : e = certSite s j.val)
    (hunread : (Z.1.1 e).qOut = .U) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hnext : j.val + 1 < topClockSpan n := by
    have hp := W.rootPosition.isLt
    omega
  have hneighbor :
      ring.rightNeighbor e = certSite s (j.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s j.val
  have hexports := topFreshTailCohortWaveRowSixNonPort
    ring C s hn Z anchor W j hbehind e hsite
  obtain ⟨afterCarrier, hslotAfter, hhomeAfter, hhistoryAfter⟩ :=
    topFreshTailCohortWaveRowSixNextUnread
      ring C s hn hbad Z anchor W j hbehind e hsite hunread
  have hlistGet :
      ∀ {α : Type} (L M : List α) (hLM : L = M)
        (q : Nat) (hqL : q < L.length) (hqM : q < M.length),
        L[q]'hqL = M[q]'hqM := by
    intro α L M hLM q hqL hqM
    cases hLM
    rfl
  refine topFreshTailCohortWaveUpdate
    ring C s hn hbad Z anchor W e
    W.currentMap
    (fun t => if t = j then some afterCarrier else W.nextMap t)
    W.currentParent W.root W.rootPosition
    (fun t => t.val = j.val ∨ t.val = j.val + 1)
    (fun k => ∃ y a, W.currentMap k = some (y, a) ∧
      y.val = j.val + 1)
    (fun t => t = j ∨ t.val = j.val + 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: source and responder are precisely j and j+1.
    intro t ht
    constructor
    · intro heq
      have hpos := topFreshTailCausalSourceSiteInjective
        s hn t j (heq.trans hsite)
      exact ht (Or.inl (congrArg Fin.val hpos))
    · intro heq
      have hpos := topFreshTailCausalSourceSiteInjective
        s hn t (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      exact ht (Or.inr (by
        have hv := congrArg Fin.val hpos
        simpa only [Fin.val_mk] using hv))
  · -- hcurrentOff: no current map entry changes in row six.
    intro k _
    rfl
  · -- hnextOff: the only modified next entry is at j.
    intro t ht
    have htj : t ≠ j := by
      intro heq
      exact ht (Or.inl heq)
    simp only [if_neg htj]
  · -- hcurrentAway: current homes start at the root, and any
    -- responder owner is explicitly marked changed.
    intro k y a hk hmap
    have hrootBound :=
      topFreshTailCohortWaveCurrentAtOrAfterRoot
        ring C s hn Z anchor W k y a hmap
    constructor
    · intro heq
      have heqj := topFreshTailCausalSourceSiteInjective
        s hn y j (heq.trans hsite)
      have hv := congrArg Fin.val heqj
      omega
    · intro heq
      have hy := topFreshTailCausalSourceSiteInjective
        s hn y (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      have hv := congrArg Fin.val hy
      exact hk ⟨y, a, hmap, by simpa only [Fin.val_mk] using hv⟩
  · -- hnextAway: every unchanged stationary site is off both endpoints.
    intro t ht _
    have htj : t ≠ j := by
      intro hh
      exact ht (Or.inl hh)
    have htSuc : t.val ≠ j.val + 1 := by
      intro hh
      exact ht (Or.inr hh)
    constructor
    · intro heq
      exact htj (topFreshTailCausalSourceSiteInjective
        s hn t j (heq.trans hsite))
    · intro heq
      have hh := topFreshTailCausalSourceSiteInjective
        s hn t (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      exact htSuc (by
        have hv := congrArg Fin.val hh
        simpa only [Fin.val_mk] using hv)
  · -- hcurrentEligibleOff: non-port export equality and fixed parent.
    intro k _ hb
    refine ⟨?_, rfl⟩
    simpa only [hexports] using hb
  · -- hcurrentAbsentOff: no change to the issued current range.
    intro k _ hb
    simpa only [hexports] using hb
  · -- hnextEligibleOff: pinned root and its next boundary are unchanged.
    intro t _ ht
    exact ⟨ht, rfl⟩
  · -- hnextAbsentOff: pinned root position is unchanged.
    intro t _ ht
    exact ht
  · -- hcurrentChanged: the touched current responder keeps its
    -- active home and the same issued packet/history.
    intro k hk hb
    obtain ⟨y, a, hmap, hy⟩ := hk
    have hbound : k.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) := by
      simpa only [hexports] using hb
    have htarget : ring.rightNeighbor e = certSite s y.val := by
      rw [hneighbor, hy]
    have hnew :=
      topFreshTailCohortWaveUnreadResponderCurrent
        ring C s hn hbad Z anchor W j e hsite hunread
        k y a hbound hmap htarget
    exact ⟨y, a, hmap, hnew.1, hnew.2⟩
  · -- hcurrentChangedAbsent: a marked responder actually has an old
    -- current-map entry, so it cannot lie above the issued range.
    intro k hk hb
    obtain ⟨y, a, hmap, _⟩ := hk
    have hbOld :
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) < k.val := by
      simpa only [hexports] using hb
    have hnone := W.currentAbsent k hbOld
    rw [hnone] at hmap
    cases hmap
  · -- hnextChanged: j is the locally sampled child; a touched j+1
    -- below the root keeps its existing next issue.
    intro t ht hbelow
    rcases ht with htj | htSuc
    · subst t
      exact ⟨afterCarrier, by simp only [if_pos rfl, ↓reduceIte],
        hslotAfter, hhomeAfter, hhistoryAfter⟩
    · have hpos :
          t = (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
        Fin.ext (by simpa only [Fin.val_mk] using htSuc)
      have htarget : ring.rightNeighbor e = certSite s t.val := by
        rw [hneighbor, htSuc]
      obtain ⟨a, hmap, hslot, hhome, hhistory⟩ :=
        topFreshTailCohortWaveUnreadResponderNext
          ring C s hn hbad Z anchor W j t
          hbelow e hsite hunread htarget
      have hneq : t ≠ j := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      exact ⟨a, by simpa only [if_neg hneq] using hmap,
        hslot, hhome, hhistory⟩
  · -- hnextChangedAbsent: j is below the root, while any marked
    -- successor at or above the root was already absent.
    intro t ht habove
    rcases ht with htj | htSuc
    · subst t
      omega
    · have hneq : t ≠ j := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      simpa only [if_neg hneq] using W.nextAbsent t habove
  · -- hcurrentOrderChanged: the current map and issued range agree
    -- exactly with the previous wave.
    intro u v _ huv hb x y a b hx hy
    have hbOld :
        v.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) := by
      simpa only [hexports] using hb
    exact W.currentOrder u v huv hbOld x y a b hx hy
  · -- hcurrentChangedSite: only the physical responder j+1
    -- can mark an existing current map entry as changed.
    intro k t a hk hmap
    obtain ⟨y, b, hmapOld, hy⟩ := hk
    have hp : (y, b) = (t, a) :=
      Option.some.inj (hmapOld.symm.trans hmap)
    have ht : t.val = j.val + 1 := by
      have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
      omega
    exact Or.inr ht
  · -- hcurrentUnchangedSite: changed-current only owns j+1.
    intro t a k ht hmap
    intro hk
    obtain ⟨y, b, hmapOld, hy⟩ := hk
    have hp : (t, a) = (y, b) :=
      Option.some.inj (hmap.symm.trans hmapOld)
    have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
    exact ht (Or.inr (by omega))
  · -- hnextUnchangedSite: changed-next is contained in
    -- the two marked physical source sites.
    intro t ht hchanged
    rcases hchanged with heq | hsuc
    · exact ht (Or.inl (by rw [heq]))
    · exact ht (Or.inr hsuc)
  · -- hsourceChanged: the newly sampled next child covers j;
    -- the occupied responder is framed and remains in its old
    -- current or next family.
    intro t a ht hslot
    rcases ht with htj | htSucc
    · have heq : t = j := Fin.ext htj
      subst t
      have ha : a = afterCarrier := by
        have both : some afterCarrier = some a :=
          hslotAfter.symm.trans hslot
        exact (Option.some.inj both).symm
      subst a
      apply Or.inr
      refine ⟨by simp only [if_pos rfl, ↓reduceIte], ?_⟩
      intro k b hmap
      have hrootBound :=
        topFreshTailCohortWaveCurrentAtOrAfterRoot
          ring C s hn Z anchor W k j b hmap
      omega
    · have htPos :
          t = (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
        Fin.ext (by simpa only [Fin.val_mk] using htSucc)
      have htarg : ring.rightNeighbor e = certSite s t.val := by
        rw [hneighbor, htSucc]
      have hocc :=
        topFreshTailCohortWaveRowTenSuccessorOccupied
          ring C s hn Z anchor W j hbehind e hsite
      have hoccSite :
          (Z.1.1 (certSite s t.val)).qOut ≠ .E := by
        rw [← htarg]
        exact hocc
      obtain ⟨oldCarrier, hslotOld⟩ :=
        topFreshTailCausalOccupiedHasCarrier
          ring C s Z W.queue t hoccSite
      have hframe :=
        topFreshTailCohortWaveUnreadResponderCarrier
          ring C s hn hbad Z anchor W j t e
          hsite hunread htarg oldCarrier hslotOld
      have ha : a = oldCarrier := by
        have both : some oldCarrier = some a :=
          hframe.2.symm.trans hslot
        exact (Option.some.inj both).symm
      subst a
      have hneq : t ≠ j := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      rcases W.sourceCoverage t oldCarrier hslotOld with
        ⟨k, hcurrent, hnextNone⟩ |
        ⟨hnextSome, hdisjoint⟩
      · exact Or.inl ⟨k, hcurrent,
          by simpa only [if_neg hneq] using hnextNone⟩
      · exact Or.inr
          ⟨by simpa only [if_neg hneq] using hnextSome,
           hdisjoint⟩
  · -- hrootStable: both the root carrier and position are unchanged.
    intro _
    exact ⟨rfl, rfl⟩
  · -- hrootChanged: when zero's map is a marked responder,
    -- its unchanged map entry is precisely the old selected root.
    intro _
    exact W.rootSelected
  · -- hrootKind: root is a D(true), either an occupied responder
    -- or off the U source pair; both its output and sample atom persist.
    have hrootPos : 0 < W.rootPosition.val := by omega
    rcases W.rootKind with ⟨hz, _⟩ |
      ⟨sample, hrecord, hlane, hsampleSite, htail,
        hdata, hatom⟩
    · omega
    · have hrootFrame :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s W.rootPosition.val)).qOut =
            (Z.1.1 (certSite s W.rootPosition.val)).qOut ∧
          ((topFixedTraceNext ring C Z e).1.2.current
            (certSite s W.rootPosition.val)).comparison.out.atom =
            (Z.1.2.current
              (certSite s W.rootPosition.val)).comparison.out.atom := by
        by_cases hrootSucc : W.rootPosition.val = j.val + 1
        · have htarget :
              ring.rightNeighbor e =
                certSite s W.rootPosition.val := by
            rw [hneighbor, hrootSucc]
          have hdataFrame :=
            topFreshTailCohortWaveUnreadResponderDataAtom
              ring C s hn hbad Z anchor W j W.rootPosition
              e hsite htarget sample.value true hdata
          exact ⟨hdataFrame.1.trans hdata.symm,
            hdataFrame.2⟩
        · have hrootAway :
              certSite s W.rootPosition.val ≠ e ∧
              certSite s W.rootPosition.val ≠
                ring.rightNeighbor e := by
            constructor
            · intro he
              have hp := topFreshTailCausalSourceSiteInjective
                s hn W.rootPosition j (he.trans hsite)
              have hv := congrArg Fin.val hp
              omega
            · intro he
              have hp := topFreshTailCausalSourceSiteInjective
                s hn W.rootPosition
                (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n))
                (by rw [← hneighbor]; exact he)
              have hv := congrArg Fin.val hp
              simp only [Fin.val_mk] at hv
              exact hrootSucc (by omega)
          have hframe :=
            topFreshTailCausalOffPairSlotAgreement
              ring C s Z e W.queue W.rootPosition
              hrootAway.1 hrootAway.2
          have hatomFrame :
              ((topFixedTraceNext ring C Z e).1.2.current
                (certSite s W.rootPosition.val)).comparison.out.atom =
              (Z.1.2.current
                (certSite s W.rootPosition.val)).comparison.out.atom := by
            change
              ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
                (certSite s W.rootPosition.val)).comparison.out.atom =
              (Z.1.2.current
                (certSite s W.rootPosition.val)).comparison.out.atom
            simp only [digitAuditStep, digitGhostStep,
              if_neg hrootAway.1, if_neg hrootAway.2]
          exact ⟨hframe.1, hatomFrame⟩
      exact Or.inr ⟨sample,
        digitRecordedSampleStep
          ring (piD Z.1.1) Z.1.2 e sample hrecord,
        hlane, hsampleSite, htail,
        hrootFrame.1.trans hdata,
        hrootFrame.2.trans hatom⟩
  · -- hparentReceipt: identical export list preserves historical parent.
    have hp := topFreshTailCohortWaveParentReceiptAppend
      ring C s hn Z anchor e
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n)
      W.currentParent W.currentParentReceipt hexports
    simpa only [hexports] using hp
  · -- hexportOld: proof-irrelevant Fin positions via List.get.
    intro q hOld hNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ hexports q hNew hOld
  · -- hexportAdded: zero new export indices.
    intro q hAdded
    have hq := q.isLt
    have hlength := congrArg List.length hexports
    omega


/-- Source U leaves the responder's physical output unchanged,
whether occupied or empty; QI/QC changes do not supply a
second comparison output. Consumer: J5 row-five coverage at
the touched successor. -/
theorem topFreshTailCohortWaveUnreadResponderOutput
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (p : Fin (topClockSpan n))
    (e : Fin n) (hsite : e = certSite s p.val)
    (hunread : (Z.1.1 e).qOut = .U) :
    ((topFixedTraceNext ring C Z e).1.1
      (ring.rightNeighbor e)).qOut =
    (Z.1.1 (ring.rightNeighbor e)).qOut := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 p
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hphysical :=
    topFreshTailCausalResponderPhysicalOutput
      ring (by omega : 2 ≤ n) C Z e
  simpa [hxl, hyl, hunread, OutTok.isD] using hphysical

/-- Sampling a chosen current U changes its carrier but not its
physical position; hence the complete current-map ordering remains
strict. Consumer: J5 row-five hcurrentOrderChanged. -/
theorem topFreshTailCohortWaveRowFiveOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (carrier afterCarrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (h, carrier))
    (e : Fin n)
    (hexports :
      topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time) :
    ∀ u v : Fin (topClockSpan n),
      u.val < v.val →
      v.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n) →
      ∀ x y a b,
        (fun k => if k = h then some (h, afterCarrier)
          else W.currentMap k) u = some (x, a) →
        (fun k => if k = h then some (h, afterCarrier)
          else W.currentMap k) v = some (y, b) →
        x.val < y.val := by
  intro u v huv hb x y a b hu hv
  have holdBound :
      v.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) := by
    simpa only [hexports] using hb
  have huOld : ∃ oldCarrier,
      W.currentMap u = some (x, oldCarrier) := by
    by_cases heq : u = h
    · subst u
      have hpair : (h, afterCarrier) = (x, a) := by
        have hs : some (h, afterCarrier) = some (x, a) := by
          simpa only [if_pos rfl, ↓reduceIte] using hu
        exact Option.some.inj hs
      have hx : x = h := (Prod.mk.inj hpair).1.symm
      exact ⟨carrier, by rw [hx]; exact hmap⟩
    · exact ⟨a, by simpa only [if_neg heq] using hu⟩
  have hvOld : ∃ oldCarrier,
      W.currentMap v = some (y, oldCarrier) := by
    by_cases heq : v = h
    · subst v
      have hpair : (h, afterCarrier) = (y, b) := by
        have hs : some (h, afterCarrier) = some (y, b) := by
          simpa only [if_pos rfl, ↓reduceIte] using hv
        exact Option.some.inj hs
      have hy : y = h := (Prod.mk.inj hpair).1.symm
      exact ⟨carrier, by rw [hy]; exact hmap⟩
    · exact ⟨b, by simpa only [if_neg heq] using hv⟩
  obtain ⟨aOld, hmapU⟩ := huOld
  obtain ⟨bOld, hmapV⟩ := hvOld
  exact W.currentOrder u v huv holdBound
    x y aOld bOld hmapU hmapV


end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A beta-marked source D cannot generate an audit export when
the destination input is nonempty or the destination carry is live.
This is read directly from the literal digitLaneReplay receipt row.
Consumer: J5 blocked-port export-list and historical-parent frame. -/
theorem topFreshTailCohortWaveBlockedPortExports
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D v tail)
    (hblocked :
      (Z.1.1 (ring.rightNeighbor e)).qIn.isE = false ∨
      (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff = false) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z W.queue.trace.1
    (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    have hm := hgeom.2.2.2
    rw [show topClockSpan n - 1 + 1 = topClockSpan n by omega] at hm
    simp only [if_pos rfl] at hm
    rw [hsite]
    exact hm
  have hblockedView :
      (digitLaneView .comparison
        (piD Z.1.1 (ring.rightNeighbor e))
        (piD Z.1.1 (ring.rightNeighbor e)).word.beta).input.isE =
          false ∨
      (digitLaneView .comparison
        (piD Z.1.1 (ring.rightNeighbor e))
        (piD Z.1.1 (ring.rightNeighbor e)).word.beta).carryLive =
          true := by
    rcases hblocked with hinput | hcarry
    · exact Or.inl hinput
    · apply Or.inr
      cases hc : (Z.1.1 (ring.rightNeighbor e)).qCarry with
      | OFF =>
          rw [hc] at hcarry
          cases hcarry
      | L bit err =>
          change (Z.1.1 (ring.rightNeighbor e)).qCarry.isL = true
          rw [hc]
          rfl
  have hblockedReplay :
      ∀ (x y : DigitLaneView (compileAdvice (ceilLogTwo n)))
        (gx gy : DigitLaneGhost (compileAdvice (ceilLogTwo n)) n),
        x.leader = false → y.leader = false →
        x.out = .D v tail → y.marker = true →
        (y.input.isE = false ∨ y.carryLive = true) →
        (digitLaneReplay .comparison (Z.1.2.clock + 1)
          e (ring.rightNeighbor e) x y gx gy).exported = none := by
    intro x y gx gy hx hy hxo hmarker hblock
    rcases hblock with hinput | hcarry
    · cases hiy : y.input with
      | E =>
          simp [hiy, InTok.isE] at hinput
      | P value bit =>
          simp [digitLaneReplay, hx, hy, hxo, hmarker, hiy,
            OutTok.isD, OutTok.isE, InTok.isE]
      | S value bit =>
          simp [digitLaneReplay, hx, hy, hxo, hmarker, hiy,
            OutTok.isD, OutTok.isE, InTok.isE]
      | X =>
          simp [digitLaneReplay, hx, hy, hxo, hmarker, hiy,
            OutTok.isD, OutTok.isE, InTok.isE]
    · cases hc : y.carryLive with
      | false =>
          rw [hc] at hcarry
          cases hcarry
      | true =>
          simp [digitLaneReplay, hx, hy, hxo, hmarker, hc,
            OutTok.isD, OutTok.isE, InTok.isE]
  have hlocal :
      (digitReceiptLane .comparison
        (topFreshTailPostAnchorCurrentFrame ring Z e).receipt).exported =
        none := by
    change
      (digitLaneReplay .comparison (Z.1.2.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison
          (piD Z.1.1 e) (piD Z.1.1 e).word.beta)
        (digitLaneView .comparison
          (piD Z.1.1 (ring.rightNeighbor e))
          (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported = none
    exact hblockedReplay _ _ _ _
      (by change (Z.1.1 e).l = false; exact hxl)
      (by change (Z.1.1 (ring.rightNeighbor e)).l = false; exact hyl)
      (by change (Z.1.1 e).qOut = .D v tail; exact hdata)
      (by change (Z.1.1 (ring.rightNeighbor e)).beta = true; exact hyb)
      hblockedView
  have hnil :
      topFreshTailPostAnchorNewEntries
        ring s Z anchor.time e = [] := by
    simp [topFreshTailPostAnchorNewEntries, hlocal]
  rw [topFreshTailPostAnchorExportsAfterStep, hnil]
  simp only [List.append_nil]

/-- Blocked-port full physical, genealogy and sample-atom frame.
Consumer: row-twelve whole-map stay step. -/
theorem topFreshTailCohortWaveBlockedPortFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D v tail)
    (hblocked :
      (Z.1.1 (ring.rightNeighbor e)).qIn.isE = false ∨
      (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff = false) :
    (∀ j : Fin (topClockSpan n),
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
      (Z.1.1 (certSite s j.val)).qOut) ∧
    (∀ (j : Fin (topClockSpan n))
      (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (t : Bool),
      (Z.1.1 (certSite s j.val)).qOut = .D value t →
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  obtain ⟨_, _, _, hatomPort⟩ :=
    topFreshTailCohortWaveRowTwelveBlockedPortCarrier
      ring C s hn hbad Z anchor W e hsite v tail hdata hblocked
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z W.queue.trace.1
    (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    have hm := hgeom.2.2.2
    rw [show topClockSpan n - 1 + 1 = topClockSpan n by omega] at hm
    simp only [if_pos rfl] at hm
    rw [hsite]
    exact hm
  have howner :
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut =
        .D v tail := by
    unfold topPortLiteralTopOwner
    rcases hblocked with hinput | hcarry
    · cases hi : (Z.1.1 (ring.rightNeighbor e)).qIn with
      | E =>
          simp [hi, InTok.isE] at hinput
      | P value stamp =>
          simp [liveTopPair, hxl, hyl, hyb,
            hdata, hi, OutTok.isD, InTok.isE]
      | S value stamp =>
          simp [liveTopPair, hxl, hyl, hyb,
            hdata, hi, OutTok.isD, InTok.isE]
      | X =>
          simp [liveTopPair, hxl, hyl, hyb,
            hdata, hi, OutTok.isD, InTok.isE]
    · cases hc : (Z.1.1 (ring.rightNeighbor e)).qCarry with
      | OFF =>
          simp [hc, QCarry.isOff] at hcarry
      | L bit err =>
          simp [liveTopPair, hxl, hyl, hyb,
            hdata, hc, OutTok.isD, QCarry.isOff]
  have hsourceStay :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D v tail := by
    change (topFixedPublicNext ring C Z.1.1 e e).qOut =
      .D v tail
    exact (topPortLiteralSourceFields
      ring C Z.1.1 e).2.2.trans howner
  have hrightSite :
      ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite, topFreshTailFirstBorderNeighborSite]
    congr 1
    omega
  have haway :
      ∀ j : Fin (topClockSpan n),
        j.val ≠ topClockSpan n - 1 →
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e := by
    intro j hne
    constructor
    · intro he
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
        (by simpa only [Fin.val_mk] using he.trans hsite)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      exact hne hv
    · rw [hrightSite]
      exact topFreshTailFirstBorderPortOutsideSource s hn j
  constructor
  · intro j
    by_cases hj : j.val = topClockSpan n - 1
    · have hs : certSite s j.val = e := by
        rw [hj]
        exact hsite.symm
      rw [hs, hdata]
      exact hsourceStay
    · obtain ⟨hs, ht⟩ := haway j hj
      exact (topFreshTailCausalOffPairSlotAgreement
        ring C s Z e W.queue j hs ht).1
  · intro j value t hdataJ
    by_cases hj : j.val = topClockSpan n - 1
    · have hs : certSite s j.val = e := by
        rw [hj]
        exact hsite.symm
      rw [hs]
      exact hatomPort
    · obtain ⟨hs, ht⟩ := haway j hj
      change
        ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
          (certSite s j.val)).comparison.out.atom =
        (Z.1.2.current (certSite s j.val)).comparison.out.atom
      simp only [digitAuditStep, digitGhostStep,
        if_neg hs, if_neg ht]


/-- When every source token and sampled atom is framed and the
filtered port receipt list is unchanged, the selected current
and next maps remain valid without any physical movement.
A conservative full update mask permits one common proof for
both interior and terminal stays.
Consumer: the blocked-port row-twelve wave closure. -/
theorem topFreshTailCohortWaveFramedStayStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hexports :
      topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time)
    (houtputs :
      ∀ j : Fin (topClockSpan n),
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut =
        (Z.1.1 (certSite s j.val)).qOut)
    (hatoms :
      ∀ (j : Fin (topClockSpan n))
        (value : Fin (compileAdvice (ceilLogTwo n)).topA)
        (tail : Bool),
        (Z.1.1 (certSite s j.val)).qOut = .D value tail →
        ((topFixedTraceNext ring C Z e).1.2.current
          (certSite s j.val)).comparison.out.atom =
        (Z.1.2.current (certSite s j.val)).comparison.out.atom) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hslots := topFreshTailCohortWaveStaySlots
    ring C s Z W.queue e houtputs
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hhistoryStay :
      ∀ home position : Fin (topClockSpan n),
        ∀ parent a : TopFreshTailCarrier (topClockSpan n),
        TopFreshTailCohortIssueHistory
          ring C s Z.2 home position parent a →
        (topFreshTailGenealogy ring C s Z).slots position =
          some a →
        TopFreshTailCohortIssueHistory
          ring C s (Z.2 ++ [e]) home position parent a := by
    intro home position parent a hissued hslot
    have hold :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C Z.2)).slots position =
          some a := by
      rw [hrun]
      exact hslot
    have hnew :
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (Z.2 ++ [e]))).slots position =
          some a := by
      rw [topFreshTailFifoRunSnoc, hrun, hslots position]
      exact hslot
    exact topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 home position parent a hissued e hold hnew
  have hactiveStay :
      ∀ home position : Fin (topClockSpan n),
        ∀ a : TopFreshTailCarrier (topClockSpan n),
        TopFreshTailPostAnchorActiveHome ring C s Z home position a →
        TopFreshTailPostAnchorActiveHome ring C s
          (topFixedTraceNext ring C Z e) home position a := by
    intro home position a hactive
    obtain ⟨hle, hslot, hfresh, hkind⟩ := hactive
    refine ⟨hle, ?_, hfresh, ?_⟩
    · rw [hslots position]
      exact hslot
    · rcases hkind with ⟨hhome, hu⟩ |
        ⟨sample, hd, hs, hl, hsiteSample, hv, ht, ha⟩
      · exact Or.inl ⟨hhome, (houtputs position).trans hu⟩
      · exact Or.inr
          ⟨sample, (houtputs position).trans hd,
            digitRecordedSampleStep
              ring (piD Z.1.1) Z.1.2 e sample hs,
            hl, hsiteSample, hv, ht,
            (hatoms position _ _ hd).trans ha⟩
  have hhomeStay :
      ∀ j : Fin (topClockSpan n),
        TopFreshTailFirstBorderHomeSlot ring C s Z W.root j →
        TopFreshTailFirstBorderHomeSlot ring C s
          (topFixedTraceNext ring C Z e) W.root j := by
    intro j hhome
    unfold TopFreshTailFirstBorderHomeSlot at hhome ⊢
    obtain ⟨a, hslot, hfresh, hparent, hkind⟩ := hhome
    refine ⟨a, by rw [hslots j]; exact hslot,
      hfresh, hparent, ?_⟩
    rcases hkind with hu |
      ⟨sample, hd, hs, hl, hsiteSample, hv, ht, ha⟩
    · exact Or.inl ((houtputs j).trans hu)
    · exact Or.inr
        ⟨sample, (houtputs j).trans hd,
          digitRecordedSampleStep
            ring (piD Z.1.1) Z.1.2 e sample hs,
          hl, hsiteSample, hv, ht,
          (hatoms j _ _ hd).trans ha⟩
  have hlistGet :
      ∀ {α : Type} (L M : List α) (hLM : L = M)
        (i : Nat) (hiL : i < L.length) (hiM : i < M.length),
        L[i]'hiL = M[i]'hiM := by
    intro α L M hLM i hiL hiM
    cases hLM
    rfl
  refine topFreshTailCohortWaveUpdate
    ring C s hn hbad Z anchor W e
    W.currentMap W.nextMap W.currentParent W.root W.rootPosition
    (fun _ => True) (fun _ => True) (fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: the full-site mask leaves no off-site obligation.
    intro j hj
    exact False.elim (hj trivial)
  · -- hcurrentOff: no current home lies outside the full mask.
    intro k hk
    exact False.elim (hk trivial)
  · -- hnextOff: no next home lies outside the full mask.
    intro j hj
    exact False.elim (hj trivial)
  · -- hcurrentAway: no current home is declared off-mask.
    intro k y a hk _
    exact False.elim (hk trivial)
  · -- hnextAway: no next home is declared off-mask.
    intro j hj _
    exact False.elim (hj trivial)
  · -- hcurrentEligibleOff: all current homes use changed proof.
    intro k hk _
    exact False.elim (hk trivial)
  · -- hcurrentAbsentOff: all current homes use changed proof.
    intro k hk _
    exact False.elim (hk trivial)
  · -- hnextEligibleOff: all next homes use changed proof.
    intro j hj _
    exact False.elim (hj trivial)
  · -- hnextAbsentOff: all next homes use changed proof.
    intro j hj _
    exact False.elim (hj trivial)
  · -- hcurrentChanged: same map, real active source and issue.
    intro k _ hb
    have hbound :
        k.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) := by
      simpa only [hexports] using hb
    obtain ⟨y, a, hm, ha, hi⟩ := W.currentIssued k hbound
    exact ⟨y, a, hm, hactiveStay k y a ha,
      hhistoryStay k y W.currentParent a hi.2 ha.2.1⟩
  · -- hcurrentChangedAbsent: same map and same cohort range.
    intro k _ hb
    exact W.currentAbsent k
      (by simpa only [hexports] using hb)
  · -- hnextChanged: same stationary child, home and issue.
    intro j _ hj
    obtain ⟨a, hm, hs, hh, hi⟩ := W.nextIssued j hj
    exact ⟨a, hm, by rw [hslots j]; exact hs,
      hhomeStay j hh,
      hhistoryStay j j W.root a hi.2 hs⟩
  · -- hnextChangedAbsent: next-map bound is unchanged.
    intro j _ hj
    exact W.nextAbsent j hj
  · -- hcurrentOrderChanged: old map order persists.
    intro u v _ huv hb p q a b hu hv
    exact W.currentOrder u v huv
      (by simpa only [hexports] using hb) p q a b hu hv
  · -- hcurrentChangedSite: every source is in the full mask.
    intro k j a _ _
    trivial
  · -- hcurrentUnchangedSite: there are no off-mask sites.
    intro j a k hj _
    exact False.elim (hj trivial)
  · -- hnextUnchangedSite: there are no off-mask sites.
    intro j hj
    exact False.elim (hj trivial)
  · -- hsourceChanged: every unchanged genealogy slot retains its owner.
    intro j a _ hs
    have hold :
        (topFreshTailGenealogy ring C s Z).slots j =
          some a := by
      rw [hslots j] at hs
      exact hs
    exact W.sourceCoverage j a hold
  · -- hrootStable: the root home is in the changed mask.
    intro hk
    exact False.elim (hk trivial)
  · -- hrootChanged: unchanged current map still selects the root.
    intro _
    exact W.rootSelected
  · -- hrootKind: source output and sampled atom frame.
    rcases W.rootKind with ⟨hp, hu⟩ |
      ⟨sample, hs, hl, hsampleSite, ht, hd, ha⟩
    · apply Or.inl
      refine ⟨hp, ?_⟩
      have hf := houtputs W.rootPosition
      rw [hp] at hf
      exact hf.trans hu
    · exact Or.inr
        ⟨sample, digitRecordedSampleStep
          ring (piD Z.1.1) Z.1.2 e sample hs,
          hl, hsampleSite, ht,
          (houtputs W.rootPosition).trans hd,
          (hatoms W.rootPosition sample.value true hd).trans ha⟩
  · -- hparentReceipt: blocked service does not change generation.
    have hp := topFreshTailCohortWaveParentReceiptAppend
      ring C s hn Z anchor e
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n) W.currentParent
      W.currentParentReceipt hexports
    simpa only [hexports] using hp
  · -- hexportOld: identical filtered lists preserve each lookup.
    intro i hiOld hiNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ hexports i hiNew hiOld
  · -- hexportAdded: the unchanged list has no new index.
    intro i hnew
    have hi := i.isLt
    have hlength := congrArg List.length hexports
    omega


/-- Row twelve is a source-terminal blocked D: no port
receipt, no rearm, no move and no map reindexing.
Consumer: J5 cohort-selected wave one-edge induction. -/
theorem topFreshTailCohortWaveStepRowTwelve
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hdata : (Z.1.1 e).qOut = .D v tail)
    (hblocked :
      (Z.1.1 (ring.rightNeighbor e)).qIn.isE = false ∨
      (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff = false) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hexports := topFreshTailCohortWaveBlockedPortExports
    ring C s hn hbad Z anchor W e hsite v tail hdata hblocked
  obtain ⟨houtputs, hatoms⟩ :=
    topFreshTailCohortWaveBlockedPortFrame
      ring C s hn hbad Z anchor W e hsite v tail hdata hblocked
  exact topFreshTailCohortWaveFramedStayStep
    ring C s hn hbad Z anchor W e hexports houtputs hatoms

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The genuine selected root hop appends a movement to the
actual zero-home packet-follow witness, preserving its OLD
historical parent and full root carrier.
Consumer: row-eight hcurrentChanged in J5 wave preservation. -/
theorem topFreshTailCohortWaveRootHopHistory
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailCohortIssueHistory
      ring C s (Z.2 ++ [e])
      (⟨0, show 0 < topClockSpan n by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ : Fin (topClockSpan n))
      (⟨W.rootPosition.val + 1, hnext⟩ :
        Fin (topClockSpan n))
      W.currentParent W.root := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have hrootSlot :=
    (topFreshTailCohortWaveRowEightSelectedRootSlot
      ring C s hn Z anchor W).2
  have hhop :=
    topFreshTailCohortWaveRowEightRootHopIssue
      ring C s hn hbad Z anchor W e hsite hnext
      v hdata hempty
  obtain ⟨x, carrier, hmap, _, hissued⟩ :=
    W.currentIssued
      (⟨0, hzero⟩ : Fin (topClockSpan n))
      (Nat.zero_le _)
  have hp : (x, carrier) = (W.rootPosition, W.root) :=
    Option.some.inj (hmap.symm.trans W.rootSelected)
  have hx : x = W.rootPosition := congrArg Prod.fst hp
  have ha : carrier = W.root := congrArg Prod.snd hp
  rw [hx, ha] at hissued
  have hhistory :
      TopFreshTailCohortIssueHistory ring C s Z.2
        (⟨0, hzero⟩ : Fin (topClockSpan n))
        W.rootPosition W.currentParent W.root := hissued.2
  unfold TopFreshTailCohortIssueHistory at hhistory ⊢
  obtain ⟨before, after, issued, hword, hrearm, hfollow⟩ :=
    hhistory
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hrunNext :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hrun]
  have hstep :
      TopFreshTailCohortPacketStep ring C s Z.2 e
        W.rootPosition W.root
        (⟨W.rootPosition.val + 1, hnext⟩ :
          Fin (topClockSpan n)) W.root := by
    unfold TopFreshTailCohortPacketStep
    refine ⟨?_, ?_, Or.inr (Or.inl ?_)⟩
    · rw [hrun]
      exact hrootSlot
    · rw [hrunNext]
      exact hhop.2.1
    · refine ⟨hnext, rfl, hsite, rfl, v, true, ?_, ?_⟩
      · rw [hrun]
        exact hdata
      · rw [hrun]
        exact hempty
  refine ⟨before, after ++ [e], issued, ?_, hrearm, ?_⟩
  · rw [hword]
    simp only [List.cons_append, List.append_assoc]
  · exact TopFreshTailCohortPacketFollow.snoc
      hfollow e
      (⟨W.rootPosition.val + 1, hnext⟩ :
        Fin (topClockSpan n)) W.root hstep

/-- A root-hop departure leaves a new stationary next-family
home with its exact root-parent rearm identity and service word.
Consumer: row-eight hnextChanged, source coverage, and nextIssued. -/
theorem topFreshTailCohortWaveRootHopChildHome
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailFirstBorderHomeSlot ring C s
      (topFixedTraceNext ring C Z e)
      W.root W.rootPosition ∧
    TopFreshTailCohortIssueHistory ring C s
      (Z.2 ++ [e]) W.rootPosition W.rootPosition W.root
      (topFreshTailGenealogyRearm W.rootPosition
        (Z.1.2.clock + 1) W.root) := by
  have hhop :=
    topFreshTailCohortWaveRowEightRootHopIssue
      ring C s hn hbad Z anchor W e hsite hnext
      v hdata hempty
  have hfresh :=
    topFreshTailFirstBorderFreshFamilyClosedStep
      ring C s hn hbad Z W.queue W.allFresh e
  constructor
  · unfold TopFreshTailFirstBorderHomeSlot
    refine ⟨topFreshTailGenealogyRearm W.rootPosition
      (Z.1.2.clock + 1) W.root,
      hhop.1, ?_, ?_, Or.inl ?_⟩
    · exact hfresh W.rootPosition _ hhop.1
    · intro _
      exact ⟨Z.1.2.clock + 1, rfl⟩
    · rw [← hsite]
      exact hhop.2.2.1
  · exact hhop.2.2.2

/-- Moving the zero-home current root by one vacant source
position preserves order with every other selected current
home. The proof delegates the global pair comparison to the
installed RowSevenOrder, which does not require a positive
home index.
Consumer: row-eight hcurrentOrderChanged. -/
theorem topFreshTailCohortWaveRootHopOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    ∀ u w : Fin (topClockSpan n),
      u.val < w.val →
      w.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length % topClockSpan n) →
      ∀ p q : Fin (topClockSpan n),
        ∀ a b : TopFreshTailCarrier (topClockSpan n),
        (fun t => if t =
            (⟨0, show 0 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) then
          some ((⟨W.rootPosition.val + 1, hnext⟩ :
            Fin (topClockSpan n)), W.root)
          else W.currentMap t) u = some (p, a) →
        (fun t => if t =
            (⟨0, show 0 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) then
          some ((⟨W.rootPosition.val + 1, hnext⟩ :
            Fin (topClockSpan n)), W.root)
          else W.currentMap t) w = some (q, b) →
        p.val < q.val := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have hs := topFreshTailCausalSourceSiteInjective
      s hn W.rootPosition
      (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
      (by rw [← hsite]; exact hp)
    have hv := congrArg Fin.val hs
    simp only [Fin.val_mk] at hv
    omega
  have hexports := topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort
  exact topFreshTailCohortWaveRowSevenOrder
    ring C s hn Z anchor W
    (⟨0, hzero⟩ : Fin (topClockSpan n))
    W.rootPosition W.root W.rootSelected hnext
    e hsite hempty hexports

/-- A selected D(false) terminal packet cannot belong to the
source-zero current home: that home's recorded sampled tail
is necessarily true. Hence the false-tail retirement occurs
at a positive home in the current cohort.
Consumer: row-thirteen nonwrapping current-map retirement. -/
theorem topFreshTailCohortWaveFalseTerminalPositiveHome
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v false) :
    0 < topClockSpan n - 1 -
      ((topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  obtain ⟨carrier, _, hactive, _⟩ :=
    topFreshTailCohortWaveRowThirteenSelectedHead
      ring C s hn Z anchor W v hterminal
  by_cases hzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) = 0
  · rcases hactive.2.2.2 with ⟨hhome, _⟩ |
        ⟨sample, hdata, _, _, _, _, _, _⟩
    · have hv := congrArg Fin.val hhome
      simp only [Fin.val_mk] at hv
      omega
    · have hvalue :
          (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
            .D (C (certSite s 0)).d true := by
        simpa only [Fin.val_mk, hzero, if_true] using hdata
      rw [hterminal] at hvalue
      cases hvalue
  · omega

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- An OLD comparison U at any source, including the terminal
port, records a sample but cannot export a D packet in the
same service. Consumer: J5 row-five cohort generation/receipt frame. -/
theorem topFreshTailCohortWaveUnreadPortExports
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (e : Fin n)
    (hsite : e = certSite s j.val)
    (hunread : (Z.1.1 e).qOut = .U) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 j
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hnoExport :
      ∀ {c : Compiled} {m : Nat}
        (time : Nat) (source destination : Fin m)
        (x y : DigitLaneView c) (gx gy : DigitLaneGhost c m),
        x.leader = false →
        y.leader = false →
        x.out = .U →
        (digitLaneReplay .comparison time source destination
          x y gx gy).exported = none := by
    intro c m time source destination x y gx gy hx hy hu
    simp [digitLaneReplay, hx, hy, hu,
      OutTok.isD, OutTok.isE, OutTok.isU]
  have hnone :
      (digitReceiptLane .comparison
        (topFreshTailPostAnchorCurrentFrame
          ring Z e).receipt).exported = none := by
    change
      (digitLaneReplay .comparison (Z.1.2.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison (piD Z.1.1 e)
          (piD Z.1.1 e).word.beta)
        (digitLaneView .comparison
          (piD Z.1.1 (ring.rightNeighbor e))
          (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported =
          none
    apply hnoExport
    · exact hxl
    · exact hyl
    · exact hunread
  have hnil :
      topFreshTailPostAnchorNewEntries
        ring s Z anchor.time e = [] := by
    simp [topFreshTailPostAnchorNewEntries, hnone]
  rw [topFreshTailPostAnchorExportsAfterStep, hnil]
  simp only [List.append_nil]



/-- Certificate offsets up to and including the terminal port
have unique physical sites. Consumer: J5 row-five terminal
responder exclusion and all-site update framing. -/
theorem topFreshTailCohortWaveSourceOffsetUnique
    {n : Nat} (s : Fin n) (hn : 5 ≤ n)
    (j : Fin (topClockSpan n)) (t : Nat)
    (ht : t ≤ topClockSpan n)
    (hsite : certSite s j.val = certSite s t) :
    j.val = t := by
  have hwidth : topClockSpan n < n := by
    have hsize := cert_n_ge_t_add_r n hn
    have htime := compileAdvice_t_ge_two
      (ceilLogTwo n) (ringQ_facts n hn).1
    unfold topClockSpan
    omega
  by_cases hj : j.val ≤ t
  · exact MarkedCells.certSite_inj_close s j.val t hj (by omega) hsite
  · have hh := MarkedCells.certSite_inj_close s t j.val
      (by omega) (by omega) hsite.symm
    omega


/-- Reading a selected current U preserves the entire post-anchor
cohort wave. The source's selected carrier is sampled/rekeyed,
a possible occupied responder keeps its own issue history, and
a zero-home read updates the root carrier without changing its
generation or the stationary next-family range.
Consumer: J5 row-five arm of the one-edge wave dispatcher. -/
theorem topFreshTailCohortWaveStepRowFive
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (h, carrier))
    (e : Fin n) (hsite : e = certSite s h.val)
    (hunread : (Z.1.1 e).qOut = .U) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzeroBound : 0 < topClockSpan n := by omega
  have hsuccBound : h.val + 1 ≤ topClockSpan n := by
    have hh := h.isLt
    omega
  have hneighbor :
      ring.rightNeighbor e = certSite s (h.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s h.val
  have hrootBound :=
    topFreshTailCohortWaveCurrentAtOrAfterRoot
      ring C s hn Z anchor W h h carrier hmap
  have hexports :=
    topFreshTailCohortWaveUnreadPortExports
      ring C s hn hbad Z anchor W h e hsite hunread
  obtain ⟨afterCarrier, hactiveAfter, hhistoryAfter⟩ :=
    topFreshTailCohortWaveRowFiveCurrentUnread
      ring C s hn hbad Z anchor W h hbound carrier
      hmap e hsite hunread
  have hlistGet :
      ∀ {α : Type} (L M : List α) (hLM : L = M)
        (q : Nat) (hqL : q < L.length) (hqM : q < M.length),
        L[q]'hqL = M[q]'hqM := by
    intro α L M hLM q hqL hqM
    cases hLM
    rfl
  refine topFreshTailCohortWaveUpdate
    ring C s hn hbad Z anchor W e
    (fun k => if k = h then some (h, afterCarrier)
      else W.currentMap k)
    W.nextMap W.currentParent
    (if h.val = 0 then afterCarrier else W.root)
    W.rootPosition
    (fun t => t.val = h.val ∨ t.val = h.val + 1)
    (fun k => k = h ∨
      ∃ y a, W.currentMap k = some (y, a) ∧
        y.val = h.val + 1)
    (fun _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: offsets outside h and h+1 are not endpoints.
    intro t ht
    constructor
    · intro he
      have hv := topFreshTailCohortWaveSourceOffsetUnique
        s hn t h.val (by omega) (he.trans hsite)
      exact ht (Or.inl hv)
    · intro he
      have hv := topFreshTailCohortWaveSourceOffsetUnique
        s hn t (h.val + 1) hsuccBound
        (by rw [← hneighbor]; exact he)
      exact ht (Or.inr hv)
  · -- hcurrentOff: the conditional map frames every unmarked home.
    intro k hk
    have hne : k ≠ h := by
      intro he
      exact hk (Or.inl he)
    simp only [if_neg hne]
  · -- hnextOff: stationary next maps are unchanged in row five.
    intro t _
    rfl
  · -- hcurrentAway: old selected current sites are distinct;
    -- a touched responder is marked changed.
    intro k y a hk hmapK
    have hne : h ≠ k := by
      intro he
      exact hk (Or.inl he.symm)
    have hdistinct :=
      topFreshTailCohortWaveCurrentHomeDistinct
        ring C s hn Z anchor W h k hne h y
        carrier a hmap hmapK
    constructor
    · intro he
      have hy := topFreshTailCausalSourceSiteInjective
        s hn y h (he.trans hsite)
      exact hdistinct hy.symm
    · intro he
      have hv := topFreshTailCohortWaveSourceOffsetUnique
        s hn y (h.val + 1) hsuccBound
        (by rw [← hneighbor]; exact he)
      exact hk (Or.inr ⟨y, a, hmapK, hv⟩)
  · -- hnextAway: stationary next sites lie strictly before the
    -- pinned root, itself no farther than the sampled home h.
    intro t _ hbelow
    have hlt : t.val < h.val := by omega
    constructor
    · intro he
      have hv := topFreshTailCohortWaveSourceOffsetUnique
        s hn t h.val (by omega) (he.trans hsite)
      omega
    · intro he
      have hv := topFreshTailCohortWaveSourceOffsetUnique
        s hn t (h.val + 1) hsuccBound
        (by rw [← hneighbor]; exact he)
      omega
  · -- hcurrentEligibleOff: source U emits no export, parent unchanged.
    intro k _ hb
    refine ⟨?_, rfl⟩
    simpa only [hexports] using hb
  · -- hcurrentAbsentOff: unchanged export count gives same range.
    intro k _ hb
    simpa only [hexports] using hb
  · -- hnextEligibleOff: next boundary is fixed; if nonempty then
    -- the current root was not sampled at home zero.
    intro t _ hbelow
    have hnonzero : h.val ≠ 0 := by
      intro hz
      have hrootZero : W.rootPosition.val = 0 := by omega
      omega
    exact ⟨hbelow, by simp only [if_neg hnonzero]⟩
  · -- hnextAbsentOff: root position has not moved.
    intro t _ hb
    exact hb
  · -- hcurrentChanged: selected h has authentic unread history;
    -- an occupied responder has the independent incoming frame.
    intro k hk hb
    rcases hk with hk | ⟨y, a, hmapK, hy⟩
    · subst k
      refine ⟨h, afterCarrier, ?_, hactiveAfter, hhistoryAfter⟩
      simp only [if_pos rfl, ↓reduceIte]
    · have hne : k ≠ h := by
        intro he
        subst k
        have hp : (h, carrier) = (y, a) :=
          Option.some.inj (hmap.symm.trans hmapK)
        have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
        omega
      have hboundOld :
          k.val ≤ topClockSpan n - 1 -
            ((topClockConcreteExportsAfter s Z anchor.time).length %
              topClockSpan n) := by
        simpa only [hexports] using hb
      have htarget :
          ring.rightNeighbor e = certSite s y.val := by
        rw [hneighbor, hy]
      have hframe :=
        topFreshTailCohortWaveUnreadResponderCurrent
          ring C s hn hbad Z anchor W h e hsite hunread
          k y a hboundOld hmapK htarget
      refine ⟨y, a, ?_, hframe.1, hframe.2⟩
      simpa only [if_neg hne] using hmapK
  · -- hcurrentChangedAbsent: both marked kinds are existing
    -- current homes within the previous issued range.
    intro k hk hb
    have hbOld :
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) < k.val := by
      simpa only [hexports] using hb
    rcases hk with heq | ⟨y, a, hm, _⟩
    · subst k
      omega
    · have hnone := W.currentAbsent k hbOld
      rw [hnone] at hm
      cases hm
  · -- hnextChanged: there are no modified next-map entries.
    intro t ht
    cases ht
  · -- hnextChangedAbsent: there are no modified next-map entries.
    intro t ht
    cases ht
  · -- hcurrentOrderChanged: unchanged physical positions and
    -- topFreshTailCohortWaveRowFiveOrder.
    intro u v _ huv hb x y a b hu hv
    exact topFreshTailCohortWaveRowFiveOrder
      ring C s hn Z anchor W h carrier afterCarrier
      hmap e hexports u v huv hb x y a b hu hv
  · -- hcurrentChangedSite: the sampled current remains at h,
    -- and any extra touched responder remains at h+1.
    intro k t a hk hnew
    rcases hk with heq | ⟨y, b, hmapK, hy⟩
    · subst k
      have hp : (h, afterCarrier) = (t, a) := by
        have hs : some (h, afterCarrier) = some (t, a) := by
          simpa only [if_pos rfl, ↓reduceIte] using hnew
        exact Option.some.inj hs
      exact Or.inl (congrArg Fin.val ((Prod.mk.inj hp).1).symm)
    · have hne : k ≠ h := by
        intro heq
        subst k
        have hp : (h, carrier) = (y, b) :=
          Option.some.inj (hmap.symm.trans hmapK)
        have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
        omega
      have hnewOld : W.currentMap k = some (t, a) := by
        simpa only [if_neg hne] using hnew
      have hp : (y, b) = (t, a) :=
        Option.some.inj (hmapK.symm.trans hnewOld)
      have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
      exact Or.inr (by omega)
  · -- hcurrentUnchangedSite: any marked current entry is
    -- physically at the served source or responder.
    intro t a k ht hmapK
    intro hk
    rcases hk with heq | ⟨y, b, hmapResponder, hy⟩
    · subst k
      have hp : (h, carrier) = (t, a) :=
        Option.some.inj (hmap.symm.trans hmapK)
      exact ht (Or.inl (congrArg Fin.val ((Prod.mk.inj hp).1).symm))
    · have hp : (t, a) = (y, b) :=
        Option.some.inj (hmapK.symm.trans hmapResponder)
      have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
      exact ht (Or.inr (by omega))
  · -- hnextUnchangedSite: changedNext is identically false.
    intro t _ ht
    cases ht
  · -- hsourceChanged: h is the newly sampled selected current;
    -- the touched responder preserves old coverage and cannot
    -- be a stationary next site to the right of the root.
    intro t a ht hslotNext
    rcases ht with hth | htSuc
    · have heq : t = h := Fin.ext hth
      subst t
      have ha : a = afterCarrier := by
        have both : some afterCarrier = some a :=
          hactiveAfter.2.1.symm.trans hslotNext
        exact (Option.some.inj both).symm
      subst a
      apply Or.inl
      refine ⟨h, by simp only [if_pos rfl, ↓reduceIte], ?_⟩
      exact W.nextAbsent h hrootBound
    · have htarget : ring.rightNeighbor e = certSite s t.val := by
        rw [hneighbor, htSuc]
      have hqueueNext :
          TopFreshTailCausalQueue ring C s
            (topFixedTraceNext ring C Z e) :=
        (topFreshTailCohortWaveRowFiveCommonFrame
          ring C s hn hbad Z anchor W e).2.1
      have hnotEmptyNext :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s t.val)).qOut ≠ .E := by
        intro he
        have hnone := (hqueueNext.slot t).mp he
        rw [hslotNext] at hnone
        cases hnone
      have houtput :=
        topFreshTailCohortWaveUnreadResponderOutput
          ring C s hn hbad Z anchor W h e hsite hunread
      have hnotEmptyOld :
          (Z.1.1 (certSite s t.val)).qOut ≠ .E := by
        intro he
        apply hnotEmptyNext
        rw [← htarget]
        exact houtput.trans (by rw [htarget]; exact he)
      obtain ⟨oldCarrier, hslotOld⟩ :=
        topFreshTailCausalOccupiedHasCarrier
          ring C s Z W.queue t hnotEmptyOld
      have hframe :=
        topFreshTailCohortWaveUnreadResponderCarrier
          ring C s hn hbad Z anchor W h t e hsite
          hunread htarget oldCarrier hslotOld
      have ha : a = oldCarrier := by
        have both : some oldCarrier = some a :=
          hframe.2.symm.trans hslotNext
        exact (Option.some.inj both).symm
      subst a
      have hnextAbsent :
          W.nextMap t = none := W.nextAbsent t (by omega)
      rcases W.sourceCoverage t oldCarrier hslotOld with
        ⟨k, hcurrent, _⟩ | ⟨hnextSome, _⟩
      · have hne : k ≠ h := by
          intro he
          subst k
          have hp : (h, carrier) = (t, oldCarrier) :=
            Option.some.inj (hmap.symm.trans hcurrent)
          have hv := congrArg Fin.val ((Prod.mk.inj hp).1)
          omega
        apply Or.inl
        exact ⟨k, by simpa only [if_neg hne] using hcurrent,
          hnextAbsent⟩
      · rw [hnextAbsent] at hnextSome
        cases hnextSome
  · -- hrootStable: if zero is untouched, the sampled home
    -- is positive, and the chosen root carrier is unchanged.
    intro hk
    have hnonzero : h.val ≠ 0 := by
      intro hz
      have heq : (⟨0, hzeroBound⟩ : Fin (topClockSpan n)) = h :=
        Fin.ext (by simpa only [Fin.val_mk] using hz.symm)
      exact hk (Or.inl heq)
    exact ⟨rfl, by simp only [if_neg hnonzero]⟩
  · -- hrootChanged: the only possible changed zero home is
    -- the served current U at zero; the new root is its sample.
    intro hk
    have hzero : h.val = 0 := by
      rcases hk with heq | ⟨y, a, hm, hy⟩
      · have hv := congrArg Fin.val heq
        simpa only [Fin.val_mk] using hv.symm
      · have hrootMap : W.currentMap
            (⟨0, hzeroBound⟩ : Fin (topClockSpan n)) =
              some (W.rootPosition, W.root) := W.rootSelected
        have hp : (W.rootPosition, W.root) = (y, a) :=
          Option.some.inj (hrootMap.symm.trans hm)
        have hyRoot := congrArg Fin.val ((Prod.mk.inj hp).1)
        omega
    have hindex : h = (⟨0, hzeroBound⟩ :
      Fin (topClockSpan n)) := Fin.ext hzero
    have hmapZero :
        W.currentMap (⟨0, hzeroBound⟩ : Fin (topClockSpan n)) =
          some (h, carrier) := by
      rw [← hindex]
      exact hmap
    have hp : (W.rootPosition, W.root) = (h, carrier) :=
      Option.some.inj (W.rootSelected.symm.trans hmapZero)
    have hrootPosition : W.rootPosition = h :=
      (Prod.mk.inj hp).1
    rw [← hindex, hrootPosition]
    simp only [if_pos rfl, if_pos hzero, ↓reduceIte]
  · -- hrootKind: a positive current U is off the root pair;
    -- a zero-home U produces a recorded D(true) root sample.
    by_cases hzero : h.val = 0
    · have hindex : h = (⟨0, hzeroBound⟩ :
        Fin (topClockSpan n)) := Fin.ext hzero
      have hmapZero :
          W.currentMap (⟨0, hzeroBound⟩ : Fin (topClockSpan n)) =
            some (h, carrier) := by
        rw [← hindex]
        exact hmap
      have hp : (W.rootPosition, W.root) = (h, carrier) :=
        Option.some.inj (W.rootSelected.symm.trans hmapZero)
      have hrootPosition : W.rootPosition = h :=
        (Prod.mk.inj hp).1
      have hgeom :=
        topFreshTailCausalSourcePublicGeometry
          ring C s hn hbad Z W.queue.trace.1 h
      have hxl : (Z.1.1 e).l = false := by
        rw [hsite]
        exact hgeom.1
      have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
        rw [hsite]
        exact hgeom.2.1
      have hmarker : (Z.1.1 e).beta = true := by
        have hm := hgeom.2.2.1
        rw [if_pos hzero] at hm
        rw [hsite]
        exact hm
      have hpostD :
          ((topFixedTraceNext ring C Z e).1.1 e).qOut =
            .D (Z.1.1 e).d true := by
        have hh := topFreshTailFifoUnreadSamples
          ring C Z e hxl hyl hunread
        rw [hmarker] at hh
        exact hh
      rcases hactiveAfter.2.2.2 with ⟨_, hpostU⟩ |
        ⟨sample, hdata, hrecord, hlane, hsampleSite,
          hvalue, htail, hatom⟩
      · have hpostSourceU :
            ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U := by
          rw [← hsite] at hpostU
          exact hpostU
        rw [hpostD] at hpostSourceU
        cases hpostSourceU
      · have hsampleZero : sample.id.site = certSite s 0 := by
          rw [hzero] at hsampleSite
          exact hsampleSite
        have hsampleTail : sample.tail = true := by
          rw [if_pos hzero] at htail
          exact htail
        have hrootData :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s W.rootPosition.val)).qOut =
                .D sample.value true := by
          rw [hrootPosition]
          have hif : (if h.val = 0 then true else false) = true :=
            if_pos hzero
          rw [hif] at hdata
          rw [hvalue]
          exact hdata
        have hrootAtom :
            ((topFixedTraceNext ring C Z e).1.2.current
              (certSite s W.rootPosition.val)).comparison.out.atom =
              some (.sampled sample.id) := by
          rw [hrootPosition]
          exact hatom
        exact Or.inr ⟨sample, hrecord, hlane,
          hsampleZero, hsampleTail, hrootData, hrootAtom⟩
    · have hpositive : 0 < h.val := by omega
      have hrootBefore :=
        topFreshTailCohortWaveCurrentRootPrecedes
          ring C s hn Z anchor W h hpositive hbound
          h carrier hmap
      have hrootAway :
          certSite s W.rootPosition.val ≠ e ∧
          certSite s W.rootPosition.val ≠ ring.rightNeighbor e := by
        constructor
        · intro he
          have hp := topFreshTailCausalSourceSiteInjective
            s hn W.rootPosition h (he.trans hsite)
          have hv := congrArg Fin.val hp
          omega
        · intro he
          have hv := topFreshTailCohortWaveSourceOffsetUnique
            s hn W.rootPosition (h.val + 1) hsuccBound
            (by rw [← hneighbor]; exact he)
          omega
      have hframe := topFreshTailCausalOffPairSlotAgreement
        ring C s Z e W.queue W.rootPosition
        hrootAway.1 hrootAway.2
      rcases W.rootKind with ⟨hrootZero, hrootU⟩ |
        ⟨sample, hrecord, hlane, hsampleSite,
          htail, hrootD, hatomRoot⟩
      · have hframeZero :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s 0)).qOut =
            (Z.1.1 (certSite s 0)).qOut := by
          simpa only [hrootZero] using hframe.1
        exact Or.inl ⟨hrootZero, hframeZero.trans hrootU⟩
      · have hatomFrame :
            ((topFixedTraceNext ring C Z e).1.2.current
              (certSite s W.rootPosition.val)).comparison.out.atom =
            (Z.1.2.current
              (certSite s W.rootPosition.val)).comparison.out.atom := by
          change
            ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
              (certSite s W.rootPosition.val)).comparison.out.atom =
            (Z.1.2.current
              (certSite s W.rootPosition.val)).comparison.out.atom
          simp only [digitAuditStep, digitGhostStep,
            if_neg hrootAway.1, if_neg hrootAway.2]
        exact Or.inr ⟨sample,
          digitRecordedSampleStep
            ring (piD Z.1.1) Z.1.2 e sample hrecord,
          hlane, hsampleSite, htail,
          hframe.1.trans hrootD, hatomFrame.trans hatomRoot⟩
  · -- hparentReceipt: non-exporting U retains its historical parent.
    have hp := topFreshTailCohortWaveParentReceiptAppend
      ring C s hn Z anchor e
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n)
      W.currentParent W.currentParentReceipt hexports
    simpa only [hexports] using hp
  · -- hexportOld: identical lists transport List.get at the same Nat.
    intro q hOld hNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ hexports q hNew hOld
  · -- hexportAdded: zero new exports after U sampling.
    intro q hAdded
    have hq := q.isLt
    have hlength := congrArg List.length hexports
    omega

end L3

namespace L3

/-- The authentic OLD accepted comparison-port receipt appends exactly
one post-anchor export, never a reordered or synthesized entry.
Consumer: J5 accepted-terminal chronological export records. -/
theorem topFreshTailCohortWaveAcceptedExports
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent :
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time ++
        [exported] := by
  obtain ⟨anchorFrame, hframeMem, hframeTime, _, _⟩ :=
    W.anchorRecorded.1
  have hframeBound :=
    (topFreshTailAuditFrameOrderReached
      ring C Z W.reached).1 anchorFrame hframeMem
  have hanchorClock : anchor.time ≤ Z.1.2.clock := by
    omega
  obtain ⟨hport, hneighbor, _, htime, _, hsource,
    hdestination, _, _⟩ :=
    topFreshTailAuditSelectedPortFrame
      ring C s Z e exported hevent
  have hportPair :
      e = certSite s (topClockSpan n - 1) ∧
      ring.rightNeighbor e = certSite s (topClockSpan n) :=
    ⟨hport, hneighbor⟩
  have hlocal :
      (digitReceiptLane .comparison
        (topFreshTailPostAnchorCurrentFrame
          ring Z e).receipt).exported =
        some exported := by
    change
      (digitService (Z.1.2.clock + 1)
        e (ring.rightNeighbor e)
        (piD Z.1.1 e)
        (piD Z.1.1 (ring.rightNeighbor e))
        (Z.1.2.current e)
        (Z.1.2.current (ring.rightNeighbor e))).comparison.exported =
          some exported
    simpa only [topFreshTailGenealogyPortExport,
      if_pos hportPair] using hevent
  have hqualified :
      anchor.time < exported.time ∧
      exported.source = certSite s (topClockSpan n - 1) ∧
      exported.destination = certSite s (topClockSpan n) := by
    exact ⟨by omega, hsource.trans hport,
      hdestination.trans hneighbor⟩
  have hsingleton :
      topFreshTailPostAnchorNewEntries
        ring s Z anchor.time e = [exported] := by
    simp [topFreshTailPostAnchorNewEntries,
      hlocal, hqualified]
  rw [topFreshTailPostAnchorExportsAfterStep, hsingleton]

/-- A terminal OLD U is the ordinary unread same-site rekey,
including when it sits at the comparison port. The port does
not accept a D or append an export in this service.
Consumer: J5 row-eleven one-edge wave preservation. -/
theorem topFreshTailCohortWaveStepRowEleven
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (h : Fin (topClockSpan n))
    (hbound :
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n))
    (x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hmap : W.currentMap h = some (x, carrier))
    (e : Fin n) (hsite : e = certSite s x.val)
    (hterminal : x.val + 1 = topClockSpan n)
    (hunread : (Z.1.1 e).qOut = .U) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  obtain ⟨oldX, oldCarrier, hmapOld, hactive, _⟩ :=
    W.currentIssued h hbound
  have hpair : (oldX, oldCarrier) = (x, carrier) :=
    Option.some.inj (hmapOld.symm.trans hmap)
  have hx : oldX = x := congrArg Prod.fst hpair
  have ha : oldCarrier = carrier := congrArg Prod.snd hpair
  rw [hx, ha] at hactive
  rcases hactive.2.2.2 with ⟨hhome, _⟩ |
    ⟨localSample, hdata, _, _, _, _, _, _⟩
  · have hmapAt : W.currentMap h = some (h, carrier) := by
      rw [hhome] at hmap
      exact hmap
    have hsiteAt : e = certSite s h.val := by
      rw [hhome] at hsite
      exact hsite
    exact topFreshTailCohortWaveStepRowFive
      ring C s hn hbad Z anchor W h hbound carrier
      hmapAt e hsiteAt hunread
  · rw [hsite] at hunread
    rw [hdata] at hunread
    cases hunread

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The selected zero-home D(true) root traverses its genuine empty
successor and remains an active zero-home packet, with unchanged full
carrier and a U at the departure site.
Consumer: row-eight hcurrentChanged and rootKind. -/
theorem topFreshTailCohortWaveRootHopActive
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdeparture : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailPostAnchorActiveHome
      ring C s (topFixedTraceNext ring C Z e)
      (⟨0, show 0 < topClockSpan n by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ : Fin (topClockSpan n))
      (⟨W.rootPosition.val + 1, hnext⟩ :
        Fin (topClockSpan n)) W.root ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have hrootActive :=
    (topFreshTailCohortWaveRowEightSelectedRootSlot
      ring C s hn Z anchor W).1
  have hcorrect :
      (Z.1.1 e).qOut =
        .D (C (certSite s 0)).d true := by
    rcases hrootActive.2.2.2 with ⟨_, hunread⟩ |
      ⟨sample, hrootData, _, _, _, _, _, _⟩
    · rw [hsite] at hdeparture
      rw [hunread] at hdeparture
      cases hdeparture
    · rw [hsite]
      simpa only [Fin.val_mk, if_true] using hrootData
  exact topFreshTailPostAnchorActiveHomeInteriorMove
    ring C s hn hbad Z W.queue
    (⟨0, hzero⟩ : Fin (topClockSpan n))
    W.rootPosition W.root hrootActive
    e hsite hnext
    (by simpa only [Fin.val_mk, if_true] using hcorrect)
    hempty

/-- The moved selected root still has the recorded zero-home
comparison sample, true tail, and the atom at its new position.
Consumer: row-eight hrootKind. -/
theorem topFreshTailCohortWaveRootHopKind
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdeparture : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample
        (topFixedTraceNext ring C Z e).1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site = certSite s 0 ∧
      sample.tail = true ∧
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s (W.rootPosition.val + 1))).qOut =
          .D sample.value true ∧
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s (W.rootPosition.val + 1))).comparison.out.atom =
          some (.sampled sample.id) := by
  have hactive :=
    (topFreshTailCohortWaveRootHopActive
      ring C s hn hbad Z anchor W e hsite hnext
      v hdeparture hempty).1
  rcases hactive.2.2.2 with ⟨hhome, _⟩ |
    ⟨sample, hdataNew, hrecord, hlane, hsampleSite,
      hsampleValue, hsampleTail, hatom⟩
  · have hv := congrArg Fin.val hhome
    simp only [Fin.val_mk] at hv
    omega
  · refine ⟨sample, hrecord, hlane, ?_, ?_, ?_, ?_⟩
    · simpa only [Fin.val_mk] using hsampleSite
    · simpa only [Fin.val_mk, if_true] using hsampleTail
    · rw [hsampleValue]
      simpa only [Fin.val_mk, if_true] using hdataNew
    · simpa only [Fin.val_mk] using hatom

/-- A selected root hop is nonterminal, so the chronological
post-anchor export list and the cohort generation stay fixed.
Consumer: row-eight eligibility, absence, receipt, and export records. -/
theorem topFreshTailCohortWaveRootHopSilent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have hs := topFreshTailCausalSourceSiteInjective
      s hn W.rootPosition
      (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
      (by rw [← hsite]; exact hp)
    have hv := congrArg Fin.val hs
    simp only [Fin.val_mk] at hv
    omega
  exact topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort

/-- The newly rearmed source is a fully issued stationary next
home, witnessed by its OLD source event and issue history.
Consumer: row-eight hnextChanged and nextIssued. -/
theorem topFreshTailCohortWaveRootHopNextIssue
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdeparture : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    ∃ a : TopFreshTailCarrier (topClockSpan n),
      (fun t => if t = W.rootPosition then
        some (topFreshTailGenealogyRearm W.rootPosition
          (Z.1.2.clock + 1) W.root)
        else W.nextMap t) W.rootPosition = some a ∧
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
          W.rootPosition = some a ∧
      TopFreshTailFirstBorderHomeSlot ring C s
        (topFixedTraceNext ring C Z e)
        W.root W.rootPosition ∧
      TopFreshTailCohortIssueHistory ring C s
        (Z.2 ++ [e]) W.rootPosition W.rootPosition
        W.root a := by
  have hhop := topFreshTailCohortWaveRowEightRootHopIssue
    ring C s hn hbad Z anchor W e hsite hnext
    v hdeparture hempty
  have hchild := topFreshTailCohortWaveRootHopChildHome
    ring C s hn hbad Z anchor W e hsite hnext
    v hdeparture hempty
  refine ⟨topFreshTailGenealogyRearm W.rootPosition
    (Z.1.2.clock + 1) W.root, ?_,
    hhop.1, hchild.1, hchild.2⟩
  simp only [if_pos rfl, ↓reduceIte]

/-- After advancing the current root, next-map positions at or
beyond the new root remain absent; only its old source is added.
Consumer: row-eight hnextChangedAbsent and nextAbsent. -/
theorem topFreshTailCohortWaveRootHopNextAbsent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (hnext : W.rootPosition.val + 1 < topClockSpan n) :
    ∀ j : Fin (topClockSpan n),
      W.rootPosition.val + 1 ≤ j.val →
      (fun t => if t = W.rootPosition then
        some (topFreshTailGenealogyRearm W.rootPosition
          (Z.1.2.clock + 1) W.root)
        else W.nextMap t) j = none := by
  intro j hbound
  have hneq : j ≠ W.rootPosition := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  simpa only [if_neg hneq] using
    W.nextAbsent j (by omega)

/-- The two touched genealogy slots are partitioned exactly:
the old root source is the newly issued next child, and the
vacant successor is the moved current root. No other current
home can own either carrier.
Consumer: row-eight hsourceChanged (whole-map coverage). -/
theorem topFreshTailCohortWaveRootHopSourceCoverage
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdeparture : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (j.val = W.rootPosition.val ∨
        j.val = W.rootPosition.val + 1) →
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
          some a →
      (∃ h : Fin (topClockSpan n),
        (fun t => if t =
          (⟨0, show 0 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n)) then
          some ((⟨W.rootPosition.val + 1, hnext⟩ :
            Fin (topClockSpan n)), W.root)
          else W.currentMap t) h = some (j, a) ∧
        (fun t => if t = W.rootPosition then
          some (topFreshTailGenealogyRearm W.rootPosition
            (Z.1.2.clock + 1) W.root)
          else W.nextMap t) j = none) ∨
      ((fun t => if t = W.rootPosition then
          some (topFreshTailGenealogyRearm W.rootPosition
            (Z.1.2.clock + 1) W.root)
          else W.nextMap t) j = some a ∧
        ∀ (h : Fin (topClockSpan n))
          (b : TopFreshTailCarrier (topClockSpan n)),
          (fun t => if t =
            (⟨0, show 0 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) then
            some ((⟨W.rootPosition.val + 1, hnext⟩ :
              Fin (topClockSpan n)), W.root)
            else W.currentMap t) h ≠ some (j, b)) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have hhop := topFreshTailCohortWaveRowEightRootHopIssue
    ring C s hn hbad Z anchor W e hsite hnext
    v hdeparture hempty
  intro j a hj hslot
  rcases hj with hsource | htarget
  · have hsame : j = W.rootPosition := Fin.ext hsource
    subst j
    have hcarrier :
        a = topFreshTailGenealogyRearm W.rootPosition
          (Z.1.2.clock + 1) W.root := by
      have hp : some (topFreshTailGenealogyRearm W.rootPosition
          (Z.1.2.clock + 1) W.root) = some a :=
        hhop.1.symm.trans hslot
      exact (Option.some.inj hp).symm
    subst a
    apply Or.inr
    refine ⟨?_, ?_⟩
    · simp only [if_pos rfl, ↓reduceIte]
    · intro h b hmap
      by_cases hzeroHome :
          h = (⟨0, hzero⟩ : Fin (topClockSpan n))
      · subst h
        have hp :
            ((⟨W.rootPosition.val + 1, hnext⟩ :
              Fin (topClockSpan n)), W.root) =
              (W.rootPosition, b) :=
          Option.some.inj
            (by simpa only [if_pos rfl, ↓reduceIte] using hmap)
        have hv := congrArg Fin.val (Prod.mk.inj hp).1
        simp only [Fin.val_mk] at hv
        omega
      · have hmapOld :
            W.currentMap h = some (W.rootPosition, b) := by
          simpa only [if_neg hzeroHome] using hmap
        have hne :
            (⟨0, hzero⟩ : Fin (topClockSpan n)) ≠ h := by
          intro heq
          exact hzeroHome heq.symm
        have hdistinct :=
          topFreshTailCohortWaveCurrentHomeDistinct
            ring C s hn Z anchor W
            (⟨0, hzero⟩ : Fin (topClockSpan n)) h hne
            W.rootPosition W.rootPosition W.root b
            W.rootSelected hmapOld
        exact hdistinct rfl
  · have hsame :
        j = (⟨W.rootPosition.val + 1, hnext⟩ :
          Fin (topClockSpan n)) :=
      Fin.ext (by simpa only [Fin.val_mk] using htarget)
    subst j
    have hcarrier : a = W.root := by
      have hp : some W.root = some a :=
        hhop.2.1.symm.trans hslot
      exact (Option.some.inj hp).symm
    subst a
    apply Or.inl
    refine ⟨(⟨0, hzero⟩ : Fin (topClockSpan n)), ?_, ?_⟩
    · simp only [if_pos rfl, ↓reduceIte]
    · have hneq :
          (⟨W.rootPosition.val + 1, hnext⟩ :
            Fin (topClockSpan n)) ≠ W.rootPosition := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_mk] at hv
        omega
      have hnone :=
        W.nextAbsent
          (⟨W.rootPosition.val + 1, hnext⟩ :
            Fin (topClockSpan n))
          (by simp only [Fin.val_mk]; omega)
      simpa only [if_neg hneq] using hnone

/-- The genuine root D(true) hop extends both cohort-selected
maps across one OLD edge. All 24 update obligations are supplied;
row thirteen is deliberately not part of this theorem.
Consumer: Q7c P.3 J5 row-eight one-edge induction. -/
theorem topFreshTailCohortWaveStepRowEight
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s W.rootPosition.val)
    (hnext : W.rootPosition.val + 1 < topClockSpan n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdeparture : (Z.1.1 e).qOut = .D v true)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have hneighbor :
      ring.rightNeighbor e =
        certSite s (W.rootPosition.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite
      ring s W.rootPosition.val
  have hexports := topFreshTailCohortWaveRootHopSilent
    ring C s hn Z anchor W e hsite hnext
  have hactive := topFreshTailCohortWaveRootHopActive
    ring C s hn hbad Z anchor W e hsite hnext
    v hdeparture hempty
  have hhistory := topFreshTailCohortWaveRootHopHistory
    ring C s hn hbad Z anchor W e hsite hnext
    v hdeparture hempty
  have hnextIssue := topFreshTailCohortWaveRootHopNextIssue
    ring C s hn hbad Z anchor W e hsite hnext
    v hdeparture hempty
  have hlistGet :
      ∀ {α : Type} (L M : List α) (hLM : L = M)
        (j : Nat) (hjL : j < L.length) (hjM : j < M.length),
        L[j]'hjL = M[j]'hjM := by
    intro α L M hLM j hjL hjM
    cases hLM
    rfl
  refine topFreshTailCohortWaveUpdate
    ring C s hn hbad Z anchor W e
    (fun t => if t = (⟨0, hzero⟩ : Fin (topClockSpan n)) then
      some ((⟨W.rootPosition.val + 1, hnext⟩ :
        Fin (topClockSpan n)), W.root)
      else W.currentMap t)
    (fun t => if t = W.rootPosition then
      some (topFreshTailGenealogyRearm W.rootPosition
        (Z.1.2.clock + 1) W.root)
      else W.nextMap t)
    W.currentParent W.root
    (⟨W.rootPosition.val + 1, hnext⟩ : Fin (topClockSpan n))
    (fun j => j.val = W.rootPosition.val ∨
      j.val = W.rootPosition.val + 1)
    (fun k => k = (⟨0, hzero⟩ : Fin (topClockSpan n)))
    (fun j => j = W.rootPosition)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: injectivity excludes both changed physical sites.
    intro j hj
    constructor
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j W.rootPosition (heq.trans hsite)
      exact hj (Or.inl (congrArg Fin.val hs))
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j
        (⟨W.rootPosition.val + 1, hnext⟩ :
          Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      exact hj (Or.inr hv)
  · -- hcurrentOff: unchanged current homes retain the old map.
    intro k hk
    simp only [if_neg hk]
  · -- hnextOff: stationary homes other than the new child are unchanged.
    intro j hj
    simp only [if_neg hj]
  · -- hcurrentAway: all other current homes avoid root and successor.
    intro k x a hk hmapK
    have hne :
        (⟨0, hzero⟩ : Fin (topClockSpan n)) ≠ k := by
      intro heq
      exact hk heq.symm
    exact topFreshTailCohortWaveCurrentAway
      ring C s hn Z anchor W
      (⟨0, hzero⟩ : Fin (topClockSpan n)) k hne
      W.rootPosition x W.root a W.rootSelected hmapK
      e hsite hnext hempty
  · -- hnextAway: older next homes lie strictly before the old root.
    intro j hj hbelow
    have hless : j.val < W.rootPosition.val := by
      have hneval : j.val ≠ W.rootPosition.val := by
        intro hv
        exact hj (Fin.ext hv)
      simp only [Fin.val_mk] at hbelow
      omega
    constructor
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j W.rootPosition (heq.trans hsite)
      have hv := congrArg Fin.val hs
      omega
    · intro heq
      have hs := topFreshTailCausalSourceSiteInjective
        s hn j
        (⟨W.rootPosition.val + 1, hnext⟩ :
          Fin (topClockSpan n))
        (by rw [← hneighbor]; exact heq)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      omega
  · -- hcurrentEligibleOff: unchanged export count and original parent.
    intro k _ hbound
    refine ⟨?_, rfl⟩
    simpa only [hexports] using hbound
  · -- hcurrentAbsentOff: identical current-home issued range.
    intro k _ hbound
    simpa only [hexports] using hbound
  · -- hnextEligibleOff: every unmodified next home precedes old root.
    intro j hj hbelow
    refine ⟨?_, rfl⟩
    have hneval : j.val ≠ W.rootPosition.val := by
      intro hv
      exact hj (Fin.ext hv)
    simp only [Fin.val_mk] at hbelow
    omega
  · -- hnextAbsentOff: new root is exactly one position ahead.
    intro j _ hbound
    simp only [Fin.val_mk] at hbound
    omega
  · -- hcurrentChanged: selected root active hop and real history.
    intro k hk _
    subst k
    refine ⟨(⟨W.rootPosition.val + 1, hnext⟩ :
      Fin (topClockSpan n)), W.root, ?_, hactive.1, hhistory⟩
    simp only [if_pos rfl, ↓reduceIte]
  · -- hcurrentChangedAbsent: home zero always remains eligible.
    intro k hk houtside
    subst k
    simp only [Fin.val_mk] at houtside
    have hnonneg :
        0 ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length % topClockSpan n) :=
      Nat.zero_le _
    omega
  · -- hnextChanged: the old root source is the issued next child.
    intro j hj _
    subst j
    exact hnextIssue
  · -- hnextChangedAbsent: the new root is beyond the old source.
    intro j hj habove
    subst j
    simp only [Fin.val_mk] at habove
    omega
  · -- hcurrentOrderChanged: root hop order follows RowSevenOrder.
    intro u w _ huw hbound p q a b hu hw
    exact topFreshTailCohortWaveRootHopOrder
      ring C s hn Z anchor W e hsite hnext hempty
      u w huw hbound p q a b hu hw
  · -- hcurrentChangedSite: changed current zero arrives at root+1.
    intro k j a hk hmapNew
    subst k
    have hp :
        ((⟨W.rootPosition.val + 1, hnext⟩ :
          Fin (topClockSpan n)), W.root) = (j, a) :=
      Option.some.inj
        (by simpa only [if_pos rfl, ↓reduceIte] using hmapNew)
    have hv := congrArg Fin.val (Prod.mk.inj hp).1
    simp only [Fin.val_mk] at hv
    exact Or.inr hv.symm
  · -- hcurrentUnchangedSite: old current zero owns the old root.
    intro j a k hj hmapOld
    intro hk
    subst k
    have hp : (W.rootPosition, W.root) = (j, a) :=
      Option.some.inj (W.rootSelected.symm.trans hmapOld)
    have hv := congrArg Fin.val (Prod.mk.inj hp).1
    exact hj (Or.inl hv.symm)
  · -- hnextUnchangedSite: its only changed index is the old root.
    intro j hj hchange
    exact hj (Or.inl (congrArg Fin.val hchange))
  · -- hsourceChanged: exact child/current partition at both endpoints.
    exact topFreshTailCohortWaveRootHopSourceCoverage
      ring C s hn hbad Z anchor W e hsite hnext
      v hdeparture hempty
  · -- hrootStable: zero is necessarily a changed current home.
    intro hnot
    exact False.elim (hnot rfl)
  · -- hrootChanged: the new current-zero entry selects moved root.
    intro _
    simp only [if_pos rfl, ↓reduceIte]
  · -- hrootKind: active moved root retains its sampled true tail.
    exact Or.inr
      (topFreshTailCohortWaveRootHopKind
        ring C s hn hbad Z anchor W e hsite hnext
        v hdeparture hempty)
  · -- hparentReceipt: historical parent survives silent nonport hop.
    have hp := topFreshTailCohortWaveParentReceiptAppend
      ring C s hn Z anchor e
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n)
      W.currentParent W.currentParentReceipt hexports
    simpa only [hexports] using hp
  · -- hexportOld: unchanged list has the same chronological get.
    intro i hiOld hiNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ hexports i hiNew hiOld
  · -- hexportAdded: a silent hop cannot create a new export index.
    intro i hadded
    have hi := i.isLt
    have hlength := congrArg List.length hexports
    omega

end L3

namespace L3

/-- The true-tail accepted port becomes the positive-generation
historical parent receipt precisely when the previous residue was
the final one. Consumer: J5 row-fourteen cohort renewal. -/
theorem topFreshTailCohortWaveAcceptedParentReceipt
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hbzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) = 0)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent :
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported)
    (htail : exported.tail = true) :
    TopFreshTailCohortHistoricalParent
      ring C s hn (topFixedTraceNext ring C Z e) anchor
      ((topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
        topClockSpan n) W.root := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v true := by
    rw [← hsite]
    exact hdata
  obtain ⟨_, hrootSlot, _⟩ :=
    topFreshTailCohortWaveRowFourteenTerminalParent
      ring C s hn Z anchor W v hterminal hbzero
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.reached.symm
  have hrunClock :
      Z.1.2.clock = Z.2.length := by
    have hc := topFreshTailAuditRunClock ring C Z.2
    rw [hrun] at hc
    exact hc
  obtain ⟨_, _, _, htime, _, _, _, _, _⟩ :=
    topFreshTailAuditSelectedPortFrame
      ring C s Z e exported hevent
  have hexports :=
    topFreshTailCohortWaveAcceptedExports
      ring C s hn Z anchor W e exported hevent
  have hnewCount :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
      (topClockConcreteExportsAfter s
        Z anchor.time).length + 1 := by
    rw [hexports]
    simp
  have hmodLt :
      (topClockConcreteExportsAfter s
        Z anchor.time).length % topClockSpan n <
          topClockSpan n :=
    Nat.mod_lt _ (by omega)
  have hwrap :
      (topClockConcreteExportsAfter s
        Z anchor.time).length % topClockSpan n =
          topClockSpan n - 1 := by
    omega
  have hmodSuccessor :
      ((topClockConcreteExportsAfter s Z anchor.time).length +
        1) % topClockSpan n = 0 := by
    rw [Nat.add_mod, hwrap]
    have hone : 1 % topClockSpan n = 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hone, show topClockSpan n - 1 + 1 =
      topClockSpan n by omega]
    exact Nat.mod_self _
  have hnewMod :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n = 0 := by
    rw [hnewCount]
    exact hmodSuccessor
  have hnewMul :
      ((topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
          topClockSpan n) * topClockSpan n =
        (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length := by
    have hdivision := Nat.mod_add_div
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length
      (topClockSpan n)
    rw [hnewMod] at hdivision
    calc
      _ = topClockSpan n *
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length /
            topClockSpan n) := Nat.mul_comm _ _
      _ = (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length := by
            omega
  have hindex :
      (topClockConcreteExportsAfter s
        Z anchor.time).length =
      ((topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
          topClockSpan n) * topClockSpan n - 1 := by
    omega
  have hgenPositive :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
          topClockSpan n ≠ 0 := by
    intro hzero
    rw [hzero] at hnewMul
    simp only [Nat.zero_mul] at hnewMul
    omega
  have hnewBound :
      (topClockConcreteExportsAfter s Z anchor.time).length <
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length := by
    omega
  have hlastExport :
      topClockConcreteExportAt s
        (topFixedTraceNext ring C Z e) anchor.time
        (⟨(topClockConcreteExportsAfter s Z anchor.time).length,
          hnewBound⟩ : Fin
          (topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e) anchor.time).length) =
        exported := by
    have hgetSnoc :
        ∀ {α : Type} (L M : List α) (a : α)
          (happend : M = L ++ [a])
          (hbound : L.length < M.length),
          M[L.length]'hbound = a := by
      intro α L M a happend hbound
      cases happend
      simp
    change
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time)[(topClockConcreteExportsAfter s Z anchor.time).length]'hnewBound =
          exported
    exact hgetSnoc _ _ _ hexports hnewBound
  unfold TopFreshTailCohortHistoricalParent
  refine ⟨Z.2, [], exported, ?_, ?_, ?_, ?_,
    htail, ?_⟩
  · change Z.2 ++ [e] =
      Z.2 ++ [certSite s (topClockSpan n - 1)]
    rw [hsite]
  · rw [hrun]
    exact hrootSlot
  · rw [hrun, ← hsite]
    exact hevent
  · omega
  · rw [if_neg hgenPositive]
    exact ⟨⟨(topClockConcreteExportsAfter
      s Z anchor.time).length, hnewBound⟩,
      hindex, hlastExport.symm⟩


end L3

namespace L3

/-- At a genuine terminal service every earlier next-cohort
stationary home survives, including its exact OLD issue history
from the accepted full root. Consumer: row-fourteen promotion of
the next family into the new current map. -/
theorem topFreshTailCohortWaveRowFourteenReindexedHome
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hrootAtTerminal :
      W.rootPosition.val = topClockSpan n - 1)
    (j : Fin (topClockSpan n))
    (hj : j.val < topClockSpan n - 1) :
    ∃ a : TopFreshTailCarrier (topClockSpan n),
      W.nextMap j = some a ∧
      TopFreshTailPostAnchorActiveHome ring C s
        (topFixedTraceNext ring C Z e) j j a ∧
      TopFreshTailCohortIssueHistory
        ring C s (Z.2 ++ [e]) j j W.root a := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hrootBefore : j.val < W.rootPosition.val := by
    rw [hrootAtTerminal]
    exact hj
  obtain ⟨a, hmap, hslotOld, hhomeOld, hissued⟩ :=
    W.nextIssued j hrootBefore
  have hpairAway :=
    topFreshTailFirstBorderEarlierSiteOffSelectedPair
      ring s hn j
      (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n)) hj e hsite
  have hframe :=
    topFreshTailCausalOffPairSlotAgreement
      ring C s Z e W.queue j hpairAway.1 hpairAway.2
  have hslotNext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
          some a := by
    rw [hframe.2]
    exact hslotOld
  have hhomeNext :=
    topFreshTailFirstBorderHomeSlotAway
      ring C s Z W.root j e W.queue
      hhomeOld hpairAway.1 hpairAway.2
  obtain ⟨other, hslotOther, hfreshOther, _, hkind⟩ :=
    hhomeNext
  have ha : other = a :=
    Option.some.inj (hslotOther.symm.trans hslotNext)
  rw [ha] at hfreshOther
  have hactive :
      TopFreshTailPostAnchorActiveHome ring C s
        (topFixedTraceNext ring C Z e) j j a := by
    refine ⟨Nat.le_refl _, hslotNext, hfreshOther, ?_⟩
    rcases hkind with hunread |
      ⟨sample, hdata, hrecord, hlane, hsampleSite,
        hsampleValue, hsampleTail, hatom⟩
    · exact Or.inl ⟨rfl, hunread⟩
    · exact Or.inr ⟨sample, hdata, hrecord, hlane,
        hsampleSite, hsampleValue, hsampleTail, hatom⟩
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hrunNext :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hrun]
  have hslotRunOld :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots j =
          some a := by
    rw [hrun]
    exact hslotOld
  have hslotRunNext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots j =
          some a := by
    rw [hrunNext]
    exact hslotNext
  have hhistory :=
    topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 j j W.root a hissued.2 e
      hslotRunOld hslotRunNext
  exact ⟨a, hmap, hactive, hhistory⟩

/-- The reindexed next-family home map is spatially diagonal:
a current entry at home j always occupies physical site j,
including the newly rearmed terminal child. Consumer:
row-fourteen hcurrentOrderChanged. -/
theorem topFreshTailCohortWaveRowFourteenReindexedOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (child : TopFreshTailCarrier (topClockSpan n))
    (u v x y : Fin (topClockSpan n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (huv : u.val < v.val)
    (hu :
      (if u = (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n))
       then some (u, child)
       else (W.nextMap u).map (fun c => (u, c))) =
        some (x, a))
    (hv :
      (if v = (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n))
       then some (v, child)
       else (W.nextMap v).map (fun c => (v, c))) =
        some (y, b)) :
    x.val < y.val := by
  have htop : topClockSpan n - 1 < topClockSpan n := by
    have hr := cert_rho_ge_three n hn
    change 3 ≤ topClockSpan n at hr
    omega
  have hlocation :
      ∀ (j z : Fin (topClockSpan n))
        (c : TopFreshTailCarrier (topClockSpan n)),
        (if j = (⟨topClockSpan n - 1, htop⟩ :
              Fin (topClockSpan n))
         then some (j, child)
         else (W.nextMap j).map (fun d => (j, d))) =
            some (z, c) →
        z = j := by
    intro j z c hmap
    by_cases hterminal :
        j = (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n))
    · simp only [if_pos hterminal] at hmap
      exact (congrArg Prod.fst (Option.some.inj hmap)).symm
    · simp only [if_neg hterminal] at hmap
      cases hm : W.nextMap j with
      | none =>
          simp only [hm, Option.map_none] at hmap
          cases hmap
      | some carrier =>
          simp only [hm, Option.map_some] at hmap
          exact (congrArg Prod.fst (Option.some.inj hmap)).symm
  have hx := hlocation u x a hu
  have hy := hlocation v y b hv
  rw [hx, hy]
  exact huv

/-- A promoted next-family home at source zero supplies the
new current root's genuine unread-or-sampled comparison kind.
Consumer: row-fourteen hrootChanged and hrootKind. -/
theorem topFreshTailCohortWaveRowFourteenRootKind
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hrootAtTerminal :
      W.rootPosition.val = topClockSpan n - 1)
    (root : TopFreshTailCarrier (topClockSpan n))
    (hrootMap :
      W.nextMap
        (⟨0, show 0 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) = some root) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots
        (⟨0, show 0 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) = some root ∧
    (((topFixedTraceNext ring C Z e).1.1
        (certSite s 0)).qOut = .U ∨
      ∃ sample : DigitSample
          (compileAdvice (ceilLogTwo n)) n,
        DigitRecordedSample
          (topFixedTraceNext ring C Z e).1.2 sample ∧
        sample.id.lane = .comparison ∧
        sample.id.site = certSite s 0 ∧
        sample.tail = true ∧
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s 0)).qOut = .D sample.value true ∧
        ((topFixedTraceNext ring C Z e).1.2.current
          (certSite s 0)).comparison.out.atom =
          some (.sampled sample.id)) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hz : 0 < topClockSpan n := by omega
  have hbelow : 0 < topClockSpan n - 1 := by omega
  obtain ⟨a, hmap, hactive, _⟩ :=
    topFreshTailCohortWaveRowFourteenReindexedHome
      ring C s hn Z anchor W e hsite hrootAtTerminal
      (⟨0, hz⟩ : Fin (topClockSpan n)) hbelow
  have ha : a = root :=
    Option.some.inj (hmap.symm.trans hrootMap)
  rw [ha] at hactive
  refine ⟨hactive.2.1, ?_⟩
  rcases hactive.2.2.2 with ⟨_, hunread⟩ |
    ⟨sample, hdata, hrecord, hlane, hsampleSite,
      hsampleValue, hsampleTail, hatom⟩
  · exact Or.inl hunread
  · have htail : sample.tail = true := by
      simpa only [Fin.val_mk, if_true] using hsampleTail
    have hsource :
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s 0)).qOut = .D sample.value true := by
      rw [hsampleValue]
      simpa only [Fin.val_mk, if_true] using hdata
    exact Or.inr ⟨sample, hrecord, hlane,
      hsampleSite, htail, hsource, hatom⟩

/-- After true-tail acceptance the terminal site is reissued
as a fresh current child; every other occupied source belongs
to the promoted old next-family map. This isolates the entire
source-coverage mapping from the export-record obligations.
Consumer: row-fourteen hsourceChanged. -/
theorem topFreshTailCohortWaveRowFourteenSourceCoverage
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hrootAtTerminal :
      W.rootPosition.val = topClockSpan n - 1)
    (child : TopFreshTailCarrier (topClockSpan n))
    (hterminalSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) = some child) :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a →
      ∃ h : Fin (topClockSpan n),
        (if h = (⟨topClockSpan n - 1,
              show topClockSpan n - 1 < topClockSpan n by
                have hr := cert_rho_ge_three n hn
                change 3 ≤ topClockSpan n at hr
                omega⟩ : Fin (topClockSpan n))
         then some (h, child)
         else (W.nextMap h).map (fun b => (h, b))) =
            some (j, a) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  intro j a hslot
  by_cases hterminal :
      j = (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n))
  · subst j
    have ha : a = child :=
      Option.some.inj (hslot.symm.trans hterminalSlot)
    subst a
    refine ⟨(⟨topClockSpan n - 1, htop⟩ :
      Fin (topClockSpan n)), ?_⟩
    simp only [if_pos rfl, ↓reduceIte]
  · have hj : j.val < topClockSpan n - 1 := by
      have hjbound := j.isLt
      have hneq : j.val ≠ topClockSpan n - 1 := by
        intro heq
        exact hterminal (Fin.ext heq)
      omega
    obtain ⟨carrier, hmap, hactive, _⟩ :=
      topFreshTailCohortWaveRowFourteenReindexedHome
        ring C s hn Z anchor W e hsite hrootAtTerminal
        j hj
    have ha : a = carrier :=
      Option.some.inj (hslot.symm.trans hactive.2.1)
    subst a
    refine ⟨j, ?_⟩
    simp only [if_neg hterminal, hmap, Option.map_some]


/-- A reached accepted terminal D(true) with the public port
input/carry guards gives the exact fresh rearm child, authentic
cohort issue, and the recorded home-zero comparison operand of
the newly appended export. Consumer: row-fourteen current-home,
parent receipt, and last export-record obligations. -/
theorem topFreshTailCohortWaveRowFourteenAcceptedChild
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hbzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) = 0)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    ∃ (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
      (sample : DigitSample (compileAdvice (ceilLogTwo n)) n),
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported ∧
      exported.tail = true ∧
      exported.operand = some (.sampled sample.id) ∧
      exported.value = sample.value ∧
      DigitRecordedSample Z.1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site = certSite s 0 ∧
      sample.value = (C (certSite s 0)).d ∧
      sample.tail = true ∧
      TopFreshTailPostAnchorActiveHome ring C s
        (topFixedTraceNext ring C Z e)
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n))
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n))
        (topFreshTailGenealogyRearm
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n))
          (Z.1.2.clock + 1) W.root) ∧
      TopFreshTailCohortIssueHistory ring C s
        (Z.2 ++ [e])
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n))
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n))
        W.root
        (topFreshTailGenealogyRearm
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n))
          (Z.1.2.clock + 1) W.root) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hpositive : topClockSpan n - 1 ≠ 0 := by omega
  have hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v true := by
    rw [← hsite]
    exact hdata
  obtain ⟨hrootPosition, hrootSlot, _⟩ :=
    topFreshTailCohortWaveRowFourteenTerminalParent
      ring C s hn Z anchor W v hterminal hbzero
  have hactive :=
    (topFreshTailCohortWaveRowEightSelectedRootSlot
      ring C s hn Z anchor W).1
  obtain ⟨_, _, hrootFresh, hkind⟩ := hactive
  rcases hkind with ⟨hzeroPos, hsourceUOld⟩ |
    ⟨sample, hsourceD, hrecord, hlane, hsampleSite,
      hsampleValue, hsampleTail, hatom⟩
  · have hz := congrArg Fin.val hzeroPos
    rw [hrootPosition] at hz
    simp only [Fin.val_mk] at hz
    omega
  · have hsourceSample :
        (Z.1.1 e).qOut = .D sample.value true := by
      rw [hrootPosition] at hsourceD
      rw [← hsite] at hsourceD
      rw [hsampleValue]
      simpa only [Fin.val_mk, if_true] using hsourceD
    have hvalueEq : v = sample.value := by
      have hh := hdata.symm.trans hsourceSample
      cases hh
      rfl
    have hsampleTrue : sample.tail = true := by
      simpa only [Fin.val_mk, if_true] using hsampleTail
    have hsourceAtom :
        (Z.1.2.current e).comparison.out.atom =
          some (.sampled sample.id) := by
      rw [hrootPosition] at hatom
      rw [← hsite] at hatom
      exact hatom
    have hgeom :=
      topFreshTailCausalSourcePublicGeometry
        ring C s hn hbad Z W.queue.trace.1
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n))
    have hxl : (Z.1.1 e).l = false := by
      rw [hsite]
      exact hgeom.1
    have hyl :
        (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [hsite]
      exact hgeom.2.1
    have hxb : (Z.1.1 e).beta = false := by
      have hh := hgeom.2.2.1
      rw [if_neg hpositive] at hh
      rw [hsite]
      exact hh
    have hyb :
        (Z.1.1 (ring.rightNeighbor e)).beta = true := by
      have hh := hgeom.2.2.2
      rw [show topClockSpan n - 1 + 1 =
        topClockSpan n by omega] at hh
      simp only [if_pos rfl] at hh
      rw [hsite]
      exact hh
    have hneighbor :
        ring.rightNeighbor e = certSite s (topClockSpan n) := by
      rw [hsite]
      rw [topFreshTailFirstBorderNeighborSite
        ring s (topClockSpan n - 1)]
      rw [show topClockSpan n - 1 + 1 =
        topClockSpan n by omega]
    have htrace := W.queue.trace.2
    obtain ⟨hsourceU, _, _, _, hslotStep, _, _, _,
      hexport⟩ :=
      topFreshTailAcceptedPortQOAllSourceScratch
        ring hn C s (topFreshTailGenealogy ring C s Z)
        e (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n))
        v true W.root hsite
        (show topClockSpan n - 1 + 1 = topClockSpan n by omega)
        hneighbor
        (by rw [htrace]; exact hxl)
        (by rw [htrace]; exact hyl)
        (by rw [htrace]; exact hxb)
        (by rw [htrace]; exact hyb)
        (by rw [htrace]; exact hyi)
        (by rw [htrace]; exact hyc)
        (by rw [htrace]; exact hdata)
        hrootSlot
    have hnewU :
        ((topFixedTraceNext ring C Z e).1.1 e).qOut =
          .U := by
      change ((topFixedTraceNext ring C
        (topFreshTailGenealogy ring C s Z).trace e).1.1 e).qOut =
        .U at hsourceU
      rw [htrace] at hsourceU
      exact hsourceU
    have hslotNext :
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n)) =
          some (topFreshTailGenealogyRearm
            (⟨topClockSpan n - 1, htop⟩ :
              Fin (topClockSpan n))
            (Z.1.2.clock + 1) W.root) := by
      rw [topFreshTailCausalReplayNext]
      have hs := hslotStep
      simp only [ite_true] at hs
      rw [htrace] at hs
      exact hs
    obtain ⟨birth, hrootOrigin⟩ := hrootFresh
    have hchildFresh :
        ∃ stamp : Nat,
          (topFreshTailGenealogyRearm
            (⟨topClockSpan n - 1, htop⟩ :
              Fin (topClockSpan n))
            (Z.1.2.clock + 1) W.root).origin =
              .freshBorder stamp := by
      refine ⟨birth, ?_⟩
      simp [topFreshTailGenealogyRearm, hpositive,
        hrootOrigin]
    have hactiveChild :
        TopFreshTailPostAnchorActiveHome ring C s
          (topFixedTraceNext ring C Z e)
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n))
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n))
          (topFreshTailGenealogyRearm
            (⟨topClockSpan n - 1, htop⟩ :
              Fin (topClockSpan n))
            (Z.1.2.clock + 1) W.root) := by
      refine ⟨Nat.le_refl _, hslotNext, hchildFresh,
        Or.inl ⟨rfl, ?_⟩⟩
      rw [← hsite]
      exact hnewU
    have hissueChild :=
      topFreshTailCohortIssueHistoryAtRearm
        ring C s Z W.queue e
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n))
        v W.root hsite hdata hrootSlot hnewU
    obtain ⟨exported, hevent, _, _, _, _, hoperand,
      hresultValue, hresultTail, _, _⟩ := hexport
    rw [htrace] at hevent hoperand
    refine ⟨exported, sample, hevent, ?_, ?_, ?_,
      hrecord, hlane, hsampleSite, hsampleValue,
      hsampleTrue, hactiveChild, hissueChild⟩
    · simpa only [if_true] using hresultTail
    · exact hoperand.trans hsourceAtom
    · exact hresultValue.trans hvalueEq


end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
J5 row-thirteen / topFreshTailCohortWaveUpdate, 24 obligations:
 1. hsiteAway: source-site injectivity and PortOutsideSource.
 2. hcurrentOff: unchanged map outside the retired home.
 3. hnextOff: nextMap is unchanged.
 4. hcurrentAway: CurrentHomeDistinct and PortOutsideSource.
 5. hnextAway: terminal/root geometry and PortOutsideSource.
 6. hcurrentEligibleOff: accepted-one-export nonwrapping index.
 7. hcurrentAbsentOff: same nonwrapping index, excluding retired home.
 8. hnextEligibleOff: unchanged root and next range.
 9. hnextAbsentOff: unchanged rootPosition.
10. hcurrentChanged: vacuous after retirement, using nonwrapping bound.
11. hcurrentChangedAbsent: if_pos rfl in retired map.
12. hnextChanged: no next entries are changed.
13. hnextChangedAbsent: no next entries are changed.
14. hcurrentOrderChanged: retired map entry is none.
15. hcurrentChangedSite: none at retired map entry.
16. hcurrentUnchangedSite: CurrentHomeDistinct from terminal head.
17. hnextUnchangedSite: nextMap is unchanged.
18. hsourceChanged: accepted source slot is none (accepted helper).
19. hrootStable: positive terminal home is not zero.
20. hrootChanged: contradiction with positive terminal home.
21. hrootKind: RowThirteenRootKindFrame.
22. hparentReceipt: genuine receipt prefix plus nonwrapping quotient.
23. hexportOld: accepted append preserves preceding exports.
24. hexportAdded: accepted port sample/value/tail at new index.

The three lemmas below establish local producers for obligations 3,
5, 8, 9, 12, 13, 17, 18 and 21, plus the accepted-export basis of
22–24. They are not substitutes for the remaining global proofs.
-/

/-- An accepted terminal D(false) retires its exact OLD source slot
and clears its OLD comparison atom. Its one new export comes from the
actual comparison-port service, with no source-side scratch premise.
Consumer: row-thirteen hsourceChanged, export and retirement. -/
theorem topFreshTailCohortWaveRowThirteenAcceptedTerminal
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D value false)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    ∃ (carrier : TopFreshTailCarrier (topClockSpan n))
      (exported : DigitExport (compileAdvice (ceilLogTwo n)) n),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
          (⟨topClockSpan n - 1, show
            topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) = none ∧
      ((topFixedTraceNext ring C Z e).1.1 e).qOut = .E ∧
      ((topFixedTraceNext ring C Z e).1.2.current
        e).comparison.out.atom = none ∧
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported ∧
      topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time ++
          [exported] ∧
      exported.tail = false ∧
      exported.value = value := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have htopFin :
      (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n)).val + 1 =
          topClockSpan n := by
    simp only [Fin.val_mk]
    omega
  have hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D value false := by
    rw [← hsite]
    exact hdata
  obtain ⟨carrier, _, hslot⟩ :=
    W.selectedHead value false hterminal
  have hneighbor :
      ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite, topFreshTailFirstBorderNeighborSite]
    congr 1
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1
      (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  have hxb : (Z.1.1 e).beta = false := by
    have hm := hgeom.2.2.1
    rw [if_neg (show (topClockSpan n - 1) ≠ 0 by omega)] at hm
    rw [hsite]
    exact hm
  have hyb :
      (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    have hm := hgeom.2.2.2
    rw [show (topClockSpan n - 1) + 1 =
      topClockSpan n by omega] at hm
    simp only [if_pos rfl] at hm
    rw [hsite]
    exact hm
  have hghostTrace :
      (topFreshTailGenealogy ring C s Z).trace = Z :=
    W.queue.trace.2
  have hghostLeft :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).l =
        false := by
    rw [hghostTrace]
    exact hxl
  have hghostRight :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hghostTrace]
    exact hyl
  have hghostBX :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).beta =
        false := by
    rw [hghostTrace]
    exact hxb
  have hghostBY :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).beta = true := by
    rw [hghostTrace]
    exact hyb
  have hghostI :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).qIn = .E := by
    rw [hghostTrace]
    exact hyi
  have hghostC :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).qCarry = .OFF := by
    rw [hghostTrace]
    exact hyc
  have hghostData :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
        .D value false := by
    rw [hghostTrace]
    exact hdata
  have hport :=
    topFreshTailAcceptedPortQOAllSourceScratch
      ring hn C s (topFreshTailGenealogy ring C s Z)
      e (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
      value false carrier
      (by simpa only [Fin.val_mk] using hsite)
      htopFin hneighbor hghostLeft hghostRight
      hghostBX hghostBY hghostI hghostC
      hghostData hslot
  obtain ⟨hsourceStep, _, _, _, hslotStep, hatomStep,
    _, _, exported, hevent, _, _, _, _, _,
    hvalueExport, htailExport, _, _⟩ := hport
  have htraceNext :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).trace =
          topFixedTraceNext ring C Z e := by
    rw [← topFreshTailCausalReplayNext]
    exact (topFreshTailCausalQueueStep
      ring C s hn hbad Z e W.queue).trace.2
  have hnewSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n)) = none := by
    rw [topFreshTailCausalReplayNext]
    simpa only [Bool.false_eq_true, ↓reduceIte] using hslotStep
  have hnewOutput :
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .E := by
    rw [← htraceNext]
    simpa only [Bool.false_eq_true, ↓reduceIte] using hsourceStep
  have hnewAtom :
      ((topFixedTraceNext ring C Z e).1.2.current
        e).comparison.out.atom = none := by
    rw [← htraceNext]
    exact hatomStep
  have hportEvent :
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported := by
    rw [← hghostTrace]
    exact hevent
  have hnewExports :=
    topFreshTailCohortWaveAcceptedExports
      ring C s hn Z anchor W e exported hportEvent
  exact ⟨carrier, exported, hnewSlot, hnewOutput,
    hnewAtom, hportEvent, hnewExports,
    htailExport, hvalueExport⟩

/-- Every next-family packet behind the pinned root is off the
terminal source/target pair. Its carrier, sampled home and full
issuer's packet-follow history survive the accepted D(false) edge.
Consumer: row-thirteen nextIssued and hnextAway. -/
theorem topFreshTailCohortWaveRowThirteenNextHistoryFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1)) :
    ∀ j : Fin (topClockSpan n),
      j.val < W.rootPosition.val →
      ∃ a : TopFreshTailCarrier (topClockSpan n),
        W.nextMap j = some a ∧
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots j =
          some a ∧
        TopFreshTailFirstBorderHomeSlot
          ring C s (topFixedTraceNext ring C Z e)
          W.root j ∧
        TopFreshTailCohortIssueHistory ring C s
          (Z.2 ++ [e]) j j W.root a := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hrunNext :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C Z e := by
    rw [topFreshTailFifoRunSnoc, hrun]
  have hneighbor :
      ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite, topFreshTailFirstBorderNeighborSite]
    congr 1
    omega
  intro j hj
  obtain ⟨a, hmap, hslot, hhome, hissued⟩ :=
    W.nextIssued j hj
  have hsourceAway : certSite s j.val ≠ e := by
    intro heq
    have hindex :=
      topFreshTailCohortWaveSourceOffsetUnique s hn j
        (topClockSpan n - 1)
        (by omega) (heq.trans hsite)
    have hk := W.rootPosition.isLt
    omega
  have htargetAway :
      certSite s j.val ≠ ring.rightNeighbor e := by
    rw [hneighbor]
    exact topFreshTailFirstBorderPortOutsideSource s hn j
  have hframe :=
    topFreshTailCausalOffPairSlotAgreement
      ring C s Z e W.queue j hsourceAway htargetAway
  have hslotNext :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
          some a := by
    rw [hframe.2]
    exact hslot
  have hhomeNext :=
    topFreshTailFirstBorderHomeSlotAway
      ring C s Z W.root j e W.queue
      hhome hsourceAway htargetAway
  have holdSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots j =
          some a := by
    rw [hrun]
    exact hslot
  have hnextSlot :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots j =
          some a := by
    rw [hrunNext]
    exact hslotNext
  have hhistoryNext :=
    topFreshTailCohortIssueHistoryAppendStay
      ring C s Z.2 j j W.root a hissued.2
      e holdSlot hnextSlot
  exact ⟨a, hmap, hslotNext, hhomeNext, hhistoryNext⟩

/-- False-tail retirement is strictly after the pinned current
root. Thus source and destination of the accepted OLD port edge
are off the root, framing its unread/sampled-D witness and atom.
Consumer: row-thirteen rootKind and rootSelected. -/
theorem topFreshTailCohortWaveRowThirteenRootKindFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D value false) :
    W.rootPosition.val < topClockSpan n - 1 ∧
    ((W.rootPosition.val = 0 ∧
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s 0)).qOut = .U) ∨
     ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
       DigitRecordedSample
         (topFixedTraceNext ring C Z e).1.2 sample ∧
       sample.id.lane = .comparison ∧
       sample.id.site = certSite s 0 ∧
       sample.tail = true ∧
       ((topFixedTraceNext ring C Z e).1.1
         (certSite s W.rootPosition.val)).qOut =
           .D sample.value true ∧
       ((topFixedTraceNext ring C Z e).1.2.current
         (certSite s W.rootPosition.val)).comparison.out.atom =
           some (.sampled sample.id)) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hb :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n) <
          topClockSpan n := by
    omega
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hterminal :
      (Z.1.1 (certSite s
        (topClockSpan n - 1))).qOut = .D value false := by
    rw [← hsite]
    exact hdata
  have hpositive :=
    topFreshTailCohortWaveFalseTerminalPositiveHome
      ring C s hn Z anchor W value hterminal
  obtain ⟨carrier, hmapHead, _, _⟩ :=
    topFreshTailCohortWaveRowThirteenSelectedHead
      ring C s hn Z anchor W value hterminal
  have hrootLt :=
    topFreshTailCohortWaveCurrentRootPrecedes
      ring C s hn Z anchor W
      (⟨topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n),
        hb⟩ : Fin (topClockSpan n))
      (by simpa only [Fin.val_mk] using hpositive)
      (Nat.le_refl _)
      (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n))
      carrier hmapHead
  have hsourceAway :
      certSite s W.rootPosition.val ≠ e := by
    intro heq
    have hv :=
      topFreshTailCohortWaveSourceOffsetUnique
        s hn W.rootPosition
        (topClockSpan n - 1)
        (by omega) (heq.trans hsite)
    omega
  have hneighbor :
      ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite, topFreshTailFirstBorderNeighborSite]
    congr 1
    omega
  have htargetAway :
      certSite s W.rootPosition.val ≠
        ring.rightNeighbor e := by
    rw [hneighbor]
    exact topFreshTailFirstBorderPortOutsideSource
      s hn W.rootPosition
  have hframe :=
    topFreshTailCausalOffPairSlotAgreement
      ring C s Z e W.queue W.rootPosition
      hsourceAway htargetAway
  refine ⟨hrootLt, ?_⟩
  rcases W.rootKind with ⟨hp, hu⟩ |
    ⟨sample, hrecord, hlane, hsampleSite, htail,
      hrootData, hatom⟩
  · have hframeZero := hframe.1
    rw [hp] at hframeZero
    exact Or.inl ⟨hp, hframeZero.trans hu⟩
  · apply Or.inr
    refine ⟨sample,
      digitRecordedSampleStep
        ring (piD Z.1.1) Z.1.2 e sample hrecord,
      hlane, hsampleSite, htail,
      hframe.1.trans hrootData, ?_⟩
    have hatomFrame :
        ((topFixedTraceNext ring C Z e).1.2.current
          (certSite s W.rootPosition.val)).comparison.out.atom =
        (Z.1.2.current
          (certSite s W.rootPosition.val)).comparison.out.atom := by
      change
        ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
          (certSite s W.rootPosition.val)).comparison.out.atom =
        (Z.1.2.current
          (certSite s W.rootPosition.val)).comparison.out.atom
      simp only [digitAuditStep, digitGhostStep,
        if_neg hsourceAway, if_neg htargetAway]
    exact hatomFrame.trans hatom

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An off-pair scheduler letter prolongs the same actual issue and
packet-follow history at an untouched source, with the same full parent.
Consumer: J5 row-one source/history frame and the common stay step. -/
theorem topFreshTailCohortWaveRowOneOffPairHistory
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (home position : Fin (topClockSpan n))
    (parent carrier : TopFreshTailCarrier (topClockSpan n))
    (hissue : TopFreshTailCohortIssueHistory
      ring C s Z.2 home position parent carrier)
    (hslot :
      (topFreshTailGenealogy ring C s Z).slots position =
        some carrier)
    (e : Fin n)
    (hsource : certSite s position.val ≠ e)
    (htarget :
      certSite s position.val ≠ ring.rightNeighbor e) :
    TopFreshTailCohortIssueHistory ring C s
      (Z.2 ++ [e]) home position parent carrier := by
  have hrun : topFixedTraceRun ring C Z.2 = Z :=
    W.queue.trace.1.symm
  have hframe :=
    (topFreshTailCausalOffPairSlotAgreement
      ring C s Z e W.queue position hsource htarget).2
  have hbefore :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C Z.2)).slots position =
          some carrier := by
    rw [hrun]
    exact hslot
  have hafter :
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (Z.2 ++ [e]))).slots
          position = some carrier := by
    rw [topFreshTailFifoRunSnoc, hrun, hframe]
    exact hslot
  exact topFreshTailCohortIssueHistoryAppendStay
    ring C s Z.2 home position parent carrier
    hissue e hbefore hafter

/-- On a literal edge outside every comparison source, the
post-anchor export list, every physical source output, and every
sampled-D comparison atom are unchanged.
Consumer: J5 row-one FramedStayStep. -/
theorem topFreshTailCohortWaveRowOneOffPairFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (haway :
      ∀ j : Fin (topClockSpan n),
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time ∧
    (∀ j : Fin (topClockSpan n),
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
      (Z.1.1 (certSite s j.val)).qOut) ∧
    (∀ (j : Fin (topClockSpan n))
      (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      (Z.1.1 (certSite s j.val)).qOut = .D value tail →
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have hdisjoint :=
      (haway (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n))).1
    exact hdisjoint (by simpa only [Fin.val_mk] using hp.symm)
  refine ⟨topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort, ?_, ?_⟩
  · intro j
    exact (topFreshTailCausalOffPairSlotAgreement
      ring C s Z e W.queue j (haway j).1 (haway j).2).1
  · intro j value tail _
    change
      ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom
    simp only [digitAuditStep, digitGhostStep,
      if_neg (haway j).1, if_neg (haway j).2]

/-- A scheduler edge disjoint from both endpoints of every
comparison source preserves the complete selected cohort wave.
Consumer: J5 OLD row one. -/
theorem topFreshTailCohortWaveStepRowOne
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (haway :
      ∀ j : Fin (topClockSpan n),
        certSite s j.val ≠ e ∧
        certSite s j.val ≠ ring.rightNeighbor e) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  obtain ⟨hexports, houtputs, hatoms⟩ :=
    topFreshTailCohortWaveRowOneOffPairFrame
      ring C s hn Z anchor W e haway
  exact topFreshTailCohortWaveFramedStayStep
    ring C s hn hbad Z anchor W e hexports houtputs hatoms

/-- A leaderless incoming OLD service at comparison source zero
does not overwrite its selected U/D responder. For a sampled D
the exact comparison atom is also preserved.
Consumer: J5 row-two global physical/atom frame. -/
theorem topFreshTailCohortWaveRowTwoIncomingZeroResponderFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hincoming : ring.rightNeighbor e = certSite s 0) :
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s 0)).qOut = (Z.1.1 (certSite s 0)).qOut ∧
    (∀ (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      (Z.1.1 (certSite s 0)).qOut = .D value tail →
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s 0)).comparison.out.atom =
      (Z.1.2.current (certSite s 0)).comparison.out.atom) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have hnotEmpty :=
    topFreshTailCohortWaveRowFourZeroOccupied
      ring C s hn Z anchor W
  obtain ⟨carrier, hslot⟩ :=
    topFreshTailCausalOccupiedHasCarrier
      ring C s Z W.queue
      (⟨0, hzero⟩ : Fin (topClockSpan n))
      (by simpa only [Fin.val_mk] using hnotEmpty)
  have htarget :
      ring.rightNeighbor e =
        certSite s (⟨0, hzero⟩ : Fin (topClockSpan n)).val := by
    simpa only [Fin.val_mk] using hincoming
  cases hq : (Z.1.1 (certSite s 0)).qOut with
  | E =>
      exact False.elim (hnotEmpty hq)
  | U =>
      have hunread :
          (Z.1.1 (certSite s
            (⟨0, hzero⟩ : Fin (topClockSpan n)).val)).qOut =
              .U := by
        simpa only [Fin.val_mk] using hq
      obtain ⟨hout, _⟩ :=
        topFreshTailFirstBorderIncomingUnreadFrame
          ring C s hn Z e W.queue hl
          (⟨0, hzero⟩ : Fin (topClockSpan n))
          htarget hunread carrier hslot
      constructor
      · simpa only [Fin.val_mk] using hout
      · intro value tail hdata
        cases hdata
  | D value tail =>
      have hdata :
          (Z.1.1 (certSite s
            (⟨0, hzero⟩ : Fin (topClockSpan n)).val)).qOut =
              .D value tail := by
        simpa only [Fin.val_mk] using hq
      obtain ⟨hout, _, hatom⟩ :=
        topFreshTailFirstBorderIncomingDataFrame
          ring C s hn Z e W.queue hl
          (⟨0, hzero⟩ : Fin (topClockSpan n))
          htarget value tail hdata carrier hslot
      constructor
      · simpa only [Fin.val_mk] using hout
      · intro _ _ _
        simpa only [Fin.val_mk] using hatom

/-- The external incoming zero-responder row with global
leaderlessness keeps all comparison source outputs, all old
sampled D atoms, and the filtered port-export list.
Consumer: J5 row-two FramedStayStep and issue-history framing. -/
theorem topFreshTailCohortWaveRowTwoIncomingZeroGlobalFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hincoming : ring.rightNeighbor e = certSite s 0) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time ∧
    (∀ j : Fin (topClockSpan n),
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
      (Z.1.1 (certSite s j.val)).qOut) ∧
    (∀ (j : Fin (topClockSpan n))
      (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      (Z.1.1 (certSite s j.val)).qOut = .D value tail →
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s j.val)).comparison.out.atom =
      (Z.1.2.current (certSite s j.val)).comparison.out.atom) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hsourceAway :=
    topFreshTailFirstBorderIncomingZeroOutsideSource
      ring s hn e hincoming
  have htargetAway :
      ∀ j : Fin (topClockSpan n), j.val ≠ 0 →
        certSite s j.val ≠ ring.rightNeighbor e := by
    intro j hj heq
    have hs :=
      topFreshTailCausalSourceSiteInjective s hn j
        (⟨0, hzero⟩ : Fin (topClockSpan n))
        (by simpa only [Fin.val_mk] using heq.trans hincoming)
    have hv := congrArg Fin.val hs
    simp only [Fin.val_mk] at hv
    exact hj hv
  have hzeroFrame :=
    topFreshTailCohortWaveRowTwoIncomingZeroResponderFrame
      ring C s hn hl Z anchor W e hincoming
  have hnotPort : e ≠ certSite s (topClockSpan n - 1) := by
    intro hp
    have hd :=
      hsourceAway (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n))
    exact hd (by simpa only [Fin.val_mk] using hp.symm)
  refine ⟨topFreshTailCohortWaveNonPortExports
    ring C s Z anchor e hnotPort, ?_, ?_⟩
  · intro j
    by_cases hj : j.val = 0
    · have heq : j =
          (⟨0, hzero⟩ : Fin (topClockSpan n)) := Fin.ext hj
      rw [heq]
      simpa only [Fin.val_mk] using hzeroFrame.1
    · exact (topFreshTailCausalOffPairSlotAgreement
        ring C s Z e W.queue j
        (hsourceAway j) (htargetAway j hj)).1
  · intro j value tail hdata
    by_cases hj : j.val = 0
    · have heq : j =
          (⟨0, hzero⟩ : Fin (topClockSpan n)) := Fin.ext hj
      rw [heq] at hdata ⊢
      have hd :
          (Z.1.1 (certSite s 0)).qOut = .D value tail := by
        simpa only [Fin.val_mk] using hdata
      simpa only [Fin.val_mk] using hzeroFrame.2 value tail hd
    · change
        ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
          (certSite s j.val)).comparison.out.atom =
        (Z.1.2.current (certSite s j.val)).comparison.out.atom
      simp only [digitAuditStep, digitGhostStep,
        if_neg (hsourceAway j), if_neg (htargetAway j hj)]

/-- The incoming source-zero responder is a stay step provided
the OLD public configuration is globally leaderless.
Consumer: J5 OLD row two. -/
theorem topFreshTailCohortWaveStepRowTwo
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hincoming : ring.rightNeighbor e = certSite s 0) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  obtain ⟨hexports, houtputs, hatoms⟩ :=
    topFreshTailCohortWaveRowTwoIncomingZeroGlobalFrame
      ring C s hn hl Z anchor W e hincoming
  exact topFreshTailCohortWaveFramedStayStep
    ring C s hn hbad Z anchor W e hexports houtputs hatoms

/-- An OLD empty output at the terminal comparison source
cannot make a port export, regardless of target input/carry.
The nonterminal export lemma does not apply at this site.
Consumer: J5 row-three terminal-E export-count frame. -/
theorem topFreshTailCohortWaveRowThreeEmptyPortSilent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hsource : (Z.1.1 e).qOut = .E) :
    topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1
      (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    simpa only [Fin.val_mk] using hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    simpa only [Fin.val_mk] using hgeom.2.1
  have hnoExport :
      ∀ {c : Compiled} {m : Nat}
        (time : Nat) (source destination : Fin m)
        (x y : DigitLaneView c) (gx gy : DigitLaneGhost c m),
        x.leader = false →
        y.leader = false →
        x.out = .E →
        (digitLaneReplay .comparison time source destination
          x y gx gy).exported = none := by
    intro c m time source destination x y gx gy hx hy he
    simp [digitLaneReplay, hx, hy, he,
      OutTok.isD, OutTok.isE, OutTok.isU]
  have hnone :
      (digitReceiptLane .comparison
        (topFreshTailPostAnchorCurrentFrame
          ring Z e).receipt).exported = none := by
    change
      (digitLaneReplay .comparison (Z.1.2.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison (piD Z.1.1 e)
          (piD Z.1.1 e).word.beta)
        (digitLaneView .comparison
          (piD Z.1.1 (ring.rightNeighbor e))
          (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported =
          none
    apply hnoExport
    · exact hxl
    · exact hyl
    · exact hsource
  have hnil :
      topFreshTailPostAnchorNewEntries ring s Z anchor.time e = [] := by
    simp [topFreshTailPostAnchorNewEntries, hnone]
  rw [topFreshTailPostAnchorExportsAfterStep, hnil]
  simp only [List.append_nil]

/-- Nonmarker E is physically inert even on an occupied
responder: it leaves all comparison source outputs and all
sampled-D atoms unchanged, while its own genealogy slot is
none. These frames retain the entire exclusive sourceCoverage
partition through FramedStayStep.
Consumer: J5 row-three global site/coverage frame. -/
theorem topFreshTailCohortWaveRowThreeNonmarkerGlobalFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (e : Fin n)
    (hsite : e = certSite s j.val)
    (hsource : (Z.1.1 e).qOut = .E) :
    (∀ p : Fin (topClockSpan n),
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s p.val)).qOut =
      (Z.1.1 (certSite s p.val)).qOut) ∧
    (∀ (p : Fin (topClockSpan n))
      (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      (Z.1.1 (certSite s p.val)).qOut = .D value tail →
      ((topFixedTraceNext ring C Z e).1.2.current
        (certSite s p.val)).comparison.out.atom =
      (Z.1.2.current (certSite s p.val)).comparison.out.atom) ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = none := by
  have hgeom :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z W.queue.trace.1 j
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeom.2.1
  obtain ⟨hsourceStay, hsourceNone⟩ :=
    topFreshTailCohortWaveRowThreeNonmarkerEmptySource
      ring C s hn hbad Z anchor W j hpositive e hsite hsource
  have hneighbor :
      ring.rightNeighbor e = certSite s (j.val + 1) := by
    rw [hsite]
    exact topFreshTailFirstBorderNeighborSite ring s j.val
  have hresponderOutput :
      ((topFixedTraceNext ring C Z e).1.1
        (ring.rightNeighbor e)).qOut =
      (Z.1.1 (ring.rightNeighbor e)).qOut := by
    have hphysical :=
      topFreshTailCausalResponderPhysicalOutput
        ring (by omega : 2 ≤ n) C Z e
    simpa [hxl, hyl, hsource, OutTok.isD] using hphysical
  have hsourceAway :
      ∀ p : Fin (topClockSpan n), p.val ≠ j.val →
        certSite s p.val ≠ e := by
    intro p hp heq
    have hs := topFreshTailCausalSourceSiteInjective
      s hn p j (heq.trans hsite)
    exact hp (congrArg Fin.val hs)
  have htargetAway :
      ∀ p : Fin (topClockSpan n), p.val ≠ j.val + 1 →
        certSite s p.val ≠ ring.rightNeighbor e := by
    intro p hp heq
    by_cases hinternal : j.val + 1 < topClockSpan n
    · have hs :=
        topFreshTailCausalSourceSiteInjective s hn p
          (⟨j.val + 1, hinternal⟩ : Fin (topClockSpan n))
          (by simpa only [Fin.val_mk] using heq.trans hneighbor)
      have hv := congrArg Fin.val hs
      simp only [Fin.val_mk] at hv
      exact hp hv
    · have hport : j.val + 1 = topClockSpan n := by
        have hj := j.isLt
        omega
      have hportSite :
          certSite s p.val = certSite s (topClockSpan n) := by
        rw [heq, hneighbor, hport]
      exact (topFreshTailFirstBorderPortOutsideSource s hn p)
        hportSite
  refine ⟨?_, ?_, hsourceNone⟩
  · intro p
    by_cases hpj : p.val = j.val
    · have heq : p = j := Fin.ext hpj
      rw [heq, ← hsite]
      rw [hsourceStay, hsource]
    · by_cases hpsucc : p.val = j.val + 1
      · have htarget :
            ring.rightNeighbor e = certSite s p.val := by
          rw [hneighbor, hpsucc]
        rw [← htarget]
        exact hresponderOutput
      · exact (topFreshTailCausalOffPairSlotAgreement
          ring C s Z e W.queue p
          (hsourceAway p hpj) (htargetAway p hpsucc)).1
  · intro p value tail hdata
    by_cases hpj : p.val = j.val
    · have heq : p = j := Fin.ext hpj
      rw [heq, ← hsite, hsource] at hdata
      cases hdata
    · by_cases hpsucc : p.val = j.val + 1
      · have htarget :
            ring.rightNeighbor e = certSite s p.val := by
          rw [hneighbor, hpsucc]
        have hd :
            (Z.1.1 (ring.rightNeighbor e)).qOut =
              .D value tail := by
          rw [htarget]
          exact hdata
        have hatom :=
          (topFreshTailAuditPhysicalResponderDataKeep
            ring (by omega : 2 ≤ n) C Z e value tail
            hxl hyl hd).2
        rw [← htarget]
        exact hatom
      · change
          ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
            (certSite s p.val)).comparison.out.atom =
          (Z.1.2.current (certSite s p.val)).comparison.out.atom
        simp only [digitAuditStep, digitGhostStep,
          if_neg (hsourceAway p hpj),
          if_neg (htargetAway p hpsucc)]

/-- A nonmarker source with OLD output E is a stationary
selected-cohort wave edge, including the terminal E case.
Consumer: J5 OLD row three. -/
theorem topFreshTailCohortWaveStepRowThree
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (e : Fin n)
    (hsite : e = certSite s j.val)
    (hsource : (Z.1.1 e).qOut = .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hexports :
      topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time := by
    by_cases hport : j.val + 1 = topClockSpan n
    · have hlast : j.val = topClockSpan n - 1 := by
        have hj := j.isLt
        omega
      have hportSite :
          e = certSite s (topClockSpan n - 1) := by
        simpa only [hlast] using hsite
      exact topFreshTailCohortWaveRowThreeEmptyPortSilent
        ring C s hn hbad Z anchor W e hportSite hsource
    · have hnotPort :
          e ≠ certSite s (topClockSpan n - 1) := by
        intro hp
        have hs := topFreshTailCausalSourceSiteInjective
          s hn j
          (⟨topClockSpan n - 1, htop⟩ : Fin (topClockSpan n))
          (by rw [← hsite]; exact hp)
        have hv := congrArg Fin.val hs
        simp only [Fin.val_mk] at hv
        omega
      exact topFreshTailCohortWaveNonPortExports
        ring C s Z anchor e hnotPort
  obtain ⟨houtputs, hatoms, _⟩ :=
    topFreshTailCohortWaveRowThreeNonmarkerGlobalFrame
      ring C s hn hbad Z anchor W j hpositive e hsite hsource
  exact topFreshTailCohortWaveFramedStayStep
    ring C s hn hbad Z anchor W e hexports houtputs hatoms

/-- The marker-zero empty-source predecessor contradicts the
selected current root or the stationary next home at zero.
Consumer: J5 OLD row four. -/
theorem topFreshTailCohortWaveStepRowFour
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s 0)
    (hsource : (Z.1.1 e).qOut = .E) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  exact topFreshTailCohortWaveRowFourMarkerBootstrap
    ring C s hn Z anchor W e hsite hsource

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The accepted false-tail terminal head has an actual OLD home-b
comparison sample. The genuine NEW port export carries that very
sampled ID, value and false tail, and the sample stays recorded.
Consumer: row-thirteen hexportAdded and chronological wave records. -/
theorem topFreshTailCohortWaveRowThirteenAcceptedSample
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D value false)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    ∃ (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
      (sample : DigitSample (compileAdvice (ceilLogTwo n)) n),
      topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time ++ [exported] ∧
      DigitRecordedSample
        (topFixedTraceNext ring C Z e).1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site =
        certSite s (topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n)) ∧
      sample.value =
        (C (certSite s (topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n)))).d ∧
      sample.tail = false ∧
      exported.operand = some (.sampled sample.id) ∧
      exported.value = sample.value ∧
      exported.tail = sample.tail := by
  have hr : 3 ≤ topClockSpan n :=
    cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hb :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n) <
        topClockSpan n := by
    omega
  have hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D value false := by
    rw [← hsite]
    exact hdata
  have hpositive :=
    topFreshTailCohortWaveFalseTerminalPositiveHome
      ring C s hn Z anchor W value hterminal
  obtain ⟨carrier, hmap, hactive, _⟩ :=
    topFreshTailCohortWaveRowThirteenSelectedHead
      ring C s hn Z anchor W value hterminal
  obtain ⟨_, exported, _, _, _, hevent, happend, hfalse,
      hvalue⟩ :=
    topFreshTailCohortWaveRowThirteenAcceptedTerminal
      ring C s hn hbad Z anchor W e hsite value hdata
      hyi hyc
  rcases hactive.2.2.2 with ⟨_, hunread⟩ |
      ⟨sample, hsampleData, hrecord, hlane, hsampleSite,
        hsampleValue, hsampleTail, hsampleAtom⟩
  · have hnotU :
        (Z.1.1 (certSite s
          (topClockSpan n - 1))).qOut = .U := by
      simpa only [Fin.val_mk] using hunread
    rw [hterminal] at hnotU
    cases hnotU
  · have hnotZero :
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n) ≠ 0 := by
      omega
    have hsampleFalse : sample.tail = false := by
      simpa only [Fin.val_mk, if_neg hnotZero]
        using hsampleTail
    have hsourceSample :
        (Z.1.1 e).qOut = .D sample.value false := by
      have hs := hsampleData
      rw [← hsampleValue] at hs
      rw [hsite]
      simpa only [Fin.val_mk, if_neg hnotZero] using hs
    have hvalueEq : value = sample.value := by
      have hd := hdata.symm.trans hsourceSample
      cases hd
      rfl
    have hsourceAtom :
        (Z.1.2.current e).comparison.out.atom =
          some (.sampled sample.id) := by
      rw [hsite]
      simpa only [Fin.val_mk] using hsampleAtom
    obtain ⟨_, _, _, _, _, _, _, hoperand, _⟩ :=
      topFreshTailAuditSelectedPortFrame
        ring C s Z e exported hevent
    refine ⟨exported, sample, happend,
      digitRecordedSampleStep
        ring (piD Z.1.1) Z.1.2 e sample hrecord,
      hlane, ?_, ?_, hsampleFalse,
      hoperand.trans hsourceAtom, ?_, ?_⟩
    · simpa only [Fin.val_mk] using hsampleSite
    · simpa only [Fin.val_mk] using hsampleValue
    · exact hvalue.trans hvalueEq
    · exact hfalse.trans hsampleFalse.symm

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A real accepted export at a zero terminal home wraps the
chronological count to the next complete cohort. Consumer:
row-fourteen current eligibility, parent generation and added record. -/
theorem topFreshTailCohortWaveRowFourteenWrappedIndex
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hbzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) = 0)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent :
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported) :
    (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n + 1) * topClockSpan n ∧
    (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
          topClockSpan n =
      (topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n + 1 ∧
    (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n = 0 ∧
    topClockSpan n - 1 -
      ((topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n) = topClockSpan n - 1 ∧
    (topClockConcreteExportsAfter s Z anchor.time).length %
      topClockSpan n = topClockSpan n - 1 := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hpos : 0 < topClockSpan n := by omega
  have hexports :=
    topFreshTailCohortWaveAcceptedExports
      ring C s hn Z anchor W e exported hevent
  have hnewCount :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
      (topClockConcreteExportsAfter s Z anchor.time).length + 1 := by
    rw [hexports]
    simp
  have hmodLt :
      (topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n < topClockSpan n :=
    Nat.mod_lt _ hpos
  have hmod :
      (topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n = topClockSpan n - 1 := by
    omega
  have hdivision := Nat.mod_add_div
    (topClockConcreteExportsAfter s Z anchor.time).length
    (topClockSpan n)
  rw [hmod] at hdivision
  have hmultiple :
      (topClockConcreteExportsAfter s Z anchor.time).length + 1 =
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n + 1) * topClockSpan n := by
    calc
      _ = topClockSpan n *
          ((topClockConcreteExportsAfter s Z anchor.time).length /
            topClockSpan n) + topClockSpan n := by
          omega
      _ = ((topClockConcreteExportsAfter s Z anchor.time).length /
          topClockSpan n + 1) * topClockSpan n := by
          simp only [Nat.add_mul, Nat.one_mul]
          rw [Nat.mul_comm (topClockSpan n)
            ((topClockConcreteExportsAfter s Z anchor.time).length /
              topClockSpan n)]
  have hnewMultiple :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
      ((topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n + 1) * topClockSpan n := by
    rw [hnewCount]
    exact hmultiple
  have hnewQuot :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
          topClockSpan n =
      (topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n + 1 := by
    rw [hnewCount, hmultiple,
      Nat.mul_comm
        ((topClockConcreteExportsAfter s Z anchor.time).length /
          topClockSpan n + 1) (topClockSpan n)]
    exact Nat.mul_div_cancel_left _ hpos
  have hmodSucc :
      ((topClockConcreteExportsAfter s Z anchor.time).length + 1) %
        topClockSpan n = 0 := by
    rw [Nat.add_mod, hmod]
    have hone : 1 % topClockSpan n = 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hone, show topClockSpan n - 1 + 1 =
      topClockSpan n by omega]
    exact Nat.mod_self _
  have hnewMod :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n = 0 := by
    rw [hnewCount]
    exact hmodSucc
  refine ⟨hnewMultiple, hnewQuot, hnewMod, ?_, hmod⟩
  rw [hnewMod]
  rfl

/-- All earlier concrete export records survive an actual accepted
append, at the same Nat position with independent Fin bounds.
Consumer: row-fourteen hexportOld. -/
theorem topFreshTailCohortWaveRowFourteenOldExportAt
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent :
      topFreshTailGenealogyPortExport ring C s Z e =
        some exported)
    (i : Nat)
    (hiOld :
      i < (topClockConcreteExportsAfter s Z anchor.time).length)
    (hiNew :
      i < (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length) :
    topClockConcreteExportAt s
      (topFixedTraceNext ring C Z e) anchor.time
      (⟨i, hiNew⟩ : Fin
        (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time).length) =
    topClockConcreteExportAt s Z anchor.time
      (⟨i, hiOld⟩ : Fin
        (topClockConcreteExportsAfter s Z anchor.time).length) := by
  have hexports :=
    topFreshTailCohortWaveAcceptedExports
      ring C s hn Z anchor W e exported hevent
  have hleft :
      ∀ {α : Type} (xs ys : List α) (a : α)
        (happend : ys = xs ++ [a])
        (j : Nat) (hjOld : j < xs.length)
        (hjNew : j < ys.length),
        ys[j]'hjNew = xs[j]'hjOld := by
    intro α xs ys a happend j hjOld hjNew
    cases happend
    simp [List.getElem_append, hjOld]
  unfold topClockConcreteExportAt
  exact hleft _ _ _ hexports i hiOld hiNew

/-- The unique newly appended concrete export is a real recorded
home-zero comparison sample with the wraparound true-tail bit.
Consumer: row-fourteen hexportAdded. -/
theorem topFreshTailCohortWaveRowFourteenAddedRecord
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hbzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) = 0)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    ∀ i : Fin (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length,
      (topClockConcreteExportsAfter s Z anchor.time).length ≤
        i.val →
      ∃ sample : DigitSample
          (compileAdvice (ceilLogTwo n)) n,
        DigitRecordedSample
          (topFixedTraceNext ring C Z e).1.2 sample ∧
        sample.id.lane = .comparison ∧
        sample.id.site =
          certSite s
            (topClockSpan n - 1 - (i.val % topClockSpan n)) ∧
        sample.value =
          (C (certSite s
            (topClockSpan n - 1 -
              (i.val % topClockSpan n)))).d ∧
        sample.tail =
          (if i.val % topClockSpan n = topClockSpan n - 1
            then true else false) ∧
        (topClockConcreteExportAt s
          (topFixedTraceNext ring C Z e) anchor.time i).operand =
            some (.sampled sample.id) ∧
        (topClockConcreteExportAt s
          (topFixedTraceNext ring C Z e) anchor.time i).value =
            sample.value ∧
        (topClockConcreteExportAt s
          (topFixedTraceNext ring C Z e) anchor.time i).tail =
            sample.tail := by
  obtain ⟨exported, sample, hevent, htail, hoperand, hvalue,
      hrecord, hlane, hsampleSite, hdigit, hsampleTail, _, _⟩ :=
    topFreshTailCohortWaveRowFourteenAcceptedChild
      ring C s hn hbad Z anchor W e hsite v hdata hbzero hyi hyc
  obtain ⟨_, _, _, _, holdMod⟩ :=
    topFreshTailCohortWaveRowFourteenWrappedIndex
      ring C s hn Z anchor W e hbzero exported hevent
  have hexports :=
    topFreshTailCohortWaveAcceptedExports
      ring C s hn Z anchor W e exported hevent
  have hnewCount :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
      (topClockConcreteExportsAfter s Z anchor.time).length + 1 := by
    rw [hexports]
    simp
  have hgetLast :
      ∀ {α : Type} (xs ys : List α) (a : α)
        (happend : ys = xs ++ [a])
        (j : Nat) (hj : j < ys.length)
        (hlast : j = xs.length),
        ys[j]'hj = a := by
    intro α xs ys a happend j hj hlast
    subst j
    cases happend
    simp
  intro i hiAdded
  have hiValue :
      i.val = (topClockConcreteExportsAfter s Z anchor.time).length := by
    have hiBound := i.isLt
    omega
  have hiMod :
      i.val % topClockSpan n = topClockSpan n - 1 := by
    rw [hiValue]
    exact holdMod
  have hiHome :
      topClockSpan n - 1 - (i.val % topClockSpan n) = 0 := by
    rw [hiMod]
    omega
  have hentry :
      topClockConcreteExportAt s
        (topFixedTraceNext ring C Z e) anchor.time i =
          exported := by
    change
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time)[i.val]'i.isLt =
          exported
    exact hgetLast _ _ _ hexports i.val i.isLt hiValue
  refine ⟨sample, ?_, hlane, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact digitRecordedSampleStep
      ring (piD Z.1.1) Z.1.2 e sample hrecord
  · rw [hiHome]
    exact hsampleSite
  · rw [hiHome]
    exact hdigit
  · rw [hiMod]
    simpa using hsampleTail
  · rw [hentry]
    exact hoperand
  · rw [hentry]
    exact hvalue
  · rw [hentry, htail, hsampleTail]

/-- A genuine terminal true-tail acceptance promotes every old next
home to the new current family and appends its new terminal child.
Consumer: Q7c P.3 J5 accepted wraparound row. -/
theorem topFreshTailCohortWaveStepRowFourteen
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D v true)
    (hbzero :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter
          s Z anchor.time).length % topClockSpan n) = 0)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hbelow : 0 < topClockSpan n - 1 := by omega
  have hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D v true := by
    rw [← hsite]
    exact hdata
  obtain ⟨hrootAtTerminal, _, _⟩ :=
    topFreshTailCohortWaveRowFourteenTerminalParent
      ring C s hn Z anchor W v hterminal hbzero
  obtain ⟨root, hrootMap, _, _, _⟩ :=
    W.nextIssued (⟨0, hzero⟩ : Fin (topClockSpan n))
      (by rw [hrootAtTerminal]; exact hbelow)
  obtain ⟨exported, sample, hevent, htail, hoperand, hvalue,
      hrecord, hlane, hsampleSite, hdigit, hsampleTail,
      hactiveChild, hhistoryChild⟩ :=
    topFreshTailCohortWaveRowFourteenAcceptedChild
      ring C s hn hbad Z anchor W e hsite v hdata hbzero hyi hyc
  obtain ⟨_, _, _, hnewTerminal, _⟩ :=
    topFreshTailCohortWaveRowFourteenWrappedIndex
      ring C s hn Z anchor W e hbzero exported hevent
  have hnotTerminal :
      (⟨0, hzero⟩ : Fin (topClockSpan n)) ≠
      (⟨topClockSpan n - 1, htop⟩ :
        Fin (topClockSpan n)) := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_mk] at hv
    omega
  refine topFreshTailCohortWaveUpdate
    ring C s hn hbad Z anchor W e
    (fun h =>
      if h = (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)) then
        some (h, topFreshTailGenealogyRearm
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n))
          (Z.1.2.clock + 1) W.root)
      else (W.nextMap h).map (fun a => (h, a)))
    (fun _ => none)
    W.root root (⟨0, hzero⟩ : Fin (topClockSpan n))
    (fun _ => True) (fun _ => True) (fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- 1 hsiteAway: the full source mask has no complement.
    intro j hj
    exact False.elim (hj trivial)
  · -- 2 hcurrentOff: every current home is marked changed.
    intro h hh
    exact False.elim (hh trivial)
  · -- 3 hnextOff: every next home is marked changed.
    intro j hj
    exact False.elim (hj trivial)
  · -- 4 hcurrentAway: no current home is outside the mask.
    intro h x a hh _
    exact False.elim (hh trivial)
  · -- 5 hnextAway: no next home is outside the mask.
    intro j hj _
    exact False.elim (hj trivial)
  · -- 6 hcurrentEligibleOff: all current indices are reinterpreted.
    intro h hh _
    exact False.elim (hh trivial)
  · -- 7 hcurrentAbsentOff: no current index retains the old bound.
    intro h hh _
    exact False.elim (hh trivial)
  · -- 8 hnextEligibleOff: no unchanged next-family parent is required.
    intro j hj _
    exact False.elim (hj trivial)
  · -- 9 hnextAbsentOff: every next entry is cleared.
    intro j hj _
    exact False.elim (hj trivial)
  · -- 10 hcurrentChanged: promote old next homes and issue terminal child.
    intro h _ _
    by_cases hlast :
        h = (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n))
    · subst h
      refine ⟨(⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)),
        topFreshTailGenealogyRearm
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n))
          (Z.1.2.clock + 1) W.root,
        ?_, hactiveChild, hhistoryChild⟩
      exact if_pos rfl
    · have hnotLast : h.val ≠ topClockSpan n - 1 := by
        intro heq
        exact hlast (Fin.ext heq)
      have hj : h.val < topClockSpan n - 1 := by
        have hh := h.isLt
        omega
      obtain ⟨a, hmap, hactiveHome, hhistoryHome⟩ :=
        topFreshTailCohortWaveRowFourteenReindexedHome
          ring C s hn Z anchor W e hsite hrootAtTerminal h hj
      refine ⟨h, a, ?_, hactiveHome, hhistoryHome⟩
      simp only [if_neg hlast, hmap, Option.map_some]
  · -- 11 hcurrentChangedAbsent: wrapped issued range is all homes.
    intro h _ houtside
    rw [hnewTerminal] at houtside
    have hh := h.isLt
    exact False.elim (by omega)
  · -- 12 hnextChanged: the new root position is zero.
    intro j _ hbelowRoot
    exact False.elim (Nat.not_lt_zero _ hbelowRoot)
  · -- 13 hnextChangedAbsent: the new next map is everywhere none.
    intro j _ _
    rfl
  · -- 14 hcurrentOrderChanged: all promoted positions are diagonal.
    intro h i _ hless _ x y a b hx hy
    exact topFreshTailCohortWaveRowFourteenReindexedOrder
      ring C s hn Z anchor W
      (topFreshTailGenealogyRearm
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n))
        (Z.1.2.clock + 1) W.root)
      h i x y a b hless hx hy
  · -- 15 hcurrentChangedSite: every physical site is changed.
    intro h j a _ _
    trivial
  · -- 16 hcurrentUnchangedSite: there is no unchanged physical site.
    intro j a h hj _
    exact False.elim (hj trivial)
  · -- 17 hnextUnchangedSite: there is no unchanged physical site.
    intro j hj
    exact False.elim (hj trivial)
  · -- 18 hsourceChanged: every occupied slot belongs to new current.
    intro j a _ hslot
    obtain ⟨h, hmap⟩ :=
      topFreshTailCohortWaveRowFourteenSourceCoverage
        ring C s hn Z anchor W e hsite hrootAtTerminal
        (topFreshTailGenealogyRearm
          (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n))
          (Z.1.2.clock + 1) W.root)
        hactiveChild.2.1 j a hslot
    exact Or.inl ⟨h, hmap, rfl⟩
  · -- 19 hrootStable: the old current root is marked changed.
    intro hh
    exact False.elim (hh trivial)
  · -- 20 hrootChanged: the promoted stationary home zero is new root.
    intro _
    simp only [if_neg hnotTerminal, hrootMap, Option.map_some]
  · -- 21 hrootKind: the promoted home-zero root is unread or sampled.
    have hkind :=
      (topFreshTailCohortWaveRowFourteenRootKind
        ring C s hn Z anchor W e hsite hrootAtTerminal
        root hrootMap).2
    rcases hkind with hunread | hsampled
    · exact Or.inl ⟨rfl, hunread⟩
    · exact Or.inr hsampled
  · -- 22 hparentReceipt: the actual accepted true-tail is the parent.
    exact topFreshTailCohortWaveAcceptedParentReceipt
      ring C s hn Z anchor W e hsite v hdata hbzero
      exported hevent htail
  · -- 23 hexportOld: the accepted append retains every older record.
    intro i hiOld hiNew
    exact topFreshTailCohortWaveRowFourteenOldExportAt
      ring C s hn Z anchor W e exported hevent i hiOld hiNew
  · -- 24 hexportAdded: the last export is the recorded true-tail sample.
    exact topFreshTailCohortWaveRowFourteenAddedRecord
      ring C s hn hbad Z anchor W e hsite v hdata hbzero hyi hyc

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One genuine accepted false-tail terminal export cannot wrap the
cohort counter. It advances the next home bound by exactly one
toward zero, keeps the current parent generation, and gives the
literal last record of the appended chronological export list.
Consumer: J5 row-thirteen current/next issue bounds and new receipt. -/
theorem topFreshTailCohortWaveRowThirteenNonwrappingExport
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (happend :
      topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
        topClockConcreteExportsAfter s Z anchor.time ++
          [exported])
    (hpositive :
      0 < topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n)) :
    (topClockConcreteExportsAfter s
      (topFixedTraceNext ring C Z e) anchor.time).length /
        topClockSpan n =
      (topClockConcreteExportsAfter s Z anchor.time).length /
        topClockSpan n ∧
    (topClockSpan n - 1 -
      ((topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e)
        anchor.time).length % topClockSpan n)) + 1 =
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n) ∧
    (topClockConcreteExportsAfter s
      (topFixedTraceNext ring C Z e) anchor.time).length %
        topClockSpan n =
      (topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n + 1 ∧
    ∃ hlast :
      (topClockConcreteExportsAfter s Z anchor.time).length <
        (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length,
      topClockConcreteExportAt s
        (topFixedTraceNext ring C Z e) anchor.time
        (⟨(topClockConcreteExportsAfter s Z anchor.time).length,
          hlast⟩ : Fin
          (topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length) = exported := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hcount :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
      (topClockConcreteExportsAfter s
        Z anchor.time).length + 1 := by
    rw [happend]
    simp
  have hmodLt :
      (topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n < topClockSpan n :=
    Nat.mod_lt _ (by omega)
  have hmodRoom :
      (topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n + 1 < topClockSpan n := by
    omega
  have hdivisionStable :
      ∀ (m r : Nat), 0 < r →
        m % r + 1 < r →
        (m + 1) / r = m / r ∧
        (m + 1) % r = m % r + 1 := by
    intro m r hrPos hroom
    have hone : 1 % r = 1 :=
      Nat.mod_eq_of_lt (by omega)
    have hmod : (m + 1) % r = m % r + 1 := by
      rw [Nat.add_mod, hone]
      exact Nat.mod_eq_of_lt hroom
    have hdivisionOld := Nat.mod_add_div m r
    have hdivisionNew := Nat.mod_add_div (m + 1) r
    rw [hmod] at hdivisionNew
    have hmul :
        r * ((m + 1) / r) = r * (m / r) := by
      omega
    exact ⟨Nat.mul_left_cancel hrPos hmul, hmod⟩
  have hstable :=
    hdivisionStable
      (topClockConcreteExportsAfter s Z anchor.time).length
      (topClockSpan n) (by omega) hmodRoom
  have hquotient :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length /
          topClockSpan n =
      (topClockConcreteExportsAfter s
        Z anchor.time).length / topClockSpan n := by
    rw [hcount]
    exact hstable.1
  have hmodNext :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length %
          topClockSpan n =
      (topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n + 1 := by
    rw [hcount]
    exact hstable.2
  have hhome :
      (topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length % topClockSpan n)) + 1 =
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n) := by
    omega
  have hlastBound :
      (topClockConcreteExportsAfter s Z anchor.time).length <
        (topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e)
          anchor.time).length := by
    omega
  have hgetSnoc :
      ∀ {α : Type} (L M : List α) (a : α)
        (hLM : M = L ++ [a])
        (hb : L.length < M.length),
        M[L.length]'hb = a := by
    intro α L M a hLM hb
    cases hLM
    simp
  refine ⟨hquotient, hhome, hmodNext,
    hlastBound, ?_⟩
  change
    (topClockConcreteExportsAfter s
      (topFixedTraceNext ring C Z e)
      anchor.time)[(topClockConcreteExportsAfter s
        Z anchor.time).length]'hlastBound = exported
  exact hgetSnoc _ _ _ happend hlastBound


/-- Nonwrapping false-tail acceptance leaves the historical
parent of the *same* current cohort unchanged. The historical
true-tail service stays at its genuine OLD prefix; a new false-tail
receipt cannot become a parent and only appends a suffix letter.
Consumer: J5 row-thirteen hparentReceipt. -/
theorem topFreshTailCohortWaveRowThirteenParentReceipt
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (happend :
      topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time ++
        [exported])
    (hpositive :
      0 < topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n)) :
    TopFreshTailCohortHistoricalParent
      ring C s hn (topFixedTraceNext ring C Z e) anchor
      ((topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e)
        anchor.time).length / topClockSpan n)
      W.currentParent := by
  have hquotient :=
    (topFreshTailCohortWaveRowThirteenNonwrappingExport
      ring C s hn Z anchor W e exported
      happend hpositive).1
  have holdReceipt := W.currentParentReceipt
  unfold TopFreshTailCohortHistoricalParent at holdReceipt ⊢
  rw [hquotient]
  obtain ⟨before, after, parentExport, hword, hslot,
    hport, htime, htail, hgen⟩ := holdReceipt
  refine ⟨before, after ++ [e], parentExport,
    ?_, hslot, hport, htime, htail, ?_⟩
  · change Z.2 ++ [e] =
      before ++ certSite s (topClockSpan n - 1) ::
        (after ++ [e])
    rw [hword]
    simp only [List.cons_append, List.append_assoc]
  · by_cases hzero :
        (topClockConcreteExportsAfter s
          Z anchor.time).length / topClockSpan n = 0
    · rw [if_pos hzero] at hgen ⊢
      exact hgen
    · rw [if_neg hzero] at hgen ⊢
      obtain ⟨i, hindex, hrecord⟩ := hgen
      have hiNew :
          i.val <
            (topClockConcreteExportsAfter s
              (topFixedTraceNext ring C Z e)
              anchor.time).length := by
        rw [happend]
        have hi := i.isLt
        simp only [List.length_append, List.length_singleton]
        omega
      refine ⟨⟨i.val, hiNew⟩, hindex, ?_⟩
      have hrecordNext :
          topClockConcreteExportAt s
            (topFixedTraceNext ring C Z e) anchor.time
            (⟨i.val, hiNew⟩ : Fin
              (topClockConcreteExportsAfter s
                (topFixedTraceNext ring C Z e)
                anchor.time).length) =
          topClockConcreteExportAt s Z anchor.time i := by
        have hlistGet :
            ∀ {α : Type} (L M : List α) (a : α)
              (hLM : M = L ++ [a]) (j : Nat)
              (hjOld : j < L.length) (hjNew : j < M.length),
              M[j]'hjNew = L[j]'hjOld := by
          intro α L M a hLM j hjOld hjNew
          cases hLM
          exact List.getElem_append_left hjOld
        unfold topClockConcreteExportAt
        exact hlistGet _ _ _ happend i.val i.isLt hiNew
      exact hrecord.trans hrecordNext.symm

/-- The genuine selected positive-home D(false) comparison-port
service retires the terminal current head, appends exactly its
sampled false-tail export, and preserves the full Type-valued
post-anchor cohort wave through the 24-field update principle.
Consumer: J5 row-thirteen one-edge wave induction. -/
theorem topFreshTailCohortWaveStepRowThirteen
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hdata : (Z.1.1 e).qOut = .D value false)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by
    omega
  have hb :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s
          Z anchor.time).length % topClockSpan n) <
        topClockSpan n := by omega
  have hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D value false := by
    rw [← hsite]
    exact hdata
  have hpositive :=
    topFreshTailCohortWaveFalseTerminalPositiveHome
      ring C s hn Z anchor W value hterminal
  obtain ⟨carrier, hmapHead, _, _⟩ :=
    topFreshTailCohortWaveRowThirteenSelectedHead
      ring C s hn Z anchor W value hterminal
  obtain ⟨exported, sample, happend, hrecordNew,
    hlane, hsampleSite, hsampleValue, hsampleFalse,
    hoperand, hexportValue, hexportTail⟩ :=
    topFreshTailCohortWaveRowThirteenAcceptedSample
      ring C s hn hbad Z anchor W e hsite value hdata
      hyi hyc
  obtain ⟨hquotient, hhomeStep, hresidueStep,
    hlastBound, hlastExport⟩ :=
    topFreshTailCohortWaveRowThirteenNonwrappingExport
      ring C s hn Z anchor W e exported happend hpositive
  obtain ⟨_, _, hslotGone, hsourceGone, _, _, _, _, _⟩ :=
    topFreshTailCohortWaveRowThirteenAcceptedTerminal
      ring C s hn hbad Z anchor W e hsite value hdata
      hyi hyc
  have hneighbor :
      ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite]
    rw [topFreshTailFirstBorderNeighborSite
      ring s (topClockSpan n - 1)]
    rw [show topClockSpan n - 1 + 1 =
      topClockSpan n by omega]
  have hrootLt :=
    (topFreshTailCohortWaveRowThirteenRootKindFrame
      ring C s hn Z anchor W e hsite value hdata).1
  have hrootKind :=
    (topFreshTailCohortWaveRowThirteenRootKindFrame
      ring C s hn Z anchor W e hsite value hdata).2
  have hnewCount :
      (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time).length =
        (topClockConcreteExportsAfter s
          Z anchor.time).length + 1 := by
    rw [happend]
    simp
  have hlistGet :
      ∀ {α : Type} (L M : List α) (a : α)
        (hLM : M = L ++ [a]) (i : Nat)
        (hiOld : i < L.length) (hiNew : i < M.length),
        M[i]'hiNew = L[i]'hiOld := by
    intro α L M a hLM i hiOld hiNew
    cases hLM
    exact List.getElem_append_left hiOld
  refine topFreshTailCohortWaveUpdate
    ring C s hn hbad Z anchor W e
    (fun k => if k =
      (⟨topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n), hb⟩ : Fin (topClockSpan n)) then
      none else W.currentMap k)
    W.nextMap W.currentParent W.root W.rootPosition
    (fun j => j.val = topClockSpan n - 1)
    (fun k => k =
      (⟨topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n), hb⟩ : Fin (topClockSpan n)))
    (fun _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hsiteAway: the sole changed source is the OLD terminal.
    intro j hj
    constructor
    · intro heq
      have hs := topFreshTailCohortWaveSourceOffsetUnique
        s hn j (topClockSpan n - 1)
        (by omega) (heq.trans hsite)
      exact hj hs
    · rw [hneighbor]
      exact topFreshTailFirstBorderPortOutsideSource s hn j
  · -- hcurrentOff: every other current entry is unchanged.
    intro k hk
    simp only [if_neg hk]
  · -- hnextOff: nextMap is unchanged.
    intro j _
    rfl
  · -- hcurrentAway: distinct selected homes and off-source responder.
    intro k y a hk hmapK
    have hne :
        (⟨topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n),
          hb⟩ : Fin (topClockSpan n)) ≠ k := by
      intro heq
      exact hk heq.symm
    have hdistinct :=
      topFreshTailCohortWaveCurrentHomeDistinct
        ring C s hn Z anchor W
        (⟨topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n),
          hb⟩ : Fin (topClockSpan n))
        k hne
        (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)) y carrier a hmapHead hmapK
    constructor
    · intro heq
      have hy :=
        topFreshTailCohortWaveSourceOffsetUnique
          s hn y (topClockSpan n - 1)
          (by omega) (heq.trans hsite)
      have hyFin :
          y = (⟨topClockSpan n - 1, htop⟩ :
            Fin (topClockSpan n)) :=
        Fin.ext hy
      exact hdistinct hyFin.symm
    · rw [hneighbor]
      exact topFreshTailFirstBorderPortOutsideSource s hn y
  · -- hnextAway: next homes precede the root and the terminal.
    intro j _ hj
    constructor
    · intro heq
      have hs := topFreshTailCohortWaveSourceOffsetUnique
        s hn j (topClockSpan n - 1)
        (by omega) (heq.trans hsite)
      omega
    · rw [hneighbor]
      exact topFreshTailFirstBorderPortOutsideSource s hn j
  · -- hcurrentEligibleOff: new bound is b-1; parent unchanged.
    intro k _ hbound
    refine ⟨?_, rfl⟩
    omega
  · -- hcurrentAbsentOff: only retired b is newly out of range.
    intro k hk houtside
    have hnotOldBound :
        k.val ≠ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n) := by
      intro heq
      exact hk (Fin.ext heq)
    omega
  · -- hnextEligibleOff: unchanged root and next-family generation.
    intro j _ hj
    exact ⟨hj, rfl⟩
  · -- hnextAbsentOff: unchanged rootPosition.
    intro j _ hj
    exact hj
  · -- hcurrentChanged: retired home b is not newly eligible.
    intro k hk hbound
    have hkVal :
        k.val = topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s
            Z anchor.time).length % topClockSpan n) := by
      rw [hk]
    omega
  · -- hcurrentChangedAbsent: currentMap[b] is literally none.
    intro k hk _
    simp only [hk, if_pos rfl, ↓reduceIte]
  · -- hnextChanged: no nextMap position changes.
    intro j hj
    cases hj
  · -- hnextChangedAbsent: no nextMap position changes.
    intro j hj
    cases hj
  · -- hcurrentOrderChanged: no selected pair can contain b.
    intro u v hchanged huv hbound p q a b hu hv
    rcases hchanged with hcu | hcv
    · rw [if_pos hcu] at hu
      cases hu
    · rw [if_pos hcv] at hv
      cases hv
  · -- hcurrentChangedSite: retired home selects no NEW source.
    intro k j a hk hmap
    rw [if_pos hk] at hmap
    cases hmap
  · -- hcurrentUnchangedSite: only the retired head owned terminal.
    intro j a k hj hmapK hk
    subst k
    have hp :
        ((⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)), carrier) =
          (j, a) :=
      Option.some.inj (hmapHead.symm.trans hmapK)
    have hjVal : j.val = topClockSpan n - 1 := by
      have heq := (Prod.mk.inj hp).1
      have hv := congrArg Fin.val heq.symm
      simpa only [Fin.val_mk] using hv
    exact hj hjVal
  · -- hnextUnchangedSite: nextMap has an empty change set.
    intro j _ hj
    cases hj
  · -- hsourceChanged: terminal genealogy slot was actually deleted.
    intro j a hj hslot
    have hterminalJ :
        j = (⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)) := Fin.ext hj
    rw [hterminalJ, hslotGone] at hslot
    cases hslot
  · -- hrootStable: current root remains selected at home zero.
    intro _
    exact ⟨rfl, rfl⟩
  · -- hrootChanged: retired positive terminal home is not zero.
    intro hk
    have hv := congrArg Fin.val hk
    simp only [Fin.val_mk] at hv
    omega
  · -- hrootKind: full old root sample and atom framed off-port.
    exact hrootKind
  · -- hparentReceipt: the previous true-tail service remains parent.
    exact topFreshTailCohortWaveRowThirteenParentReceipt
      ring C s hn Z anchor W e exported happend hpositive
  · -- hexportOld: genuine chronological append preserves old entries.
    intro i hiOld hiNew
    unfold topClockConcreteExportAt
    exact hlistGet _ _ _ happend i hiOld hiNew
  · -- hexportAdded: unique new entry is the sampled home-b false tail.
    intro i hnew
    have hi := i.isLt
    have hindex :
        i.val = (topClockConcreteExportsAfter s
          Z anchor.time).length := by
      omega
    have hlastFin :
        i = (⟨(topClockConcreteExportsAfter s
          Z anchor.time).length, hlastBound⟩ :
          Fin (topClockConcreteExportsAfter s
            (topFixedTraceNext ring C Z e)
            anchor.time).length) :=
      Fin.ext hindex
    have hlookup :
        topClockConcreteExportAt s
          (topFixedTraceNext ring C Z e) anchor.time i =
        exported := by
      rw [hlastFin]
      exact hlastExport
    have hnotLast :
        (topClockConcreteExportsAfter s Z
          anchor.time).length % topClockSpan n ≠
            topClockSpan n - 1 := by
      omega
    refine ⟨sample, hrecordNew, hlane, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hindex]
      exact hsampleSite
    · rw [hindex]
      exact hsampleValue
    · rw [hindex, if_neg hnotLast]
      exact hsampleFalse
    · rw [hlookup]
      exact hoperand
    · rw [hlookup]
      exact hexportValue
    · rw [hlookup]
      exact hexportTail

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every physical scheduler source lies on the finite comparison
source arc, entirely misses that arc, or is the exceptional
external predecessor with responder at comparison source zero.
Consumer: topFreshTailCohortWaveEdgeCases. -/
theorem topFreshTailCohortWaveSourceArcCover
    {n : Nat} (ring : DirectedRing n)
    (s : Fin n) (hn : 5 ≤ n) (e : Fin n) :
    (∀ j : Fin (topClockSpan n),
      certSite s j.val ≠ e ∧
      certSite s j.val ≠ ring.rightNeighbor e) ∨
    ring.rightNeighbor e = certSite s 0 ∨
    ∃ j : Fin (topClockSpan n), e = certSite s j.val := by
  by_cases hsource :
      ∃ j : Fin (topClockSpan n), e = certSite s j.val
  · exact Or.inr (Or.inr hsource)
  · by_cases htarget :
        ∃ j : Fin (topClockSpan n),
          ring.rightNeighbor e = certSite s j.val
    · obtain ⟨j, hjtarget⟩ := htarget
      by_cases hjzero : j.val = 0
      · exact Or.inr (Or.inl
          (by simpa only [hjzero] using hjtarget))
      · have hjpositive : 0 < j.val := by omega
        have hprevious :=
          topFreshTailCausalIncomingPredecessor
            ring hn s j hjpositive e hjtarget
        have hpreviousBound : j.val - 1 < topClockSpan n := by
          have hjbound := j.isLt
          omega
        have hcontra := hsource
          ⟨(⟨j.val - 1, hpreviousBound⟩ :
            Fin (topClockSpan n)),
            by simpa only [Fin.val_mk] using hprevious⟩
        exact False.elim hcontra
    · apply Or.inl
      intro j
      constructor
      · intro hsame
        exact hsource ⟨j, hsame.symm⟩
      · intro hsame
        exact htarget ⟨j, hsame.symm⟩

/-- A true-tail D at the terminal comparison source is the
selected zero-home head. This derives its home-index boundary,
rather than assuming it from the output bit alone.
Consumer: topFreshTailCohortWaveEdgeCases, accepted row fourteen. -/
theorem topFreshTailCohortWaveTrueTerminalHomeZero
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hterminal :
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D value true) :
    topClockSpan n - 1 -
      ((topClockConcreteExportsAfter s Z anchor.time).length %
        topClockSpan n) = 0 := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  have hb :
      topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) < topClockSpan n := by omega
  obtain ⟨carrier, hhead, _⟩ :=
    W.selectedHead value true hterminal
  obtain ⟨x, oldCarrier, hmap, hactive, _⟩ :=
    W.currentIssued
      (⟨topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n), hb⟩ : Fin (topClockSpan n))
      (Nat.le_refl _)
  have hpair :
      (x, oldCarrier) =
        ((⟨topClockSpan n - 1, htop⟩ :
          Fin (topClockSpan n)), carrier) :=
    Option.some.inj (hmap.symm.trans hhead)
  have hx : x = (⟨topClockSpan n - 1, htop⟩ :
      Fin (topClockSpan n)) := (Prod.mk.inj hpair).1
  have ha : oldCarrier = carrier := (Prod.mk.inj hpair).2
  rw [hx, ha] at hactive
  rcases hactive.2.2.2 with ⟨_, hunread⟩ |
    ⟨sample, hdata, _, _, _, _, _, _⟩
  · have hsourceU :
        (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
          .U := by
      simpa only [Fin.val_mk] using hunread
    rw [hterminal] at hsourceU
    cases hsourceU
  · by_cases hzero :
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) = 0
    · exact hzero
    · have hdataFalse :
          (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
            .D (C (certSite s
              (topClockSpan n - 1 -
                ((topClockConcreteExportsAfter s Z anchor.time).length %
                  topClockSpan n)))).d false := by
        simpa only [Fin.val_mk, if_neg hzero] using hdata
      rw [hterminal] at hdataFalse
      cases hdataFalse

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every nonempty physical source of a selected wave belongs
either to its unique selected current home (with the real
ActiveHome witness) or to an issued stationary next child.
Consumer: topFreshTailCohortWaveEdgeCases. -/
theorem topFreshTailCohortWaveSelectedSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (j : Fin (topClockSpan n)) (e : Fin n)
    (hsite : e = certSite s j.val)
    (hoccupied : (Z.1.1 e).qOut ≠ .E) :
    (∃ (h : Fin (topClockSpan n))
      (carrier : TopFreshTailCarrier (topClockSpan n)),
      h.val ≤ topClockSpan n - 1 -
        ((topClockConcreteExportsAfter s Z anchor.time).length %
          topClockSpan n) ∧
      W.currentMap h = some (j, carrier) ∧
      TopFreshTailPostAnchorActiveHome
        ring C s Z h j carrier) ∨
    (j.val < W.rootPosition.val ∧
      ∃ carrier : TopFreshTailCarrier (topClockSpan n),
        W.nextMap j = some carrier ∧
        TopFreshTailFirstBorderHomeSlot
          ring C s Z W.root j) := by
  have hnotEmpty :
      (Z.1.1 (certSite s j.val)).qOut ≠ .E := by
    rw [← hsite]
    exact hoccupied
  obtain ⟨carrier, hslot⟩ :=
    topFreshTailCausalOccupiedHasCarrier
      ring C s Z W.queue j hnotEmpty
  rcases W.sourceCoverage j carrier hslot with
    ⟨h, hmap, _⟩ | ⟨hnext, _⟩
  · have hbound :
        h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) := by
      by_cases hb :
          h.val ≤ topClockSpan n - 1 -
            ((topClockConcreteExportsAfter s Z anchor.time).length %
              topClockSpan n)
      · exact hb
      · have hnone := W.currentAbsent h (by omega)
        rw [hnone] at hmap
        cases hmap
    obtain ⟨x, oldCarrier, hselected, hactive, _⟩ :=
      W.currentIssued h hbound
    have hpair : (x, oldCarrier) = (j, carrier) :=
      Option.some.inj (hselected.symm.trans hmap)
    have hx : x = j := (Prod.mk.inj hpair).1
    have ha : oldCarrier = carrier := (Prod.mk.inj hpair).2
    rw [hx, ha] at hactive
    exact Or.inl ⟨h, carrier, hbound, hmap, hactive⟩
  · have hbelow : j.val < W.rootPosition.val := by
      by_cases hb : j.val < W.rootPosition.val
      · exact hb
      · have hnone := W.nextAbsent j (by omega)
        rw [hnone] at hnext
        cases hnext
    obtain ⟨nextCarrier, hmap, _, hhome, _⟩ :=
      W.nextIssued j hbelow
    exact Or.inr ⟨hbelow, nextCarrier, hmap, hhome⟩


/-- Every OLD scheduler edge of a leaderless selected cohort wave
satisfies the exact witness/guard bundle of at least one row of
the J5 source/responder table, including the two accepted-terminal
rows awaiting their full one-edge preservation theorems.
Consumer: topFreshTailCohortWaveStepOfRows. -/
theorem topFreshTailCohortWaveEdgeCases
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n) :
    (∀ j : Fin (topClockSpan n),
      certSite s j.val ≠ e ∧
      certSite s j.val ≠ ring.rightNeighbor e) ∨
    (ring.rightNeighbor e = certSite s 0) ∨
    (∃ j : Fin (topClockSpan n),
      0 < j.val ∧ e = certSite s j.val ∧
      (Z.1.1 e).qOut = .E) ∨
    (e = certSite s 0 ∧ (Z.1.1 e).qOut = .E) ∨
    (∃ (h : Fin (topClockSpan n))
      (carrier : TopFreshTailCarrier (topClockSpan n)),
      h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) ∧
      W.currentMap h = some (h, carrier) ∧
      e = certSite s h.val ∧ (Z.1.1 e).qOut = .U) ∨
    (∃ j : Fin (topClockSpan n),
      j.val < W.rootPosition.val ∧
      e = certSite s j.val ∧ (Z.1.1 e).qOut = .U) ∨
    (∃ (h x : Fin (topClockSpan n))
      (carrier : TopFreshTailCarrier (topClockSpan n)),
      h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) ∧ 0 < h.val ∧
      W.currentMap h = some (x, carrier) ∧
      e = certSite s x.val ∧ x.val + 1 < topClockSpan n ∧
      (Z.1.1 e).qOut = .D (C (certSite s h.val)).d false ∧
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) ∨
    (e = certSite s W.rootPosition.val ∧
      W.rootPosition.val + 1 < topClockSpan n ∧
      ∃ value : Fin (compileAdvice (ceilLogTwo n)).topA,
        (Z.1.1 e).qOut = .D value true ∧
        (Z.1.1 (ring.rightNeighbor e)).qOut = .E) ∨
    (∃ (h x : Fin (topClockSpan n))
      (carrier : TopFreshTailCarrier (topClockSpan n)),
      h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) ∧
      W.currentMap h = some (x, carrier) ∧
      e = certSite s x.val ∧ x.val + 1 < topClockSpan n ∧
      (Z.1.1 e).qOut =
        .D (C (certSite s h.val)).d (if h.val = 0 then true else false) ∧
      (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) ∨
    (∃ (j : Fin (topClockSpan n))
      (value : Fin (compileAdvice (ceilLogTwo n)).topA),
      j.val < W.rootPosition.val ∧ e = certSite s j.val ∧
      (Z.1.1 e).qOut =
        .D value (if j.val = 0 then true else false)) ∨
    (∃ (h x : Fin (topClockSpan n))
      (carrier : TopFreshTailCarrier (topClockSpan n)),
      h.val ≤ topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) ∧
      W.currentMap h = some (x, carrier) ∧
      e = certSite s x.val ∧ x.val + 1 = topClockSpan n ∧
      (Z.1.1 e).qOut = .U) ∨
    (e = certSite s (topClockSpan n - 1) ∧
      ∃ (value : Fin (compileAdvice (ceilLogTwo n)).topA)
        (tail : Bool),
        (Z.1.1 e).qOut = .D value tail ∧
        ((Z.1.1 (ring.rightNeighbor e)).qIn.isE = false ∨
          (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff = false)) ∨
    (e = certSite s (topClockSpan n - 1) ∧
      ∃ value : Fin (compileAdvice (ceilLogTwo n)).topA,
        (Z.1.1 e).qOut = .D value false ∧
        (Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
        (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF ∧
        0 < topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n)) ∨
    (e = certSite s (topClockSpan n - 1) ∧
      ∃ value : Fin (compileAdvice (ceilLogTwo n)).topA,
        (Z.1.1 e).qOut = .D value true ∧
        (Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
        (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF ∧
        topClockSpan n - 1 -
          ((topClockConcreteExportsAfter s Z anchor.time).length %
            topClockSpan n) = 0) ∨
    (∃ (j : Fin (topClockSpan n))
      (value : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool),
      0 < j.val ∧ ring.rightNeighbor e = certSite s j.val ∧
      (Z.1.1 e).qOut = .D value tail ∧
      ∃ carrier : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s Z).slots j = some carrier) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hzero : 0 < topClockSpan n := by omega
  have htop : topClockSpan n - 1 < topClockSpan n := by omega
  rcases topFreshTailCohortWaveSourceArcCover
      ring s hn e with haway | hincoming | ⟨j, hsite⟩
  · exact Or.inl (haway)
  · exact Or.inr (Or.inl (hincoming))
  · cases hout : (Z.1.1 e).qOut with
    | E =>
        by_cases hjzero : j.val = 0
        · have hzeroSite : e = certSite s 0 := by
            simpa only [hjzero] using hsite
          exact Or.inr (Or.inr (Or.inr (Or.inl (⟨hzeroSite, rfl⟩))))
        · have hjpositive : 0 < j.val := by omega
          exact Or.inr (Or.inr (Or.inl (⟨j, hjpositive, hsite, rfl⟩)))
    | U =>
        have hoccupied : (Z.1.1 e).qOut ≠ .E := by
          intro heq
          rw [hout] at heq
          cases heq
        rcases topFreshTailCohortWaveSelectedSource
            ring C s hn Z anchor W j e hsite hoccupied with
          ⟨h, carrier, hbound, hmap, hactive⟩ |
          ⟨hbehind, carrier, hmap, hhome⟩
        · rcases hactive.2.2.2 with ⟨hhome, hunread⟩ |
            ⟨sample, hdata, _, _, _, _, _, _⟩
          · have hhomeSite : e = certSite s h.val := by
              simpa only [hhome] using hsite
            have hhomeMap : W.currentMap h = some (h, carrier) := by
              simpa only [hhome] using hmap
            by_cases hterminal : j.val + 1 = topClockSpan n
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h, j, carrier, hbound, hmap, hsite, hterminal, rfl⟩)))))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h, carrier, hbound, hhomeMap, hhomeSite, rfl⟩)))))
          · have hdataAt : (Z.1.1 e).qOut =
                .D (C (certSite s h.val)).d
                  (if h.val = 0 then true else false) := by
              rw [hsite]
              exact hdata
            rw [hout] at hdataAt
            cases hdataAt
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j, hbehind, hsite, rfl⟩))))))
    | D value tail =>
        by_cases hterminal : j.val + 1 = topClockSpan n
        · have hlast : j.val = topClockSpan n - 1 := by omega
          have hport : e = certSite s (topClockSpan n - 1) := by
            rw [hsite, hlast]
          by_cases hinput :
              (Z.1.1 (ring.rightNeighbor e)).qIn = .E
          · by_cases hcarry :
                (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF
            · cases tail with
              | false =>
                  have hterminalData :
                      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
                        .D value false := by
                    rw [← hport]
                    exact hout
                  have hpositive :=
                    topFreshTailCohortWaveFalseTerminalPositiveHome
                      ring C s hn Z anchor W value hterminalData
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨hport, value, rfl, hinput, hcarry, hpositive⟩)))))))))))))
              | true =>
                  have hterminalData :
                      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
                        .D value true := by
                    rw [← hport]
                    exact hout
                  have hhomeZero :=
                    topFreshTailCohortWaveTrueTerminalHomeZero
                      ring C s hn Z anchor W value hterminalData
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨hport, value, rfl, hinput, hcarry, hhomeZero⟩))))))))))))))
            · have hcarryBlocked :
                  (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff =
                    false := by
                cases hq : (Z.1.1 (ring.rightNeighbor e)).qCarry with
                | OFF => exact False.elim (hcarry hq)
                | L bit err => rfl
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨hport, value, tail, rfl, Or.inr hcarryBlocked⟩))))))))))))
          · have hinputBlocked :
                (Z.1.1 (ring.rightNeighbor e)).qIn.isE = false := by
              cases hq : (Z.1.1 (ring.rightNeighbor e)).qIn with
              | E => exact False.elim (hinput hq)
              | P digit bit => rfl
              | S digit bit => rfl
              | X => rfl
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨hport, value, tail, rfl, Or.inl hinputBlocked⟩))))))))))))
        · have hnext : j.val + 1 < topClockSpan n := by
            have hjbound := j.isLt
            omega
          have hoccupied : (Z.1.1 e).qOut ≠ .E := by
            intro heq
            rw [hout] at heq
            cases heq
          rcases topFreshTailCohortWaveSelectedSource
              ring C s hn Z anchor W j e hsite hoccupied with
            ⟨h, carrier, hbound, hmap, hactive⟩ |
            ⟨hbehind, carrier, hmap, hhome⟩
          · rcases hactive.2.2.2 with ⟨_, hunread⟩ |
                ⟨sample, hdata, _, _, _, _, _, _⟩
            · have hunreadAt : (Z.1.1 e).qOut = .U := by
                rw [hsite]
                exact hunread
              rw [hout] at hunreadAt
              cases hunreadAt
            · have hdataAt :
                  (Z.1.1 e).qOut =
                    .D (C (certSite s h.val)).d
                      (if h.val = 0 then true else false) := by
                rw [hsite]
                exact hdata
              by_cases hempty :
                  (Z.1.1 (ring.rightNeighbor e)).qOut = .E
              · by_cases hhomeZero : h.val = 0
                · have hzeroIndex :
                      h = (⟨0, hzero⟩ : Fin (topClockSpan n)) :=
                    Fin.ext hhomeZero
                  have hzeroMap :
                      W.currentMap
                        (⟨0, hzero⟩ : Fin (topClockSpan n)) =
                          some (j, carrier) := by
                    rw [← hzeroIndex]
                    exact hmap
                  have hpair : (j, carrier) =
                      (W.rootPosition, W.root) :=
                    Option.some.inj
                      (hzeroMap.symm.trans W.rootSelected)
                  have hrootEq : j = W.rootPosition :=
                    (Prod.mk.inj hpair).1
                  have hrootSite :
                      e = certSite s W.rootPosition.val := by
                    rw [hrootEq] at hsite
                    exact hsite
                  have hrootNext :
                      W.rootPosition.val + 1 < topClockSpan n := by
                    rw [← hrootEq]
                    exact hnext
                  have htrue :
                      (Z.1.1 e).qOut =
                        .D (C (certSite s h.val)).d true := by
                    simpa only [if_pos hhomeZero] using hdataAt
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨hrootSite, hrootNext, (C (certSite s h.val)).d, (by simpa only [hout] using htrue), hempty⟩))))))))
                · have hpositive : 0 < h.val := by omega
                  have hfalse :
                      (Z.1.1 e).qOut =
                        .D (C (certSite s h.val)).d false := by
                    simpa only [if_neg hhomeZero] using hdataAt
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h, j, carrier, hbound, hpositive, hmap, hsite, hnext, (by simpa only [hout] using hfalse), hempty⟩)))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨h, j, carrier, hbound, hmap, hsite, hnext, (by simpa only [hout] using hdataAt), hempty⟩)))))))))
          · unfold TopFreshTailFirstBorderHomeSlot at hhome
            obtain ⟨other, hslot, hfresh, hparent, hkind⟩ := hhome
            rcases hkind with hunread |
              ⟨sample, hdata, _, _, _, _, _, _⟩
            · have hunreadAt : (Z.1.1 e).qOut = .U := by
                rw [hsite]
                exact hunread
              rw [hout] at hunreadAt
              cases hunreadAt
            · have hdataAt :
                  (Z.1.1 e).qOut =
                    .D (C (certSite s j.val)).d
                      (if j.val = 0 then true else false) := by
                rw [hsite]
                exact hdata
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j, (C (certSite s j.val)).d, hbehind, hsite, (by simpa only [hout] using hdataAt)⟩))))))))))

/-- The full cohort-wave one-edge step follows from the fifteen
merged OLD row theorems and the exhaustive source/response split.
The external incoming-zero row requires global leaderlessness.
Consumer: J5 post-anchor word induction. -/
theorem topFreshTailCohortWaveStepOfRows
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n) (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (W : TopFreshTailPostAnchorCohortWave
      ring C s hn Z anchor)
    (e : Fin n) :
    Nonempty (TopFreshTailPostAnchorCohortWave
      ring C s hn (topFixedTraceNext ring C Z e) anchor) := by
  rcases topFreshTailCohortWaveEdgeCases
      ring C s hn hbad hl Z anchor W e with
    hOne | hTwo | hThree | hFour | hFive |
    hSix | hSeven | hEight | hNine | hTen |
    hEleven | hTwelve | hThirteen | hFourteen | hFifteen
  · exact topFreshTailCohortWaveStepRowOne
      ring C s hn hbad Z anchor W e hOne
  · exact topFreshTailCohortWaveStepRowTwo
      ring C s hn hbad hl Z anchor W e hTwo
  · obtain ⟨j, hpositive, hsite, hsource⟩ := hThree
    exact topFreshTailCohortWaveStepRowThree
      ring C s hn hbad Z anchor W j hpositive e hsite hsource
  · exact topFreshTailCohortWaveStepRowFour
      ring C s hn hbad Z anchor W e hFour.1 hFour.2
  · obtain ⟨h, carrier, hbound, hmap, hsite, hunread⟩ := hFive
    exact topFreshTailCohortWaveStepRowFive
      ring C s hn hbad Z anchor W h hbound
      carrier hmap e hsite hunread
  · obtain ⟨j, hbehind, hsite, hunread⟩ := hSix
    exact topFreshTailCohortWaveStepRowSix
      ring C s hn hbad Z anchor W j hbehind e hsite hunread
  · obtain ⟨h, x, carrier, hbound, hpositive, hmap,
      hsite, hnext, hdata, hempty⟩ := hSeven
    exact topFreshTailCohortWaveStepRowSeven
      ring C s hn hbad Z anchor W h hbound hpositive
      x carrier hmap e hsite hnext hdata hempty
  · obtain ⟨hsite, hnext, value, hdata, hempty⟩ := hEight
    exact topFreshTailCohortWaveStepRowEight
      ring C s hn hbad Z anchor W e hsite hnext
      value hdata hempty
  · obtain ⟨h, x, carrier, hbound, hmap,
      hsite, hnext, hdata, hoccupied⟩ := hNine
    exact topFreshTailCohortWaveStepRowNine
      ring C s hn hbad Z anchor W h hbound
      x carrier hmap e hsite hnext hdata hoccupied
  · obtain ⟨j, value, hbehind, hsite, hdata⟩ := hTen
    exact topFreshTailCohortWaveStepRowTen
      ring C s hn hbad Z anchor W j hbehind e hsite value hdata
  · obtain ⟨h, x, carrier, hbound, hmap,
      hsite, hterminal, hunread⟩ := hEleven
    exact topFreshTailCohortWaveStepRowEleven
      ring C s hn hbad Z anchor W h hbound x carrier
      hmap e hsite hterminal hunread
  · obtain ⟨hsite, value, tail, hdata, hblocked⟩ := hTwelve
    exact topFreshTailCohortWaveStepRowTwelve
      ring C s hn hbad Z anchor W e hsite
      value tail hdata hblocked
  · obtain ⟨hsite, value, hdata, hyi, hyc, _⟩ :=
      hThirteen
    exact topFreshTailCohortWaveStepRowThirteen
      ring C s hn hbad Z anchor W e hsite value hdata hyi hyc
  · obtain ⟨hsite, value, hdata, hyi, hyc, hzero⟩ :=
      hFourteen
    exact topFreshTailCohortWaveStepRowFourteen
      ring C s hn hbad Z anchor W e hsite value hdata hzero hyi hyc
  · obtain ⟨j, value, tail, hpositive, hneighbor,
      hdata, carrier, hslot⟩ := hFifteen
    exact topFreshTailCohortWaveStepRowFifteen
      ring C s hn hbad Z anchor W j hpositive e
      hneighbor value tail hdata ⟨carrier, hslot⟩

end L3

#print axioms L3.topFreshTailCohortRealRearmIssueStep
#print axioms L3.topFreshTailCohortFirstAnchorEnvelope
#print axioms L3.topFreshTailCohortNewEntryTime
#print axioms L3.topFreshTailCohortExportClockBoundStep
#print axioms L3.topFreshTailCohortExportClockBoundFold
#print axioms L3.topFreshTailCohortExportClockBoundRun
#print axioms L3.topFreshTailCohortFirstAnchorExportsEmpty
#print axioms L3.topFreshTailCohortIssueHistoryAppendStay
#print axioms L3.topFreshTailCohortIssuedBarrierAtZero
#print axioms L3.topFreshTailCohortIssuedBarrierFrameStep
#print axioms L3.topFreshTailCohortIssuedBarrierAwayStep
#print axioms L3.topFreshTailCohortIssuedBarrierAheadStep
#print axioms L3.topFreshTailCohortIssueHistoryAtRearm
#print axioms L3.topFreshTailCohortIssuedBarrierRootHop
#print axioms L3.topFreshTailCohortIssuedBarrierRootOccupied
#print axioms L3.topFreshTailCohortIssuedBarrierPortBlocked
#print axioms L3.topFreshTailCohortFirstAnchorAllHomeIssuesOfBarrier
#print axioms L3.topFreshTailCohortIssuedBarrierBorderIncomingAtZero
#print axioms L3.topFreshTailCohortIssueHistoryAppendZeroRekey
#print axioms L3.topFreshTailCohortIssuedBarrierInitial
#print axioms L3.topFreshTailCohortBehindSourceHistory
#print axioms L3.topFreshTailCohortBehindResponderCarrierFrame
#print axioms L3.topFreshTailCohortIssuedBarrierBehindStep
#print axioms L3.topFreshTailCohortIssuedBarrierIncomingZero
#print axioms L3.topFreshTailCohortIssuedBarrierEdge
#print axioms L3.topFreshTailCohortIssuedBarrierRun
#print axioms L3.topFreshTailCohortWaveBaseFromHomeIssues
#print axioms L3.topFreshTailPostAnchorCohortWaveBase
#print axioms L3.topFreshTailCohortFirstAnchorAllHomeIssues
#print axioms L3.topFreshTailCohortWaveRowEightSelectedRootSlot
#print axioms L3.topFreshTailCohortWaveRowEightRootHopIssue
#print axioms L3.topFreshTailCohortWaveRowNineBlockedCurrent
#print axioms L3.topFreshTailCohortWaveRowTenSuccessorOccupied
#print axioms L3.topFreshTailCohortWaveRowElevenTerminalUnread
#print axioms L3.topFreshTailCohortWaveRowTwelveBlockedPortCarrier
#print axioms L3.topFreshTailCohortWaveRowThirteenSelectedHead
#print axioms L3.topFreshTailCohortWaveRowFourteenTerminalParent
#print axioms L3.topFreshTailCohortWaveRowFifteenIncomingPredecessor
#print axioms L3.topFreshTailCohortWaveRowFiveCommonFrame
#print axioms L3.topFreshTailCohortWaveRowFiveCurrentUnread
#print axioms L3.topFreshTailCohortWaveRowSixNextUnread
#print axioms L3.topFreshTailCohortWaveRowSevenCurrentFalseMove
#print axioms L3.topFreshTailCohortWaveRowFourZeroOccupied
#print axioms L3.topFreshTailCohortWaveRowFourMarkerBootstrap
#print axioms L3.topFreshTailCohortWaveRowThreeNonmarkerEmptySource
#print axioms L3.topFreshTailCohortWaveUpdate
#print axioms L3.topFreshTailCohortWaveCurrentHomeDistinct
#print axioms L3.topFreshTailCohortWaveCurrentHomeOccupied
#print axioms L3.topFreshTailCohortWaveCurrentAway
#print axioms L3.topFreshTailCohortWaveCurrentRootPrecedes
#print axioms L3.topFreshTailCohortWaveNonPortExports
#print axioms L3.topFreshTailCohortWaveParentReceiptAppend
#print axioms L3.topFreshTailCohortWaveRowSevenOrder
#print axioms L3.topFreshTailCohortWaveRowSevenSourceCoverage
#print axioms L3.topFreshTailCohortWaveStepRowSeven
#print axioms L3.topFreshTailCohortWaveRowSixNonPort
#print axioms L3.topFreshTailCohortWaveStayOutputs
#print axioms L3.topFreshTailCohortWaveStaySlots
#print axioms L3.topFreshTailCohortWaveStayAtoms
#print axioms L3.topFreshTailCohortWaveStayStep
#print axioms L3.topFreshTailCohortWaveStepRowNine
#print axioms L3.topFreshTailCohortWaveStepRowTen
#print axioms L3.topFreshTailCohortWaveStepRowFifteen
#print axioms L3.topFreshTailCohortWaveCurrentAtOrAfterRoot
#print axioms L3.topFreshTailCohortWaveUnreadResponderCarrier
#print axioms L3.topFreshTailCohortWaveUnreadResponderDataAtom
#print axioms L3.topFreshTailCohortWaveUnreadResponderCurrent
#print axioms L3.topFreshTailCohortWaveUnreadResponderHome
#print axioms L3.topFreshTailCohortWaveUnreadResponderNext
#print axioms L3.topFreshTailCohortWaveStepRowSix
#print axioms L3.topFreshTailCohortWaveUnreadResponderOutput
#print axioms L3.topFreshTailCohortWaveRowFiveOrder
#print axioms L3.topFreshTailCohortWaveBlockedPortExports
#print axioms L3.topFreshTailCohortWaveBlockedPortFrame
#print axioms L3.topFreshTailCohortWaveFramedStayStep
#print axioms L3.topFreshTailCohortWaveStepRowTwelve
#print axioms L3.topFreshTailCohortWaveRootHopHistory
#print axioms L3.topFreshTailCohortWaveRootHopChildHome
#print axioms L3.topFreshTailCohortWaveRootHopOrder
#print axioms L3.topFreshTailCohortWaveFalseTerminalPositiveHome
#print axioms L3.topFreshTailCohortWaveUnreadPortExports
#print axioms L3.topFreshTailCohortWaveSourceOffsetUnique
#print axioms L3.topFreshTailCohortWaveStepRowFive
#print axioms L3.topFreshTailCohortWaveAcceptedExports
#print axioms L3.topFreshTailCohortWaveStepRowEleven
#print axioms L3.topFreshTailCohortWaveRootHopActive
#print axioms L3.topFreshTailCohortWaveRootHopKind
#print axioms L3.topFreshTailCohortWaveRootHopSilent
#print axioms L3.topFreshTailCohortWaveRootHopNextIssue
#print axioms L3.topFreshTailCohortWaveRootHopNextAbsent
#print axioms L3.topFreshTailCohortWaveRootHopSourceCoverage
#print axioms L3.topFreshTailCohortWaveStepRowEight
#print axioms L3.topFreshTailCohortWaveAcceptedParentReceipt
#print axioms L3.topFreshTailCohortWaveRowFourteenReindexedHome
#print axioms L3.topFreshTailCohortWaveRowFourteenReindexedOrder
#print axioms L3.topFreshTailCohortWaveRowFourteenRootKind
#print axioms L3.topFreshTailCohortWaveRowFourteenSourceCoverage
#print axioms L3.topFreshTailCohortWaveRowFourteenAcceptedChild
#print axioms L3.topFreshTailCohortWaveRowThirteenAcceptedTerminal
#print axioms L3.topFreshTailCohortWaveRowThirteenNextHistoryFrame
#print axioms L3.topFreshTailCohortWaveRowThirteenRootKindFrame
#print axioms L3.topFreshTailCohortWaveRowOneOffPairHistory
#print axioms L3.topFreshTailCohortWaveRowOneOffPairFrame
#print axioms L3.topFreshTailCohortWaveStepRowOne
#print axioms L3.topFreshTailCohortWaveRowTwoIncomingZeroResponderFrame
#print axioms L3.topFreshTailCohortWaveRowTwoIncomingZeroGlobalFrame
#print axioms L3.topFreshTailCohortWaveStepRowTwo
#print axioms L3.topFreshTailCohortWaveRowThreeEmptyPortSilent
#print axioms L3.topFreshTailCohortWaveRowThreeNonmarkerGlobalFrame
#print axioms L3.topFreshTailCohortWaveStepRowThree
#print axioms L3.topFreshTailCohortWaveStepRowFour
#print axioms L3.topFreshTailCohortWaveRowThirteenAcceptedSample
#print axioms L3.topFreshTailCohortWaveRowFourteenWrappedIndex
#print axioms L3.topFreshTailCohortWaveRowFourteenOldExportAt
#print axioms L3.topFreshTailCohortWaveRowFourteenAddedRecord
#print axioms L3.topFreshTailCohortWaveStepRowFourteen
#print axioms L3.topFreshTailCohortWaveRowThirteenNonwrappingExport
#print axioms L3.topFreshTailCohortWaveRowThirteenParentReceipt
#print axioms L3.topFreshTailCohortWaveStepRowThirteen
#print axioms L3.topFreshTailCohortWaveSourceArcCover
#print axioms L3.topFreshTailCohortWaveTrueTerminalHomeZero
#print axioms L3.topFreshTailCohortWaveSelectedSource
#print axioms L3.topFreshTailCohortWaveEdgeCases
#print axioms L3.topFreshTailCohortWaveStepOfRows
