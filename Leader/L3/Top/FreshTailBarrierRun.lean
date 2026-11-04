import Leader.L3.Top.FreshTailFrameOrder
import Leader.L3.Top.FreshTailOldFront

/-!
Q7c P.3 J5: a source-home barrier remains valid on every
OLD edge that does not export its tracked root. At a free
terminal port the same OLD edge records a genuine root-tail
anchor and a complete locally sampled fresh staircase.

This module works on the fixed-public physical/audit trace.
The word theorem stops at the first acceptance of the
tracked root encountered by the fold. Identification with
the globally first genuine receipt is a separate first-root
selection obligation: the home barrier itself does not
assert that no other fresh carrier is ahead of the root.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- One actual OLD scheduler edge is either a tracked-root
nonacceptance (possibly moving it one interior slot) or the
accepted genuine root-tail port with its full home staircase.

Rows: HomeBarrierBehindStep for source U/D behind;
HomeBarrierAheadStep for old U, false D, true D/rearm or
terminal old service ahead; HomeBarrierRootHop for enabled
root interior D(true); HomeBarrierOccupiedStep for blocked
interior; HomeBarrierPortBlocked for each blocked target
QI/QC state; AcceptedPortRootHomeStaircase for free target;
HomeBarrierBorderIncoming/IncomingZero for wrapped incoming
source-zero; HomeBarrierAwayStep for off-pair. The positive
incoming-responder case is already a source-initiator case
by topFreshTailCausalIncomingPredecessor.
Consumer: topFreshTailFirstBorderBarrierRun. -/
theorem topFreshTailFirstBorderBarrierEdge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hbarrier :
      TopFreshTailFirstBorderHomeBarrier
        ring C s Z root k sample)
    (e : Fin n) :
    (∃ moved : Fin (topClockSpan n),
      TopFreshTailFirstBorderHomeBarrier
        ring C s (topFixedTraceNext ring C Z e)
        root moved sample ∧
      (moved = k ∨ moved.val = k.val + 1)) ∨
    (topClockGenuineTailAccepted C s
      (topFixedTraceNext ring C Z e) ∧
      ∀ j : Fin (topClockSpan n),
        TopFreshTailFirstBorderHomeSlot
          ring C s (topFixedTraceNext ring C Z e)
          root j) := by
  by_cases hsource :
      ∃ j : Fin (topClockSpan n), e = certSite s j.val
  · obtain ⟨j, hsite⟩ := hsource
    by_cases hbelow : j.val < k.val
    · left
      exact ⟨k,
        topFreshTailFirstBorderHomeBarrierBehindStep
          ring C s hn hbad hl Z root k sample
          hbarrier j hbelow e hsite,
        Or.inl rfl⟩
    · by_cases hequal : j.val = k.val
      · have hindex : j = k := Fin.ext hequal
        subst j
        by_cases hnext : k.val + 1 < topClockSpan n
        · cases htarget :
            (Z.1.1 (ring.rightNeighbor e)).qOut with
          | E =>
              left
              exact ⟨(⟨k.val + 1, hnext⟩ :
                Fin (topClockSpan n)),
                topFreshTailFirstBorderHomeBarrierRootHop
                  ring C s hn hbad Z root k sample
                  hbarrier e hsite hnext htarget,
                Or.inr rfl⟩
          | U =>
              have hoccupied :
                  (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E := by
                intro h
                rw [htarget] at h
                cases h
              left
              exact ⟨k,
                topFreshTailFirstBorderHomeBarrierOccupiedStep
                  ring C s hn hbad Z root k sample
                  hbarrier e hsite hnext hoccupied,
                Or.inl rfl⟩
          | D value tail =>
              have hoccupied :
                  (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E := by
                intro h
                rw [htarget] at h
                cases h
              left
              exact ⟨k,
                topFreshTailFirstBorderHomeBarrierOccupiedStep
                  ring C s hn hbad Z root k sample
                  hbarrier e hsite hnext hoccupied,
                Or.inl rfl⟩
        · have hterminal : k.val + 1 = topClockSpan n := by
            have hk := k.isLt
            omega
          cases hinput :
              (Z.1.1 (ring.rightNeighbor e)).qIn with
          | E =>
              cases hcarry :
                  (Z.1.1 (ring.rightNeighbor e)).qCarry with
              | OFF =>
                  right
                  exact topFreshTailAcceptedPortRootHomeStaircase
                    ring C s hn hbad Z root k sample
                    hbarrier hterminal e hsite hinput hcarry
              | L bit err =>
                  have hblocked :
                      (Z.1.1 (ring.rightNeighbor e)).qIn.isE =
                          false ∨
                      (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff =
                          false :=
                    Or.inr (by simp [hcarry, QCarry.isOff])
                  left
                  exact ⟨k,
                    topFreshTailFirstBorderHomeBarrierPortBlocked
                      ring C s hn hbad Z root k sample
                      hbarrier hterminal e hsite hblocked,
                    Or.inl rfl⟩
          | P value tail =>
              have hblocked :
                  (Z.1.1 (ring.rightNeighbor e)).qIn.isE =
                      false ∨
                  (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff =
                      false :=
                Or.inl (by simp [hinput, InTok.isE])
              left
              exact ⟨k,
                topFreshTailFirstBorderHomeBarrierPortBlocked
                  ring C s hn hbad Z root k sample
                  hbarrier hterminal e hsite hblocked,
                Or.inl rfl⟩
          | S value tail =>
              have hblocked :
                  (Z.1.1 (ring.rightNeighbor e)).qIn.isE =
                      false ∨
                  (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff =
                      false :=
                Or.inl (by simp [hinput, InTok.isE])
              left
              exact ⟨k,
                topFreshTailFirstBorderHomeBarrierPortBlocked
                  ring C s hn hbad Z root k sample
                  hbarrier hterminal e hsite hblocked,
                Or.inl rfl⟩
          | X =>
              have hblocked :
                  (Z.1.1 (ring.rightNeighbor e)).qIn.isE =
                      false ∨
                  (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff =
                      false :=
                Or.inl (by simp [hinput, InTok.isE])
              left
              exact ⟨k,
                topFreshTailFirstBorderHomeBarrierPortBlocked
                  ring C s hn hbad Z root k sample
                  hbarrier hterminal e hsite hblocked,
                Or.inl rfl⟩
      · have hahead : k.val < j.val := by omega
        left
        exact ⟨k,
          topFreshTailFirstBorderHomeBarrierAheadStep
            ring C s hn hbad Z root k sample
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
            topFreshTailFirstBorderHomeBarrierBorderIncoming
              ring C s hn hbad hl Z root k sample
              hbarrier hkzero e
              (by rw [hkzero]; exact hzeroIncoming),
            Or.inl rfl⟩
        · have hkpositive : 0 < k.val := by omega
          left
          exact ⟨k,
            topFreshTailFirstBorderHomeBarrierIncomingZero
              ring C s hn hbad hl Z root k sample
              hbarrier hkpositive e hzeroIncoming,
            Or.inl rfl⟩
      · have hjpositive : 0 < j.val := by omega
        have hpredecessor :=
          topFreshTailCausalIncomingPredecessor
            ring hn s j hjpositive e htarget
        have hprevBound : j.val - 1 < topClockSpan n := by
          have hj := j.isLt
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
        topFreshTailFirstBorderHomeBarrierAwayStep
          ring C s hn hbad Z root k sample
          hbarrier e hawaySource hawayTarget,
        Or.inl rfl⟩

/-- Fold any finite scheduler word, stopping at the first selected
acceptance of the tracked root. Before such a letter the exact
home barrier persists, and its position cannot decrease.

The receipt witness is an actual prefix of the scheduler word;
the suffix after it is not assumed to preserve the just-created
anchor cut. Consumer: topFreshTailFirstRootStaircaseExit and
the J5 earliest-root assembly. -/
theorem topFreshTailFirstBorderBarrierRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n)) :
    ∀ (Z : TopFixedTraceState n)
      (root : TopFreshTailCarrier (topClockSpan n))
      (k : Fin (topClockSpan n))
      (sample : DigitSample (compileAdvice (ceilLogTwo n)) n),
      TopFreshTailFirstBorderHomeBarrier
        ring C s Z root k sample →
      (∃ finalPosition : Fin (topClockSpan n),
        TopFreshTailFirstBorderHomeBarrier
          ring C s
          (word.foldl (topFixedTraceNext ring C) Z)
          root finalPosition sample ∧
        k.val ≤ finalPosition.val) ∨
      (∃ (pre suffix : List (Fin n)) (edge : Fin n),
        word = pre ++ edge :: suffix ∧
        topClockGenuineTailAccepted C s
          (topFixedTraceNext ring C
            (pre.foldl (topFixedTraceNext ring C) Z) edge) ∧
        ∀ j : Fin (topClockSpan n),
          TopFreshTailFirstBorderHomeSlot
            ring C s
            (topFixedTraceNext ring C
              (pre.foldl (topFixedTraceNext ring C) Z) edge)
            root j) := by
  induction word with
  | nil =>
      intro Z root k sample hbarrier
      left
      exact ⟨k, hbarrier, Nat.le_refl _⟩
  | cons e rest ih =>
      intro Z root k sample hbarrier
      rcases topFreshTailFirstBorderBarrierEdge
          ring C s hn hbad hl Z root k sample hbarrier e with
        ⟨moved, hbarrierNext, hstep⟩ | ⟨hanchor, hhomes⟩
      · rcases ih (topFixedTraceNext ring C Z e)
          root moved sample hbarrierNext with
          ⟨finalPosition, hfinal, hmonotone⟩ |
          ⟨pre, suffix, edge, hword, haccepted, hfinalHomes⟩
        · left
          refine ⟨finalPosition, ?_, ?_⟩
          · change
              TopFreshTailFirstBorderHomeBarrier ring C s
                (rest.foldl (topFixedTraceNext ring C)
                  (topFixedTraceNext ring C Z e))
                root finalPosition sample
            exact hfinal
          · rcases hstep with hstay | hmove
            · rw [hstay] at hmonotone
              exact hmonotone
            · omega
        · right
          refine ⟨e :: pre, suffix, edge, ?_, ?_, ?_⟩
          · rw [hword]
            rfl
          · change
              topClockGenuineTailAccepted C s
                (topFixedTraceNext ring C
                  (pre.foldl (topFixedTraceNext ring C)
                    (topFixedTraceNext ring C Z e))
                  edge)
            exact haccepted
          · change
              ∀ j : Fin (topClockSpan n),
                TopFreshTailFirstBorderHomeSlot ring C s
                  (topFixedTraceNext ring C
                    (pre.foldl (topFixedTraceNext ring C)
                      (topFixedTraceNext ring C Z e))
                    edge)
                  root j
            exact hfinalHomes
      · right
        exact ⟨[], rest, e, rfl, hanchor, hhomes⟩

/-- At the tracked-root accepted edge there is a genuine comparison
tail receipt and a home-sampled fresh carrier at every source slot.
Every OLD inherited/oldVisit identity observed at any earlier word
prefix has a unique actual historical terminal comparison service
at or before this accepted edge. The OLD consumed origin is attached
to the OLD head slot; it is not used as a full identity on its own.

Uses AcceptedPortRootHomeStaircase and HistoricalOldExitRows,
with the no-live-OLD alternative excluded by the fresh home slots.
Consumer: J5 first-root family exhaustion and post-anchor W base. -/
theorem topFreshTailFirstRootStaircaseExit
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
    (e : Fin n)
    (hsite : e = certSite s k.val)
    (hyi :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qIn = .E)
    (hyc :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qCarry = .OFF) :
    topClockGenuineTailAccepted C s
      (topFixedTraceRun ring C (word ++ [e])) ∧
    (∀ j : Fin (topClockSpan n),
      TopFreshTailFirstBorderHomeSlot
        ring C s (topFixedTraceRun ring C (word ++ [e]))
        root j) ∧
    (∀ (u suffix : List (Fin n))
      (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      word ++ [e] = u ++ suffix →
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C u)).slots j = some a →
      ((∃ i : Fin (topClockSpan n),
          a.origin = .inherited i) ∨
        (∃ i t : Fin (topClockSpan n),
          a.origin = .oldVisit i t)) →
      ∃ (pre rest : List (Fin n))
        (exported : DigitExport (compileAdvice (ceilLogTwo n)) n),
        u ++ suffix =
          pre ++ [certSite s (topClockSpan n - 1)] ++ rest ∧
        u.length ≤ pre.length ∧
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C pre)).slots
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ : Fin (topClockSpan n)) = some a ∧
        topFreshTailGenealogyPortExport ring C s
          (topFixedTraceRun ring C pre)
          (certSite s (topClockSpan n - 1)) = some exported ∧
        DigitRecordedExport
          (topFixedTraceRun ring C (u ++ suffix)).1.2
          exported ∧
        exported.time = pre.length + 1 ∧
        TopFreshTailAuditHistoricalPortAt ring C s
          (u ++ suffix) pre.length exported ∧
        (∀ other : Nat,
          TopFreshTailAuditHistoricalPortAt ring C s
            (u ++ suffix) other exported →
          other = pre.length) ∧
        (exported.time, some a.origin) ∈
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (u ++ suffix))).consumed) := by
  have hpost :=
    topFreshTailAcceptedPortRootHomeStaircase
      ring C s hn hbad
      (topFixedTraceRun ring C word)
      root k sample hbarrier hterminal e hsite hyi hyc
  have hsnoc :=
    topFreshTailFifoRunSnoc ring C word e
  refine ⟨?_, ?_, ?_⟩
  · rw [hsnoc]
    exact hpost.1
  · intro j
    rw [hsnoc]
    exact hpost.2 j
  · intro u suffix j a hdecomp hslot hold
    rcases topFreshTailHistoricalOldExitRows
        ring C s hn hbad hl suffix u j a hslot hold with
      ⟨livePosition, hlive⟩ | hserviced
    · have hfull :
          topFixedTraceRun ring C (u ++ suffix) =
            topFixedTraceNext ring C
              (topFixedTraceRun ring C word) e := by
        rw [← hdecomp]
        exact hsnoc
      rw [hfull] at hlive
      obtain ⟨other, hother,
        ⟨stamp, hfresh⟩, _, _⟩ := hpost.2 livePosition
      rw [hother] at hlive
      have hsame : a = other := (Option.some.inj hlive).symm
      rcases hold with ⟨i, hi⟩ | ⟨i, t, ht⟩
      · rw [hsame, hfresh] at hi
        cases hi
      · rw [hsame, hfresh] at ht
        cases ht
    · exact hserviced

end L3

#print axioms L3.topFreshTailFirstBorderBarrierEdge
#print axioms L3.topFreshTailFirstBorderBarrierRun
#print axioms L3.topFreshTailFirstRootStaircaseExit
