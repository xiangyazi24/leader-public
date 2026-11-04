import Leader.L3.Top.FreshTailTicket

/-!
Q7c P.3 J3: the part of the first
border barrier that J3 needs. Before the first genuine border tail is
accepted, every fresh-border carrier that is not itself a genuinely
zero-sampled D(true) lies strictly behind a live fresh D(true), and
the border never holds a fresh D(false). Hence the first fresh-family
port acceptance is the genuine anchor, and every earlier accepted
port spends a nonfresh (inherited or oldVisit) ticket.

The old-family-ahead half of the J5 barrier is not needed here and is
not stated.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- J3 fresh-family barrier on a reached cut (I.order, the fresh
half; I.receipts restricted to the pre-anchor prefix). -/
structure TopFreshTailFirstBorderBarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop where
  borderFresh :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
      j.val = 0 →
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      topFreshTailTicketIsFresh a.origin = true →
      ∀ v : Fin (compileAdvice (ceilLogTwo n)).topA,
        (Z.1.1 (certSite s j.val)).qOut ≠ .D v false
  freshBehind :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      topFreshTailTicketIsFresh a.origin = true →
      0 < j.val →
      (∀ v : Fin (compileAdvice (ceilLogTwo n)).topA,
        (Z.1.1 (certSite s j.val)).qOut ≠ .D v true) →
      ∃ (k : Fin (topClockSpan n)) (b : TopFreshTailCarrier (topClockSpan n))
        (v : Fin (compileAdvice (ceilLogTwo n)).topA),
        j.val < k.val ∧
        (topFreshTailGenealogy ring C s Z).slots k = some b ∧
        topFreshTailTicketIsFresh b.origin = true ∧
        (Z.1.1 (certSite s k.val)).qOut = .D v true
  spentAll :
    ∀ entry ∈ (topFreshTailGenealogy ring C s Z).consumed,
      ∃ o : TopFreshTailOrigin (topClockSpan n),
        entry.2 = some o ∧ topFreshTailTicketIsFresh o = false

/-- A live fresh D(true) at a positive offset survives an edge whose
NEW state is not a genuine tail acceptance: it stays, or moves right
with its byte. Consumer: topFreshTailFirstBorderBarrierStep. -/
theorem topFreshTailTicketWitnessTrack
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hng : ¬ topClockGenuineTailAccepted C s (topFixedTraceNext ring C Z e))
    (k : Fin (topClockSpan n)) (b : TopFreshTailCarrier (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hb : (topFreshTailGenealogy ring C s Z).slots k = some b)
    (hfr : topFreshTailTicketIsFresh b.origin = true)
    (hold : (Z.1.1 (certSite s k.val)).qOut = .D v true)
    (hk : 0 < k.val) :
    ∃ k' : Fin (topClockSpan n),
      k.val ≤ k'.val ∧
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots k' =
        some b ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k'.val)).qOut = .D v true := by
  rcases topFreshTailTicketDataTrack ring C s hn hbad Z hreach e k v true hold b hb with
    ⟨hslot, hnD⟩ | ⟨_, _, ⟨hnext, hnD, hslot⟩ | ⟨hlast, ⟨x, hx⟩, _⟩⟩ | ⟨hk0, _⟩
  · exact ⟨k, Nat.le_refl _, hslot, hnD⟩
  · exact ⟨⟨k.val + 1, hnext⟩, by simp only; omega, hslot, hnD⟩
  · exfalso
    apply hng
    have hkFin : k = ⟨topClockSpan n - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [hkFin] at hb
    have hold' : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v true := by
      rw [show topClockSpan n - 1 = k.val by omega]; exact hold
    have hfresh : ∃ t : Nat, b.origin = .freshBorder t := by
      cases ho : b.origin with
      | inherited i => rw [ho] at hfr; cases hfr
      | oldVisit i j => rw [ho] at hfr; cases hfr
      | freshBorder t => exact ⟨t, rfl⟩
    exact topFreshTailTicketFreshExportGenuine ring C s hn hbad Z hreach e x hx b hb
      hfresh v hold'
  · omega

/-- J3 barrier induction step on an edge that does not itself accept
the first genuine border tail. Consumer:
topFreshTailFirstBorderBarrierFromCut. -/
theorem topFreshTailFirstBorderBarrierStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (B : TopFreshTailFirstBorderBarrier ring C s Z)
    (e : Fin n)
    (hng : ¬ topClockGenuineTailAccepted C s (topFixedTraceNext ring C Z e)) :
    TopFreshTailFirstBorderBarrier ring C s (topFixedTraceNext ring C Z e) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  refine ⟨?_, ?_, ?_⟩
  · intro j a hj0 hnew hfr v hD
    rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e j a hnew with
      ⟨hold, _, hphys⟩ | ⟨hpos, _⟩ | ⟨_, _, _, _, _, _, hnU⟩ | ⟨_, _, _, hnew'⟩
    · rcases hphys with heq | ⟨hpos, _⟩
      · exact B.borderFresh j a hj0 hold hfr v (heq ▸ hD)
      · omega
    · omega
    · rw [hnU] at hD; cases hD
    · rcases hnew' with h | ⟨d, h⟩ <;> (rw [h] at hD; cases hD)
  · intro j a hnew hfr hpos hnotD
    rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e j a hnew with
      ⟨hold, _, hphys⟩ | ⟨hpos', _, hoE, hold, w, u, hpD, hnD⟩ |
      ⟨_, p, v, hp, ha, hoD, hnU⟩ | ⟨hj0, _⟩
    · have hnotOld : ∀ v : Fin (compileAdvice (ceilLogTwo n)).topA,
          (Z.1.1 (certSite s j.val)).qOut ≠ .D v true := by
        intro v hv
        rcases hphys with heq | ⟨_, _, hoU, _⟩
        · exact hnotD v (heq.trans hv)
        · rw [hoU] at hv; cases hv
      obtain ⟨k, b, v, hjk, hb, hfrb, hkD⟩ := B.freshBehind j a hold hfr hpos hnotOld
      obtain ⟨k', hle, hb', hnD'⟩ := topFreshTailTicketWitnessTrack ring C s hn hbad
        Z hreach e hng k b v hb hfrb hkD (by omega)
      exact ⟨k', b, v, by omega, hb', hfrb, hnD'⟩
    · have hu : u = false := by
        cases u with
        | false => rfl
        | true => exact absurd hnD (hnotD w)
      subst hu
      by_cases hj1 : j.val - 1 = 0
      · exact absurd hpD (B.borderFresh _ a hj1 hold hfr w)
      · have hnotOld : ∀ v : Fin (compileAdvice (ceilLogTwo n)).topA,
            (Z.1.1 (certSite s (j.val - 1))).qOut ≠ .D v true := by
          intro v hv
          rw [hpD] at hv
          cases hv
        obtain ⟨k, b, v, hjk, hb, hfrb, hkD⟩ :=
          B.freshBehind _ a hold hfr (by simp only; omega) hnotOld
        simp only at hjk
        have hkj : k.val ≠ j.val := by
          intro hkj
          have hkFin : k = j := Fin.ext hkj
          subst hkFin
          rw [hoE] at hkD
          cases hkD
        obtain ⟨k', hle, hb', hnD'⟩ := topFreshTailTicketWitnessTrack ring C s hn hbad
          Z hreach e hng k b v hb hfrb hkD (by omega)
        exact ⟨k', b, v, by omega, hb', hfrb, hnD'⟩
    · subst ha
      have hpfr : topFreshTailTicketIsFresh p.origin = true := by
        rcases topFreshTailTicketRearmOrigin j (Z.1.2.clock + 1) p with
          ⟨hj0, _⟩ | ⟨_, ⟨i, _, h⟩ | ⟨i, k, _, h⟩ | ⟨b, hpo, _⟩⟩
        · omega
        · rw [h] at hfr; cases hfr
        · rw [h] at hfr; cases hfr
        · rw [hpo]; rfl
      obtain ⟨k', hle, hb', hnD'⟩ := topFreshTailTicketWitnessTrack ring C s hn hbad
        Z hreach e hng j p v hp hpfr hoD hpos
      have hne : k'.val ≠ j.val := by
        intro hk
        have hkFin : k' = j := Fin.ext hk
        subst hkFin
        rw [hnU] at hnD'
        cases hnD'
      exact ⟨k', p, v, by omega, hb', hpfr, hnD'⟩
    · omega
  · intro entry hmem
    have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
    rw [topFreshTailTicketConsumedStep ring C s hn Z hreach e, List.mem_append] at hmem
    rcases hmem with hold | hadd
    · exact B.spentAll entry hold
    · cases hx : topFreshTailGenealogyPortExport ring C s Z e with
      | none => rw [hx] at hadd; simp at hadd
      | some x =>
          rw [hx] at hadd
          obtain ⟨_, v, t, hD⟩ := topFreshTailTicketPortExportSource ring C s Z e x hx
          have hnotE : (Z.1.1 (certSite s
              (⟨topClockSpan n - 1, by omega⟩ : Fin (topClockSpan n)).val)).qOut ≠ .E := by
            simp only; rw [hD]; intro h; cases h
          cases hc : (topFreshTailGenealogy ring C s Z).slots
              ⟨topClockSpan n - 1, by omega⟩ with
          | none => exact absurd ((hqueue.slot _).2 hc) hnotE
          | some c =>
              rw [hc] at hadd
              simp only [Option.toList, List.map_cons, List.map_nil,
                List.mem_singleton, Option.map_some] at hadd
              subst hadd
              cases hf : topFreshTailTicketIsFresh c.origin with
              | false => exact ⟨c.origin, rfl, hf⟩
              | true =>
                  exfalso
                  cases t with
                  | false =>
                      obtain ⟨k, _, _, hjk, _, _, _⟩ :=
                        B.freshBehind _ c hc hf (by simp only; omega)
                          (by intro v' h; simp only at h; rw [hD] at h; cases h)
                      simp only at hjk
                      have := k.isLt
                      omega
                  | true =>
                      have hfresh : ∃ b : Nat, c.origin = .freshBorder b := by
                        cases ho : c.origin with
                        | inherited i => rw [ho] at hf; cases hf
                        | oldVisit i j => rw [ho] at hf; cases hf
                        | freshBorder b => exact ⟨b, rfl⟩
                      exact hng (topFreshTailTicketFreshExportGenuine ring C s hn hbad
                        Z hreach e x hx c hc hfresh v hD)

/-- The barrier holds at the audit start: the only initial fresh
carrier is an unread border U, and nothing is spent.
Consumer: topFreshTailFirstBorderBarrier. -/
theorem topFreshTailFirstBorderBarrierInitial
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailFirstBorderBarrier ring C s ((C, digitAuditInitial (piD C)), []) := by
  have hslots : (topFreshTailGenealogy ring C s
      ((C, digitAuditInitial (piD C)), [])).slots =
      topFreshTailGenealogyInitialSlot C s := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro j a _ h hfr v hD
    rw [hslots] at h
    rcases topFreshTailTicketInitialSlotOrigin C s j a h with h1 | ⟨_, _, hU⟩
    · rw [h1] at hfr; cases hfr
    · change (C (certSite s j.val)).qOut = _ at hD
      rw [hU] at hD; cases hD
  · intro j a h hfr hpos _
    rw [hslots] at h
    rcases topFreshTailTicketInitialSlotOrigin C s j a h with h1 | ⟨hj0, _, _⟩
    · rw [h1] at hfr; cases hfr
    · omega
  · intro entry h
    change entry ∈ ([] : List _) at h
    cases h

/-- Barrier along any future word from a barrier cut, as long as no
nonempty prefix of the word reaches a genuine tail acceptance.
Consumer: topFreshTailFirstBorderBarrier. -/
theorem topFreshTailFirstBorderBarrierFromCut
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    ∀ (w : List (Fin n)) (Y : TopFixedTraceState n),
      topClockReached ring C Y →
      TopFreshTailFirstBorderBarrier ring C s Y →
      (∀ pre suffix : List (Fin n), pre ++ suffix = w → pre ≠ [] →
        ¬ topClockGenuineTailAccepted C s (pre.foldl (topFixedTraceNext ring C) Y)) →
      TopFreshTailFirstBorderBarrier ring C s (w.foldl (topFixedTraceNext ring C) Y) := by
  intro w
  induction w with
  | nil => intro Y _ hB _; exact hB
  | cons e rest ih =>
      intro Y hY hB hpre
      have hng : ¬ topClockGenuineTailAccepted C s (topFixedTraceNext ring C Y e) :=
        hpre [e] rest rfl (by simp)
      apply ih (topFixedTraceNext ring C Y e) (topClockReachedNext ring C Y e hY)
        (topFreshTailFirstBorderBarrierStep ring C s hn hbad Y hY hB e hng)
      intro pre suffix h hne
      exact hpre (e :: pre) suffix (by rw [← h]; rfl) (by simp)

/-- Item 3, the part J3 needs. On every actual word none of whose
nonempty prefixes ends with the first genuine border tail accepted,
the fresh family sits behind a live genuinely zero-sampled D(true),
and every consumed port receipt so far spent a nonfresh ticket.
Consumer: P.3 J3 (topFreshTailPreTailVisitCharge); the J5 lane owns
the old-family-ahead half. -/
theorem topFreshTailFirstBorderBarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (hpre : ∀ pre suffix : List (Fin n), pre ++ suffix = word → pre ≠ [] →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre)) :
    TopFreshTailFirstBorderBarrier ring C s (topFixedTraceRun ring C word) :=
  topFreshTailFirstBorderBarrierFromCut ring C s hn hbad word
    ((C, digitAuditInitial (piD C)), [])
    (by unfold topClockReached; rfl)
    (topFreshTailFirstBorderBarrierInitial ring C s) hpre

end L3

#print axioms L3.topFreshTailTicketWitnessTrack
#print axioms L3.topFreshTailFirstBorderBarrierStep
#print axioms L3.topFreshTailFirstBorderBarrierInitial
#print axioms L3.topFreshTailFirstBorderBarrierFromCut
#print axioms L3.topFreshTailFirstBorderBarrier
