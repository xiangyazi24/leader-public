import Leader.L3.Top.FreshTailTicketRows

/-!
Q7c P.3 J3: the historical
visit-ticket invariant of the actual reached trace.

Tickets are origins: `inherited i` (one per initial source occupant)
and `oldVisit i k` (minted when the original inherited carrier i, as
D(true), leaves offset k >= 1). The spent tickets are the nonfresh
origins recorded in the genealogy's real `consumed` list. No new
ghost field is added: everything is a function of the scheduler word.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The fresh border family (the only family that may rekey/rearm
without minting a historical ticket). -/
def topFreshTailTicketIsFresh {r : Nat} : TopFreshTailOrigin r → Bool
  | .freshBorder _ => true
  | _ => false

/-- The nonfresh origins spent by the actual chronological port
receipts, in order. -/
def topFreshTailTicketSpent {n : Nat} (G : TopFreshTailGenealogyState n) :
    List (TopFreshTailOrigin (topClockSpan n)) :=
  G.consumed.filterMap (fun entry =>
    match entry.2 with
    | some o => if topFreshTailTicketIsFresh o = true then none else some o
    | none => none)

/-- J3 historical ticket invariant on the actual trace (I.ids
and I.receipts): inherited carriers only move right; oldVisit
carriers sit right of their mint cell, read at an interior site and
are never tails; live tickets are unique; spent tickets are distinct,
never live again, and once oldVisit(i,k) is issued the original
inherited carrier i is strictly right of k for ever. -/
structure TopFreshTailTicketHistory
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop where
  inheritedAhead :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n))
      (i : Fin (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      a.origin = .inherited i → i.val ≤ j.val
  visitShape :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n))
      (i k : Fin (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      a.origin = .oldVisit i k →
      i.val ≤ k.val ∧ 0 < k.val ∧ k.val ≤ j.val ∧
      ((Z.1.1 (certSite s j.val)).qOut = .U → j = k) ∧
      (∀ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        (Z.1.1 (certSite s j.val)).qOut = .D v t → t = false)
  liveUnique :
    ∀ (i j : Fin (topClockSpan n)) (a b : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots i = some a →
      (topFreshTailGenealogy ring C s Z).slots j = some b →
      a.origin = b.origin → topFreshTailTicketIsFresh a.origin = false → i = j
  spentVisitShape :
    ∀ i k : Fin (topClockSpan n),
      TopFreshTailOrigin.oldVisit i k ∈
        topFreshTailTicketSpent (topFreshTailGenealogy ring C s Z) →
      i.val ≤ k.val ∧ 0 < k.val
  spentNotLive :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      a.origin ∉ topFreshTailTicketSpent (topFreshTailGenealogy ring C s Z)
  spentNodup :
    (topFreshTailTicketSpent (topFreshTailGenealogy ring C s Z)).Nodup
  visitIssued :
    ∀ i k : Fin (topClockSpan n),
      ((∃ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
          (topFreshTailGenealogy ring C s Z).slots j = some a ∧
          a.origin = .oldVisit i k) ∨
        TopFreshTailOrigin.oldVisit i k ∈
          topFreshTailTicketSpent (topFreshTailGenealogy ring C s Z)) →
      ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
        (topFreshTailGenealogy ring C s Z).slots j = some a →
        a.origin = .inherited i → k.val < j.val

/-- Spent tickets are never fresh. Consumer: History clauses. -/
theorem topFreshTailTicketSpentNonfresh
    {n : Nat} (G : TopFreshTailGenealogyState n)
    (o : TopFreshTailOrigin (topClockSpan n))
    (h : o ∈ topFreshTailTicketSpent G) :
    topFreshTailTicketIsFresh o = false := by
  unfold topFreshTailTicketSpent at h
  rw [List.mem_filterMap] at h
  obtain ⟨entry, _, hentry⟩ := h
  cases h2 : entry.2 with
  | none => rw [h2] at hentry; cases hentry
  | some p =>
      rw [h2] at hentry
      simp only at hentry
      by_cases hp : topFreshTailTicketIsFresh p = true
      · rw [if_pos hp] at hentry; cases hentry
      · rw [if_neg hp] at hentry
        cases hentry
        simpa using hp

/-- The rearm child's origin: fresh at the border, otherwise the
parent's inherited ticket becomes oldVisit(i, j) and the other two
families keep their origin. Consumer: J3 rearm rows. -/
theorem topFreshTailTicketRearmOrigin
    {r : Nat} (j : Fin r) (time : Nat) (p : TopFreshTailCarrier r) :
    (j.val = 0 ∧ (topFreshTailGenealogyRearm j time p).origin = .freshBorder time) ∨
    (j.val ≠ 0 ∧
      ((∃ i, p.origin = .inherited i ∧
          (topFreshTailGenealogyRearm j time p).origin = .oldVisit i j) ∨
       (∃ i k, p.origin = .oldVisit i k ∧
          (topFreshTailGenealogyRearm j time p).origin = .oldVisit i k) ∨
       (∃ b, p.origin = .freshBorder b ∧
          (topFreshTailGenealogyRearm j time p).origin = .freshBorder b))) := by
  by_cases hj : j.val = 0
  · left
    exact ⟨hj, by simp [topFreshTailGenealogyRearm, hj]⟩
  · right
    refine ⟨hj, ?_⟩
    cases hp : p.origin with
    | inherited i =>
        exact Or.inl ⟨i, rfl, by simp [topFreshTailGenealogyRearm, hj, hp]⟩
    | oldVisit i k =>
        exact Or.inr (Or.inl ⟨i, k, rfl, by simp [topFreshTailGenealogyRearm, hj, hp]⟩)
    | freshBorder b =>
        exact Or.inr (Or.inr ⟨b, rfl, by simp [topFreshTailGenealogyRearm, hj, hp]⟩)

/-- The spent list grows on one edge by the OLD terminal carrier's
origin exactly when the port event occurs and that origin is not
fresh. Consumer: J3 receipt clauses. -/
theorem topFreshTailTicketSpentStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (o : TopFreshTailOrigin (topClockSpan n))
    (h : o ∈ topFreshTailTicketSpent
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e))) :
    o ∈ topFreshTailTicketSpent (topFreshTailGenealogy ring C s Z) ∨
    ((∃ x, topFreshTailGenealogyPortExport ring C s Z e = some x) ∧
      ∃ c : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s Z).slots
          ⟨topClockSpan n - 1, by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ = some c ∧
        c.origin = o) := by
  unfold topFreshTailTicketSpent at h
  rw [topFreshTailTicketConsumedStep ring C s hn Z hreach e,
    List.filterMap_append, List.mem_append] at h
  rcases h with hold | hnew
  · exact Or.inl hold
  · right
    cases hx : topFreshTailGenealogyPortExport ring C s Z e with
    | none =>
        rw [hx] at hnew
        simp at hnew
    | some x =>
        rw [hx] at hnew
        refine ⟨⟨x, rfl⟩, ?_⟩
        cases hc : (topFreshTailGenealogy ring C s Z).slots
            ⟨topClockSpan n - 1, by
              have hr := cert_rho_ge_three n hn
              change 3 ≤ topClockSpan n at hr
              omega⟩ with
        | none =>
            rw [hc] at hnew
            simp at hnew
        | some c =>
            rw [hc] at hnew
            refine ⟨c, rfl, ?_⟩
            simp only [Option.toList, List.map_cons, List.map_nil,
              List.filterMap_cons, List.filterMap_nil, Option.map_some] at hnew
            by_cases hf : topFreshTailTicketIsFresh c.origin = true
            · simp [hf] at hnew
            · simp [hf] at hnew
              exact hnew.symm

/-- Item 1. On every actual edge an original inherited carrier
is never recreated: a NEW carrier with an inherited ticket is the same
OLD carrier, either kept at its slot or moved exactly one offset to
the right. Together with `visitIssued` (once oldVisit(i,k) is issued
the original is strictly right of k) it never revisits an offset.
Consumer: P.3 J3 (topFreshTailTicketHistoryStep, visitIssued row). -/
theorem topFreshTailInheritedCarrierMonotoneNoRevisit
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n)) (i : Fin (topClockSpan n))
    (hnew : (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = some a)
    (horig : a.origin = .inherited i) :
    ∃ j0 : Fin (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots j0 = some a ∧
      (j0 = j ∨ j0.val + 1 = j.val) := by
  rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e j a hnew with
    ⟨hold, _, _⟩ | ⟨hpos, _, _, hold, _⟩ | ⟨_, p, _, _, ha, _, _⟩ |
    ⟨_, _, ha, _⟩
  · exact ⟨j, hold, Or.inl rfl⟩
  · exact ⟨_, hold, Or.inr (by simp only; omega)⟩
  · subst ha
    rcases topFreshTailTicketRearmOrigin j (Z.1.2.clock + 1) p with
      ⟨_, h⟩ | ⟨_, ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩⟩ <;>
      (rw [h] at horig; cases horig)
  · subst ha
    cases horig

/-- A NEW nonfresh carrier is an OLD carrier, or the oldVisit(i,j)
child just minted at the served slot j by the original inherited i
leaving as D(true). Consumer: J3 history step (uniqueness, spent and
issue clauses). -/
theorem topFreshTailTicketNonfreshSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew : (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = some a)
    (hnf : topFreshTailTicketIsFresh a.origin = false) :
    (∃ j0 : Fin (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots j0 = some a) ∨
    (a.born = Z.1.2.clock + 1 ∧ e = certSite s j.val ∧
      ∃ (i : Fin (topClockSpan n)) (p : TopFreshTailCarrier (topClockSpan n))
        (v : Fin (compileAdvice (ceilLogTwo n)).topA),
        a.origin = .oldVisit i j ∧
        (topFreshTailGenealogy ring C s Z).slots j = some p ∧
        p.origin = .inherited i ∧
        (Z.1.1 (certSite s j.val)).qOut = .D v true) := by
  rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e j a hnew with
    ⟨hold, _, _⟩ | ⟨_, _, _, hold, _⟩ | ⟨hsrc, p, v, hp, ha, hoD, _⟩ |
    ⟨_, _, ha, _⟩
  · exact Or.inl ⟨j, hold⟩
  · exact Or.inl ⟨_, hold⟩
  · subst ha
    rcases topFreshTailTicketRearmOrigin j (Z.1.2.clock + 1) p with
      ⟨_, h⟩ | ⟨_, ⟨i, hpi, h⟩ | ⟨i, k, hpo, _⟩ | ⟨_, _, h⟩⟩
    · rw [h] at hnf; cases hnf
    · exact Or.inr ⟨rfl, hsrc, i, p, v, h, hp, hpi, hoD⟩
    · have hshape := H.visitShape j p i k hp hpo
      have := hshape.2.2.2.2 v true hoD
      cases this
    · rw [h] at hnf; cases hnf
  · subst ha
    cases hnf

/-- History clause inheritedAhead on one actual edge.
Consumer: topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketInheritedAheadStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n))
      (i : Fin (topClockSpan n)),
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
        some a →
      a.origin = .inherited i → i.val ≤ j.val := by
  intro j a i hnew horig
  obtain ⟨j0, hold, hj⟩ := topFreshTailInheritedCarrierMonotoneNoRevisit
    ring C s hn hbad Z hreach e j a i hnew horig
  have h := H.inheritedAhead j0 a i hold horig
  rcases hj with h0 | h0
  · subst h0; exact h
  · omega

/-- History clause visitShape on one actual edge.
Consumer: topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketVisitShapeStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n))
      (i k : Fin (topClockSpan n)),
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
        some a →
      a.origin = .oldVisit i k →
      i.val ≤ k.val ∧ 0 < k.val ∧ k.val ≤ j.val ∧
      (((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut = .U → j = k) ∧
      (∀ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut = .D v t →
        t = false) := by
  intro j a i k hnew horig
  rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e j a hnew with
    ⟨hold, _, hphys⟩ | ⟨hpos, _, _, hold, w, u, hpD, hnD⟩ |
    ⟨hsrc, p, v, hp, ha, hoD, hnU⟩ | ⟨_, _, ha, _⟩
  · obtain ⟨h1, h2, h3, hU, hD⟩ := H.visitShape j a i k hold horig
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · intro hnU
      rcases hphys with heq | ⟨_, _, _, hnD⟩
      · exact hU (heq ▸ hnU)
      · rw [hnD] at hnU; cases hnU
    · intro v t hnD
      rcases hphys with heq | ⟨_, _, _, hnD'⟩
      · exact hD v t (heq ▸ hnD)
      · rw [hnD'] at hnD
        cases hnD
        rfl
  · obtain ⟨h1, h2, h3, _, hD⟩ := H.visitShape _ a i k hold horig
    have hu : u = false := hD w u hpD
    simp only at h3
    refine ⟨h1, h2, by omega, ?_, ?_⟩
    · intro hnU; rw [hnD] at hnU; cases hnU
    · intro v t h
      rw [hnD] at h
      cases h
      exact hu
  · subst ha
    rcases topFreshTailTicketRearmOrigin j (Z.1.2.clock + 1) p with
      ⟨_, h⟩ | ⟨hj, ⟨i', hpi, h⟩ | ⟨i', k', hpo, _⟩ | ⟨_, _, h⟩⟩
    · rw [h] at horig; cases horig
    · rw [h] at horig
      cases horig
      have hi := H.inheritedAhead j p i hp hpi
      refine ⟨hi, by omega, Nat.le_refl _, fun _ => rfl, ?_⟩
      intro v t h'
      rw [hnU] at h'
      cases h'
    · have := (H.visitShape j p i' k' hp hpo).2.2.2.2 v true hoD
      cases this
    · rw [h] at horig; cases horig
  · subst ha
    cases horig

/-- History clause liveUnique on one actual edge. Two OLD copies use
OLD uniqueness and the NEW causal-queue identity; a new oldVisit child
cannot share a ticket with a live OLD carrier because the issue clause
puts the original strictly right of its mint cell.
Consumer: topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketLiveUniqueStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    ∀ (i j : Fin (topClockSpan n)) (a b : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots i =
        some a →
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
        some b →
      a.origin = b.origin → topFreshTailTicketIsFresh a.origin = false →
      i = j := by
  intro i1 i2 a b ha hb horig hnf
  have hnfb : topFreshTailTicketIsFresh b.origin = false := horig ▸ hnf
  have hq' := topFreshTailCloseReachedQueue ring C s hn hbad
    (topFixedTraceNext ring C Z e) (topClockReachedNext ring C Z e hreach)
  rcases topFreshTailTicketNonfreshSource ring C s hn hbad Z hreach H e i1 a ha hnf
    with ⟨j1, ha0⟩ | ⟨hba, _, ia, pa, _, hoa, hpa, hpai, _⟩ <;>
  rcases topFreshTailTicketNonfreshSource ring C s hn hbad Z hreach H e i2 b hb hnfb
    with ⟨j2, hb0⟩ | ⟨hbb, _, ib, pb, _, hob, hpb, hpbi, _⟩
  · have hj := H.liveUnique j1 j2 a b ha0 hb0 horig hnf
    subst hj
    have hab : a = b := Option.some.inj (ha0.symm.trans hb0)
    subst hab
    exact hq'.identity i1 i2 a a ha hb rfl rfl
  · have h := H.visitIssued ib i2 (Or.inl ⟨j1, a, ha0, horig.trans hob⟩)
      i2 pb hpb hpbi
    omega
  · have h := H.visitIssued ia i1 (Or.inl ⟨j2, b, hb0, horig.symm.trans hoa⟩)
      i1 pa hpa hpai
    omega
  · exact hq'.identity i1 i2 a b ha hb horig (hba.trans hbb.symm)

/-- History clause spentVisitShape on one actual edge.
Consumer: topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketSpentVisitShapeStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    ∀ i k : Fin (topClockSpan n),
      TopFreshTailOrigin.oldVisit i k ∈ topFreshTailTicketSpent
        (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)) →
      i.val ≤ k.val ∧ 0 < k.val := by
  intro i k hmem
  rcases topFreshTailTicketSpentStep ring C s hn Z hreach e _ hmem with
    hold | ⟨_, c, hc, hco⟩
  · exact H.spentVisitShape i k hold
  · have h := H.visitShape _ c i k hc hco
    exact ⟨h.1, h.2.1⟩

/-- History clause spentNotLive on one actual edge: the accepted OLD
terminal carrier has left its slot, and a freshly minted oldVisit
child was never spent. Consumer: topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketSpentNotLiveStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
        some a →
      a.origin ∉ topFreshTailTicketSpent
        (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)) := by
  intro j a hnew hmem
  have hnf := topFreshTailTicketSpentNonfresh _ a.origin hmem
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  rcases topFreshTailTicketSpentStep ring C s hn Z hreach e a.origin hmem with
    hold | ⟨⟨x, hx⟩, c, hc, hco⟩ <;>
  rcases topFreshTailTicketNonfreshSource ring C s hn hbad Z hreach H e j a hnew hnf
    with ⟨j0, ha0⟩ | ⟨_, _, ia, pa, _, hoa, hpa, hpai, _⟩
  · exact H.spentNotLive j0 a ha0 hold
  · have h := H.visitIssued ia j (Or.inr (hoa ▸ hold)) j pa hpa hpai
    omega
  · have hj0 := H.liveUnique j0 _ a c ha0 hc hco.symm hnf
    subst hj0
    have hac : a = c := Option.some.inj (ha0.symm.trans hc)
    subst hac
    obtain ⟨hsite, v, t, hD⟩ :=
      topFreshTailTicketPortExportSource ring C s Z e x hx
    have hxo : (Z.1.1 e).qOut = .D v t := by rw [hsite]; exact hD
    have hport := topFreshTailTicketPortRow ring C s hn hbad Z hreach e
      hsite v t hxo
    have hguard := hport.2.2.1.1 ⟨x, hx⟩
    have hnewE : ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        (if t then .U else .E) := by
      rw [hport.2.1]
      simp [hguard.1, hguard.2, InTok.isE, QCarry.isOff]
    rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e j a hnew with
      ⟨hold, _, hphys⟩ | ⟨hpos, _, _, hold, _⟩ | ⟨_, p, _, _, ha, _, _⟩ |
      ⟨_, _, ha, _⟩
    · have hj := H.liveUnique j _ a a hold ha0 rfl hnf
      subst hj
      rcases hphys with heq | ⟨_, _, hoU, _⟩
      · rw [← hsite] at heq
        rw [heq, hxo] at hnewE
        cases t <;> simp at hnewE
      · rw [← hsite, hxo] at hoU
        cases hoU
    · have hj := H.liveUnique _ _ a a hold ha0 rfl hnf
      have hv := congrArg Fin.val hj
      simp only at hv
      omega
    · have hage := hqueue.age _ a ha0
      rw [ha] at hage
      change Z.1.2.clock + 1 ≤ Z.1.2.clock at hage
      omega
    · rw [ha] at hnf; cases hnf
  · have h := H.visitIssued ia j (Or.inl ⟨_, c, hc, hco.trans hoa⟩) j pa hpa hpai
    omega

/-- History clause spentNodup on one actual edge: the newly spent
ticket was live, hence not yet spent. Consumer:
topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketSpentNodupStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    (topFreshTailTicketSpent
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e))).Nodup := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  unfold topFreshTailTicketSpent
  rw [topFreshTailTicketConsumedStep ring C s hn Z hreach e,
    List.filterMap_append, List.nodup_append]
  refine ⟨H.spentNodup, ?_, ?_⟩
  · cases topFreshTailGenealogyPortExport ring C s Z e with
    | none => simp
    | some x =>
        cases (topFreshTailGenealogy ring C s Z).slots
            ⟨topClockSpan n - 1, by omega⟩ with
        | none => simp
        | some c =>
            by_cases hf : topFreshTailTicketIsFresh c.origin = true
            · simp [hf]
            · simp [hf]
  · intro o ho o' ho' heq
    subst heq
    cases hx : topFreshTailGenealogyPortExport ring C s Z e with
    | none => rw [hx] at ho'; simp at ho'
    | some x =>
        rw [hx] at ho'
        cases hc : (topFreshTailGenealogy ring C s Z).slots
            ⟨topClockSpan n - 1, by omega⟩ with
        | none => rw [hc] at ho'; simp at ho'
        | some c =>
            rw [hc] at ho'
            by_cases hf : topFreshTailTicketIsFresh c.origin = true
            · simp [hf] at ho'
            · simp [hf] at ho'
              subst ho'
              exact H.spentNotLive _ c hc ho

/-- History clause visitIssued on one actual edge.
Consumer: topFreshTailTicketHistoryStep. -/
theorem topFreshTailTicketVisitIssuedStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    ∀ i k : Fin (topClockSpan n),
      ((∃ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
          (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
            some a ∧
          a.origin = .oldVisit i k) ∨
        TopFreshTailOrigin.oldVisit i k ∈ topFreshTailTicketSpent
          (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e))) →
      ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
        (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
          some a →
        a.origin = .inherited i → k.val < j.val := by
  intro i k hiss j a hnew horig
  obtain ⟨j0, ha0, hj⟩ := topFreshTailInheritedCarrierMonotoneNoRevisit
    ring C s hn hbad Z hreach e j a i hnew horig
  have hle : j0.val ≤ j.val := by
    rcases hj with h | h
    · rw [h]; exact Nat.le_refl _
    · omega
  rcases hiss with ⟨j2, b, hb, hbo⟩ | hspent
  · have hnfb : topFreshTailTicketIsFresh b.origin = false := by
      rw [hbo]; rfl
    rcases topFreshTailTicketNonfreshSource ring C s hn hbad Z hreach H e j2 b hb hnfb
      with ⟨j3, hb0⟩ | ⟨_, _, ib, pb, _, hob, hpb, hpbi, _⟩
    · have h := H.visitIssued i k (Or.inl ⟨j3, b, hb0, hbo⟩) j0 a ha0 horig
      omega
    · have hvis := hbo.symm.trans hob
      injection hvis with h1 h2
      subst h1
      subst h2
      have hj0 := H.liveUnique j0 k a pb ha0 hpb (horig.trans hpbi.symm)
        (by rw [horig]; rfl)
      subst hj0
      rcases hj with h | h
      · subst h
        have hab : a = b := Option.some.inj (hnew.symm.trans hb)
        rw [hab, hbo] at horig
        cases horig
      · omega
  · rcases topFreshTailTicketSpentStep ring C s hn Z hreach e _ hspent with
      hold | ⟨_, c, hc, hco⟩
    · have h := H.visitIssued i k (Or.inr hold) j0 a ha0 horig
      omega
    · have h := H.visitIssued i k (Or.inl ⟨_, c, hc, hco⟩) j0 a ha0 horig
      omega

/-- J3 history induction step on any actual selected edge.
Consumer: topFreshTailOldVisitIssuedOnceAndNonTail. -/
theorem topFreshTailTicketHistoryStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (H : TopFreshTailTicketHistory ring C s Z)
    (e : Fin n) :
    TopFreshTailTicketHistory ring C s (topFixedTraceNext ring C Z e) :=
  { inheritedAhead :=
      topFreshTailTicketInheritedAheadStep ring C s hn hbad Z hreach H e
    visitShape :=
      topFreshTailTicketVisitShapeStep ring C s hn hbad Z hreach H e
    liveUnique :=
      topFreshTailTicketLiveUniqueStep ring C s hn hbad Z hreach H e
    spentVisitShape :=
      topFreshTailTicketSpentVisitShapeStep ring C s hn Z hreach H e
    spentNotLive :=
      topFreshTailTicketSpentNotLiveStep ring C s hn hbad Z hreach H e
    spentNodup :=
      topFreshTailTicketSpentNodupStep ring C s hn Z hreach H e
    visitIssued :=
      topFreshTailTicketVisitIssuedStep ring C s hn hbad Z hreach H e }

/-- Initial labels are the source's own inherited tickets, except an
initial border U, which is fresh. Consumer: History/Barrier start. -/
theorem topFreshTailTicketInitialSlotOrigin
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n))
    (h : topFreshTailGenealogyInitialSlot C s j = some a) :
    a.origin = .inherited j ∨
    (j.val = 0 ∧ a.origin = .freshBorder 0 ∧ (C (certSite s j.val)).qOut = .U) := by
  unfold topFreshTailGenealogyInitialSlot at h
  cases hq : (C (certSite s j.val)).qOut with
  | E => rw [hq] at h; cases h
  | U =>
      rw [hq] at h
      simp only at h
      by_cases hj : j.val = 0
      · rw [if_pos hj] at h
        cases h
        exact Or.inr ⟨hj, rfl, rfl⟩
      · rw [if_neg hj] at h
        cases h
        exact Or.inl rfl
  | D v t =>
      rw [hq] at h
      cases h
      exact Or.inl rfl

/-- J3 history at the audit start. Consumer:
topFreshTailOldVisitIssuedOnceAndNonTail. -/
theorem topFreshTailTicketHistoryInitial
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailTicketHistory ring C s ((C, digitAuditInitial (piD C)), []) := by
  have hslots : (topFreshTailGenealogy ring C s
      ((C, digitAuditInitial (piD C)), [])).slots =
      topFreshTailGenealogyInitialSlot C s := rfl
  have hspent : topFreshTailTicketSpent (topFreshTailGenealogy ring C s
      ((C, digitAuditInitial (piD C)), [])) = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j a i h horig
    rw [hslots] at h
    rcases topFreshTailTicketInitialSlotOrigin C s j a h with h1 | ⟨_, h1, _⟩
    · rw [h1] at horig; cases horig; exact Nat.le_refl _
    · rw [h1] at horig; cases horig
  · intro j a i k h horig
    rw [hslots] at h
    rcases topFreshTailTicketInitialSlotOrigin C s j a h with h1 | ⟨_, h1, _⟩ <;>
      (rw [h1] at horig; cases horig)
  · intro i j a b ha hb horig hnf
    rw [hslots] at ha hb
    rcases topFreshTailTicketInitialSlotOrigin C s i a ha with h1 | ⟨_, h1, _⟩
    · rcases topFreshTailTicketInitialSlotOrigin C s j b hb with h2 | ⟨_, h2, _⟩
      · rw [h1, h2] at horig; cases horig; rfl
      · rw [h1, h2] at horig; cases horig
    · rw [h1] at hnf; cases hnf
  · intro i k h; rw [hspent] at h; cases h
  · intro j a _ h; rw [hspent] at h; cases h
  · rw [hspent]; exact List.nodup_nil
  · intro i k hiss
    rcases hiss with ⟨j, a, h, horig⟩ | h
    · rw [hslots] at h
      rcases topFreshTailTicketInitialSlotOrigin C s j a h with h1 | ⟨_, h1, _⟩ <;>
        (rw [h1] at horig; cases horig)
    · rw [hspent] at h; cases h

/-- Item 2. On every reached cut of the actual fixed-public
trace the J3 ticket history holds: each oldVisit(i,k) has i <= k,
k >= 1, sits at or right of k, is read at k (an interior site) and is
never a tail, so it can never mint another ticket; every live ticket
is unique; spent tickets are pairwise distinct and never live again;
and once oldVisit(i,k) is issued (live or spent) the original
inherited carrier i stays strictly right of k, so the cell (i,k) is
issued at most once in the whole history.
Consumer: P.3 J3/J4 (topFreshTailPreTailVisitCharge). -/
theorem topFreshTailOldVisitIssuedOnceAndNonTail
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) :
    TopFreshTailTicketHistory ring C s Z := by
  have hfold : ∀ (w : List (Fin n)) (Y : TopFixedTraceState n),
      topClockReached ring C Y → TopFreshTailTicketHistory ring C s Y →
      TopFreshTailTicketHistory ring C s (w.foldl (topFixedTraceNext ring C) Y) := by
    intro w
    induction w with
    | nil => intro Y _ h; exact h
    | cons e rest ih =>
        intro Y hY h
        exact ih (topFixedTraceNext ring C Y e) (topClockReachedNext ring C Y e hY)
          (topFreshTailTicketHistoryStep ring C s hn hbad Y hY h e)
  have h := hfold Z.2 ((C, digitAuditInitial (piD C)), [])
    (by unfold topClockReached; rfl) (topFreshTailTicketHistoryInitial ring C s)
  change TopFreshTailTicketHistory ring C s (topFixedTraceRun ring C Z.2) at h
  rw [← hreach] at h
  exact h

end L3

#print axioms L3.topFreshTailTicketSpentNonfresh
#print axioms L3.topFreshTailTicketRearmOrigin
#print axioms L3.topFreshTailTicketSpentStep
#print axioms L3.topFreshTailInheritedCarrierMonotoneNoRevisit
#print axioms L3.topFreshTailTicketNonfreshSource
#print axioms L3.topFreshTailTicketInheritedAheadStep
#print axioms L3.topFreshTailTicketVisitShapeStep
#print axioms L3.topFreshTailTicketLiveUniqueStep
#print axioms L3.topFreshTailTicketSpentVisitShapeStep
#print axioms L3.topFreshTailTicketSpentNotLiveStep
#print axioms L3.topFreshTailTicketSpentNodupStep
#print axioms L3.topFreshTailTicketVisitIssuedStep
#print axioms L3.topFreshTailTicketHistoryStep
#print axioms L3.topFreshTailTicketInitialSlotOrigin
#print axioms L3.topFreshTailTicketHistoryInitial
#print axioms L3.topFreshTailOldVisitIssuedOnceAndNonTail
