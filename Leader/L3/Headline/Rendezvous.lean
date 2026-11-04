import Leader.L3.Headline.Stages
import Leader.L3.BaseTokenFrame

/-!
Items (1) and (2) of the physical
request/grant rendezvous are discharged at the source level below.
The first unfinished item is (3): a full minimum-attainment and
one-edge minimum-gap/rank drift proof. No assertion of
StageBirthTokenRendezvous is made.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The certificate and H/K owners cannot overwrite the four
token fields written by the full base owner. -/
theorem headlineRendezvousTransitionTokenFrame
    (c : Compiled) (x y : Agent c) :
    (transition c x y).1.req =
        (baseTokenOutputs c (certificateStep c x y).2.2 x y).1.req ∧
    (transition c x y).1.grant =
        (baseTokenOutputs c (certificateStep c x y).2.2 x y).1.grant ∧
    (transition c x y).2.req =
        (baseTokenOutputs c (certificateStep c x y).2.2 x y).2.1.req ∧
    (transition c x y).2.grant =
        (baseTokenOutputs c (certificateStep c x y).2.2 x y).2.1.grant := by
  have h := baseStep_token_fields c
    (certificateStep c x y).2.2 x y
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Substituting the actual no-FIRE guard into the proved
baseStep_token_fields bridge leaves literal, unconsumed OLD tokens.
The DCC and BANK success bits remain unrestricted. -/
theorem headlineRendezvousBaseTokenNoFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hfire : oldFire x y = none) :
    baseTokenOutputs c ev x y =
      tokenStep x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2
        none (dccStep x y ev).request
        (baseBankSuccessBit c x y) := by
  change fireSelect x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2 = none at hfire
  simp [baseTokenOutputs, hfire, fireAtSite]

/-- Exact full selected-pair retention, not just a tokenStep
fact: E has no final leader at a leaderless OLD pair; T0/T1
therefore consume nothing without FIRE; T2 only adds tokens.
The four outputs are the fields of Protocol.transition. -/
theorem headlineRendezvousTransitionNoFireRetains
    (c : Compiled) (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hfire : oldFire x y = none) :
    ((x.req = true ∨ y.req = true) →
      (transition c x y).1.req = true ∨
      (transition c x y).2.req = true) ∧
    ((x.grant = true ∨ y.grant = true) →
      (transition c x y).1.grant = true ∨
      (transition c x y).2.grant = true) := by
  have hpost := headlineRendezvousLeaderlessPostE
    x.certNative y.certNative
    (by simpa only [Agent.certNative] using hx)
    (by simpa only [Agent.certNative] using hy)
  have hrow := headlineRendezvousLocalNoFireRetainsTokens
    x y (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y (certificateStep c x y).2.2).request
    (baseBankSuccessBit c x y)
    hpost.1 hpost.2.1
  have hbase := headlineRendezvousBaseTokenNoFire c
    (certificateStep c x y).2.2 x y hfire
  have hframe := headlineRendezvousTransitionTokenFrame c x y
  constructor
  · intro hold
    have hnow := hrow.1 hold
    rw [← hbase] at hnow
    rcases hnow with hs | ht
    · exact Or.inl (hframe.1.trans hs)
    · exact Or.inr (hframe.2.2.1.trans ht)
  · intro hold
    have hnow := hrow.2 hold
    rw [← hbase] at hnow
    rcases hnow with hs | ht
    · exact Or.inl (hframe.2.1.trans hs)
    · exact Or.inr (hframe.2.2.2.trans ht)

/-- A physical step writes its source from transition's
initiator record, even though HeadlineConfiguration is an
abstract protocol configuration. -/
theorem headlineRendezvousStepAtSource {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e e =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).1 := by
  simp [headlinePhysicalNext, PopulationProtocol.step, protocol]

/-- The responder is distinct when n >= 2. -/
theorem headlineRendezvousStepAtResponder {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2 := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  simp [headlinePhysicalNext, PopulationProtocol.step, protocol, hne]

/-- No other site is touched by the real physical service. -/
theorem headlineRendezvousStepAway {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    headlinePhysicalNext ring C e i = C i := by
  simp [headlinePhysicalNext, PopulationProtocol.step, he, hj]

/-- The existence of an OLD request survives an actual no-FIRE
service from a leaderless cut, including OLD requests outside
the selected pair. -/
theorem headlineRendezvousNoFireRequestSurvives {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hnoLeader : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hreq : ∃ i : Fin n, (C i).req = true) :
    ∃ i : Fin n, ((headlinePhysicalNext ring C e) i).req = true := by
  have hpair := (headlineRendezvousTransitionNoFireRetains
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hnoLeader e) (hnoLeader (ring.rightNeighbor e)) hfire).1
  obtain ⟨i, hi⟩ := hreq
  by_cases hp : i = e ∨ i = ring.rightNeighbor e
  · have hold : (C e).req = true ∨
        (C (ring.rightNeighbor e)).req = true := by
      rcases hp with he | hj
      · exact Or.inl (by simpa [he] using hi)
      · exact Or.inr (by simpa [hj] using hi)
    rcases hpair hold with hs | ht
    · refine ⟨e, ?_⟩
      rw [headlineRendezvousStepAtSource ring C e]
      exact hs
    · refine ⟨ring.rightNeighbor e, ?_⟩
      rw [headlineRendezvousStepAtResponder ring hn C e]
      exact ht
  · have he : i ≠ e := by
      intro h
      exact hp (Or.inl h)
    have hj : i ≠ ring.rightNeighbor e := by
      intro h
      exact hp (Or.inr h)
    refine ⟨i, ?_⟩
    rw [headlineRendezvousStepAway ring C e i he hj]
    exact hi

/-- The same OLD-to-real comparison for grants. The BANK/SMALL
producer is not assumed to succeed; the OLD grant alone survives. -/
theorem headlineRendezvousNoFireGrantSurvives {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hnoLeader : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hgrant : ∃ i : Fin n, (C i).grant = true) :
    ∃ i : Fin n, ((headlinePhysicalNext ring C e) i).grant = true := by
  have hpair := (headlineRendezvousTransitionNoFireRetains
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hnoLeader e) (hnoLeader (ring.rightNeighbor e)) hfire).2
  obtain ⟨i, hi⟩ := hgrant
  by_cases hp : i = e ∨ i = ring.rightNeighbor e
  · have hold : (C e).grant = true ∨
        (C (ring.rightNeighbor e)).grant = true := by
      rcases hp with he | hj
      · exact Or.inl (by simpa [he] using hi)
      · exact Or.inr (by simpa [hj] using hi)
    rcases hpair hold with hs | ht
    · refine ⟨e, ?_⟩
      rw [headlineRendezvousStepAtSource ring C e]
      exact hs
    · refine ⟨ring.rightNeighbor e, ?_⟩
      rw [headlineRendezvousStepAtResponder ring hn C e]
      exact ht
  · have he : i ≠ e := by
      intro h
      exact hp (Or.inl h)
    have hj : i ≠ ring.rightNeighbor e := by
      intro h
      exact hp (Or.inr h)
    refine ⟨i, ?_⟩
    rw [headlineRendezvousStepAway ring C e i he hj]
    exact hi

/-- A nonempty literal FIRE selects one and only one of the
two sites. This proof uses the three actual FireSel cases. -/
theorem headlineRendezvousFireHasSite (fire : Option FireSel)
    (h : fire ≠ none) :
    fireAtSite fire .siteX = true ∨
    fireAtSite fire .siteY = true := by
  cases fire with
  | none =>
      exact False.elim (h rfl)
  | some f =>
      cases hs : f.site with
      | siteX => exact Or.inl (by simp [fireAtSite, hs])
      | siteY => exact Or.inr (by simp [fireAtSite, hs])

/-- A structure field commutes with an arbitrary conditional. -/
private theorem headlineRendezvousIteLeader {c : Compiled}
    (p : Prop) [Decidable p] (a b : Agent c) :
    (if p then a else b).l =
      if p then a.l else b.l := by
  split <;> rfl

/-- Any selected source FIRE writes firedNative, whose leader
bit is true, irrespective of certificate and BANK scratch. -/
theorem headlineRendezvousBaseFireSource
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (h : fireAtSite (oldFire x y) .siteX = true) :
    (baseStep c ev x y).1.l = true := by
  change fireAtSite
    (fireSelect x y (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2)
    .siteX = true at h
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, h, Agent.setNative, Agent.setCPriv,
      headlineRendezvousIteLeader, firedNative]

/-- The analogous selected responder FIRE. -/
theorem headlineRendezvousBaseFireResponder
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (h : fireAtSite (oldFire x y) .siteY = true) :
    (baseStep c ev x y).2.l = true := by
  change fireAtSite
    (fireSelect x y (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2)
    .siteY = true at h
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, h, Agent.setNative, Agent.setCPriv,
      headlineRendezvousIteLeader, firedNative]

/-- The certificate/HK assembly also frames the native leader bit.
This is deliberately a field theorem, not a rewrite of the
configuration type. -/
theorem headlineRendezvousTransitionLeaderFrame
    (c : Compiled) (x y : Agent c) :
    (transition c x y).1.l =
      (baseStep c (certificateStep c x y).2.2 x y).1.l ∧
    (transition c x y).2.l =
      (baseStep c (certificateStep c x y).2.2 x y).2.l := by
  exact ⟨rfl, rfl⟩

/-- Item (2). Every actual F0/F1/F2 event from a native-peaceful
cut produces a protected physical leader. In fact OLD
leaderlessness is unnecessary for this implication:
real_step_preserves_P handles the native safety factor, while
the selected site is literally overwritten by firedNative. -/
theorem headlineRendezvousFireRooted {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hpurified : headlinePurified ring C)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) ≠ none) :
    headlineRooted ring (headlinePhysicalNext ring C e) := by
  have hP : P ring
      (nativeProjection (headlinePhysicalNext ring C e)) :=
    real_step_preserves_P (by omega : 3 ≤ n)
      ring C e hpurified.1
  have hsites := headlineRendezvousFireHasSite
    (oldFire (C e) (C (ring.rightNeighbor e))) hfire
  have hframe := headlineRendezvousTransitionLeaderFrame
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
  have hleader : ∃ i : Fin n,
      ((headlinePhysicalNext ring C e) i).l = true := by
    rcases hsites with hs | ht
    · refine ⟨e, ?_⟩
      rw [headlineRendezvousStepAtSource ring C e]
      exact hframe.1.trans
        (headlineRendezvousBaseFireSource
          (compileAdvice (ceilLogTwo n))
          (certificateStep (compileAdvice (ceilLogTwo n))
            (C e) (C (ring.rightNeighbor e))).2.2
          (C e) (C (ring.rightNeighbor e)) hs)
    · refine ⟨ring.rightNeighbor e, ?_⟩
      rw [headlineRendezvousStepAtResponder ring (by omega : 2 ≤ n) C e]
      exact hframe.2.trans
        (headlineRendezvousBaseFireResponder
          (compileAdvice (ceilLogTwo n))
          (certificateStep (compileAdvice (ceilLogTwo n))
            (C e) (C (ring.rightNeighbor e))).2.2
          (C e) (C (ring.rightNeighbor e)) ht)
  have hpurifiedNext :=
    headlineStagesPurifiedOfPeaceful ring
      (headlinePhysicalNext ring C e) hP
  exact ⟨hpurifiedNext.2 hleader, hleader⟩

/-- Item (1). This is the all-Cartesian one-physical-edge
survival-or-rooted alternative. It includes remote tokens,
the actual E/BANK/DCC/FIRE owners, and every possible certificate
and private scratch value. -/
theorem headlineRendezvousRealEdgeSurvival {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hpurified : headlinePurified ring C)
    (hnoLeader : ∀ i : Fin n, (C i).l = false)
    (hreq : ∃ i : Fin n, (C i).req = true)
    (hgrant : ∃ i : Fin n, (C i).grant = true) :
    headlineRooted ring (headlinePhysicalNext ring C e) ∨
      ((∃ i : Fin n,
          ((headlinePhysicalNext ring C e) i).req = true) ∧
       (∃ i : Fin n,
          ((headlinePhysicalNext ring C e) i).grant = true)) := by
  by_cases hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none
  · exact Or.inr
      ⟨headlineRendezvousNoFireRequestSurvives ring
        (by omega : 2 ≤ n) C e hnoLeader hfire hreq,
       headlineRendezvousNoFireGrantSurvives ring
        (by omega : 2 ≤ n) C e hnoLeader hfire hgrant⟩
  · exact Or.inl
      (headlineRendezvousFireRooted ring hn C e hpurified hfire)

/-! Item (3), proved purely as far as the foldl upper bounds. -/

/-- A fold of pointwise decreasing Nat updates is below its
initial accumulator. -/
private theorem headlineRendezvousFoldDecreases {α : Type}
    (step : Nat → α → Nat)
    (hred : ∀ a x, step a x ≤ a) :
    ∀ (xs : List α) (start : Nat),
      xs.foldl step start ≤ start := by
  intro xs
  induction xs with
  | nil =>
      intro start
      exact Nat.le_refl _
  | cons x tail ih =>
      intro start
      exact Nat.le_trans (ih (step start x)) (hred start x)

/-- A witnessed element forces an upper bound on a decreasing
fold, independently of where the element occurs in the list. -/
private theorem headlineRendezvousFoldMemberBound {α : Type}
    (step : Nat → α → Nat)
    (hred : ∀ a x, step a x ≤ a)
    (bound : Nat) :
    ∀ (xs : List α) (start : Nat) (x : α),
      x ∈ xs → (∀ a, step a x ≤ bound) →
      xs.foldl step start ≤ bound := by
  intro xs
  induction xs with
  | nil =>
      intro start x hx _
      cases hx
  | cons y tail ih =>
      intro start x hx hbound
      rcases List.mem_cons.mp hx with heq | htail
      · cases heq
        exact Nat.le_trans
          (headlineRendezvousFoldDecreases step hred
            tail (step start y))
          (hbound start)
      · exact ih (step start y) x htail hbound

private theorem headlineRendezvousCellDecreases {n : Nat}
    (C : HeadlineConfiguration n)
    (r g : Fin n) (a : Nat) :
    (if (C r).req = true ∧ (C g).grant = true then
      min a ((g.val + n - r.val) % n) else a) ≤ a := by
  split
  · exact Nat.min_le_left _ _
  · exact Nat.le_refl _

private theorem headlineRendezvousRowDecreases {n : Nat}
    (C : HeadlineConfiguration n) (r : Fin n) (a : Nat) :
    (List.finRange n).foldl
      (fun acc g =>
        if (C r).req = true ∧ (C g).grant = true then
          min acc ((g.val + n - r.val) % n) else acc) a ≤ a := by
  exact headlineRendezvousFoldDecreases
    (fun acc g =>
      if (C r).req = true ∧ (C g).grant = true then
        min acc ((g.val + n - r.val) % n) else acc)
    (fun acc g => headlineRendezvousCellDecreases C r g acc)
    (List.finRange n) a

/-- First requested characterization: the actual nested List.foldl
minimum is <= the gap of EVERY simultaneously witnessed OLD pair.
This is not an unverified alternative min definition. -/
theorem headlineRendezvousMinGapLePair {n : Nat}
    (C : HeadlineConfiguration n) (r g : Fin n)
    (hreq : (C r).req = true)
    (hgrant : (C g).grant = true) :
    headlineRendezvousMinGap C ≤ (g.val + n - r.val) % n := by
  unfold headlineRendezvousMinGap
  apply headlineRendezvousFoldMemberBound
    (fun acc r' =>
      (List.finRange n).foldl (fun acc' g' =>
        if (C r').req = true ∧ (C g').grant = true then
          min acc' ((g'.val + n - r'.val) % n) else acc') acc)
    (fun acc r' => headlineRendezvousRowDecreases C r' acc)
    ((g.val + n - r.val) % n)
    (List.finRange n) n r (List.mem_finRange r)
  intro acc
  apply headlineRendezvousFoldMemberBound
    (fun acc' g' =>
      if (C r).req = true ∧ (C g').grant = true then
        min acc' ((g'.val + n - r.val) % n) else acc')
    (fun acc' g' => headlineRendezvousCellDecreases C r g' acc')
    ((g.val + n - r.val) % n)
    (List.finRange n) acc g (List.mem_finRange g)
  intro acc'
  split
  · exact Nat.min_le_right _ _
  · rename_i hne
    exact absurd (And.intro hreq hgrant) hne

/-- The outer fold starts from n and never grows. -/
theorem headlineRendezvousMinGapLeSize {n : Nat}
    (C : HeadlineConfiguration n) :
    headlineRendezvousMinGap C ≤ n := by
  unfold headlineRendezvousMinGap
  exact headlineRendezvousFoldDecreases
    (fun acc r =>
      (List.finRange n).foldl (fun acc' g =>
        if (C r).req = true ∧ (C g).grant = true then
          min acc' ((g.val + n - r.val) % n) else acc') acc)
    (fun acc r => headlineRendezvousRowDecreases C r acc)
    (List.finRange n) n

/-- Both OLD token kinds exclude the n-sentinel. The converse,
an attained (request,grant) pair, still requires the inner/outer
fold result-witness induction. -/
theorem headlineRendezvousMinGapBelowSize {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hreq : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    headlineRendezvousMinGap C < n := by
  obtain ⟨r, hr⟩ := hreq
  obtain ⟨g, hg⟩ := hgrant
  have hbound := headlineRendezvousMinGapLePair C r g hr hg
  exact Nat.lt_of_le_of_lt hbound
    (Nat.mod_lt _ ring.hn)

/-!
First unfinished item: (3).
To finish it, first prove attainment of headlineRendezvousMinGap by
an actual (request,grant) pair when the value is below n.
Then prove the full real-step position-sensitive token rows, not only
the existential survival rows:
  * source request advances clockwise unless paired with a source
    grant (which would select F0 on its own outgoing edge);
  * responder request remains at the responder;
  * source grant remains at the source;
  * responder grant moves counterclockwise, except a co-located
    nonfiring request/grant pair is retained by HOLD.
Use the circular Nat modulo gap calculation to show every no-FIRE
edge weakly decreases the observed minimum, and the outgoing edge
of a minimum-gap request strictly decreases headlineRendezvousRank
unless it fires. The missing result is NOT an axiom or a theorem
assumed in this module.

Item (4) is intentionally omitted. Its use of
Prob.costNumerator_le_of_nominated_edge requires a stopped target
that includes loss of the purified/two-token domain, followed by
an exact cost comparison showing that this exit is impossible
before a rooted FIRE. One cannot apply the global drift theorem
to headlineRooted alone, because arbitrary rootless configurations
with no OLD request or no OLD grant admit no nominated drop.
-/

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Fold attainment for the physical rendezvous rank, followed
by exact directed no-FIRE token rows for the as-yet-open drift step.

No global rank
drift or stage theorem is asserted in the absence of a complete
position-and-modulo proof.
-/

/-- A finite fold whose one-item update either keeps the accumulator
or selects a genuine candidate must finish either at its starting
value or at the score of a genuine candidate. -/
private theorem headlineRendezvousFoldOrigin
    {α β : Type}
    (step : Nat → α → Nat)
    (good : β → Prop) (measure : β → Nat)
    (hsingle : ∀ (a : Nat) (x : α),
      step a x = a ∨
        ∃ w : β, good w ∧ step a x = measure w)
    (xs : List α) (a : Nat) :
    xs.foldl step a = a ∨
      ∃ w : β, good w ∧ xs.foldl step a = measure w := by
  induction xs generalizing a with
  | nil =>
      exact Or.inl rfl
  | cons x xs ih =>
      rcases ih (step a x) with htail | ⟨w, hw, htail⟩
      · rcases hsingle a x with hkeep | ⟨w, hw, hvalue⟩
        · left
          calc
            (x :: xs).foldl step a =
                xs.foldl step (step a x) := rfl
            _ = step a x := htail
            _ = a := hkeep
        · right
          refine ⟨w, hw, ?_⟩
          calc
            (x :: xs).foldl step a =
                xs.foldl step (step a x) := rfl
            _ = step a x := htail
            _ = measure w := hvalue
      · right
        refine ⟨w, hw, ?_⟩
        change xs.foldl step (step a x) = measure w
        exact htail

/-- One inner minimum row either leaves its incoming bound unchanged
or selects an OLD grant paired with the fixed OLD request. -/
private theorem headlineRendezvousRowOrigin {n : Nat}
    (C : HeadlineConfiguration n) (r : Fin n) (a : Nat) :
    (List.finRange n).foldl
      (fun acc g =>
        if (C r).req = true ∧ (C g).grant = true then
          min acc ((g.val + n - r.val) % n) else acc) a = a ∨
    ∃ g : Fin n,
      ((C r).req = true ∧ (C g).grant = true) ∧
      (List.finRange n).foldl
        (fun acc g' =>
          if (C r).req = true ∧ (C g').grant = true then
            min acc ((g'.val + n - r.val) % n) else acc) a =
        (g.val + n - r.val) % n := by
  have hsingle : ∀ (acc : Nat) (g : Fin n),
      (if (C r).req = true ∧ (C g).grant = true then
        min acc ((g.val + n - r.val) % n) else acc) = acc ∨
      ∃ w : Fin n,
        ((C r).req = true ∧ (C w).grant = true) ∧
        (if (C r).req = true ∧ (C g).grant = true then
          min acc ((g.val + n - r.val) % n) else acc) =
          (w.val + n - r.val) % n := by
    intro acc g
    by_cases hgood : (C r).req = true ∧ (C g).grant = true
    · by_cases hleft : acc ≤ (g.val + n - r.val) % n
      · exact Or.inl
          (by simp only [if_pos hgood, Nat.min_eq_left hleft])
      · have hright : (g.val + n - r.val) % n ≤ acc := by
          omega
        exact Or.inr
          ⟨g, hgood, by simp only [if_pos hgood, Nat.min_eq_right hright]⟩
    · exact Or.inl (by simp only [if_neg hgood])
  exact headlineRendezvousFoldOrigin
    (fun acc g =>
      if (C r).req = true ∧ (C g).grant = true then
        min acc ((g.val + n - r.val) % n) else acc)
    (fun g => (C r).req = true ∧ (C g).grant = true)
    (fun g => (g.val + n - r.val) % n)
    hsingle (List.finRange n) a

/-- The actual two-level List.finRange fold has an exact origin:
the initial sentinel n, or a real OLD request/OLD grant pair. -/
theorem headlineRendezvousMinGapOrigin {n : Nat}
    (C : HeadlineConfiguration n) :
    headlineRendezvousMinGap C = n ∨
      ∃ r g : Fin n,
        (C r).req = true ∧
        (C g).grant = true ∧
        headlineRendezvousMinGap C =
          (g.val + n - r.val) % n := by
  unfold headlineRendezvousMinGap
  have hsingle : ∀ (a : Nat) (r : Fin n),
      (List.finRange n).foldl
        (fun acc g =>
          if (C r).req = true ∧ (C g).grant = true then
            min acc ((g.val + n - r.val) % n) else acc) a = a ∨
      ∃ p : Fin n × Fin n,
        ((C p.1).req = true ∧ (C p.2).grant = true) ∧
        (List.finRange n).foldl
          (fun acc g =>
            if (C r).req = true ∧ (C g).grant = true then
              min acc ((g.val + n - r.val) % n) else acc) a =
          (p.2.val + n - p.1.val) % n := by
    intro a r
    rcases headlineRendezvousRowOrigin C r a with
      hkeep | ⟨g, hgood, hvalue⟩
    · exact Or.inl hkeep
    · exact Or.inr ⟨(r, g), hgood, hvalue⟩
  have houter := headlineRendezvousFoldOrigin
    (fun acc r =>
      (List.finRange n).foldl
        (fun acc' g =>
          if (C r).req = true ∧ (C g).grant = true then
            min acc' ((g.val + n - r.val) % n) else acc') acc)
    (fun p : Fin n × Fin n =>
      (C p.1).req = true ∧ (C p.2).grant = true)
    (fun p : Fin n × Fin n =>
      (p.2.val + n - p.1.val) % n)
    hsingle (List.finRange n) n
  rcases houter with hkeep | ⟨p, hgood, hvalue⟩
  · exact Or.inl hkeep
  · rcases p with ⟨r, g⟩
    exact Or.inr ⟨r, g, hgood.1, hgood.2, hvalue⟩

/-- Item (3a): both OLD token kinds force the nested
minimum to be attained by an actual ordered pair. -/
theorem headlineRendezvousMinGapAttained {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hreq : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    ∃ r g : Fin n,
      (C r).req = true ∧
      (C g).grant = true ∧
      headlineRendezvousMinGap C =
        (g.val + n - r.val) % n := by
  have hsmall :=
    headlineRendezvousMinGapBelowSize ring C hreq hgrant
  rcases headlineRendezvousMinGapOrigin C with
    hsentinel | ⟨r, g, hr, hg, hvalue⟩
  · omega
  · exact ⟨r, g, hr, hg, hvalue⟩

/-! Directed no-FIRE rows: these isolate the actual surviving
positions, rather than only existence of each OLD token kind.
Every BOOL producer and every other OLD token flag is arbitrary. -/

/-- T1 has no sink; T0 has no consumption. The source's unpaired
request moves to the responder, and the responder's unpaired grant
moves to the source. An OLD responder request and an OLD source
grant persist at their respective sites. HOLD retains a coincident
OLD responder pair. -/
theorem headlineRendezvousLocalDirectedNoFire
    {c : Compiled}
    (x y : Agent c) (finalX finalY : CertNative)
    (dccRequest bankSuccessX : Bool)
    (hX : finalX.l = false) (hY : finalY.l = false) :
    ((x.req = true ∧ x.grant = false) →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).2.1.req = true) ∧
    ((y.grant = true ∧ y.req = false) →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).1.grant = true) ∧
    (y.req = true →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).2.1.req = true) ∧
    (x.grant = true →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).1.grant = true) ∧
    ((y.req = true ∧ y.grant = true) →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).2.1.grant = true) := by
  cases hreqX : x.req <;>
    cases hgrantX : x.grant <;>
    cases hreqY : y.req <;>
    cases hgrantY : y.grant <;>
    cases dccRequest <;>
    cases bankSuccessX <;>
    simp [tokenStep, fireAtSite, hX, hY, hreqX, hgrantX,
      hreqY, hgrantY] <;>
    (repeat' split) <;> simp

/-- The position-sensitive no-FIRE rows through the base
token frame and the actual certificate/HK assembler. -/
theorem headlineRendezvousTransitionDirectedNoFire
    (c : Compiled) (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hfire : oldFire x y = none) :
    ((x.req = true ∧ x.grant = false) →
      (transition c x y).2.req = true) ∧
    ((y.grant = true ∧ y.req = false) →
      (transition c x y).1.grant = true) ∧
    (y.req = true →
      (transition c x y).2.req = true) ∧
    (x.grant = true →
      (transition c x y).1.grant = true) ∧
    ((y.req = true ∧ y.grant = true) →
      (transition c x y).2.grant = true) := by
  have hpost := headlineRendezvousLeaderlessPostE
    x.certNative y.certNative
    (by simpa only [Agent.certNative] using hx)
    (by simpa only [Agent.certNative] using hy)
  have hrow := headlineRendezvousLocalDirectedNoFire
    x y (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y (certificateStep c x y).2.2).request
    (baseBankSuccessBit c x y) hpost.1 hpost.2.1
  have hbase := headlineRendezvousBaseTokenNoFire c
    (certificateStep c x y).2.2 x y hfire
  rw [← hbase] at hrow
  have hframe := headlineRendezvousTransitionTokenFrame c x y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    exact hframe.2.2.1.trans (hrow.1 hh)
  · intro hh
    exact hframe.2.1.trans (hrow.2.1 hh)
  · intro hh
    exact hframe.2.2.1.trans (hrow.2.2.1 hh)
  · intro hh
    exact hframe.2.1.trans (hrow.2.2.2.1 hh)
  · intro hh
    exact hframe.2.2.2.trans (hrow.2.2.2.2 hh)

/-- No-FIRE at a leaderless source containing an OLD request
rules out an OLD source grant, by the F0 theorem. -/
theorem headlineRendezvousNoFireSourceGrantFalse
    {c : Compiled} (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hfire : oldFire x y = none)
    (hrequest : x.req = true) :
    x.grant = false := by
  cases hgrant : x.grant with
  | false =>
      rfl
  | true =>
      have hf := headlineRendezvousCoincidentFires
        x y hx hy hrequest hgrant
      exact False.elim (hf hfire)

/-- No-FIRE at a leaderless source containing an OLD request
rules out an OLD responder grant, by the F2 theorem. -/
theorem headlineRendezvousNoFireCrossGrantFalse
    {c : Compiled} (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hfire : oldFire x y = none)
    (hrequest : x.req = true) :
    y.grant = false := by
  cases hgrant : y.grant with
  | false =>
      rfl
  | true =>
      have hf := headlineRendezvousCrossFires
        x y hx hy hrequest hgrant
      exact False.elim (hf hfire)

/-- Exact real-edge advance: an OLD source request necessarily
appears at the clockwise responder on a no-FIRE service from a
leaderless cut. We rewrite only the transition hypothesis,
not the headlinePhysicalNext goal. -/
theorem headlineRendezvousNoFireOutgoingRequestMoves {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hrequest : (C e).req = true) :
    ((headlinePhysicalNext ring C e)
      (ring.rightNeighbor e)).req = true := by
  have hnoGrant := headlineRendezvousNoFireSourceGrantFalse
    (C e) (C (ring.rightNeighbor e))
    (hrootless e) (hrootless (ring.rightNeighbor e))
    hfire hrequest
  have hmove :=
    (headlineRendezvousTransitionDirectedNoFire
      (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e))
      (hrootless e) (hrootless (ring.rightNeighbor e))
      hfire).1 ⟨hrequest, hnoGrant⟩
  have hframe := headlineRendezvousStepAtResponder ring hn C e
  rw [← hframe] at hmove
  exact hmove

/-!
FIRST UNFINISHED ITEM: (3b).

The fold-origin/attaining-pair proof is above, and the full-real-step
source-request advance and five literal token rows are available.
The missing result is an EVERY-edge inequality for
headlineRendezvousMinGap under non-FIRE services. Its Lean proof
must track an attaining pair through the selected edge, distinguish
the coincident responder HOLD case, and prove the relevant directed
cyclic-distance inequalities involving Nat.mod and
ring.rightNeighbor. No old request/grant is deleted by a rootless
no-FIRE service, and the rows do not exhibit a contrary example.

Item (3c), strict nominated-edge rank drift, and item (4), the
stopped-domain expected hitting time and StageBirthTokenRendezvous,
are not asserted. In particular the global cost-numerator theorem
cannot be invoked on arbitrary rootless states missing a token.
-/

end L3


namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
An all-edge directed minimum-gap drift, the nominated
request edge, and a stopped-domain expected-time argument.
-/

/-- Clockwise distance when the request coordinate is not after
the grant coordinate. The Nat subtraction does not underflow. -/
private theorem headlineRendezvousGapForward {n : Nat}
    (r g : Fin n) (h : r.val ≤ g.val) :
    (g.val + n - r.val) % n = g.val - r.val := by
  have he : g.val + n - r.val = n + (g.val - r.val) := by
    omega
  rw [he, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by have hg := g.isLt; omega)]

/-- Clockwise distance in the wrapping request-after-grant case.
The representative already lies strictly below n. -/
private theorem headlineRendezvousGapWrapped {n : Nat}
    (r g : Fin n) (h : g.val < r.val) :
    (g.val + n - r.val) % n = g.val + n - r.val := by
  apply Nat.mod_eq_of_lt
  have hr := r.isLt
  have hg := g.isLt
  omega

/-- The directed distance of a co-located OLD pair is zero. -/
theorem headlineRendezvousGapCoincident {n : Nat} (i : Fin n) :
    (i.val + n - i.val) % n = 0 := by
  have he : i.val + n - i.val = n := by omega
  rw [he, Nat.mod_self]

/-- Advancing an OLD request at e to its clockwise neighbor
strictly reduces its distance to a different fixed grant.
The two branches handle the wrap e = n-1 and no wrap; the
non-wrapping branch splits g after/before e. -/
theorem headlineRendezvousGapRequestAdvance {n : Nat}
    (ring : DirectedRing n) (e g : Fin n) (hneq : e ≠ g) :
    (g.val + n - (ring.rightNeighbor e).val) % n + 1 =
      (g.val + n - e.val) % n := by
  have hneqval : e.val ≠ g.val := by
    intro h
    exact hneq (Fin.ext h)
  by_cases hwrap : e.val + 1 < n
  · have hj : (ring.rightNeighbor e).val = e.val + 1 := by
      change (e.val + 1) % n = e.val + 1
      exact Nat.mod_eq_of_lt hwrap
    by_cases hlt : e.val < g.val
    · have hbefore : e.val ≤ g.val := by omega
      have hafter : (ring.rightNeighbor e).val ≤ g.val := by
        omega
      rw [headlineRendezvousGapForward (ring.rightNeighbor e) g hafter,
        headlineRendezvousGapForward e g hbefore]
      omega
    · have hbefore : g.val < e.val := by omega
      have hafter : g.val < (ring.rightNeighbor e).val := by
        omega
      rw [headlineRendezvousGapWrapped (ring.rightNeighbor e) g hafter,
        headlineRendezvousGapWrapped e g hbefore]
      omega
  · have he : e.val + 1 = n := by
      have hl := e.isLt
      omega
    have hj : (ring.rightNeighbor e).val = 0 := by
      change (e.val + 1) % n = 0
      rw [he, Nat.mod_self]
    have hbefore : g.val < e.val := by
      have hg := g.isLt
      omega
    have hafter : (ring.rightNeighbor e).val ≤ g.val := by
      omega
    rw [headlineRendezvousGapForward (ring.rightNeighbor e) g hafter,
      headlineRendezvousGapWrapped e g hbefore]
    omega

/-- Moving an OLD responder grant one site counterclockwise
strictly reduces distance from any different fixed request.
The excluded r=j case is precisely the responder HOLD branch. -/
theorem headlineRendezvousGapGrantRetreat {n : Nat}
    (ring : DirectedRing n) (e r : Fin n)
    (hneq : r ≠ ring.rightNeighbor e) :
    (e.val + n - r.val) % n + 1 =
      ((ring.rightNeighbor e).val + n - r.val) % n := by
  have hneqval : r.val ≠ (ring.rightNeighbor e).val := by
    intro h
    exact hneq (Fin.ext h)
  by_cases hwrap : e.val + 1 < n
  · have hj : (ring.rightNeighbor e).val = e.val + 1 := by
      change (e.val + 1) % n = e.val + 1
      exact Nat.mod_eq_of_lt hwrap
    by_cases hle : r.val ≤ e.val
    · have hafter : r.val ≤ (ring.rightNeighbor e).val := by
        omega
      rw [headlineRendezvousGapForward r e hle,
        headlineRendezvousGapForward r (ring.rightNeighbor e) hafter]
      omega
    · have hbefore : e.val < r.val := by omega
      have hafter : (ring.rightNeighbor e).val < r.val := by
        omega
      rw [headlineRendezvousGapWrapped r e hbefore,
        headlineRendezvousGapWrapped r (ring.rightNeighbor e) hafter]
      omega
  · have he : e.val + 1 = n := by
      have hl := e.isLt
      omega
    have hj : (ring.rightNeighbor e).val = 0 := by
      change (e.val + 1) % n = 0
      rw [he, Nat.mod_self]
    have hbefore : r.val ≤ e.val := by
      have hr := r.isLt
      omega
    have hafter : (ring.rightNeighbor e).val < r.val := by
      omega
    rw [headlineRendezvousGapForward r e hbefore,
      headlineRendezvousGapWrapped r (ring.rightNeighbor e) hafter]
    omega

/-- An OLD request outside the source survives in place:
the responder keeps its OLD request, and the off-edge
sites are not written by PopulationProtocol.step. -/
theorem headlineRendezvousNoFireRequestStays {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e r : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hne : r ≠ e) (hreq : (C r).req = true) :
    ((headlinePhysicalNext ring C e) r).req = true := by
  by_cases hj : r = ring.rightNeighbor e
  · have hrow :=
      (headlineRendezvousTransitionDirectedNoFire
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))
        (hrootless e) (hrootless (ring.rightNeighbor e))
        hfire).2.2.1 (by simpa only [hj] using hreq)
    have hframe := headlineRendezvousStepAtResponder ring hn C e
    rw [← hframe] at hrow
    simpa only [hj] using hrow
  · have hframe := headlineRendezvousStepAway ring C e r hne hj
    have heq :
        ((headlinePhysicalNext ring C e) r).req = (C r).req :=
      congrArg (fun a => a.req) hframe
    exact heq.trans hreq

/-- An OLD grant outside the responder survives in place:
the source keeps its OLD grant, and off-edge grants are framed. -/
theorem headlineRendezvousNoFireGrantStays {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e g : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hne : g ≠ ring.rightNeighbor e)
    (hgrant : (C g).grant = true) :
    ((headlinePhysicalNext ring C e) g).grant = true := by
  by_cases he : g = e
  · have hrow :=
      (headlineRendezvousTransitionDirectedNoFire
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))
        (hrootless e) (hrootless (ring.rightNeighbor e))
        hfire).2.2.2.1 (by simpa only [he] using hgrant)
    have hframe := headlineRendezvousStepAtSource ring C e
    rw [← hframe] at hrow
    simpa only [he] using hrow
  · have hframe := headlineRendezvousStepAway ring C e g he hne
    have heq :
        ((headlinePhysicalNext ring C e) g).grant = (C g).grant :=
      congrArg (fun a => a.grant) hframe
    exact heq.trans hgrant

/-- Without a responder request, an OLD responder grant moves
counterclockwise to the source under a no-FIRE service. -/
theorem headlineRendezvousNoFireGrantMoves {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hgrant : (C (ring.rightNeighbor e)).grant = true)
    (hreqFalse : (C (ring.rightNeighbor e)).req = false) :
    ((headlinePhysicalNext ring C e) e).grant = true := by
  have hrow :=
    (headlineRendezvousTransitionDirectedNoFire
      (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e))
      (hrootless e) (hrootless (ring.rightNeighbor e))
      hfire).2.1 ⟨hgrant, hreqFalse⟩
  have hframe := headlineRendezvousStepAtSource ring C e
  rw [← hframe] at hrow
  exact hrow

/-- The responder HOLD case retains both OLD token kinds
at their common site, so the surviving minimum is zero. -/
theorem headlineRendezvousNoFireResponderHolds {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hreq : (C (ring.rightNeighbor e)).req = true)
    (hgrant : (C (ring.rightNeighbor e)).grant = true) :
    ((headlinePhysicalNext ring C e)
      (ring.rightNeighbor e)).req = true ∧
    ((headlinePhysicalNext ring C e)
      (ring.rightNeighbor e)).grant = true := by
  have hrow := headlineRendezvousTransitionDirectedNoFire
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hrootless e) (hrootless (ring.rightNeighbor e))
    hfire
  have hr := hrow.2.2.1 hreq
  have hg := hrow.2.2.2.2 ⟨hreq, hgrant⟩
  have hframe := headlineRendezvousStepAtResponder ring hn C e
  rw [← hframe] at hr hg
  exact ⟨hr, hg⟩

/-- The complete attaining-pair descendant row on one no-FIRE
real edge. Three geometries suffice: request at the source;
otherwise grant at the responder, with HOLD or retreat; or
neither tracked token moves. Extra tokens and production can
only improve the new minimum. -/
theorem headlineRendezvousNoFirePairDescendant {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e r g : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hreq : (C r).req = true)
    (hgrant : (C g).grant = true) :
    ∃ r' g' : Fin n,
      ((headlinePhysicalNext ring C e) r').req = true ∧
      ((headlinePhysicalNext ring C e) g').grant = true ∧
      (g'.val + n - r'.val) % n ≤
        (g.val + n - r.val) % n := by
  by_cases hre : r = e
  · have hreqE : (C e).req = true := by
      simpa only [hre] using hreq
    have hgrantEFalse := headlineRendezvousNoFireSourceGrantFalse
      (C e) (C (ring.rightNeighbor e))
      (hrootless e) (hrootless (ring.rightNeighbor e))
      hfire hreqE
    have hgrantYFalse := headlineRendezvousNoFireCrossGrantFalse
      (C e) (C (ring.rightNeighbor e))
      (hrootless e) (hrootless (ring.rightNeighbor e))
      hfire hreqE
    have hneE : e ≠ g := by
      intro hh
      have hv : (C e).grant = true := by rw [hh]; exact hgrant
      rw [hgrantEFalse] at hv
      cases hv
    have hneY : g ≠ ring.rightNeighbor e := by
      intro hh
      have hv : (C (ring.rightNeighbor e)).grant = true := by
        rw [← hh]
        exact hgrant
      rw [hgrantYFalse] at hv
      cases hv
    have hreqNext := headlineRendezvousNoFireOutgoingRequestMoves
      ring hn C e hrootless hfire hreqE
    have hgrantNext := headlineRendezvousNoFireGrantStays
      ring C e g hrootless hfire hneY hgrant
    have hdistance :=
      headlineRendezvousGapRequestAdvance ring e g hneE
    refine ⟨ring.rightNeighbor e, g, hreqNext, hgrantNext, ?_⟩
    rw [hre]
    omega
  · by_cases hge : g = ring.rightNeighbor e
    · have hgrantY : (C (ring.rightNeighbor e)).grant = true := by
        rw [← hge]
        exact hgrant
      by_cases hreqY : (C (ring.rightNeighbor e)).req = true
      · have hhold := headlineRendezvousNoFireResponderHolds
          ring hn C e hrootless hfire hreqY hgrantY
        refine ⟨ring.rightNeighbor e, ring.rightNeighbor e,
          hhold.1, hhold.2, ?_⟩
        rw [headlineRendezvousGapCoincident]
        exact Nat.zero_le _
      · have hreqFalse : (C (ring.rightNeighbor e)).req = false := by
          cases hh : (C (ring.rightNeighbor e)).req with
          | false => rfl
          | true => exact False.elim (hreqY hh)
        have hneY : r ≠ ring.rightNeighbor e := by
          intro hh
          have hv : (C (ring.rightNeighbor e)).req = true := by
            rw [← hh]
            exact hreq
          rw [hreqFalse] at hv
          cases hv
        have hreqNext := headlineRendezvousNoFireRequestStays
          ring hn C e r hrootless hfire hre hreq
        have hgrantNext := headlineRendezvousNoFireGrantMoves
          ring C e hrootless hfire hgrantY hreqFalse
        have hdistance :=
          headlineRendezvousGapGrantRetreat ring e r hneY
        refine ⟨r, e, hreqNext, hgrantNext, ?_⟩
        rw [hge]
        omega
    · have hreqNext := headlineRendezvousNoFireRequestStays
        ring hn C e r hrootless hfire hre hreq
      have hgrantNext := headlineRendezvousNoFireGrantStays
        ring C e g hrootless hfire hge hgrant
      exact ⟨r, g, hreqNext, hgrantNext, Nat.le_refl _⟩

/-- Item (3b), gap part: arbitrary no-FIRE real services
from a leaderless two-token cut cannot increase the
actual nested-fold minimum. -/
theorem headlineRendezvousNoFireMinGapNonincrease {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hrequest : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    headlineRendezvousMinGap (headlinePhysicalNext ring C e) ≤
      headlineRendezvousMinGap C := by
  obtain ⟨r, g, hr, hg, hmin⟩ :=
    headlineRendezvousMinGapAttained ring C hrequest hgrant
  obtain ⟨r', g', hr', hg', hgap⟩ :=
    headlineRendezvousNoFirePairDescendant
      ring hn C e r g hrootless hfire hr hg
  have hle :=
    headlineRendezvousMinGapLePair
      (headlinePhysicalNext ring C e) r' g' hr' hg'
  rw [hmin]
  exact Nat.le_trans hle hgap

/-- Monotonicity of the cap used in the observer rank. -/
private theorem headlineRendezvousCappedMonotone
    (n a b : Nat) (h : a ≤ b) :
    min n a ≤ min n b := by
  by_cases ha : n ≤ a
  · have hb : n ≤ b := Nat.le_trans ha h
    rw [Nat.min_eq_left ha, Nat.min_eq_left hb]
    exact Nat.le_refl n
  · have ha' : a ≤ n := by omega
    rw [Nat.min_eq_right ha']
    by_cases hb : n ≤ b
    · rw [Nat.min_eq_left hb]
      exact ha'
    · have hb' : b ≤ n := by omega
      rw [Nat.min_eq_right hb']
      exact h

private theorem headlineRendezvousRootlessNotRooted {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hrootless : ∀ i : Fin n, (C i).l = false) :
    ¬ headlineRooted ring C := by
  intro hh
  obtain ⟨i, hi⟩ := hh.2
  rw [hrootless i] at hi
  cases hi

/-- The rank, including its rooted branch, is always bounded by
one more than the actual minimum gap. -/
theorem headlineRendezvousRankUpper {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    headlineRendezvousRank ring C ≤
      headlineRendezvousMinGap C + 1 := by
  classical
  unfold headlineRendezvousRank
  split
  · exact Nat.zero_le _
  · exact Nat.min_le_right _ _

/-- On a rootless cut with both OLD token kinds, the cap n
does not truncate the true rank (since gap < n). -/
theorem headlineRendezvousRankRootlessExact {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hrequest : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    headlineRendezvousRank ring C =
      headlineRendezvousMinGap C + 1 := by
  classical
  have hnoroot :=
    headlineRendezvousRootlessNotRooted ring C hrootless
  have hsmall :=
    headlineRendezvousMinGapBelowSize ring C hrequest hgrant
  have hcap : headlineRendezvousMinGap C + 1 ≤ n := by
    omega
  unfold headlineRendezvousRank
  split
  · rename_i hroot
    exact False.elim (hnoroot hroot)
  · exact Nat.min_eq_right hcap

/-- Item (3b), rank part: every no-FIRE real edge weakly
decreases the physical observer rank from a leaderless
two-token cut. -/
theorem headlineRendezvousNoFireRankNonincrease {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hrequest : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    headlineRendezvousRank ring
      (headlinePhysicalNext ring C e) ≤
    headlineRendezvousRank ring C := by
  classical
  have hgap := headlineRendezvousNoFireMinGapNonincrease
    ring hn C e hrootless hfire hrequest hgrant
  have hOldRootless :=
    headlineRendezvousRootlessNotRooted ring C hrootless
  have hOld :
      headlineRendezvousRank ring C =
        min n (headlineRendezvousMinGap C + 1) := by
    unfold headlineRendezvousRank
    split
    · rename_i hroot
      exact False.elim (hOldRootless hroot)
    · rfl
  by_cases hNewRooted :
      headlineRooted ring (headlinePhysicalNext ring C e)
  · have hNew :
        headlineRendezvousRank ring
          (headlinePhysicalNext ring C e) = 0 := by
      unfold headlineRendezvousRank
      split
      · rfl
      · rename_i hnot
        exact False.elim (hnot hNewRooted)
    rw [hNew, hOld]
    exact Nat.zero_le _
  · have hNew :
        headlineRendezvousRank ring
          (headlinePhysicalNext ring C e) =
          min n (headlineRendezvousMinGap
            (headlinePhysicalNext ring C e) + 1) := by
      unfold headlineRendezvousRank
      split
      · rename_i hroot
        exact False.elim (hNewRooted hroot)
      · rfl
    rw [hNew, hOld]
    exact headlineRendezvousCappedMonotone n _ _
      (Nat.add_le_add_right hgap 1)

/-- Every edge weakly decreases the rank while the cut is
purified, leaderless and has an OLD token of each kind:
FIRE sends the rank to zero, otherwise the min-gap row applies. -/
theorem headlineRendezvousAllEdgesRankNonincrease {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hpurified : headlinePurified ring C)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hrequest : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    headlineRendezvousRank ring
      (headlinePhysicalNext ring C e) ≤
    headlineRendezvousRank ring C := by
  by_cases hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none
  · exact headlineRendezvousNoFireRankNonincrease
      ring (by omega : 2 ≤ n) C e hrootless hfire
      hrequest hgrant
  · have hroot := headlineRendezvousFireRooted
      ring hn C e hpurified hfire
    have hzero :
        headlineRendezvousRank ring
          (headlinePhysicalNext ring C e) = 0 := by
      classical
      unfold headlineRendezvousRank
      split
      · rfl
      · rename_i hnot
        exact False.elim (hnot hroot)
    rw [hzero]
    exact Nat.zero_le _

/-- Item (3c): nominating the outgoing edge of a minimum-gap
OLD request strictly decreases rank by at least one; if the
edge FIREs, the rooted rank is zero. -/
theorem headlineRendezvousNominatedStrict {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (r g : Fin n)
    (hpurified : headlinePurified ring C)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hrequest : (C r).req = true)
    (hgrant : (C g).grant = true)
    (hmin : headlineRendezvousMinGap C =
      (g.val + n - r.val) % n) :
    headlineRendezvousRank ring
      (headlinePhysicalNext ring C r) + 1 ≤
    headlineRendezvousRank ring C := by
  have hOld := headlineRendezvousRankRootlessExact
    ring C hrootless ⟨r, hrequest⟩ ⟨g, hgrant⟩
  by_cases hfire : oldFire (C r)
      (C (ring.rightNeighbor r)) = none
  · have hreqNext := headlineRendezvousNoFireOutgoingRequestMoves
      ring (by omega : 2 ≤ n) C r hrootless hfire hrequest
    have hgrantEFalse := headlineRendezvousNoFireSourceGrantFalse
      (C r) (C (ring.rightNeighbor r))
      (hrootless r) (hrootless (ring.rightNeighbor r))
      hfire hrequest
    have hgrantYFalse := headlineRendezvousNoFireCrossGrantFalse
      (C r) (C (ring.rightNeighbor r))
      (hrootless r) (hrootless (ring.rightNeighbor r))
      hfire hrequest
    have hneE : r ≠ g := by
      intro hh
      have hv : (C r).grant = true := by rw [hh]; exact hgrant
      rw [hgrantEFalse] at hv
      cases hv
    have hneY : g ≠ ring.rightNeighbor r := by
      intro hh
      have hv : (C (ring.rightNeighbor r)).grant = true := by
        rw [← hh]
        exact hgrant
      rw [hgrantYFalse] at hv
      cases hv
    have hgrantNext := headlineRendezvousNoFireGrantStays
      ring C r g hrootless hfire hneY hgrant
    have hgapNext := headlineRendezvousMinGapLePair
      (headlinePhysicalNext ring C r)
      (ring.rightNeighbor r) g hreqNext hgrantNext
    have hdist := headlineRendezvousGapRequestAdvance
      ring r g hneE
    have hUpper := headlineRendezvousRankUpper
      ring (headlinePhysicalNext ring C r)
    rw [hOld, hmin]
    omega
  · have hroot := headlineRendezvousFireRooted
      ring hn C r hpurified hfire
    have hNew :
        headlineRendezvousRank ring
          (headlinePhysicalNext ring C r) = 0 := by
      classical
      unfold headlineRendezvousRank
      split
      · rfl
      · rename_i hnot
        exact False.elim (hnot hroot)
    rw [hNew, hOld]
    omega

/-! Stopped target. The rank-drift argument cannot be applied
to arbitrary Cartesian cuts missing requests or grants.
The stopped target makes such cuts terminal, while a separate
invariant shows they cannot be encountered before the first
rooted FIRE from the starts of StageBirthTokenRendezvous. -/

def headlineRendezvousReady {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) : Prop :=
  headlinePurified ring C ∧
    (∃ r : Fin n, (C r).req = true) ∧
    (∃ g : Fin n, (C g).grant = true)

def headlineRendezvousStopped {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) : Prop :=
  headlineRooted ring C ∨ ¬headlineRendezvousReady ring C

/-- Any purified nonrooted cut has no leader at all. -/
theorem headlineRendezvousNoLeaderOfUnrooted {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hpurified : headlinePurified ring C)
    (hnot : ¬ headlineRooted ring C) :
    ∀ i : Fin n, (C i).l = false := by
  intro i
  cases hi : (C i).l with
  | false =>
      rfl
  | true =>
      have hleader : ∃ j : Fin n, (C j).l = true :=
        ⟨i, hi⟩
      have hroot : headlineRooted ring C :=
        ⟨hpurified.2 hleader, hleader⟩
      exact False.elim (hnot hroot)

/-- At each physical edge, a ready cut which is not rooted
either reaches rooted or remains ready. All native and
token coordinates are those of the actual protocol. -/
theorem headlineRendezvousReadyStepUntilRoot {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hready : headlineRendezvousReady ring C)
    (hnot : ¬ headlineRooted ring C) :
    headlineRooted ring (headlinePhysicalNext ring C e) ∨
      headlineRendezvousReady ring
        (headlinePhysicalNext ring C e) := by
  have hrootless := headlineRendezvousNoLeaderOfUnrooted
    ring C hready.1 hnot
  rcases headlineRendezvousRealEdgeSurvival
    ring hn C e hready.1 hrootless hready.2.1 hready.2.2 with
    hroot | ⟨hrequest, hgrant⟩
  · exact Or.inl hroot
  · exact Or.inr
      ⟨headlineStagesPurifiedStep ring hn C e hready.1,
        hrequest, hgrant⟩

/-- Choose an attaining OLD request, with the arbitrary zero
site reserved for invalid cuts that the stopped target absorbs. -/
noncomputable def headlineRendezvousChosenRequest {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) : Fin n := by
  classical
  exact if h : ∃ r g : Fin n,
      (C r).req = true ∧
      (C g).grant = true ∧
      headlineRendezvousMinGap C =
        (g.val + n - r.val) % n then
    Classical.choose h
  else ⟨0, ring.hn⟩

/-- In the valid two-token domain, the chosen source really
attains the nested-fold minimum with some OLD grant. -/
theorem headlineRendezvousChosenRequestAttains {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hrequest : ∃ r : Fin n, (C r).req = true)
    (hgrant : ∃ g : Fin n, (C g).grant = true) :
    ∃ g : Fin n,
      (C (headlineRendezvousChosenRequest ring C)).req = true ∧
      (C g).grant = true ∧
      headlineRendezvousMinGap C =
        (g.val + n -
          (headlineRendezvousChosenRequest ring C).val) % n := by
  classical
  unfold headlineRendezvousChosenRequest
  split
  · rename_i hex
    exact Classical.choose_spec hex
  · rename_i hfalse
    exact False.elim
      (hfalse (headlineRendezvousMinGapAttained
        ring C hrequest hgrant))

/-- A nonterminal stopped cut is exactly a ready, nonrooted cut. -/
private theorem headlineRendezvousUnstoppedReady {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hnot : ¬ headlineRendezvousStopped ring C) :
    headlineRendezvousReady ring C ∧
      ¬ headlineRooted ring C := by
  have hnroot : ¬ headlineRooted ring C := by
    intro hh
    exact hnot (Or.inl hh)
  have hready : headlineRendezvousReady ring C := by
    by_cases h : headlineRendezvousReady ring C
    · exact h
    · exact False.elim (hnot (Or.inr h))
  exact ⟨hready, hnroot⟩

/-- The selected ticket drops by one in every nonterminal
state of the stopped chain. -/
theorem headlineRendezvousStoppedNominatedDrop {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ C : HeadlineConfiguration n,
      ¬ headlineRendezvousStopped ring C →
      headlineRendezvousRank ring
        (headlinePhysicalNext ring C
          (headlineRendezvousChosenRequest ring C)) + 1 ≤
      headlineRendezvousRank ring C := by
  intro C hnot
  obtain ⟨hready, hnroot⟩ :=
    headlineRendezvousUnstoppedReady ring C hnot
  have hrootless := headlineRendezvousNoLeaderOfUnrooted
    ring C hready.1 hnroot
  obtain ⟨g, hreq, hgrant, hmin⟩ :=
    headlineRendezvousChosenRequestAttains
      ring C hready.2.1 hready.2.2
  exact headlineRendezvousNominatedStrict
    ring hn C (headlineRendezvousChosenRequest ring C) g
    hready.1 hrootless hreq hgrant hmin

/-- The rank is nonincreasing on every scheduler ticket
while the stopped chain is still nonterminal. -/
theorem headlineRendezvousStoppedAllEdgesNonincrease {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ C : HeadlineConfiguration n,
      ¬ headlineRendezvousStopped ring C →
      ∀ e : Fin n,
        headlineRendezvousRank ring
          (headlinePhysicalNext ring C e) ≤
        headlineRendezvousRank ring C := by
  intro C hnot e
  obtain ⟨hready, hnroot⟩ :=
    headlineRendezvousUnstoppedReady ring C hnot
  have hrootless := headlineRendezvousNoLeaderOfUnrooted
    ring C hready.1 hnroot
  exact headlineRendezvousAllEdgesRankNonincrease
    ring hn C e hready.1 hrootless
    hready.2.1 hready.2.2

/-- The finite-horizon first-hit cost of the physical rooted
target equals that of the stopped target on a rooted-or-ready
start. The inductive invariant prevents the stopped chain from
terminating through token loss before a real rooted FIRE. -/
theorem headlineRendezvousStoppedCostEqualsRooted {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n)
    (hstate : headlineRooted ring C ∨
      headlineRendezvousReady ring C) (T : Nat) :
    costNumerator (headlinePhysicalNext ring)
      (headlineRooted ring) C T =
    costNumerator (headlinePhysicalNext ring)
      (headlineRendezvousStopped ring) C T := by
  classical
  induction T generalizing C with
  | zero =>
      rfl
  | succ T ih =>
      by_cases hroot : headlineRooted ring C
      · have hstop : headlineRendezvousStopped ring C :=
          Or.inl hroot
        rw [costNumerator_terminal
          (headlinePhysicalNext ring) (headlineRooted ring)
          C hroot (T + 1),
          costNumerator_terminal
          (headlinePhysicalNext ring) (headlineRendezvousStopped ring)
          C hstop (T + 1)]
      · have hready : headlineRendezvousReady ring C := by
          rcases hstate with hr | hgood
          · exact False.elim (hroot hr)
          · exact hgood
        have hnotStop : ¬ headlineRendezvousStopped ring C := by
          intro hh
          rcases hh with hh | hh
          · exact hroot hh
          · exact hh hready
        rw [costNumerator_succ
          (headlinePhysicalNext ring) (headlineRooted ring)
          C hroot T,
          costNumerator_succ
          (headlinePhysicalNext ring) (headlineRendezvousStopped ring)
          C hnotStop T]
        have hsum :
            (List.ofFn (fun e : Fin n =>
              costNumerator (headlinePhysicalNext ring)
                (headlineRooted ring)
                (headlinePhysicalNext ring C e) T)).sum =
            (List.ofFn (fun e : Fin n =>
              costNumerator (headlinePhysicalNext ring)
                (headlineRendezvousStopped ring)
                (headlinePhysicalNext ring C e) T)).sum :=
          ofFn_sum_eq _ _ (fun e =>
            ih (headlinePhysicalNext ring C e)
              (headlineRendezvousReadyStepUntilRoot
                ring hn C e hready hroot))
        exact congrArg
          (fun a : Nat => n ^ (T + 1) + a) hsum

/-- Item (4): the expected first protected birth takes at
most n^2 physical scheduler tickets, uniformly over every
purified leaderless Cartesian cut containing both OLD token kinds. -/
theorem stageBirthTokenRendezvous_proved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageBirthTokenRendezvous ring := by
  intro C hpurified hrootless hgrant hrequest
  have hready : headlineRendezvousReady ring C :=
    ⟨hpurified, hrequest, hgrant⟩
  have hcost :
      ∀ D : HeadlineConfiguration n, ∀ T : Nat,
        costNumerator (headlinePhysicalNext ring)
          (headlineRendezvousStopped ring) D T ≤
        n ^ T * (n * headlineRendezvousRank ring D) :=
    Prob.costNumerator_le_of_nominated_edge
      (headlinePhysicalNext ring)
      (headlineRendezvousStopped ring)
      (headlineRendezvousRank ring)
      (headlineRendezvousChosenRequest ring)
      (headlineRendezvousStoppedNominatedDrop ring hn)
      (headlineRendezvousStoppedAllEdgesNonincrease ring hn)
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring)
    (headlineRooted ring)
    (by omega : 0 < n) C (n ^ 2)).2
  intro T
  have hcap :
      n * headlineRendezvousRank ring C ≤ n ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left n
      (headlineRendezvousRankCap ring C)
  calc
    costNumerator (headlinePhysicalNext ring)
        (headlineRooted ring) C T =
      costNumerator (headlinePhysicalNext ring)
        (headlineRendezvousStopped ring) C T :=
      headlineRendezvousStoppedCostEqualsRooted
        ring hn C (Or.inr hready) T
    _ ≤ n ^ T * (n * headlineRendezvousRank ring C) :=
      hcost C T
    _ ≤ n ^ T * (n ^ 2) :=
      Nat.mul_le_mul_left (n ^ T) hcap

end L3

