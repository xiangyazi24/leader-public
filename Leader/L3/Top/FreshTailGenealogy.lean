import Leader.L3.Top.FreshTailFifo

/-!
Deterministic G3 carrier replay.

The genealogy is computed from the scheduler word of a fixed-public
trace. In particular it is not a choice of labels existentially
attached to a path. A missing physical/ghost step is represented by
a missing slot label or by a receipt with an absent origin; neither
case is silently discarded.

Queue preservation and receipt injection have not been proved.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The three genealogical families. An origin is not a unique
live-carrier ID: a moving true tail leaves a separate U child. -/
inductive TopFreshTailOrigin (r : Nat) where
  | inherited (initialSlot : Fin r)
  | oldVisit (initialTail visitedSlot : Fin r)
  | freshBorder (sampleTime : Nat)
deriving DecidableEq

/-- Carrier birth time is separate from ancestral origin, so
two live children can have the same freshBorder origin. -/
structure TopFreshTailCarrier (r : Nat) where
  origin : TopFreshTailOrigin r
  born : Nat
deriving DecidableEq

/-- Port receipts use their chronological service time as identity.
The optional origin explicitly exposes a missing label bridge. -/
structure TopFreshTailGenealogyState (n : Nat) where
  trace : TopFixedTraceState n
  slots :
    Fin (topClockSpan n) →
      Option (TopFreshTailCarrier (topClockSpan n))
  consumed :
    List (Nat × Option (TopFreshTailOrigin (topClockSpan n)))

/-- Arbitrary initial source D or U bytes receive inherited
labels, except that an initially unread border is a fresh
waiting precursor, not a presumed historical sample. -/
def topFreshTailGenealogyInitialSlot
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (j : Fin (topClockSpan n)) :
    Option (TopFreshTailCarrier (topClockSpan n)) :=
  match (C (certSite s j.val)).qOut with
  | .E => none
  | .U =>
      if j.val = 0 then
        some { origin := .freshBorder 0, born := 0 }
      else
        some { origin := .inherited j, born := 0 }
  | .D _ _ =>
      some { origin := .inherited j, born := 0 }

/-- A true-tail departure creates an independent U child.
At nonborder slots, inherited tails generate OldVisit(i,j);
fresh tails instead generate a younger fresh-cohort child.
At the border, the new U is a fresh waiting precursor. -/
def topFreshTailGenealogyRearm
    {r : Nat} (j : Fin r) (time : Nat)
    (carrier : TopFreshTailCarrier r) :
    TopFreshTailCarrier r :=
  { origin :=
      (if j.val = 0 then
        .freshBorder time
      else
        match carrier.origin with
        | .inherited i => .oldVisit i j
        | .oldVisit i k => .oldVisit i k
        | .freshBorder birth => .freshBorder birth),
    born := time }

/-- Read both OLD and NEW physical source output fields.
Every case either transports an existing label, creates a
documented new carrier, or leaves the gap visible as none.
There is no assumed frame for a non-source scheduler edge. -/
noncomputable def topFreshTailGenealogyNextSlot
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (j : Fin (topClockSpan n)) :
    Option (TopFreshTailCarrier (topClockSpan n)) :=
  match
      ((topFixedTraceNext ring C G.trace e).1.1
        (certSite s j.val)).qOut with
  | .E => none
  | .U =>
      match (G.trace.1.1 (certSite s j.val)).qOut with
      | .E =>
          if j.val = 0 then
            some {
              origin := .freshBorder (G.trace.1.2.clock + 1),
              born := G.trace.1.2.clock + 1 }
          else none
      | .U => G.slots j
      | .D _ true =>
          (G.slots j).map
            (topFreshTailGenealogyRearm j
              (G.trace.1.2.clock + 1))
      | .D _ false => none
  | .D _ _ =>
      match (G.trace.1.1 (certSite s j.val)).qOut with
      | .E =>
          if hj : 0 < j.val then
            if e = certSite s (j.val - 1) then
              G.slots
                (⟨j.val - 1,
                  show j.val - 1 < topClockSpan n by omega⟩)
            else none
          else none
      | .U =>
          if j.val = 0 then
            some {
              origin := .freshBorder (G.trace.1.2.clock + 1),
              born := G.trace.1.2.clock + 1 }
          else G.slots j
      | .D _ _ => G.slots j

/-- The exact OLD digit-service export on the nominated physical
source-to-target edge; a clock-tick elsewhere is not a receipt. -/
noncomputable def topFreshTailGenealogyPortExport
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    Option (DigitExport (compileAdvice (ceilLogTwo n)) n) :=
  if e = certSite s (topClockSpan n - 1) ∧
      ring.rightNeighbor e = certSite s (topClockSpan n) then
    (digitService (Z.1.2.clock + 1)
      e (ring.rightNeighbor e)
      ((piD Z.1.1) e)
      ((piD Z.1.1) (ring.rightNeighbor e))
      (Z.1.2.current e)
      (Z.1.2.current (ring.rightNeighbor e))).comparison.exported
  else none

/-- One literal scheduler service updates the physical/audit
state, all source marks, and the chronological acceptance list. -/
noncomputable def topFreshTailGenealogyStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n) :
    TopFreshTailGenealogyState n :=
  { trace := topFixedTraceNext ring C G.trace e
    slots := fun j => topFreshTailGenealogyNextSlot ring C s G e j
    consumed :=
      G.consumed ++
        (if hr : 0 < topClockSpan n then
          (topFreshTailGenealogyPortExport ring C s G.trace e).toList.map
            (fun _ =>
              (G.trace.1.2.clock + 1,
                (G.slots
                  (⟨topClockSpan n - 1,
                    show topClockSpan n - 1 < topClockSpan n by omega⟩)
                  ).map (fun carrier => carrier.origin)))
        else []) }

/-- Initial labels are determined solely by the supplied C. -/
def topFreshTailGenealogyInitial
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailGenealogyState n :=
  { trace := ((C, digitAuditInitial (piD C)), [])
    slots := topFreshTailGenealogyInitialSlot C s
    consumed := [] }

/-- The deterministic source genealogy replay on an actual word. -/
noncomputable def topFreshTailGenealogyReplay
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    TopFreshTailGenealogyState n :=
  word.foldl (topFreshTailGenealogyStep ring C s)
    (topFreshTailGenealogyInitial C s)

/-- This is a FUNCTION of Z.2; Z itself is never decorated. -/
noncomputable def topFreshTailGenealogy
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) :
    TopFreshTailGenealogyState n :=
  topFreshTailGenealogyReplay ring C s Z.2

/-- The genealogy reproduces the exact physical/audit trace,
not a second transition system. Consumer: G3 queue induction. -/
private theorem topFreshTailGenealogyFoldTrace
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (word : List (Fin n)) :
    (word.foldl (topFreshTailGenealogyStep ring C s) G).trace =
      word.foldl (topFixedTraceNext ring C) G.trace := by
  induction word generalizing G with
  | nil => rfl
  | cons e rest ih =>
      change
        (rest.foldl (topFreshTailGenealogyStep ring C s)
          (topFreshTailGenealogyStep ring C s G e)).trace =
        rest.foldl (topFixedTraceNext ring C)
          (topFixedTraceNext ring C G.trace e)
      exact ih (topFreshTailGenealogyStep ring C s G e)

/-- The reconstructed trace is the imported exact fixed-public run. -/
theorem topFreshTailGenealogyTrace
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) :
    (topFreshTailGenealogy ring C s Z).trace =
      topFixedTraceRun ring C Z.2 := by
  change
    (Z.2.foldl (topFreshTailGenealogyStep ring C s)
      (topFreshTailGenealogyInitial C s)).trace =
    Z.2.foldl (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), [])
  exact topFreshTailGenealogyFoldTrace ring C s
    (topFreshTailGenealogyInitial C s) Z.2

/-- At a reached cut, deterministic replay returns the given
physical/audit state exactly. Consumer: historical receipt mapping. -/
theorem topFreshTailGenealogyTraceReached
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) :
    (topFreshTailGenealogy ring C s Z).trace = Z := by
  rw [topFreshTailGenealogyTrace]
  exact hreach.symm

/-- The actual G3 queue assertion is physical-slot agreement
plus right-to-left age order; it is not identified with the
desired counting theorem or made true by definition. -/
def TopFreshTailGenealogyQueue
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  (topFreshTailGenealogy ring C s Z).trace = Z ∧
  (∀ j : Fin (topClockSpan n),
      (Z.1.1 (certSite s j.val)).qOut = .E ↔
        (topFreshTailGenealogy ring C s Z).slots j = none) ∧
  (∀ i j : Fin (topClockSpan n),
      i.val < j.val →
      ∀ ahead behind : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s Z).slots j =
          some ahead →
        (topFreshTailGenealogy ring C s Z).slots i =
          some behind →
        ahead.born ≤ behind.born)

/-- Every initially marked carrier has birth age zero.
Consumer: the actual G3 queue base case. -/
private theorem topFreshTailGenealogyInitialBorn
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (j : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (h : topFreshTailGenealogyInitialSlot C s j =
      some carrier) :
    carrier.born = 0 := by
  cases hq : (C (certSite s j.val)).qOut with
  | E =>
      simp [topFreshTailGenealogyInitialSlot, hq] at h
  | U =>
      simp only [topFreshTailGenealogyInitialSlot, hq] at h
      split at h <;> cases h <;> rfl
  | D v tail =>
      simp only [topFreshTailGenealogyInitialSlot, hq] at h
      cases h
      rfl

/-- Base of the physical-source carrier queue: no sample or
export is fabricated from the arbitrary inherited scratch. -/
theorem topFreshTailGenealogyQueueStart
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailGenealogyQueue ring C s
      ((C, digitAuditInitial (piD C)), []) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro j
    change
      (C (certSite s j.val)).qOut = .E ↔
        topFreshTailGenealogyInitialSlot C s j = none
    cases hq : (C (certSite s j.val)).qOut with
    | E => simp [topFreshTailGenealogyInitialSlot, hq]
    | U =>
        simp only [topFreshTailGenealogyInitialSlot, hq]
        split <;> simp
    | D v tail =>
        simp [topFreshTailGenealogyInitialSlot, hq]
  · intro i j hij ahead behind ha hb
    change
      topFreshTailGenealogyInitialSlot C s j =
        some ahead at ha
    change
      topFreshTailGenealogyInitialSlot C s i =
        some behind at hb
    have hbefore :=
      topFreshTailGenealogyInitialBorn C s j ahead ha
    have hafter :=
      topFreshTailGenealogyInitialBorn C s i behind hb
    omega

/-- A labelled, occupied source slot cannot be overtaken by
a D on its incoming edge. Consumer: G3 queue step blocking case.
Uses the literal first-match physical QO owner row. -/
theorem topFreshTailGenealogyBlockedSourceFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailGenealogyQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hlabel :
      (topFreshTailGenealogy ring C s Z).slots j ≠ none)
    (e : Fin n)
    (hneighbour : ring.rightNeighbor e = certSite s j.val)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxo : (Z.1.1 e).qOut = .D v tail)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      .D v tail := by
  have hoccupied :
      (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E := by
    intro hE
    have hslot :
        (topFreshTailGenealogy ring C s Z).slots j =
          none :=
      (hqueue.2.1 j).1 (by rw [← hneighbour]; exact hE)
    exact hlabel hslot
  exact topFreshTailFifoOccupiedFrame ring C Z e
    v tail hxl hyl hxo hyb hoccupied

end L3

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: G3 causal FIFO. The only parent-child creation
recorded by this relation is a literal true-D departure leaving
a new U at the served source. The chronological prefix is
part of the real fixed-public scheduler word. -/
inductive TopFreshTailCausalParent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    TopFreshTailCarrier (topClockSpan n) →
    TopFreshTailCarrier (topClockSpan n) → Prop where
  | rearm
      (pre suffix : List (Fin n))
      (e : Fin n) (j : Fin (topClockSpan n))
      (v : Fin (compileAdvice (ceilLogTwo n)).topA)
      (parent : TopFreshTailCarrier (topClockSpan n))
      (hword : pre ++ e :: suffix = word)
      (hsite : e = certSite s j.val)
      (hsource :
        ((topFreshTailGenealogyReplay ring C s pre).trace.1.1 e).qOut =
          .D v true)
      (hslot :
        (topFreshTailGenealogyReplay ring C s pre).slots j =
          some parent)
      (hnew :
        ((topFixedTraceNext ring C
          (topFreshTailGenealogyReplay ring C s pre).trace e).1.1 e).qOut =
          .U) :
      TopFreshTailCausalParent ring C s word parent
        (topFreshTailGenealogyRearm j
          ((topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1)
          parent)
  | borderSample
      (pre suffix : List (Fin n))
      (e : Fin n) (j : Fin (topClockSpan n))
      (v : Fin (compileAdvice (ceilLogTwo n)).topA)
      (parent : TopFreshTailCarrier (topClockSpan n))
      (hword : pre ++ e :: suffix = word)
      (hjzero : j.val = 0)
      (hsite : e = certSite s j.val)
      (hsource :
        ((topFreshTailGenealogyReplay ring C s pre).trace.1.1 e).qOut =
          .U)
      (hslot :
        (topFreshTailGenealogyReplay ring C s pre).slots j =
          some parent)
      (hnew :
        ((topFixedTraceNext ring C
          (topFreshTailGenealogyReplay ring C s pre).trace e).1.1 e).qOut =
          .D v true) :
      TopFreshTailCausalParent ring C s word parent
        { origin := .freshBorder
            ((topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1),
          born :=
            (topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1 }

/-- Consumer: G3 parent-before-descendant clause. This is
the transitive closure of the actual chronological rearm
events, not an ordering of arbitrary birth timestamps. -/
inductive TopFreshTailCausalAncestor
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    TopFreshTailCarrier (topClockSpan n) →
    TopFreshTailCarrier (topClockSpan n) → Prop where
  | direct {a b}
      (h : TopFreshTailCausalParent ring C s word a b) :
      TopFreshTailCausalAncestor ring C s word a b
  | follow {a b c}
      (hfirst : TopFreshTailCausalAncestor ring C s word a b)
      (hlast : TopFreshTailCausalAncestor ring C s word b c) :
      TopFreshTailCausalAncestor ring C s word a c

/-- Consumer: first G3 induction case. No parent birth can
occur in the empty scheduler history. -/
private theorem topFreshTailCausalNoParentAtStart
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n)) :
    ¬ TopFreshTailCausalParent ring C s [] a b := by
  intro h
  cases h with
  | rearm pre suffix e j v parent hword hsite hsource hslot hnew =>
      have hlength := congrArg List.length hword
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hlength
      omega
  | borderSample pre suffix e j v parent hword hjzero hsite hsource hslot hnew =>
      have hlength := congrArg List.length hword
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hlength
      omega

structure TopFreshTailCausalQueue
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop where
  trace :
    topClockReached ring C Z ∧
    (topFreshTailGenealogy ring C s Z).trace = Z
  slot :
    ∀ j : Fin (topClockSpan n),
      (Z.1.1 (certSite s j.val)).qOut = .E ↔
        (topFreshTailGenealogy ring C s Z).slots j = none
  age :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots j = some a →
      a.born ≤ Z.1.2.clock
  identity :
    ∀ (i j : Fin (topClockSpan n))
      (a b : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots i = some a →
      (topFreshTailGenealogy ring C s Z).slots j = some b →
      a.origin = b.origin → a.born = b.born → i = j
  nonpass :
    (∀ (i j : Fin (topClockSpan n))
      (parent child : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s Z).slots i = some child →
      (topFreshTailGenealogy ring C s Z).slots j = some parent →
      TopFreshTailCausalAncestor ring C s Z.2 parent child →
      i.val < j.val) ∧
    (∀ (pre suffix : List (Fin n)) (e : Fin n)
      (i j movedI movedJ : Fin (topClockSpan n))
      (a b : TopFreshTailCarrier (topClockSpan n)),
      pre ++ e :: suffix = Z.2 →
      (topFreshTailGenealogyReplay ring C s pre).slots i = some a →
      (topFreshTailGenealogyReplay ring C s pre).slots j = some b →
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogyReplay ring C s pre) e).slots movedI =
          some a →
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogyReplay ring C s pre) e).slots movedJ =
          some b →
      i.val < j.val → movedI.val < movedJ.val)

/-- Consumer: CQ.identity at the arbitrary-private entrance.
Initial occupied slots have their own inherited label; the sole
other possibility is the border's initial U precursor. -/
private theorem topFreshTailCausalInitialLabelClass
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hslot : topFreshTailGenealogyInitialSlot C s j = some a) :
    a.origin = .inherited j ∨
      (j.val = 0 ∧ a.origin = .freshBorder 0) := by
  cases htok : (C (certSite s j.val)).qOut with
  | E =>
      simp [topFreshTailGenealogyInitialSlot, htok] at hslot
  | U =>
      by_cases hj : j.val = 0
      · simp only [topFreshTailGenealogyInitialSlot, htok,
          if_pos hj] at hslot
        cases hslot
        exact Or.inr ⟨hj, rfl⟩
      · simp only [topFreshTailGenealogyInitialSlot, htok,
          if_neg hj] at hslot
        cases hslot
        exact Or.inl rfl
  | D value tail =>
      simp only [topFreshTailGenealogyInitialSlot, htok] at hslot
      cases hslot
      exact Or.inl rfl

/-- Consumer: CQ.identity initial injectivity, including the
special inherited U at the source border. -/
private theorem topFreshTailCausalInitialIdentity
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (i j : Fin (topClockSpan n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (hi : topFreshTailGenealogyInitialSlot C s i = some a)
    (hj : topFreshTailGenealogyInitialSlot C s j = some b)
    (horigin : a.origin = b.origin) :
    i = j := by
  rcases topFreshTailCausalInitialLabelClass C s i a hi with
    hia | ⟨hizero, hia⟩
  · rcases topFreshTailCausalInitialLabelClass C s j b hj with
      hjb | ⟨hjzero, hjb⟩
    · have hlabel :
          (TopFreshTailOrigin.inherited i :
            TopFreshTailOrigin (topClockSpan n)) =
          .inherited j := by
        calc
          _ = a.origin := hia.symm
          _ = b.origin := horigin
          _ = _ := hjb
      cases hlabel
      rfl
    · have hlabel :
          (TopFreshTailOrigin.inherited i :
            TopFreshTailOrigin (topClockSpan n)) =
          .freshBorder 0 := by
        calc
          _ = a.origin := hia.symm
          _ = b.origin := horigin
          _ = _ := hjb
      cases hlabel
  · rcases topFreshTailCausalInitialLabelClass C s j b hj with
      hjb | ⟨hjzero, hjb⟩
    · have hlabel :
          (TopFreshTailOrigin.freshBorder 0 :
            TopFreshTailOrigin (topClockSpan n)) =
          .inherited j := by
        calc
          _ = a.origin := hia.symm
          _ = b.origin := horigin
          _ = _ := hjb
      cases hlabel
    · apply Fin.ext
      omega


/-- Consumer: source-to-successor genealogy transfer. -/
private theorem topFreshTailCausalNeighborSite
    {n : Nat} (ring : DirectedRing n) (s : Fin n)
    (k : Nat) :
    ring.rightNeighbor (certSite s k) =
      certSite s (k + 1) := by
  apply Fin.ext
  change ((s.val + k) % n + 1) % n =
    (s.val + (k + 1)) % n
  calc
    ((s.val + k) % n + 1) % n =
        (s.val + k + 1) % n :=
      Nat.mod_add_mod (s.val + k) n 1
    _ = (s.val + (k + 1)) % n := by
      congr 1

theorem topFreshTailCausalOccupiedBlock
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool) (parent : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hsource : (G.trace.1.1 e).qOut = .D v tail)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (G.trace.1.1 (ring.rightNeighbor e)).beta = false)
    (hoccupied :
      (G.trace.1.1 (ring.rightNeighbor e)).qOut ≠ .E)
    (hlabel : G.slots j = some parent) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some parent := by
  have hstay := topFreshTailFifoOccupiedFrame ring C G.trace e
    v tail hxl hyl hsource hyb hoccupied
  rw [hsite] at hstay hsource
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some parent
  simp [topFreshTailGenealogyNextSlot, hsite, hstay, hsource, hlabel]


theorem topFreshTailCausalOffPairFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hsource : certSite s j.val ≠ e)
    (htarget : certSite s j.val ≠ ring.rightNeighbor e)
    (hoccupied :
      (G.trace.1.1 (certSite s j.val)).qOut ≠ .E)
    (hlabel : G.slots j = some a) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some a := by
  have hframe := (topPortLiteralAwayFields ring C G.trace.1.1
    e (certSite s j.val) hsource htarget).2.2
  change
    ((topFixedTraceNext ring C G.trace e).1.1
      (certSite s j.val)).qOut =
        (G.trace.1.1 (certSite s j.val)).qOut at hframe
  cases htok : (G.trace.1.1 (certSite s j.val)).qOut with
  | E =>
      exact False.elim (hoccupied htok)
  | U =>
      change topFreshTailGenealogyNextSlot ring C s G e j =
        some a
      simp [topFreshTailGenealogyNextSlot, hframe, htok,
        hlabel]
  | D value tail =>
      change topFreshTailGenealogyNextSlot ring C s G e j =
        some a
      simp [topFreshTailGenealogyNextSlot, hframe, htok,
        hlabel]

/-- Consumer: QI/QC parallel owner rows. The genealogy reads
the same post-QO physical fields of the common OLD liveTopPair. -/
theorem topFreshTailCausalIndependentOwnerRows
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n) :
    ((topFreshTailGenealogyStep ring C s G e).trace.1.1 e).qOut =
      (topPortLiteralTopOwner ring G.trace.1.1 e).x.qOut ∧
    ((topFreshTailGenealogyStep ring C s G e).trace.1.1
      (ring.rightNeighbor e)).qOut =
      (topPortLiteralTopOwner ring G.trace.1.1 e).y.qOut := by
  change
    (topFixedPublicNext ring C G.trace.1.1 e e).qOut =
        (topPortLiteralTopOwner ring G.trace.1.1 e).x.qOut ∧
    (topFixedPublicNext ring C G.trace.1.1 e
       (ring.rightNeighbor e)).qOut =
        (topPortLiteralTopOwner ring G.trace.1.1 e).y.qOut
  exact ⟨(topPortLiteralSourceFields ring C G.trace.1.1 e).2.2,
    (topPortLiteralResponderFields
      ring hn C G.trace.1.1 e).2.2⟩


/-- Consumer: P.3 border-port accepted tail. The exact OLD
QO port row consumes the parent and leaves a new U child at
the source, simultaneously delivering a pending input. -/
theorem topFreshTailCausalPortDeparture
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hxi : (G.trace.1.1 e).qIn = .E)
    (hxc : (G.trace.1.1 e).qCarry = .OFF)
    (hyi : (G.trace.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (G.trace.1.1 (ring.rightNeighbor e)).qCarry = .OFF)
    (hyb : (G.trace.1.1 (ring.rightNeighbor e)).beta = true)
    (hxo : (G.trace.1.1 e).qOut = .D v true)
    (hslot : G.slots j = some parent) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
        some (topFreshTailGenealogyRearm j
          (G.trace.1.2.clock + 1) parent) ∧
    ((topFreshTailGenealogyStep ring C s G e).trace.1.1
       (ring.rightNeighbor e)).qIn = .P v true := by
  have hport := topFreshTailFifoPortTailRearms
    ring hn C G.trace e v hxl hyl hxi hxc hyi hyc hyb hxo
  have hsourceNew := hport.1
  rw [hsite] at hsourceNew hxo
  constructor
  · change topFreshTailGenealogyNextSlot ring C s G e j =
      some (topFreshTailGenealogyRearm j
        (G.trace.1.2.clock + 1) parent)
    simp [topFreshTailGenealogyNextSlot, hsite, hsourceNew,
      hxo, hslot]
  · exact hport.2

/-- Consumer: blocked-border source row for G3. This proves
the OLD first-match QO result without assuming that QI or QC
has performed a separate transition. -/
private theorem topFreshTailCausalBlockedOwner
    (c : Compiled) (x y : Agent c) (betaX betaY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hyb : y.beta = true)
    (hxo : x.qOut = .D v tail)
    (hblock : y.qIn.isE = false ∨ y.qCarry.isOff = false) :
    (liveTopPair c x y betaX betaY).x.qOut = .D v tail := by
  rcases hblock with hinput | hcarry
  · cases hiy : y.qIn with
    | E =>
        simp [hiy, InTok.isE] at hinput
    | P value stamp =>
        simp [liveTopPair, hxl, hyl, hyb, hxo, hiy,
          OutTok.isD, InTok.isE]
    | S value stamp =>
        simp [liveTopPair, hxl, hyl, hyb, hxo, hiy,
          OutTok.isD, InTok.isE]
    | X =>
        simp [liveTopPair, hxl, hyl, hyb, hxo, hiy,
          OutTok.isD, InTok.isE]
  · cases hcy : y.qCarry with
    | OFF =>
        simp [hcy, QCarry.isOff] at hcarry
    | L carry error =>
        simp [liveTopPair, hxl, hyl, hyb, hxo, hcy,
          OutTok.isD, QCarry.isOff]

/-- Consumer: P.3 blocked border port. An OLD D cannot
disappear when the target input/carry fails the acceptance
guard; both its physical byte and its genealogy are retained. -/
theorem topFreshTailCausalPortBlocked
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (G.trace.1.1 (ring.rightNeighbor e)).beta = true)
    (hxo : (G.trace.1.1 e).qOut = .D v tail)
    (hblock :
      (G.trace.1.1 (ring.rightNeighbor e)).qIn.isE = false ∨
      (G.trace.1.1 (ring.rightNeighbor e)).qCarry.isOff = false)
    (hlabel : G.slots j = some parent) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some parent := by
  have howner :
      (topPortLiteralTopOwner ring G.trace.1.1 e).x.qOut =
        .D v tail := by
    unfold topPortLiteralTopOwner
    exact topFreshTailCausalBlockedOwner
      (compileAdvice (ceilLogTwo n))
      (G.trace.1.1 e) (G.trace.1.1 (ring.rightNeighbor e))
      _ _ v tail hxl hyl hyb hxo hblock
  have hsourceNew :
      ((topFixedTraceNext ring C G.trace e).1.1 e).qOut =
        .D v tail := by
    change (topFixedPublicNext ring C G.trace.1.1 e e).qOut =
      .D v tail
    exact (topPortLiteralSourceFields
      ring C G.trace.1.1 e).2.2.trans howner
  rw [hsite] at hsourceNew hxo
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some parent
  simp [topFreshTailGenealogyNextSlot, hsite, hsourceNew,
    hxo, hlabel]

/-- Consumer: deterministic CQ genealogy coordinate on an
appended scheduler word; no witness is chosen or erased. -/
private theorem topFreshTailCausalFoldSnoc
    {α β : Type} (f : β → α → β)
    (initial : β) (word : List α) (e : α) :
    (word ++ [e]).foldl f initial =
      f (word.foldl f initial) e := by
  induction word generalizing initial with
  | nil =>
      rfl
  | cons a rest ih =>
      exact ih (f initial a)

/-- Consumer: topFreshTailCausalQueueStep. The deterministic
genealogy of a one-edge-reached trace is exactly one ghost step
of the old real trace, not an independently selected labelling. -/
theorem topFreshTailCausalReplayNext
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e) =
    topFreshTailGenealogyStep ring C s
      (topFreshTailGenealogy ring C s Z) e := by
  change topFreshTailGenealogyReplay ring C s (Z.2 ++ [e]) =
    topFreshTailGenealogyStep ring C s
      (topFreshTailGenealogyReplay ring C s Z.2) e
  unfold topFreshTailGenealogyReplay
  exact topFreshTailCausalFoldSnoc
    (topFreshTailGenealogyStep ring C s)
    (topFreshTailGenealogyInitial C s) Z.2 e

/-- Consumer: topFreshTailCausalQueueRun. Every property of
the real causal queue that has a genuine one-step preservation
proof propagates over the arbitrary scheduler word. -/
private theorem topFreshTailCausalFoldQueue
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hstep : ∀ (Z : TopFixedTraceState n) (e : Fin n),
      TopFreshTailCausalQueue ring C s Z →
      TopFreshTailCausalQueue ring C s
        (topFixedTraceNext ring C Z e))
    (Z : TopFixedTraceState n)
    (hZ : TopFreshTailCausalQueue ring C s Z)
    (word : List (Fin n)) :
    TopFreshTailCausalQueue ring C s
      (word.foldl (topFixedTraceNext ring C) Z) := by
  induction word generalizing Z with
  | nil =>
      exact hZ
  | cons e rest ih =>
      change TopFreshTailCausalQueue ring C s
        (rest.foldl (topFixedTraceNext ring C)
          (topFixedTraceNext ring C Z e))
      exact ih (topFixedTraceNext ring C Z e)
        (hstep Z e hZ)

private theorem topFreshTailCausalNonmarkerEmptyOwner
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hxo : x.qOut = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut = .E := by
  simp [liveTopPair, hxl, hyl, hxb, hxo,
    OutTok.isD, OutTok.isE, OutTok.isU]

/-- Consumer: source-slot occupancy part of CQ. The fixed
nonmarker source E remains E and its ghost slot stays none. -/
theorem topFreshTailCausalNonmarkerEmpty
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hxb : (G.trace.1.1 e).beta = false)
    (hxo : (G.trace.1.1 e).qOut = .E) :
    ((topFreshTailGenealogyStep ring C s G e).trace.1.1 e).qOut =
        .E ∧
    (topFreshTailGenealogyStep ring C s G e).slots j =
        none := by
  have howner :
      (topPortLiteralTopOwner ring G.trace.1.1 e).x.qOut = .E := by
    unfold topPortLiteralTopOwner
    exact topFreshTailCausalNonmarkerEmptyOwner
      (compileAdvice (ceilLogTwo n))
      (G.trace.1.1 e) (G.trace.1.1 (ring.rightNeighbor e))
      _ _ hxl hyl hxb hxo
  have hpost :
      ((topFixedTraceNext ring C G.trace e).1.1 e).qOut = .E := by
    change (topFixedPublicNext ring C G.trace.1.1 e e).qOut = .E
    exact (topPortLiteralSourceFields
      ring C G.trace.1.1 e).2.2.trans howner
  constructor
  · exact hpost
  · rw [hsite] at hpost
    change topFreshTailGenealogyNextSlot ring C s G e j = none
    simp [topFreshTailGenealogyNextSlot, hsite, hpost]


end L3

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: the empty-word nonpass field of
topFreshTailCausalQueueStart. -/
private theorem topFreshTailCausalNoAncestorAtStart
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n)) :
    ¬ TopFreshTailCausalAncestor ring C s [] a b := by
  intro h
  induction h with
  | direct hp =>
      exact topFreshTailCausalNoParentAtStart ring C s _ _ hp
  | follow hfirst hlast ihfirst ihlast =>
      exact ihfirst

/-- Consumer: the actual causal queue induction on a scheduler word.
Arbitrary initial private source output is allowed. -/
theorem topFreshTailCausalQueueStart
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailCausalQueue ring C s
      ((C, digitAuditInitial (piD C)), []) := by
  have hold := topFreshTailGenealogyQueueStart ring C s
  refine ⟨⟨?_, hold.1⟩, hold.2.1, ?_, ?_, ?_⟩
  · change ((C, digitAuditInitial (piD C)), []) =
        topFixedTraceRun ring C []
    rfl
  · intro j a ha
    change topFreshTailGenealogyInitialSlot C s j = some a at ha
    have hborn := topFreshTailGenealogyInitialBorn C s j a ha
    rw [hborn]
    exact Nat.le_refl _
  · intro i j a b hi hj horg _hborn
    change topFreshTailGenealogyInitialSlot C s i = some a at hi
    change topFreshTailGenealogyInitialSlot C s j = some b at hj
    exact topFreshTailCausalInitialIdentity C s i j a b hi hj horg
  · constructor
    · intro i j parent child hi hj hancestor
      exact False.elim
        (topFreshTailCausalNoAncestorAtStart
          ring C s parent child hancestor)
    · intro pre suffix e i j movedI movedJ a b hword
        hbeforeI hbeforeJ hafterI hafterJ hij
      have hlength := congrArg List.length hword
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hlength
      omega

/-- Consumer: CQ.slot and CQ.identity in the source-rearm row.
A true-tail D leaves a younger U; a non-tail D leaves E. -/
theorem topFreshTailCausalDataMove
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool) (parent : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hsource : (G.trace.1.1 e).qOut = .D v tail)
    (htarget : (G.trace.1.1 (ring.rightNeighbor e)).qOut = .E)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (G.trace.1.1 (ring.rightNeighbor e)).beta = false)
    (hlabel : G.slots j = some parent) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      if tail then
        some (topFreshTailGenealogyRearm j
          (G.trace.1.2.clock + 1) parent)
      else none := by
  have hmove := (topFreshTailFifoDataMove ring hn C G.trace e
    v tail hxl hyl hsource htarget hyb).1
  rw [hsite] at hmove hsource
  cases tail with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hmove ⊢
      change topFreshTailGenealogyNextSlot ring C s G e j = none
      simp [topFreshTailGenealogyNextSlot, hsite, hmove]
  | true =>
      simp only [ite_true] at hmove ⊢
      change topFreshTailGenealogyNextSlot ring C s G e j =
        some (topFreshTailGenealogyRearm j
          (G.trace.1.2.clock + 1) parent)
      simp [topFreshTailGenealogyNextSlot, hsite, hmove,
        hsource, hlabel]

/-- Consumer: CQ.identity under movement into an OLD empty
nonmarker source successor; the responder gets the OLD carrier. -/
theorem topFreshTailCausalDataMoveTarget
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool) (parent : TopFreshTailCarrier (topClockSpan n))
    (hnext : j.val + 1 < topClockSpan n)
    (hsite : e = certSite s j.val)
    (hsource : (G.trace.1.1 e).qOut = .D v tail)
    (htarget : (G.trace.1.1 (ring.rightNeighbor e)).qOut = .E)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (G.trace.1.1 (ring.rightNeighbor e)).beta = false)
    (hlabel : G.slots j = some parent) :
    (topFreshTailGenealogyStep ring C s G e).slots
      (⟨j.val + 1, show j.val + 1 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n)) = some parent := by
  have hmove := (topFreshTailFifoDataMove ring hn C G.trace e
    v tail hxl hyl hsource htarget hyb).2
  have hneighbour :
      ring.rightNeighbor e = certSite s (j.val + 1) := by
    rw [hsite]
    exact topFreshTailCausalNeighborSite ring s j.val
  rw [hneighbour] at hmove htarget
  rw [hsite] at hmove
  have hindexFin :
      (⟨(j.val + 1) - 1,
        show (j.val + 1) - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)) = j := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  have hsiteBefore :
      e = certSite s ((j.val + 1) - 1) := by
    have hsub : (j.val + 1) - 1 = j.val := by omega
    rw [hsub]
    exact hsite
  change topFreshTailGenealogyNextSlot ring C s G e
    (⟨j.val + 1, show j.val + 1 < topClockSpan n by omega⟩ :
      Fin (topClockSpan n)) = some parent
  simp [topFreshTailGenealogyNextSlot, hsite, hmove, htarget,
    hsiteBefore, hindexFin, hlabel]

/-- Consumer: CQ.slot border bootstrap by the actual marker E->U row. -/
theorem topFreshTailCausalMarkerBirth
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hjzero : j.val = 0)
    (hempty : (G.trace.1.1 e).qOut = .E)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hmarker : (G.trace.1.1 e).beta = true) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some { origin := .freshBorder (G.trace.1.2.clock + 1),
             born := G.trace.1.2.clock + 1 } := by
  have hnew := topFreshTailFifoMarkerBootstraps
    ring C G.trace e hxl hyl hmarker hempty
  rw [hsite] at hnew hempty
  rw [hjzero] at hnew hempty
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some { origin := .freshBorder (G.trace.1.2.clock + 1),
           born := G.trace.1.2.clock + 1 }
  simp [topFreshTailGenealogyNextSlot, hsite, hjzero, hnew, hempty]

/-- Consumer: CQ.slot for an interior OLD U sampled into
a physical D, without allocating another carrier identity. -/
theorem topFreshTailCausalUnreadInterior
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hjpositive : 0 < j.val)
    (hsource : (G.trace.1.1 e).qOut = .U)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hslot : G.slots j = some a) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some a := by
  have hnew := topFreshTailFifoUnreadSamples
    ring C G.trace e hxl hyl hsource
  rw [hsite] at hnew hsource
  have hnonzero : j.val ≠ 0 := by omega
  change topFreshTailGenealogyNextSlot ring C s G e j = some a
  simp [topFreshTailGenealogyNextSlot, hsite, hnew,
    hsource, hnonzero, hslot]

/-- Consumer: CQ.age and border causal-retag at U->D.
The new identity has precisely the service-time birth. -/
theorem topFreshTailCausalUnreadBorder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hsite : e = certSite s j.val)
    (hjzero : j.val = 0)
    (hsource : (G.trace.1.1 e).qOut = .U)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some { origin := .freshBorder (G.trace.1.2.clock + 1),
             born := G.trace.1.2.clock + 1 } := by
  have hnew := topFreshTailFifoUnreadSamples
    ring C G.trace e hxl hyl hsource
  rw [hsite] at hnew hsource
  rw [hjzero] at hnew hsource
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some { origin := .freshBorder (G.trace.1.2.clock + 1),
           born := G.trace.1.2.clock + 1 }
  simp [topFreshTailGenealogyNextSlot, hsite, hjzero, hnew, hsource]

/-- Consumer: an independently proved real-edge CQ preservation
lifts to the original fixed-public scheduler word and audit. -/
theorem topFreshTailCausalQueueRun_of_step
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hstep : ∀ (Z : TopFixedTraceState n) (e : Fin n),
      TopFreshTailCausalQueue ring C s Z →
      TopFreshTailCausalQueue ring C s
        (topFixedTraceNext ring C Z e))
    (word : List (Fin n)) :
    TopFreshTailCausalQueue ring C s
      (topFixedTraceRun ring C word) := by
  have hstart :
      TopFreshTailCausalQueue ring C s
        ((C, digitAuditInitial (piD C)), []) :=
    topFreshTailCausalQueueStart ring C s
  have hfold :
      TopFreshTailCausalQueue ring C s
        (word.foldl (topFixedTraceNext ring C)
          ((C, digitAuditInitial (piD C)), [])) :=
    topFreshTailCausalFoldQueue ring C s hstep
      ((C, digitAuditInitial (piD C)), []) hstart word
  change TopFreshTailCausalQueue ring C s
    (word.foldl (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), []))
  exact hfold

end L3

namespace L3

/-- P.3: the actual reached fixed-public trace retains the OLD
    leader and delimiter bits of its nominated entrance.
    Consumer: the geometry hypotheses of
    topFreshTailCausalQueueStep. -/
theorem topFreshTailCausalReachedPublicMask
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (i : Fin n) :
    (Z.1.1 i).l = (C i).l ∧
    (Z.1.1 i).beta = (C i).beta := by
  have hfold :
      ∀ (word : List (Fin n))
        (F : TopFixedTraceState n),
        (F.1.1 i).l = (C i).l ∧
        (F.1.1 i).beta = (C i).beta →
        ((word.foldl (topFixedTraceNext ring C) F).1.1 i).l =
          (C i).l ∧
        ((word.foldl (topFixedTraceNext ring C) F).1.1 i).beta =
          (C i).beta := by
    intro word
    induction word with
    | nil =>
        intro F hF
        exact hF
    | cons e rest ih =>
        intro F _
        change
          ((rest.foldl (topFixedTraceNext ring C)
            (topFixedTraceNext ring C F e)).1.1 i).l =
              (C i).l ∧
          ((rest.foldl (topFixedTraceNext ring C)
            (topFixedTraceNext ring C F e)).1.1 i).beta =
              (C i).beta
        exact ih (topFixedTraceNext ring C F e)
          (topPortFixedPublicMaskStep ring C F e i)
  have hrun :
      ((topFixedTraceRun ring C Z.2).1.1 i).l = (C i).l ∧
      ((topFixedTraceRun ring C Z.2).1.1 i).beta =
        (C i).beta := by
    exact hfold Z.2
      ((C, digitAuditInitial (piD C)), [])
      ⟨rfl, rfl⟩
  rw [← hreach] at hrun
  exact hrun

/-- P.3 fixed source arc: all source sites and their outgoing
    neighbors are followers, with a true marker only at offset
    zero and at the destination border r. The two marker clauses
    are exactly CompleteBlockPair, not an assumption on qOut.
    Consumer: nonmarker E and marker-bootstrapping branches
    of topFreshTailCausalQueueStep. -/
theorem topFreshTailCausalSourcePublicGeometry
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (j : Fin (topClockSpan n)) :
    (Z.1.1 (certSite s j.val)).l = false ∧
    (Z.1.1 (ring.rightNeighbor
      (certSite s j.val))).l = false ∧
    (Z.1.1 (certSite s j.val)).beta =
      (if j.val = 0 then true else false) ∧
    (Z.1.1 (ring.rightNeighbor
      (certSite s j.val))).beta =
      (if j.val + 1 = topClockSpan n then true else false) := by
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  have hneigh :
      ring.rightNeighbor (certSite s j.val) =
        certSite s (j.val + 1) :=
    topFreshTailCausalNeighborSite ring s j.val
  have hsrc := topFreshTailCausalReachedPublicMask
    ring C Z hreach (certSite s j.val)
  have hdst := topFreshTailCausalReachedPublicMask
    ring C Z hreach
      (ring.rightNeighbor (certSite s j.val))
  have hsrcLeader :
      (C (certSite s j.val)).l = false :=
    topPortEligibleFollower C s hbad j.val (by have hj := j.isLt; omega)
  have hdstLeader :
      (C (ring.rightNeighbor (certSite s j.val))).l =
        false := by
    rw [hneigh]
    exact topPortEligibleFollower C s hbad (j.val + 1)
      (by have hj := j.isLt; omega)
  have hsrcMarker :
      (C (certSite s j.val)).beta =
        (if j.val = 0 then true else false) := by
    by_cases hj : j.val = 0
    · rw [if_pos hj, hj, certSite_zero]
      exact hbad.1.1
    · rw [if_neg hj]
      exact hbad.1.2.2.2.2.1 j (by omega)
  have hdstMarker :
      (C (ring.rightNeighbor (certSite s j.val))).beta =
        (if j.val + 1 = topClockSpan n then true else false) := by
    rw [hneigh]
    by_cases hj : j.val + 1 = topClockSpan n
    · rw [if_pos hj, hj]
      exact hbad.1.2.1
    · rw [if_neg hj]
      have hpos : 0 < j.val + 1 := by omega
      have hbound : j.val + 1 < topClockSpan n := by
        have hlim := j.isLt
        omega
      exact hbad.1.2.2.2.2.1
        (⟨j.val + 1, hbound⟩ : Fin (topClockSpan n))
        (by simpa only [Fin.val_mk] using hpos)
  exact ⟨hsrc.1.trans hsrcLeader,
    hdst.1.trans hdstLeader,
    hsrc.2.trans hsrcMarker,
    hdst.2.trans hdstMarker⟩

/-- P.3 causal queue: the reached trace and deterministic replay
    component survives one literal selected edge, independent of
    the private qOut first-match branch. Consumer:
    topFreshTailCausalQueueStep.trace. -/
theorem topFreshTailCausalQueueTraceStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z) :
    topClockReached ring C
      (topFixedTraceNext ring C Z e) ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).trace =
      topFixedTraceNext ring C Z e := by
  have hreach :=
    topPortReachedNext ring C Z e hqueue.trace.1
  exact ⟨hreach,
    topFreshTailGenealogyTraceReached ring C s
      (topFixedTraceNext ring C Z e) hreach⟩


/-- A deterministic causal carrier cannot acquire a birth time
    later than the selected audit service. Every nonfresh branch
    copies an OLD slot; a rearm or border sample is stamped with
    exactly the NEW audit clock. Consumer: CQ.age in
    topFreshTailCausalQueueStep. -/
theorem topFreshTailCausalSlotAgeNext
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n)
    (hAge : ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      G.slots j = some a →
        a.born ≤ G.trace.1.2.clock)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogyStep ring C s G e).slots j =
        some a) :
    a.born ≤
      (topFreshTailGenealogyStep ring C s G e).trace.1.2.clock := by
  change a.born ≤ G.trace.1.2.clock + 1
  change
    topFreshTailGenealogyNextSlot ring C s G e j = some a at hnew
  unfold topFreshTailGenealogyNextSlot at hnew
  cases hpost :
      ((topFixedTraceNext ring C G.trace e).1.1
        (certSite s j.val)).qOut with
  | E =>
      simp only [hpost] at hnew
      cases hnew
  | U =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            exact Nat.le_refl _
          · cases hnew
      | U =>
          simp only [hold] at hnew
          exact Nat.le_trans (hAge j a hnew) (Nat.le_succ _)
      | D value tail =>
          cases tail with
          | false =>
              simp [hold] at hnew
          | true =>
              cases hslot : G.slots j with
              | none =>
                  simp [hold, hslot] at hnew
              | some parent =>
                  simp [hold, hslot] at hnew
                  cases hnew
                  exact Nat.le_refl _
  | D value tail =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · split at hnew
            · exact Nat.le_trans
                (hAge
                  (⟨j.val - 1,
                    show j.val - 1 < topClockSpan n by omega⟩ :
                    Fin (topClockSpan n)) a hnew)
                (Nat.le_succ _)
            · cases hnew
          · cases hnew
      | U =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            exact Nat.le_refl _
          · exact Nat.le_trans (hAge j a hnew) (Nat.le_succ _)
      | D oldValue oldTail =>
          simp only [hold] at hnew
          exact Nat.le_trans (hAge j a hnew) (Nat.le_succ _)

/-- CQ.age on the actual deterministic genealogy replay, with the
    historical clock taken from the same physical scheduler trace.
    Consumer: topFreshTailCausalQueueStep.age. -/
theorem topFreshTailCausalQueueAgeStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z) :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a →
      a.born ≤
        (topFixedTraceNext ring C Z e).1.2.clock := by
  intro j a hnew
  rw [topFreshTailCausalReplayNext] at hnew
  have hAge :
      ∀ (k : Fin (topClockSpan n))
        (b : TopFreshTailCarrier (topClockSpan n)),
        (topFreshTailGenealogy ring C s Z).slots k = some b →
          b.born ≤
            (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
    intro k b hslot
    rw [hqueue.trace.2]
    exact hqueue.age k b hslot
  have hstep := topFreshTailCausalSlotAgeNext
    ring C s (topFreshTailGenealogy ring C s Z) e
    hAge j a hnew
  change
    a.born ≤
      (topFixedTraceNext ring C
        (topFreshTailGenealogy ring C s Z).trace e).1.2.clock
    at hstep
  rw [hqueue.trace.2] at hstep
  exact hstep


/-- On every actual P.3 scheduler word, irrespective of arbitrary
    inherited output bytes, every causal carrier's birth time is
    at most the completed digit-audit clock. This is the
    unconditional CQ.age word-induction component, independent
    of the still-open identity and ancestry clauses.
    Consumer: topFreshTailCausalQueueRun.age. -/
theorem topFreshTailCausalQueueAgeRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C word)).slots j = some a →
      a.born ≤ (topFixedTraceRun ring C word).1.2.clock := by
  have hfold :
      ∀ (w : List (Fin n)) (G : TopFreshTailGenealogyState n),
        (∀ (j : Fin (topClockSpan n))
          (a : TopFreshTailCarrier (topClockSpan n)),
          G.slots j = some a →
            a.born ≤ G.trace.1.2.clock) →
        ∀ (j : Fin (topClockSpan n))
          (a : TopFreshTailCarrier (topClockSpan n)),
          (w.foldl (topFreshTailGenealogyStep ring C s) G).slots j =
            some a →
          a.born ≤
            (w.foldl (topFreshTailGenealogyStep ring C s) G).trace.1.2.clock := by
    intro w
    induction w with
    | nil =>
        intro G hage j a hslot
        exact hage j a hslot
    | cons e rest ih =>
        intro G hage j a hslot
        change
          (rest.foldl (topFreshTailGenealogyStep ring C s)
            (topFreshTailGenealogyStep ring C s G e)).slots j =
              some a at hslot
        exact ih (topFreshTailGenealogyStep ring C s G e)
          (fun k b hb =>
            topFreshTailCausalSlotAgeNext
              ring C s G e hage k b hb) j a hslot
  have hstart :
      ∀ (j : Fin (topClockSpan n))
        (a : TopFreshTailCarrier (topClockSpan n)),
        (topFreshTailGenealogyInitial C s).slots j = some a →
          a.born ≤
            (topFreshTailGenealogyInitial C s).trace.1.2.clock := by
    intro j a hslot
    change topFreshTailGenealogyInitialSlot C s j = some a at hslot
    have hborn := topFreshTailGenealogyInitialBorn C s j a hslot
    rw [hborn]
    exact Nat.zero_le _
  have hrun := hfold word (topFreshTailGenealogyInitial C s) hstart
  intro j a hslot
  have hword :
      (topFixedTraceRun ring C word).2 = word :=
    topFreshTailFifoRunWord ring C word
  change
    (topFreshTailGenealogyReplay ring C s
      (topFixedTraceRun ring C word).2).slots j =
        some a at hslot
  rw [hword] at hslot
  have hbound := hrun j a hslot
  have htrace :
      (topFreshTailGenealogyReplay ring C s word).trace =
        topFixedTraceRun ring C word := by
    have hreal :=
      topFreshTailGenealogyTraceReached ring C s
        (topFixedTraceRun ring C word) (by
          change topFixedTraceRun ring C word =
            topFixedTraceRun ring C
              (topFixedTraceRun ring C word).2
          rw [hword])
    change
      (topFreshTailGenealogyReplay ring C s
        (topFixedTraceRun ring C word).2).trace =
          topFixedTraceRun ring C word at hreal
    rw [hword] at hreal
    exact hreal
  change a.born ≤
    (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock at hbound
  rw [htrace] at hbound
  exact hbound


/-- A source D/true move with an OLD empty nonmarker successor
    leaves the new child at the old source and transports the
    unchanged parent to the immediately following source slot.
    This is the local parent-behind-descendant geometry
    consumed by CQ.nonpass; no global age sorting is asserted. -/
theorem topFreshTailCausalRearmBehindMovedParent
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hnext : j.val + 1 < topClockSpan n)
    (hsite : e = certSite s j.val)
    (hsource : (G.trace.1.1 e).qOut = .D v true)
    (htarget : (G.trace.1.1 (ring.rightNeighbor e)).qOut = .E)
    (hxl : (G.trace.1.1 e).l = false)
    (hyl : (G.trace.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (G.trace.1.1 (ring.rightNeighbor e)).beta = false)
    (hlabel : G.slots j = some parent) :
    (topFreshTailGenealogyStep ring C s G e).slots j =
      some (topFreshTailGenealogyRearm j
        (G.trace.1.2.clock + 1) parent) ∧
    (topFreshTailGenealogyStep ring C s G e).slots
      (⟨j.val + 1,
        show j.val + 1 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n)) = some parent := by
  have hsourceNew := topFreshTailCausalDataMove
    ring hn C s G e j v true parent hsite hsource
    htarget hxl hyl hyb hlabel
  have htargetNew := topFreshTailCausalDataMoveTarget
    ring hn C s G e j v true parent hnext hsite
    hsource htarget hxl hyl hyb hlabel
  exact ⟨(by simpa only [ite_true] using hsourceNew),
    htargetNew⟩

/-- An inherited or previously live carrier cannot be mistaken
    for a newly rearmed child at the NEXT service time.
    This rules out an entire class of CQ.identity collisions.
    Consumer: the rearm branch of topFreshTailCausalQueueStep. -/
theorem topFreshTailCausalNewChildDistinct
    {n : Nat} (G : TopFreshTailGenealogyState n)
    (j : Fin (topClockSpan n))
    (parent old : TopFreshTailCarrier (topClockSpan n))
    (hold : old.born ≤ G.trace.1.2.clock) :
    topFreshTailGenealogyRearm j
      (G.trace.1.2.clock + 1) parent ≠ old := by
  intro heq
  have hborn := congrArg
    (fun a : TopFreshTailCarrier (topClockSpan n) => a.born)
    heq
  change G.trace.1.2.clock + 1 = old.born at hborn
  omega


/-- P.3 public input geometry persists on every literal finite
    scheduler word, without a FIFO hypothesis or a reselected
    source/target pair. This supplies the owner-row OLD guards
    needed by topFreshTailCausalQueueRun. -/
theorem topFreshTailCausalSourcePublicGeometryRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n))
    (j : Fin (topClockSpan n)) :
    ((topFixedTraceRun ring C word).1.1
      (certSite s j.val)).l = false ∧
    ((topFixedTraceRun ring C word).1.1
      (ring.rightNeighbor (certSite s j.val))).l = false ∧
    ((topFixedTraceRun ring C word).1.1
      (certSite s j.val)).beta =
        (if j.val = 0 then true else false) ∧
    ((topFixedTraceRun ring C word).1.1
      (ring.rightNeighbor (certSite s j.val))).beta =
        (if j.val + 1 = topClockSpan n then true else false) := by
  have hreach :
      topClockReached ring C
        (topFixedTraceRun ring C word) := by
    change
      topFixedTraceRun ring C word =
        topFixedTraceRun ring C
          (topFixedTraceRun ring C word).2
    rw [topFreshTailFifoRunWord]
  exact topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad (topFixedTraceRun ring C word)
    hreach j


/-- Under the actual bad complete pair, an interior OLD empty
    output slot cannot perform the spurious E-to-U bootstrap.
    Both its physical qOut and deterministic replay slot remain
    empty on the selected source service. This is the exact
    repair of the interior-marker obstruction.
    Consumer: CQ.slot in topFreshTailCausalQueueStep. -/
theorem topFreshTailCausalBadInteriorEmptyStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (hsite : e = certSite s j.val)
    (hempty : (Z.1.1 e).qOut = .E) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .E ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = none := by
  have hgeometry := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hnotZero : j.val ≠ 0 := by omega
  have hleader :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).l =
        false := by
    rw [hqueue.trace.2, hsite]
    exact hgeometry.1
  have hneighbor :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hqueue.trace.2, hsite]
    exact hgeometry.2.1
  have hmarker :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).beta =
        false := by
    have hsource := hgeometry.2.2.1
    rw [if_neg hnotZero] at hsource
    rw [hqueue.trace.2, hsite]
    exact hsource
  have holdEmpty :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
        .E := by
    rw [hqueue.trace.2]
    exact hempty
  have hstep := topFreshTailCausalNonmarkerEmpty ring C s
    (topFreshTailGenealogy ring C s Z) e j hsite
    hleader hneighbor hmarker holdEmpty
  have htr :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).trace =
        topFixedTraceNext ring C Z e := by
    change topFixedTraceNext ring C
      (topFreshTailGenealogy ring C s Z).trace e = _
    rw [hqueue.trace.2]
  constructor
  · rw [← htr]
    exact hstep.1
  · rw [topFreshTailCausalReplayNext]
    exact hstep.2


/-- At the P.3 source delimiter, an OLD E bootstraps a
    physically unread U with a new birth-time carrier at the
    real audit tick. It does not borrow a label from the
    preceding physical edge. Consumer: CQ.slot and CQ.age
    at the only legal E-to-U marker birth. -/
theorem topFreshTailCausalBadBorderBirthStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hzero : j.val = 0)
    (hsite : e = certSite s j.val)
    (hempty : (Z.1.1 e).qOut = .E) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
      some { origin := .freshBorder (Z.1.2.clock + 1),
             born := Z.1.2.clock + 1 } := by
  have hgeometry := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hleft : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeometry.1
  have hright :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeometry.2.1
  have hmarker : (Z.1.1 e).beta = true := by
    have hh := hgeometry.2.2.1
    rw [if_pos hzero] at hh
    rw [hsite]
    exact hh
  have hphys := topFreshTailFifoMarkerBootstraps
    ring C Z e hleft hright hmarker hempty
  have holdEmpty :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
        .E := by
    rw [hqueue.trace.2]
    exact hempty
  have hbirth := topFreshTailCausalMarkerBirth
    ring C s (topFreshTailGenealogy ring C s Z)
    e j hsite hzero holdEmpty
    (by rw [hqueue.trace.2]; exact hleft)
    (by rw [hqueue.trace.2]; exact hright)
    (by rw [hqueue.trace.2]; exact hmarker)
  refine ⟨hphys, ?_⟩
  rw [topFreshTailCausalReplayNext]
  rw [hqueue.trace.2] at hbirth
  exact hbirth

end L3

namespace L3

/-- Every occupied causal source slot after one actual selected
    service is either the same old carrier at some old source
    slot or a carrier stamped with this service time.
    Consumer: the old/fresh classification in
    topFreshTailCausalQueueIdentityStep. -/
theorem topFreshTailCausalSuccessorOldOrNew
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogyStep ring C s G e).slots j =
        some a) :
    (∃ k : Fin (topClockSpan n), G.slots k = some a) ∨
      a.born = G.trace.1.2.clock + 1 := by
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some a at hnew
  unfold topFreshTailGenealogyNextSlot at hnew
  cases hpost :
      ((topFixedTraceNext ring C G.trace e).1.1
        (certSite s j.val)).qOut with
  | E =>
      simp only [hpost] at hnew
      cases hnew
  | U =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            exact Or.inr rfl
          · cases hnew
      | U =>
          simp only [hold] at hnew
          exact Or.inl ⟨j, hnew⟩
      | D value tail =>
          cases tail with
          | false =>
              simp [hold] at hnew
          | true =>
              cases hslot : G.slots j with
              | none =>
                  simp [hold, hslot] at hnew
              | some parent =>
                  simp [hold, hslot] at hnew
                  cases hnew
                  exact Or.inr rfl
  | D value tail =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · split at hnew
            · exact Or.inl
                ⟨(⟨j.val - 1,
                    show j.val - 1 < topClockSpan n by omega⟩ :
                    Fin (topClockSpan n)), hnew⟩
            · cases hnew
          · cases hnew
      | U =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            exact Or.inr rfl
          · exact Or.inl ⟨j, hnew⟩
      | D oldValue oldTail =>
          simp only [hold] at hnew
          exact Or.inl ⟨j, hnew⟩

theorem topFreshTailCausalMovedParentAbsentAtSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (parent : TopFreshTailCarrier (topClockSpan n))
    (hinside : j.val + 1 < topClockSpan n)
    (hsite : e = certSite s j.val)
    (hsource : (Z.1.1 e).qOut = .D v tail)
    (htarget :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E)
    (hparent :
      (topFreshTailGenealogy ring C s Z).slots j =
        some parent) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j ≠
        some parent ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots
      (⟨j.val + 1,
        show j.val + 1 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n)) = some parent := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have htargetMarker := hgeom.2.2.2
  have htargetNonmarker :
      (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    rw [if_neg (by omega : j.val + 1 ≠ topClockSpan n)]
      at htargetMarker
    rw [hsite]
    exact htargetMarker
  have hsourceG :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).qOut =
        .D v tail := by
    rw [hqueue.trace.2]
    exact hsource
  have htargetG :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).qOut = .E := by
    rw [hqueue.trace.2]
    exact htarget
  have hleftG :
      ((topFreshTailGenealogy ring C s Z).trace.1.1 e).l =
        false := by
    rw [hqueue.trace.2, hsite]
    exact hgeom.1
  have hrightG :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).l = false := by
    rw [hqueue.trace.2, hsite]
    exact hgeom.2.1
  have hbetaG :
      ((topFreshTailGenealogy ring C s Z).trace.1.1
        (ring.rightNeighbor e)).beta = false := by
    rw [hqueue.trace.2]
    exact htargetNonmarker
  have hsourceNew := topFreshTailCausalDataMove
    ring (by omega : 2 ≤ n) C s
    (topFreshTailGenealogy ring C s Z)
    e j v tail parent hsite hsourceG htargetG
    hleftG hrightG hbetaG hparent
  have htargetNew := topFreshTailCausalDataMoveTarget
    ring (by omega : 2 ≤ n) C s
    (topFreshTailGenealogy ring C s Z)
    e j v tail parent hinside hsite
    hsourceG htargetG hleftG hrightG hbetaG hparent
  rw [topFreshTailCausalReplayNext]
  constructor
  · cases tail with
    | false =>
        simp only [Bool.false_eq_true, if_false] at hsourceNew
        rw [hsourceNew]
        intro h
        cases h
    | true =>
        simp only [ite_true] at hsourceNew
        rw [hsourceNew]
        intro heq
        have hdistinct := topFreshTailCausalNewChildDistinct
          (topFreshTailGenealogy ring C s Z) j
          parent parent
          (by rw [hqueue.trace.2]; exact hqueue.age j parent hparent)
        exact hdistinct (Option.some.inj heq)
  · exact htargetNew


theorem topFreshTailCausalSourceSiteInjective
    {n : Nat} (s : Fin n) (hn : 5 ≤ n)
    (i j : Fin (topClockSpan n))
    (hsite : certSite s i.val = certSite s j.val) :
    i = j := by
  have hle : topClockSpan n ≤ n :=
    cert_rho_le_n n hn
  have hi : i.val < n := by
    have hi0 := i.isLt
    omega
  have hj : j.val < n := by
    have hj0 := j.isLt
    omega
  have h := congrArg Fin.val hsite
  change (s.val + i.val) % n =
    (s.val + j.val) % n at h
  have hs := s.isLt
  by_cases hleft : s.val + i.val < n
  · rw [Nat.mod_eq_of_lt hleft] at h
    by_cases hright : s.val + j.val < n
    · rw [Nat.mod_eq_of_lt hright] at h
      apply Fin.ext
      omega
    · have hge : n ≤ s.val + j.val := by omega
      have hrem : s.val + j.val - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt hrem] at h
      omega
  · have hge : n ≤ s.val + i.val := by omega
    have hrem : s.val + i.val - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hrem] at h
    by_cases hright : s.val + j.val < n
    · rw [Nat.mod_eq_of_lt hright] at h
      omega
    · have hge' : n ≤ s.val + j.val := by omega
      have hrem' : s.val + j.val - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge',
        Nat.mod_eq_of_lt hrem'] at h
      apply Fin.ext
      omega


end L3

namespace L3

/-- A carrier with birth time strictly before the selected
    service must be copied from an old occupied slot, never
    invented by a current QO marker/bootstrap/retag branch.
    Consumer: old-carrier portion of CQ.identity. -/
theorem topFreshTailCausalOlderCarrierHasSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogyStep ring C s G e).slots j =
        some a)
    (hold : a.born ≤ G.trace.1.2.clock) :
    ∃ k : Fin (topClockSpan n), G.slots k = some a := by
  rcases topFreshTailCausalSuccessorOldOrNew
    ring C s G e j a hnew with hsource | hfresh
  · exact hsource
  · omega


theorem topFreshTailCausalDSourceOutcomes
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxo : (Z.1.1 e).qOut = .D v tail) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D v tail ∨
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        (if tail then .U else .E) := by
  have howner :
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut =
        .D v tail ∨
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut =
        (if tail then .U else .E) := by
    unfold topPortLiteralTopOwner
    cases hmarker : (Z.1.1 (ring.rightNeighbor e)).beta with
    | false =>
        cases htarget : (Z.1.1 (ring.rightNeighbor e)).qOut with
        | E =>
            exact Or.inr (topPortOwnerQODataMoves
              _ _ _ _ _ v tail hxl hyl hxo htarget hmarker).1
        | U =>
            apply Or.inl
            exact topFreshTailFifoOccupiedOwner
              _ _ _ _ _ v tail hxl hyl hxo hmarker
              (by intro h; rw [htarget] at h; cases h)
        | D w t =>
            apply Or.inl
            exact topFreshTailFifoOccupiedOwner
              _ _ _ _ _ v tail hxl hyl hxo hmarker
              (by intro h; rw [htarget] at h; cases h)
    | true =>
        cases hinput : (Z.1.1 (ring.rightNeighbor e)).qIn with
        | E =>
            cases hcarry :
                (Z.1.1 (ring.rightNeighbor e)).qCarry with
            | OFF =>
                apply Or.inr
                cases hsourceInput : (Z.1.1 e).qIn <;>
                  cases hsourceCarry : (Z.1.1 e).qCarry <;>
                  simp [liveTopPair, hxl, hyl, hxo, hmarker,
                    hinput, hcarry, hsourceInput, hsourceCarry, inT,
                    OutTok.isD, OutTok.isE,
                    InTok.isE, InTok.isP, InTok.isS, InTok.isX,
                    QCarry.isOff, QCarry.isL,
                    topInternal, topTerminal, outV, outT] <;>
                  (try split) <;> (try split) <;> simp
            | L carry err =>
                apply Or.inl
                exact topFreshTailCausalBlockedOwner
                  _ _ _ _ _ v tail hxl hyl hmarker hxo
                  (Or.inr (by simp [hcarry, QCarry.isOff]))
        | P value stamp =>
            apply Or.inl
            exact topFreshTailCausalBlockedOwner
              _ _ _ _ _ v tail hxl hyl hmarker hxo
              (Or.inl (by simp [hinput, InTok.isE]))
        | S value stamp =>
            apply Or.inl
            exact topFreshTailCausalBlockedOwner
              _ _ _ _ _ v tail hxl hyl hmarker hxo
              (Or.inl (by simp [hinput, InTok.isE]))
        | X =>
            apply Or.inl
            exact topFreshTailCausalBlockedOwner
              _ _ _ _ _ v tail hxl hyl hmarker hxo
              (Or.inl (by simp [hinput, InTok.isE]))
  have hsource := (topPortLiteralSourceFields
    ring C Z.1.1 e).2.2
  change
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut at hsource
  rw [hsource]
  exact howner


/-- P.3 source-side CQ.slot. The selected OLD source may be
    E, U or D; a nonmarker E remains empty, a border E
    receives a fresh U, U samples an OLD D, and D either
    remains blocked or departs without losing its genealogical
    carrier before the corresponding rearm/deletion.
    Consumer: selected source arm of
    topFreshTailCausalQueueSlotStep. -/
theorem topFreshTailCausalSourceSlotAgreement
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hsite : e = certSite s j.val) :
    ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .E ↔
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = none := by
  subst e
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hxl : (Z.1.1 (certSite s j.val)).l = false :=
    hgeom.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor (certSite s j.val))).l =
        false := hgeom.2.1
  have hnotEmpty (hNon :
      (Z.1.1 (certSite s j.val)).qOut ≠ .E) :
      ∃ a : TopFreshTailCarrier (topClockSpan n),
        (topFreshTailGenealogy ring C s Z).slots j = some a := by
    cases hslot :
        (topFreshTailGenealogy ring C s Z).slots j with
    | none =>
        have hE := (hqueue.slot j).2 hslot
        exact False.elim (hNon hE)
    | some a =>
        exact ⟨a, rfl⟩
  cases hold : (Z.1.1 (certSite s j.val)).qOut with
  | E =>
      by_cases hzero : j.val = 0
      · have hstep := topFreshTailCausalBadBorderBirthStep
          ring C s hn hbad Z (certSite s j.val) hqueue
          j hzero rfl hold
        rw [hstep.1, hstep.2]
        simp
      · have hpositive : 0 < j.val := by omega
        have hstep := topFreshTailCausalBadInteriorEmptyStep
          ring C s hn hbad Z (certSite s j.val) hqueue
          j hpositive rfl hold
        rw [hstep.1, hstep.2]
        simp
  | U =>
      obtain ⟨a, ha⟩ := hnotEmpty (by
        intro hE
        rw [hold] at hE
        cases hE)
      have hphysical := topFreshTailFifoUnreadSamples
        ring C Z (certSite s j.val) hxl hyl hold
      have hghost :
          (topFreshTailGenealogyStep ring C s
            (topFreshTailGenealogy ring C s Z)
            (certSite s j.val)).slots j ≠ none := by
        by_cases hzero : j.val = 0
        · have hsource :
              ((topFreshTailGenealogy ring C s Z).trace.1.1
                (certSite s j.val)).qOut = .U := by
            rw [hqueue.trace.2]
            exact hold
          have hnext := topFreshTailCausalUnreadBorder
            ring C s (topFreshTailGenealogy ring C s Z)
            (certSite s j.val) j rfl hzero hsource
            (by rw [hqueue.trace.2]; exact hxl)
            (by rw [hqueue.trace.2]; exact hyl)
          rw [hnext]
          intro h
          cases h
        · have hsource :
              ((topFreshTailGenealogy ring C s Z).trace.1.1
                (certSite s j.val)).qOut = .U := by
            rw [hqueue.trace.2]
            exact hold
          have hnext := topFreshTailCausalUnreadInterior
            ring C s (topFreshTailGenealogy ring C s Z)
            (certSite s j.val) j a rfl (by omega)
            hsource
            (by rw [hqueue.trace.2]; exact hxl)
            (by rw [hqueue.trace.2]; exact hyl)
            ha
          rw [hnext]
          intro h
          cases h
      rw [topFreshTailCausalReplayNext, hphysical]
      constructor
      · intro hE
        cases hE
      · intro hE
        exact False.elim (hghost hE)
  | D v tail =>
      obtain ⟨a, ha⟩ := hnotEmpty (by
        intro hE
        rw [hold] at hE
        cases hE)
      have hpossible := topFreshTailCausalDSourceOutcomes
        ring C Z (certSite s j.val) v tail hxl hyl hold
      rw [topFreshTailCausalReplayNext]
      rcases hpossible with hstay | hdeparture
      · rw [hstay]
        change
          OutTok.D v tail = .E ↔
            topFreshTailGenealogyNextSlot ring C s
              (topFreshTailGenealogy ring C s Z)
              (certSite s j.val) j = none
        simp [topFreshTailGenealogyNextSlot,
          hqueue.trace.2, hstay, hold, ha]
      · cases tail with
        | false =>
            rw [hdeparture]
            change
              OutTok.E = .E ↔
                topFreshTailGenealogyNextSlot ring C s
                  (topFreshTailGenealogy ring C s Z)
                  (certSite s j.val) j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hdeparture, hold]
        | true =>
            rw [hdeparture]
            change
              OutTok.U = .E ↔
                topFreshTailGenealogyNextSlot ring C s
                  (topFreshTailGenealogy ring C s Z)
                  (certSite s j.val) j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hdeparture, hold, ha]


theorem topFreshTailCausalResponderOwnerOutput
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool) :
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      (if x.l || y.l then .E
       else if x.qOut.isD && !y.beta && y.qOut.isE then
         .D (outV c x.qOut) (outT x.qOut)
       else y.qOut) := by
  cases hxl : x.l with
  | true =>
      simp [liveTopPair, hxl]
  | false =>
      cases hyl : y.l with
      | true =>
          simp [liveTopPair, hxl, hyl]
      | false =>
          cases hxo : x.qOut with
          | E =>
              simp [liveTopPair, hxl, hyl, hxo,
                OutTok.isD, OutTok.isE, OutTok.isU]
          | U =>
              simp [liveTopPair, hxl, hyl, hxo,
                OutTok.isD, OutTok.isE, OutTok.isU]
          | D value tail =>
              cases hmarker : y.beta with
              | false =>
                  simp [liveTopPair, hxl, hyl, hxo, hmarker,
                    OutTok.isD, OutTok.isE, outV, outT]
              | true =>
                  simp [liveTopPair, hxl, hyl, hxo, hmarker,
                    OutTok.isD, OutTok.isE, outV, outT]


/-- The preceding owner formula transported to the actual
    fixed-public scheduler edge; this includes the OLD leader
    cleanup branch and does not mistake QI or QC assignments
    for a second QO service. Consumer: CQ.slot incoming edges. -/
theorem topFreshTailCausalResponderPhysicalOutput
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    ((topFixedTraceNext ring C Z e).1.1
      (ring.rightNeighbor e)).qOut =
      (if (Z.1.1 e).l ||
          (Z.1.1 (ring.rightNeighbor e)).l then .E
       else if (Z.1.1 e).qOut.isD &&
          !(Z.1.1 (ring.rightNeighbor e)).beta &&
          (Z.1.1 (ring.rightNeighbor e)).qOut.isE then
         .D (outV (compileAdvice (ceilLogTwo n))
           (Z.1.1 e).qOut)
           (outT (Z.1.1 e).qOut)
       else (Z.1.1 (ring.rightNeighbor e)).qOut) := by
  have hfields := (topPortLiteralResponderFields
    ring hn C Z.1.1 e).2.2
  change
    ((topFixedTraceNext ring C Z e).1.1
      (ring.rightNeighbor e)).qOut =
      (topPortLiteralTopOwner ring Z.1.1 e).y.qOut at hfields
  rw [hfields]
  unfold topPortLiteralTopOwner
  exact topFreshTailCausalResponderOwnerOutput
    (compileAdvice (ceilLogTwo n))
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) _ _


/-- The clockwise physical scheduler has one predecessor at
    every site. Consumer: the incoming-responder arm of
    topFreshTailCausalQueueSlotStep. -/
theorem topFreshTailCausalRightNeighborInjective
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (e f : Fin n)
    (heq : ring.rightNeighbor e = ring.rightNeighbor f) :
    e = f := by
  apply Fin.ext
  have hv := congrArg Fin.val heq
  change (e.val + 1) % n = (f.val + 1) % n at hv
  have heBound := e.isLt
  have hfBound := f.isLt
  by_cases heShort : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt heShort] at hv
    by_cases hfShort : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hfShort] at hv
      omega
    · have hfEnd : f.val + 1 = n := by omega
      rw [hfEnd, Nat.mod_self] at hv
      omega
  · have heEnd : e.val + 1 = n := by omega
    rw [heEnd, Nat.mod_self] at hv
    by_cases hfShort : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hfShort] at hv
      omega
    · omega

/-- Every incoming service at a positive source offset comes
    from the immediately preceding source slot. The source
    border (offset zero) is the only incoming exception.
    Consumer: CQ.slot incoming-arc case partition. -/
theorem topFreshTailCausalIncomingPredecessor
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (s : Fin n)
    (j : Fin (topClockSpan n))
    (hj : 0 < j.val) (e : Fin n)
    (hnext :
      ring.rightNeighbor e = certSite s j.val) :
    e = certSite s (j.val - 1) := by
  have hprev :
      ring.rightNeighbor (certSite s (j.val - 1)) =
        certSite s j.val := by
    rw [topFreshTailCausalNeighborSite]
    have hsub : (j.val - 1) + 1 = j.val := by omega
    rw [hsub]
  exact topFreshTailCausalRightNeighborInjective
    ring (by omega : 2 ≤ n) e
    (certSite s (j.val - 1)) (hnext.trans hprev.symm)

/-- Any non-E physical output source slot in a reached CQ has
    exactly some recorded carrier. This is the reusable old-slot
    witness for an incoming D transfer or unchanged responder.
    Consumer: CQ.slot and CQ.identity transport. -/
theorem topFreshTailCausalOccupiedHasCarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hnotE :
      (Z.1.1 (certSite s j.val)).qOut ≠ .E) :
    ∃ a : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots j =
        some a := by
  cases hslot :
      (topFreshTailGenealogy ring C s Z).slots j with
  | none =>
      have hE := (hqueue.slot j).2 hslot
      exact False.elim (hnotE hE)
  | some a =>
      exact ⟨a, rfl⟩


theorem topFreshTailCausalResponderSlotAgreement
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hrespond :
      ring.rightNeighbor e = certSite s j.val) :
    ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .E ↔
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = none := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hphysical := topFreshTailCausalResponderPhysicalOutput
    ring (by omega : 2 ≤ n) C Z e
  rw [hrespond] at hphysical
  by_cases hzero : j.val = 0
  · have hmarker : (Z.1.1 (certSite s j.val)).beta =
        true := by
      have h := hgeom.2.2.1
      rw [if_pos hzero] at h
      exact h
    have hframe :
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut =
        (if (Z.1.1 e).l then .E
         else (Z.1.1 (certSite s j.val)).qOut) := by
      simpa [hgeom.1, hmarker] using hphysical
    cases hroot : (Z.1.1 e).l with
    | true =>
        have hnextEmpty :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s j.val)).qOut = .E := by
          simpa [hroot] using hframe
        rw [topFreshTailCausalReplayNext]
        change
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .E ↔
          topFreshTailGenealogyNextSlot ring C s
            (topFreshTailGenealogy ring C s Z) e j = none
        simp [topFreshTailGenealogyNextSlot,
          hqueue.trace.2, hnextEmpty]
    | false =>
        have hnextFrame :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s j.val)).qOut =
            (Z.1.1 (certSite s j.val)).qOut := by
          simpa [hroot] using hframe
        cases hold : (Z.1.1 (certSite s j.val)).qOut with
        | E =>
            rw [topFreshTailCausalReplayNext]
            change
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E ↔
              topFreshTailGenealogyNextSlot ring C s
                (topFreshTailGenealogy ring C s Z) e j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hnextFrame, hold]
        | U =>
            obtain ⟨a, ha⟩ :=
              topFreshTailCausalOccupiedHasCarrier
                ring C s Z hqueue j (by
                  intro h
                  rw [hold] at h
                  cases h)
            rw [topFreshTailCausalReplayNext]
            change
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E ↔
              topFreshTailGenealogyNextSlot ring C s
                (topFreshTailGenealogy ring C s Z) e j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hnextFrame, hold, ha]
        | D v tail =>
            obtain ⟨a, ha⟩ :=
              topFreshTailCausalOccupiedHasCarrier
                ring C s Z hqueue j (by
                  intro h
                  rw [hold] at h
                  cases h)
            rw [topFreshTailCausalReplayNext]
            change
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E ↔
              topFreshTailGenealogyNextSlot ring C s
                (topFreshTailGenealogy ring C s Z) e j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hnextFrame, hold, ha]
  · have hpositive : 0 < j.val := by omega
    have hpred := topFreshTailCausalIncomingPredecessor
      ring hn s j hpositive e hrespond
    have hpreGeometry := topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z hqueue.trace.1
      (⟨j.val - 1,
        show j.val - 1 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n))
    have hleft : (Z.1.1 e).l = false := by
      rw [hpred]
      exact hpreGeometry.1
    have hright : (Z.1.1 (certSite s j.val)).l = false :=
      hgeom.1
    have hnonmark :
        (Z.1.1 (certSite s j.val)).beta = false := by
      have h := hgeom.2.2.1
      rw [if_neg hzero] at h
      exact h
    have howner :
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut =
          (if (Z.1.1 e).qOut.isD &&
               (Z.1.1 (certSite s j.val)).qOut.isE then
             .D (outV (compileAdvice (ceilLogTwo n))
               (Z.1.1 e).qOut)
               (outT (Z.1.1 e).qOut)
           else (Z.1.1 (certSite s j.val)).qOut) := by
      simpa [hleft, hright, hnonmark] using hphysical
    cases hold : (Z.1.1 (certSite s j.val)).qOut with
    | E =>
        cases hsource : (Z.1.1 e).qOut with
        | E =>
            have hnextE :
                ((topFixedTraceNext ring C Z e).1.1
                  (certSite s j.val)).qOut = .E := by
              simpa [hsource, hold, OutTok.isD,
                OutTok.isE] using howner
            rw [topFreshTailCausalReplayNext]
            change
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E ↔
              topFreshTailGenealogyNextSlot ring C s
                (topFreshTailGenealogy ring C s Z) e j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hnextE]
        | U =>
            have hnextE :
                ((topFixedTraceNext ring C Z e).1.1
                  (certSite s j.val)).qOut = .E := by
              simpa [hsource, hold, OutTok.isD,
                OutTok.isE] using howner
            rw [topFreshTailCausalReplayNext]
            change
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E ↔
              topFreshTailGenealogyNextSlot ring C s
                (topFreshTailGenealogy ring C s Z) e j = none
            simp [topFreshTailGenealogyNextSlot,
              hqueue.trace.2, hnextE]
        | D v tail =>
            have hnextD :
                ((topFixedTraceNext ring C Z e).1.1
                  (certSite s j.val)).qOut =
                    .D v tail := by
              simpa [hsource, hold, OutTok.isD,
                OutTok.isE, outV, outT] using howner
            have hpreNotE :
                (Z.1.1 (certSite s (j.val - 1))).qOut ≠
                  .E := by
              rw [← hpred, hsource]
              intro h
              cases h
            obtain ⟨a, ha⟩ :=
              topFreshTailCausalOccupiedHasCarrier
                ring C s Z hqueue
                (⟨j.val - 1,
                  show j.val - 1 < topClockSpan n by omega⟩ :
                  Fin (topClockSpan n))
                hpreNotE
            have hnewSlot :
                topFreshTailGenealogyNextSlot ring C s
                  (topFreshTailGenealogy ring C s Z) e j =
                  some a := by
              unfold topFreshTailGenealogyNextSlot
              rw [hqueue.trace.2]
              simp only [hnextD, hold, dif_pos hpositive,
                if_pos hpred, ha]
            rw [topFreshTailCausalReplayNext]
            change
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E ↔
              topFreshTailGenealogyNextSlot ring C s
                (topFreshTailGenealogy ring C s Z) e j = none
            rw [hnextD, hnewSlot]
            simp

    | U =>
        have hnextU :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s j.val)).qOut = .U := by
          simpa [hold, OutTok.isE] using howner
        obtain ⟨a, ha⟩ :=
          topFreshTailCausalOccupiedHasCarrier
            ring C s Z hqueue j (by
              intro h
              rw [hold] at h
              cases h)
        rw [topFreshTailCausalReplayNext]
        change
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .E ↔
          topFreshTailGenealogyNextSlot ring C s
            (topFreshTailGenealogy ring C s Z) e j = none
        simp [topFreshTailGenealogyNextSlot,
          hqueue.trace.2, hnextU, hold, ha]
    | D v tail =>
        have hnextD :
            ((topFixedTraceNext ring C Z e).1.1
              (certSite s j.val)).qOut = .D v tail := by
          simpa [hold, OutTok.isE] using howner
        obtain ⟨a, ha⟩ :=
          topFreshTailCausalOccupiedHasCarrier
            ring C s Z hqueue j (by
              intro h
              rw [hold] at h
              cases h)
        rw [topFreshTailCausalReplayNext]
        change
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .E ↔
          topFreshTailGenealogyNextSlot ring C s
            (topFreshTailGenealogy ring C s Z) e j = none
        simp [topFreshTailGenealogyNextSlot,
          hqueue.trace.2, hnextD, hold, ha]


/-- A source output slot untouched by both endpoints of the
    selected real physical pair keeps its OLD qOut and the
    very same causal carrier option. In particular OLD E
    stays paired with none, without inventing a fresh slot.
    Consumer: off-pair arm of topFreshTailCausalQueueSlotStep. -/
theorem topFreshTailCausalOffPairSlotAgreement
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hsource : certSite s j.val ≠ e)
    (htarget :
      certSite s j.val ≠ ring.rightNeighbor e) :
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s j.val)).qOut =
        (Z.1.1 (certSite s j.val)).qOut ∧
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j =
        (topFreshTailGenealogy ring C s Z).slots j := by
  have hframe := (topPortLiteralAwayFields
    ring C Z.1.1 e (certSite s j.val) hsource htarget).2.2
  change
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s j.val)).qOut =
        (Z.1.1 (certSite s j.val)).qOut at hframe
  constructor
  · exact hframe
  · cases hold : (Z.1.1 (certSite s j.val)).qOut with
    | E =>
        have hnone := (hqueue.slot j).1 hold
        rw [topFreshTailCausalReplayNext]
        change
          topFreshTailGenealogyNextSlot ring C s
            (topFreshTailGenealogy ring C s Z) e j =
              (topFreshTailGenealogy ring C s Z).slots j
        rw [hnone]
        simp [topFreshTailGenealogyNextSlot,
          hqueue.trace.2, hframe, hold]
    | U =>
        obtain ⟨a, ha⟩ :=
          topFreshTailCausalOccupiedHasCarrier
            ring C s Z hqueue j (by
              intro h
              rw [hold] at h
              cases h)
        have hoccupied :
            ((topFreshTailGenealogy ring C s Z).trace.1.1
              (certSite s j.val)).qOut ≠ .E := by
          rw [hqueue.trace.2, hold]
          intro h
          cases h
        have hkeep := topFreshTailCausalOffPairFrame
          ring C s (topFreshTailGenealogy ring C s Z)
          e j a hsource htarget hoccupied ha
        rw [topFreshTailCausalReplayNext]
        rw [hkeep, ha]
    | D v tail =>
        obtain ⟨a, ha⟩ :=
          topFreshTailCausalOccupiedHasCarrier
            ring C s Z hqueue j (by
              intro h
              rw [hold] at h
              cases h)
        have hoccupied :
            ((topFreshTailGenealogy ring C s Z).trace.1.1
              (certSite s j.val)).qOut ≠ .E := by
          rw [hqueue.trace.2, hold]
          intro h
          cases h
        have hkeep := topFreshTailCausalOffPairFrame
          ring C s (topFreshTailGenealogy ring C s Z)
          e j a hsource htarget hoccupied ha
        rw [topFreshTailCausalReplayNext]
        rw [hkeep, ha]

/-- Q7c P.3 CQ.slot closed under EVERY literal selected pair.
    Each source offset is either the initiator, the responder,
    or outside both endpoints. The responder case includes
    marker-border incoming cleanup, interior D receipt from
    the preceding slot, and the last source-to-port edge.
    All output classifications use the OLD QO pair before
    the simultaneous QI/QC writes. -/
theorem topFreshTailCausalQueueSlotStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z) :
    ∀ j : Fin (topClockSpan n),
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut = .E ↔
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = none := by
  intro j
  by_cases hsource : certSite s j.val = e
  · exact topFreshTailCausalSourceSlotAgreement
      ring C s hn hbad Z e hqueue j hsource.symm
  · by_cases htarget :
        certSite s j.val = ring.rightNeighbor e
    · exact topFreshTailCausalResponderSlotAgreement
        ring C s hn hbad Z e hqueue j htarget.symm
    · have hframe := topFreshTailCausalOffPairSlotAgreement
        ring C s Z e hqueue j hsource htarget
      rw [hframe.1, hframe.2]
      exact hqueue.slot j


theorem topFreshTailCausalOlderCarrierPlacement
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogyStep ring C s G e).slots j =
        some a)
    (hborn : a.born ≤ G.trace.1.2.clock) :
    G.slots j = some a ∨
      (0 < j.val ∧
        e = certSite s (j.val - 1) ∧
        G.slots
          (⟨j.val - 1,
            show j.val - 1 < topClockSpan n by omega⟩ :
            Fin (topClockSpan n)) = some a) := by
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some a at hnew
  unfold topFreshTailGenealogyNextSlot at hnew
  cases hpost :
      ((topFixedTraceNext ring C G.trace e).1.1
        (certSite s j.val)).qOut with
  | E =>
      simp only [hpost] at hnew
      cases hnew
  | U =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            dsimp only [topFreshTailGenealogyRearm] at hborn
            omega
          · cases hnew
      | U =>
          simp only [hold] at hnew
          exact Or.inl hnew
      | D value tail =>
          cases tail with
          | false =>
              simp [hold] at hnew
          | true =>
              cases hslot : G.slots j with
              | none =>
                  simp [hold, hslot] at hnew
              | some parent =>
                  simp [hold, hslot] at hnew
                  cases hnew
                  dsimp only [topFreshTailGenealogyRearm] at hborn
                  omega
  | D value tail =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · split at hnew
            · exact Or.inr ⟨by assumption, by assumption, hnew⟩
            · cases hnew
          · cases hnew
      | U =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            dsimp only [topFreshTailGenealogyRearm] at hborn
            omega
          · exact Or.inl hnew
      | D oldValue oldTail =>
          simp only [hold] at hnew
          exact Or.inl hnew


/-- An incoming edge to the fixed source-border marker never
    creates a new carrier identity in that responder slot.
    It either preserves the OLD carrier or deletes it when
    the outside initiator is a leader. Consumer: fresh-birth
    uniqueness in CQ.identity. -/
theorem topFreshTailCausalBorderIncomingOldCarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hzero : j.val = 0)
    (hincoming :
      ring.rightNeighbor e = certSite s j.val)
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a) :
    (topFreshTailGenealogy ring C s Z).slots j = some a := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hmark :
      (Z.1.1 (certSite s j.val)).beta = true := by
    have h := hgeom.2.2.1
    rw [if_pos hzero] at h
    exact h
  have hphys := topFreshTailCausalResponderPhysicalOutput
    ring (by omega : 2 ≤ n) C Z e
  rw [hincoming] at hphys
  have hframe :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
        (if (Z.1.1 e).l then .E
         else (Z.1.1 (certSite s j.val)).qOut) := by
    simpa [hgeom.1, hmark] using hphys
  rw [topFreshTailCausalReplayNext] at hnew
  change topFreshTailGenealogyNextSlot ring C s
    (topFreshTailGenealogy ring C s Z) e j = some a at hnew
  cases hleader : (Z.1.1 e).l with
  | true =>
      have hpostE :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .E := by
        simpa [hleader] using hframe
      simp [topFreshTailGenealogyNextSlot,
        hqueue.trace.2, hpostE] at hnew
  | false =>
      have hpostFrame :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut =
          (Z.1.1 (certSite s j.val)).qOut := by
        simpa [hleader] using hframe
      cases hold : (Z.1.1 (certSite s j.val)).qOut with
      | E =>
          simp [topFreshTailGenealogyNextSlot,
            hqueue.trace.2, hpostFrame, hold] at hnew
      | U =>
          simpa [topFreshTailGenealogyNextSlot,
            hqueue.trace.2, hpostFrame, hold] using hnew
      | D v tail =>
          simpa [topFreshTailGenealogyNextSlot,
            hqueue.trace.2, hpostFrame, hold] using hnew


theorem topFreshTailCausalInteriorIncomingOldCarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hpositive : 0 < j.val)
    (hincoming :
      ring.rightNeighbor e = certSite s j.val)
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a) :
    ∃ k : Fin (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots k =
        some a := by
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hpred := topFreshTailCausalIncomingPredecessor
    ring hn s j hpositive e hincoming
  have hprevGeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1
    (⟨j.val - 1,
      show j.val - 1 < topClockSpan n by omega⟩ :
      Fin (topClockSpan n))
  have hleft : (Z.1.1 e).l = false := by
    rw [hpred]
    exact hprevGeom.1
  have hnonmarker :
      (Z.1.1 (certSite s j.val)).beta = false := by
    have h := hgeom.2.2.1
    rw [if_neg (by omega : j.val ≠ 0)] at h
    exact h
  have hphys := topFreshTailCausalResponderPhysicalOutput
    ring (by omega : 2 ≤ n) C Z e
  rw [hincoming] at hphys
  have houtput :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s j.val)).qOut =
      (if (Z.1.1 e).qOut.isD &&
           (Z.1.1 (certSite s j.val)).qOut.isE then
         .D (outV (compileAdvice (ceilLogTwo n))
           (Z.1.1 e).qOut)
           (outT (Z.1.1 e).qOut)
       else (Z.1.1 (certSite s j.val)).qOut) := by
    simpa [hleft, hgeom.1, hnonmarker] using hphys
  rw [topFreshTailCausalReplayNext] at hnew
  change topFreshTailGenealogyNextSlot ring C s
    (topFreshTailGenealogy ring C s Z) e j = some a at hnew
  cases hold : (Z.1.1 (certSite s j.val)).qOut with
  | E =>
      cases hsource : (Z.1.1 e).qOut with
      | E =>
          have hpostE :
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E := by
            simpa [hsource, hold,
              OutTok.isD, OutTok.isE] using houtput
          simp [topFreshTailGenealogyNextSlot,
            hqueue.trace.2, hpostE] at hnew
      | U =>
          have hpostE :
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .E := by
            simpa [hsource, hold,
              OutTok.isD, OutTok.isE] using houtput
          simp [topFreshTailGenealogyNextSlot,
            hqueue.trace.2, hpostE] at hnew
      | D v tail =>
          have hpostD :
              ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut =
                .D v tail := by
            simpa [hsource, hold, OutTok.isD,
              OutTok.isE, outV, outT] using houtput
          unfold topFreshTailGenealogyNextSlot at hnew
          rw [hqueue.trace.2] at hnew
          simp only [hpostD, hold, dif_pos hpositive,
            if_pos hpred] at hnew
          exact
            ⟨(⟨j.val - 1,
                show j.val - 1 < topClockSpan n by omega⟩ :
                Fin (topClockSpan n)), hnew⟩
  | U =>
      have hpostU :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .U := by
        simpa [hold, OutTok.isE] using houtput
      simp [topFreshTailGenealogyNextSlot,
        hqueue.trace.2, hpostU, hold,
        (show j.val ≠ 0 by omega)] at hnew
      exact ⟨j, hnew⟩
  | D v tail =>
      have hpostD :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .D v tail := by
        simpa [hold, OutTok.isE] using houtput
      simp [topFreshTailGenealogyNextSlot,
        hqueue.trace.2, hpostD, hold] at hnew
      exact ⟨j, hnew⟩


/-- No responder in the P.3 source array is a fresh birthplace:
    every surviving responder carrier is inherited from some
    OLD source-array slot, including incoming leader cleanup
    at the source marker. Consumer: CQ.identity transport. -/
theorem topFreshTailCausalResponderCarrierOld
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (hincoming :
      ring.rightNeighbor e = certSite s j.val)
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a) :
    ∃ k : Fin (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots k =
        some a := by
  by_cases hzero : j.val = 0
  · exact ⟨j,
      topFreshTailCausalBorderIncomingOldCarrier
        ring C s hn hbad Z e hqueue j hzero
        hincoming a hnew⟩
  · exact topFreshTailCausalInteriorIncomingOldCarrier
      ring C s hn hbad Z e hqueue j
      (by omega) hincoming a hnew


/-- Every newly born carrier in the P.3 source array must
    occupy the selected INITIATOR's source slot. An incoming
    responder cannot create one (including at the border),
    and an off-pair site only retains its old age. This is
    the one-birthplace component of CQ.identity. -/
theorem topFreshTailCausalFreshBirthAtSelectedSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a)
    (hfresh : a.born = Z.1.2.clock + 1) :
    certSite s j.val = e := by
  by_cases hsource : certSite s j.val = e
  · exact hsource
  · by_cases htarget :
        certSite s j.val = ring.rightNeighbor e
    · obtain ⟨k, hold⟩ :=
        topFreshTailCausalResponderCarrierOld
          ring C s hn hbad Z e hqueue j htarget.symm
          a hnew
      have hbound := hqueue.age k a hold
      omega
    · have hremote := topFreshTailCausalOffPairSlotAgreement
        ring C s Z e hqueue j hsource htarget
      have hold :
          (topFreshTailGenealogy ring C s Z).slots j =
            some a := by
        rw [hremote.2] at hnew
        exact hnew
      have hbound := hqueue.age j a hold
      omega


/-- CQ.identity is closed in the genuinely NEW-birth branch:
    two successor slots with the same freshly stamped carrier
    identity must both be the unique selected source site.
    Consumer: fresh half of topFreshTailCausalQueueIdentityStep. -/
theorem topFreshTailCausalFreshIdentityStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (i j : Fin (topClockSpan n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (hi :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots i = some a)
    (hj :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some b)
    (horigin : a.origin = b.origin)
    (hborn : a.born = b.born)
    (hfresh : a.born = Z.1.2.clock + 1) :
    i = j := by
  have hiSite := topFreshTailCausalFreshBirthAtSelectedSource
    ring C s hn hbad Z e hqueue i a hi hfresh
  have hjSite := topFreshTailCausalFreshBirthAtSelectedSource
    ring C s hn hbad Z e hqueue j b hj
      (hborn.symm.trans hfresh)
  exact topFreshTailCausalSourceSiteInjective s hn i j
    (hiSite.trans hjSite.symm)

end L3

namespace L3

/-- Refines the old-carrier placement alternative with the OLD
    empty-target condition. Consumer: CQ.identity, in the
    changed-slot case. -/
theorem topFreshTailCausalOlderCarrierPlacementExact
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew :
      (topFreshTailGenealogyStep ring C s G e).slots j =
        some a)
    (hborn : a.born ≤ G.trace.1.2.clock) :
    G.slots j = some a ∨
      (0 < j.val ∧
        e = certSite s (j.val - 1) ∧
        G.slots
          (⟨j.val - 1,
            show j.val - 1 < topClockSpan n by omega⟩ :
            Fin (topClockSpan n)) = some a ∧
        (G.trace.1.1 (certSite s j.val)).qOut = .E) := by
  change topFreshTailGenealogyNextSlot ring C s G e j =
    some a at hnew
  unfold topFreshTailGenealogyNextSlot at hnew
  cases hpost :
      ((topFixedTraceNext ring C G.trace e).1.1
        (certSite s j.val)).qOut with
  | E =>
      simp only [hpost] at hnew
      cases hnew
  | U =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            dsimp only [topFreshTailGenealogyRearm] at hborn
            omega
          · cases hnew
      | U =>
          simp only [hold] at hnew
          exact Or.inl hnew
      | D value tail =>
          cases tail with
          | false =>
              simp [hold] at hnew
          | true =>
              cases hslot : G.slots j with
              | none =>
                  simp [hold, hslot] at hnew
              | some parent =>
                  simp [hold, hslot] at hnew
                  cases hnew
                  dsimp only [topFreshTailGenealogyRearm] at hborn
                  omega
  | D value tail =>
      simp only [hpost] at hnew
      cases hold : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hold] at hnew
          split at hnew
          · split at hnew
            · exact Or.inr
                ⟨by assumption, by assumption, hnew, rfl⟩
            · cases hnew
          · cases hnew
      | U =>
          simp only [hold] at hnew
          split at hnew
          · cases hnew
            dsimp only [topFreshTailGenealogyRearm] at hborn
            omega
          · exact Or.inl hnew
      | D oldValue oldTail =>
          simp only [hold] at hnew
          exact Or.inl hnew

/-- An OLD-empty interior responder which acquires an existing
    causal carrier must have received a D from the selected
    physical initiator. Consumer: CQ.identity source removal. -/
theorem topFreshTailCausalInteriorArrivalSourceToken
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hpositive : 0 < j.val)
    (hsite : e = certSite s (j.val - 1))
    (htarget :
      (Z.1.1 (certSite s j.val)).qOut = .E)
    (hnew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a) :
    ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA)
      (tail : Bool), (Z.1.1 e).qOut = .D v tail := by
  have hnext :
      ring.rightNeighbor e = certSite s j.val := by
    rw [hsite, topFreshTailCausalNeighborSite]
    have hsub : (j.val - 1) + 1 = j.val := by omega
    rw [hsub]
  have hgeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1 j
  have hprevGeom := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hqueue.trace.1
    (⟨j.val - 1,
      show j.val - 1 < topClockSpan n by omega⟩ :
      Fin (topClockSpan n))
  have hleft : (Z.1.1 e).l = false := by
    rw [hsite]
    simpa only [Fin.val_mk] using hprevGeom.1
  have hright :
      (Z.1.1 (certSite s j.val)).l = false := hgeom.1
  have hbeta :
      (Z.1.1 (certSite s j.val)).beta = false := by
    have h := hgeom.2.2.1
    rw [if_neg (show j.val ≠ 0 by omega)] at h
    exact h
  have hnewSlot :
      topFreshTailGenealogyNextSlot ring C s
        (topFreshTailGenealogy ring C s Z) e j = some a := by
    rw [topFreshTailCausalReplayNext] at hnew
    exact hnew
  unfold topFreshTailGenealogyNextSlot at hnewSlot
  rw [hqueue.trace.2] at hnewSlot
  have hpostD :
      ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA)
        (tail : Bool),
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut = .D v tail := by
    cases hpost :
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s j.val)).qOut with
    | E =>
        simp only [hpost] at hnewSlot
        cases hnewSlot
    | U =>
        simp only [hpost, htarget,
          if_neg (show j.val ≠ 0 by omega)] at hnewSlot
        cases hnewSlot
    | D v tail =>
        exact ⟨v, tail, rfl⟩
  have hphys := topFreshTailCausalResponderPhysicalOutput
    ring (by omega : 2 ≤ n) C Z e
  rw [hnext] at hphys
  rcases hpostD with ⟨v, tail, hpostD⟩
  cases hsource : (Z.1.1 e).qOut with
  | E =>
      have hpostE :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .E := by
        simpa [hleft, hright, hbeta, htarget, hsource,
          OutTok.isD, OutTok.isE] using hphys
      rw [hpostE] at hpostD
      cases hpostD
  | U =>
      have hpostE :
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s j.val)).qOut = .E := by
        simpa [hleft, hright, hbeta, htarget, hsource,
          OutTok.isD, OutTok.isE] using hphys
      rw [hpostE] at hpostD
      cases hpostD
  | D value stamp =>
      exact ⟨value, stamp, rfl⟩

/-- A genuinely moved OLD carrier cannot simultaneously remain
    at its OLD predecessor. Consumer: old/old CQ.identity. -/
theorem topFreshTailCausalOlderMoveConsumesSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hpositive : 0 < j.val)
    (hsite : e = certSite s (j.val - 1))
    (hparent :
      (topFreshTailGenealogy ring C s Z).slots
        (⟨j.val - 1,
          show j.val - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)) = some a)
    (htarget :
      (Z.1.1 (certSite s j.val)).qOut = .E)
    (hnew :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some a) :
    (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots
        (⟨j.val - 1,
          show j.val - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)) ≠ some a := by
  obtain ⟨v, tail, hsource⟩ :=
    topFreshTailCausalInteriorArrivalSourceToken
      ring C s hn hbad Z e hqueue j a
      hpositive hsite htarget hnew
  have hnext :
      ring.rightNeighbor e = certSite s j.val := by
    rw [hsite, topFreshTailCausalNeighborSite]
    have hsub : (j.val - 1) + 1 = j.val := by omega
    rw [hsub]
  have htargetSource :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E := by
    rw [hnext]
    exact htarget
  have habsent := (topFreshTailCausalMovedParentAbsentAtSource
    ring C s hn hbad Z hqueue e
    (⟨j.val - 1,
      show j.val - 1 < topClockSpan n by omega⟩ :
      Fin (topClockSpan n))
    v tail a
    (by simpa only [Fin.val_mk] using
      (show (j.val - 1) + 1 < topClockSpan n by omega))
    (by simpa only [Fin.val_mk] using hsite)
    hsource htargetSource hparent).1
  exact habsent

/-- The identity part of CQ is preserved at one actual
    scheduler service. New identities are confined to the
    selected source; OLD moves remove the predecessor label.
    Consumer: topFreshTailCausalQueueStep.identity. -/
theorem topFreshTailCausalQueueIdentityStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z) :
    ∀ (i j : Fin (topClockSpan n))
      (a b : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots i = some a →
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some b →
      a.origin = b.origin → a.born = b.born → i = j := by
  intro i j a b hi hj horigin hborn
  have hab : a = b := by
    cases a with
    | mk originA bornA =>
        cases b with
        | mk originB bornB =>
            cases horigin
            cases hborn
            rfl
  subst b
  by_cases hfresh : a.born = Z.1.2.clock + 1
  · exact topFreshTailCausalFreshIdentityStep
      ring C s hn hbad Z e hqueue i j a a
      hi hj rfl rfl hfresh
  · have hnextAge :=
      topFreshTailCausalQueueAgeStep
        ring C s Z e hqueue i a hi
    have hbornOld : a.born ≤ Z.1.2.clock := by
      change a.born ≤ Z.1.2.clock + 1 at hnextAge
      omega
    have hbornG :
        a.born ≤
          (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
      rw [hqueue.trace.2]
      exact hbornOld
    have hstepI :
        (topFreshTailGenealogyStep ring C s
          (topFreshTailGenealogy ring C s Z) e).slots i =
            some a := by
      rw [topFreshTailCausalReplayNext] at hi
      exact hi
    have hstepJ :
        (topFreshTailGenealogyStep ring C s
          (topFreshTailGenealogy ring C s Z) e).slots j =
            some a := by
      rw [topFreshTailCausalReplayNext] at hj
      exact hj
    rcases topFreshTailCausalOlderCarrierPlacementExact
      ring C s (topFreshTailGenealogy ring C s Z)
      e i a hstepI hbornG with
      hstayI | ⟨hpositiveI, hsiteI, hparentI, htargetI⟩
    · rcases topFreshTailCausalOlderCarrierPlacementExact
        ring C s (topFreshTailGenealogy ring C s Z)
        e j a hstepJ hbornG with
        hstayJ | ⟨hpositiveJ, hsiteJ, hparentJ, htargetJ⟩
      · exact hqueue.identity i j a a hstayI hstayJ rfl rfl
      · have hindex :
            i =
              (⟨j.val - 1,
                show j.val - 1 < topClockSpan n by omega⟩ :
                Fin (topClockSpan n)) :=
          hqueue.identity i
            (⟨j.val - 1,
              show j.val - 1 < topClockSpan n by omega⟩ :
              Fin (topClockSpan n))
            a a hstayI hparentJ rfl rfl
        have hconsumed := topFreshTailCausalOlderMoveConsumesSource
          ring C s hn hbad Z e hqueue j a
          hpositiveJ hsiteJ hparentJ (by rw [hqueue.trace.2] at htargetJ; exact htargetJ) hj
        apply False.elim
        apply hconsumed
        rw [← hindex]
        exact hi
    · rcases topFreshTailCausalOlderCarrierPlacementExact
        ring C s (topFreshTailGenealogy ring C s Z)
        e j a hstepJ hbornG with
        hstayJ | ⟨hpositiveJ, hsiteJ, hparentJ, htargetJ⟩
      · have hindex :
            j =
              (⟨i.val - 1,
                show i.val - 1 < topClockSpan n by omega⟩ :
                Fin (topClockSpan n)) :=
          hqueue.identity j
            (⟨i.val - 1,
              show i.val - 1 < topClockSpan n by omega⟩ :
              Fin (topClockSpan n))
            a a hstayJ hparentI rfl rfl
        have hconsumed := topFreshTailCausalOlderMoveConsumesSource
          ring C s hn hbad Z e hqueue i a
          hpositiveI hsiteI hparentI (by rw [hqueue.trace.2] at htargetI; exact htargetI) hi
        apply False.elim
        apply hconsumed
        rw [← hindex]
        exact hj
      · have hindex :
            (⟨i.val - 1,
              show i.val - 1 < topClockSpan n by omega⟩ :
              Fin (topClockSpan n)) =
            (⟨j.val - 1,
              show j.val - 1 < topClockSpan n by omega⟩ :
              Fin (topClockSpan n)) :=
          hqueue.identity
            (⟨i.val - 1,
              show i.val - 1 < topClockSpan n by omega⟩ :
              Fin (topClockSpan n))
            (⟨j.val - 1,
              show j.val - 1 < topClockSpan n by omega⟩ :
              Fin (topClockSpan n))
            a a hparentI hparentJ rfl rfl
        apply Fin.ext
        have hv := congrArg Fin.val hindex
        simp only [Fin.val_mk] at hv
        omega

/-- Two pre-existing causal identities that both persist
    cannot reverse their order in one physical scheduler step.
    Consumer: the historical-edge half of CQ.nonpass. -/
theorem topFreshTailCausalPersistentOrderStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (hage :
      ∀ (k : Fin (topClockSpan n))
        (a : TopFreshTailCarrier (topClockSpan n)),
        G.slots k = some a →
        a.born ≤ G.trace.1.2.clock)
    (hidentity :
      ∀ (i j : Fin (topClockSpan n))
        (a b : TopFreshTailCarrier (topClockSpan n)),
        G.slots i = some a →
        G.slots j = some b →
        a.origin = b.origin → a.born = b.born → i = j)
    (i j movedI movedJ : Fin (topClockSpan n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (hi : G.slots i = some a)
    (hj : G.slots j = some b)
    (hnewI :
      (topFreshTailGenealogyStep ring C s G e).slots movedI =
        some a)
    (hnewJ :
      (topFreshTailGenealogyStep ring C s G e).slots movedJ =
        some b)
    (hbefore : i.val < j.val) :
    movedI.val < movedJ.val := by
  have hplaceI := topFreshTailCausalOlderCarrierPlacement
    ring C s G e movedI a hnewI (hage i a hi)
  have hplaceJ := topFreshTailCausalOlderCarrierPlacement
    ring C s G e movedJ b hnewJ (hage j b hj)
  have hdifferent : movedI.val ≠ movedJ.val := by
    intro hequal
    have hindex : movedI = movedJ := Fin.ext hequal
    rw [hindex] at hnewI
    have hab : a = b :=
      Option.some.inj (hnewI.symm.trans hnewJ)
    have holdIndex :=
      hidentity i j a b hi hj
        (congrArg
          (fun z : TopFreshTailCarrier (topClockSpan n) => z.origin)
          hab)
        (congrArg
          (fun z : TopFreshTailCarrier (topClockSpan n) => z.born)
          hab)
    have hval := congrArg Fin.val holdIndex
    omega
  have hboundI :
      i.val ≤ movedI.val ∧ movedI.val ≤ i.val + 1 := by
    rcases hplaceI with hstay | ⟨hpositive, hsite, hprev⟩
    · have heq :=
        hidentity i movedI a a hi hstay rfl rfl
      have hv := congrArg Fin.val heq
      omega
    · have heq :=
        hidentity i
          (⟨movedI.val - 1,
            show movedI.val - 1 < topClockSpan n by omega⟩ :
            Fin (topClockSpan n))
          a a hi hprev rfl rfl
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
  have hboundJ :
      j.val ≤ movedJ.val ∧ movedJ.val ≤ j.val + 1 := by
    rcases hplaceJ with hstay | ⟨hpositive, hsite, hprev⟩
    · have heq :=
        hidentity j movedJ b b hj hstay rfl rfl
      have hv := congrArg Fin.val heq
      omega
    · have heq :=
        hidentity j
          (⟨movedJ.val - 1,
            show movedJ.val - 1 < topClockSpan n by omega⟩ :
            Fin (topClockSpan n))
          b b hj hprev rfl rfl
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
  omega

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A selected old-state service creates a parent/child edge in
exactly one of the two literal genealogy rows: true-tail rearm
or border U-to-true-D sample. Consumer: causal ParentAppend. -/
def TopFreshTailCausalServiceParent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (parent child : TopFreshTailCarrier (topClockSpan n)) : Prop :=
  (∃ (j : Fin (topClockSpan n))
      (v : Fin (compileAdvice (ceilLogTwo n)).topA),
      e = certSite s j.val ∧
      ((topFreshTailGenealogyReplay ring C s word).trace.1.1 e).qOut =
        .D v true ∧
      (topFreshTailGenealogyReplay ring C s word).slots j =
        some parent ∧
      ((topFixedTraceNext ring C
        (topFreshTailGenealogyReplay ring C s word).trace e).1.1 e).qOut =
        .U ∧
      child =
        topFreshTailGenealogyRearm j
          ((topFreshTailGenealogyReplay ring C s word).trace.1.2.clock + 1)
          parent) ∨
  (∃ (j : Fin (topClockSpan n))
      (v : Fin (compileAdvice (ceilLogTwo n)).topA),
      j.val = 0 ∧
      e = certSite s j.val ∧
      ((topFreshTailGenealogyReplay ring C s word).trace.1.1 e).qOut =
        .U ∧
      (topFreshTailGenealogyReplay ring C s word).slots j =
        some parent ∧
      ((topFixedTraceNext ring C
        (topFreshTailGenealogyReplay ring C s word).trace e).1.1 e).qOut =
        .D v true ∧
      child = {
        origin := .freshBorder
          ((topFreshTailGenealogyReplay ring C s word).trace.1.2.clock + 1),
        born :=
          (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock + 1 })

/-- An occurrence in a scheduler word with one appended service
was either already present in the old word or is exactly its
last occurrence. Consumer: both genealogy event constructors. -/
private theorem topFreshTailCausalOccurrenceSnoc
    {α : Type} (word pre suffix : List α)
    (edge e : α)
    (hword : pre ++ edge :: suffix = word ++ [e]) :
    (∃ middle : List α,
      suffix = middle ++ [e] ∧
      pre ++ edge :: middle = word) ∨
    (pre = word ∧ edge = e ∧ suffix = []) := by
  induction word generalizing pre with
  | nil =>
      cases pre with
      | nil =>
          cases suffix with
          | nil =>
              have he : edge = e := by simpa using hword
              exact Or.inr ⟨rfl, he, rfl⟩
          | cons a rest =>
              have hlength := congrArg List.length hword
              simp only [List.length_append, List.length_cons,
                List.length_nil] at hlength
              omega
      | cons a rest =>
          have hlength := congrArg List.length hword
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hlength
          omega
  | cons first rest ih =>
      cases pre with
      | nil =>
          have hpair :
              edge = first ∧ suffix = rest ++ [e] := by
            exact List.cons.inj hword
          refine Or.inl ⟨rest, hpair.2, ?_⟩
          simp [hpair.1]
      | cons head tail =>
          have hpair :
              head = first ∧
              tail ++ edge :: suffix = rest ++ [e] := by
            exact List.cons.inj hword
          rcases ih tail hpair.2 with
            ⟨middle, hsuffix, hprefix⟩ |
            ⟨hprefix, hedge, hsuffix⟩
          · refine Or.inl ⟨middle, hsuffix, ?_⟩
            simp [hpair.1, hprefix]
          · refine Or.inr ⟨?_, hedge, hsuffix⟩
            simp [hpair.1, hprefix]

/-- Exact append classification for the *historical* parent
relation, including the border-sample parent whose old U
carrier is replaced rather than moved forward. Consumer:
AncestorAppend and CQ.nonpass's new-edge case. -/
theorem topFreshTailCausalParentAppend
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n)) :
    TopFreshTailCausalParent ring C s (word ++ [e]) a b ↔
      TopFreshTailCausalParent ring C s word a b ∨
      TopFreshTailCausalServiceParent ring C s word e a b := by
  constructor
  · intro h
    cases h with
    | rearm pre suffix edge j v a hword hsite hsource hslot hnew =>
        rcases topFreshTailCausalOccurrenceSnoc
          word pre suffix edge e hword with
          ⟨middle, _, hprefix⟩ | ⟨hpre, hedge, _⟩
        · exact Or.inl
            (TopFreshTailCausalParent.rearm
              pre middle edge j v a hprefix
              hsite hsource hslot hnew)
        · subst pre
          subst hedge
          exact Or.inr (Or.inl
            ⟨j, v, hsite, hsource, hslot, hnew, rfl⟩)
    | borderSample pre suffix edge j v a hword hjzero
        hsite hsource hslot hnew =>
        rcases topFreshTailCausalOccurrenceSnoc
          word pre suffix edge e hword with
          ⟨middle, _, hprefix⟩ | ⟨hpre, hedge, _⟩
        · exact Or.inl
            (TopFreshTailCausalParent.borderSample
              pre middle edge j v a hprefix
              hjzero hsite hsource hslot hnew)
        · subst pre
          subst hedge
          exact Or.inr (Or.inr
            ⟨j, v, hjzero, hsite, hsource, hslot, hnew, rfl⟩)
  · intro h
    rcases h with hold | hnew
    · cases hold with
      | rearm pre suffix edge j v a hword hsite hsource hslot hnew =>
          have hwordNew :
              pre ++ edge :: (suffix ++ [e]) = word ++ [e] := by
            simpa [List.append_assoc] using
              congrArg (fun w : List (Fin n) => w ++ [e]) hword
          exact TopFreshTailCausalParent.rearm
            pre (suffix ++ [e]) edge j v a
            hwordNew hsite hsource hslot hnew
      | borderSample pre suffix edge j v a hword
          hjzero hsite hsource hslot hnew =>
          have hwordNew :
              pre ++ edge :: (suffix ++ [e]) = word ++ [e] := by
            simpa [List.append_assoc] using
              congrArg (fun w : List (Fin n) => w ++ [e]) hword
          exact TopFreshTailCausalParent.borderSample
            pre (suffix ++ [e]) edge j v a
            hwordNew hjzero hsite hsource hslot hnew
    · rcases hnew with hrear | hborder
      · rcases hrear with ⟨j, v, hsite, hsource,
          hslot, hnew, hb⟩
        subst b
        exact TopFreshTailCausalParent.rearm
          word [] e j v a (by simp)
          hsite hsource hslot hnew
      · rcases hborder with ⟨j, v, hjzero, hsite,
          hsource, hslot, hnew, hb⟩
        subst b
        exact TopFreshTailCausalParent.borderSample
          word [] e j v a (by simp)
          hjzero hsite hsource hslot hnew

/-- An existing chronological ancestry path remains valid when
one more physical scheduler service is appended. Consumer:
the OLD-history branch of CQ.nonpass and AncestorAppend. -/
theorem topFreshTailCausalAncestorOldAppend
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n))
    (h : TopFreshTailCausalAncestor ring C s word a b) :
    TopFreshTailCausalAncestor ring C s (word ++ [e]) a b := by
  induction h with
  | direct hp =>
      exact TopFreshTailCausalAncestor.direct
        ((topFreshTailCausalParentAppend
          ring C s word e _ _).2 (Or.inl hp))
  | follow hfirst hlast ihfirst ihlast =>
      exact TopFreshTailCausalAncestor.follow ihfirst ihlast

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Each selected true-tail rearm or source-border sample stamps
a new carrier at exactly the new audit clock; other occupied
slots retain a pre-service carrier. This is the all-prefix
born-before-clock invariant, established from the literal
genealogy step rather than from the nonpass hypothesis.
Consumer: the historical parent-event chronology. -/
private theorem topFreshTailCausalReplayBornBeforeClock
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    ∀ (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogyReplay ring C s word).slots j = some a →
      a.born ≤
        (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock := by
  have hfold :
      ∀ (w : List (Fin n))
        (G : TopFreshTailGenealogyState n),
        (∀ (k : Fin (topClockSpan n))
          (b : TopFreshTailCarrier (topClockSpan n)),
          G.slots k = some b → b.born ≤ G.trace.1.2.clock) →
        ∀ (j : Fin (topClockSpan n))
          (a : TopFreshTailCarrier (topClockSpan n)),
          (w.foldl (topFreshTailGenealogyStep ring C s) G).slots j =
            some a →
          a.born ≤
            (w.foldl (topFreshTailGenealogyStep ring C s)
              G).trace.1.2.clock := by
    intro w
    induction w with
    | nil =>
        intro G hage j a hslot
        exact hage j a hslot
    | cons e rest ih =>
        intro G hage j a hslot
        change
          (rest.foldl (topFreshTailGenealogyStep ring C s)
            (topFreshTailGenealogyStep ring C s G e)).slots j =
              some a at hslot
        exact ih (topFreshTailGenealogyStep ring C s G e)
          (fun k b hb =>
            topFreshTailCausalSlotAgeNext
              ring C s G e hage k b hb) j a hslot
  have hinitial :
      ∀ (j : Fin (topClockSpan n))
        (a : TopFreshTailCarrier (topClockSpan n)),
        (topFreshTailGenealogyInitial C s).slots j = some a →
        a.born ≤
          (topFreshTailGenealogyInitial C s).trace.1.2.clock := by
    intro j a hslot
    change topFreshTailGenealogyInitialSlot C s j = some a
      at hslot
    have hborn := topFreshTailGenealogyInitialBorn C s j a hslot
    rw [hborn]
    exact Nat.zero_le _
  exact hfold word (topFreshTailGenealogyInitial C s)
    hinitial

/-- A selected physical service increases the genealogy's
observed DigitAudit.clock by exactly one. Consumer: prefix
clock monotonicity and chronological event classification. -/
private theorem topFreshTailCausalReplayClockStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n) :
    (topFreshTailGenealogyStep ring C s G e).trace.1.2.clock =
      G.trace.1.2.clock + 1 := by
  rfl

/-- The deterministic replay clock equals the number of
completed selected scheduler services. Consumer: bounded birth
time and old-word/source separation in AncestorAppend. -/
private theorem topFreshTailCausalReplayClock
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) :
    (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock =
      word.length := by
  have hfold :
      ∀ (w : List (Fin n)) (G : TopFreshTailGenealogyState n),
        (w.foldl (topFreshTailGenealogyStep ring C s)
          G).trace.1.2.clock =
        G.trace.1.2.clock + w.length := by
    intro w
    induction w with
    | nil =>
        intro G
        rfl
    | cons edge rest ih =>
        intro G
        change
          (rest.foldl (topFreshTailGenealogyStep ring C s)
            (topFreshTailGenealogyStep ring C s G edge)).trace.1.2.clock =
          G.trace.1.2.clock + (edge :: rest).length
        rw [ih (topFreshTailGenealogyStep ring C s G edge)]
        rw [topFreshTailCausalReplayClockStep ring C s G edge]
        simp only [List.length_cons]
        omega
  have h := hfold word (topFreshTailGenealogyInitial C s)
  change
    (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock =
      0 + word.length at h
  simpa only [Nat.zero_add] using h

/-- An actual fixed-public replay prefix never has a clock
greater than any extension of the same scheduler word.
Consumer: the prefix-vs-terminal parent-event bound. -/
theorem topFreshTailCausalReplayClockPrefix
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (pre suffix : List (Fin n)) :
    (topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock ≤
      (topFreshTailGenealogyReplay ring C s
        (pre ++ suffix)).trace.1.2.clock := by
  rw [topFreshTailCausalReplayClock ring C s pre,
      topFreshTailCausalReplayClock ring C s (pre ++ suffix)]
  simp only [List.length_append]
  omega

/-- In any old chronological prefix, a carrier stored at a
source slot was born no later than the prefix clock.
This consequence of the independent born-before-clock fold
is the source-side input for both parent constructors. -/
private theorem topFreshTailCausalReplaySlotAge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hslot :
      (topFreshTailGenealogyReplay ring C s word).slots j =
        some a) :
    a.born ≤ word.length := by
  have hage := topFreshTailCausalReplayBornBeforeClock
    ring C s word j a hslot
  rw [topFreshTailCausalReplayClock ring C s word] at hage
  exact hage

/-- At any reached genealogy cut, the real audit clock
equals the length of its original scheduler word. The
explicit trace equality avoids rewriting the current state
in unrelated positions of the goal. -/
private theorem topFreshTailCausalReachedClock
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z) :
    Z.1.2.clock = Z.2.length := by
  have hclock := topFreshTailCausalReplayClock ring C s Z.2
  change
    (topFreshTailGenealogy ring C s Z).trace.1.2.clock =
      Z.2.length at hclock
  calc
    Z.1.2.clock =
        (topFreshTailGenealogy ring C s Z).trace.1.2.clock :=
      congrArg
        (fun T : TopFixedTraceState n => T.1.2.clock)
        hqueue.trace.2.symm
    _ = Z.2.length := hclock

/-- The old history cannot treat the newly born descendant
of the selected service as the source of any pre-existing
direct parent event. Consumer: the transitive closure split. -/
private theorem topFreshTailCausalParentChronology
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (h : TopFreshTailCausalParent ring C s word a b) :
    a.born < b.born ∧ b.born ≤ word.length := by
  cases h with
  | rearm pre suffix e j v a hword hsite hsource hslot hnew =>
      have hage := topFreshTailCausalReplaySlotAge
        ring C s pre j a hslot
      have hclock := topFreshTailCausalReplayClock
        ring C s pre
      have hlength : pre.length + 1 ≤ word.length := by
        have hl := congrArg List.length hword
        simp only [List.length_append, List.length_cons] at hl
        omega
      constructor
      · change a.born <
          (topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1
        rw [hclock]
        omega
      · change
          (topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1 ≤
            word.length
        rw [hclock]
        exact hlength
  | borderSample pre suffix e j v a hword hjzero
        hsite hsource hslot hnew =>
      have hage := topFreshTailCausalReplaySlotAge
        ring C s pre j a hslot
      have hclock := topFreshTailCausalReplayClock
        ring C s pre
      have hlength : pre.length + 1 ≤ word.length := by
        have hl := congrArg List.length hword
        simp only [List.length_append, List.length_cons] at hl
        omega
      constructor
      · change a.born <
          (topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1
        rw [hclock]
        omega
      · change
          (topFreshTailGenealogyReplay ring C s pre).trace.1.2.clock + 1 ≤
            word.length
        rw [hclock]
        exact hlength

/-- Any new last-service event has an OLD live source identity
and a NEW child identity stamped at precisely that service. -/
private theorem topFreshTailCausalServiceChronology
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n))
    (h : TopFreshTailCausalServiceParent
      ring C s word e a b) :
    a.born ≤ word.length ∧ b.born = word.length + 1 := by
  rcases h with
    ⟨j, v, hsite, hsource, hslot, hnew, hb⟩ |
    ⟨j, v, hjzero, hsite, hsource, hslot, hnew, hb⟩
  · have hage := topFreshTailCausalReplaySlotAge
      ring C s word j a hslot
    have hclock := topFreshTailCausalReplayClock ring C s word
    constructor
    · exact hage
    · rw [hb]
      change
        (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock + 1 =
          word.length + 1
      rw [hclock]
  · have hage := topFreshTailCausalReplaySlotAge
      ring C s word j a hslot
    have hclock := topFreshTailCausalReplayClock ring C s word
    constructor
    · exact hage
    · rw [hb]
      change
        (topFreshTailGenealogyReplay ring C s word).trace.1.2.clock + 1 =
          word.length + 1
      rw [hclock]

/-- Every directed parent edge in a word with one final
service still begins at a carrier born in the OLD prefix. -/
theorem topFreshTailCausalNewChildNoOldParent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (parent child : TopFreshTailCarrier (topClockSpan n))
    (hnew : TopFreshTailCausalServiceParent
      ring C s word e parent child)
    (next : TopFreshTailCarrier (topClockSpan n)) :
    ¬ TopFreshTailCausalParent ring C s word child next := by
  intro hparent
  have hstamp := (topFreshTailCausalServiceChronology
    ring C s word e parent child hnew).2
  have hold := topFreshTailCausalParentChronology
    ring C s word child next hparent
  omega

private theorem topFreshTailCausalAppendParentSourceBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n))
    (h : TopFreshTailCausalParent
      ring C s (word ++ [e]) a b) :
    a.born ≤ word.length := by
  rcases (topFreshTailCausalParentAppend
    ring C s word e a b).1 h with hold | hnew
  · have hchron := topFreshTailCausalParentChronology
      ring C s word a b hold
    omega
  · exact (topFreshTailCausalServiceChronology
      ring C s word e a b hnew).1

/-- The same source bound propagates through an arbitrary
nonempty ancestry path: its FIRST edge is necessarily an
event whose source existed before the final service. -/
private theorem topFreshTailCausalAppendAncestorSourceBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n))
    (h : TopFreshTailCausalAncestor
      ring C s (word ++ [e]) a b) :
    a.born ≤ word.length := by
  induction h with
  | direct hp =>
      exact topFreshTailCausalAppendParentSourceBound
        ring C s word e _ _ hp
  | follow hfirst hlast ihfirst ihlast =>
      exact ihfirst

/-- Full historical ancestor classification under one selected
service. New paths terminate at the freshly stamped child:
they consist of its direct parent edge, or an OLD ancestry
path to that parent followed by that edge. The source-time
bound excludes any continuation after the fresh child.
Consumer: CQ.nonpass's live parent-before-descendant clause. -/
theorem topFreshTailCausalAncestorAppend
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n)) (e : Fin n)
    (a b : TopFreshTailCarrier (topClockSpan n)) :
    TopFreshTailCausalAncestor
        ring C s (word ++ [e]) a b ↔
      TopFreshTailCausalAncestor ring C s word a b ∨
      TopFreshTailCausalServiceParent ring C s word e a b ∨
      (∃ parent : TopFreshTailCarrier (topClockSpan n),
        TopFreshTailCausalAncestor ring C s word a parent ∧
        TopFreshTailCausalServiceParent
          ring C s word e parent b) := by
  constructor
  · intro h
    induction h with
    | direct hp =>
        rcases (topFreshTailCausalParentAppend
          ring C s word e _ _).1 hp with hold | hnew
        · exact Or.inl (TopFreshTailCausalAncestor.direct hold)
        · exact Or.inr (Or.inl hnew)
    | follow hfirst hlast ihfirst ihlast =>
        rcases ihfirst with hfirstOld |
          (hfirstDirect | ⟨parentFirst, hfirstOldPart,
            hfirstSelected⟩)
        · rcases ihlast with hlastOld |
            (hlastDirect | ⟨parentLast, hlastOldPart,
              hlastSelected⟩)
          · exact Or.inl
              (TopFreshTailCausalAncestor.follow
                hfirstOld hlastOld)
          · exact Or.inr (Or.inr
              ⟨_, hfirstOld, hlastDirect⟩)
          · exact Or.inr (Or.inr
              ⟨parentLast,
                TopFreshTailCausalAncestor.follow
                  hfirstOld hlastOldPart, hlastSelected⟩)
        · have htime :=
            (topFreshTailCausalServiceChronology
              ring C s word e _ _ hfirstDirect).2
          have hbound :=
            topFreshTailCausalAppendAncestorSourceBound
              ring C s word e _ _ hlast
          omega
        · have htime :=
            (topFreshTailCausalServiceChronology
              ring C s word e _ _ hfirstSelected).2
          have hbound :=
            topFreshTailCausalAppendAncestorSourceBound
              ring C s word e _ _ hlast
          omega
  · intro h
    rcases h with hold | (hnew | ⟨parent, hfirst, hlast⟩)
    · exact topFreshTailCausalAncestorOldAppend
        ring C s word e a b hold
    · exact TopFreshTailCausalAncestor.direct
        ((topFreshTailCausalParentAppend
          ring C s word e a b).2 (Or.inr hnew))
    · exact TopFreshTailCausalAncestor.follow
        (topFreshTailCausalAncestorOldAppend
          ring C s word e a parent hfirst)
        (TopFreshTailCausalAncestor.direct
          ((topFreshTailCausalParentAppend
            ring C s word e parent b).2 (Or.inr hlast)))


/-- If a freshly stamped child and its direct old parent both
remain live after the selected service, the child is strictly
behind. The border-sample case is handled automatically:
its replaced U parent cannot also remain in the same source
slot, and only an existing parent transported into the next
slot can remain live. Consumer: new-direct CQ.nonpass. -/
theorem topFreshTailCausalNewParentLiveOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (parent child : TopFreshTailCarrier (topClockSpan n))
    (hselected : TopFreshTailCausalServiceParent
      ring C s Z.2 e parent child)
    (i j : Fin (topClockSpan n))
    (hchild :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots i = some child)
    (hparent :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some parent) :
    i.val < j.val := by
  have hstamp := (topFreshTailCausalServiceChronology
    ring C s Z.2 e parent child hselected).2
  have hparentBorn := (topFreshTailCausalServiceChronology
    ring C s Z.2 e parent child hselected).1
  have hclock := topFreshTailCausalReplayClock
    ring C s Z.2
  have hphysicalClock :=
    topFreshTailCausalReachedClock ring C s Z hqueue
  have hborn : child.born = Z.1.2.clock + 1 := by
    rw [hphysicalClock]
    exact hstamp
  have hsiteNew :=
    topFreshTailCausalFreshBirthAtSelectedSource
      ring C s hn hbad Z e hqueue i child hchild hborn
  obtain ⟨k, hsite, hslot⟩ :
      ∃ k : Fin (topClockSpan n),
        e = certSite s k.val ∧
        (topFreshTailGenealogy ring C s Z).slots k =
          some parent := by
    rcases hselected with
      ⟨k, v, hsite, _, hslot, _, _⟩ |
      ⟨k, v, _, hsite, _, hslot, _, _⟩
    · exact ⟨k, hsite, hslot⟩
    · exact ⟨k, hsite, hslot⟩
  have hik : i = k :=
    topFreshTailCausalSourceSiteInjective s hn i k
      (hsiteNew.trans hsite)
  have hstepParent :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).slots j =
          some parent := by
    rw [topFreshTailCausalReplayNext] at hparent
    exact hparent
  have hparentAge :
      parent.born ≤
        (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
    rw [hqueue.trace.2]
    exact hqueue.age k parent hslot
  have hplacement := topFreshTailCausalOlderCarrierPlacementExact
    ring C s (topFreshTailGenealogy ring C s Z)
      e j parent hstepParent hparentAge
  have hdistinct : child ≠ parent := by
    intro hsame
    have hb := congrArg
      (fun a : TopFreshTailCarrier (topClockSpan n) => a.born)
      hsame
    rw [hstamp] at hb
    omega
  rcases hplacement with hstay |
    ⟨hjpositive, hsiteParent, holdAtPredecessor, _⟩
  · have hjk : j = k :=
      hqueue.identity j k parent parent
        hstay hslot rfl rfl
    have hij : i = j := hik.trans hjk.symm
    rw [hij] at hchild
    have hsame := Option.some.inj
      (hchild.symm.trans hparent)
    exact False.elim (hdistinct hsame)
  · have hprev :
        k = (⟨j.val - 1,
          show j.val - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)) :=
      hqueue.identity k
        (⟨j.val - 1,
          show j.val - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n))
        parent parent hslot holdAtPredecessor rfl rfl
    have hv := congrArg Fin.val hprev
    simp only [Fin.val_mk] at hv
    have hi := congrArg Fin.val hik
    omega


/-- Historical ancestry strictly increases the carrier birth
time and its final member is born by the end of that history.
Consumer: the old/old branch of the next-step nonpass law. -/
private theorem topFreshTailCausalAncestorChronology
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (word : List (Fin n))
    (a b : TopFreshTailCarrier (topClockSpan n))
    (h : TopFreshTailCausalAncestor ring C s word a b) :
    a.born < b.born ∧ b.born ≤ word.length := by
  induction h with
  | direct hp =>
      exact topFreshTailCausalParentChronology
        ring C s word _ _ hp
  | follow hfirst hlast ihfirst ihlast =>
      omega

/-- A historical ancestor and descendant that are both still
live after the new service preserve their strict spatial
relation, using the OLD queue nonpass and the merged local
persistent-order theorem. Consumer: old-ancestor CQ.nonpass. -/
theorem topFreshTailCausalOldAncestorLiveOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (parent child : TopFreshTailCarrier (topClockSpan n))
    (hancestor : TopFreshTailCausalAncestor
      ring C s Z.2 parent child)
    (i j : Fin (topClockSpan n))
    (hchild :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots i = some child)
    (hparent :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some parent) :
    i.val < j.val := by
  have hchron := topFreshTailCausalAncestorChronology
    ring C s Z.2 parent child hancestor
  have hclock := topFreshTailCausalReplayClock
    ring C s Z.2
  have hageChild :
      child.born ≤
        (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
    change child.born ≤
      (topFreshTailGenealogyReplay ring C s Z.2).trace.1.2.clock
    rw [hclock]
    exact hchron.2
  have hageParent :
      parent.born ≤
        (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
    change parent.born ≤
      (topFreshTailGenealogyReplay ring C s Z.2).trace.1.2.clock
    rw [hclock]
    omega
  have hnewChild :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).slots i =
        some child := by
    rw [topFreshTailCausalReplayNext] at hchild
    exact hchild
  have hnewParent :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).slots j =
        some parent := by
    rw [topFreshTailCausalReplayNext] at hparent
    exact hparent
  obtain ⟨oldI, hOldI⟩ :=
    topFreshTailCausalOlderCarrierHasSource
      ring C s (topFreshTailGenealogy ring C s Z)
      e i child hnewChild hageChild
  obtain ⟨oldJ, hOldJ⟩ :=
    topFreshTailCausalOlderCarrierHasSource
      ring C s (topFreshTailGenealogy ring C s Z)
      e j parent hnewParent hageParent
  have hbefore := hqueue.nonpass.1
    oldI oldJ parent child hOldI hOldJ hancestor
  have hAge :
      ∀ (k : Fin (topClockSpan n))
        (a : TopFreshTailCarrier (topClockSpan n)),
        (topFreshTailGenealogy ring C s Z).slots k = some a →
        a.born ≤
          (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
    intro k a hslot
    rw [hqueue.trace.2]
    exact hqueue.age k a hslot
  exact topFreshTailCausalPersistentOrderStep
    ring C s (topFreshTailGenealogy ring C s Z) e
    hAge hqueue.identity oldI oldJ i j
    child parent hOldI hOldJ
    hnewChild hnewParent hbefore

/-- When the selected service creates a new child of an OLD
parent, a still-live OLD ancestor of that parent remains ahead
even when the immediate parent was replaced by border sampling.
Consumer: the transitive-new branch of CQ.nonpass. -/
theorem topFreshTailCausalOldAncestorNewChildLiveOrder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (ancestor parent child :
      TopFreshTailCarrier (topClockSpan n))
    (holdAncestor : TopFreshTailCausalAncestor
      ring C s Z.2 ancestor parent)
    (hselected : TopFreshTailCausalServiceParent
      ring C s Z.2 e parent child)
    (i j : Fin (topClockSpan n))
    (hchild :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots i = some child)
    (hancestor :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j = some ancestor) :
    i.val < j.val := by
  obtain ⟨k, hsite, hOldParent⟩ :
      ∃ k : Fin (topClockSpan n),
        e = certSite s k.val ∧
        (topFreshTailGenealogy ring C s Z).slots k =
          some parent := by
    rcases hselected with
      ⟨k, v, hsite, _, hslot, _, _⟩ |
      ⟨k, v, _, hsite, _, hslot, _, _⟩
    · exact ⟨k, hsite, hslot⟩
    · exact ⟨k, hsite, hslot⟩
  have hchron := topFreshTailCausalAncestorChronology
    ring C s Z.2 ancestor parent holdAncestor
  have hclock := topFreshTailCausalReplayClock
    ring C s Z.2
  have hOldBorn :
      ancestor.born ≤
        (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
    change ancestor.born ≤
      (topFreshTailGenealogyReplay ring C s Z.2).trace.1.2.clock
    rw [hclock]
    omega
  have hchildStamp :=
    (topFreshTailCausalServiceChronology
      ring C s Z.2 e parent child hselected).2
  have hphysicalClock :=
    topFreshTailCausalReachedClock ring C s Z hqueue
  have hnewBorn : child.born = Z.1.2.clock + 1 := by
    rw [hphysicalClock]
    exact hchildStamp
  have hnewSite := topFreshTailCausalFreshBirthAtSelectedSource
    ring C s hn hbad Z e hqueue i child hchild hnewBorn
  have hik : i = k :=
    topFreshTailCausalSourceSiteInjective s hn i k
      (hnewSite.trans hsite)
  have hnewAncestor :
      (topFreshTailGenealogyStep ring C s
        (topFreshTailGenealogy ring C s Z) e).slots j =
          some ancestor := by
    rw [topFreshTailCausalReplayNext] at hancestor
    exact hancestor
  have hplace := topFreshTailCausalOlderCarrierPlacementExact
    ring C s (topFreshTailGenealogy ring C s Z)
    e j ancestor hnewAncestor hOldBorn
  rcases hplace with hstay |
    ⟨hjpositive, hsitePredecessor, hOldPrev, _⟩
  · have holdOrder := hqueue.nonpass.1
      k j ancestor parent hOldParent hstay holdAncestor
    have hi := congrArg Fin.val hik
    omega
  · have holdOrder := hqueue.nonpass.1
      k
      (⟨j.val - 1,
        show j.val - 1 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n))
      ancestor parent hOldParent hOldPrev holdAncestor
    have hi := congrArg Fin.val hik
    simp only [Fin.val_mk] at holdOrder
    omega


/-- The full P.3 causal queue is closed under one genuine
selected scheduler edge. All five fields use the actual
fixed-public trace and deterministic genealogy, not a
separate carrier process. The first nonpass field follows
from AncestorAppend and the three live-order cases; the
second splits a historical service in Z.2++[e] into its old
prefix or the new selected service. Consumer: Q7c P.3. -/
theorem topFreshTailCausalQueueStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hqueue : TopFreshTailCausalQueue ring C s Z) :
    TopFreshTailCausalQueue ring C s
      (topFixedTraceNext ring C Z e) := by
  refine {
    trace := topFreshTailCausalQueueTraceStep
      ring C s Z e hqueue
    slot := topFreshTailCausalQueueSlotStep
      ring C s hn hbad Z e hqueue
    age := topFreshTailCausalQueueAgeStep
      ring C s Z e hqueue
    identity := topFreshTailCausalQueueIdentityStep
      ring C s hn hbad Z e hqueue
    nonpass := ?_ }
  constructor
  · intro i j parent child hchild hparent hancestor
    change TopFreshTailCausalAncestor ring C s
      (Z.2 ++ [e]) parent child at hancestor
    rcases (topFreshTailCausalAncestorAppend
      ring C s Z.2 e parent child).1 hancestor with
      hold | (hnew | ⟨middle, hbefore, hselected⟩)
    · exact topFreshTailCausalOldAncestorLiveOrder
        ring C s Z e hqueue parent child hold
        i j hchild hparent
    · exact topFreshTailCausalNewParentLiveOrder
        ring C s hn hbad Z e hqueue parent child
        hnew i j hchild hparent
    · exact topFreshTailCausalOldAncestorNewChildLiveOrder
        ring C s hn hbad Z e hqueue
        parent middle child hbefore hselected
        i j hchild hparent
  · intro pre suffix edge i j movedI movedJ a b
      hword hi hj hnewI hnewJ hbefore
    have hwordCut :
        pre ++ edge :: suffix = Z.2 ++ [e] := by
      exact hword
    rcases topFreshTailCausalOccurrenceSnoc
      Z.2 pre suffix edge e hwordCut with
      ⟨middle, hsuffix, hprefix⟩ |
      ⟨hprefix, hedge, hsuffix⟩
    · exact hqueue.nonpass.2
        pre middle edge i j movedI movedJ a b
        hprefix hi hj hnewI hnewJ hbefore
    · subst pre
      subst edge
      have hAge :
          ∀ (k : Fin (topClockSpan n))
            (carrier : TopFreshTailCarrier (topClockSpan n)),
            (topFreshTailGenealogy ring C s Z).slots k =
              some carrier →
            carrier.born ≤
              (topFreshTailGenealogy ring C s Z).trace.1.2.clock := by
        intro k carrier hslot
        rw [hqueue.trace.2]
        exact hqueue.age k carrier hslot
      change
        (topFreshTailGenealogyStep ring C s
          (topFreshTailGenealogy ring C s Z) e).slots movedI =
            some a at hnewI
      change
        (topFreshTailGenealogyStep ring C s
          (topFreshTailGenealogy ring C s Z) e).slots movedJ =
            some b at hnewJ
      exact topFreshTailCausalPersistentOrderStep
        ring C s (topFreshTailGenealogy ring C s Z) e
        hAge hqueue.identity
        i j movedI movedJ a b hi hj hnewI hnewJ hbefore


/-- Future-word CQ closure from any already reached cut:
the selected physical state and genealogy are carried by the
same topFixedTraceNext fold. Consumer: P.3 cut continuation. -/
theorem topFreshTailCausalQueueRunFromCut
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (word : List (Fin n)) :
    TopFreshTailCausalQueue ring C s
      (word.foldl (topFixedTraceNext ring C) Z) := by
  induction word generalizing Z with
  | nil =>
      exact hqueue
  | cons edge rest ih =>
      change TopFreshTailCausalQueue ring C s
        (rest.foldl (topFixedTraceNext ring C)
          (topFixedTraceNext ring C Z edge))
      exact ih (topFixedTraceNext ring C Z edge)
        (topFreshTailCausalQueueStep
          ring C s hn hbad Z edge hqueue)

theorem topFreshTailCausalQueueRun
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (word : List (Fin n)) :
    TopFreshTailCausalQueue ring C s
      (topFixedTraceRun ring C word) := by
  exact topFreshTailCausalQueueRun_of_step
    ring C s
    (fun Z e hqueue =>
      topFreshTailCausalQueueStep
        ring C s hn hbad Z e hqueue)
    word
end L3

#print axioms L3.topFreshTailGenealogyTrace
#print axioms L3.topFreshTailGenealogyTraceReached
#print axioms L3.topFreshTailGenealogyQueueStart
#print axioms L3.topFreshTailGenealogyBlockedSourceFrame
#print axioms L3.topFreshTailCausalOccupiedBlock
#print axioms L3.topFreshTailCausalOffPairFrame
#print axioms L3.topFreshTailCausalIndependentOwnerRows
#print axioms L3.topFreshTailCausalPortDeparture
#print axioms L3.topFreshTailCausalPortBlocked
#print axioms L3.topFreshTailCausalReplayNext
#print axioms L3.topFreshTailCausalNonmarkerEmpty
#print axioms L3.topFreshTailCausalQueueStart
#print axioms L3.topFreshTailCausalDataMove
#print axioms L3.topFreshTailCausalDataMoveTarget
#print axioms L3.topFreshTailCausalMarkerBirth
#print axioms L3.topFreshTailCausalUnreadInterior
#print axioms L3.topFreshTailCausalUnreadBorder
#print axioms L3.topFreshTailCausalQueueRun_of_step
#print axioms L3.topFreshTailCausalReachedPublicMask
#print axioms L3.topFreshTailCausalSourcePublicGeometry
#print axioms L3.topFreshTailCausalQueueTraceStep
#print axioms L3.topFreshTailCausalSlotAgeNext
#print axioms L3.topFreshTailCausalQueueAgeStep
#print axioms L3.topFreshTailCausalQueueAgeRun
#print axioms L3.topFreshTailCausalRearmBehindMovedParent
#print axioms L3.topFreshTailCausalNewChildDistinct
#print axioms L3.topFreshTailCausalSourcePublicGeometryRun
#print axioms L3.topFreshTailCausalBadInteriorEmptyStep
#print axioms L3.topFreshTailCausalBadBorderBirthStep
#print axioms L3.topFreshTailCausalSuccessorOldOrNew
#print axioms L3.topFreshTailCausalMovedParentAbsentAtSource
#print axioms L3.topFreshTailCausalSourceSiteInjective
#print axioms L3.topFreshTailCausalOlderCarrierHasSource
#print axioms L3.topFreshTailCausalDSourceOutcomes
#print axioms L3.topFreshTailCausalSourceSlotAgreement
#print axioms L3.topFreshTailCausalResponderOwnerOutput
#print axioms L3.topFreshTailCausalResponderPhysicalOutput
#print axioms L3.topFreshTailCausalRightNeighborInjective
#print axioms L3.topFreshTailCausalIncomingPredecessor
#print axioms L3.topFreshTailCausalOccupiedHasCarrier
#print axioms L3.topFreshTailCausalResponderSlotAgreement
#print axioms L3.topFreshTailCausalOffPairSlotAgreement
#print axioms L3.topFreshTailCausalQueueSlotStep
#print axioms L3.topFreshTailCausalOlderCarrierPlacement
#print axioms L3.topFreshTailCausalBorderIncomingOldCarrier
#print axioms L3.topFreshTailCausalInteriorIncomingOldCarrier
#print axioms L3.topFreshTailCausalResponderCarrierOld
#print axioms L3.topFreshTailCausalFreshBirthAtSelectedSource
#print axioms L3.topFreshTailCausalFreshIdentityStep
#print axioms L3.topFreshTailCausalOlderCarrierPlacementExact
#print axioms L3.topFreshTailCausalInteriorArrivalSourceToken
#print axioms L3.topFreshTailCausalOlderMoveConsumesSource
#print axioms L3.topFreshTailCausalQueueIdentityStep
#print axioms L3.topFreshTailCausalPersistentOrderStep
#print axioms L3.topFreshTailCausalParentAppend
#print axioms L3.topFreshTailCausalAncestorOldAppend
#print axioms L3.topFreshTailCausalReplayClockPrefix
#print axioms L3.topFreshTailCausalNewChildNoOldParent
#print axioms L3.topFreshTailCausalAncestorAppend
#print axioms L3.topFreshTailCausalNewParentLiveOrder
#print axioms L3.topFreshTailCausalOldAncestorLiveOrder
#print axioms L3.topFreshTailCausalOldAncestorNewChildLiveOrder
#print axioms L3.topFreshTailCausalQueueStep
#print axioms L3.topFreshTailCausalQueueRunFromCut
#print axioms L3.topFreshTailCausalQueueRun
