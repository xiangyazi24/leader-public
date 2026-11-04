import Leader.Wu.ShortGap.CurrentCohort

/-!
# Literal epoch reset: a reachable obstruction, with persistent history

The requested JOIN-to-idle rule is implemented literally. It differs from
the alternative that explicitly retains delivered epochs across JOIN. The theorem
lineage_step below is a COUNTEREXAMPLE, reached by two direct interactions
from a clean uniform start. An owner resets its epoch while the right root
still holds the result of that very comparison.

History observes resolved raw choices before JOIN and seeds the initially
resolved base. The previous completion-only
historyStep is not a resolution monitor; observeHistory supplies that missing
write before using its tickHistory. Every write remains append-only.

The requested different-epoch-to-delivered token projection is also literal:
in particular idle maps to delivered. tokensOf_step is a reachable
COUNTEREXAMPLE at the very first launch. Neither failure is repaired by
silently changing the specified transition or projection.
-/
namespace ShortGapLineage
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapDenialTransportLiteral ShortGapJoinedIncidenceBalance
set_option autoImplicit false

inductive GapEpoch where
  | idle
  | outbound (r : Nat) (c : Choice)
  | returning (r : Nat) (c d : Choice)
  | delivered (r : Nat) (c d : Choice)
  deriving DecidableEq

structure GhostRing (R : RFrame) where
  cfg : Vtx R → Agent
  k : Fin R.m → Nat
  hist : History R
  epoch : Fin R.m → GapEpoch

def physical (R : RFrame) (s : GhostRing R) : SliceState R := ⟨s.cfg, s.k⟩

def resolvedOpt : Choice → Option Choice
  | .race => none
  | c => some c

def observeHistory (a : Agent) (k : Nat) (H : Nat → Option Choice) : Nat → Option Choice :=
  match a with
  | .root .out1 _ _ => record H k .out1
  | .root .in0 _ _ => record H k .in0
  | _ => H

def updateHistory (a : Agent) (k : Nat) (H : Nat → Option Choice) : Nat → Option Choice :=
  tickHistory a k (observeHistory a k H)

/-- Events annotate the physical input row, without consulting ghosts to
select a row. Interior forwarding preserves the epoch. Direct P1 performs
launch, comparison and delivery in its single physical interaction. -/
def rowEpoch (k : Nat) (E : GapEpoch) : Agent → Agent → GapEpoch
  | .root c .toSend _, .interior .empty => .outbound k (resolveInit c)
  | .interior (.decl _), .root d _ .free =>
    match E with
    | .outbound r c => .returning r c (resolveResp d)
    | _ => E
  | .root _ .waiting _, .interior (.reply _) =>
    match E with
    | .returning r c d => .delivered r c d
    | _ => E
  | .root c .toSend _, .root d _ .free =>
    .delivered k (resolveInit c) (resolveResp d)
  | _, _ => E

def rawEpochs (R : RFrame) (s : GhostRing R) (e : Vtx R) (g : Fin R.m) : GapEpoch :=
  if g = e.1 then rowEpoch (s.k g) (s.epoch g) (s.cfg e) (s.cfg (rn R e))
  else s.epoch g

def ghostStep (R : RFrame) (s : GhostRing R) (e : Vtx R) : GhostRing R where
  cfg := (liftedStep R (physical R s) e).cfg
  k := (liftedStep R (physical R s) e).k
  hist i := if incident R e (rootV R i) then
    updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i) else s.hist i
  epoch g := if fires R (physical R s) e g then .idle else rawEpochs R s e g

theorem ghostStep_physical (R : RFrame) (s : GhostRing R) (e : Vtx R) :
    (ghostStep R s e).cfg = ShortGapOwnerRoundSlice.ringStepU R s.cfg e := rfl

theorem ghostStep_erases (R : RFrame) (s : GhostRing R) (e : Vtx R) :
    physical R (ghostStep R s e) = liftedStep R (physical R s) e := rfl

def ghostStart (R : RFrame) : GhostRing R where
  cfg := (ShortGapCurrentCohort.uniformStart R).cfg
  k _ := 0
  hist _ r := if r = 0 then some R.b else none
  epoch _ := .idle

def ghostRun (R : RFrame) : GhostRing R → List (Vtx R) → GhostRing R
  | s, [] => s
  | s, e :: es => ghostRun R (ghostStep R s e) es

def GhostReachable (R : RFrame) (s : GhostRing R) : Prop :=
  ∃ es, ghostRun R (ghostStart R) es = s

theorem ghostRun_erases (R : RFrame) (s : GhostRing R) (es : List (Vtx R)) :
    physical R (ghostRun R s es) = run R (physical R s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

theorem reachable_erases (R : RFrame) (s : GhostRing R) (hs : GhostReachable R s) :
    Reachable R (physical R s) := by
  obtain ⟨es, rfl⟩ := hs
  exact ⟨es, (ghostRun_erases R (ghostStart R) es).symm⟩

def ComparedAt : GapEpoch → Nat → Prop
  | .idle, _ => False
  | .outbound t _, r => r < t
  | .returning t _ _, r | .delivered t _ _, r => r ≤ t

def DeliveredAt : GapEpoch → Nat → Prop
  | .idle, _ => False
  | .outbound t _, r | .returning t _ _, r => r < t
  | .delivered t _ _, r => r ≤ t

def Live : GapEpoch → Prop
  | .outbound _ _ | .returning _ _ _ => True
  | _ => False

instance (E : GapEpoch) (r : Nat) : Decidable (ComparedAt E r) := by
  cases E <;> unfold ComparedAt <;> infer_instance
instance (E : GapEpoch) (r : Nat) : Decidable (DeliveredAt E r) := by
  cases E <;> unfold DeliveredAt <;> infer_instance
instance (E : GapEpoch) : Decidable (Live E) := by
  cases E <;> unfold Live <;> infer_instance

def EmptyGap (R : RFrame) (s : GhostRing R) (g : Fin R.m) : Prop :=
  ∀ a : Fin R.h, 0 < a.val → s.cfg (g,a) = .interior .empty

/-- Existence of one position and emptiness of every other interior slot. -/
def OneToken (R : RFrame) (s : GhostRing R) (g : Fin R.m) (token : Slot) : Prop :=
  ∃ p : Fin R.h, 0 < p.val ∧
    ∀ a : Fin R.h, 0 < a.val → s.cfg (g,a) = .interior (if a = p then token else .empty)

def EpochShape (R : RFrame) (s : GhostRing R) (g : Fin R.m) : Prop :=
  match s.epoch g with
  | .idle => s.k g = 0 ∧ s.k (next R g) = 0 ∧ EmptyGap R s g
  | .outbound t c => s.k g = t ∧
    (s.k (next R g) = t ∨ s.k (next R g) + 1 = t) ∧
    s.hist g t = some c ∧ OneToken R s g (.decl c)
  | .returning t c d => s.k g = t ∧
    (s.k (next R g) = t ∨ s.k (next R g) = t + 1) ∧
    s.hist g t = some c ∧ s.hist (next R g) t = some d ∧ OneToken R s g (.reply d)
  | .delivered t c d => (s.k g = t ∨ s.k g = t + 1) ∧
    (s.k (next R g) = t ∨ s.k (next R g) = t + 1) ∧
    s.hist g t = some c ∧ s.hist (next R g) t = some d ∧ EmptyGap R s g

def CcwHeld : Option CcwPort → Prop
  | some .heldDenial | some .heldCandidate => True
  | _ => False

def CwHeld : Option CwPort → Prop
  | some .heldDenial | some .heldCandidate => True
  | _ => False

instance (p : Option CcwPort) : Decidable (CcwHeld p) := by
  cases p with
  | none => exact isFalse id
  | some p => cases p <;> unfold CcwHeld <;> infer_instance
instance (p : Option CwPort) : Decidable (CwHeld p) := by
  cases p with
  | none => exact isFalse id
  | some p => cases p <;> unfold CwHeld <;> infer_instance

def BeforeLatest : GapEpoch → Nat → Prop
  | .idle, _ => False
  | .outbound t _, r | .returning t _ _, r | .delivered t _ _, r => r < t

def HistoricalDenial (R : RFrame) (s : GhostRing R) (g : Fin R.m) (r : Nat) : Prop :=
  ∃ c d, s.hist g r = some c ∧ s.hist (next R g) r = some d ∧ res c d = .denial

/-- History, shape, current receipt, and completed-prefix clauses.
No skew, provenance, simulation, closure, or candidate-lock conclusion is a
field. Exact receipt values are indexed by the receiving endpoint's CURRENT
round. These clauses fail under the requested epoch reset. -/
structure Lineage (R : RFrame) (s : GhostRing R) : Prop where
  roots : ∀ i, ∃ c cw ccw, s.cfg (rootV R i) = .root c cw ccw
  normalized : ∀ i, joinReady (s.cfg (rootV R i)) = false
  histValues : ∀ i r c, s.hist i r = some c → c ≠ .race
  histPast : ∀ i r, r < s.k i → ∃ c, s.hist i r = some c
  histNow : ∀ i c cw ccw, s.cfg (rootV R i) = .root c cw ccw →
    s.hist i (s.k i) = resolvedOpt c
  histFuture : ∀ i r, s.k i < r → s.hist i r = none
  raceReady : ∀ i, (s.cfg (rootV R i)).choice = some .race →
    s.cfg (rootV R i) = .root .race .toSend .free
  shape : ∀ g, EpochShape R s g
  waiting : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live (s.epoch g)
  outgoing : ∀ g, CwHeld (s.cfg (rootV R g)).cwPort ↔ DeliveredAt (s.epoch g) (s.k g)
  incoming : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    ComparedAt (s.epoch g) (s.k (next R g))
  prefixPayloads : ∀ g r, ComparedAt (s.epoch g) r →
    ∃ c d, s.hist g r = some c ∧ s.hist (next R g) r = some d
  prefixDenials : ∀ g r, BeforeLatest (s.epoch g) r → HistoricalDenial R s g r
  joinedDenials : ∀ i r, r < s.k i →
    DeliveredAt (s.epoch i) r ∧ ComparedAt (s.epoch (prev R i)) r ∧
    HistoricalDenial R s i r ∧ HistoricalDenial R s (prev R i) r
  outgoingValue : ∀ g, DeliveredAt (s.epoch g) (s.k g) →
    ∃ c d, s.hist g (s.k g) = some c ∧ s.hist (next R g) (s.k g) = some d ∧
      (s.cfg (rootV R g)).cwPort = some (resCw c d)
  incomingValue : ∀ g, ComparedAt (s.epoch g) (s.k (next R g)) →
    ∃ c d, s.hist g (s.k (next R g)) = some c ∧
      s.hist (next R g) (s.k (next R g)) = some d ∧
      (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)

theorem lineage_start (R : RFrame) : Lineage R (ghostStart R) := by
  have hb : R.b ≠ .race := by rcases R.hb with h | h <;> simp [h]
  constructor
  · intro i; exact ⟨R.b, .toSend, .free, rfl⟩
  · intro i; rfl
  · intro i r c hc
    simp only [ghostStart] at hc
    split at hc
    · cases hc; exact hb
    · contradiction
  · intro i r hr; change r < 0 at hr; omega
  · intro i c cw ccw hc
    change Agent.root R.b .toSend .free = Agent.root c cw ccw at hc
    cases hc
    rcases R.hb with h | h <;> simp [ghostStart, resolvedOpt, h]
  · intro i r hr; change 0 < r at hr
    simp [ghostStart, Nat.ne_of_gt hr]
  · intro i hi
    change some R.b = some .race at hi
    exact False.elim (hb (Option.some.inj hi))
  · intro g; refine ⟨rfl, rfl, ?_⟩
    intro a ha; simp [ghostStart, ShortGapCurrentCohort.uniformStart, Nat.ne_of_gt ha]
  · intro g; exact ⟨(fun h => nomatch h), False.elim⟩
  · intro g; exact Iff.rfl
  · intro g; exact Iff.rfl
  · intro g r h; exact False.elim h
  · intro g r h; exact False.elim h
  · intro i r h; change r < 0 at h; omega
  · intro g h; exact False.elim h
  · intro g h; exact False.elim h

/-- Skew is derived from epoch endpoint ranges, not a Lineage field. -/
theorem neighborSkew_of_lineage (R : RFrame) (s : GhostRing R) (hs : Lineage R s) :
    NeighborSkew R (physical R s) := by
  intro g
  have h := hs.shape g
  change s.k g ≤ s.k (next R g) + 1 ∧ s.k (next R g) ≤ s.k g + 1
  cases he : s.epoch g <;> simp only [EpochShape, he] at h
  all_goals omega

theorem outgoing_support (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (hc : CwHeld (s.cfg (rootV R g)).cwPort) : s.k g ≤ s.k (next R g) := by
  have hd := (hs.outgoing g).mp hc
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  all_goals simp only [he, DeliveredAt] at hd
  all_goals omega

theorem incoming_support (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (hc : CcwHeld (s.cfg (rootV R (next R g))).ccwPort) :
    s.k (next R g) ≤ s.k g := by
  have hd := (hs.incoming g).mp hc
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  all_goals simp only [he, ComparedAt] at hd
  all_goals omega

/-- The P1 guards force equal endpoint generations from the epoch ranges. -/
theorem direct_generations (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (hc : (s.cfg (rootV R g)).cwPort = some .toSend)
    (hd : (s.cfg (rootV R (next R g))).ccwPort = some .free) : s.k g = s.k (next R g) := by
  have hn : ¬ Live (s.epoch g) := by
    intro h
    have hh := (hs.waiting g).mpr h
    rw [hc] at hh; cases hh
  have ho : ¬ DeliveredAt (s.epoch g) (s.k g) := by
    intro h
    have hh := (hs.outgoing g).mpr h
    rw [hc] at hh; exact hh
  have hi : ¬ ComparedAt (s.epoch g) (s.k (next R g)) := by
    intro h
    have hh := (hs.incoming g).mpr h
    rw [hd] at hh; exact hh
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  all_goals simp only [he, Live, DeliveredAt, ComparedAt] at hn ho hi
  all_goals first | exact False.elim (hn trivial) | omega

/-- Slot-occupied launches are excluded on Lineage states. Calling such a
launch a universal word stutter would be wrong: dirty L3 can resolve Race. -/
theorem toSend_empty_gap (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (hc : (s.cfg (rootV R g)).cwPort = some .toSend) : EmptyGap R s g := by
  have hn : ¬ Live (s.epoch g) := by
    intro h
    have hh := (hs.waiting g).mpr h
    rw [hc] at hh; cases hh
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  · exact hh.2.2
  · exact False.elim (hn (by rw [he]; trivial))
  · exact False.elim (hn (by rw [he]; trivial))
  · exact hh.2.2.2.2

private theorem oneToken_kind (R : RFrame) (s : GhostRing R) (g : Fin R.m)
    (t u : Slot) (ht : OneToken R s g t) (a : Fin R.h) (ha : 0 < a.val)
    (hu : s.cfg (g,a) = .interior u) : u = t ∨ u = .empty := by
  obtain ⟨p, _, hp⟩ := ht
  have hh := hp a ha
  rw [hu] at hh
  by_cases h : a = p
  · simp only [if_pos h] at hh; cases hh; exact Or.inl rfl
  · simp only [if_neg h] at hh; cases hh; exact Or.inr rfl

theorem reply_support (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (d : Choice)
    (ht : s.cfg (g,a) = .interior (.reply d)) : s.k g ≤ s.k (next R g) := by
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  · have hx := hh.2.2 a ha; rw [ht] at hx; cases hx
  · have hx := oneToken_kind R s g _ _ hh.2.2.2 a ha ht
    rcases hx with h | h <;> cases h
  · omega
  · have hx := hh.2.2.2.2 a ha; rw [ht] at hx; cases hx

theorem declaration_support (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (c : Choice)
    (ht : s.cfg (g,a) = .interior (.decl c)) : s.k (next R g) ≤ s.k g := by
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  · have hx := hh.2.2 a ha; rw [ht] at hx; cases hx
  · omega
  · have hx := oneToken_kind R s g _ _ hh.2.2.2.2 a ha ht
    rcases hx with h | h <;> cases h
  · have hx := hh.2.2.2.2 a ha; rw [ht] at hx; cases hx

private theorem row_cw_receipt (c : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent)
    (h : (row (.root c cw ccw) b).1.cwPort = some .heldDenial) :
    cw = .heldDenial ∨ (∃ d, b = .interior (.reply d)) ∨
      (cw = .toSend ∧ ∃ d dw, b = .root d dw .free) := by
  cases b with
  | root d dw dd => cases cw <;> cases dd <;> simp_all [row, Agent.cwPort]
  | interior t => cases t <;> cases cw <;> simp_all [row, Agent.cwPort]

private theorem row_ccw_receipt (a : Agent) (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (h : (row a (.root c cw ccw)).2.ccwPort = some .heldDenial) :
    ccw = .heldDenial ∨ (∃ d, a = .interior (.decl d)) ∨
      (ccw = .free ∧ ∃ d dd, a = .root d .toSend dd) := by
  cases a with
  | root d dw dd => cases dw <;> cases ccw <;> simp_all [row, Agent.ccwPort]
  | interior t => cases t <;> cases ccw <;> simp_all [row, Agent.ccwPort]

private theorem row_resp_cw (a : Agent) (c : Choice) (cw : CwPort) (ccw : CcwPort) :
    (row a (.root c cw ccw)).2.cwPort = some cw := by
  cases a with
  | root d dw dd => cases dw <;> cases ccw <;> simp [row, Agent.cwPort]
  | interior t => cases t <;> cases ccw <;> simp [row, Agent.cwPort]

private theorem row_init_ccw (c : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent) :
    (row (.root c cw ccw) b).1.ccwPort = some ccw := by
  cases b with
  | root d dw dd => cases cw <;> cases dd <;> simp [row, Agent.ccwPort]
  | interior t => cases t <;> cases cw <;> simp [row, Agent.ccwPort]

theorem interior_roles (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) : ∃ t, s.cfg (g,a) = .interior t := by
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  · exact ⟨.empty, hh.2.2 a ha⟩
  · obtain ⟨p, _, hp⟩ := hh.2.2.2; exact ⟨_, hp a ha⟩
  · obtain ⟨p, _, hp⟩ := hh.2.2.2.2; exact ⟨_, hp a ha⟩
  · exact ⟨.empty, hh.2.2.2.2 a ha⟩

private theorem rn_root_cases (R : RFrame) (i : Fin R.m) :
    rn R (rootV R i) = rootV R (next R i) ∨
      ∃ a : Fin R.h, 0 < a.val ∧ rn R (rootV R i) = (i,a) := by
  by_cases h : 1 < R.h
  · exact Or.inr ⟨⟨1,h⟩, Nat.zero_lt_succ 0, by simp [rn, h]⟩
  · exact Or.inl (by simp [rn, rootV, h])

private theorem boundary_root (R : RFrame) (e : Vtx R) (i : Fin R.m)
    (hd : rootV R i = rn R e) : i = next R e.1 := by
  by_cases h : e.2.val + 1 < R.h
  · have hh := congrArg (fun v => v.2.val) hd
    simp [rn, h] at hh
  · have hh := congrArg Prod.fst hd
    simpa [rn, rootV, h] using hh

private theorem zero_is_root (R : RFrame) (e : Vtx R) (h : e.2.val = 0) : e = rootV R e.1 := by
  exact Prod.ext rfl (Fin.ext h)

private theorem cw_raw_support (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (i : Fin R.m) (e : Vtx R)
    (hr : (rawAt R s.cfg e (rootV R i)).cwPort = some .heldDenial) :
    s.k i ≤ s.k (next R i) := by
  obtain ⟨c, cw, ccw, hc⟩ := hs.roots i
  have old : cw = .heldDenial → s.k i ≤ s.k (next R i) := by
    intro h; apply outgoing_support R s hs i
    rw [hc, h]; trivial
  by_cases ht : rootV R i = e
  · unfold rawAt at hr
    rw [if_pos ht, ← ht, hc] at hr
    rcases row_cw_receipt c cw ccw _ hr with h | h | h
    · exact old h
    · obtain ⟨d, hd⟩ := h
      rcases rn_root_cases R i with hn | ⟨a, ha, hn⟩
      · rw [hn] at hd
        obtain ⟨c', cw', ccw', hc'⟩ := hs.roots (next R i)
        rw [hc'] at hd; cases hd
      · rw [hn] at hd; exact reply_support R s hs i a ha d hd
    · obtain ⟨hw, d, dw, hd⟩ := h
      rcases rn_root_cases R i with hn | ⟨a, ha, hn⟩
      · rw [hn] at hd
        exact Nat.le_of_eq (direct_generations R s hs i
          (by rw [hc, hw]; rfl) (by rw [hd]; rfl))
      · rw [hn] at hd
        obtain ⟨t, ht⟩ := interior_roles R s hs i a ha
        rw [ht] at hd; cases hd
  · by_cases hd : rootV R i = rn R e
    · unfold rawAt at hr
      rw [if_neg ht, if_pos hd, ← hd, hc, row_resp_cw] at hr
      exact old (Option.some.inj hr)
    · unfold rawAt at hr
      rw [if_neg ht, if_neg hd, hc] at hr
      exact old (Option.some.inj hr)

private theorem ccw_raw_support (R : RFrame) (s : GhostRing R) (hs : Lineage R s)
    (i : Fin R.m) (e : Vtx R)
    (hr : (rawAt R s.cfg e (rootV R i)).ccwPort = some .heldDenial) :
    s.k i ≤ s.k (prev R i) := by
  obtain ⟨c, cw, ccw, hc⟩ := hs.roots i
  have old : ccw = .heldDenial → s.k i ≤ s.k (prev R i) := by
    intro h
    have hh := incoming_support R s hs (prev R i)
    rw [next_prev] at hh
    exact hh (by rw [hc, h]; trivial)
  by_cases ht : rootV R i = e
  · unfold rawAt at hr
    rw [if_pos ht, ← ht, hc, row_init_ccw] at hr
    exact old (Option.some.inj hr)
  · by_cases hd : rootV R i = rn R e
    · unfold rawAt at hr
      rw [if_neg ht, if_pos hd, ← hd, hc] at hr
      have hi := boundary_root R e i hd
      have hp : prev R i = e.1 := by rw [hi, prev_next]
      rcases row_ccw_receipt _ c cw ccw hr with h | h | h
      · exact old h
      · obtain ⟨d, hd⟩ := h
        by_cases hz : e.2.val = 0
        · have he := zero_is_root R e hz
          rw [he] at hd
          obtain ⟨c', cw', ccw', hc'⟩ := hs.roots e.1
          rw [hc'] at hd; cases hd
        · have hh := declaration_support R s hs e.1 e.2 (by omega) d hd
          rw [← hi] at hh
          rw [hp]
          exact hh
      · obtain ⟨hf, d, dd, hd⟩ := h
        by_cases hz : e.2.val = 0
        · have hd' : s.cfg (rootV R e.1) = .root d .toSend dd := by
            have he2 : e.2 = (⟨0,R.hh⟩ : Fin R.h) := Fin.ext hz
            change s.cfg (e.1,e.2) = _ at hd
            rw [he2] at hd
            exact hd
          have hh := direct_generations R s hs e.1 (by rw [hd']; rfl)
            (by rw [← hi, hc, hf]; rfl)
          rw [hp, hi]
          exact Nat.le_of_eq hh.symm
        · obtain ⟨t, ht⟩ := interior_roles R s hs e.1 e.2 (by omega)
          rw [ht] at hd; cases hd
    · unfold rawAt at hr
      rw [if_neg ht, if_neg hd, hc] at hr
      exact old (Option.some.inj hr)

/-- Raw provenance is proved by classifying the actual row: framed receipts,
V1 reply delivery, K1/K2 declarations, and equal-generation direct P1. -/
theorem provenance_of_lineage (R : RFrame) (s : GhostRing R) (hs : Lineage R s) (e : Vtx R) :
    RawReceiptProvenance R (physical R s) e :=
  ⟨fun i h => cw_raw_support R s hs i e h, fun i h => ccw_raw_support R s hs i e h⟩

theorem join_requires_neighbors_of_lineage (R : RFrame) (s : GhostRing R)
    (hs : Lineage R s) (e : Vtx R) (i : Fin R.m) (hj : fires R (physical R s) e i = true) :
    s.k i ≤ s.k (next R i) ∧ s.k i ≤ s.k (prev R i) :=
  join_requires_neighbors R (physical R s) e (provenance_of_lineage R s hs e) i hj

/-- One-step skew preservation is positive even though full lineage closure
fails: the proof uses raw receipt provenance, not post-step lineage. -/
theorem neighborSkew_step_of_lineage (R : RFrame) (s : GhostRing R)
    (hs : Lineage R s) (e : Vtx R) : NeighborSkew R (physical R (ghostStep R s e)) :=
  neighborSkew_step R (physical R s) e (neighborSkew_of_lineage R s hs)
    (provenance_of_lineage R s hs e)

theorem updateHistory_monotone (a : Agent) (k r : Nat) (H : Nat → Option Choice)
    (c : Choice) (hc : H r = some c) : updateHistory a k H r = some c := by
  apply tickHistory_monotone
  cases a with
  | interior t => exact hc
  | root d cw ccw =>
    cases d
    · exact hc
    · exact record_monotone _ _ _ _ _ hc
    · exact record_monotone _ _ _ _ _ hc

theorem hist_monotone (R : RFrame) (s : GhostRing R) (e : Vtx R)
    (i : Fin R.m) (r : Nat) (c : Choice) (hc : s.hist i r = some c) :
    (ghostStep R s e).hist i r = some c := by
  simp only [ghostStep]
  split
  · exact updateHistory_monotone _ _ _ _ _ hc
  · exact hc

theorem hist_run_monotone (R : RFrame) (s : GhostRing R) (es : List (Vtx R))
    (i : Fin R.m) (r : Nat) (c : Choice) (hc : s.hist i r = some c) :
    (ghostRun R s es).hist i r = some c := by
  induction es generalizing s with
  | nil => exact hc
  | cons e es ih => exact ih _ (hist_monotone R s e i r c hc)

def choiceToWord : Choice → PeriodHIncidenceChoice.Choice
  | .race => .race
  | .out1 => .out1
  | .in0 => .in0

/-- Option.getD .race, followed only by the alphabet adapter required by
the existing incidence module's distinct Choice type. -/
def wordOf (R : RFrame) (r : Nat) (s : GhostRing R) : PeriodHIncidenceChoice.Configuration R.m :=
  fun i => choiceToWord ((s.hist i r).getD .race)

def mask (R : RFrame) (r : Nat) (s : GhostRing R) (i : Fin R.m) : Bool := decide (r ≤ s.k i)

def VirtualCandidate (R : RFrame) (r : Nat) (s : GhostRing R) : Prop :=
  ∃ g, PeriodHIncidenceChoice.Candidate10 (ring R) (wordOf R r s) g

private theorem word_saved {R : RFrame} {r : Nat} {s : GhostRing R} {i : Fin R.m}
    {c : PeriodHIncidenceChoice.Choice} (hc : c ≠ .race) (hi : wordOf R r s i = c) :
    ∃ d, s.hist i r = some d ∧ choiceToWord d = c := by
  cases hh : s.hist i r with
  | none => simp [wordOf, hh, choiceToWord] at hi; exact False.elim (hc hi.symm)
  | some d => exact ⟨d, rfl, by simpa [wordOf, hh] using hi⟩

theorem virtualCandidate_persists (R : RFrame) (r : Nat) (s : GhostRing R)
    (e : Vtx R) (hc : VirtualCandidate R r s) : VirtualCandidate R r (ghostStep R s e) := by
  obtain ⟨g, h0, h1⟩ := hc
  obtain ⟨c, hc, hcw⟩ := word_saved (by decide) h0
  obtain ⟨d, hd, hdw⟩ := word_saved (by decide) h1
  refine ⟨g, ?_, ?_⟩
  · simp [wordOf, hist_monotone R s e g r c hc, hcw]
  · simp [wordOf, hist_monotone R s e ((ring R).rightNeighbor g) r d hd, hdw]

theorem virtualCandidate_run (R : RFrame) (r : Nat) (s : GhostRing R)
    (es : List (Vtx R)) (hc : VirtualCandidate R r s) :
    VirtualCandidate R r (ghostRun R s es) := by
  induction es generalizing s with
  | nil => exact hc
  | cons e es ih => exact ih _ (virtualCandidate_persists R r s e hc)

theorem ring_next (R : RFrame) (g : Fin R.m) : (ring R).rightNeighbor g = next R g := by
  apply Fin.ext
  change (g.val + 1) % R.m = if g.val + 1 = R.m then 0 else g.val + 1
  by_cases h : g.val + 1 = R.m
  · simp [h]
  · have hl : g.val + 1 < R.m := by have := g.isLt; omega
    simp [h, Nat.mod_eq_of_lt hl]

/-- A historical candidate pins both generations on Lineage states.
Completed-round denial history, rather than a candidate-lock field, excludes
an endpoint above r. This is not a claim of Lineage closure along a run. -/
theorem virtualCandidate_pins (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage R s) (g : Fin R.m)
    (hc : PeriodHIncidenceChoice.Candidate10 (ring R) (wordOf R r s) g) :
    s.k g = r ∧ s.k (next R g) = r := by
  obtain ⟨c, h0, hc0⟩ := word_saved (by decide) hc.1
  obtain ⟨d, h1, hd1⟩ := word_saved (by decide) hc.2
  have hc' : c = .out1 := by cases c <;> first | rfl | cases hc0
  have hd' : d = .in0 := by cases d <;> first | rfl | cases hd1
  subst c; subst d
  rw [ring_next] at h1
  have noDenial : ¬ HistoricalDenial R s g r := by
    rintro ⟨c, d, h0', h1', hd⟩
    rw [h0] at h0'; rw [h1] at h1'
    cases h0'; cases h1'; cases hd
  have hlow0 : r ≤ s.k g := by
    have hn : ¬ s.k g < r := by
      intro h; have hh := hs.histFuture g r h; rw [h0] at hh; cases hh
    omega
  have hlow1 : r ≤ s.k (next R g) := by
    have hn : ¬ s.k (next R g) < r := by
      intro h; have hh := hs.histFuture (next R g) r h; rw [h1] at hh; cases hh
    omega
  have hhigh0 : ¬ r < s.k g := fun h => noDenial (hs.joinedDenials g r h).2.2.1
  have hhigh1 : ¬ r < s.k (next R g) := by
    intro h
    have hd := (hs.joinedDenials (next R g) r h).2.2.2
    rw [prev_next] at hd
    exact noDenial hd
  exact ⟨by omega, by omega⟩

/-- Conditional finite-run lock. Only the final state's Lineage is needed,
since history persists without any invariant. Full unconditional future
locking still needs a preserved selected-gap invariant: lineage_step is false.
The Lineage premise here is explicit and is not supplied by reachability. -/
theorem virtualCandidate_locks_of_lineage_run (R : RFrame) (r : Nat)
    (s : GhostRing R) (g : Fin R.m)
    (hc : PeriodHIncidenceChoice.Candidate10 (ring R) (wordOf R r s) g)
    (es : List (Vtx R)) (hs : Lineage R (ghostRun R s es)) :
    (ghostRun R s es).k g = r ∧ (ghostRun R s es).k (next R g) = r := by
  have keep : PeriodHIncidenceChoice.Candidate10 (ring R) (wordOf R r (ghostRun R s es)) g := by
    obtain ⟨c, h0, hc0⟩ := word_saved (by decide) hc.1
    obtain ⟨d, h1, hd1⟩ := word_saved (by decide) hc.2
    have saved := hist_run_monotone R s es
    exact ⟨by simp [wordOf, saved _ r _ h0, hc0], by simp [wordOf, saved _ r _ h1, hd1]⟩
  exact virtualCandidate_pins R r _ hs g keep

theorem updateHistory_other (a : Agent) (k r : Nat) (H : Nat → Option Choice)
    (hr : r ≠ k) : updateHistory a k H r = H r := by
  cases a with
  | interior t => rfl
  | root c cw ccw => cases c <;> cases cw <;> cases ccw <;>
      simp [updateHistory, tickHistory, observeHistory, record, hr]

/-- All scheduled roots must be outside the accounting round. A mixed edge
touching a current-round root is deliberately not classified as side activity. -/
theorem wordOf_side_stutter (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hside : ∀ i, incident R e (rootV R i) → r ≠ s.k i) :
    wordOf R r (ghostStep R s e) = wordOf R r s := by
  funext i
  by_cases hi : incident R e (rootV R i)
  · simp only [wordOf, ghostStep, if_pos hi, updateHistory_other _ _ _ _ (hside i hi)]
  · simp only [wordOf, ghostStep, if_neg hi]

private theorem record_already (H : Nat → Option Choice) (k : Nat) (c d : Choice)
    (hh : H k = some c) : record H k d = H := by
  funext r
  by_cases hr : r = k
  · subst r; simp [record, hh]
  · simp [record, hr]

private theorem updateHistory_current (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (k : Nat) (H : Nat → Option Choice) (hh : H k = resolvedOpt c)
    (hn : joinReady (.root c cw ccw) = false) : updateHistory (.root c cw ccw) k H = H := by
  cases c <;> cases cw <;> cases ccw
  all_goals first | contradiction | rfl |
    simp [updateHistory, observeHistory, tickHistory, record_already H k _ _ hh]

theorem wordOf_row_stutter (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hs : Lineage R s) (he : row (s.cfg e) (s.cfg (rn R e)) = (s.cfg e, s.cfg (rn R e))) :
    wordOf R r (ghostStep R s e) = wordOf R r s := by
  have hraw : ∀ w, rawAt R s.cfg e w = s.cfg w := by
    intro w
    by_cases ht : w = e
    · simp [rawAt, he, ht]
    · by_cases hd : w = rn R e
      · unfold rawAt; rw [if_neg ht, if_pos hd, he]; simp [hd]
      · simp [rawAt, ht, hd]
  funext i
  by_cases hi : incident R e (rootV R i)
  · obtain ⟨c, cw, ccw, hc⟩ := hs.roots i
    have hn := hs.normalized i
    rw [hc] at hn
    simp only [wordOf, ghostStep, if_pos hi, hraw, hc,
      updateHistory_current c cw ccw _ _ (hs.histNow i c cw ccw hc) hn]
  · simp only [wordOf, ghostStep, if_neg hi]

/-- K3 is an actual row identity, so its history word stutters at every r.
This is distinct from P2, which may resolve the initiator while waiting. -/
theorem wordOf_K3_stutter (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hs : Lineage R s) (c d : Choice) (cw : CwPort) (ccw : CcwPort)
    (he : s.cfg e = .interior (.decl c))
    (hd : s.cfg (rn R e) = .root d cw ccw) (hf : ccw ≠ .free) :
    wordOf R r (ghostStep R s e) = wordOf R r s := by
  apply wordOf_row_stutter R r s e hs
  simp [he, hd, row, hf]

private theorem fresh_init_choice (a : Agent) :
    (row (.root .race .toSend .free) a).1.choice = some .out1 := by
  cases a with
  | root c cw ccw => cases ccw <;> simp [row, resolveInit, Agent.choice]
  | interior t => cases t <;> simp [row, resolveInit, Agent.choice]

private theorem fresh_resp_choice (a : Agent) :
    (row a (.root .race .toSend .free)).2.choice = some .in0 := by
  cases a with
  | root c cw ccw => cases cw <;> simp [row, resolveResp, Agent.choice]
  | interior t => cases t <;> simp [row, resolveResp, Agent.choice]

private theorem updateHistory_choice (a : Agent) (k : Nat) (H : Nat → Option Choice)
    (c : Choice) (hc : c ≠ .race) (ha : a.choice = some c) (hh : H k = none) :
    updateHistory a k H k = some c := by
  cases a with
  | interior t => cases ha
  | root d cw ccw =>
    have hd : d = c := Option.some.inj ha
    subst d
    cases c <;> cases cw <;> cases ccw <;>
      simp_all [updateHistory, tickHistory, observeHistory, record]

private theorem tail_encode (R : RFrame) (e : Vtx R) (i : Fin R.m) :
    (placement R).root i = encode R e ↔ rootV R i = e :=
  ⟨fun h => encode_injective R h, fun h => congrArg (encode R) h⟩

private theorem head_encode (R : RFrame) (e : Vtx R) (i : Fin R.m) :
    (placement R).root i = (placement R).physicalRing.rightNeighbor (encode R e) ↔
      rootV R i = rn R e := by
  rw [← encode_rn]
  exact ⟨fun h => encode_injective R h, fun h => congrArg (encode R) h⟩

/-- POSITIVE, conditional on the displayed necessary Lineage clauses.
In fact no stutter disjunct is needed: current Race roots are fresh, so an
incident row resolves in its correct orientation. This does NOT claim the
false lineage_step closure or infer Lineage for arbitrary reachable states. -/
theorem wordOf_step (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hs : Lineage R s) :
    wordOf R r (ghostStep R s e) =
      joinedIncidenceStep (placement R) (mask R r s) (wordOf R r s) (encode R e) := by
  funext i
  cases hh : s.hist i r with
  | some c =>
    have hc := hs.histValues i r c hh
    have hw : wordOf R r s i ≠ .race := by
      cases c <;> simp_all [wordOf, choiceToWord]
    rw [joinedIncidenceStep_of_ne_race _ _ _ _ _ hw]
    simp [wordOf, hh, hist_monotone R s e i r c hh]
  | none =>
    by_cases hm : r ≤ s.k i
    · have hr : r = s.k i := by
        have hn : ¬ r < s.k i := by
          intro h
          obtain ⟨c, hc⟩ := hs.histPast i r h
          rw [hh] at hc
          cases hc
        omega
      obtain ⟨c, cw, ccw, hcfg⟩ := hs.roots i
      have hn := hs.histNow i c cw ccw hcfg
      rw [← hr, hh] at hn
      have hc : c = .race := by
        cases c
        · rfl
        · cases hn
        · cases hn
      subst c
      have hf := hs.raceReady i (by rw [hcfg]; rfl)
      have hmask : mask R r s i = true := by simp [mask, hm]
      rw [joinedIncidenceStep_of_joined _ _ _ _ _ hmask]
      have hw : wordOf R r s i = .race := by simp [wordOf, hh, choiceToWord]
      simp only [PeriodHIncidenceChoice.incidenceStep, hw, ne_eq, not_true_eq_false, if_false]
      by_cases ht : rootV R i = e
      · have hte := (tail_encode R e i).mpr ht
        simp only [hte, if_true]
        have hi : incident R e (rootV R i) := Or.inl ht
        have ha : (rawAt R s.cfg e (rootV R i)).choice = some .out1 := by
          simp only [rawAt, ht, if_true]
          rw [← ht, hf]
          exact fresh_init_choice _
        have hsaved : (ghostStep R s e).hist i r = some .out1 := by
          simp only [ghostStep, if_pos hi]
          rw [hr] at hh ⊢
          exact updateHistory_choice _ _ _ _ (by decide) ha hh
        simp [wordOf, hsaved, choiceToWord]
      · have hte : (placement R).root i ≠ encode R e := fun h => ht ((tail_encode R e i).mp h)
        simp only [hte, if_false]
        by_cases hd : rootV R i = rn R e
        · have hde := (head_encode R e i).mpr hd
          simp only [hde, if_true]
          have hi : incident R e (rootV R i) := Or.inr hd
          have ha : (rawAt R s.cfg e (rootV R i)).choice = some .in0 := by
            unfold rawAt
            rw [if_neg ht, if_pos hd]
            rw [← hd, hf]
            exact fresh_resp_choice _
          have hsaved : (ghostStep R s e).hist i r = some .in0 := by
            simp only [ghostStep, if_pos hi]
            rw [hr] at hh ⊢
            exact updateHistory_choice _ _ _ _ (by decide) ha hh
          simp [wordOf, hsaved, choiceToWord]
        · have hde : (placement R).root i ≠
              (placement R).physicalRing.rightNeighbor (encode R e) :=
            fun h => hd ((head_encode R e i).mp h)
          have hi : ¬ incident R e (rootV R i) := by
            intro h; exact h.elim ht hd
          simp [hde, wordOf, ghostStep, hi, hh, choiceToWord]
    · have hmask : mask R r s i = false := by simp [mask, hm]
      rw [joinedIncidenceStep_of_unjoined _ _ _ _ _ hmask]
      have hr : r ≠ s.k i := by omega
      by_cases hi : incident R e (rootV R i)
      · simp only [wordOf, ghostStep, if_pos hi, updateHistory_other _ _ _ _ hr]
      · simp only [wordOf, ghostStep, if_neg hi]

private theorem forall_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hv with h | h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1
  · have he : i = 2 := Fin.ext h; exact he ▸ h2

abbrev DirectFrame : RFrame := ⟨3, 1, by decide, by decide, .out1, Or.inl rfl⟩
abbrev directEdge (i : Fin 3) : Vtx DirectFrame := (i,0)
def directOne := ghostStep DirectFrame (ghostStart DirectFrame) (directEdge 0)
def directTwo := ghostStep DirectFrame directOne (directEdge 1)

theorem directOne_counters : ∀ i, directOne.k i = 0 := by
  apply forall_three <;> decide

theorem directOne_history : ∀ i r, directOne.hist i r = if r = 0 then some .out1 else none := by
  intro i r
  by_cases hr : r = 0
  · subst r
    exact hist_monotone DirectFrame (ghostStart DirectFrame) (directEdge 0) i 0 .out1 rfl
  · change (ghostStep DirectFrame (ghostStart DirectFrame) (directEdge 0)).hist i r = _
    simp only [ghostStep]
    split
    · rw [updateHistory_other _ _ _ _ (show r ≠ (ghostStart DirectFrame).k i from hr)]
      simp [ghostStart, hr]
    · simp [ghostStart, hr]

private theorem no_interior (s : GhostRing DirectFrame) (g : Fin 3) : EmptyGap DirectFrame s g := by
  intro a ha
  have hh : a.val < 1 := a.isLt
  omega

theorem directOne_lineage : Lineage DirectFrame directOne := by
  constructor
  · apply forall_three
    · exact ⟨.out1, .heldDenial, .free, rfl⟩
    · exact ⟨.out1, .toSend, .heldDenial, rfl⟩
    · exact ⟨.out1, .toSend, .free, rfl⟩
  · apply forall_three <;> decide
  · intro i r c hc
    rw [directOne_history] at hc
    split at hc
    · cases hc; decide
    · contradiction
  · intro i r hr; rw [directOne_counters] at hr; omega
  · intro i c cw ccw hc
    have hall : ∀ j, (directOne.cfg (rootV DirectFrame j)).choice = some .out1 := by
      apply forall_three <;> decide
    have hi := hall i
    rw [hc] at hi
    have he : c = .out1 := Option.some.inj hi
    subst c
    rw [directOne_counters, directOne_history]
    rfl
  · intro i r hr
    rw [directOne_counters] at hr
    simp [directOne_history, Nat.ne_of_gt hr]
  · intro i hi
    have hh : (directOne.cfg (rootV DirectFrame i)).choice ≠ some .race := by
      revert i; apply forall_three <;> decide
    exact False.elim (hh hi)
  · apply forall_three
    · exact ⟨Or.inl rfl, Or.inl rfl, rfl, rfl, no_interior _ _⟩
    · exact ⟨rfl, rfl, no_interior _ _⟩
    · exact ⟨rfl, rfl, no_interior _ _⟩
  · apply forall_three <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> decide
  · intro g r h
    have he : ∀ j, directOne.epoch j = if j = 0 then .delivered 0 .out1 .out1 else .idle := by
      apply forall_three <;> decide
    rw [he] at h
    split at h
    · have hr : r = 0 := by change r ≤ 0 at h; omega
      subst r
      exact ⟨.out1, .out1, by rw [directOne_history]; rfl, by rw [directOne_history]; rfl⟩
    · exact False.elim h
  · intro g r h
    have he : ∀ j, directOne.epoch j = if j = 0 then .delivered 0 .out1 .out1 else .idle := by
      apply forall_three <;> decide
    rw [he] at h
    split at h
    · change r < 0 at h; omega
    · exact False.elim h
  · intro i r h; rw [directOne_counters] at h; omega
  · apply forall_three
    · intro _; exact ⟨.out1, .out1, rfl, rfl, rfl⟩
    · intro h; exact False.elim h
    · intro h; exact False.elim h
  · apply forall_three
    · intro _; exact ⟨.out1, .out1, rfl, rfl, rfl⟩
    · intro h; exact False.elim h
    · intro h; exact False.elim h

/-- Exact obstruction: the owner JOINs after P1 and forgets the epoch, but
the right endpoint remains in round zero holding that comparison's denial. -/
theorem reset_loses_current_receipt :
    directTwo.k 1 = 1 ∧ directTwo.k 2 = 0 ∧ directTwo.epoch 1 = .idle ∧
    (directTwo.cfg (rootV DirectFrame 2)).ccwPort = some .heldDenial := by decide

/-- COUNTEREXAMPLE, not a preservation theorem. The pre-state is reached
by edge 0 from the clean uniform start; edge 1 violates the incoming clause. -/
theorem lineage_step : GhostReachable DirectFrame directOne ∧ Lineage DirectFrame directOne ∧
    ¬ Lineage DirectFrame (ghostStep DirectFrame directOne (directEdge 1)) := by
  refine ⟨⟨[directEdge 0], rfl⟩, directOne_lineage, ?_⟩
  intro hs
  have h := (hs.incoming 1).mp (show CcwHeld
    ((ghostStep DirectFrame directOne (directEdge 1)).cfg
      (rootV DirectFrame (next DirectFrame 1))).ccwPort from trivial)
  exact h

/-- The failure is physical clean reachability too, not only a ghost trace. -/
theorem reset_witness_reachable : GhostReachable DirectFrame directTwo ∧
    Reachable DirectFrame (physical DirectFrame directTwo) := by
  have hr : GhostReachable DirectFrame directTwo := ⟨[directEdge 0, directEdge 1], rfl⟩
  exact ⟨hr, reachable_erases _ _ hr⟩

/-- Bounded physical scan; no choice principle or unbounded search. -/
def tokenPos (R : RFrame) (s : GhostRing R) (g : Fin R.m) : Nat :=
  ((List.finRange R.h).find? (fun a => decide (0 < a.val) &&
    match s.cfg (g,a) with
    | .interior (.decl _) | .interior (.reply _) => true
    | _ => false)).map Fin.val |>.getD 0

/-- Literal requested projection, including idle -> delivered and Nat r-1.
The retaining alternative instead asks for latent when idle/older, and a special predecessor at 0. -/
def tokensOf (R : RFrame) (r : Nat) (s : GhostRing R) (g : Fin R.m) : LitGapState R.h :=
  match s.epoch g with
  | .outbound t _ =>
    if t = r - 1 then ofPhase R (.declAt (tokenPos R s g)) else .delivered
  | .returning t _ _ =>
    if t = r - 1 then ofPhase R (.replyAt (tokenPos R s g)) else .delivered
  | _ => .delivered

def IrrelevantEpoch (r : Nat) : GapEpoch → Prop
  | .outbound t _ | .returning t _ _ => t ≠ r - 1
  | _ => True

theorem tokensOf_irrelevant (R : RFrame) (r : Nat) (s : GhostRing R) (g : Fin R.m)
    (h : IrrelevantEpoch r (s.epoch g)) : tokensOf R r s g = .delivered := by
  cases he : s.epoch g <;> simp only [he, IrrelevantEpoch] at h
  all_goals simp [tokensOf, he, h]

/-- Other-round carrier activity stutters when BOTH old and new views are
irrelevant. A later label on only one endpoint is not such a certificate. -/
theorem tokensOf_side_stutter (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (h0 : ∀ g, IrrelevantEpoch r (s.epoch g))
    (h1 : ∀ g, IrrelevantEpoch r ((ghostStep R s e).epoch g)) :
    tokensOf R r (ghostStep R s e) = tokensOf R r s := by
  funext g
  rw [tokensOf_irrelevant R r _ g (h1 g), tokensOf_irrelevant R r _ g (h0 g)]

abbrev LongFrame : RFrame := ⟨3, 2, by decide, by decide, .out1, Or.inl rfl⟩
abbrev firstEdge : Vtx LongFrame := (0,0)

/-- COUNTEREXAMPLE, even allowing a stutter: the first launch creates live
debt from the projection's delivered state. A delivered token cannot advance. -/
theorem tokensOf_step : GhostReachable LongFrame (ghostStart LongFrame) ∧
    Lineage LongFrame (ghostStart LongFrame) ∧
    ¬ (tokensOf LongFrame 1 (ghostStep LongFrame (ghostStart LongFrame) firstEdge) =
      multiLitLocalStep (layout LongFrame) (tokensOf LongFrame 1 (ghostStart LongFrame))
        (encode LongFrame firstEdge) ∨
      tokensOf LongFrame 1 (ghostStep LongFrame (ghostStart LongFrame) firstEdge) =
        tokensOf LongFrame 1 (ghostStart LongFrame)) := by
  refine ⟨⟨[], rfl⟩, lineage_start _, ?_⟩
  intro h
  rcases h with h | h
  · have hh := congrArg (fun f => (f 0).hops) h
    change 2 = 0 at hh
    omega
  · have hh := congrArg (fun f => (f 0).hops) h
    change 2 = 0 at hh
    omega

#print axioms lineage_step
#print axioms neighborSkew_of_lineage
#print axioms provenance_of_lineage
#print axioms join_requires_neighbors_of_lineage
#print axioms neighborSkew_step_of_lineage
#print axioms wordOf_step
#print axioms tokensOf_step
#print axioms virtualCandidate_persists
#print axioms virtualCandidate_pins
#print axioms virtualCandidate_locks_of_lineage_run

/-!
Stall boundary: universal lineage preservation and the requested total token
simulation are refuted above, including their stuttering versions where
applicable. The retained delivered epochs and latent token view would
change the hard-specified definitions, so neither repair is substituted here.
Unconditional virtualCandidate_locks for every future physical execution is
not proved. virtualCandidate_locks_of_lineage_run explicitly requires final
Lineage; removing that premise needs a separately preserved selected-gap
invariant or a repaired full lineage lift. No physical realization bound or
new Bellman budget is claimed by this file.
-/

end ShortGapLineage
