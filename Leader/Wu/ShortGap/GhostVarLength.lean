import Leader.Wu.ShortGap.StrictRoundService
import Leader.Wu.ShortGap.VarRingDebt
import Leader.Wu.ShortGap.GapTiling

/-!
# Literal ghosts on gaps of varying lengths

A vertex is a dependent pair: gap g and position in Fin (len g).
Only geometry and local transport positions depend on length. Physical rows,
JOIN, history recording, and the two-epoch event order are unchanged.
-/
namespace ShortGapGhostVarLength
open ShortGapLiteralGapRows
open ShortGapLineage (GapEpoch resolvedOpt updateHistory rowEpoch ComparedAt DeliveredAt Live
  CcwHeld CwHeld BeforeLatest choiceToWord)
open ShortGapLineageRetained (CurrentResult)
open ShortGapTwoEpoch (GapLineage CurrentTag PreviousResult compares)
open ShortGapOwnerRoundSlice (joinReady joinTick)
open ShortGapDenialTransportLiteral (LitGapState)
open FiniteUniformStoppingTree
set_option autoImplicit false

/-- The physical size is the sum of the positive gap lengths. Sigma
coordinates supply gap noninterference without a protocol assumption. -/
structure VFrame where
  m : Nat
  n : Nat
  len : Fin m → Nat
  hm : 2 ≤ m
  len_pos : ∀ g, 0 < len g
  total : (List.ofFn len).sum = n
  b : Choice
  hb : IsBase b

abbrev Vtx (R : VFrame) := (g : Fin R.m) × Fin (R.len g)

theorem vtx_eq (R : VFrame) (v w : Vtx R) (hg : v.1 = w.1)
    (ha : v.2.val = w.2.val) : v = w := by
  obtain ⟨g,a⟩ := v
  obtain ⟨j,b⟩ := w
  dsimp only at hg ha
  subst j
  have h : a = b := Fin.ext ha
  cases h
  rfl

theorem gap_noninterference (R : VFrame) (g j : Fin R.m)
    (a : Fin (R.len g)) (b : Fin (R.len j)) (h : (⟨g,a⟩ : Vtx R) = ⟨j,b⟩) :
    g = j ∧ a.val = b.val :=
  ⟨congrArg Sigma.fst h,congrArg (fun v : Vtx R => v.2.val) h⟩

/-- Exact maximum length, rather than an arbitrary external cap. -/
def hMax (R : VFrame) : Nat := ShortGapLineage2Closure.generationMax R.len

theorem len_le_hMax (R : VFrame) (g : Fin R.m) : R.len g ≤ hMax R :=
  ShortGapLineage2Closure.le_generationMax R.len g

theorem m_le_n (R : VFrame) : R.m ≤ R.n := by
  have h := ofFn_sum_le (fun _ : Fin R.m => 1) R.len R.len_pos
  simpa only [ofFn_sum_const,Nat.mul_one,R.total] using h

theorem n_pos (R : VFrame) : 0 < R.n := by have := m_le_n R; have := R.hm; omega

theorem sum_two_len_sub_one_add_m (R : VFrame) :
    (List.ofFn (fun g => 2*R.len g-1)).sum + R.m = 2*R.n := by
  have h := VariableGap.sum_ofFn_twice_sub_one_add_card R.len R.len_pos
  simpa only [VariableGap.sumOfFn,R.total] using h

theorem sum_two_len_sub_one (R : VFrame) :
    (List.ofFn (fun g => 2*R.len g-1)).sum = 2*R.n-R.m := by
  have := sum_two_len_sub_one_add_m R
  omega

/-- Uniform frames embed without changing their physical size. -/
def ofUniform (R : ShortGapLiteralRingRows.RFrame) : VFrame where
  m := R.m
  n := R.n
  len _ := R.h
  hm := R.hm
  len_pos _ := R.hh
  total := ofFn_sum_const _ _
  b := R.b
  hb := R.hb

/-- The placement route supplies only geometry. RootsOrdered does not
appear in any ghost transition or lineage clause. -/
def ofPlacement {n m : Nat} (ring : DirectedRing m)
    (P : PeriodHIncidenceChoice.Placement n m)
    (hord : ShortGapDenialTransportPlacement.RootsOrdered ring P)
    (hm : 2 ≤ m) (b : Choice) (hb : IsBase b) : VFrame where
  m := m
  n := n
  len := ShortGapDenialTransportPlacement.gapLen ring P
  hm := hm
  len_pos := ShortGapDenialTransportPlacement.gapLen_pos ring P hm
  total := ShortGapGapTiling.gapLen_sum_eq ring P hord hm
  b := b
  hb := hb

/-- Cyclic neighbors belong to the root ring, independently of length. -/
def next (R : VFrame) (g : Fin R.m) : Fin R.m :=
  ⟨if g.val+1 < R.m then g.val+1 else 0,by have := g.isLt; have := R.hm; split <;> omega⟩

def prev (R : VFrame) (g : Fin R.m) : Fin R.m :=
  ⟨if g.val=0 then R.m-1 else g.val-1,by have := g.isLt; have := R.hm; split <;> omega⟩

theorem next_ne_self (R : VFrame) (g : Fin R.m) : next R g ≠ g := by
  intro h
  have he := congrArg Fin.val h
  unfold next at he
  dsimp only at he
  split at he <;> have := g.isLt <;> have := R.hm <;> omega

theorem prev_next (R : VFrame) (g : Fin R.m) : prev R (next R g) = g := by
  apply Fin.ext
  simp only [prev,next]
  have := g.isLt
  have := R.hm
  split <;> split <;> omega

theorem next_prev (R : VFrame) (g : Fin R.m) : next R (prev R g) = g := by
  apply Fin.ext
  simp only [prev,next]
  have := g.isLt
  have := R.hm
  split <;> split <;> omega

abbrev rootV (R : VFrame) (g : Fin R.m) : Vtx R := ⟨g,⟨0,R.len_pos g⟩⟩

/-- The last edge of gap g ends at position zero of the next gap,
whose length need not equal len g. -/
def rn (R : VFrame) (v : Vtx R) : Vtx R :=
  if h : v.2.val+1 < R.len v.1 then ⟨v.1,⟨v.2.val+1,h⟩⟩ else rootV R (next R v.1)

theorem rn_of_lt (R : VFrame) (v : Vtx R) (h : v.2.val+1 < R.len v.1) :
    rn R v = ⟨v.1,⟨v.2.val+1,h⟩⟩ := by simp [rn,h]

theorem rn_of_last (R : VFrame) (v : Vtx R) (h : ¬ v.2.val+1 < R.len v.1) :
    rn R v = rootV R (next R v.1) := by simp [rn,h]

theorem rn_ne_self (R : VFrame) (v : Vtx R) : rn R v ≠ v := by
  intro he
  by_cases h : v.2.val+1 < R.len v.1
  · rw [rn_of_lt R v h] at he
    have := congrArg (fun w : Vtx R => w.2.val) he
    dsimp only at this
    omega
  · rw [rn_of_last R v h] at he
    exact next_ne_self R v.1 (congrArg Sigma.fst he)

/-! The literal row and JOIN layer. -/

def rawAt (R : VFrame) (cfg : Vtx R → Agent) (e w : Vtx R) : Agent :=
  if w = e then (row (cfg e) (cfg (rn R e))).1
  else if w = rn R e then (row (cfg e) (cfg (rn R e))).2 else cfg w

def incident (R : VFrame) (e w : Vtx R) : Prop := w = e ∨ w = rn R e
instance (R : VFrame) (e w : Vtx R) : Decidable (incident R e w) :=
  inferInstanceAs (Decidable (w=e ∨ w=rn R e))

def ringStepU (R : VFrame) (cfg : Vtx R → Agent) (e : Vtx R) : Vtx R → Agent :=
  fun w => if incident R e w then (joinTick (rawAt R cfg e w) 0).1 else cfg w

structure SliceState (R : VFrame) where
  cfg : Vtx R → Agent
  k : Fin R.m → Nat

def fires (R : VFrame) (s : SliceState R) (e : Vtx R) (i : Fin R.m) : Bool :=
  decide (incident R e (rootV R i)) && joinReady (rawAt R s.cfg e (rootV R i))

def liftedStep (R : VFrame) (s : SliceState R) (e : Vtx R) : SliceState R where
  cfg := ringStepU R s.cfg e
  k i := s.k i + if fires R s e i then 1 else 0

abbrev History (R : VFrame) := Fin R.m → Nat → Option Choice

structure GhostRing (R : VFrame) where
  cfg : Vtx R → Agent
  k : Fin R.m → Nat
  hist : History R
  epoch : Fin R.m → GapEpoch

def physical (R : VFrame) (s : GhostRing R) : SliceState R := ⟨s.cfg,s.k⟩

def rawEpochs (R : VFrame) (s : GhostRing R) (e : Vtx R) (g : Fin R.m) : GapEpoch :=
  if g=e.1 then rowEpoch (s.k g) (s.epoch g) (s.cfg e) (s.cfg (rn R e)) else s.epoch g

def ghostStep (R : VFrame) (s : GhostRing R) (e : Vtx R) : GhostRing R where
  cfg := (liftedStep R (physical R s) e).cfg
  k := (liftedStep R (physical R s) e).k
  hist i := if incident R e (rootV R i) then
    updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i) else s.hist i
  epoch g := if fires R (physical R s) e g then .idle else rawEpochs R s e g

def ghostStart (R : VFrame) : GhostRing R where
  cfg v := if v.2.val=0 then .root R.b .toSend .free else .interior .empty
  k _ := 0
  hist _ q := if q=0 then some R.b else none
  epoch _ := .idle
def prefixView (R : VFrame) (s : GhostRing R) : GhostRing R :=
  { s with epoch := fun g => match s.epoch g with
    | .idle => if s.k g = 0 then .idle else
        .delivered (s.k g - 1) ((s.hist g (s.k g - 1)).getD .race)
          ((s.hist (next R g) (s.k g - 1)).getD .race)
    | E => E }

def EmptyGap (R : VFrame) (s : GhostRing R) (g : Fin R.m) : Prop :=
  ∀ a : Fin (R.len g), 0 < a.val → s.cfg ⟨g,a⟩ = .interior .empty

/-- Existence of one position and emptiness of every other interior slot. -/
def OneToken (R : VFrame) (s : GhostRing R) (g : Fin R.m) (token : Slot) : Prop :=
  ∃ p : Fin (R.len g), 0 < p.val ∧
    ∀ a : Fin (R.len g), 0 < a.val → s.cfg ⟨g,a⟩ = .interior (if a = p then token else .empty)

def EpochShape (R : VFrame) (s : GhostRing R) (g : Fin R.m) : Prop :=
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

def HistoricalDenial (R : VFrame) (s : GhostRing R) (g : Fin R.m) (r : Nat) : Prop :=
  ∃ c d, s.hist g r = some c ∧ s.hist (next R g) r = some d ∧ res c d = .denial

/-- History, shape, current receipt, and completed-prefix clauses.
No skew, provenance, simulation, closure, or candidate-lock conclusion is a
field. Exact receipt values are indexed by the receiving endpoint's CURRENT
round. These clauses fail under the requested epoch reset. -/
structure Lineage (R : VFrame) (s : GhostRing R) : Prop where
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

theorem lineage_start (R : VFrame) : Lineage R (ghostStart R) := by
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
    intro a ha; simp [ghostStart, Nat.ne_of_gt ha]
  · intro g; exact ⟨(fun h => nomatch h), False.elim⟩
  · intro g; exact Iff.rfl
  · intro g; exact Iff.rfl
  · intro g r h; exact False.elim h
  · intro g r h; exact False.elim h
  · intro i r h; change r < 0 at h; omega
  · intro g h; exact False.elim h
  · intro g h; exact False.elim h

/-- Skew is derived from epoch endpoint ranges, not a Lineage field. -/
structure GhostRing2 (R : VFrame) where
  cfg : Vtx R → Agent
  k : Fin R.m → Nat
  hist : History R
  epoch : Fin R.m → GapLineage

/-- Erase the previous archive when an API only reads physical fields or
the owner's current transaction. -/
def curView (R : VFrame) (s : GhostRing2 R) : GhostRing R :=
  ⟨s.cfg,s.k,s.hist,fun g => (s.epoch g).cur⟩

private theorem curView_epoch (R : VFrame) (s : GhostRing2 R) (g : Fin R.m) :
    (curView R s).epoch g = (s.epoch g).cur := rfl

/-- The newest stored epoch determines the completed historical prefix.
An idle cur can expose prev, but a new outbound never destroys prev. -/
def combinedView (R : VFrame) (s : GhostRing2 R) : GhostRing R :=
  ⟨s.cfg,s.k,s.hist,fun g => match (s.epoch g).cur with
    | .idle => (s.epoch g).prev
    | E => E⟩

def physical2 (R : VFrame) (s : GhostRing2 R) : SliceState R := ⟨s.cfg,s.k⟩

/-- Event order: raw annotation, owner transfer, right-root retirement.
The unconditional owner transfer follows the spec even if the right root
cleared this result earlier; current-generation port tests ignore such a
stale previous result. No extra guard is silently added to the transfer. -/
def epochStep2 (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m) : GapLineage :=
  let old := s.epoch g
  let current := rawEpochs R (curView R s) e g
  let previous := if g = e.1 ∧ compares (s.cfg e) (s.cfg (rn R e)) = true
    then .idle else old.prev
  let joined := if fires R (physical2 R s) e g then
    {prev := current, cur := .idle} else {prev := previous, cur := current}
  if fires R (physical2 R s) e (next R g) then {joined with prev := .idle} else joined

def ghostStep2 (R : VFrame) (s : GhostRing2 R) (e : Vtx R) : GhostRing2 R where
  cfg := (ghostStep R (curView R s) e).cfg
  k := (ghostStep R (curView R s) e).k
  hist := (ghostStep R (curView R s) e).hist
  epoch := epochStep2 R s e

def ghostStart2 (R : VFrame) : GhostRing2 R :=
  ⟨(ghostStart R).cfg,(ghostStart R).k,(ghostStart R).hist,fun _ => ⟨.idle,.idle⟩⟩

def PrevShape (R : VFrame) (s : GhostRing2 R) (g : Fin R.m) : Prop :=
  match (s.epoch g).prev with
  | .idle => True
  | .delivered q c d => s.k g = q+1 ∧
      (s.k (next R g) = q ∨ s.k (next R g) = q+1) ∧
      s.hist g q = some c ∧ s.hist (next R g) q = some d
  | _ => False

/-- Physical history/shape coherence is interpreted through the newest
record and its completed prefix. No closure, skew, row simulation or debt
law is stored as a field. Live-token uniqueness is already part of the
coherent epoch shape and is exposed by current_token_shape below. -/
structure Lineage2 (R : VFrame) (s : GhostRing2 R) : Prop where
  coherent : Lineage R (prefixView R (combinedView R s))
  previous : ∀ g, PrevShape R s g
  current : ∀ g, CurrentTag (s.k g) (s.epoch g).cur
  idleSend : ∀ g, (s.epoch g).cur = .idle →
    (s.cfg (rootV R g)).cwPort = some .toSend
  waiting : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live (s.epoch g).cur
  incoming : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g).cur (s.k (next R g)) ∨
    PreviousResult (s.epoch g).prev (s.k (next R g))

theorem lineage2_start (R : VFrame) : Lineage2 R (ghostStart2 R) := by
  refine ⟨lineage_start R, ?_, ?_, ?_, ?_, ?_⟩
  · intro g; trivial
  · intro g; trivial
  · intro g _; rfl
  · intro g
    constructor
    · intro h; cases h
    · intro h; exact False.elim h
  · intro g; exact ⟨False.elim,fun h => h.elim id id⟩

abbrev view (R : VFrame) (s : GhostRing2 R) := prefixView R (combinedView R s)

/-- C0: root roles, normalized ports, and the fresh form of Race roots. -/
structure C0 (R : VFrame) (s : GhostRing2 R) : Prop where
  roots : ∀ i, ∃ c cw ccw, s.cfg (rootV R i) = .root c cw ccw
  normalized : ∀ i, joinReady (s.cfg (rootV R i)) = false
  raceReady : ∀ i, (s.cfg (rootV R i)).choice = some .race →
    s.cfg (rootV R i) = .root .race .toSend .free

/-- C1: full epoch shape, including unique token position, endpoint
generation ranges, and the payloads represented by that epoch. -/
def C1 (R : VFrame) (s : GhostRing2 R) : Prop := ∀ g, EpochShape R (view R s) g

/-- C2: owner ports, exact outgoing values, and current-epoch agreement. -/
structure C2 (R : VFrame) (s : GhostRing2 R) : Prop where
  waitingPrefix : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live ((view R s).epoch g)
  outgoing : ∀ g, CwHeld (s.cfg (rootV R g)).cwPort ↔ DeliveredAt ((view R s).epoch g) (s.k g)
  outgoingValue : ∀ g, DeliveredAt ((view R s).epoch g) (s.k g) →
    ∃ c d, s.hist g (s.k g) = some c ∧ s.hist (next R g) (s.k g) = some d ∧
      (s.cfg (rootV R g)).cwPort = some (resCw c d)
  idleSend : ∀ g, (s.epoch g).cur = .idle → (s.cfg (rootV R g)).cwPort = some .toSend
  waiting : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live (s.epoch g).cur

/-- C3: both historical and two-epoch right-port readings, with exact values. -/
structure C3 (R : VFrame) (s : GhostRing2 R) : Prop where
  incomingPrefix : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    ComparedAt ((view R s).epoch g) (s.k (next R g))
  incomingValue : ∀ g, ComparedAt ((view R s).epoch g) (s.k (next R g)) →
    ∃ c d, s.hist g (s.k (next R g)) = some c ∧ s.hist (next R g) (s.k (next R g)) = some d ∧
      (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)
  incoming : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g).cur (s.k (next R g)) ∨ PreviousResult (s.epoch g).prev (s.k (next R g))

/-- C4: exact history domain and non-Race recorded values. -/
structure C4 (R : VFrame) (s : GhostRing2 R) : Prop where
  values : ∀ i r c, s.hist i r = some c → c ≠ .race
  past : ∀ i r, r < s.k i → ∃ c, s.hist i r = some c
  now : ∀ i c cw ccw, s.cfg (rootV R i) = .root c cw ccw → s.hist i (s.k i) = resolvedOpt c
  future : ∀ i r, s.k i < r → s.hist i r = none

/-- C5 retains the original previous-result condition verbatim. A stale
previous result may belong to the right root's immediately prior round. -/
def C5 (R : VFrame) (s : GhostRing2 R) : Prop := ∀ g, PrevShape R s g

/-- C6 binds current epochs to their owner's generation. -/
def C6 (R : VFrame) (s : GhostRing2 R) : Prop := ∀ g, CurrentTag (s.k g) (s.epoch g).cur

/-- C7: completed payloads, strict-prefix denials, and both denials
required for every completed owner round. -/
structure C7 (R : VFrame) (s : GhostRing2 R) : Prop where
  payloads : ∀ g r, ComparedAt ((view R s).epoch g) r →
    ∃ c d, s.hist g r = some c ∧ s.hist (next R g) r = some d
  denials : ∀ g r, BeforeLatest ((view R s).epoch g) r → HistoricalDenial R (view R s) g r
  joined : ∀ i r, r < s.k i →
    DeliveredAt ((view R s).epoch i) r ∧ ComparedAt ((view R s).epoch (prev R i)) r ∧
    HistoricalDenial R (view R s) i r ∧ HistoricalDenial R (view R s) (prev R i) r

def Clauses (R : VFrame) (s : GhostRing2 R) : Prop :=
  C0 R s ∧ C1 R s ∧ C2 R s ∧ C3 R s ∧ C4 R s ∧ C5 R s ∧ C6 R s ∧ C7 R s

/-- Every original field occurs in the decomposition, in both directions. -/
theorem lineage2_iff_clauses (R : VFrame) (s : GhostRing2 R) : Lineage2 R s ↔ Clauses R s := by
  constructor
  · intro h
    exact ⟨⟨h.coherent.roots,h.coherent.normalized,h.coherent.raceReady⟩,h.coherent.shape,
      ⟨h.coherent.waiting,h.coherent.outgoing,h.coherent.outgoingValue,h.idleSend,h.waiting⟩,
      ⟨h.coherent.incoming,h.coherent.incomingValue,h.incoming⟩,
      ⟨h.coherent.histValues,h.coherent.histPast,h.coherent.histNow,h.coherent.histFuture⟩,
      h.previous,h.current,⟨h.coherent.prefixPayloads,h.coherent.prefixDenials,h.coherent.joinedDenials⟩⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨⟨h0.roots,h0.normalized,h4.values,h4.past,h4.now,h4.future,h0.raceReady,h1,
      h2.waitingPrefix,h2.outgoing,h3.incomingPrefix,h7.payloads,h7.denials,h7.joined,
      h2.outgoingValue,h3.incomingValue⟩,h5,h6,h2.idleSend,h2.waiting,h3.incoming⟩



open ShortGapCurrentCohort (record tickHistory record_monotone)
open ShortGapLineage (observeHistory)

theorem ghostStep2_physical (R : VFrame) (s : GhostRing2 R) (e : Vtx R) :
    (ghostStep2 R s e).cfg = ringStepU R s.cfg e := rfl

theorem ghostStep2_erases (R : VFrame) (s : GhostRing2 R) (e : Vtx R) :
    physical2 R (ghostStep2 R s e) = liftedStep R (physical2 R s) e := rfl

theorem ghostStep2_k (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m) :
    (ghostStep2 R s e).k g = s.k g + if fires R (physical2 R s) e g then 1 else 0 := rfl

theorem epochStep2_cur (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m) :
    (epochStep2 R s e g).cur =
      if fires R (physical2 R s) e g then .idle else rawEpochs R (curView R s) e g := by
  simp only [epochStep2]
  split <;> split <;> rfl
private theorem resolveInit_fixed (c : Choice) (hc : c ≠ .race) : resolveInit c = c := by
  cases c <;> simp_all [resolveInit]

private theorem resolveResp_fixed (c : Choice) (hc : c ≠ .race) : resolveResp c = c := by
  cases c <;> simp_all [resolveResp]

private theorem left_root (c : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent) :
    ∃ d dw dd, (row (.root c cw ccw) b).1 = .root d dw dd ∧ (c ≠ .race → d = c) := by
  cases b with
  | interior t =>
    cases t <;> cases cw <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals refine ⟨_,_,_,rfl,?_⟩
    all_goals first | exact fun _ => rfl | exact resolveInit_fixed c
  | root d dw dd =>
    cases cw <;> cases dd <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals exact ⟨_,_,_,rfl,resolveInit_fixed c⟩

private theorem right_root (a : Agent) (c : Choice) (cw : CwPort) (ccw : CcwPort) :
    ∃ d dw dd, (row a (.root c cw ccw)).2 = .root d dw dd ∧ (c ≠ .race → d = c) := by
  cases a with
  | interior t =>
    cases t <;> cases ccw <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals refine ⟨_,_,_,rfl,?_⟩
    all_goals first | exact fun _ => rfl | exact resolveResp_fixed c
  | root d dw dd =>
    cases dw <;> cases ccw <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals refine ⟨_,_,_,rfl,?_⟩
    all_goals first | exact fun _ => rfl | exact resolveResp_fixed c

private theorem left_fresh_choice (a : Agent) :
    (row (.root .race .toSend .free) a).1.choice = some .out1 := by
  cases a with
  | root c cw ccw => cases ccw <;> simp [row,resolveInit,Agent.choice]
  | interior t => cases t <;> simp [row,resolveInit,Agent.choice]

private theorem right_fresh_choice (a : Agent) :
    (row a (.root .race .toSend .free)).2.choice = some .in0 := by
  cases a with
  | root c cw ccw => cases cw <;> simp [row,resolveResp,Agent.choice]
  | interior t => cases t <;> simp [row,resolveResp,Agent.choice]

/-- The raw endpoint has a resolved choice and agrees with every
previously recorded current choice. This covers all literal row kinds. -/
theorem raw_root_resolved (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hi : incident R e (rootV R i)) :
    ∃ d cw ccw, rawAt R s.cfg e (rootV R i) = .root d cw ccw ∧ d ≠ .race ∧
      (s.hist i (s.k i) = none ∨ s.hist i (s.k i) = some d) := by
  obtain ⟨c,cw,ccw,hc⟩ := hs.coherent.roots i
  change s.cfg (rootV R i) = .root c cw ccw at hc
  have hh := hs.coherent.histNow i c cw ccw hc
  change s.hist i (s.k i) = resolvedOpt c at hh
  have hraw : ∃ d dw dd, rawAt R s.cfg e (rootV R i) = .root d dw dd ∧
      (c ≠ .race → d = c) ∧ (c = .race → d ≠ .race) := by
    by_cases ht : rootV R i = e
    · obtain ⟨d,dw,dd,hr,hd⟩ := left_root c cw ccw (s.cfg (rn R e))
      refine ⟨d,dw,dd,?_,hd,?_⟩
      · have hce : s.cfg e = .root c cw ccw := ht ▸ hc
        rw [rawAt,if_pos ht,hce,hr]
      · intro hcr
        have hf := hs.coherent.raceReady i (by change (s.cfg (rootV R i)).choice = _; rw [hc,hcr]; rfl)
        change s.cfg (rootV R i) = .root .race .toSend .free at hf
        have heq := hc.symm.trans hf
        cases heq
        have hx := left_fresh_choice (s.cfg (rn R e))
        rw [hr] at hx
        have hdv : d = .out1 := Option.some.inj hx
        rw [hdv]; intro h; cases h
    · have ht' : rootV R i = rn R e := hi.resolve_left ht
      obtain ⟨d,dw,dd,hr,hd⟩ := right_root (s.cfg e) c cw ccw
      refine ⟨d,dw,dd,?_,hd,?_⟩
      · have hce : s.cfg (rn R e) = .root c cw ccw := ht' ▸ hc
        rw [rawAt,if_neg ht,if_pos ht',hce,hr]
      · intro hcr
        have hf := hs.coherent.raceReady i (by change (s.cfg (rootV R i)).choice = _; rw [hc,hcr]; rfl)
        change s.cfg (rootV R i) = .root .race .toSend .free at hf
        have heq := hc.symm.trans hf
        cases heq
        have hx := right_fresh_choice (s.cfg e)
        rw [hr] at hx
        have hdv : d = .in0 := Option.some.inj hx
        rw [hdv]; intro h; cases h
  obtain ⟨d,dw,dd,hr,hd,hfresh⟩ := hraw
  refine ⟨d,dw,dd,hr,?_,?_⟩
  · by_cases hcr : c = .race
    · exact hfresh hcr
    · rw [hd hcr]; exact hcr
  · by_cases hcr : c = .race
    · exact Or.inl (by simpa [hcr,resolvedOpt] using hh)
    · right
      rw [hd hcr]
      cases c <;> simp_all [resolvedOpt]

/-- All roots remain roots, JOIN-normalized, and fresh whenever Race. -/
theorem C0_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C0 R (ghostStep2 R s e) := by
  have hp : ∀ i, (∃ c cw ccw, (ghostStep2 R s e).cfg (rootV R i) = .root c cw ccw) ∧
      joinReady ((ghostStep2 R s e).cfg (rootV R i)) = false ∧
      (((ghostStep2 R s e).cfg (rootV R i)).choice = some .race →
        (ghostStep2 R s e).cfg (rootV R i) = .root .race .toSend .free) := by
    intro i
    by_cases hi : incident R e (rootV R i)
    · obtain ⟨c,cw,ccw,hr,hc,_⟩ := raw_root_resolved R s hs e i hi
      have he : (ghostStep2 R s e).cfg (rootV R i) = ShortGapLiteralRingRows.joinA (.root c cw ccw) := by
        rw [ghostStep2_physical]
        simp only [ringStepU,if_pos hi,joinTick,hr]
      rw [he]
      cases c <;> cases cw <;> cases ccw <;>
        simp_all [ShortGapLiteralRingRows.joinA,joinReady,Agent.choice]
    · have he : (ghostStep2 R s e).cfg (rootV R i) = s.cfg (rootV R i) := by
        rw [ghostStep2_physical]
        exact if_neg hi
      rw [he]
      exact ⟨hs.coherent.roots i,hs.coherent.normalized i,hs.coherent.raceReady i⟩
  exact ⟨fun i => (hp i).1,fun i => (hp i).2.1,fun i => (hp i).2.2⟩

private theorem record_record (H : Nat → Option Choice) (k : Nat) (d : Choice) :
    record (record H k d) k d = record H k d := by
  funext r
  by_cases hr : r = k
  · subst r
    cases hh : H k <;> simp [record,hh]
  · simp [record,hr]

private theorem updateHistory_resolved (d : Choice) (cw : CwPort) (ccw : CcwPort)
    (hd : d ≠ .race) (k : Nat) (H : Nat → Option Choice) :
    updateHistory (.root d cw ccw) k H = record H k d := by
  cases d <;> cases cw <;> cases ccw <;>
    simp_all [updateHistory,observeHistory,tickHistory,record_record]

theorem history_step_record (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (i : Fin R.m) (hi : incident R e (rootV R i)) (d : Choice) (cw : CwPort) (ccw : CcwPort)
    (hr : rawAt R s.cfg e (rootV R i) = .root d cw ccw) (hd : d ≠ .race) :
    (ghostStep2 R s e).hist i = record (s.hist i) (s.k i) d := by
  change (if incident R e (rootV R i) then updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i)
    else s.hist i) = _
  rw [if_pos hi,hr,updateHistory_resolved d cw ccw hd]

private theorem record_current (H : Nat → Option Choice) (k : Nat) (d : Choice)
    (hh : H k = none ∨ H k = some d) : record H k d k = some d := by
  rcases hh with hh | hh <;> simp [record,hh]

/-- Every history clause is preserved, including exact current and future
domains after each of the four possible endpoint JOIN combinations. -/
theorem C4_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C4 R (ghostStep2 R s e) := by
  have hh : ∀ i, (∀ r c, (ghostStep2 R s e).hist i r = some c → c ≠ .race) ∧
      (∀ r, r < (ghostStep2 R s e).k i → ∃ c, (ghostStep2 R s e).hist i r = some c) ∧
      (∀ c cw ccw, (ghostStep2 R s e).cfg (rootV R i) = .root c cw ccw →
        (ghostStep2 R s e).hist i ((ghostStep2 R s e).k i) = resolvedOpt c) ∧
      (∀ r, (ghostStep2 R s e).k i < r → (ghostStep2 R s e).hist i r = none) := by
    intro i
    by_cases hi : incident R e (rootV R i)
    · obtain ⟨d,cw,ccw,hraw,hd,hcur⟩ := raw_root_resolved R s hs e i hi
      have hhist := history_step_record R s e i hi d cw ccw hraw hd
      have hcfg : (ghostStep2 R s e).cfg (rootV R i) = ShortGapLiteralRingRows.joinA (.root d cw ccw) := by
        rw [ghostStep2_physical]
        simp only [ringStepU,if_pos hi,joinTick,hraw]
      have hk : (ghostStep2 R s e).k i = s.k i + if joinReady (.root d cw ccw) then 1 else 0 := by
        rw [ghostStep2_k]
        simp [fires,physical2,hi,hraw]
      rw [hhist,hcfg,hk]
      refine ⟨?_,?_,?_,?_⟩
      · intro r c hc
        unfold record at hc
        split at hc
        · cases hc; exact hd
        · exact hs.coherent.histValues i r c hc
      · intro r hr
        by_cases hlt : r < s.k i
        · obtain ⟨c,hc⟩ := hs.coherent.histPast i r hlt
          exact ⟨c,record_monotone _ _ _ _ _ hc⟩
        · have heq : r = s.k i := by split at hr <;> omega
          subst r
          exact ⟨d,record_current _ _ _ hcur⟩
      · intro c cwa ccwa hc
        have hn : record (s.hist i) (s.k i) d (s.k i+1) = none := by
          have hf := hs.coherent.histFuture i (s.k i+1) (Nat.lt_succ_self _)
          change s.hist i (s.k i+1) = none at hf
          simp [record,hf]
        have hz := record_current (s.hist i) (s.k i) d hcur
        cases cw <;> cases ccw <;>
          simp only [ShortGapLiteralRingRows.joinA,joinReady,Bool.false_eq_true,if_false,if_true,Nat.add_zero] at hc ⊢
        all_goals cases hc
        all_goals first | exact hn | (cases d <;> simp_all [resolvedOpt])
      · intro r hr
        have hlt : s.k i < r := by split at hr <;> omega
        have hf := hs.coherent.histFuture i r hlt
        change s.hist i r = none at hf
        simp [record,Nat.ne_of_gt hlt,hf]
    · have hf : fires R (physical2 R s) e i = false := by simp [fires,hi]
      have hhist : (ghostStep2 R s e).hist i = s.hist i := by
        change (if incident R e (rootV R i) then _ else _) = _
        exact if_neg hi
      have hcfg : (ghostStep2 R s e).cfg (rootV R i) = s.cfg (rootV R i) := by
        rw [ghostStep2_physical]; exact if_neg hi
      rw [hhist,hcfg,ghostStep2_k,hf]
      simp only [Bool.false_eq_true,if_false,Nat.add_zero]
      exact ⟨hs.coherent.histValues i,hs.coherent.histPast i,hs.coherent.histNow i,hs.coherent.histFuture i⟩
  exact ⟨fun i => (hh i).1,fun i => (hh i).2.1,fun i => (hh i).2.2.1,fun i => (hh i).2.2.2⟩

/-- A waiting owner has the physical root form needed for the V1/L2 rows. -/
theorem currentTag_rowEpoch (k : Nat) (E : GapEpoch) (a b : Agent)
    (ht : CurrentTag k E) : CurrentTag k (rowEpoch k E a b) := by
  cases a with
  | root c cw ccw =>
    cases b with
    | interior t => cases cw <;> cases t <;> cases E <;> simp_all [rowEpoch,CurrentTag]
    | root d dw dd => cases cw <;> cases dd <;> simp_all [rowEpoch,CurrentTag]
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> exact ht
    | root d dw dd => cases t <;> cases dd <;> cases E <;> simp_all [rowEpoch,CurrentTag]

/-- Current generation tags are preserved by every raw row, owner
transfer and right retirement, independently of Dom's stopping condition. -/
theorem currentTag_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) :
    CurrentTag ((ghostStep2 R s e).k g) ((ghostStep2 R s e).epoch g).cur := by
  change CurrentTag ((ghostStep2 R s e).k g) (epochStep2 R s e g).cur
  rw [epochStep2_cur,ghostStep2_k]
  cases hf : fires R (physical2 R s) e g with
  | true => trivial
  | false =>
    simp only [Bool.false_eq_true,if_false,Nat.add_zero]
    by_cases hg : g = e.1
    · rw [rawEpochs,if_pos hg]
      exact currentTag_rowEpoch _ _ _ _ (hs.current g)
    · rw [rawEpochs,if_neg hg]
      exact hs.current g

/-! Closure is derived clause by clause below from the literal rows. -/


theorem C6_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C6 R (ghostStep2 R s e) := currentTag_step R s hs e

theorem current_token_shape (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) :
    match (s.epoch g).cur with
    | .idle | .delivered _ _ _ => EmptyGap R (curView R s) g
    | .outbound _ c => OneToken R (curView R s) g (.decl c)
    | .returning _ _ d => OneToken R (curView R s) g (.reply d) := by
  have h := hs.coherent.shape g
  cases he : (s.epoch g).cur with
  | idle =>
    have hp := hs.previous g
    cases ep : (s.epoch g).prev with
    | idle =>
      by_cases hk : s.k g = 0
      · simp only [prefixView,combinedView,he,ep,hk,if_pos,EpochShape] at h
        exact h.2.2
      · simp only [prefixView,combinedView,he,ep,hk,EpochShape] at h
        exact h.2.2.2.2
    | outbound q c => simp only [PrevShape,ep] at hp
    | returning q c d => simp only [PrevShape,ep] at hp
    | delivered q c d =>
      simp only [prefixView,combinedView,he,ep,EpochShape] at h
      exact h.2.2.2.2
  | outbound q c =>
    simp only [prefixView,combinedView,he,EpochShape] at h
    exact h.2.2.2
  | returning q c d =>
    simp only [prefixView,combinedView,he,EpochShape] at h
    exact h.2.2.2.2
  | delivered q c d =>
    simp only [prefixView,combinedView,he,EpochShape] at h
    exact h.2.2.2.2

/-! Generation-aware literal carriers. Each component has its own type. -/

def tokenPos (R : VFrame) (s : GhostRing R) (g : Fin R.m) : Nat :=
  ((List.finRange (R.len g)).find? (fun a => decide (0 < a.val) &&
    match s.cfg ⟨g,a⟩ with
    | .interior (.decl _) | .interior (.reply _) => true
    | _ => false)).map Fin.val |>.getD 0

/-- Malformed positions have the same total fallback as the uniform
projection. OneToken excludes this fallback in all live-lineage uses. -/
def ofPhase (R : VFrame) (g : Fin R.m) : Phase → LitGapState (R.len g)
  | .prelaunch => .declareAt 0 (R.len_pos g)
  | .declAt j => if hj : j < R.len g then .declareAt j hj else .delivered
  | .replyAt j => if hj : 1 ≤ j ∧ j ≤ R.len g-1 then .replyAt j hj else .delivered
  | .delivered => .delivered
def cohortToken (R : VFrame) (q : Nat) (s : GhostRing R) (g : Fin R.m) : LitGapState (R.len g) :=
  if q < s.k g then .delivered else
  if s.k g < q then .declareAt 0 (R.len_pos g) else
  match s.epoch g with
  | .idle => .declareAt 0 (R.len_pos g)
  | .outbound t _ => if t = q then ofPhase R g (.declAt (tokenPos R s g)) else .declareAt 0 (R.len_pos g)
  | .returning t _ _ => if t = q then ofPhase R g (.replyAt (tokenPos R s g)) else .declareAt 0 (R.len_pos g)
  | .delivered t _ _ => if t = q then .delivered else .declareAt 0 (R.len_pos g)

def tokensOf' (R : VFrame) : Nat → GhostRing R → (g : Fin R.m) → LitGapState (R.len g)
  | 0, _, _ => .delivered
  | q+1, s, g => cohortToken R q s g


theorem tokensOf'_past (R : VFrame) (q : Nat) (s : GhostRing R) (g : Fin R.m)
    (hq : q < s.k g) : tokensOf' R (q+1) s g = .delivered := by
  simp [tokensOf',cohortToken,hq]

def tokens2 (R : VFrame) (r : Nat) (s : GhostRing2 R) (g : Fin R.m) : LitGapState (R.len g) :=
  tokensOf' R r (curView R s) g

def latentDebt2 (R : VFrame) (r : Nat) (s : GhostRing2 R) : Nat :=
  (List.ofFn (fun g => (tokens2 R r s g).hops)).sum

def word2 (R : VFrame) (r : Nat) (s : GhostRing2 R) : PeriodHIncidenceChoice.Configuration R.m :=
  fun i => choiceToWord ((s.hist i r).getD .race)

def genMask2 (R : VFrame) (r : Nat) (s : GhostRing2 R) (i : Fin R.m) : Bool := decide (r ≤ s.k i)

theorem ring (R : VFrame) : DirectedRing R.m := ⟨by have := R.hm; omega⟩

@[simp] theorem ring_next (R : VFrame) (g : Fin R.m) : (ring R).rightNeighbor g = next R g := by
  apply Fin.ext
  change (g.val+1)%R.m = if g.val+1<R.m then g.val+1 else 0
  by_cases h : g.val+1<R.m
  · simp [h,Nat.mod_eq_of_lt h]
  · have he : g.val+1=R.m := by have := g.isLt; omega
    simp [he]

def VirtualCandidate2 (R : VFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  ∃ g, PeriodHIncidenceChoice.Candidate10 (ring R) (word2 R r s) g

def maxGen (R : VFrame) (s : GhostRing2 R) : Nat := ShortGapLineage2Closure.generationMax s.k

/-- The stop scans all recorded generations, including predecessor locks. -/
def VirtualSuccess (R : VFrame) (_r : Nat) (s : GhostRing2 R) : Prop :=
  ∃ q, q ≤ maxGen R s ∧ VirtualCandidate2 R q s

def DenialOnly2 (R : VFrame) : Nat → GhostRing2 R → Prop
  | 0, _ => True
  | q+1, s => ∀ g c d, ComparedAt ((view R s).epoch g) q →
    s.hist g q = some c → s.hist (next R g) q = some d → res c d = .denial

def CohortEntered2 (R : VFrame) (r : Nat) (s : GhostRing2 R) : Prop := ∀ i, r-1 ≤ s.k i

theorem genMask2_step (R : VFrame) (r : Nat) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (h : genMask2 R r s g = true) : genMask2 R r (ghostStep2 R s e) g = true := by
  have hk : r ≤ s.k g := by simpa [genMask2] using h
  change decide (r ≤ (ghostStep2 R s e).k g) = true
  exact decide_eq_true (Nat.le_trans hk (Nat.le_add_right _ _))

theorem latent_pos (R : VFrame) (g : Fin R.m) : 0 < (LitGapState.declareAt 0 (R.len_pos g)).hops := by
  change 0 < 2*R.len g-1-0
  have := R.len_pos g
  omega

theorem tokenPos_of_unique (R : VFrame) (s : GhostRing R) (g : Fin R.m)
    (p : Fin (R.len g)) (hp : 0 < p.val) (t : Slot) (ht : t ≠ .empty)
    (hs : ∀ a : Fin (R.len g), 0 < a.val →
      s.cfg ⟨g,a⟩ = .interior (if a = p then t else .empty)) : tokenPos R s g = p.val := by
  let P : Fin (R.len g) → Bool := fun a => decide (0 < a.val) &&
    match s.cfg ⟨g,a⟩ with
    | .interior (.decl _) | .interior (.reply _) => true
    | _ => false
  have hpp : P p = true := by
    have hh := hs p hp
    cases t with
    | empty => exact False.elim (ht rfl)
    | decl c => simp [P,hh,hp]
    | reply d => simp [P,hh,hp]
  have unique : ∀ a, P a = true → a = p := by
    intro a ha
    have ha0 : 0 < a.val := by
      by_cases hh : 0 < a.val
      · exact hh
      · simp [P,hh] at ha
    by_cases h : a = p
    · exact h
    · have hh := hs a ha0
      simp [P,hh,h] at ha
  have hfind : (List.finRange (R.len g)).find? P = some p := by
    cases he : (List.finRange (R.len g)).find? P with
    | none =>
      have hn := (List.find?_eq_none.mp he) p (List.mem_finRange p)
      exact False.elim (hn hpp)
    | some a =>
      have ha := unique a (List.find?_some he)
      subst a; rfl
  change (((List.finRange (R.len g)).find? P).map Fin.val).getD 0 = p.val
  rw [hfind]
  rfl

theorem tokenPos_bounds (R : VFrame) (s : GhostRing R) (g : Fin R.m)
    (t : Slot) (ht : t ≠ .empty) (hs : OneToken R s g t) :
    0 < tokenPos R s g ∧ tokenPos R s g < (R.len g) := by
  obtain ⟨p,hp,hslots⟩ := hs
  rw [tokenPos_of_unique R s g p hp t ht hslots]
  exact ⟨hp,p.isLt⟩


/-- The scalar cap uses the actual sum of per-gap literal hop budgets. -/
theorem latentDebt_total_var_le (R : VFrame) (r : Nat) (s : GhostRing2 R) :
    latentDebt2 R r s ≤ 2*R.n-R.m := by
  rw [← sum_two_len_sub_one]
  exact ofFn_sum_le _ _ (fun g => ShortGapCohortCut.token_hops_le (tokens2 R r s g))

theorem latchDebt_start_le_var (R : VFrame) (r : Nat) (s : GhostRing2 R) (g : Fin R.m) :
    (tokens2 R (r+1) s g).hops ≤ 2*R.len g-1 := ShortGapCohortCut.token_hops_le _

theorem latchDebt_hMax_le (R : VFrame) (r : Nat) (s : GhostRing2 R) (g : Fin R.m) :
    (tokens2 R (r+1) s g).hops ≤ 2*hMax R-1 := by
  have := latchDebt_start_le_var R r s g
  have := len_le_hMax R g
  omega

theorem all_joined_tokens_done (R : VFrame) (r : Nat) (s : GhostRing R)
    (h : ∀ i, r ≤ s.k i) : ∀ g, tokensOf' R r s g = .delivered := by
  cases r with
  | zero => intro g; rfl
  | succ q => intro g; exact tokensOf'_past R q s g (h g)
theorem zero_token2_completed (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (hz : (tokens2 R (q+1) s g).hops = 0) :
    DeliveredAt ((prefixView R (combinedView R s)).epoch g) q := by
  by_cases hpast : q < (curView R s).k g
  · exact (hs.coherent.joinedDenials g q hpast).1
  · by_cases hfuture : (curView R s).k g < q
    · have hh := latent_pos R g
      simp only [tokens2,tokensOf',cohortToken,if_neg hpast,if_pos hfuture] at hz
      omega
    · have hk' : (curView R s).k g = q := by omega
      have hk : s.k g = q := hk'
      simp only [tokens2,tokensOf',cohortToken,if_neg hpast,if_neg hfuture,curView_epoch] at hz
      have ht := hs.current g
      have hp := current_token_shape R s hs g
      cases he : (s.epoch g).cur with
      | idle =>
        simp only [he] at hz
        have hh := latent_pos R g
        omega
      | outbound t c =>
        simp only [CurrentTag,he,hk] at ht
        simp only [he] at hp
        have hb := tokenPos_bounds R (curView R s) g (.decl c) (by intro h; cases h) hp
        simp only [he,if_pos ht] at hz
        change (ofPhase R g (.declAt (tokenPos R (curView R s) g))).hops = 0 at hz
        have hh := (R.len_pos g)
        simp [ofPhase,hb.2,LitGapState.hops] at hz
        omega
      | returning t c d =>
        simp only [CurrentTag,he,hk] at ht
        simp only [he] at hp
        have hb := tokenPos_bounds R (curView R s) g (.reply d) (by intro h; cases h) hp
        have hle : tokenPos R (curView R s) g ≤ (R.len g)-1 := by omega
        have hge : 1 ≤ tokenPos R (curView R s) g := by omega
        simp only [he,if_pos ht] at hz
        change (ofPhase R g (.replyAt (tokenPos R (curView R s) g))).hops = 0 at hz
        simp [ofPhase,hge,hle,LitGapState.hops] at hz
        omega
      | delivered t c d =>
        simp only [CurrentTag,he,hk] at ht
        simp [prefixView,combinedView,he,DeliveredAt,ht]

private theorem sum_zero_point {m : Nat} (f : Fin m → Nat)
    (h : (List.ofFn f).sum = 0) : ∀ i, f i = 0 := by
  induction m with
  | zero => exact fun i => Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ,List.sum_cons] at h
    intro i
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i; omega
    · have hip : 0 < i.val := by omega
      let j : Fin m := ⟨i.val-1,by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have hz := ih (fun a => f a.succ) (by omega) j
      simpa only [hj] using hz

private theorem view_k (R : VFrame) (s : GhostRing2 R) :
    (prefixView R (combinedView R s)).k = s.k := rfl
private theorem view_hist (R : VFrame) (s : GhostRing2 R) :
    (prefixView R (combinedView R s)).hist = s.hist := rfl
private theorem view_cfg (R : VFrame) (s : GhostRing2 R) :
    (prefixView R (combinedView R s)).cfg = s.cfg := rfl

/-- Any root not yet JOINed into r forces positive predecessor debt.
Neither Race nor an entry-cut assumption is needed for this bridge. -/
theorem unjoined_gen_has_debt2 (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hd : DenialOnly2 R r s)
    (i : Fin R.m) (hi : s.k i < r) : 0 < latentDebt2 R r s := by
  apply Nat.pos_of_ne_zero
  intro hz
  cases r with
  | zero => omega
  | succ q =>
    change ∀ g c d, ComparedAt ((prefixView R (combinedView R s)).epoch g) q →
      s.hist g q = some c → s.hist (next R g) q = some d → res c d = .denial at hd
    have allzero := sum_zero_point (fun g => (tokens2 R (q+1) s g).hops) hz
    have ho := zero_token2_completed R q s hs i (allzero i)
    have hp := zero_token2_completed R q s hs (prev R i) (allzero (prev R i))
    have hq : s.k i = q := by
      have hh := hs.coherent.shape i
      cases he : (prefixView R (combinedView R s)).epoch i
      all_goals simp only [EpochShape,he,view_k] at hh
      all_goals simp only [he,DeliveredAt] at ho
      all_goals omega
    obtain ⟨c,d,hc,hd',hw⟩ := hs.coherent.outgoingValue i
      (by simpa only [view_k,hq] using ho)
    have hcomp : ComparedAt ((prefixView R (combinedView R s)).epoch i) q := by
      cases he : (prefixView R (combinedView R s)).epoch i
      all_goals simp_all only [DeliveredAt,ComparedAt]
      all_goals omega
    have hv := hd i c d hcomp (by simpa only [view_hist,view_k,hq] using hc)
      (by simpa only [view_hist,view_k,hq] using hd')
    have hcw : (s.cfg (rootV R i)).cwPort = some .heldDenial := by
      change (s.cfg (rootV R i)).cwPort = some (resCw c d) at hw
      simpa only [resCw,hv,Verdict.cw] using hw
    have hcompPrev : ComparedAt ((prefixView R (combinedView R s)).epoch (prev R i)) q := by
      cases he : (prefixView R (combinedView R s)).epoch (prev R i)
      all_goals simp_all only [DeliveredAt,ComparedAt]
      all_goals omega
    obtain ⟨c',d',hc',hd'',hw'⟩ := hs.coherent.incomingValue (prev R i)
      (by simpa only [view_k,next_prev,hq] using hcompPrev)
    have hv' := hd (prev R i) c' d' hcompPrev
      (by simpa only [view_hist,view_k,next_prev,hq] using hc')
      (by simpa only [view_hist,view_k,next_prev,hq] using hd'')
    have hccw : (s.cfg (rootV R i)).ccwPort = some .heldDenial := by
      simpa only [view_cfg,next_prev,resCcw,hv',Verdict.ccw] using hw'
    obtain ⟨ch,cw,ccw,hroot⟩ := hs.coherent.roots i
    change s.cfg (rootV R i) = .root ch cw ccw at hroot
    rw [hroot] at hcw hccw
    have hcw' : cw = .heldDenial := Option.some.inj hcw
    have hccw' : ccw = .heldDenial := Option.some.inj hccw
    have hn := hs.coherent.normalized i
    change joinReady (s.cfg (rootV R i)) = false at hn
    rw [hroot,hcw',hccw'] at hn
    cases hn

theorem latentDebt2_zero_all_joined (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hd : DenialOnly2 R r s) (hz : latentDebt2 R r s = 0) :
    ∀ i, r ≤ s.k i := by
  intro i
  by_cases hi : s.k i < r
  · have hp := unjoined_gen_has_debt2 R r s hs hd i hi
    omega
  · omega

/-- The zero-debt case of nonincrease is fully physical and needs no
post-step invariant or carrier-simulation hypothesis. -/
theorem latentDebt2_zero_step (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hd : DenialOnly2 R r s) (hz : latentDebt2 R r s = 0)
    (e : Vtx R) : latentDebt2 R r (ghostStep2 R s e) = 0 := by
  have hj := latentDebt2_zero_all_joined R r s hs hd hz
  have ht := all_joined_tokens_done R r (curView R (ghostStep2 R s e))
    (fun i => Nat.le_trans (hj i) (Nat.le_add_right _ _))
  simp [latentDebt2,tokens2,ht,LitGapState.hops,ofFn_sum_const]

theorem other_gap_interior (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (hg : g ≠ e.1) (a : Fin (R.len g)) (ha : 0 < a.val) :
    (ghostStep2 R s e).cfg ⟨g,a⟩ = s.cfg ⟨g,a⟩ := by
  have hn : ¬ incident R e ⟨g,a⟩ := by
    rintro (h | h)
    · exact hg (congrArg Sigma.fst h)
    · by_cases he : e.2.val+1 < R.len e.1
      · rw [rn_of_lt R e he] at h
        exact hg (congrArg Sigma.fst h)
      · rw [rn_of_last R e he] at h
        have hz := congrArg (fun v : Vtx R => v.2.val) h
        change a.val = 0 at hz
        omega
  rw [ghostStep2_physical]
  exact if_neg hn

/-- In particular, the bounded physical scan of every other gap stutters. -/
theorem other_gap_tokenPos (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (hg : g ≠ e.1) :
    tokenPos R (curView R (ghostStep2 R s e)) g = tokenPos R (curView R s) g := by
  have hp : (fun a : Fin (R.len g) => decide (0 < a.val) &&
      match (ghostStep2 R s e).cfg ⟨g,a⟩ with
      | .interior (.decl _) | .interior (.reply _) => true | _ => false) =
    (fun a : Fin (R.len g) => decide (0 < a.val) &&
      match s.cfg ⟨g,a⟩ with
      | .interior (.decl _) | .interior (.reply _) => true | _ => false) := by
    funext a
    by_cases ha : 0 < a.val
    · rw [other_gap_interior R s e g hg a ha]
    · simp [ha]
  exact congrArg (fun p : Fin (R.len g) → Bool =>
    (((List.finRange (R.len g)).find? p).map Fin.val).getD 0) hp

/-- The current token of another gap stutters unless its owner JOINs.
The entry cut makes such a JOIN discharge its token, never create debt.
This theorem is unconditional in Lineage2 and in denial history. -/
theorem other_gap_token_debt_le (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) (hc : CohortEntered2 R r s) :
    (tokens2 R r (ghostStep2 R s e) g).hops ≤ (tokens2 R r s g).hops := by
  cases r with
  | zero => exact Nat.le_refl _
  | succ q =>
    have hq : q ≤ s.k g := hc g
    cases hf : fires R (physical2 R s) e g with
    | true =>
      have hk : q < (curView R (ghostStep2 R s e)).k g := by
        change q < (ghostStep2 R s e).k g
        rw [ghostStep2_k,hf]
        change q < s.k g + 1
        omega
      have ht := tokensOf'_past R q (curView R (ghostStep2 R s e)) g hk
      change (tokensOf' R (q+1) (curView R (ghostStep2 R s e)) g).hops ≤ _
      rw [ht]
      exact Nat.zero_le _
    | false =>
      have hk : (curView R (ghostStep2 R s e)).k g = (curView R s).k g := by
        change (ghostStep2 R s e).k g = s.k g
        simp [ghostStep2_k,hf]
      have he : (curView R (ghostStep2 R s e)).epoch g = (curView R s).epoch g := by
        change (epochStep2 R s e g).cur = _
        rw [epochStep2_cur,hf]
        simp [rawEpochs,hg]
      have hp := other_gap_tokenPos R s e g hg
      change (cohortToken R q (curView R (ghostStep2 R s e)) g).hops ≤
        (cohortToken R q (curView R s) g).hops
      simp only [cohortToken,hk,he,hp]
      exact Nat.le_refl _

/-- Idle current transactions have maximal latent debt or are already
past the accounting cohort. In either case no physical edge increases
their projected debt, without any lineage or simulation premise. -/
theorem idle_gap_token_debt_le (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m) (hi : (s.epoch g).cur = .idle) :
    (tokens2 R r (ghostStep2 R s e) g).hops ≤ (tokens2 R r s g).hops := by
  cases r with
  | zero => exact Nat.le_refl _
  | succ q =>
    by_cases hp : q < (curView R s).k g
    · have hp' : q < (curView R (ghostStep2 R s e)).k g :=
        Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)
      change (tokensOf' R (q+1) (curView R (ghostStep2 R s e)) g).hops ≤
        (tokensOf' R (q+1) (curView R s) g).hops
      rw [tokensOf'_past R q _ g hp',tokensOf'_past R q _ g hp]
      exact Nat.le_refl _
    · have ht : tokens2 R (q+1) s g = .declareAt 0 (R.len_pos g) := by
        simp only [tokens2,tokensOf',cohortToken,if_neg hp,curView_epoch,hi,ite_self]
      rw [ht]
      exact ShortGapCohortCut.token_hops_le _

/-- The total nonincrease theorem reduces to its single scheduled gap.
All other gaps are discharged by the unconditional side-activity lemma. -/
theorem latentDebt2_step_le_of_scheduled_gap (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (hc : CohortEntered2 R r s)
    (hselected : (tokens2 R r (ghostStep2 R s e) e.1).hops ≤ (tokens2 R r s e.1).hops) :
    latentDebt2 R r (ghostStep2 R s e) ≤ latentDebt2 R r s := by
  apply ofFn_sum_le
  intro g
  by_cases hg : g = e.1
  · subst g; exact hselected
  · exact other_gap_token_debt_le R r s e g hg hc



/-! Local provenance and geometry needed for the remaining clauses. -/
def NeighborSkew (R : VFrame) (s : SliceState R) : Prop :=
  ∀ g, s.k g ≤ s.k (next R g)+1 ∧ s.k (next R g) ≤ s.k g+1

theorem fires_iff (R : VFrame) (s : SliceState R) (e : Vtx R) (i : Fin R.m) :
    fires R s e i = true ↔ incident R e (rootV R i) ∧
      ∃ c, rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial := by
  simp [fires,ShortGapOwnerRoundSlice.joinReady_iff]
theorem neighborSkew_of_lineage (R : VFrame) (s : GhostRing R) (hs : Lineage R s) :
    NeighborSkew R (physical R s) := by
  intro g
  have h := hs.shape g
  change s.k g ≤ s.k (next R g) + 1 ∧ s.k (next R g) ≤ s.k g + 1
  cases he : s.epoch g <;> simp only [EpochShape, he] at h
  all_goals omega

theorem outgoing_support (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (hc : CwHeld (s.cfg (rootV R g)).cwPort) : s.k g ≤ s.k (next R g) := by
  have hd := (hs.outgoing g).mp hc
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  all_goals simp only [he, DeliveredAt] at hd
  all_goals omega

theorem incoming_support (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (hc : CcwHeld (s.cfg (rootV R (next R g))).ccwPort) :
    s.k (next R g) ≤ s.k g := by
  have hd := (hs.incoming g).mp hc
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  all_goals simp only [he, ComparedAt] at hd
  all_goals omega

/-- The P1 guards force equal endpoint generations from the epoch ranges. -/
theorem direct_generations (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
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
theorem toSend_empty_gap (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
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

private theorem oneToken_kind (R : VFrame) (s : GhostRing R) (g : Fin R.m)
    (t u : Slot) (ht : OneToken R s g t) (a : Fin (R.len g)) (ha : 0 < a.val)
    (hu : s.cfg ⟨g,a⟩ = .interior u) : u = t ∨ u = .empty := by
  obtain ⟨p, _, hp⟩ := ht
  have hh := hp a ha
  rw [hu] at hh
  by_cases h : a = p
  · simp only [if_pos h] at hh; cases hh; exact Or.inl rfl
  · simp only [if_neg h] at hh; cases hh; exact Or.inr rfl

theorem reply_support (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (d : Choice)
    (ht : s.cfg ⟨g,a⟩ = .interior (.reply d)) : s.k g ≤ s.k (next R g) := by
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  · have hx := hh.2.2 a ha; rw [ht] at hx; cases hx
  · have hx := oneToken_kind R s g _ _ hh.2.2.2 a ha ht
    rcases hx with h | h <;> cases h
  · omega
  · have hx := hh.2.2.2.2 a ha; rw [ht] at hx; cases hx

theorem declaration_support (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (c : Choice)
    (ht : s.cfg ⟨g,a⟩ = .interior (.decl c)) : s.k (next R g) ≤ s.k g := by
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

theorem interior_roles (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) : ∃ t, s.cfg ⟨g,a⟩ = .interior t := by
  have hh := hs.shape g
  cases he : s.epoch g <;> simp only [EpochShape, he] at hh
  · exact ⟨.empty, hh.2.2 a ha⟩
  · obtain ⟨p, _, hp⟩ := hh.2.2.2; exact ⟨_, hp a ha⟩
  · obtain ⟨p, _, hp⟩ := hh.2.2.2.2; exact ⟨_, hp a ha⟩
  · exact ⟨.empty, hh.2.2.2.2 a ha⟩

private theorem rn_root_cases (R : VFrame) (i : Fin R.m) :
    rn R (rootV R i) = rootV R (next R i) ∨
      ∃ a : Fin (R.len i), 0 < a.val ∧ rn R (rootV R i) = ⟨i,a⟩ := by
  by_cases h : 1 < (R.len i)
  · exact Or.inr ⟨⟨1,h⟩, Nat.zero_lt_succ 0, by simp [rn, h]⟩
  · exact Or.inl (by simp [rn, rootV, h])

private theorem boundary_root (R : VFrame) (e : Vtx R) (i : Fin R.m)
    (hd : rootV R i = rn R e) : i = next R e.1 := by
  by_cases h : e.2.val+1 < R.len e.1
  · rw [rn_of_lt R e h] at hd
    have hh := congrArg (fun v : Vtx R => v.2.val) hd
    change 0 = e.2.val+1 at hh
    omega
  · have hh := congrArg Sigma.fst hd
    simpa [rn, rootV, h] using hh

private theorem zero_is_root (R : VFrame) (e : Vtx R) (h : e.2.val = 0) : e = rootV R e.1 := by
  exact vtx_eq R _ _ rfl h

private theorem cw_raw_support (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
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

private theorem ccw_raw_support (R : VFrame) (s : GhostRing R) (hs : Lineage R s)
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
            have he2 : e.2 = (⟨0,(R.len_pos e.1)⟩ : Fin (R.len e.1)) := Fin.ext hz
            change s.cfg ⟨e.1,e.2⟩ = _ at hd
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

theorem join_requires_neighbors_of_lineage (R : VFrame) (s : GhostRing R)
    (hs : Lineage R s) (e : Vtx R) (i : Fin R.m) (hj : fires R (physical R s) e i = true) :
    s.k i ≤ s.k (next R i) ∧ s.k i ≤ s.k (prev R i) := by
  obtain ⟨_,c,hc⟩ := (fires_iff R (physical R s) e i).mp hj
  change rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial at hc
  exact ⟨cw_raw_support R s hs i e (by rw [hc]; rfl),
    ccw_raw_support R s hs i e (by rw [hc]; rfl)⟩

theorem neighborSkew_of_lineage2 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) :
    NeighborSkew R (physical2 R s) := neighborSkew_of_lineage R (view R s) hs.coherent

theorem history2_monotone (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (i : Fin R.m) (q : Nat) (c : Choice) (h : s.hist i q = some c) :
    (ghostStep2 R s e).hist i q = some c := by
  change (if incident R e (rootV R i) then
    updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i) else s.hist i) q = _
  split
  · exact ShortGapLineage.updateHistory_monotone _ _ _ _ _ h
  · exact h

theorem toSend_empty_gap2 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (h : (s.cfg (rootV R g)).cwPort = some .toSend) : EmptyGap R (curView R s) g :=
  toSend_empty_gap R (view R s) hs.coherent g h
theorem cfg_step_pair (R : VFrame) (s : GhostRing2 R) (e v : Vtx R) :
    (ghostStep2 R s e).cfg v =
      if v = e then ShortGapLiteralRingRows.joinA (row (s.cfg e) (s.cfg (rn R e))).1
      else if v = rn R e then ShortGapLiteralRingRows.joinA (row (s.cfg e) (s.cfg (rn R e))).2
      else s.cfg v := by
  rw [ghostStep2_physical]
  by_cases h0 : v = e
  · simp [ringStepU,joinTick,rawAt,incident,h0]
  · by_cases h1 : v = rn R e
    · simp [ringStepU,joinTick,rawAt,incident,h1,rn_ne_self]
    · simp [ringStepU,incident,h0,h1]

/-- With no owner JOIN, an unscheduled gap's entire accounting token
stutters, not merely its debt. -/
theorem other_gap_token_eq (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e g = false) :
    tokens2 R r (ghostStep2 R s e) g = tokens2 R r s g := by
  cases r with
  | zero => rfl
  | succ q =>
    have hk : (curView R (ghostStep2 R s e)).k g = (curView R s).k g := by
      change (ghostStep2 R s e).k g = s.k g
      simp [ghostStep2_k,hf]
    have he : (curView R (ghostStep2 R s e)).epoch g = (curView R s).epoch g := by
      change (epochStep2 R s e g).cur = _
      rw [epochStep2_cur,hf]
      simp [rawEpochs,hg]
    have hp := other_gap_tokenPos R s e g hg
    change cohortToken R q (curView R (ghostStep2 R s e)) g =
      cohortToken R q (curView R s) g
    simp only [cohortToken,hk,he,hp]

/-- The first edge of a nontrivial gap has a genuine interior receiver. -/
theorem rn_root_first (R : VFrame) (g : Fin R.m) (hh : 1 < (R.len g)) :
    rn R (rootV R g) = ⟨g,⟨1,hh⟩⟩ := by
  exact rn_of_lt R (rootV R g) hh

/-- The actual L1 row, with the first slot's emptiness derived from lineage. -/
theorem prelaunch_row (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g)) :
    row (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) =
      (.root (resolveInit c) .waiting ccw,.interior (.decl (resolveInit c))) := by
  have hempty := toSend_empty_gap2 R s hs g (by rw [hc]; rfl)
  have hslot : s.cfg ⟨g,⟨1,hh⟩⟩ = .interior .empty := hempty ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  rw [rn_root_first R g hh,hc,hslot]
  rfl

/-- L1 leaves every root outside JOIN: the owner is waiting and the
other endpoint is an interior slot. -/
theorem prelaunch_no_joins (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g)) :
    ∀ i, fires R (physical2 R s) (rootV R g) i = false := by
  have hr := prelaunch_row R s hs g c ccw hc hh
  intro i
  have hright : rootV R i ≠ rn R (rootV R g) := by
    rw [rn_root_first R g hh]
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = 1 at hv
    omega
  by_cases hi : rootV R i = rootV R g
  · simp [fires,physical2,incident,rawAt,hi,hr,joinReady]
  · simp [fires,physical2,incident,hi,hright]

/-- A genuine L1 launch creates exactly one declaration at slot 1. -/
theorem row_right_cw (a : Agent) (c : Choice) (cw : CwPort) (ccw : CcwPort) :
    ((row a (.root c cw ccw)).2).cwPort = some cw := by
  cases a with
  | root d dw dd => cases dw <;> cases ccw <;> rfl
  | interior t => cases t <;> cases ccw <;> rfl

theorem raw_cw_other (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (rawAt R s.cfg e (rootV R g)).cwPort = (s.cfg (rootV R g)).cwPort := by
  have hleft : rootV R g ≠ e := fun h => hg (congrArg Sigma.fst h)
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hroot
  by_cases hright : rootV R g = rn R e
  · have hr : s.cfg (rn R e) = .root c cw ccw := by rw [← hright]; exact hroot
    rw [rawAt,if_neg hleft,if_pos hright,hr,hroot]
    exact row_right_cw _ _ _ _
  · rw [rawAt,if_neg hleft,if_neg hright]

/-- A shared-root JOIN can affect an unscheduled owner only after its
own current transaction is delivered. This is derived from port agreement. -/
theorem other_join_current_delivered (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e g = true) :
    ∃ c d, (s.epoch g).cur = .delivered (s.k g) c d := by
  have hj := (fires_iff R (physical2 R s) e g).mp hf
  obtain ⟨c,hc⟩ := hj.2
  change rawAt R s.cfg e (rootV R g) = .root c .heldDenial .heldDenial at hc
  have hcw : (s.cfg (rootV R g)).cwPort = some .heldDenial := by
    rw [← raw_cw_other R s hs e g hg,hc]
    rfl
  cases he : (s.epoch g).cur with
  | idle =>
    have hh := hs.idleSend g he
    rw [hcw] at hh
    cases hh
  | outbound q c =>
    have hh := (hs.waiting g).mpr (by rw [he]; trivial)
    rw [hcw] at hh
    cases hh
  | returning q c d =>
    have hh := (hs.waiting g).mpr (by rw [he]; trivial)
    rw [hcw] at hh
    cases hh
  | delivered q c d =>
    have ht := hs.current g
    simp only [he,CurrentTag] at ht
    exact ⟨c,d,by rw [ht]⟩

/-- Transfer of a delivered current epoch to prev, with owner increment,
preserves every accounting token: past tokens stay discharged and future
tokens stay latent. -/
theorem rowEpoch_delivered (k q : Nat) (c d : Choice) (a b : Agent)
    (ha : a.cwPort ≠ some .toSend) :
    rowEpoch k (.delivered q c d) a b = .delivered q c d := by
  cases a with
  | interior t =>
    cases b with
    | root x cw ccw => cases t <;> cases ccw <;> rfl
    | interior u => cases t <;> rfl
  | root x cw ccw =>
    cases cw with
    | toSend => exact False.elim (ha rfl)
    | waiting => cases b with
      | root y yw yy => rfl
      | interior t => cases t <;> rfl
    | heldDenial => cases b with
      | root y yw yy => rfl
      | interior t => cases t <;> rfl
    | heldCandidate => cases b with
      | root y yw yy => rfl
      | interior t => cases t <;> rfl

theorem delivered_raw_epoch (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (q : Nat) (c d : Choice) (he : (s.epoch e.1).cur = .delivered q c d) :
    rawEpochs R (curView R s) e e.1 = .delivered q c d := by
  have hk := hs.current e.1
  simp only [he,CurrentTag] at hk
  have hheld := (hs.coherent.outgoing e.1).mpr (by
    simp [prefixView,combinedView,he,DeliveredAt,hk])
  have hnot : (s.cfg e).cwPort ≠ some .toSend := by
    by_cases ha : e.2.val = 0
    · have heRoot : e = rootV R e.1 := vtx_eq R _ _ rfl ha
      rw [heRoot]
      intro hc
      change CwHeld (s.cfg (rootV R e.1)).cwPort at hheld
      rw [hc] at hheld
      exact hheld
    · have hp : 0 < e.2.val := by omega
      have hempty := current_token_shape R s hs e.1
      rw [he] at hempty
      have hslot : s.cfg e = .interior .empty := hempty e.2 hp
      rw [hslot]
      intro h; cases h
  rw [rawEpochs,if_pos rfl]
  change rowEpoch (s.k e.1) (s.epoch e.1).cur (s.cfg e) (s.cfg (rn R e)) = _
  rw [he]
  exact rowEpoch_delivered _ _ _ _ _ _ hnot

/-- A delivered selected token stutters through any physical interaction,
including owner JOIN. This discharges the complete delivered branch. -/
theorem no_owner_join_at_positive (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (hp : 0 < e.2.val) : fires R (physical2 R s) e e.1 = false := by
  have hl : rootV R e.1 ≠ e := by
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = e.2.val at hv
    omega
  have hr : rootV R e.1 ≠ rn R e := by
    by_cases he : e.2.val+1 < R.len e.1
    · rw [rn_of_lt R e he]
      intro h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = e.2.val+1 at hv
      omega
    · rw [rn_of_last R e he]
      intro h
      have hv := congrArg Sigma.fst h
      exact next_ne_self R e.1 hv.symm
  simp [fires,incident,hl,hr]

/-- A pair-local move of a single token. The payload may change at the
same occupied slot, as it does at declaration/reply comparison. -/
theorem waiting_root (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hl : Live (s.epoch g).cur) :
    ∃ c ccw, s.cfg (rootV R g) = .root c .waiting ccw := by
  obtain ⟨c,cw,ccw,hc⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hc
  have hw := (hs.waiting g).mpr hl
  rw [hc] at hw
  have he : cw = .waiting := Option.some.inj hw
  exact ⟨c,ccw,he ▸ hc⟩

/-- Every owner JOIN transfers a genuinely delivered raw epoch. L1 and
outbound L2/L3 cannot JOIN; V1 and direct P1 are the delivery producers.
An owner JOIN caused by another gap uses its retained current delivery. -/
theorem owner_join_raw_delivered (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hf : fires R (physical2 R s) e g = true) :
    ∃ q c d, rawEpochs R (curView R s) e g = .delivered q c d := by
  by_cases hg : g ≠ e.1
  · obtain ⟨c,d,he⟩ := other_join_current_delivered R s hs e g hg hf
    exact ⟨s.k g,c,d,by simp [rawEpochs,hg,he,curView]⟩
  · have hge : g = e.1 := Classical.not_not.mp hg
    have hp : e.2.val = 0 := by
      by_cases hp : 0 < e.2.val
      · have hn := no_owner_join_at_positive R s e hp
        rw [← hge,hf] at hn
        cases hn
      · omega
    have he : e = rootV R g := by
      apply vtx_eq R
      · exact hge.symm
      · exact hp
    rw [he] at hf ⊢
    have hshape := current_token_shape R s hs g
    cases hc : (s.epoch g).cur with
    | delivered q c d =>
      exact ⟨q,c,d,delivered_raw_epoch R s hs (rootV R g) q c d hc⟩
    | idle =>
      obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root c cw ccw at hroot
      have hw := hs.idleSend g hc
      rw [hroot] at hw
      have hcw : cw = .toSend := Option.some.inj hw
      subst cw
      by_cases hh : 1 < (R.len g)
      · have hn := prelaunch_no_joins R s hs g c ccw hroot hh g
        rw [hf] at hn; cases hn
      · have hh1 : (R.len g) = 1 := by have := (R.len_pos g); omega
        have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<(R.len g); omega)
        obtain ⟨d,dw,dd,hr⟩ := hs.coherent.roots (next R g)
        change s.cfg (rootV R (next R g)) = .root d dw dd at hr
        cases dd with
        | free =>
          refine ⟨s.k g,resolveInit c,resolveResp d,?_⟩
          rw [rawEpochs,if_pos rfl]
          change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
          rw [hroot,hrn,hr]; rfl
        | heldDenial => simp [fires,physical2,rawAt,hroot,hrn,hr,row,joinReady] at hf
        | heldCandidate => simp [fires,physical2,rawAt,hroot,hrn,hr,row,joinReady] at hf
    | outbound q c =>
      obtain ⟨x,ccw,hroot⟩ := waiting_root R s hs g (by rw [hc]; trivial)
      rw [hc] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      have hh : 1 < (R.len g) := by have := p.isLt; omega
      have hrn := rn_root_first R g hh
      have hslot := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
      change s.cfg ⟨g,⟨1,hh⟩⟩ = _ at hslot
      by_cases hp1 : (⟨1,hh⟩ : Fin (R.len g)) = p
      · rw [if_pos hp1] at hslot
        simp [fires,physical2,rawAt,hroot,hrn,hslot,row,joinReady] at hf
      · rw [if_neg hp1] at hslot
        simp [fires,physical2,rawAt,hroot,hrn,hslot,row,joinReady] at hf
    | returning q c d =>
      obtain ⟨x,ccw,hroot⟩ := waiting_root R s hs g (by rw [hc]; trivial)
      rw [hc] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      have hh : 1 < (R.len g) := by have := p.isLt; omega
      have hrn := rn_root_first R g hh
      have hslot := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
      change s.cfg ⟨g,⟨1,hh⟩⟩ = _ at hslot
      by_cases hp1 : (⟨1,hh⟩ : Fin (R.len g)) = p
      · rw [if_pos hp1] at hslot
        refine ⟨q,c,d,?_⟩
        rw [rawEpochs,if_pos rfl]
        change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
        rw [hc,hroot,hrn,hslot]; rfl
      · rw [if_neg hp1] at hslot
        simp [fires,physical2,rawAt,hroot,hrn,hslot,row,joinReady] at hf

/-- Reading a resolved raw root at its departing generation gives the
actual post-step history record, also when JOIN erases that choice. -/
theorem raw_choice_recorded (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hi : incident R e (rootV R i)) (c : Choice)
    (hc : (rawAt R s.cfg e (rootV R i)).choice = some c) :
    (ghostStep2 R s e).hist i (s.k i) = some c := by
  obtain ⟨d,cw,ccw,hr,hd,hh⟩ := raw_root_resolved R s hs e i hi
  rw [hr] at hc
  have hdc : d = c := Option.some.inj hc
  rw [history_step_record R s e i hi d cw ccw hr hd,record_current _ _ _ hh,hdc]

private theorem rowEpoch_delivery_origin (k : Nat) (E : GapEpoch) (a b : Agent)
    (q : Nat) (c d : Choice) (h : rowEpoch k E a b = .delivered q c d) :
    E = .delivered q c d ∨ E = .returning q c d ∨
      ∃ x X y Y, a = .root x .toSend X ∧ b = .root y Y .free ∧
        q = k ∧ c = resolveInit x ∧ d = resolveResp y := by
  cases a with
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> exact Or.inl h
    | root y Y Z =>
      cases t <;> cases Z <;> cases E <;> simp only [rowEpoch] at h
      all_goals first | (exact Or.inl h) | (cases h <;> exact Or.inl rfl)
  | root x X Z =>
    cases b with
    | interior t =>
      cases X <;> cases t <;> cases E <;> simp only [rowEpoch] at h
      all_goals first | (exact Or.inl h) | (cases h <;> exact Or.inl rfl) |
        (cases h <;> exact Or.inr (Or.inl rfl))
    | root y Y W =>
      cases X <;> cases W <;> simp only [rowEpoch] at h
      all_goals first | (exact Or.inl h) |
        (cases h <;> exact Or.inr (Or.inr ⟨_,_,_,_,rfl,rfl,rfl,rfl,rfl⟩))

/-- A delivered raw epoch carries the two immutable history payloads.
The only new pair is direct P1; its guards force equal generations. -/
theorem raw_delivered_payloads (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (q : Nat) (c d : Choice)
    (he : rawEpochs R (curView R s) e g = .delivered q c d) :
    (ghostStep2 R s e).hist g q = some c ∧ (ghostStep2 R s e).hist (next R g) q = some d := by
  have old : (s.epoch g).cur = .delivered q c d ∨ (s.epoch g).cur = .returning q c d →
      (ghostStep2 R s e).hist g q = some c ∧ (ghostStep2 R s e).hist (next R g) q = some d := by
    intro hc
    have ht := hs.coherent.shape g
    rcases hc with hc | hc
    all_goals simp only [EpochShape,prefixView,combinedView,hc] at ht
    all_goals exact ⟨history2_monotone R s e g q c ht.2.2.1,
      history2_monotone R s e (next R g) q d ht.2.2.2.1⟩
  by_cases hg : g = e.1
  · rw [rawEpochs,if_pos hg] at he
    rcases rowEpoch_delivery_origin _ _ _ _ q c d he with hc | hc | hnew
    · exact old (Or.inl hc)
    · exact old (Or.inr hc)
    · obtain ⟨x,X,y,Y,hl,hr,hq,hc,hd⟩ := hnew
      change s.cfg e = .root x .toSend X at hl
      change s.cfg (rn R e) = .root y Y .free at hr
      have hz : e.2.val = 0 := by
        by_cases hp : 0 < e.2.val
        · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 e.2 hp
          change s.cfg e = .interior t at ht
          rw [hl] at ht; cases ht
        · omega
      have hleft : e = rootV R g := by
        apply vtx_eq R
        · exact hg.symm
        · exact hz
      have hlast : ¬ e.2.val+1 < R.len e.1 := by
        intro hp
        have hrn := rn_of_lt R e hp
        obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 ⟨e.2.val+1,hp⟩ (Nat.zero_lt_succ _)
        change s.cfg ⟨e.1,⟨e.2.val+1,hp⟩⟩ = .interior t at ht
        rw [hrn,ht] at hr; cases hr
      have hright : rn R e = rootV R (next R g) := by rw [rn_of_last R e hlast,← hg]
      have hgen := direct_generations R (view R s) hs.coherent g
        (by change (s.cfg (rootV R g)).cwPort = _; rw [← hleft,hl]; rfl)
        (by change (s.cfg (rootV R (next R g))).ccwPort = _; rw [← hright,hr]; rfl)
      change s.k g = s.k (next R g) at hgen
      have hq' : q = s.k g := hq
      have hrawL : (rawAt R s.cfg e (rootV R g)).choice = some c := by
        rw [rawAt,if_pos hleft.symm,hl,hr,hc]
        rfl
      have hnr : rootV R (next R g) ≠ e := by
        rw [← hright]; exact rn_ne_self R e
      have hrawR : (rawAt R s.cfg e (rootV R (next R g))).choice = some d := by
        rw [rawAt,if_neg hnr,if_pos hright.symm,hl,hr,hd]
        rfl
      rw [hq']
      exact ⟨raw_choice_recorded R s hs e g (Or.inl hleft.symm) c hrawL,
        hgen ▸ raw_choice_recorded R s hs e (next R g) (Or.inr hright.symm) d hrawR⟩
  · have hc : (s.epoch g).cur = .delivered q c d := by simpa [rawEpochs,hg,curView] using he
    exact old (Or.inl hc)

/-- The archive clause is preserved for all four JOIN combinations.
Right JOIN clears it; owner JOIN transfers a delivered result; otherwise
comparison clears it or the previous record persists with unchanged counters. -/
theorem C5_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C5 R (ghostStep2 R s e) := by
  intro g
  cases hR : fires R (physical2 R s) e (next R g) with
  | true =>
    have hp : ((ghostStep2 R s e).epoch g).prev = .idle := by
      change (epochStep2 R s e g).prev = _
      simp [epochStep2,hR]
    simp only [PrevShape,hp]
  | false =>
    have hkR : (ghostStep2 R s e).k (next R g) = s.k (next R g) := by simp [ghostStep2_k,hR]
    cases hO : fires R (physical2 R s) e g with
    | true =>
      obtain ⟨q,c,d,he⟩ := owner_join_raw_delivered R s hs e g hO
      have ht : CurrentTag (s.k g) (rawEpochs R (curView R s) e g) := by
        by_cases hg : g = e.1
        · rw [rawEpochs,if_pos hg]
          exact currentTag_rowEpoch _ _ _ _ (hs.current g)
        · rw [rawEpochs,if_neg hg]
          exact hs.current g
      have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
      have hkO : (ghostStep2 R s e).k g = q+1 := by simp [ghostStep2_k,hO,hq]
      have hsupport := join_requires_neighbors_of_lineage R (view R s) hs.coherent e g hO
      have hskew := neighborSkew_of_lineage2 R s hs g
      change s.k g ≤ s.k (next R g) ∧ s.k g ≤ s.k (prev R g) at hsupport
      change s.k g ≤ s.k (next R g)+1 ∧ s.k (next R g) ≤ s.k g+1 at hskew
      have hbound : s.k (next R g) = q ∨ s.k (next R g) = q+1 := by omega
      have hp : ((ghostStep2 R s e).epoch g).prev = .delivered q c d := by
        change (epochStep2 R s e g).prev = _
        simp [epochStep2,hR,hO,he]
      rw [PrevShape,hp]
      exact ⟨hkO,hkR ▸ hbound,raw_delivered_payloads R s hs e g q c d he⟩
    | false =>
      have hkO : (ghostStep2 R s e).k g = s.k g := by simp [ghostStep2_k,hO]
      by_cases hc : g = e.1 ∧ compares (s.cfg e) (s.cfg (rn R e)) = true
      · have hp : ((ghostStep2 R s e).epoch g).prev = .idle := by
          change (epochStep2 R s e g).prev = _
          simp only [epochStep2,hR,hO,Bool.false_eq_true,if_false,if_pos hc]
        simp only [PrevShape,hp]
      · have hp : ((ghostStep2 R s e).epoch g).prev = (s.epoch g).prev := by
          change (epochStep2 R s e g).prev = _
          simp [epochStep2,hR,hO,hc]
        have hsP := hs.previous g
        cases he : (s.epoch g).prev with
        | idle => simp only [PrevShape,hp,he]
        | outbound q c => simp only [PrevShape,he] at hsP
        | returning q c d => simp only [PrevShape,he] at hsP
        | delivered q c d =>
          simp only [PrevShape,he] at hsP
          rw [PrevShape,hp,he,hkO,hkR]
          exact ⟨hsP.1,hsP.2.1,history2_monotone R s e g q c hsP.2.2.1,
            history2_monotone R s e (next R g) q d hsP.2.2.2⟩

/-- The archive contributes completed history but never a live owner
transaction or a delivery in the owner's current generation. -/
theorem view_owner_tests (R : VFrame) (s : GhostRing2 R) (h5 : C5 R s) (h6 : C6 R s)
    (g : Fin R.m) :
    (Live ((view R s).epoch g) ↔ Live (s.epoch g).cur) ∧
    (DeliveredAt ((view R s).epoch g) (s.k g) ↔ ∃ q c d, (s.epoch g).cur = .delivered q c d) := by
  have ht := h6 g
  cases hc : (s.epoch g).cur with
  | idle =>
    have hp := h5 g
    cases he : (s.epoch g).prev with
    | idle =>
      by_cases hz : s.k g = 0
      · simp [view,prefixView,combinedView,hc,he,hz,Live,DeliveredAt]
      · have hn : ¬ s.k g ≤ s.k g-1 := by omega
        simp [view,prefixView,combinedView,hc,he,hz,Live,DeliveredAt,hn]
    | outbound q c => simp only [PrevShape,he] at hp
    | returning q c d => simp only [PrevShape,he] at hp
    | delivered q c d =>
      simp only [PrevShape,he] at hp
      have hk : s.k g = q+1 := hp.1
      simp [view,prefixView,combinedView,hc,he,Live,DeliveredAt,hk]
  | outbound q c =>
    have hq : q = s.k g := by simpa [hc,CurrentTag] using ht
    simp [view,prefixView,combinedView,hc,Live,DeliveredAt,hq]
  | returning q c d =>
    have hq : q = s.k g := by simpa [hc,CurrentTag] using ht
    simp [view,prefixView,combinedView,hc,Live,DeliveredAt,hq]
  | delivered q c d =>
    have hq : q = s.k g := by simpa [hc,CurrentTag] using ht
    simp [view,prefixView,combinedView,hc,Live,DeliveredAt,hq]

/-- Exact owner-port encoding of the current transaction. -/
def epochCw : GapEpoch → CwPort
  | .idle => .toSend
  | .outbound _ _ | .returning _ _ _ => .waiting
  | .delivered _ c d => resCw c d

theorem owner_port_exact (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (g : Fin R.m) :
    (s.cfg (rootV R g)).cwPort = some (epochCw (s.epoch g).cur) := by
  cases he : (s.epoch g).cur with
  | idle => exact hs.idleSend g he
  | outbound q c => exact (hs.waiting g).mpr (by rw [he]; trivial)
  | returning q c d => exact (hs.waiting g).mpr (by rw [he]; trivial)
  | delivered q c d =>
    have hv := (view_owner_tests R s hs.previous hs.current g).2.mpr ⟨q,c,d,he⟩
    obtain ⟨x,y,hx,hy,hw⟩ := hs.coherent.outgoingValue g hv
    have ht := hs.current g
    have hq : q = s.k g := by simpa [he,CurrentTag] using ht
    have hshape := hs.coherent.shape g
    simp only [EpochShape,prefixView,combinedView,he] at hshape
    change s.hist g (s.k g) = some x at hx
    change s.hist (next R g) (s.k g) = some y at hy
    have hxc : x = c := Option.some.inj (hx.symm.trans (hq ▸ hshape.2.2.1))
    have hyd : y = d := Option.some.inj (hy.symm.trans (hq ▸ hshape.2.2.2.1))
    change (s.cfg (rootV R g)).cwPort = some (resCw x y) at hw
    simpa only [he,epochCw,hxc,hyd] using hw

/-- A live or delivered current payload is the owner's actual choice. -/
theorem owner_choice_of_current (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (q : Nat) (c : Choice)
    (he : (s.epoch g).cur = .outbound q c ∨
      ∃ d, (s.epoch g).cur = .returning q c d ∨ (s.epoch g).cur = .delivered q c d) :
    (s.cfg (rootV R g)).choice = some c := by
  obtain ⟨x,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root x cw ccw at hroot
  have hhist : s.hist g q = some c ∧ q = s.k g := by
    have ht := hs.current g
    have hshape := hs.coherent.shape g
    rcases he with he | ⟨d,he | he⟩
    all_goals simp only [he,CurrentTag] at ht
    all_goals simp only [he,prefixView,combinedView,EpochShape] at hshape
    · exact ⟨hshape.2.2.1,ht⟩
    · exact ⟨hshape.2.2.1,ht⟩
    · exact ⟨hshape.2.2.1,ht⟩
  have hh := hs.coherent.histNow g x cw ccw hroot
  change s.hist g (s.k g) = resolvedOpt x at hh
  have hx : resolvedOpt x = some c := hh.symm.trans (hhist.2 ▸ hhist.1)
  rw [hroot]
  cases x <;> simp_all [resolvedOpt,Agent.choice]

private theorem epochCw_interior_row (k : Nat) (E : GapEpoch) (t : Slot) (b : Agent) :
    epochCw (rowEpoch k E (.interior t) b) = epochCw E := by
  cases b with
  | interior u => cases t <;> cases u <;> rfl
  | root c cw ccw => cases t <;> cases ccw <;> cases E <;> rfl

private theorem raw_owner_positive (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (hp : 0 < e.2.val) : rawAt R s.cfg e (rootV R e.1) = s.cfg (rootV R e.1) := by
  have hl : rootV R e.1 ≠ e := by
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = e.2.val at hv
    omega
  have hr : rootV R e.1 ≠ rn R e := by
    by_cases he : e.2.val+1 < R.len e.1
    · rw [rn_of_lt R e he]
      intro h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = e.2.val+1 at hv
      omega
    · rw [rn_of_last R e he]
      intro h
      have hv := congrArg Sigma.fst h
      exact next_ne_self R e.1 hv.symm
  simp [rawAt,hl,hr]

/-- The owner port agrees exactly with the raw current epoch before JOIN.
This checks L1, the clean L2/L3 cases, V1, P1/P2/P3, and interior activity. -/
theorem raw_owner_port_exact (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) :
    (rawAt R s.cfg e (rootV R g)).cwPort = some (epochCw (rawEpochs R (curView R s) e g)) := by
  by_cases hg : g = e.1
  · subst g
    by_cases hp : 0 < e.2.val
    · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 e.2 hp
      change s.cfg e = .interior t at ht
      rw [raw_owner_positive R s e hp,rawEpochs,if_pos rfl]
      change (s.cfg (rootV R e.1)).cwPort = some (epochCw (rowEpoch (s.k e.1) (s.epoch e.1).cur (s.cfg e) (s.cfg (rn R e))))
      rw [ht,epochCw_interior_row]
      exact owner_port_exact R s hs e.1
    · have he : e = rootV R e.1 := by
        apply vtx_eq R
        · rfl
        · change e.2.val = 0; omega
      generalize hg : e.1 = g at he ⊢
      rw [he,rawAt,if_pos rfl,rawEpochs,if_pos rfl]
      change (row (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g)))).1.cwPort =
        some (epochCw (rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g)))))
      obtain ⟨x,cw,ccw,hroot⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root x cw ccw at hroot
      have hport := owner_port_exact R s hs g
      rw [hroot] at hport
      have hcw : cw = epochCw (s.epoch g).cur := Option.some.inj hport
      subst cw
      have hshape := current_token_shape R s hs g
      cases hc : (s.epoch g).cur with
      | idle =>
        rw [hc] at hshape hroot
        by_cases hh : 1 < (R.len g)
        · have ht := hshape ⟨1,hh⟩ (Nat.zero_lt_succ 0)
          change s.cfg ⟨g,⟨1,hh⟩⟩ = .interior .empty at ht
          rw [rn_root_first R g hh,hroot,ht]
          rfl
        · have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<(R.len g); omega)
          obtain ⟨d,dw,dd,hr⟩ := hs.coherent.roots (next R g)
          change s.cfg (rootV R (next R g)) = .root d dw dd at hr
          rw [hrn,hroot,hr]
          cases dd <;> rfl
      | outbound q c =>
        rw [hc] at hshape hroot
        obtain ⟨p,hp,hslots⟩ := hshape
        have hh : 1 < (R.len g) := by have := p.isLt; omega
        have ht := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
        change s.cfg ⟨g,⟨1,hh⟩⟩ = _ at ht
        rw [rn_root_first R g hh,hroot,ht]
        split <;> rfl
      | returning q c d =>
        have hx := owner_choice_of_current R s hs g q c (Or.inr ⟨d,Or.inl hc⟩)
        rw [hroot] at hx
        have hxc : x = c := Option.some.inj hx
        subst x
        rw [hc] at hshape hroot
        obtain ⟨p,hp,hslots⟩ := hshape
        have hh : 1 < (R.len g) := by have := p.isLt; omega
        have ht := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
        change s.cfg ⟨g,⟨1,hh⟩⟩ = _ at ht
        rw [rn_root_first R g hh,hroot,ht]
        split <;> rfl
      | delivered q c d =>
        rw [hc] at hshape hroot
        by_cases hh : 1 < (R.len g)
        · have ht := hshape ⟨1,hh⟩ (Nat.zero_lt_succ 0)
          change s.cfg ⟨g,⟨1,hh⟩⟩ = .interior .empty at ht
          rw [rn_root_first R g hh,hroot,ht]
          cases c <;> cases d <;> rfl
        · have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<(R.len g); omega)
          obtain ⟨y,dw,dd,hr⟩ := hs.coherent.roots (next R g)
          change s.cfg (rootV R (next R g)) = .root y dw dd at hr
          rw [hrn,hroot,hr]
          cases c <;> cases d <;> cases dd <;> rfl
  · rw [raw_cw_other R s hs e g hg,rawEpochs,if_neg hg]
    exact owner_port_exact R s hs g

private theorem joinA_eq_of_not_ready (a : Agent) (ha : joinReady a = false) :
    ShortGapLiteralRingRows.joinA a = a := by
  cases a with
  | interior t => rfl
  | root c cw ccw => cases cw <;> cases ccw <;> simp_all [joinReady,ShortGapLiteralRingRows.joinA]

/-- Without a root JOIN, the physical root equals its raw row output. -/
theorem root_cfg_no_join (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hf : fires R (physical2 R s) e g = false) :
    (ghostStep2 R s e).cfg (rootV R g) = rawAt R s.cfg e (rootV R g) := by
  by_cases hi : incident R e (rootV R g)
  · have hr : joinReady (rawAt R s.cfg e (rootV R g)) = false := by
      simpa [fires,physical2,hi] using hf
    rw [ghostStep2_physical]
    simp only [ringStepU,if_pos hi,joinTick,joinA_eq_of_not_ready _ hr]
  · have hl : rootV R g ≠ e := fun h => hi (Or.inl h)
    have hr : rootV R g ≠ rn R e := fun h => hi (Or.inr h)
    rw [ghostStep2_physical]
    simp [ringStepU,hi,rawAt,hl,hr]

/-- A firing root has the fresh physical form after JOIN. -/
theorem root_cfg_join (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hf : fires R (physical2 R s) e g = true) :
    (ghostStep2 R s e).cfg (rootV R g) = .root .race .toSend .free := by
  obtain ⟨hi,c,hc⟩ := (fires_iff R (physical2 R s) e g).mp hf
  change rawAt R s.cfg e (rootV R g) = .root c .heldDenial .heldDenial at hc
  rw [ghostStep2_physical]
  simp only [ringStepU,if_pos hi,joinTick,hc]
  rfl

theorem owner_port_exact_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) :
    ((ghostStep2 R s e).cfg (rootV R g)).cwPort =
      some (epochCw ((ghostStep2 R s e).epoch g).cur) := by
  change _ = some (epochCw (epochStep2 R s e g).cur)
  rw [epochStep2_cur]
  cases hf : fires R (physical2 R s) e g with
  | true => rw [root_cfg_join R s e g hf]; rfl
  | false =>
    simp only [Bool.false_eq_true,if_false]
    rw [root_cfg_no_join R s e g hf]
    exact raw_owner_port_exact R s hs e g

private theorem epochCw_waiting (E : GapEpoch) : epochCw E = .waiting ↔ Live E := by
  cases E with
  | idle => simp [epochCw,Live]
  | outbound q c => simp [epochCw,Live]
  | returning q c d => simp [epochCw,Live]
  | delivered q c d => cases c <;> cases d <;> simp [epochCw,Live,resCw,res,Verdict.cw]

private theorem epochCw_held (E : GapEpoch) :
    CwHeld (some (epochCw E)) ↔ ∃ q c d, E = .delivered q c d := by
  cases E with
  | idle => simp [epochCw,CwHeld]
  | outbound q c => simp [epochCw,CwHeld]
  | returning q c d => simp [epochCw,CwHeld]
  | delivered q c d => cases c <;> cases d <;> simp [epochCw,CwHeld,resCw,res,Verdict.cw]

/-- All five owner-port clauses, including exact receipt payloads, are
preserved. The archive and tag lemmas translate the current encoding
back into the original completed-prefix interpretation. -/
theorem C2_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C2 R (ghostStep2 R s e) := by
  have ht := C6_step R s hs e
  have hp := C5_step R s hs e
  have hw := owner_port_exact_step R s hs e
  have hv := view_owner_tests R (ghostStep2 R s e) hp ht
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro g
    rw [hw g,(hv g).1]
    simpa only [Option.some.injEq] using epochCw_waiting ((ghostStep2 R s e).epoch g).cur
  · intro g
    rw [hw g,(hv g).2]
    exact epochCw_held _
  · intro g h
    obtain ⟨q,c,d,hc⟩ := (hv g).2.mp h
    have htag := ht g
    have hq : q = (ghostStep2 R s e).k g := by simpa only [hc,CurrentTag] using htag
    have hr : rawEpochs R (curView R s) e g = .delivered q c d := by
      change (epochStep2 R s e g).cur = _ at hc
      rw [epochStep2_cur] at hc
      split at hc
      · cases hc
      · exact hc
    have hpay := raw_delivered_payloads R s hs e g q c d hr
    refine ⟨c,d,hq ▸ hpay.1,hq ▸ hpay.2,?_⟩
    simpa only [hc,epochCw] using hw g
  · intro g hc
    simpa only [hc,epochCw] using hw g
  · intro g
    rw [hw g]
    simpa only [Option.some.injEq] using epochCw_waiting ((ghostStep2 R s e).epoch g).cur


theorem vtx_snd (R : VFrame) {g : Fin R.m} {a b : Fin (R.len g)}
    (h : (⟨g,a⟩ : Vtx R) = ⟨g,b⟩) : a = b :=
  Fin.ext (congrArg (fun v : Vtx R => v.2.val) h)

theorem tokenPos2_of_unique (R : VFrame) (s : GhostRing2 R) (g : Fin R.m)
    (p : Fin (R.len g)) (hp : 0 < p.val) (t : Slot) (ht : t ≠ .empty)
    (hs : ∀ a : Fin (R.len g), 0 < a.val → s.cfg ⟨g,a⟩ = .interior (if a=p then t else .empty)) :
    tokenPos R (curView R s) g = p.val := tokenPos_of_unique R (curView R s) g p hp t ht hs
theorem prelaunch_token (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g)) :
    OneToken R (curView R (ghostStep2 R s (rootV R g))) g (.decl (resolveInit c)) := by
  have hr := prelaunch_row R s hs g c ccw hc hh
  have hempty := toSend_empty_gap2 R s hs g (by rw [hc]; rfl)
  refine ⟨⟨1,hh⟩,Nat.zero_lt_succ 0,?_⟩
  intro a ha
  have hleft : ⟨g,a⟩ ≠ rootV R g := by
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change a.val = 0 at hv
    omega
  have hright : ⟨g,a⟩ = rn R (rootV R g) ↔ a = ⟨1,hh⟩ := by
    rw [rn_root_first R g hh]
    exact ⟨fun h => vtx_snd R h,fun h => congrArg (fun a => (⟨g,a⟩ : Vtx R)) h⟩
  change (ghostStep2 R s (rootV R g)).cfg ⟨g,a⟩ = _
  rw [cfg_step_pair,if_neg hleft,hr]
  by_cases he : a = ⟨1,hh⟩
  · rw [if_pos (hright.mpr he),if_pos he]; rfl
  · rw [if_neg (fun h => he (hright.mp h)),if_neg he]
    exact hempty a ha

/-- Hence the real bounded scan identifies the new token's position. -/
theorem prelaunch_tokenPos (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g)) :
    tokenPos R (curView R (ghostStep2 R s (rootV R g))) g = 1 := by
  obtain ⟨p,hp,hslots⟩ := prelaunch_token R s hs g c ccw hc hh
  have hfirst := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  have hpone : p = ⟨1,hh⟩ := by
    by_cases he : p = ⟨1,hh⟩
    · exact he
    · have hp' : (⟨1,hh⟩ : Fin (R.len g)) ≠ p := Ne.symm he
      rw [if_neg hp'] at hfirst
      have hslot := (prelaunch_token R s hs g c ccw hc hh)
      have hr := prelaunch_row R s hs g c ccw hc hh
      have hne : (⟨g,⟨1,hh⟩⟩ : Vtx R) ≠ rootV R g := by
        intro heq
        have hv := congrArg (fun v : Vtx R => v.2.val) heq
        change 1 = 0 at hv; omega
      change (ghostStep2 R s (rootV R g)).cfg ⟨g,⟨1,hh⟩⟩ = .interior .empty at hfirst
      rw [cfg_step_pair,if_neg hne,← rn_root_first R g hh,if_pos rfl,hr] at hfirst
      cases hfirst
  rw [tokenPos2_of_unique R (ghostStep2 R s (rootV R g)) g p hp
    (.decl (resolveInit c)) (by intro h; cases h) hslots]
  rw [hpone]

theorem prelaunch_current_epoch (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g)) :
    ((ghostStep2 R s (rootV R g)).epoch g).cur = .outbound (s.k g) (resolveInit c) := by
  have hf := prelaunch_no_joins R s hs g c ccw hc hh g
  have hslot := toSend_empty_gap2 R s hs g (by rw [hc]; rfl) ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  change s.cfg ⟨g,⟨1,hh⟩⟩ = .interior .empty at hslot
  change (epochStep2 R s (rootV R g) g).cur = _
  rw [epochStep2_cur,hf]
  simp only [Bool.false_eq_true,if_false]
  rw [rawEpochs,if_pos rfl]
  change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
  rw [hc,rn_root_first R g hh,hslot]
  rfl

theorem token_move_pair (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (a b p p' : Fin (R.len g)) (t u : Slot)
    (hl : e = ⟨g,a⟩) (hr : rn R e = ⟨g,b⟩)
    (hp : p = a ∨ p = b) (hp' : p' = a ∨ p' = b)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then t else .empty))
    (hrow : row (s.cfg e) (s.cfg (rn R e)) =
      (.interior (if a = p' then u else .empty),.interior (if b = p' then u else .empty))) :
    ∀ x : Fin (R.len g), 0 < x.val → (ghostStep2 R s e).cfg ⟨g,x⟩ =
      .interior (if x = p' then u else .empty) := by
  intro x hx
  rw [cfg_step_pair,hrow]
  by_cases h0 : ⟨g,x⟩ = e
  · rw [if_pos h0]
    have hxa : x = a := vtx_snd R (h0.trans hl)
    subst x; rfl
  · rw [if_neg h0]
    by_cases h1 : ⟨g,x⟩ = rn R e
    · rw [if_pos h1]
      have hxb : x = b := vtx_snd R (h1.trans hr)
      subst x; rfl
    · rw [if_neg h1,hslots x hx]
      have hn : x ≠ p := by
        intro he; subst x
        rcases hp with hp | hp
        · exact h0 (by rw [hl,hp])
        · exact h1 (by rw [hr,hp])
      have hn' : x ≠ p' := by
        intro he; subst x
        rcases hp' with hp' | hp'
        · exact h0 (by rw [hl,hp'])
        · exact h1 (by rw [hr,hp'])
      rw [if_neg hn,if_neg hn']

theorem boundary_token_replace (R : VFrame) (s : GhostRing2 R) (g : Fin R.m)
    (p : Fin (R.len g)) (_hp : 0 < p.val) (hlast : p.val+1 = (R.len g)) (t u : Slot)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then t else .empty))
    (hrow : (row (s.cfg ⟨g,p⟩) (s.cfg (rn R ⟨g,p⟩))).1 = .interior u) :
    ∀ x : Fin (R.len g), 0 < x.val → (ghostStep2 R s ⟨g,p⟩).cfg ⟨g,x⟩ =
      .interior (if x = p then u else .empty) := by
  intro x hx
  have hrn : rn R ⟨g,p⟩ = rootV R (next R g) :=
    rn_of_last R ⟨g,p⟩ (by change ¬ p.val+1 < (R.len g); omega)
  have hr : ⟨g,x⟩ ≠ rn R ⟨g,p⟩ := by
    rw [hrn]
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change x.val = 0 at hv
    omega
  rw [cfg_step_pair]
  by_cases he : x = p
  · have hl : (⟨g,x⟩ : Vtx R) = ⟨g,p⟩ := congrArg (fun a => (⟨g,a⟩ : Vtx R)) he
    rw [if_pos hl,hrow,if_pos he]
    rfl
  · have hl : (⟨g,x⟩ : Vtx R) ≠ ⟨g,p⟩ := fun h => he (vtx_snd R h)
    rw [if_neg hl,if_neg hr,hslots x hx,if_neg he,if_neg he]

/-- K1/K2 comparison turns the last declaration into a reply in the same
slot. The entry cut proves that the receiver is free; no extra hop is charged. -/
theorem declaration_epoch (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (c : Choice)
    (hc : s.cfg ⟨g,a⟩ = .interior (.decl c)) :
    (s.epoch g).cur = .outbound (s.k g) c ∧
      ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = a then .decl c else .empty) := by
  have ht := hs.current g
  have hshape := current_token_shape R s hs g
  cases he : (s.epoch g).cur with
  | idle =>
    rw [he] at hshape
    have hx := hshape a ha
    change s.cfg ⟨g,a⟩ = .interior .empty at hx
    rw [hc] at hx; cases hx
  | delivered q x y =>
    rw [he] at hshape
    have hx := hshape a ha
    change s.cfg ⟨g,a⟩ = .interior .empty at hx
    rw [hc] at hx; cases hx
  | outbound q x =>
    have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg ⟨g,a⟩ = _ at hx
    rw [hc] at hx
    by_cases hap : a = p
    · rw [if_pos hap] at hx
      cases hx
      exact ⟨by rw [hq],by simpa only [curView,← hap] using hslots⟩
    · rw [if_neg hap] at hx; cases hx
  | returning q x y =>
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg ⟨g,a⟩ = _ at hx
    rw [hc] at hx
    split at hx <;> cases hx

/-- K1/K2's free receiver belongs to exactly the declaration's round. -/
theorem comparison_generations (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (hc : (s.epoch g).cur = .outbound (s.k g) c)
    (hf : (s.cfg (rootV R (next R g))).ccwPort = some .free) :
    s.k (next R g) = s.k g := by
  have hshape := hs.coherent.shape g
  simp only [prefixView,combinedView,hc,EpochShape] at hshape
  have hn : ¬ s.k (next R g) < s.k g := by
    intro h
    have hi := (hs.coherent.incoming g).mpr (by
      change ComparedAt ((view R s).epoch g) (s.k (next R g))
      simpa only [view,prefixView,combinedView,hc,ComparedAt] using h)
    change CcwHeld (s.cfg (rootV R (next R g))).ccwPort at hi
    rw [hf] at hi
    exact hi
  rcases hshape.2.1 with he | he
  · exact he
  · omega

/-- General K1/K2 boundary package: comparison records the receiver,
creates a unique reply, retires prev, and handles either right-root JOIN
outcome. The selected owner cannot JOIN at this positive-offset edge. -/
theorem boundary_comparison (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (hlast : a.val+1 = (R.len g))
    (c d : Choice) (cw : CwPort)
    (hl : s.cfg ⟨g,a⟩ = .interior (.decl c))
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    let t := ghostStep2 R s ⟨g,a⟩
    let q := s.k g
    (t.epoch g).cur = .returning q c (resolveResp d) ∧
    (t.epoch g).prev = .idle ∧ t.k g = q ∧
    t.k (next R g) = q + (if fires R (physical2 R s) ⟨g,a⟩ (next R g) then 1 else 0) ∧
    t.hist g q = some c ∧ t.hist (next R g) q = some (resolveResp d) ∧
    OneToken R (curView R t) g (.reply (resolveResp d)) ∧
    (t.cfg (rootV R (next R g))).ccwPort = some
      (if fires R (physical2 R s) ⟨g,a⟩ (next R g) then .free else resCcw c (resolveResp d)) := by
  dsimp only
  obtain ⟨he,hslots⟩ := declaration_epoch R s hs g a ha c hl
  have hgen := comparison_generations R s hs g c he (by rw [hr]; rfl)
  have hrn : rn R ⟨g,a⟩ = rootV R (next R g) := rn_of_last R _ (by change ¬a.val+1<(R.len g); omega)
  have hraw : rawEpochs R (curView R s) ⟨g,a⟩ g = .returning (s.k g) c (resolveResp d) := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩)) = _
    rw [he,hl,hrn,hr]; rfl
  have hO := no_owner_join_at_positive R s ⟨g,a⟩ ha
  have hcur : ((ghostStep2 R s ⟨g,a⟩).epoch g).cur = .returning (s.k g) c (resolveResp d) := by
    change (epochStep2 R s ⟨g,a⟩ g).cur = _
    simp [epochStep2_cur,hO,hraw]
  have hprev : ((ghostStep2 R s ⟨g,a⟩).epoch g).prev = .idle := by
    change (epochStep2 R s ⟨g,a⟩ g).prev = _
    simp [epochStep2,hO,hl,hrn,hr,compares]
  have hk : (ghostStep2 R s ⟨g,a⟩).k g = s.k g := by simp [ghostStep2_k,hO]
  have hkR : (ghostStep2 R s ⟨g,a⟩).k (next R g) = s.k g +
      (if fires R (physical2 R s) ⟨g,a⟩ (next R g) then 1 else 0) := by rw [ghostStep2_k,hgen]
  have hshape := hs.coherent.shape g
  simp only [prefixView,combinedView,he,EpochShape] at hshape
  have hpayL := history2_monotone R s ⟨g,a⟩ g (s.k g) c hshape.2.2.1
  have hnr : rootV R (next R g) ≠ ⟨g,a⟩ := by
    intro h
    have hz := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = a.val at hz
    omega
  have hrraw : rawAt R s.cfg ⟨g,a⟩ (rootV R (next R g)) =
      .root (resolveResp d) cw (resCcw c (resolveResp d)) := by
    rw [rawAt,if_neg hnr,if_pos hrn.symm,hl,hrn,hr]; rfl
  have hpayR := raw_choice_recorded R s hs ⟨g,a⟩ (next R g) (Or.inr hrn.symm)
    (resolveResp d) (by rw [hrraw]; rfl)
  rw [hgen] at hpayR
  have hslots' := boundary_token_replace R s g a ha hlast
    (.decl c) (.reply (resolveResp d)) hslots (by rw [hl,hrn,hr]; rfl)
  refine ⟨hcur,hprev,hk,hkR,hpayL,hpayR,⟨a,ha,hslots'⟩,?_⟩
  cases hf : fires R (physical2 R s) ⟨g,a⟩ (next R g) with
  | true => rw [root_cfg_join R s ⟨g,a⟩ (next R g) hf]; rfl
  | false => rw [root_cfg_no_join R s ⟨g,a⟩ (next R g) hf,hrraw]; rfl

/-- The three original right-port clauses at one gap. -/
def C3At (R : VFrame) (s : GhostRing2 R) (g : Fin R.m) : Prop :=
  (CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔ ComparedAt ((view R s).epoch g) (s.k (next R g))) ∧
  (ComparedAt ((view R s).epoch g) (s.k (next R g)) →
    ∃ c d, s.hist g (s.k (next R g)) = some c ∧ s.hist (next R g) (s.k (next R g)) = some d ∧
      (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)) ∧
  (CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g).cur (s.k (next R g)) ∨ PreviousResult (s.epoch g).prev (s.k (next R g)))

theorem C3_iff_forall (R : VFrame) (s : GhostRing2 R) : C3 R s ↔ ∀ g, C3At R s g := by
  constructor
  · intro h g; exact ⟨h.incomingPrefix g,h.incomingValue g,h.incoming g⟩
  · intro h; exact ⟨fun g => (h g).1,fun g => (h g).2.1,fun g => (h g).2.2⟩

/-- C1 and all three C3 clauses for the selected K1/K2 gap, including
the receiver's optional JOIN in the very same physical interaction. -/
theorem C1_C3_step_comparison (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (hlast : a.val+1 = (R.len g))
    (c d : Choice) (cw : CwPort)
    (hl : s.cfg ⟨g,a⟩ = .interior (.decl c))
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    EpochShape R (view R (ghostStep2 R s ⟨g,a⟩)) g ∧ C3At R (ghostStep2 R s ⟨g,a⟩) g := by
  obtain ⟨hc,hp,hk,hkR,hcH,hdH,hslots,hw⟩ := boundary_comparison R s hs g a ha hlast c d cw hl hr
  have hv : (view R (ghostStep2 R s ⟨g,a⟩)).epoch g = .returning (s.k g) c (resolveResp d) := by
    simp [view,prefixView,combinedView,hc]
  constructor
  · rw [EpochShape,hv]
    refine ⟨hk,?_,hcH,hdH,hslots⟩
    change (ghostStep2 R s ⟨g,a⟩).k (next R g) = s.k g ∨
      (ghostStep2 R s ⟨g,a⟩).k (next R g) = s.k g+1
    rw [hkR]
    split
    · exact Or.inr rfl
    · exact Or.inl (Nat.add_zero _)
  · have hh : CcwHeld (some (resCcw c (resolveResp d))) := by
      cases c <;> cases d <;> trivial
    unfold C3At
    rw [hv,hc,hp,hkR,hw]
    cases hf : fires R (physical2 R s) ⟨g,a⟩ (next R g) with
    | true =>
      simp [ComparedAt,CurrentResult,PreviousResult,CcwHeld]
      intro h
      omega
    | false =>
      simp only [Bool.false_eq_true,if_false,Nat.add_zero]
      refine ⟨?_,?_,?_⟩
      · exact ⟨fun _ => Nat.le_refl _,fun _ => hh⟩
      · intro _; exact ⟨c,resolveResp d,hcH,hdH,rfl⟩
      · exact ⟨fun _ => Or.inl rfl,fun _ => hh⟩

/-- Already established historical denials persist under every physical step. -/
theorem historicalDenial_step (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (q : Nat) (h : HistoricalDenial R (view R s) g q) :
    HistoricalDenial R (view R (ghostStep2 R s e)) g q := by
  obtain ⟨c,d,hc,hd,hr⟩ := h
  exact ⟨c,d,history2_monotone R s e g q c hc,history2_monotone R s e (next R g) q d hd,hr⟩

/-- K1/K2 extends the selected gap's payload prefix by its newly compared
round and preserves every strict-prefix denial. -/
theorem prefix_step_comparison (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (hlast : a.val+1 = (R.len g))
    (c d : Choice) (cw : CwPort)
    (hl : s.cfg ⟨g,a⟩ = .interior (.decl c))
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    (∀ q, ComparedAt ((view R (ghostStep2 R s ⟨g,a⟩)).epoch g) q →
      ∃ x y, (ghostStep2 R s ⟨g,a⟩).hist g q = some x ∧
        (ghostStep2 R s ⟨g,a⟩).hist (next R g) q = some y) ∧
    (∀ q, BeforeLatest ((view R (ghostStep2 R s ⟨g,a⟩)).epoch g) q →
      HistoricalDenial R (view R (ghostStep2 R s ⟨g,a⟩)) g q) := by
  obtain ⟨he,_⟩ := declaration_epoch R s hs g a ha c hl
  obtain ⟨hc,_,_,_,hcH,hdH,_,_⟩ := boundary_comparison R s hs g a ha hlast c d cw hl hr
  have hv : (view R (ghostStep2 R s ⟨g,a⟩)).epoch g = .returning (s.k g) c (resolveResp d) := by
    simp [view,prefixView,combinedView,hc]
  constructor
  · intro q hq
    rw [hv] at hq
    change q ≤ s.k g at hq
    by_cases hlt : q < s.k g
    · have hpre : ComparedAt ((view R s).epoch g) q := by
        simpa only [view,prefixView,combinedView,he,ComparedAt] using hlt
      obtain ⟨x,y,hx,hy⟩ := hs.coherent.prefixPayloads g q hpre
      exact ⟨x,y,history2_monotone R s ⟨g,a⟩ g q x hx,history2_monotone R s ⟨g,a⟩ (next R g) q y hy⟩
    · have hqeq : q = s.k g := by omega
      exact hqeq ▸ ⟨c,resolveResp d,hcH,hdH⟩
  · intro q hq
    have hpre : BeforeLatest ((view R s).epoch g) q := by
      simpa only [view,prefixView,combinedView,he,hc,BeforeLatest] using hq
    exact historicalDenial_step R s ⟨g,a⟩ g q (hs.coherent.prefixDenials g q hpre)

/-- Direct P1 preserves the selected gap's epoch shape and all right-port
clauses for all four combinations of endpoint JOINs. If both JOIN, the
completed-prefix interpretation reconstructs the delivered round from
the two records written by this same physical edge. -/
theorem C1_C3_step_P1 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hh : R.len g = 1) (c d : Choice) (ccw : CcwPort) (cw : CwPort)
    (hl : s.cfg (rootV R g) = .root c .toSend ccw)
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    EpochShape R (view R (ghostStep2 R s (rootV R g))) g ∧
      C3At R (ghostStep2 R s (rootV R g)) g := by
  let e := rootV R g
  let t := ghostStep2 R s e
  let q := s.k g
  let C := resolveInit c
  let D := resolveResp d
  change EpochShape R (view R t) g ∧ C3At R t g
  have hrn : rn R e = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<(R.len g); omega)
  have hgen := direct_generations R (view R s) hs.coherent g
    (by change (s.cfg (rootV R g)).cwPort = _; rw [hl]; rfl)
    (by change (s.cfg (rootV R (next R g))).ccwPort = _; rw [hr]; rfl)
  change s.k g = s.k (next R g) at hgen
  have hraw : rawEpochs R (curView R s) e g = .delivered q C D := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R e)) = _
    rw [hl,hrn,hr]; rfl
  have hpay := raw_delivered_payloads R s hs e g q C D hraw
  change t.hist g q = some C ∧ t.hist (next R g) q = some D at hpay
  have hcur : (t.epoch g).cur = if fires R (physical2 R s) e g then .idle else .delivered q C D := by
    change (epochStep2 R s e g).cur = _
    rw [epochStep2_cur,hraw]
  have hprev : (t.epoch g).prev = if fires R (physical2 R s) e (next R g) then .idle
      else if fires R (physical2 R s) e g then .delivered q C D else .idle := by
    change (epochStep2 R s e g).prev = _
    have hl' : s.cfg e = .root c .toSend ccw := hl
    cases hO : fires R (physical2 R s) e g <;> cases hR : fires R (physical2 R s) e (next R g) <;>
      simp [epochStep2,hl',hrn,hr,compares,hraw,hO,hR,if_pos (show g = e.1 from rfl)]
  have hkO : t.k g = q + if fires R (physical2 R s) e g then 1 else 0 := ghostStep2_k R s e g
  have hkR : t.k (next R g) = q + if fires R (physical2 R s) e (next R g) then 1 else 0 := by
    change (ghostStep2 R s e).k (next R g) = _
    rw [ghostStep2_k,← hgen]
  have hv : (view R t).epoch g = .delivered q C D := by
    cases hO : fires R (physical2 R s) e g <;> cases hR : fires R (physical2 R s) e (next R g) <;>
      simp [view,prefixView,combinedView,hcur,hprev,hO,hR,hkO,hpay.1,hpay.2]
  have hw : (t.cfg (rootV R (next R g))).ccwPort = some
      (if fires R (physical2 R s) e (next R g) then .free else resCcw C D) := by
    cases hf : fires R (physical2 R s) e (next R g) with
    | true => rw [root_cfg_join R s e (next R g) hf]; rfl
    | false =>
      rw [root_cfg_no_join R s e (next R g) hf]
      have hn : rootV R (next R g) ≠ e := by rw [← hrn]; exact rn_ne_self R e
      have hl' : s.cfg e = .root c .toSend ccw := hl
      rw [rawAt,if_neg hn,if_pos hrn.symm,hl',hrn,hr]; rfl
  constructor
  · rw [EpochShape,hv]
    refine ⟨?_,?_,hpay.1,hpay.2,?_⟩
    · change t.k g = q ∨ t.k g = q+1
      rw [hkO]
      split
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
    · change t.k (next R g) = q ∨ t.k (next R g) = q+1
      rw [hkR]
      split
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
    · intro a ha
      have hb := a.isLt
      omega
  · have hheld : CcwHeld (some (resCcw C D)) := by
      dsimp only [C,D]
      cases c <;> cases d <;> trivial
    unfold C3At
    rw [hv,hcur,hprev,hkR,hw]
    cases hO : fires R (physical2 R s) e g <;> cases hR : fires R (physical2 R s) e (next R g)
    all_goals simp only [Bool.false_eq_true,if_false,if_true,Nat.add_zero]
    all_goals first |
      (exact ⟨⟨fun _ => Nat.le_refl _,fun _ => hheld⟩,
        fun _ => ⟨C,D,hpay.1,hpay.2,rfl⟩,
        ⟨fun _ => Or.inl rfl,fun _ => hheld⟩⟩) |
      (exact ⟨⟨fun _ => Nat.le_refl _,fun _ => hheld⟩,
        fun _ => ⟨C,D,hpay.1,hpay.2,rfl⟩,
        ⟨fun _ => Or.inr rfl,fun _ => hheld⟩⟩) |
      (simp [ComparedAt,CurrentResult,PreviousResult,CcwHeld]; intro h; omega)

/-- If the receiver has caught up with the owner, prev cannot represent
the receiver's current round. This uses exactly the retained tag clause. -/
theorem previous_not_current (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hk : s.k g ≤ s.k (next R g)) :
    ¬ PreviousResult (s.epoch g).prev (s.k (next R g)) := by
  have hp := hs.previous g
  cases he : (s.epoch g).prev with
  | idle => exact id
  | outbound q c => simp only [PrevShape,he] at hp
  | returning q c d => simp only [PrevShape,he] at hp
  | delivered q c d =>
    simp only [PrevShape,he] at hp
    change ¬ q = s.k (next R g)
    omega

/-- V1's selected gap satisfies full C1 and C3 after either owner JOIN
outcome. The receiver is not incident, so its generation and receipt
remain unchanged; a transferred delivery occupies prev when cur resets. -/
theorem C1_C3_step_V1 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (q : Nat) (c d : Choice) (hh : 1 < (R.len g))
    (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x.val = 1 then .reply d else .empty)) :
    EpochShape R (view R (ghostStep2 R s (rootV R g))) g ∧
      C3At R (ghostStep2 R s (rootV R g)) g := by
  let e := rootV R g
  let t := ghostStep2 R s e
  change EpochShape R (view R t) g ∧ C3At R t g
  have htag := hs.current g
  have hq : q = s.k g := by simpa only [he,CurrentTag] using htag
  have hshape := hs.coherent.shape g
  simp only [prefixView,combinedView,he,EpochShape] at hshape
  have hbound : s.k (next R g) = q ∨ s.k (next R g) = q+1 := hshape.2.1
  obtain ⟨x,ccw,hroot⟩ := waiting_root R s hs g (by rw [he]; trivial)
  have hx := owner_choice_of_current R s hs g q c (Or.inr ⟨d,Or.inl he⟩)
  rw [hroot] at hx
  have hxc : x = c := Option.some.inj hx
  subst x
  have hrn : rn R e = ⟨g,⟨1,hh⟩⟩ := rn_root_first R g hh
  have hrslot : s.cfg ⟨g,⟨1,hh⟩⟩ = .interior (.reply d) := by simpa using hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  have hraw : rawEpochs R (curView R s) e g = .delivered q c d := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R e)) = _
    rw [he,hroot,hrn,hrslot]; rfl
  have hpay := raw_delivered_payloads R s hs e g q c d hraw
  change t.hist g q = some c ∧ t.hist (next R g) q = some d at hpay
  have hnotR : ¬ incident R e (rootV R (next R g)) := by
    rintro (h | h)
    · exact next_ne_self R g (congrArg Sigma.fst h)
    · rw [hrn] at h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = 1 at hv
      omega
  have hR : fires R (physical2 R s) e (next R g) = false := by simp [fires,hnotR]
  have hkR : t.k (next R g) = s.k (next R g) := by simp [t,ghostStep2_k,hR]
  have hcfgR : t.cfg (rootV R (next R g)) = s.cfg (rootV R (next R g)) := by
    rw [ghostStep2_physical]
    exact if_neg hnotR
  have hkO : t.k g = q + if fires R (physical2 R s) e g then 1 else 0 := by
    change (ghostStep2 R s e).k g = _
    rw [ghostStep2_k,← hq]
  have hcur : (t.epoch g).cur = if fires R (physical2 R s) e g then .idle else .delivered q c d := by
    change (epochStep2 R s e g).cur = _
    rw [epochStep2_cur,hraw]
  have hprev : (t.epoch g).prev = if fires R (physical2 R s) e g then .delivered q c d else (s.epoch g).prev := by
    change (epochStep2 R s e g).prev = _
    have hl : s.cfg e = .root c .waiting ccw := hroot
    cases hO : fires R (physical2 R s) e g <;>
      simp [epochStep2,hR,hO,hraw,hl,hrn,hrslot,compares]
  have hv : (view R t).epoch g = .delivered q c d := by
    cases hO : fires R (physical2 R s) e g <;> simp [view,prefixView,combinedView,hcur,hprev,hO]
  have hempty : EmptyGap R (view R t) g := by
    intro a ha
    change (ghostStep2 R s e).cfg ⟨g,a⟩ = .interior .empty
    rw [cfg_step_pair]
    have hn : ⟨g,a⟩ ≠ e := by
      intro h
      have hz := congrArg (fun v : Vtx R => v.2.val) h
      change a.val = 0 at hz
      omega
    rw [if_neg hn]
    by_cases har : ⟨g,a⟩ = rn R e
    · rw [if_pos har]
      change ShortGapLiteralRingRows.joinA (row (s.cfg (rootV R g)) (s.cfg (rn R e))).2 = _
      rw [hroot,hrn,hrslot]; rfl
    · have ha1 : a.val ≠ 1 := by
        intro h
        apply har
        rw [hrn]
        exact congrArg (fun a => (⟨g,a⟩ : Vtx R)) (Fin.ext h)
      rw [if_neg har,hslots a ha,if_neg ha1]
  have hprevN := previous_not_current R s hs g (by omega)
  have hheld : CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔ q = s.k (next R g) := by
    have h := hs.incoming g
    simpa only [he,CurrentResult,or_false,iff_false,not_false_eq_true,hprevN] using h
  constructor
  · rw [EpochShape,hv]
    refine ⟨?_,?_,hpay.1,hpay.2,hempty⟩
    · change t.k g = q ∨ t.k g = q+1
      rw [hkO]
      split
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
    · change t.k (next R g) = q ∨ t.k (next R g) = q+1
      rw [hkR]
      exact hbound
  · unfold C3At
    rw [hv,hcfgR,hkR,hcur,hprev]
    refine ⟨?_,?_,?_⟩
    · have h := hs.coherent.incoming g
      simpa only [prefixView,combinedView,he,ComparedAt] using h
    · intro h
      have hpre : ComparedAt ((view R s).epoch g) (s.k (next R g)) := by
        simpa only [view,prefixView,combinedView,he,ComparedAt] using h
      obtain ⟨x,y,hx,hy,hw⟩ := hs.coherent.incomingValue g hpre
      exact ⟨x,y,history2_monotone R s e g _ x hx,history2_monotone R s e (next R g) _ y hy,hw⟩
    · cases hO : fires R (physical2 R s) e g with
      | false => simpa only [Bool.false_eq_true,if_false,CurrentResult,hprevN,or_false] using hheld
      | true => simpa only [if_true,CurrentResult,PreviousResult,false_or] using hheld

private theorem identity_annotations (k : Nat) (E : GapEpoch) (a b : Agent)
    (h : row a b = (a,b)) : rowEpoch k E a b = E ∧ compares a b = false := by
  cases a with
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> exact ⟨rfl,rfl⟩
    | root d cw ccw =>
      cases t <;> cases ccw
      all_goals first | exact ⟨rfl,rfl⟩ | (simp [row] at h)
  | root c cw ccw =>
    cases b with
    | interior t =>
      cases cw <;> cases t
      all_goals first | exact ⟨rfl,rfl⟩ | (simp [row] at h)
    | root d dw dd =>
      cases cw <;> cases dd
      all_goals first | exact ⟨rfl,rfl⟩ |
        (cases c <;> cases d <;> simp [row,resolveInit,resolveResp,resCw,res,Verdict.cw] at h)

private theorem record_of_saved (H : Nat → Option Choice) (k : Nat) (d : Choice)
    (hh : H k = some d) : record H k d = H := by
  funext r
  by_cases hr : r = k
  · subst r; simp [record,hh]
  · simp [record,hr]

private theorem ghost2_ext {R : VFrame} {s t : GhostRing2 R}
    (hc : ∀ v, s.cfg v = t.cfg v) (hk : ∀ i, s.k i = t.k i)
    (hh : ∀ i r, s.hist i r = t.hist i r) (he : ∀ g, s.epoch g = t.epoch g) : s = t := by
  have hc' := funext hc
  have hk' := funext hk
  have hh' := funext (fun i => funext (hh i))
  have he' := funext he
  cases s
  cases t
  cases hc'
  cases hk'
  cases hh'
  cases he'
  rfl

/-- A literal pair identity is an identity of the full two-epoch state
on Lineage2, including history and both retained annotations. -/
theorem ghostStep2_noop (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (hrow : row (s.cfg e) (s.cfg (rn R e)) = (s.cfg e,s.cfg (rn R e))) :
    ghostStep2 R s e = s := by
  have hraw : ∀ v, rawAt R s.cfg e v = s.cfg v := by
    intro v
    by_cases h0 : v = e
    · simp [rawAt,hrow,h0]
    · by_cases h1 : v = rn R e
      · simp [rawAt,hrow,h1,rn_ne_self]
      · simp [rawAt,h0,h1]
  have hfire : ∀ i, fires R (physical2 R s) e i = false := by
    intro i
    have hn := hs.coherent.normalized i
    change joinReady (s.cfg (rootV R i)) = false at hn
    simp [fires,physical2,hraw,hn]
  have hjoin : ∀ v, ShortGapLiteralRingRows.joinA (s.cfg v) = s.cfg v := by
    intro v
    by_cases hp : 0 < v.2.val
    · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent v.1 v.2 hp
      change s.cfg v = .interior t at ht
      rw [ht]; rfl
    · have hv : v = rootV R v.1 := by
        apply vtx_eq R
        · rfl
        · change v.2.val = 0; omega
      rw [hv]
      exact joinA_eq_of_not_ready _ (hs.coherent.normalized v.1)
  have hE : ∀ g, rawEpochs R (curView R s) e g = (s.epoch g).cur := by
    intro g
    by_cases hg : g = e.1
    · rw [rawEpochs,if_pos hg]
      exact (identity_annotations _ _ _ _ hrow).1
    · exact if_neg hg
  have hcomp : compares (s.cfg e) (s.cfg (rn R e)) = false := (identity_annotations 0 .idle _ _ hrow).2
  apply ghost2_ext
  · intro v
    rw [ghostStep2_physical]
    simp [ringStepU,joinTick,hraw,hjoin]
  · intro i; simp [ghostStep2_k,hfire]
  · intro i r
    by_cases hi : incident R e (rootV R i)
    · obtain ⟨d,cw,ccw,hr,hd,_⟩ := raw_root_resolved R s hs e i hi
      have hroot : s.cfg (rootV R i) = .root d cw ccw := (hraw _).symm.trans hr
      have hh := hs.coherent.histNow i d cw ccw hroot
      change s.hist i (s.k i) = resolvedOpt d at hh
      have hh' : s.hist i (s.k i) = some d := by cases d <;> simp_all [resolvedOpt]
      rw [history_step_record R s e i hi d cw ccw hr hd,record_of_saved _ _ _ hh']
    · change (if incident R e (rootV R i) then
        updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i) else s.hist i) r = s.hist i r
      rw [if_neg hi]
  · intro g
    change epochStep2 R s e g = s.epoch g
    simp [epochStep2,hfire,hE,hcomp]

/-- Full closure for every actual no-op pair, including K3 and clean
waiting/stationary rows; all eight clauses are preserved together. -/
theorem lineage2_step_noop (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (hrow : row (s.cfg e) (s.cfg (rn R e)) = (s.cfg e,s.cfg (rn R e))) :
    Lineage2 R (ghostStep2 R s e) := by
  rw [ghostStep2_noop R s hs e hrow]
  exact hs


theorem join_requires_neighbors_of_lineage2 (R : VFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) (i : Fin R.m) (hi : fires R (physical2 R s) e i = true) :
    s.k i ≤ s.k (next R i) ∧ s.k i ≤ s.k (prev R i) :=
  join_requires_neighbors_of_lineage R (view R s) hs.coherent e i hi

theorem neighborSkew_step_of_lineage2 (R : VFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) : NeighborSkew R (physical2 R (ghostStep2 R s e)) := by
  intro i
  have hb := neighborSkew_of_lineage2 R s hs i
  change s.k i ≤ s.k (next R i)+1 ∧ s.k (next R i) ≤ s.k i+1 at hb
  have hl : fires R (physical2 R s) e i = true → s.k i ≤ s.k (next R i) :=
    fun h => (join_requires_neighbors_of_lineage2 R s hs e i h).1
  have hr : fires R (physical2 R s) e (next R i) = true → s.k (next R i) ≤ s.k i := by
    intro h
    simpa only [prev_next] using (join_requires_neighbors_of_lineage2 R s hs e (next R i) h).2
  change (ghostStep2 R s e).k i ≤ (ghostStep2 R s e).k (next R i)+1 ∧
    (ghostStep2 R s e).k (next R i) ≤ (ghostStep2 R s e).k i+1
  cases h1 : fires R (physical2 R s) e i <;> cases h2 : fires R (physical2 R s) e (next R i) <;>
    simp_all [ghostStep2_k] <;> omega
private theorem row_left_ccw (c : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent) :
    (row (.root c cw ccw) b).1.ccwPort = some ccw := by
  cases b with
  | interior t => cases t <;> cases cw <;> rfl
  | root d dw dd => cases cw <;> cases dd <;> rfl

/-- An unscheduled gap's right port is unchanged by the raw row. The
shared root may still JOIN afterward, which is handled separately. -/
theorem raw_ccw_other (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (rawAt R s.cfg e (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort := by
  have hn : rootV R (next R g) ≠ rn R e := by
    by_cases hp : e.2.val+1 < R.len e.1
    · rw [rn_of_lt R e hp]
      intro h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = e.2.val+1 at hv
      omega
    · rw [rn_of_last R e hp]
      intro h
      have hnext : next R g = next R e.1 := congrArg Sigma.fst h
      have hprev := congrArg (prev R) hnext
      exact hg (by simpa only [prev_next] using hprev)
  by_cases ht : rootV R (next R g) = e
  · obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots (next R g)
    change s.cfg (rootV R (next R g)) = .root c cw ccw at hroot
    have hl : s.cfg e = .root c cw ccw := ht ▸ hroot
    rw [rawAt,if_pos ht,hl,hroot]
    exact row_left_ccw c cw ccw _
  · rw [rawAt,if_neg ht,if_neg hn]

/-- For an unscheduled gap, a right JOIN requires a receipt that was
already present before the raw row. -/
theorem other_right_join_held (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e (next R g) = true) :
    CcwHeld (s.cfg (rootV R (next R g))).ccwPort := by
  obtain ⟨_,c,hc⟩ := (fires_iff R (physical2 R s) e (next R g)).mp hf
  change rawAt R s.cfg e (rootV R (next R g)) = .root c .heldDenial .heldDenial at hc
  have hp := raw_ccw_other R s hs e g hg
  rw [hc] at hp
  rw [← hp]
  trivial

/-- Outside the scheduled gap, the two annotations change only through
owner transfer and right retirement, with right retirement taking precedence. -/
theorem epoch_other (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hg : g ≠ e.1) :
    ((ghostStep2 R s e).epoch g).cur =
      (if fires R (physical2 R s) e g then .idle else (s.epoch g).cur) ∧
    ((ghostStep2 R s e).epoch g).prev =
      (if fires R (physical2 R s) e (next R g) then .idle
       else if fires R (physical2 R s) e g then (s.epoch g).cur else (s.epoch g).prev) := by
  have he : rawEpochs R (curView R s) e g = (s.epoch g).cur := if_neg hg
  constructor
  · change (epochStep2 R s e g).cur = _
    rw [epochStep2_cur,he]
  · change (epochStep2 R s e g).prev = _
    cases ho : fires R (physical2 R s) e g <;>
      cases hr : fires R (physical2 R s) e (next R g) <;>
      simp [epochStep2,ho,hr,he,hg]

/-- The effective completed-prefix epoch of an unscheduled gap is
unchanged, even when either or both shared roots JOIN. A cleared archive
is reconstructed from the owner's counter and immutable history. -/
theorem view_epoch_other (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (view R (ghostStep2 R s e)).epoch g = (view R s).epoch g := by
  obtain ⟨hcur,hprev⟩ := epoch_other R s e g hg
  have hshape := hs.coherent.shape g
  have ht := hs.current g
  cases he : (s.epoch g).cur with
  | outbound q c =>
    have hO : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true =>
        obtain ⟨x,y,hc⟩ := other_join_current_delivered R s hs e g hg hf
        rw [he] at hc; cases hc
    simp [view,prefixView,combinedView,hcur,hO,he]
  | returning q c d =>
    have hO : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true =>
        obtain ⟨x,y,hc⟩ := other_join_current_delivered R s hs e g hg hf
        rw [he] at hc; cases hc
    simp [view,prefixView,combinedView,hcur,hO,he]
  | delivered q c d =>
    have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
    simp only [prefixView,combinedView,he,EpochShape] at hshape
    have hL := history2_monotone R s e g q c hshape.2.2.1
    have hR := history2_monotone R s e (next R g) q d hshape.2.2.2.1
    cases hO : fires R (physical2 R s) e g <;>
      cases hJ : fires R (physical2 R s) e (next R g) <;>
      simp [view,prefixView,combinedView,hcur,hprev,hO,hJ,he,ghostStep2_k,← hq,hL,hR]
  | idle =>
    have hO : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true =>
        obtain ⟨x,y,hc⟩ := other_join_current_delivered R s hs e g hg hf
        rw [he] at hc; cases hc
    have hk : (ghostStep2 R s e).k g = s.k g := by simp [ghostStep2_k,hO]
    have hp := hs.previous g
    cases hep : (s.epoch g).prev with
    | outbound q c => simp only [PrevShape,hep] at hp
    | returning q c d => simp only [PrevShape,hep] at hp
    | delivered q c d =>
      simp only [PrevShape,hep] at hp
      have hL := history2_monotone R s e g q c hp.2.2.1
      have hR := history2_monotone R s e (next R g) q d hp.2.2.2
      cases hJ : fires R (physical2 R s) e (next R g) <;>
        simp [view,prefixView,combinedView,hcur,hprev,hO,hJ,he,hep,hk,hp.1,hL,hR]
    | idle =>
      by_cases hz : s.k g = 0
      · simp [view,prefixView,combinedView,hcur,hprev,hO,he,hep,hk,hz]
      · simp only [prefixView,combinedView,he,hep,hz,if_false,EpochShape] at hshape
        have hL := history2_monotone R s e g (s.k g-1) _ hshape.2.2.1
        have hR := history2_monotone R s e (next R g) (s.k g-1) _ hshape.2.2.2.1
        simp [view,prefixView,combinedView,hcur,hprev,hO,he,hep,hk,hz,hL,hR]

/-- Adjacent-gap receipt equality includes the optional clear performed
by right JOIN. The raw interaction itself does not write this port. -/
theorem ccw_other_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    ((ghostStep2 R s e).cfg (rootV R (next R g))).ccwPort =
      if fires R (physical2 R s) e (next R g) then some .free
      else (s.cfg (rootV R (next R g))).ccwPort := by
  cases hf : fires R (physical2 R s) e (next R g) with
  | true => rw [root_cfg_join R s e (next R g) hf]; rfl
  | false =>
    rw [root_cfg_no_join R s e (next R g) hf]
    exact raw_ccw_other R s hs e g hg

theorem other_owner_join_view (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e g = true) :
    ∃ c d, (view R s).epoch g = .delivered (s.k g) c d := by
  obtain ⟨c,d,hc⟩ := other_join_current_delivered R s hs e g hg hf
  exact ⟨c,d,by simp [view,prefixView,combinedView,hc]⟩

theorem other_right_join_compared (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e (next R g) = true) :
    ComparedAt ((view R s).epoch g) (s.k (next R g)) :=
  (hs.coherent.incoming g).mp (other_right_join_held R s hs e g hg hf)

private theorem empty_other (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hg : g ≠ e.1) (h : EmptyGap R (view R s) g) : EmptyGap R (view R (ghostStep2 R s e)) g := by
  intro a ha
  change (ghostStep2 R s e).cfg ⟨g,a⟩ = _
  rw [other_gap_interior R s e g hg a ha]
  exact h a ha

private theorem token_other (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hg : g ≠ e.1) (t : Slot) (h : OneToken R (view R s) g t) :
    OneToken R (view R (ghostStep2 R s e)) g t := by
  obtain ⟨p,hp,hslots⟩ := h
  refine ⟨p,hp,?_⟩
  intro a ha
  change (ghostStep2 R s e).cfg ⟨g,a⟩ = _
  rw [other_gap_interior R s e g hg a ha]
  exact hslots a ha

/-- C1 for every unscheduled gap, including both adjacent gaps and
all four combinations of its endpoint JOINs. No global band is assumed. -/
theorem C1_step_adjacent (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    EpochShape R (view R (ghostStep2 R s e)) g := by
  have hp := hs.coherent.shape g
  have heq := view_epoch_other R s hs e g hg
  have hO := other_owner_join_view R s hs e g hg
  have hR := other_right_join_compared R s hs e g hg
  cases he : (view R s).epoch g with
  | idle =>
    have ho : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true => obtain ⟨c,d,hc⟩ := hO hf; rw [he] at hc; cases hc
    have hr : fires R (physical2 R s) e (next R g) = false := by
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => rfl
      | true => have h := hR hf; rw [he] at h; exact False.elim h
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    exact ⟨by simpa [view,prefixView,combinedView,ghostStep2_k,ho] using hp.1,
      by simpa [view,prefixView,combinedView,ghostStep2_k,hr] using hp.2.1,
      empty_other R s e g hg hp.2.2⟩
  | outbound q c =>
    have ho : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true => obtain ⟨c,d,hc⟩ := hO hf; rw [he] at hc; cases hc
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    refine ⟨?_,?_,history2_monotone R s e g q c hp.2.2.1,token_other R s e g hg _ hp.2.2.2⟩
    · change (ghostStep2 R s e).k g = q
      simpa [view,prefixView,combinedView,ghostStep2_k,ho] using hp.1
    · change (ghostStep2 R s e).k (next R g) = q ∨ (ghostStep2 R s e).k (next R g)+1 = q
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => simpa [view,prefixView,combinedView] using hp.2.1
      | true =>
        have h := hR hf
        rw [he] at h
        change s.k (next R g) < q at h
        have hb : s.k (next R g) = q ∨ s.k (next R g)+1 = q := hp.2.1
        exact Or.inl (by simp only [if_true]; omega)
  | returning q c d =>
    have ho : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true => obtain ⟨c,d,hc⟩ := hO hf; rw [he] at hc; cases hc
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    refine ⟨?_,?_,history2_monotone R s e g q c hp.2.2.1,
      history2_monotone R s e (next R g) q d hp.2.2.2.1,token_other R s e g hg _ hp.2.2.2.2⟩
    · change (ghostStep2 R s e).k g = q
      simpa [view,prefixView,combinedView,ghostStep2_k,ho] using hp.1
    · change (ghostStep2 R s e).k (next R g) = q ∨ (ghostStep2 R s e).k (next R g) = q+1
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => simpa [view,prefixView,combinedView] using hp.2.1
      | true =>
        have h := hR hf
        rw [he] at h
        change s.k (next R g) ≤ q at h
        have hb : s.k (next R g) = q ∨ s.k (next R g) = q+1 := hp.2.1
        exact Or.inr (by simp only [if_true]; omega)
  | delivered q c d =>
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    refine ⟨?_,?_,history2_monotone R s e g q c hp.2.2.1,
      history2_monotone R s e (next R g) q d hp.2.2.2.1,empty_other R s e g hg hp.2.2.2.2⟩
    · change (ghostStep2 R s e).k g = q ∨ (ghostStep2 R s e).k g = q+1
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e g with
      | false => simpa [view,prefixView,combinedView] using hp.1
      | true =>
        obtain ⟨x,y,hc⟩ := hO hf
        rw [he] at hc
        have hk : q = s.k g := by cases hc; rfl
        exact Or.inr (by simp [hk])
    · change (ghostStep2 R s e).k (next R g) = q ∨ (ghostStep2 R s e).k (next R g) = q+1
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => simpa [view,prefixView,combinedView] using hp.2.1
      | true =>
        have h := hR hf
        rw [he] at h
        change s.k (next R g) ≤ q at h
        have hb : s.k (next R g) = q ∨ s.k (next R g) = q+1 := hp.2.1
        exact Or.inr (by simp only [if_true]; omega)

/-- A right JOIN consumes the last comparison belonging to that root's
old generation; the effective epoch cannot cover its incremented counter. -/
theorem other_right_join_exhausts_compared (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e (next R g) = true) :
    ¬ ComparedAt ((view R s).epoch g) (s.k (next R g)+1) := by
  have hp := hs.coherent.shape g
  have hc := other_right_join_compared R s hs e g hg hf
  have hkL : (view R s).k g = s.k g := rfl
  have hkR : (view R s).k (next R g) = s.k (next R g) := rfl
  change EpochShape R (view R s) g at hp
  cases he : (view R s).epoch g <;> rw [EpochShape,he] at hp
  all_goals simp only [he,ComparedAt] at hc ⊢
  all_goals first | exact False.elim hc | omega

private theorem currentResult_compared (R : VFrame) (s : GhostRing2 R) (g : Fin R.m)
    (q : Nat) (hc : CurrentResult (s.epoch g).cur q) : ComparedAt ((view R s).epoch g) q := by
  cases he : (s.epoch g).cur <;> simp only [he,CurrentResult] at hc
  all_goals first | exact False.elim hc |
    (simpa only [view,prefixView,combinedView,he,ComparedAt,hc] using Nat.le_refl q)

/-- All three C3 clauses hold for every unscheduled gap, with no
assumption of post-state lineage and no restriction on endpoint JOINs. -/
theorem C3_step_adjacent (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) : C3At R (ghostStep2 R s e) g := by
  have heq := view_epoch_other R s hs e g hg
  have hw := ccw_other_step R s hs e g hg
  obtain ⟨hcur,hprev⟩ := epoch_other R s e g hg
  have hk := ghostStep2_k R s e (next R g)
  unfold C3At
  rw [heq,hw,hk]
  cases hR : fires R (physical2 R s) e (next R g) with
  | false =>
    simp only [Bool.false_eq_true,if_false,Nat.add_zero]
    refine ⟨hs.coherent.incoming g,?_,?_⟩
    · intro h
      obtain ⟨c,d,hc,hd,hv⟩ := hs.coherent.incomingValue g h
      exact ⟨c,d,history2_monotone R s e g _ c hc,history2_monotone R s e (next R g) _ d hd,hv⟩
    · rw [hcur,hprev,hR]
      cases hO : fires R (physical2 R s) e g with
      | false => simpa only [Bool.false_eq_true,if_false] using hs.incoming g
      | true =>
        obtain ⟨c,d,he⟩ := other_join_current_delivered R s hs e g hg hO
        have hsupport := join_requires_neighbors_of_lineage2 R s hs e g hO
        have hn := previous_not_current R s hs g hsupport.1
        have hi := hs.incoming g
        simp only [he,CurrentResult,hn,or_false] at hi
        simpa only [Bool.false_eq_true,if_false,if_true,he,CurrentResult,PreviousResult,false_or] using hi
  | true =>
    simp only [if_true]
    have hn := other_right_join_exhausts_compared R s hs e g hg hR
    refine ⟨⟨False.elim,fun h => False.elim (hn h)⟩,?_,?_⟩
    · intro h; exact False.elim (hn h)
    · rw [hcur,hprev,hR]
      cases hO : fires R (physical2 R s) e g with
      | true => exact ⟨False.elim,fun h => h.elim id id⟩
      | false =>
        refine ⟨False.elim,?_⟩
        intro h
        rcases h with h | h
        · exact hn (currentResult_compared R s g _ h)
        · exact h

/-- Historical payload and strict-denial prefixes for every unscheduled
gap persist because its effective epoch is unchanged. -/
theorem prefix_step_adjacent (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (∀ q, ComparedAt ((view R (ghostStep2 R s e)).epoch g) q →
      ∃ c d, (ghostStep2 R s e).hist g q = some c ∧ (ghostStep2 R s e).hist (next R g) q = some d) ∧
    (∀ q, BeforeLatest ((view R (ghostStep2 R s e)).epoch g) q →
      HistoricalDenial R (view R (ghostStep2 R s e)) g q) := by
  have he := view_epoch_other R s hs e g hg
  constructor
  · intro q hq
    rw [he] at hq
    obtain ⟨c,d,hc,hd⟩ := hs.coherent.prefixPayloads g q hq
    exact ⟨c,d,history2_monotone R s e g q c hc,history2_monotone R s e (next R g) q d hd⟩
  · intro q hq
    rw [he] at hq
    exact historicalDenial_step R s e g q (hs.coherent.prefixDenials g q hq)

private theorem resCw_denial (c d : Choice) (h : resCw c d = .heldDenial) : res c d = .denial := by
  cases c <;> cases d <;> simp_all [resCw,res,Verdict.cw]

private theorem resCcw_denial (c d : Choice) (h : resCcw c d = .heldDenial) : res c d = .denial := by
  cases c <;> cases d <;> simp_all [resCcw,res,Verdict.ccw]

theorem raw_current_tag (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) : CurrentTag (s.k g) (rawEpochs R (curView R s) e g) := by
  by_cases hg : g = e.1
  · rw [rawEpochs,if_pos hg]
    exact currentTag_rowEpoch _ _ _ _ (hs.current g)
  · rw [rawEpochs,if_neg hg]
    exact hs.current g

/-- The new completed owner round has an outgoing historical denial:
its raw delivered payloads agree with the physical denial consumed by JOIN. -/
theorem joined_outgoing_denial (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hf : fires R (physical2 R s) e g = true) :
    HistoricalDenial R (view R (ghostStep2 R s e)) g (s.k g) := by
  obtain ⟨q,c,d,he⟩ := owner_join_raw_delivered R s hs e g hf
  have ht := raw_current_tag R s hs e g
  have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
  obtain ⟨_,x,hraw⟩ := (fires_iff R (physical2 R s) e g).mp hf
  change rawAt R s.cfg e (rootV R g) = .root x .heldDenial .heldDenial at hraw
  have hp := raw_owner_port_exact R s hs e g
  rw [hraw,he] at hp
  have hd : resCw c d = .heldDenial := (Option.some.inj hp).symm
  have hh := raw_delivered_payloads R s hs e g q c d he
  exact hq ▸ ⟨c,d,hh.1,hh.2,resCw_denial c d hd⟩

private theorem row_right_ccw_no_compare (a : Agent) (d : Choice) (cw : CwPort) (ccw : CcwPort)
    (hn : compares a (.root d cw ccw) = false) :
    (row a (.root d cw ccw)).2.ccwPort = some ccw := by
  cases a with
  | interior t => cases t <;> cases ccw <;> first | rfl | cases hn
  | root c x y => cases x <;> cases ccw <;> first | rfl | cases hn

/-- When no comparison is performed, every raw right-facing receipt
is preserved, including the scheduled gap's receipt. -/
theorem raw_ccw_no_compare (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hn : compares (s.cfg e) (s.cfg (rn R e)) = false) :
    (rawAt R s.cfg e (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort := by
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root c cw ccw at hroot
  by_cases hl : rootV R (next R g) = e
  · have he : s.cfg e = .root c cw ccw := hl ▸ hroot
    rw [rawAt,if_pos hl,he,hroot]
    exact row_left_ccw _ _ _ _
  · by_cases hr : rootV R (next R g) = rn R e
    · have he : s.cfg (rn R e) = .root c cw ccw := hr ▸ hroot
      rw [rawAt,if_neg hl,if_pos hr,he,hroot]
      exact row_right_ccw_no_compare _ _ _ _ (by simpa only [he] using hn)
    · rw [rawAt,if_neg hl,if_neg hr]

private theorem comparison_inputs (a b : Agent) (h : compares a b = true) :
    (∃ c d cw, a = .interior (.decl c) ∧ b = .root d cw .free) ∨
    (∃ c ccw d cw, a = .root c .toSend ccw ∧ b = .root d cw .free) := by
  cases a with
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> cases h
    | root d cw ccw =>
      cases t <;> cases ccw <;> first | exact Or.inl ⟨_,_,_,rfl,rfl⟩ | cases h
  | root c cw ccw =>
    cases b with
    | interior u => cases cw <;> cases u <;> cases h
    | root d dw dd =>
      cases cw <;> cases dd <;> first | exact Or.inr ⟨_,_,_,_,rfl,rfl⟩ | cases h

private theorem root_input_zero (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (c : Choice) (cw : CwPort) (ccw : CcwPort) (he : s.cfg e = .root c cw ccw) :
    e.2.val = 0 := by
  by_cases hp : 0 < e.2.val
  · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 e.2 hp
    change s.cfg e = .interior t at ht
    rw [he] at ht; cases ht
  · omega

private theorem root_receiver_last (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (he : s.cfg (rn R e) = .root c cw ccw) :
    e.2.val+1 = (R.len e.1) ∧ rn R e = rootV R (next R e.1) := by
  have hz := root_input_zero R s hs (rn R e) c cw ccw he
  have hn : ¬ e.2.val+1 < R.len e.1 := by
    intro h
    rw [rn_of_lt R e h] at hz
    change e.2.val+1 = 0 at hz
    omega
  exact ⟨by have := e.2.isLt; omega,rn_of_last R e hn⟩

/-- The raw denial at a gap's right root is a historical denial in that
root's old generation, whether inherited or newly written by K1/P1. -/
theorem raw_right_denial_history (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (hd : (rawAt R s.cfg e (rootV R (next R g))).ccwPort = some .heldDenial) :
    HistoricalDenial R (view R (ghostStep2 R s e)) g (s.k (next R g)) := by
  have old : (s.cfg (rootV R (next R g))).ccwPort = some .heldDenial →
      HistoricalDenial R (view R (ghostStep2 R s e)) g (s.k (next R g)) := by
    intro hp
    have hc := (hs.coherent.incoming g).mp (by change CcwHeld (s.cfg (rootV R (next R g))).ccwPort; rw [hp]; trivial)
    obtain ⟨c,d,hc,hd',hv⟩ := hs.coherent.incomingValue g hc
    change (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d) at hv
    rw [hp] at hv
    exact ⟨c,d,history2_monotone R s e g _ c hc,history2_monotone R s e (next R g) _ d hd',
      resCcw_denial c d (Option.some.inj hv).symm⟩
  by_cases hg : g = e.1
  · cases hcomp : compares (s.cfg e) (s.cfg (rn R e)) with
    | false => exact old ((raw_ccw_no_compare R s hs e g hcomp).symm.trans hd)
    | true =>
      rcases comparison_inputs _ _ hcomp with ⟨c,d,cw,hl,hr⟩ | ⟨c,ccw,d,cw,hl,hr⟩
      · obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d cw .free hr
        rw [← hg] at hrn
        have ha : 0 < e.2.val := by
          by_cases hz : e.2.val = 0
          · have he : e = rootV R g := by
              apply vtx_eq R
              · exact hg.symm
              · exact hz
            obtain ⟨x,xw,xc,hroot⟩ := hs.coherent.roots g
            change s.cfg (rootV R g) = .root x xw xc at hroot
            rw [he,hroot] at hl; cases hl
          · omega
        subst g
        have hl' : s.cfg ⟨e.1,e.2⟩ = .interior (.decl c) := hl
        have hr' : s.cfg (rootV R (next R e.1)) = .root d cw .free := hrn ▸ hr
        have hcur := (declaration_epoch R s hs e.1 e.2 ha c hl').1
        have hgen := comparison_generations R s hs e.1 c hcur (by rw [hr']; rfl)
        have hx := boundary_comparison R s hs e.1 e.2 ha hlast c d cw hl' hr'
        have hnr : rootV R (next R e.1) ≠ e := by rw [← hrn]; exact rn_ne_self R e
        rw [rawAt,if_neg hnr,if_pos hrn.symm,hl,hr] at hd
        have hv : resCcw c (resolveResp d) = .heldDenial := Option.some.inj hd
        rw [hgen]
        exact ⟨c,resolveResp d,hx.2.2.2.2.1,hx.2.2.2.2.2.1,resCcw_denial _ _ hv⟩
      · obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d cw .free hr
        rw [← hg] at hrn
        have hz := root_input_zero R s hs e c .toSend ccw hl
        have he : e = rootV R g := by
          apply vtx_eq R
          · exact hg.symm
          · exact hz
        have hl' : s.cfg (rootV R g) = .root c .toSend ccw := he ▸ hl
        have hr' : s.cfg (rootV R (next R g)) = .root d cw .free := hrn ▸ hr
        have hgen := direct_generations R (view R s) hs.coherent g
          (by change (s.cfg (rootV R g)).cwPort = _; rw [hl']; rfl)
          (by change (s.cfg (rootV R (next R g))).ccwPort = _; rw [hr']; rfl)
        change s.k g = s.k (next R g) at hgen
        have hraw : rawEpochs R (curView R s) e g = .delivered (s.k g) (resolveInit c) (resolveResp d) := by
          rw [rawEpochs,if_pos hg]
          change rowEpoch (s.k g) (s.epoch g).cur (s.cfg e) (s.cfg (rn R e)) = _
          rw [hl,hr]; rfl
        have hpay := raw_delivered_payloads R s hs e g (s.k g) (resolveInit c) (resolveResp d) hraw
        have hnr : rootV R (next R g) ≠ e := by rw [← hrn]; exact rn_ne_self R e
        rw [rawAt,if_neg hnr,if_pos hrn.symm,hl,hr] at hd
        have hv : resCcw (resolveInit c) (resolveResp d) = .heldDenial := Option.some.inj hd
        rw [← hgen]
        exact ⟨resolveInit c,resolveResp d,hpay.1,hpay.2,resCcw_denial _ _ hv⟩
  · exact old ((raw_ccw_other R s hs e g hg).symm.trans hd)

/-- JOIN consumes an incoming denial in the root's old generation. -/
theorem joined_incoming_denial (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hf : fires R (physical2 R s) e i = true) :
    HistoricalDenial R (view R (ghostStep2 R s e)) (prev R i) (s.k i) := by
  obtain ⟨_,c,hc⟩ := (fires_iff R (physical2 R s) e i).mp hf
  change rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial at hc
  have hd : (rawAt R s.cfg e (rootV R (next R (prev R i)))).ccwPort = some .heldDenial := by
    rw [next_prev,hc]; rfl
  simpa only [next_prev] using raw_right_denial_history R s hs e (prev R i) hd

/-- Every completed post-step round has both historical denials. -/
theorem completed_denials_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (r : Nat) (hr : r < (ghostStep2 R s e).k i) :
    HistoricalDenial R (view R (ghostStep2 R s e)) i r ∧
    HistoricalDenial R (view R (ghostStep2 R s e)) (prev R i) r := by
  by_cases ho : r < s.k i
  · have hh := hs.coherent.joinedDenials i r ho
    exact ⟨historicalDenial_step R s e i r hh.2.2.1,
      historicalDenial_step R s e (prev R i) r hh.2.2.2⟩
  · rw [ghostStep2_k] at hr
    cases hf : fires R (physical2 R s) e i with
    | false => simp only [hf,Bool.false_eq_true,if_false,Nat.add_zero] at hr; omega
    | true =>
      simp only [hf,if_true] at hr
      have he : r = s.k i := by omega
      subst r
      exact ⟨joined_outgoing_denial R s hs e i hf,joined_incoming_denial R s hs e i hf⟩

/-- Shape alone places completed owner rounds in both incident prefixes. -/
theorem completed_coverage_of_C1 (R : VFrame) (s : GhostRing2 R) (h1 : C1 R s)
    (i : Fin R.m) (r : Nat) (hr : r < s.k i) :
    DeliveredAt ((view R s).epoch i) r ∧ ComparedAt ((view R s).epoch (prev R i)) r := by
  have hl := h1 i
  have hp := h1 (prev R i)
  have hk : (view R s).k i = s.k i := rfl
  have hn : (view R s).k (next R (prev R i)) = s.k i := by rw [next_prev]; rfl
  constructor
  · cases he : (view R s).epoch i <;>
      simp only [EpochShape,he] at hl <;> simp only [DeliveredAt] <;> omega
  · cases he : (view R s).epoch (prev R i) <;>
      simp only [EpochShape,he] at hp <;> simp only [ComparedAt] <;> omega

/-- C7 follows from shape and the two denial records of completed rounds.
This derives the actual historical-prefix clause, not just neighbour skew. -/
theorem C7_of_C1_completed_denials (R : VFrame) (s : GhostRing2 R) (h1 : C1 R s)
    (hd : ∀ i r, r < s.k i → HistoricalDenial R (view R s) i r ∧
      HistoricalDenial R (view R s) (prev R i) r) : C7 R s := by
  have pay : ∀ i r, r < s.k i → ∃ c d, s.hist i r = some c ∧ s.hist (next R i) r = some d := by
    intro i r hr
    obtain ⟨c,d,hc,hd,_⟩ := (hd i r hr).1
    exact ⟨c,d,hc,hd⟩
  refine ⟨?_,?_,?_⟩
  · intro g r hc
    have hg := h1 g
    have hk : (view R s).k g = s.k g := rfl
    cases he : (view R s).epoch g with
    | idle => simp only [he,ComparedAt] at hc
    | outbound q c =>
      simp only [he,ComparedAt] at hc
      simp only [he,EpochShape] at hg
      exact pay g r (by omega)
    | returning q c d =>
      simp only [he,ComparedAt] at hc
      simp only [he,EpochShape] at hg
      by_cases hq : r < q
      · exact pay g r (by omega)
      · have heq : r = q := by omega
        subst r
        exact ⟨c,d,hg.2.2.1,hg.2.2.2.1⟩
    | delivered q c d =>
      simp only [he,ComparedAt] at hc
      simp only [he,EpochShape] at hg
      by_cases hq : r < q
      · exact pay g r (by omega)
      · have heq : r = q := by omega
        subst r
        exact ⟨c,d,hg.2.2.1,hg.2.2.2.1⟩
  · intro g r hr
    have hg := h1 g
    have hk : (view R s).k g = s.k g := rfl
    apply (hd g r ?_).1
    cases he : (view R s).epoch g <;>
      simp only [he,BeforeLatest] at hr <;> simp only [he,EpochShape] at hg <;> omega
  · intro i r hr
    exact ⟨(completed_coverage_of_C1 R s h1 i r hr).1,
      (completed_coverage_of_C1 R s h1 i r hr).2,hd i r hr⟩

/-- The only remaining premise for historical-prefix preservation is C1. -/
theorem C7_step_of_C1 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (h1 : C1 R (ghostStep2 R s e)) : C7 R (ghostStep2 R s e) :=
  C7_of_C1_completed_denials R _ h1 (completed_denials_step R s hs e)

private theorem view_epoch_of_unchanged (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (he : (ghostStep2 R s e).epoch g = s.epoch g)
    (hk : (ghostStep2 R s e).k g = s.k g) :
    (view R (ghostStep2 R s e)).epoch g = (view R s).epoch g := by
  have hc : (combinedView R (ghostStep2 R s e)).epoch g = (combinedView R s).epoch g := by
    simp only [combinedView,he]
  change (prefixView R (combinedView R (ghostStep2 R s e))).epoch g = _
  simp only [prefixView,hc]
  cases hh : (combinedView R s).epoch g <;> try rfl
  change (if (ghostStep2 R s e).k g = 0 then GapEpoch.idle else
    GapEpoch.delivered ((ghostStep2 R s e).k g-1)
      (((ghostStep2 R s e).hist g ((ghostStep2 R s e).k g-1)).getD .race)
      (((ghostStep2 R s e).hist (next R g) ((ghostStep2 R s e).k g-1)).getD .race)) = _
  rw [hk]
  by_cases hz : s.k g = 0
  · simp only [combinedView,hz,if_true]
  · have hp := hs.coherent.shape g
    change EpochShape R (prefixView R (combinedView R s)) g at hp
    simp only [EpochShape,prefixView,hh] at hp
    simp only [combinedView,hz,if_false] at hp
    have hl := history2_monotone R s e g _ _ hp.2.2.1
    have hr := history2_monotone R s e (next R g) _ _ hp.2.2.2.1
    simp only [combinedView,hz,if_false,hl,hr,Option.getD_some]

/-- A row with unchanged annotations and counters preserves the selected
clauses once its literal slot motion and right receipt have been checked. -/
theorem C1_C3_step_transport (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (he : (ghostStep2 R s e).epoch g = s.epoch g)
    (hk : (ghostStep2 R s e).k g = s.k g)
    (hr : (ghostStep2 R s e).k (next R g) = s.k (next R g))
    (hw : ((ghostStep2 R s e).cfg (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort)
    (hE : EmptyGap R (view R s) g → EmptyGap R (view R (ghostStep2 R s e)) g)
    (hT : ∀ t, OneToken R (view R s) g t → OneToken R (view R (ghostStep2 R s e)) g t) :
    EpochShape R (view R (ghostStep2 R s e)) g ∧ C3At R (ghostStep2 R s e) g := by
  have hv := view_epoch_of_unchanged R s hs e g he hk
  have hk' : (view R (ghostStep2 R s e)).k g = (view R s).k g := hk
  have hr' : (view R (ghostStep2 R s e)).k (next R g) = (view R s).k (next R g) := hr
  constructor
  · have hp := hs.coherent.shape g
    change EpochShape R (view R s) g at hp
    cases hh : (view R s).epoch g <;> simp only [EpochShape,hv,hh,hk',hr'] at hp ⊢
    · exact ⟨hp.1,hp.2.1,hE hp.2.2⟩
    · exact ⟨hp.1,hp.2.1,history2_monotone R s e _ _ _ hp.2.2.1,hT _ hp.2.2.2⟩
    · exact ⟨hp.1,hp.2.1,history2_monotone R s e _ _ _ hp.2.2.1,
        history2_monotone R s e _ _ _ hp.2.2.2.1,hT _ hp.2.2.2.2⟩
    · exact ⟨hp.1,hp.2.1,history2_monotone R s e _ _ _ hp.2.2.1,
        history2_monotone R s e _ _ _ hp.2.2.2.1,hE hp.2.2.2.2⟩
  · unfold C3At
    rw [hv,he,hr,hw]
    refine ⟨hs.coherent.incoming g,?_,hs.incoming g⟩
    intro h
    obtain ⟨c,d,hc,hd,hv⟩ := hs.coherent.incomingValue g h
    exact ⟨c,d,history2_monotone R s e _ _ _ hc,history2_monotone R s e _ _ _ hd,hv⟩

private theorem no_joins_of_row (R : VFrame) (s : GhostRing2 R) (e : Vtx R)
    (hl : joinReady (row (s.cfg e) (s.cfg (rn R e))).1 = false)
    (hr : joinReady (row (s.cfg e) (s.cfg (rn R e))).2 = false) :
    ∀ i, fires R (physical2 R s) e i = false := by
  intro i
  by_cases h0 : rootV R i = e
  · simp [fires,physical2,rawAt,h0,hl]
  · by_cases h1 : rootV R i = rn R e
    · simp [fires,physical2,rawAt,h1,rn_ne_self,hr]
    · simp [fires,physical2,incident,h0,h1]

private theorem epoch_unchanged_of_quiet (R : VFrame) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m)
    (hf : ∀ i, fires R (physical2 R s) e i = false)
    (hc : compares (s.cfg e) (s.cfg (rn R e)) = false)
    (he : rawEpochs R (curView R s) e g = (s.epoch g).cur) :
    (ghostStep2 R s e).epoch g = s.epoch g := by
  change epochStep2 R s e g = _
  simp [epochStep2,hf,hc,he]

private theorem C1_C3_step_quiet (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (hf : ∀ i, fires R (physical2 R s) e i = false)
    (hc : compares (s.cfg e) (s.cfg (rn R e)) = false)
    (he : rawEpochs R (curView R s) e g = (s.epoch g).cur)
    (hE : EmptyGap R (view R s) g → EmptyGap R (view R (ghostStep2 R s e)) g)
    (hT : ∀ t, OneToken R (view R s) g t → OneToken R (view R (ghostStep2 R s e)) g t) :
    EpochShape R (view R (ghostStep2 R s e)) g ∧ C3At R (ghostStep2 R s e) g := by
  apply C1_C3_step_transport R s hs e g (epoch_unchanged_of_quiet R s e g hf hc he)
    (by simp [ghostStep2_k,hf]) (by simp [ghostStep2_k,hf]) _ hE hT
  rw [root_cfg_no_join R s e (next R g) (hf _)]
  exact raw_ccw_no_compare R s hs e g hc

/-- Erase only root choices; ports and interior payloads remain literal. -/
private def portsSlots : Agent → Agent
  | .root _ cw ccw => .root .race cw ccw
  | .interior t => .interior t

private theorem joinReady_portsSlots (a : Agent) : joinReady (portsSlots a) = joinReady a := by
  cases a with
  | interior t => rfl
  | root c cw ccw => cases cw <;> cases ccw <;> rfl

private theorem normalized_vertex (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (v : Vtx R) : joinReady (s.cfg v) = false := by
  by_cases hp : 0 < v.2.val
  · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent v.1 v.2 hp
    change s.cfg v = .interior t at ht
    rw [ht]; rfl
  · have hv : v = rootV R v.1 := vtx_eq R _ _ rfl (by change v.2.val = 0; omega)
    rw [hv]
    exact hs.coherent.normalized v.1

/-- Resolution-only rows preserve C1 and C3 even when the history at
the current generation is first recorded during this interaction. -/
theorem C1_C3_step_resolution (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R)
    (hl : portsSlots (row (s.cfg e) (s.cfg (rn R e))).1 = portsSlots (s.cfg e))
    (hr : portsSlots (row (s.cfg e) (s.cfg (rn R e))).2 = portsSlots (s.cfg (rn R e)))
    (hc : compares (s.cfg e) (s.cfg (rn R e)) = false)
    (he : rawEpochs R (curView R s) e e.1 = (s.epoch e.1).cur) :
    EpochShape R (view R (ghostStep2 R s e)) e.1 ∧ C3At R (ghostStep2 R s e) e.1 := by
  have hf := no_joins_of_row R s e
    (by rw [← joinReady_portsSlots,hl,joinReady_portsSlots]; exact normalized_vertex R s hs e)
    (by rw [← joinReady_portsSlots,hr,joinReady_portsSlots]; exact normalized_vertex R s hs (rn R e))
  have hslots : ∀ a : Fin (R.len e.1), 0 < a.val →
      (ghostStep2 R s e).cfg ⟨e.1,a⟩ = s.cfg ⟨e.1,a⟩ := by
    intro a ha
    obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 a ha
    change s.cfg ⟨e.1,a⟩ = .interior t at ht
    have get : ∀ b : Agent, portsSlots b = .interior t → b = .interior t := by
      intro b hb
      cases b with
      | interior u => exact hb
      | root c cw ccw => cases hb
    rw [cfg_step_pair]
    by_cases h0 : ⟨e.1,a⟩ = e
    · rw [if_pos h0]
      have hh : s.cfg e = .interior t := h0 ▸ ht
      have hb := hl
      rw [hh] at hb
      have hb' := get _ hb
      rw [hh,hb',ht]; rfl
    · rw [if_neg h0]
      by_cases h1 : ⟨e.1,a⟩ = rn R e
      · rw [if_pos h1]
        have hb := hr
        rw [← h1,ht] at hb
        have hb' := get _ hb
        rw [← h1,ht,hb']; rfl
      · rw [if_neg h1]
  apply C1_C3_step_quiet R s hs e e.1 hf hc he
  · intro h a ha
    change (ghostStep2 R s e).cfg ⟨e.1,a⟩ = _
    rw [hslots a ha]
    exact h a ha
  · intro t h
    obtain ⟨p,hp,h⟩ := h
    refine ⟨p,hp,?_⟩
    intro a ha
    change (ghostStep2 R s e).cfg ⟨e.1,a⟩ = _
    rw [hslots a ha]
    exact h a ha

/-- Interior transport preserves both selected clauses for either
direction; the payload and unique-token position are checked literally. -/
theorem C1_C3_step_move (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (a b p p' : Fin (R.len g)) (t : Slot)
    (ha : 0 < a.val) (hb : 0 < b.val) (hp : 0 < p.val) (hp' : 0 < p'.val)
    (ht : t ≠ .empty) (hl : e = ⟨g,a⟩) (hr : rn R e = ⟨g,b⟩)
    (hpos : p = a ∨ p = b) (hpos' : p' = a ∨ p' = b)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then t else .empty))
    (hrow : row (s.cfg e) (s.cfg (rn R e)) =
      (.interior (if a = p' then t else .empty),.interior (if b = p' then t else .empty))) :
    EpochShape R (view R (ghostStep2 R s e)) g ∧ C3At R (ghostStep2 R s e) g := by
  have hf := no_joins_of_row R s e (by rw [hrow]; rfl) (by rw [hrow]; rfl)
  have hc : compares (s.cfg e) (s.cfg (rn R e)) = false := by
    rw [hr,hl,hslots a ha,hslots b hb]
    split <;> split <;> cases t <;> rfl
  have he : rawEpochs R (curView R s) e g = (s.epoch g).cur := by
    have hg : g = e.1 := by rw [hl]
    rw [rawEpochs,if_pos hg]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg e) (s.cfg (rn R e)) = _
    rw [hr,hl,hslots a ha,hslots b hb]
    split <;> split <;> cases t <;> rfl
  have hpost := token_move_pair R s e g a b p p' t t
    hl hr hpos hpos' hslots hrow
  have hcfg : s.cfg ⟨g,p⟩ = .interior t := by simpa using hslots p hp
  apply C1_C3_step_quiet R s hs e g hf hc he
  · intro hempty
    have hh := hempty p hp
    change s.cfg ⟨g,p⟩ = .interior .empty at hh
    rw [hcfg] at hh
    exact False.elim (ht (Agent.interior.inj hh))
  · intro u hu
    obtain ⟨q,hq,hqslots⟩ := hu
    have hh := hqslots p hp
    change s.cfg ⟨g,p⟩ = .interior (if p = q then u else .empty) at hh
    rw [hcfg] at hh
    have htu : t = u := by
      by_cases heq : p = q
      · rw [if_pos heq] at hh; exact Agent.interior.inj hh
      · rw [if_neg heq] at hh; exact False.elim (ht (Agent.interior.inj hh))
    subst u
    exact ⟨p',hp',hpost⟩

private theorem send_current_idle (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hw : (s.cfg (rootV R g)).cwPort = some .toSend) :
    (s.epoch g).cur = .idle := by
  have hh := owner_port_exact R s hs g
  rw [hw] at hh
  cases he : (s.epoch g).cur with
  | idle => rfl
  | outbound q c => simp only [he,epochCw] at hh; cases hh
  | returning q c d => simp only [he,epochCw] at hh; cases hh
  | delivered q c d => cases c <;> cases d <;> simp [he,epochCw,resCw,res,Verdict.cw] at hh

/-- An idle current transaction exposes precisely the completed strict
prefix, including the synthetic prefix after both archives were cleared. -/
theorem idle_prefix (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hi : (s.epoch g).cur = .idle) :
    (s.k (next R g) = s.k g ∨ s.k (next R g)+1 = s.k g) ∧
    ∀ r, ComparedAt ((view R s).epoch g) r ↔ r < s.k g := by
  have hp := hs.previous g
  have hshape := hs.coherent.shape g
  cases he : (s.epoch g).prev with
  | outbound q c => simp only [PrevShape,he] at hp
  | returning q c d => simp only [PrevShape,he] at hp
  | delivered q c d =>
    simp only [PrevShape,he] at hp
    constructor
    · omega
    · intro r
      simp only [view,prefixView,combinedView,hi,he,ComparedAt]
      omega
  | idle =>
    by_cases hz : s.k g = 0
    · simp only [prefixView,combinedView,hi,he,hz,if_true,EpochShape] at hshape
      constructor
      · exact Or.inl (hshape.2.1.trans hz.symm)
      · intro r; simp [view,prefixView,combinedView,hi,he,hz,ComparedAt]
    · simp only [prefixView,combinedView,hi,he,hz,if_false,EpochShape] at hshape
      have hk : (view R s).k (next R g) = s.k (next R g) := rfl
      have hb : s.k (next R g) = s.k g-1 ∨ s.k (next R g) = s.k g-1+1 := hshape.2.1
      constructor
      · omega
      · intro r
        simp only [view,prefixView,combinedView,hi,he,hz,if_false,ComparedAt]
        omega

/-- L1 closes the selected clauses for arbitrary positive gap length. -/
theorem C1_C3_step_L1 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hl : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g)) :
    EpochShape R (view R (ghostStep2 R s (rootV R g))) g ∧
      C3At R (ghostStep2 R s (rootV R g)) g := by
  have hf := prelaunch_no_joins R s hs g c ccw hl hh
  have hcur := prelaunch_current_epoch R s hs g c ccw hl hh
  have hrow := prelaunch_row R s hs g c ccw hl hh
  have hslot := toSend_empty_gap2 R s hs g (by rw [hl]; rfl)
    ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  have hn : compares (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = false := by
    rw [rn_root_first R g hh,hl]
    change s.cfg ⟨g,⟨1,hh⟩⟩ = .interior .empty at hslot
    rw [hslot]; rfl
  have hi := send_current_idle R s hs g (by rw [hl]; rfl)
  obtain ⟨hb,hprefix⟩ := idle_prefix R s hs g hi
  have hprev : ((ghostStep2 R s (rootV R g)).epoch g).prev = (s.epoch g).prev := by
    change (epochStep2 R s (rootV R g) g).prev = _
    simp [epochStep2,hf,hn]
  have hk : ∀ i, (ghostStep2 R s (rootV R g)).k i = s.k i := by
    intro i; simp [ghostStep2_k,hf]
  have hv : (view R (ghostStep2 R s (rootV R g))).epoch g =
      .outbound (s.k g) (resolveInit c) := by simp [view,prefixView,combinedView,hcur]
  have hw : ((ghostStep2 R s (rootV R g)).cfg (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort := by
    rw [root_cfg_no_join R s (rootV R g) (next R g) (hf _)]
    exact raw_ccw_no_compare R s hs (rootV R g) g hn
  have hpay := raw_choice_recorded R s hs (rootV R g) g (by simp [incident]) (resolveInit c)
    (by rw [rawAt,if_pos rfl,hrow]; rfl)
  constructor
  · rw [EpochShape,hv]
    exact ⟨hk g,by simpa only [view,prefixView,combinedView,hk] using hb,hpay,
      prelaunch_token R s hs g c ccw hl hh⟩
  · unfold C3At
    rw [hv,hcur,hprev,hk,hw]
    refine ⟨(hs.coherent.incoming g).trans (hprefix _),?_,?_⟩
    · intro h
      obtain ⟨c,d,hc,hd,hv⟩ := hs.coherent.incomingValue g ((hprefix _).mpr h)
      exact ⟨c,d,history2_monotone R s (rootV R g) _ _ _ hc,
        history2_monotone R s (rootV R g) _ _ _ hd,hv⟩
    · simpa only [hi,CurrentResult] using hs.incoming g

/-- A physical reply identifies its retained declaration payload and
the unique live return position. -/
theorem reply_epoch (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin (R.len g)) (ha : 0 < a.val) (d : Choice)
    (hc : s.cfg ⟨g,a⟩ = .interior (.reply d)) :
    ∃ c, (s.epoch g).cur = .returning (s.k g) c d ∧
      ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = a then .reply d else .empty) := by
  have ht := hs.current g
  have hshape := current_token_shape R s hs g
  cases he : (s.epoch g).cur with
  | idle =>
    rw [he] at hshape
    have hx := hshape a ha
    change s.cfg ⟨g,a⟩ = .interior .empty at hx
    rw [hc] at hx; cases hx
  | delivered q x y =>
    rw [he] at hshape
    have hx := hshape a ha
    change s.cfg ⟨g,a⟩ = .interior .empty at hx
    rw [hc] at hx; cases hx
  | outbound q x =>
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg ⟨g,a⟩ = _ at hx
    rw [hc] at hx
    split at hx <;> cases hx
  | returning q x y =>
    have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg ⟨g,a⟩ = _ at hx
    rw [hc] at hx
    by_cases hap : a = p
    · rw [if_pos hap] at hx
      cases hx
      exact ⟨x,by rw [hq],by simpa only [curView,← hap] using hslots⟩
    · rw [if_neg hap] at hx; cases hx

private theorem interior_input_positive (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (t : Slot) (he : s.cfg e = .interior t) : 0 < e.2.val := by
  by_cases hz : e.2.val = 0
  · have hv : e = rootV R e.1 := vtx_eq R _ _ rfl hz
    obtain ⟨c,cw,ccw,hc⟩ := hs.coherent.roots e.1
    change s.cfg (rootV R e.1) = .root c cw ccw at hc
    rw [hv,hc] at he; cases he
  · omega

private theorem interior_receiver_next (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (t : Slot) (he : s.cfg (rn R e) = .interior t) : e.2.val+1 < R.len e.1 := by
  have hp := interior_input_positive R s hs (rn R e) t he
  by_cases hn : e.2.val+1 < R.len e.1
  · exact hn
  · rw [rn_of_last R e hn] at hp
    change 0 < 0 at hp
    omega

/-- All literal selected-edge rows, including L1, F1, B1 and the
resolution-only rows omitted from the earlier selected-gap lemmas. -/
theorem C1_C3_step_selected (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) : EpochShape R (view R (ghostStep2 R s e)) e.1 ∧ C3At R (ghostStep2 R s e) e.1 := by
  cases hl : s.cfg e with
  | interior a =>
    have ha := interior_input_positive R s hs e a hl
    cases hr : s.cfg (rn R e) with
    | interior b =>
      have hn := interior_receiver_next R s hs e b hr
      let j : Fin (R.len e.1) := ⟨e.2.val+1,hn⟩
      have hj : 0 < j.val := by change 0 < e.2.val+1; omega
      have hrn : rn R e = ⟨e.1,j⟩ := rn_of_lt R e hn
      have hne : e.2 ≠ j := by intro h; have := congrArg Fin.val h; change e.2.val = e.2.val+1 at this; omega
      cases a <;> cases b
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      · obtain ⟨c,_,hslots⟩ := reply_epoch R s hs e.1 j hj _ (hrn ▸ hr)
        exact C1_C3_step_move R s hs e e.1 e.2 j j e.2 _ ha hj hj ha
          (by intro h; cases h) rfl hrn (Or.inr rfl) (Or.inl rfl) hslots
          (by rw [hl,hr]; simp [row,Ne.symm hne])
      · obtain ⟨_,hslots⟩ := declaration_epoch R s hs e.1 e.2 ha _ hl
        exact C1_C3_step_move R s hs e e.1 e.2 j e.2 j _ ha hj ha hj
          (by intro h; cases h) rfl hrn (Or.inl rfl) (Or.inr rfl) hslots
          (by rw [hl,hr]; simp [row,hne])
    | root d cw ccw =>
      obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d cw ccw hr
      cases a <;> cases ccw
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      exact C1_C3_step_comparison R s hs e.1 e.2 ha hlast _ d cw hl (hrn ▸ hr)
  | root c cw ccw =>
    have hz := root_input_zero R s hs e c cw ccw hl
    have he : e = rootV R e.1 := vtx_eq R _ _ rfl hz
    cases hr : s.cfg (rn R e) with
    | interior t =>
      have hn := interior_receiver_next R s hs e t hr
      have hh : 1 < (R.len e.1) := by omega
      cases cw <;> cases t
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      · have h := C1_C3_step_L1 R s hs e.1 c ccw (he ▸ hl) hh
        simpa only [← he] using h
      all_goals
        have hrn : rn R e = ⟨e.1,⟨1,hh⟩⟩ := by
          rw [rn_of_lt R e hn]
          exact vtx_eq R _ _ rfl (by dsimp only; omega)
        obtain ⟨x,hcur,hslots⟩ := reply_epoch R s hs e.1 ⟨1,hh⟩ (Nat.zero_lt_succ 0) _ (hrn ▸ hr)
        have h := C1_C3_step_V1 R s hs e.1 (s.k e.1) x _ hh hcur (by
          intro a ha
          have hiff : a = (⟨1,hh⟩ : Fin (R.len e.1)) ↔ a.val = 1 := ⟨congrArg Fin.val,fun h => Fin.ext h⟩
          simpa only [hiff] using hslots a ha)
        simpa only [← he] using h
    | root d dw dd =>
      obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d dw dd hr
      have hh : (R.len e.1) = 1 := by omega
      cases cw <;> cases dd
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      have h := C1_C3_step_P1 R s hs e.1 hh c d ccw dw (he ▸ hl) (hrn ▸ hr)
      simpa only [← he] using h

/-- The scheduled gap and every unscheduled gap satisfy post-step shape. -/
theorem C1_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C1 R (ghostStep2 R s e) := by
  intro g
  by_cases hg : g = e.1
  · subst g; exact (C1_C3_step_selected R s hs e).1
  · exact C1_step_adjacent R s hs e g hg

/-- Both prefix and two-epoch right-port agreements hold after every edge. -/
theorem C3_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C3 R (ghostStep2 R s e) := by
  apply (C3_iff_forall R _).mpr
  intro g
  by_cases hg : g = e.1
  · subst g; exact (C1_C3_step_selected R s hs e).2
  · exact C3_step_adjacent R s hs e g hg

/-- All three actual C7 history clauses are preserved unconditionally. -/
theorem C7_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C7 R (ghostStep2 R s e) := C7_step_of_C1 R s hs e (C1_step R s hs e)


/-- All eight clauses close for every literal physical edge. -/
theorem lineage2_step (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    Lineage2 R (ghostStep2 R s e) :=
  (lineage2_iff_clauses R _).mpr ⟨C0_step R s hs e,C1_step R s hs e,C2_step R s hs e,
    C3_step R s hs e,C4_step R s hs e,C5_step R s hs e,C6_step R s hs e,C7_step R s hs e⟩


/-! Denial-only domain, stopped at any historical candidate. -/

theorem candidate_round_le_maxGen (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (hc : VirtualCandidate2 R q s) : q ≤ maxGen R s := by
  obtain ⟨g,hg,_⟩ := hc
  have hq : q ≤ s.k g := by
    by_cases hh : s.k g < q
    · have hf := hs.coherent.histFuture g q hh
      change s.hist g q = none at hf
      simp [word2,hf,choiceToWord] at hg
    · omega
  exact Nat.le_trans hq (ShortGapLineage2Closure.le_generationMax s.k g)

theorem denial2_or_predecessor_candidate (R : VFrame) (r : Nat) (s : GhostRing2 R) :
    DenialOnly2 R r s ∨ VirtualCandidate2 R (r-1) s := by
  classical
  cases r with
  | zero => exact Or.inl trivial
  | succ q =>
    by_cases hv : VirtualCandidate2 R q s
    · exact Or.inr hv
    · left
      intro g c d _ hc hd
      cases c <;> cases d <;> first | rfl |
        exact False.elim (hv ⟨g,by simp [word2,hc,choiceToWord],by simp [word2,hd,choiceToWord]⟩)

def Dom (R : VFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  Lineage2 R s ∧ CohortEntered2 R r s ∧ ¬ VirtualSuccess R r s

theorem dom_denial (R : VFrame) (r : Nat) (s : GhostRing2 R) (hs : Dom R r s) : DenialOnly2 R r s := by
  rcases denial2_or_predecessor_candidate R r s with hd | hc
  · exact hd
  · exact False.elim (hs.2.2 ⟨r-1,candidate_round_le_maxGen R s hs.1 _ hc,hc⟩)

theorem zero_debt_step_on_dom (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hz : latentDebt2 R r s = 0) (e : Vtx R) :
    latentDebt2 R r (ghostStep2 R s e) = 0 :=
  latentDebt2_zero_step R r s hs.1 (dom_denial R r s hs) hz e
theorem prelaunch_token_debt_drop (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < (R.len g))
    (hq : s.k g = q) (hi : (s.epoch g).cur = .idle) :
    (tokens2 R (q+1) (ghostStep2 R s (rootV R g)) g).hops + 1 =
      (tokens2 R (q+1) s g).hops := by
  have hf := prelaunch_no_joins R s hs g c ccw hc hh g
  have hk0 : (curView R s).k g = q := hq
  have hk1 : (curView R (ghostStep2 R s (rootV R g))).k g = q := by
    change (ghostStep2 R s (rootV R g)).k g = q
    simp [ghostStep2_k,hf,hq]
  have he0 : (curView R s).epoch g = .idle := hi
  have he1 : (curView R (ghostStep2 R s (rootV R g))).epoch g = .outbound q (resolveInit c) := by
    change ((ghostStep2 R s (rootV R g)).epoch g).cur = _
    rw [prelaunch_current_epoch R s hs g c ccw hc hh,hq]
  have hp := prelaunch_tokenPos R s hs g c ccw hc hh
  simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hp,ofPhase,hh,LitGapState.hops]
  omega

private theorem sum_one_drop {m : Nat} (f g : Fin m → Nat) (i : Fin m)
    (hi : f i + 1 = g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (List.ofFn f).sum + 1 = (List.ofFn g).sum := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hz : i = 0
    · subst i
      have ht := ofFn_sum_eq (fun j : Fin m => f j.succ) (fun j => g j.succ)
        (fun j => ho j.succ (by intro he; have hv := congrArg Fin.val he; simp at hv))
      omega
    · have hp : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hz (Fin.ext h)
        omega
      let j : Fin m := ⟨i.val-1,by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin m => f j.succ) (fun j => g j.succ) j
        (by simpa only [hj] using hi) (by
          intro k hk
          apply ho k.succ
          intro he
          rw [← hj] at he
          exact hk (Fin.succ_inj.mp he))
      have h0 := ho 0 (Ne.symm hz)
      omega

/-- Complete arbitrary-h prelaunch progress, including the total debt:
all other tokens stutter because L1 fires no JOIN at any root. -/
theorem prelaunch_lowers_latentDebt2 (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (hq : s.k g = q)
    (hi : (s.epoch g).cur = .idle) (hh : 1 < (R.len g)) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hroot
  have hc := hs.idleSend g hi
  rw [hroot] at hc
  have hcw : cw = .toSend := Option.some.inj hc
  subst cw
  apply sum_one_drop _ _ g
  · exact prelaunch_token_debt_drop R q s hs g c ccw hroot hh hq hi
  · intro j hj
    rw [other_gap_token_eq R (q+1) s (rootV R g) j hj
      (prelaunch_no_joins R s hs g c ccw hroot hh j)]

/-! Shared-root JOIN does not charge another gap's token. -/

theorem token_eq_of_delivered_join (R : VFrame) (r : Nat) (s t : GhostRing2 R)
    (g : Fin R.m) (c d : Choice) (hc : (s.epoch g).cur = .delivered (s.k g) c d)
    (hk : t.k g = s.k g + 1) (he : (t.epoch g).cur = .idle) :
    tokens2 R r t g = tokens2 R r s g := by
  cases r with
  | zero => rfl
  | succ q =>
    have he0 : (curView R s).epoch g = .delivered ((curView R s).k g) c d := hc
    have he1 : (curView R t).epoch g = .idle := he
    have hk' : (curView R t).k g = (curView R s).k g + 1 := hk
    by_cases hp : q < (curView R s).k g
    · have hp' : q < (curView R t).k g := by rw [hk']; omega
      simp only [tokens2,tokensOf'_past R q _ g hp,tokensOf'_past R q _ g hp']
    · by_cases hq : q = (curView R s).k g
      · have hp' : q < (curView R t).k g := by rw [hk',hq]; omega
        simp [tokens2,tokensOf',cohortToken,he0,hk',hq]
      · have hfuture : (curView R s).k g < q := by omega
        have hnotpast : ¬ q < (curView R t).k g := by rw [hk']; omega
        simp only [tokens2,tokensOf',cohortToken,if_neg hp,if_pos hfuture,
          if_neg hnotpast,he1,ite_self]

/-- Under lineage, every unscheduled gap's token stutters exactly, even
when its owner JOINs as the right endpoint of the scheduled interaction. -/
theorem other_gap_token_eq_lineage (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    tokens2 R r (ghostStep2 R s e) g = tokens2 R r s g := by
  cases hf : fires R (physical2 R s) e g with
  | false => exact other_gap_token_eq R r s e g hg hf
  | true =>
    obtain ⟨c,d,hc⟩ := other_join_current_delivered R s hs e g hg hf
    apply token_eq_of_delivered_join R r s (ghostStep2 R s e) g c d hc
    · simp [ghostStep2_k,hf]
    · change (epochStep2 R s e g).cur = .idle
      simp [epochStep2_cur,hf]

theorem delivered_selected_token_eq (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) (q : Nat) (c d : Choice)
    (he : (s.epoch e.1).cur = .delivered q c d) :
    tokens2 R r (ghostStep2 R s e) e.1 = tokens2 R r s e.1 := by
  have hq := hs.current e.1
  simp only [he,CurrentTag] at hq
  cases hf : fires R (physical2 R s) e e.1 with
  | true =>
    apply token_eq_of_delivered_join R r s (ghostStep2 R s e) e.1 c d
      (by rw [he,hq])
    · simp [ghostStep2_k,hf]
    · change (epochStep2 R s e e.1).cur = .idle
      simp [epochStep2_cur,hf]
  | false =>
    have hk : (curView R (ghostStep2 R s e)).k e.1 = (curView R s).k e.1 := by
      change (ghostStep2 R s e).k e.1 = s.k e.1
      simp [ghostStep2_k,hf]
    have he0 : (curView R s).epoch e.1 = .delivered q c d := he
    have he1 : (curView R (ghostStep2 R s e)).epoch e.1 = .delivered q c d := by
      change (epochStep2 R s e e.1).cur = _
      simp [epochStep2_cur,hf,delivered_raw_epoch R s hs e q c d he]
    cases r with
    | zero => rfl
    | succ t => simp only [tokens2,tokensOf',cohortToken,hk,he0,he1]

/-- Once the receiver has entered q, an owner's preceding record cannot
account for a still-held receipt when that owner is itself at q. -/
theorem previous_not_current_at_cut (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q) :
    ¬ PreviousResult (s.epoch g).prev (s.k (next R g)) := by
  have hp := hs.1.previous g
  have hcut : q ≤ s.k (next R g) := hs.2.1 (next R g)
  intro hh
  cases he : (s.epoch g).prev
  all_goals simp only [he,PreviousResult] at hh
  simp only [PrevShape,he] at hp
  omega

/-- The entry cut supplies the receiver-free guard needed by direct P1
and by the last declaration comparison. This is derived, not assumed. -/
theorem right_free_at_cut (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q)
    (hc : ¬ CurrentResult (s.epoch g).cur (s.k (next R g))) :
    (s.cfg (rootV R (next R g))).ccwPort = some .free := by
  have hn : ¬ CcwHeld (s.cfg (rootV R (next R g))).ccwPort := by
    intro hh
    rcases (hs.1.incoming g).mp hh with hh | hh
    · exact hc hh
    · exact previous_not_current_at_cut R q s hs g hk hh
  obtain ⟨c,cw,ccw,hroot⟩ := hs.1.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root c cw ccw at hroot
  rw [hroot] at hn ⊢
  cases ccw with
  | free => rfl
  | heldDenial => exact False.elim (hn trivial)
  | heldCandidate => exact False.elim (hn trivial)

/-- Direct P1 discharges the one-hop latent token, regardless of whether
its comparison produces a denial or immediately uses the success port. -/
theorem direct_prelaunch_drop (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q)
    (hi : (s.epoch g).cur = .idle) (hh : (R.len g) = 1) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  have hfree := right_free_at_cut R q s hs g hk (by rw [hi]; exact id)
  obtain ⟨c,cw,ccw,hroot⟩ := hs.1.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hroot
  have hsend := hs.1.idleSend g hi
  rw [hroot] at hsend
  have hcw : cw = .toSend := Option.some.inj hsend
  subst cw
  obtain ⟨d,dw,dd,hrecv⟩ := hs.1.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root d dw dd at hrecv
  rw [hrecv] at hfree
  have hdd : dd = .free := Option.some.inj hfree
  subst dd
  have hrn : rn R (rootV R g) = rootV R (next R g) :=
    rn_of_last R (rootV R g) (by change ¬ 1 < (R.len g); omega)
  have hraw : rawEpochs R (curView R s) (rootV R g) g =
      .delivered q (resolveInit c) (resolveResp d) := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
    rw [hrn,hroot,hrecv,hk]
    rfl
  have hk0 : (curView R s).k g = q := hk
  have he0 : (curView R s).epoch g = .idle := hi
  have hbefore : (tokens2 R (q+1) s g).hops = 1 := by
    simp [tokens2,tokensOf',cohortToken,hk0,he0,LitGapState.hops,hh]
  have hafter : (tokens2 R (q+1) (ghostStep2 R s (rootV R g)) g).hops = 0 := by
    cases hf : fires R (physical2 R s) (rootV R g) g with
    | true =>
      have hp : q < (curView R (ghostStep2 R s (rootV R g))).k g := by
        change q < (ghostStep2 R s (rootV R g)).k g
        simp [ghostStep2_k,hf,hk]
      exact congrArg LitGapState.hops (tokensOf'_past R q _ g hp)
    | false =>
      have hk1 : (curView R (ghostStep2 R s (rootV R g))).k g = q := by
        change (ghostStep2 R s (rootV R g)).k g = q
        simp [ghostStep2_k,hf,hk]
      have he1 : (curView R (ghostStep2 R s (rootV R g))).epoch g =
          .delivered q (resolveInit c) (resolveResp d) := by
        change (epochStep2 R s (rootV R g) g).cur = _
        simp [epochStep2_cur,hf,hraw]
      simp [tokens2,tokensOf',cohortToken,hk1,he1,LitGapState.hops]
  apply sum_one_drop _ _ g
  · omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs.1 (rootV R g) j hj]

/-- The full latent-prelaunch branch for every h>0, with its actual
advancing physical edge and exactly one unit of total debt removed. -/
theorem prelaunch_drop_on_dom (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q)
    (hi : (s.epoch g).cur = .idle) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  by_cases hh : (R.len g) = 1
  · exact direct_prelaunch_drop R q s hs g hk hi hh
  · exact prelaunch_lowers_latentDebt2 R q s hs.1 g hk hi (by have := (R.len_pos g); omega)

/-! Interior transport. -/

theorem forwarding_lowers_latentDebt2 (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c : Choice) (p : Fin (R.len g))
    (hp : 0 < p.val) (hpnext : p.val+1 < (R.len g)) (hk : s.k g = q)
    (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty)) :
    latentDebt2 R (q+1) (ghostStep2 R s ⟨g,p⟩) + 1 = latentDebt2 R (q+1) s := by
  let p' : Fin (R.len g) := ⟨p.val+1,hpnext⟩
  have hp' : 0 < p'.val := by change 0 < p.val+1; omega
  have hne : p ≠ p' := by intro h; have hv := congrArg Fin.val h; change p.val = p.val+1 at hv; omega
  have hrn : rn R ⟨g,p⟩ = ⟨g,p'⟩ := rn_of_lt R ⟨g,p⟩ hpnext
  have hl : s.cfg ⟨g,p⟩ = .interior (.decl c) := by simpa using hslots p hp
  have hr : s.cfg (rn R ⟨g,p⟩) = .interior .empty := by
    rw [hrn,hslots p' hp',if_neg (Ne.symm hne)]
  have hrow : row (s.cfg ⟨g,p⟩) (s.cfg (rn R ⟨g,p⟩)) =
      (.interior .empty,.interior (.decl c)) := by rw [hl,hr]; rfl
  have hpost := token_move_pair R s ⟨g,p⟩ g p p' p p' (.decl c) (.decl c)
    rfl hrn (Or.inl rfl) (Or.inr rfl) hslots (by simpa [hne] using hrow)
  have hpos0 := tokenPos2_of_unique R s g p hp (.decl c) (by intro h; cases h) hslots
  have hpos1 := tokenPos2_of_unique R (ghostStep2 R s ⟨g,p⟩) g p' hp'
    (.decl c) (by intro h; cases h) hpost
  have hf := no_owner_join_at_positive R s ⟨g,p⟩ hp
  have hk0 : (curView R s).k g = q := hk
  have hk1 : (curView R (ghostStep2 R s ⟨g,p⟩)).k g = q := by
    change (ghostStep2 R s ⟨g,p⟩).k g = q
    simp [ghostStep2_k,hf,hk]
  have he0 : (curView R s).epoch g = .outbound q c := he
  have he1 : (curView R (ghostStep2 R s ⟨g,p⟩)).epoch g = .outbound q c := by
    change (epochStep2 R s ⟨g,p⟩ g).cur = _
    rw [epochStep2_cur,hf]
    simp only [Bool.false_eq_true,if_false]
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg ⟨g,p⟩) (s.cfg (rn R ⟨g,p⟩)) = _
    rw [he,hl,hr]
    rfl
  apply sum_one_drop _ _ g
  · simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hpos0,hpos1,
      ofPhase,p.isLt,p'.isLt,LitGapState.hops]
    change 2*(R.len g)-1-(p.val+1)+1 = 2*(R.len g)-1-p.val
    omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs ⟨g,p⟩ j hj]

/-- Interior B1 moves a reply one slot toward its owner and lowers the
total debt exactly once. -/
theorem backward_lowers_latentDebt2 (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c d : Choice) (p : Fin (R.len g))
    (hp : 1 < p.val) (hk : s.k g = q) (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty)) :
    let p' : Fin (R.len g) := ⟨p.val-1,by have := p.isLt; omega⟩
    latentDebt2 R (q+1) (ghostStep2 R s ⟨g,p'⟩) + 1 = latentDebt2 R (q+1) s := by
  dsimp only
  let p' : Fin (R.len g) := ⟨p.val-1,by have := p.isLt; omega⟩
  change latentDebt2 R (q+1) (ghostStep2 R s ⟨g,p'⟩) + 1 = latentDebt2 R (q+1) s
  have hp' : 0 < p'.val := by change 0 < p.val-1; omega
  have hnext : p'.val+1 < (R.len g) := by have := p.isLt; change p.val-1+1 < (R.len g); omega
  have hne : p' ≠ p := by intro h; have hv := congrArg Fin.val h; change p.val-1 = p.val at hv; omega
  have hrn : rn R ⟨g,p'⟩ = ⟨g,p⟩ := by
    rw [rn_of_lt R ⟨g,p'⟩ hnext]
    apply vtx_eq R
    · rfl
    · change p.val-1+1 = p.val
      omega
  have hl : s.cfg ⟨g,p'⟩ = .interior .empty := by rw [hslots p' hp',if_neg hne]
  have hr : s.cfg (rn R ⟨g,p'⟩) = .interior (.reply d) := by
    rw [hrn,hslots p (by omega),if_pos rfl]
  have hrow : row (s.cfg ⟨g,p'⟩) (s.cfg (rn R ⟨g,p'⟩)) =
      (.interior (.reply d),.interior .empty) := by rw [hl,hr]; rfl
  have hpost := token_move_pair R s ⟨g,p'⟩ g p' p p p' (.reply d) (.reply d)
    rfl hrn (Or.inr rfl) (Or.inl rfl) hslots (by simpa [Ne.symm hne] using hrow)
  have hpos0 := tokenPos2_of_unique R s g p (by omega) (.reply d) (by intro h; cases h) hslots
  have hpos1 := tokenPos2_of_unique R (ghostStep2 R s ⟨g,p'⟩) g p' hp'
    (.reply d) (by intro h; cases h) hpost
  have hf := no_owner_join_at_positive R s ⟨g,p'⟩ hp'
  have hk0 : (curView R s).k g = q := hk
  have hk1 : (curView R (ghostStep2 R s ⟨g,p'⟩)).k g = q := by
    change (ghostStep2 R s ⟨g,p'⟩).k g = q
    simp [ghostStep2_k,hf,hk]
  have he0 : (curView R s).epoch g = .returning q c d := he
  have he1 : (curView R (ghostStep2 R s ⟨g,p'⟩)).epoch g = .returning q c d := by
    change (epochStep2 R s ⟨g,p'⟩ g).cur = _
    rw [epochStep2_cur,hf]
    simp only [Bool.false_eq_true,if_false]
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg ⟨g,p'⟩) (s.cfg (rn R ⟨g,p'⟩)) = _
    rw [he,hl,hr]
    rfl
  have hb0 : 1 ≤ p.val ∧ p.val ≤ (R.len g)-1 := by have := p.isLt; omega
  have hb1 : 1 ≤ p'.val ∧ p'.val ≤ (R.len g)-1 := by have := p'.isLt; omega
  apply sum_one_drop _ _ g
  · simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hpos0,hpos1,
      ofPhase,hb0.1,hb0.2,hb1.1,hb1.2,LitGapState.hops]
    change p.val-1+1 = p.val
    omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs ⟨g,p'⟩ j hj]

theorem comparison_lowers_latentDebt2 (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (c : Choice) (p : Fin (R.len g))
    (hp : 0 < p.val) (hlast : p.val+1 = (R.len g)) (hk : s.k g = q)
    (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty)) :
    latentDebt2 R (q+1) (ghostStep2 R s ⟨g,p⟩) + 1 = latentDebt2 R (q+1) s := by
  have hfree := right_free_at_cut R q s hs g hk (by rw [he]; exact id)
  obtain ⟨d,dw,dd,hrecv⟩ := hs.1.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root d dw dd at hrecv
  rw [hrecv] at hfree
  have hdd : dd = .free := Option.some.inj hfree
  subst dd
  have hrn : rn R ⟨g,p⟩ = rootV R (next R g) :=
    rn_of_last R ⟨g,p⟩ (by change ¬ p.val+1 < (R.len g); omega)
  have hl : s.cfg ⟨g,p⟩ = .interior (.decl c) := by simpa using hslots p hp
  have hr : s.cfg (rn R ⟨g,p⟩) = .root d dw .free := by rw [hrn]; exact hrecv
  have hrow : (row (s.cfg ⟨g,p⟩) (s.cfg (rn R ⟨g,p⟩))).1 = .interior (.reply (resolveResp d)) := by
    rw [hl,hr]; rfl
  have hpost := boundary_token_replace R s g p hp hlast (.decl c) (.reply (resolveResp d)) hslots hrow
  have hpos0 := tokenPos2_of_unique R s g p hp (.decl c) (by intro h; cases h) hslots
  have hpos1 := tokenPos2_of_unique R (ghostStep2 R s ⟨g,p⟩) g p hp
    (.reply (resolveResp d)) (by intro h; cases h) hpost
  have hf := no_owner_join_at_positive R s ⟨g,p⟩ hp
  have hk0 : (curView R s).k g = q := hk
  have hk1 : (curView R (ghostStep2 R s ⟨g,p⟩)).k g = q := by
    change (ghostStep2 R s ⟨g,p⟩).k g = q
    simp [ghostStep2_k,hf,hk]
  have he0 : (curView R s).epoch g = .outbound q c := he
  have he1 : (curView R (ghostStep2 R s ⟨g,p⟩)).epoch g = .returning q c (resolveResp d) := by
    change (epochStep2 R s ⟨g,p⟩ g).cur = _
    rw [epochStep2_cur,hf]
    simp only [Bool.false_eq_true,if_false]
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg ⟨g,p⟩) (s.cfg (rn R ⟨g,p⟩)) = _
    rw [he,hl,hr]
    rfl
  have hb : 1 ≤ p.val ∧ p.val ≤ (R.len g)-1 := by omega
  apply sum_one_drop _ _ g
  · simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hpos0,hpos1,
      ofPhase,p.isLt,hb.1,hb.2,LitGapState.hops]
    omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs.1 ⟨g,p⟩ j hj]

/-- A delivered raw current result discharges its accounting token both
with and without the owner's post-row JOIN. -/
theorem token_zero_of_raw_delivered (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m) (c d : Choice) (hk : s.k g = q)
    (hr : rawEpochs R (curView R s) e g = .delivered q c d) :
    (tokens2 R (q+1) (ghostStep2 R s e) g).hops = 0 := by
  cases hf : fires R (physical2 R s) e g with
  | true =>
    have hp : q < (curView R (ghostStep2 R s e)).k g := by
      change q < (ghostStep2 R s e).k g
      simp [ghostStep2_k,hf,hk]
    exact congrArg LitGapState.hops (tokensOf'_past R q _ g hp)
  | false =>
    have hk1 : (curView R (ghostStep2 R s e)).k g = q := by
      change (ghostStep2 R s e).k g = q
      simp [ghostStep2_k,hf,hk]
    have he1 : (curView R (ghostStep2 R s e)).epoch g = .delivered q c d := by
      change (epochStep2 R s e g).cur = _
      simp [epochStep2_cur,hf,hr]
    simp [tokens2,tokensOf',cohortToken,hk1,he1,LitGapState.hops]

/-- V1 consumes a reply in slot 1. Its selected token disappears whether
the owner retains its receipt or JOINs immediately; all other tokens stutter. -/
theorem delivery_lowers_latentDebt2 (R : VFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c d : Choice) (p : Fin (R.len g))
    (hp : p.val = 1) (hk : s.k g = q) (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty)) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  have hh : 1 < (R.len g) := by have := p.isLt; omega
  have hp0 : 0 < p.val := by omega
  obtain ⟨x,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root x cw ccw at hroot
  have hw := (hs.waiting g).mpr (by rw [he]; trivial)
  rw [hroot] at hw
  have hcw : cw = .waiting := Option.some.inj hw
  subst cw
  have hrn : rn R (rootV R g) = ⟨g,p⟩ := by
    rw [rn_root_first R g hh]
    exact congrArg (fun a => (⟨g,a⟩ : Vtx R)) (Fin.ext hp.symm)
  have hright : s.cfg (rn R (rootV R g)) = .interior (.reply d) := by
    rw [hrn,hslots p hp0,if_pos rfl]
  have hraw : rawEpochs R (curView R s) (rootV R g) g = .delivered q c d := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
    rw [he,hroot,hright]
    rfl
  have hafter := token_zero_of_raw_delivered R q s (rootV R g) g c d hk hraw
  have hpos := tokenPos2_of_unique R s g p hp0 (.reply d) (by intro h; cases h) hslots
  have hk0 : (curView R s).k g = q := hk
  have he0 : (curView R s).epoch g = .returning q c d := he
  have hbefore : (tokens2 R (q+1) s g).hops = 1 := by
    have hbound : 1 ≤ (R.len g)-1 := by omega
    simp [tokens2,tokensOf',cohortToken,hk0,he0,hpos,ofPhase,hp,hbound,LitGapState.hops]
  apply sum_one_drop _ _ g
  · omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs (rootV R g) j hj]

/-- Positive debt exposes a genuine useful physical edge. The proof
selects a positive gap, uses the cut to identify its owner generation,
then uses slot 0, the declaration's position, or the reply's predecessor
position according to cur. Each branch proves exactly one total hop. -/
theorem advancing_edge_lowers_latentDebt2 (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hp : 0 < latentDebt2 R r s) :
    ∃ e : Vtx R, latentDebt2 R r (ghostStep2 R s e) + 1 = latentDebt2 R r s := by
  classical
  have hex : ∃ g, 0 < (tokens2 R r s g).hops := by
    apply Classical.byContradiction
    intro hn
    have hz : ∀ g, (tokens2 R r s g).hops = 0 := by
      intro g
      have hnot : ¬ 0 < (tokens2 R r s g).hops := fun h => hn ⟨g,h⟩
      omega
    have heq := ofFn_sum_eq (fun g => (tokens2 R r s g).hops) (fun _ => 0) hz
    rw [ofFn_sum_const] at heq
    change latentDebt2 R r s = R.m*0 at heq
    omega
  obtain ⟨g,hg⟩ := hex
  cases r with
  | zero => change 0 < 0 at hg; omega
  | succ q =>
    have hk : s.k g = q := by
      have hc : q ≤ s.k g := hs.2.1 g
      by_cases hgt : q < s.k g
      · have ht := tokensOf'_past R q (curView R s) g hgt
        change 0 < (tokensOf' R (q+1) (curView R s) g).hops at hg
        rw [ht] at hg
        change 0 < 0 at hg
        omega
      · omega
    have ht := hs.1.current g
    have hshape := current_token_shape R s hs.1 g
    cases he : (s.epoch g).cur with
    | idle => exact ⟨rootV R g,prelaunch_drop_on_dom R q s hs g hk he⟩
    | outbound t c =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp0,hslots⟩ := hshape
      change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty) at hslots
      by_cases hnext : p.val+1 < (R.len g)
      · exact ⟨⟨g,p⟩,forwarding_lowers_latentDebt2 R q s hs.1 g c p hp0 hnext hk he hslots⟩
      · have hlast : p.val+1 = (R.len g) := by have := p.isLt; omega
        exact ⟨⟨g,p⟩,comparison_lowers_latentDebt2 R q s hs g c p hp0 hlast hk he hslots⟩
    | returning t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp0,hslots⟩ := hshape
      change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty) at hslots
      by_cases hp1 : p.val = 1
      · exact ⟨rootV R g,delivery_lowers_latentDebt2 R q s hs.1 g c d p hp1 hk he hslots⟩
      · have hp2 : 1 < p.val := by omega
        exact ⟨⟨g,⟨p.val-1,by have := p.isLt; omega⟩⟩,
          backward_lowers_latentDebt2 R q s hs.1 g c d p hp2 hk he hslots⟩
    | delivered t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      have hk0 : (curView R s).k g = q := hk
      have he0 : (curView R s).epoch g = .delivered q c d := by rw [← hq]; exact he
      simp [tokens2,tokensOf',cohortToken,hk0,he0,LitGapState.hops] at hg

/-- If the selected left endpoint and every interior right endpoint are
unchanged by the pair row, the selected token stutters. A right root may
still resolve its choice or JOIN. -/
theorem selected_token_stutters (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R)
    (hl : (row (s.cfg e) (s.cfg (rn R e))).1 = s.cfg e)
    (hr : 0 < (rn R e).2.val → (row (s.cfg e) (s.cfg (rn R e))).2 = s.cfg (rn R e))
    (he : rawEpochs R (curView R s) e e.1 = (s.epoch e.1).cur) :
    tokens2 R r (ghostStep2 R s e) e.1 = tokens2 R r s e.1 := by
  have hf : fires R (physical2 R s) e e.1 = false := by
    by_cases hp : 0 < e.2.val
    · exact no_owner_join_at_positive R s e hp
    · have hz : e = rootV R e.1 := by
        apply vtx_eq R
        · rfl
        · change e.2.val = 0; omega
      have hn := hs.coherent.normalized e.1
      change joinReady (s.cfg (rootV R e.1)) = false at hn
      have hleft : rootV R e.1 = e := hz.symm
      simp only [fires,physical2,rawAt,if_pos hleft,hl]
      rw [hz,hn]
      exact Bool.and_false _
  have hslots : ∀ a : Fin (R.len e.1), 0 < a.val →
      (ghostStep2 R s e).cfg ⟨e.1,a⟩ = s.cfg ⟨e.1,a⟩ := by
    intro a ha
    obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 a ha
    change s.cfg ⟨e.1,a⟩ = .interior t at ht
    rw [cfg_step_pair]
    by_cases h0 : ⟨e.1,a⟩ = e
    · rw [if_pos h0,hl]
      have ht' : s.cfg e = .interior t := h0 ▸ ht
      rw [ht',ht]; rfl
    · rw [if_neg h0]
      by_cases h1 : ⟨e.1,a⟩ = rn R e
      · have hp : 0 < (rn R e).2.val := by rw [← h1]; exact ha
        rw [if_pos h1,hr hp,← h1,ht]; rfl
      · rw [if_neg h1]
  have hp : tokenPos R (curView R (ghostStep2 R s e)) e.1 = tokenPos R (curView R s) e.1 := by
    have hp' : (fun a : Fin (R.len e.1) => decide (0 < a.val) &&
        match (ghostStep2 R s e).cfg ⟨e.1,a⟩ with
        | .interior (.decl _) | .interior (.reply _) => true | _ => false) =
      (fun a : Fin (R.len e.1) => decide (0 < a.val) &&
        match s.cfg ⟨e.1,a⟩ with
        | .interior (.decl _) | .interior (.reply _) => true | _ => false) := by
      funext a
      by_cases ha : 0 < a.val
      · rw [hslots a ha]
      · simp [ha]
    exact congrArg (fun p : Fin (R.len e.1) → Bool =>
      (((List.finRange (R.len e.1)).find? p).map Fin.val).getD 0) hp'
  have hk : (curView R (ghostStep2 R s e)).k e.1 = (curView R s).k e.1 := by
    change (ghostStep2 R s e).k e.1 = s.k e.1
    simp [ghostStep2_k,hf]
  have hep : (curView R (ghostStep2 R s e)).epoch e.1 = (curView R s).epoch e.1 := by
    change (epochStep2 R s e e.1).cur = (s.epoch e.1).cur
    simp [epochStep2_cur,hf,he]
  cases r with
  | zero => rfl
  | succ q =>
    change cohortToken R q (curView R (ghostStep2 R s e)) e.1 = cohortToken R q (curView R s) e.1
    simp only [cohortToken,hk,hep,hp]

/-- An outbound token stutters on every edge except the one starting
at its occupied position. -/
theorem outbound_wrong_edge (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (a p : Fin (R.len g)) (q : Nat) (c : Choice)
    (hp : 0 < p.val) (hne : a ≠ p) (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty)) :
    tokens2 R r (ghostStep2 R s ⟨g,a⟩) g = tokens2 R r s g := by
  have hrow : (row (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩))).1 = s.cfg ⟨g,a⟩ ∧
      (0 < (rn R ⟨g,a⟩).2.val →
        (row (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩))).2 = s.cfg (rn R ⟨g,a⟩)) ∧
      rowEpoch (s.k g) (s.epoch g).cur (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩)) = (s.epoch g).cur := by
    by_cases ha : 0 < a.val
    · have hl : s.cfg ⟨g,a⟩ = .interior .empty := by rw [hslots a ha,if_neg hne]
      by_cases hn : a.val+1 < (R.len g)
      · let b : Fin (R.len g) := ⟨a.val+1,hn⟩
        have hrn : rn R ⟨g,a⟩ = ⟨g,b⟩ := rn_of_lt R ⟨g,a⟩ hn
        have hb : 0 < b.val := by change 0 < a.val+1; omega
        rw [hl,hrn,hslots b hb]
        by_cases hbp : b = p <;> simp [hbp,row,rowEpoch]
      · have hrn : rn R ⟨g,a⟩ = rootV R (next R g) := rn_of_last R ⟨g,a⟩ hn
        obtain ⟨d,cw,ccw,hr⟩ := hs.coherent.roots (next R g)
        change s.cfg (rootV R (next R g)) = .root d cw ccw at hr
        rw [hl,hrn,hr]
        cases ccw <;> simp [row,rowEpoch]
    · have haz : ⟨g,a⟩ = rootV R g := by
        apply vtx_eq R
        · rfl
        · change a.val = 0; omega
      have hh : 1 < (R.len g) := by have := p.isLt; omega
      obtain ⟨d,cw,ccw,hl⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root d cw ccw at hl
      have hw := (hs.waiting g).mpr (by rw [he]; trivial)
      rw [hl] at hw
      have hc : cw = .waiting := Option.some.inj hw
      subst cw
      rw [haz,rn_root_first R g hh,hl,hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)]
      by_cases hb : (⟨1,hh⟩ : Fin (R.len g)) = p <;> simp [hb,row,rowEpoch]
  apply selected_token_stutters R r s hs ⟨g,a⟩ hrow.1 hrow.2.1
  exact (if_pos rfl).trans hrow.2.2

/-- A reply stutters unless the selected edge ends at its position. -/
theorem returning_wrong_edge (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (a p : Fin (R.len g)) (q : Nat) (c d : Choice)
    (hp : 0 < p.val) (hne : a.val+1 ≠ p.val) (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val →
      s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty)) :
    tokens2 R r (ghostStep2 R s ⟨g,a⟩) g = tokens2 R r s g := by
  have hrow : (row (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩))).1 = s.cfg ⟨g,a⟩ ∧
      (0 < (rn R ⟨g,a⟩).2.val →
        (row (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩))).2 = s.cfg (rn R ⟨g,a⟩)) ∧
      rowEpoch (s.k g) (s.epoch g).cur (s.cfg ⟨g,a⟩) (s.cfg (rn R ⟨g,a⟩)) = (s.epoch g).cur := by
    by_cases ha : 0 < a.val
    · by_cases hn : a.val+1 < (R.len g)
      · let b : Fin (R.len g) := ⟨a.val+1,hn⟩
        have hrn : rn R ⟨g,a⟩ = ⟨g,b⟩ := rn_of_lt R ⟨g,a⟩ hn
        have hb : 0 < b.val := by change 0 < a.val+1; omega
        have hbp : b ≠ p := fun h => hne (congrArg Fin.val h)
        rw [hrn,hslots a ha,hslots b hb,if_neg hbp]
        by_cases hap : a = p <;> simp [hap,row,rowEpoch]
      · have hrn : rn R ⟨g,a⟩ = rootV R (next R g) := rn_of_last R ⟨g,a⟩ hn
        obtain ⟨x,cw,ccw,hr⟩ := hs.coherent.roots (next R g)
        change s.cfg (rootV R (next R g)) = .root x cw ccw at hr
        rw [hrn,hr,hslots a ha]
        by_cases hap : a = p <;> cases ccw <;> simp [hap,row,rowEpoch]
    · have hav : a.val = 0 := by omega
      have haz : ⟨g,a⟩ = rootV R g := by
        apply vtx_eq R
        · rfl
        · exact hav
      have hh : 1 < (R.len g) := by have := p.isLt; omega
      obtain ⟨x,cw,ccw,hl⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root x cw ccw at hl
      have hw := (hs.waiting g).mpr (by rw [he]; trivial)
      rw [hl] at hw
      have hc : cw = .waiting := Option.some.inj hw
      subst cw
      have hb : (⟨1,hh⟩ : Fin (R.len g)) ≠ p := by
        intro h
        have hv := congrArg Fin.val h
        apply hne
        simpa [hav] using hv
      rw [haz,rn_root_first R g hh,hl,hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0),if_neg hb]
      simp [row,rowEpoch]
  apply selected_token_stutters R r s hs ⟨g,a⟩ hrow.1 hrow.2.1
  exact (if_pos rfl).trans hrow.2.2

/-- Every physical edge weakly decreases the accounting debt on Dom.
The only live-token changes are F1, K1/K2, B1 and V1; all other live
rows stutter. Idle and delivered epochs use their separate reductions. -/
theorem latentDebt2_step_le (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (e : Vtx R) :
    latentDebt2 R r (ghostStep2 R s e) ≤ latentDebt2 R r s := by
  rcases e with ⟨g,a⟩
  cases r with
  | zero => exact Nat.le_refl _
  | succ q =>
    by_cases hgt : q < s.k g
    · apply latentDebt2_step_le_of_scheduled_gap R (q+1) s ⟨g,a⟩ hs.2.1
      have hp : q < (curView R (ghostStep2 R s ⟨g,a⟩)).k g :=
        Nat.lt_of_lt_of_le hgt (Nat.le_add_right _ _)
      change (tokensOf' R (q+1) (curView R (ghostStep2 R s ⟨g,a⟩)) g).hops ≤
        (tokensOf' R (q+1) (curView R s) g).hops
      rw [tokensOf'_past R q _ g hp,tokensOf'_past R q _ g hgt]
      exact Nat.le_refl _
    · have hk : s.k g = q := by have hc : q ≤ s.k g := hs.2.1 g; omega
      have ht := hs.1.current g
      have hshape := current_token_shape R s hs.1 g
      cases he : (s.epoch g).cur with
      | idle =>
        apply latentDebt2_step_le_of_scheduled_gap R (q+1) s ⟨g,a⟩ hs.2.1
        exact idle_gap_token_debt_le R (q+1) s ⟨g,a⟩ g he
      | delivered t c d =>
        apply latentDebt2_step_le_of_scheduled_gap R (q+1) s ⟨g,a⟩ hs.2.1
        rw [delivered_selected_token_eq R (q+1) s hs.1 ⟨g,a⟩ t c d he]
        exact Nat.le_refl _
      | outbound t c =>
        have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
        subst t
        rw [he] at hshape
        obtain ⟨p,hp,hslots⟩ := hshape
        change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty) at hslots
        by_cases hap : a = p
        · subst a
          by_cases hn : p.val+1 < (R.len g)
          · have hd := forwarding_lowers_latentDebt2 R q s hs.1 g c p hp hn hk he hslots
            omega
          · have hl : p.val+1 = (R.len g) := by have := p.isLt; omega
            have hd := comparison_lowers_latentDebt2 R q s hs g c p hp hl hk he hslots
            omega
        · apply latentDebt2_step_le_of_scheduled_gap R (q+1) s ⟨g,a⟩ hs.2.1
          rw [outbound_wrong_edge R (q+1) s hs.1 g a p q c hp hap he hslots]
          exact Nat.le_refl _
      | returning t c d =>
        have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
        subst t
        rw [he] at hshape
        obtain ⟨p,hp,hslots⟩ := hshape
        change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty) at hslots
        by_cases hap : a.val+1 = p.val
        · by_cases hp1 : p.val = 1
          · have ha : ⟨g,a⟩ = rootV R g := by
              apply vtx_eq R
              · rfl
              · change a.val = 0; omega
            rw [ha]
            have hd := delivery_lowers_latentDebt2 R q s hs.1 g c d p hp1 hk he hslots
            omega
          · have hp2 : 1 < p.val := by omega
            have hd := backward_lowers_latentDebt2 R q s hs.1 g c d p hp2 hk he hslots
            have ha : a = (⟨p.val-1,by have := p.isLt; omega⟩ : Fin (R.len g)) := by
              apply Fin.ext
              change a.val = p.val-1
              omega
            rw [ha]
            omega
        · apply latentDebt2_step_le_of_scheduled_gap R (q+1) s ⟨g,a⟩ hs.2.1
          rw [returning_wrong_edge R (q+1) s hs.1 g a p q c d hp hap he hslots]
          exact Nat.le_refl _



/-! Exact enumeration of the physical ring. Prefix sums make adjacency
and the uniform Fin n scheduler agree, including varying boundary lengths. -/

def gapOffset (R : VFrame) (k : Nat) : Nat :=
  (List.ofFn (fun g : Fin R.m => if g.val < k then R.len g else 0)).sum

theorem prefix_zero (R : VFrame) : gapOffset R 0 = 0 := by simp [gapOffset,ofFn_sum_const]

theorem prefix_total (R : VFrame) : gapOffset R R.m = R.n := by
  simpa only [gapOffset,Fin.isLt,if_true] using R.total

theorem prefix_step (R : VFrame) (g : Fin R.m) : gapOffset R (g.val+1) = gapOffset R g.val + R.len g := by
  have hp : ∀ i : Fin R.m, (if i.val < g.val+1 then R.len i else 0) =
      (if i.val < g.val then R.len i else 0) + (if i=g then R.len g else 0) := by
    intro i
    by_cases he : i=g
    · subst i; simp
    · have hne : i.val ≠ g.val := fun h => he (Fin.ext h)
      by_cases hi : i.val < g.val <;> simp [he,hi,(by omega : i.val < g.val+1 ↔ i.val < g.val)]
  have h := ofFn_sum_eq _ _ hp
  have hs : (List.ofFn (fun i : Fin R.m => if i=g then R.len g else 0)).sum = R.len g :=
    VariableGap.sum_ofFn_single g (R.len g)
  rw [ofFn_sum_add,hs] at h
  exact h

theorem prefix_mono (R : VFrame) {a b : Nat} (h : a ≤ b) : gapOffset R a ≤ gapOffset R b := by
  apply ofFn_sum_le
  intro i
  by_cases ha : i.val < a
  · simp [ha,Nat.lt_of_lt_of_le ha h]
  · simp [ha]

def encode (R : VFrame) (v : Vtx R) : Fin R.n :=
  ⟨gapOffset R v.1.val + v.2.val,by
    have ht := prefix_mono R (Nat.succ_le_of_lt v.1.isLt)
    rw [prefix_total,prefix_step R v.1] at ht
    have := v.2.isLt
    omega⟩

theorem encode_injective (R : VFrame) {v w : Vtx R} (h : encode R v = encode R w) : v=w := by
  have hv := congrArg Fin.val h
  change gapOffset R v.1.val+v.2.val = gapOffset R w.1.val+w.2.val at hv
  have hg : v.1 = w.1 := by
    by_cases hlt : v.1.val < w.1.val
    · have hp := prefix_mono R (Nat.succ_le_of_lt hlt)
      rw [prefix_step] at hp
      have := v.2.isLt
      omega
    · by_cases hgt : w.1.val < v.1.val
      · have hp := prefix_mono R (Nat.succ_le_of_lt hgt)
        rw [prefix_step] at hp
        have := w.2.isLt
        omega
      · exact Fin.ext (by omega)
  apply vtx_eq R v w hg
  have hp := congrArg (fun g : Fin R.m => gapOffset R g.val) hg
  omega

private theorem prefix_cover (R : VFrame) (k : Nat) (hk : k ≤ R.m) (j : Nat) (hj : j < gapOffset R k) :
    ∃ v : Vtx R, gapOffset R v.1.val + v.2.val = j := by
  induction k with
  | zero => rw [prefix_zero] at hj; omega
  | succ k ih =>
    by_cases hp : j < gapOffset R k
    · exact ih (by omega) hp
    · let g : Fin R.m := ⟨k,by omega⟩
      have hstep := prefix_step R g
      change gapOffset R (k+1) = gapOffset R k + R.len g at hstep
      have ha : j-gapOffset R k < R.len g := by omega
      refine ⟨⟨g,⟨j-gapOffset R k,ha⟩⟩,?_⟩
      change gapOffset R k + (j-gapOffset R k) = j
      omega

theorem encode_surjective (R : VFrame) (i : Fin R.n) : ∃ v, encode R v = i := by
  obtain ⟨v,hv⟩ := prefix_cover R R.m (Nat.le_refl _) i.val (by rw [prefix_total]; exact i.isLt)
  exact ⟨v,Fin.ext hv⟩

noncomputable def edgeVtx (R : VFrame) (i : Fin R.n) : Vtx R := (encode_surjective R i).choose

theorem encode_edgeVtx (R : VFrame) (i : Fin R.n) : encode R (edgeVtx R i) = i :=
  (encode_surjective R i).choose_spec

theorem edgeVtx_encode (R : VFrame) (v : Vtx R) : edgeVtx R (encode R v) = v :=
  encode_injective R (encode_edgeVtx R (encode R v))

def placement (R : VFrame) : PeriodHIncidenceChoice.Placement R.n R.m where
  physicalRing := ⟨n_pos R⟩
  root g := encode R (rootV R g)
  root_injective := fun _ _ h => congrArg Sigma.fst (encode_injective R h)

theorem encode_rn (R : VFrame) (v : Vtx R) :
    encode R (rn R v) = (placement R).physicalRing.rightNeighbor (encode R v) := by
  apply Fin.ext
  change (encode R (rn R v)).val = ((encode R v).val+1)%R.n
  by_cases hl : v.2.val+1 < R.len v.1
  · rw [rn_of_lt R v hl]
    have hb := (encode R ⟨v.1,⟨v.2.val+1,hl⟩⟩).isLt
    change gapOffset R v.1.val+(v.2.val+1) < R.n at hb
    change gapOffset R v.1.val+(v.2.val+1) = (gapOffset R v.1.val+v.2.val+1)%R.n
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have ha : v.2.val+1=R.len v.1 := by have := v.2.isLt; omega
    have hp := prefix_step R v.1
    rw [rn_of_last R v hl]
    change gapOffset R (next R v.1).val + 0 = (gapOffset R v.1.val+v.2.val+1)%R.n
    have he : gapOffset R v.1.val+v.2.val+1 = gapOffset R (v.1.val+1) := by omega
    rw [he]
    by_cases hg : v.1.val+1 < R.m
    · have hn : (next R v.1).val=v.1.val+1 := if_pos hg
      have hb := (encode R (rootV R (next R v.1))).isLt
      change gapOffset R (next R v.1).val+0 < R.n at hb
      rw [hn] at hb ⊢
      simp [Nat.mod_eq_of_lt (by omega : gapOffset R (v.1.val+1)<R.n)]
    · have hn : (next R v.1).val=0 := if_neg hg
      have hv : v.1.val+1=R.m := by have := v.1.isLt; omega
      rw [hn,hv,prefix_zero,prefix_total]
      simp

noncomputable def schedulerEquiv (R : VFrame) : VariableGap.Equiv (Fin R.n) (Vtx R) where
  toFun := edgeVtx R
  invFun := encode R
  left_inv := encode_edgeVtx R
  right_inv := edgeVtx_encode R


/-! History words commute with the actual placement incidence kernel. -/
open ShortGapJoinedIncidenceBalance
open ShortGapLineage (updateHistory_other)

def wordOf (R : VFrame) (r : Nat) (s : GhostRing R) : PeriodHIncidenceChoice.Configuration R.m :=
  fun i => choiceToWord ((s.hist i r).getD .race)

def mask (R : VFrame) (r : Nat) (s : GhostRing R) (i : Fin R.m) : Bool := decide (r ≤ s.k i)

theorem hist_monotone (R : VFrame) (s : GhostRing R) (e : Vtx R) (i : Fin R.m)
    (r : Nat) (c : Choice) (hc : s.hist i r = some c) : (ghostStep R s e).hist i r = some c := by
  change (if incident R e (rootV R i) then
    updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i) else s.hist i) r = _
  split
  · exact ShortGapLineage.updateHistory_monotone _ _ _ _ _ hc
  · exact hc
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

private theorem tail_encode (R : VFrame) (e : Vtx R) (i : Fin R.m) :
    (placement R).root i = encode R e ↔ rootV R i = e :=
  ⟨fun h => encode_injective R h, fun h => congrArg (encode R) h⟩

private theorem head_encode (R : VFrame) (e : Vtx R) (i : Fin R.m) :
    (placement R).root i = (placement R).physicalRing.rightNeighbor (encode R e) ↔
      rootV R i = rn R e := by
  rw [← encode_rn]
  exact ⟨fun h => encode_injective R h, fun h => congrArg (encode R) h⟩

/-- The historical word simulates incidence exactly under Lineage:
current Race roots are fresh, so incident rows resolve in their orientation.
The two-epoch closure below supplies these clauses along physical runs. -/
theorem wordOf_step (R : VFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
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


theorem wordOf2_step (R : VFrame) (r : Nat) (s : GhostRing2 R) (e : Vtx R) (hs : Lineage2 R s) :
    word2 R r (ghostStep2 R s e) =
      joinedIncidenceStep (placement R) (genMask2 R r s) (word2 R r s) (encode R e) :=
  wordOf_step R r (view R s) e hs.coherent


/-! Cross-round balance and strict round composition. -/
open ShortGapChoiceStopping BalancedFailureRestartPartialExitEntry ShortGapPipelinedRearmSpec

theorem candidate_round_le_maxGen_of_C4 (R : VFrame) (s : GhostRing2 R) (hs : C4 R s)
    (q : Nat) (hc : VirtualCandidate2 R q s) : q ≤ maxGen R s := by
  obtain ⟨g,hg,_⟩ := hc
  have hq : q ≤ s.k g := by
    by_cases hh : s.k g < q
    · have hf := hs.future g q hh
      simp [word2,hf,choiceToWord] at hg
    · omega
  exact Nat.le_trans hq (ShortGapLineage2Closure.le_generationMax s.k g)

theorem current_candidate_success (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hc : VirtualCandidate2 R r s) : VirtualSuccess R r s :=
  ⟨r,candidate_round_le_maxGen R s hs r hc,hc⟩

def RoundFailure (R : VFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  PeriodHIncidenceChoice.Frozen (word2 R r s) ∧ ¬ VirtualSuccess R r s

theorem roundFailure_uniform (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (h4 : C4 R s) (hf : RoundFailure R r s) : PeriodHIncidenceChoice.Constant (word2 R r s) := by
  apply PeriodHIncidenceChoice.frozen_noCandidate_constant (ring R) _ hf.1
  intro g hg
  exact hf.2 ⟨r,candidate_round_le_maxGen_of_C4 R s h4 r ⟨g,hg⟩,⟨g,hg⟩⟩

theorem no_virtualSuccess_start (R : VFrame) (r : Nat) : ¬ VirtualSuccess R r (ghostStart2 R) := by
  rintro ⟨q,_,g,hg⟩
  have h0 := hg.1
  have h1 := hg.2
  change word2 R q (ghostStart2 R) g = .out1 at h0
  change word2 R q (ghostStart2 R) ((ring R).rightNeighbor g) = .in0 at h1
  have hw : ∀ i, word2 R q (ghostStart2 R) i =
    choiceToWord ((if q=0 then some R.b else none).getD .race) := fun _ => rfl
  rw [hw] at h0 h1
  rw [h0] at h1
  cases h1

theorem dom_start (R : VFrame) : Dom R 1 (ghostStart2 R) :=
  ⟨lineage2_start R,fun _ => Nat.zero_le _,no_virtualSuccess_start R 1⟩

theorem latentDebt2_start (R : VFrame) : latentDebt2 R 1 (ghostStart2 R) = 2*R.n-R.m :=
  sum_two_len_sub_one R

theorem unjoined_debt_on_dom (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (i : Fin R.m) (hi : s.k i < r) : 0 < latentDebt2 R r s :=
  unjoined_gen_has_debt2 R r s hs.1 (dom_denial R r s hs) i hi
noncomputable def successEdgeCount (R : VFrame) (r : Nat) (s : GhostRing2 R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n =>
    if VirtualSuccess R r (ghostStep2 R s (edgeVtx R e)) then 1 else 0)).sum

noncomputable def failureEdgeCount (R : VFrame) (r : Nat) (s : GhostRing2 R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n =>
    if RoundFailure R r (ghostStep2 R s (edgeVtx R e)) then 1 else 0)).sum


private theorem frame_n_gt_one (R : VFrame) : 1 < R.n := by have := m_le_n R; have := R.hm; omega
theorem joined_localBalance (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (b : PeriodHIncidenceChoice.FrozenValue)
    (hb : PeriodHIncidenceChoice.BaseOrRace b (word2 R r s))
    (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    joinedBadEdgeCount b (placement R) (genMask2 R r s) (word2 R r s) ≤
      joinedGoodEdgeCount (ring R) (placement R) (genMask2 R r s) (word2 R r s) :=
  joinedGoodEdgeCount_ge_joinedBadEdgeCount (ring R) R.hm (placement R)
    (frame_n_gt_one R) b _ _ hb hr

/-- Unconditional balance on the requested domain. If a Race root has
not joined, no edge can freeze the word. Otherwise all joined steps equal
bare incidence, whose general balance theorem handles fixed-base, mixed
and all-Race words. Enlarging success can only reduce failure and increase
success counts. No extra BaseOrRace premise is imposed on Dom. -/
theorem genPipelined2_localBalance (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    failureEdgeCount R r s ≤ successEdgeCount R r s := by
  classical
  by_cases hall : ∀ i, word2 R r s i = .race → genMask2 R r s i = true
  · let state : CandidateDrainState (ring R) :=
      ⟨word2 R r s,hr,fun i hi => hs.2.2 (current_candidate_success R r s hs.1 ⟨i,hi⟩)⟩
    have hw : ∀ e : Fin R.n, word2 R r (ghostStep2 R s (edgeVtx R e)) =
        PeriodHIncidenceChoice.incidenceStep (placement R) state.configuration e := by
      intro e
      rw [wordOf2_step R r s _ hs.1,encode_edgeVtx]
      exact joinedIncidenceStep_eq_of_all_joined _ _ _ _ hall
    have hf : failureEdgeCount R r s ≤
        (List.ofFn (fun e : Fin R.n => failureWeight (candidateDrainStep (ring R) (placement R) state e))).sum := by
      apply ofFn_sum_le
      intro e
      by_cases hfail : RoundFailure R r (ghostStep2 R s (edgeVtx R e))
      · have hold : candidateDrainStep (ring R) (placement R) state e = .failure := by
          apply (candidateDrainStep_eq_failure_iff _ _ _ _).mpr
          constructor
          · intro g hg
            apply hfail.2
            apply current_candidate_success R r _ (lineage2_step R s hs.1 _)
            refine ⟨g,?_⟩
            change PeriodHIncidenceChoice.Candidate10 (ring R)
              (word2 R r (ghostStep2 R s (edgeVtx R e))) g
            rw [hw]
            exact hg
          · simpa only [hw] using hfail.1
        simp only [if_pos hfail,hold,failureWeight]
        exact Nat.le_refl _
      · simp only [if_neg hfail]
        exact Nat.zero_le _
    have hsucc :
        (List.ofFn (fun e : Fin R.n => successWeight (candidateDrainStep (ring R) (placement R) state e))).sum ≤
          successEdgeCount R r s := by
      apply ofFn_sum_le
      intro e
      by_cases hold : candidateDrainStep (ring R) (placement R) state e = .success
      · have hg := (candidateDrainStep_eq_success_iff _ _ _ _).mp hold
        have hnew : VirtualSuccess R r (ghostStep2 R s (edgeVtx R e)) := by
          apply current_candidate_success R r _ (lineage2_step R s hs.1 _)
          change ∃ g, PeriodHIncidenceChoice.Candidate10 (ring R)
            (word2 R r (ghostStep2 R s (edgeVtx R e))) g
          rw [hw]
          exact hg
        simp only [hold,successWeight,if_pos hnew]
        exact Nat.le_refl _
      · have hz : successWeight (candidateDrainStep (ring R) (placement R) state e) = 0 := by
          cases he : candidateDrainStep (ring R) (placement R) state e
          · rfl
          · exact False.elim (hold he)
          · rfl
        rw [hz]
        exact Nat.zero_le _
    exact Nat.le_trans hf (Nat.le_trans
      (candidateDrain_localBalance (ring R) R.hm (placement R) (frame_n_gt_one R) state) hsucc)
  · have hn : ∀ e : Fin R.n, ¬ RoundFailure R r (ghostStep2 R s (edgeVtx R e)) := by
      intro e hf
      apply hall
      have hfr := hf.1
      rw [wordOf2_step R r s _ hs.1] at hfr
      exact all_joined_of_frozen _ _ _ _ hfr
    have hz : failureEdgeCount R r s = 0 := by
      simp [failureEdgeCount,hn,ofFn_sum_const]
    rw [hz]
    exact Nat.zero_le _

theorem frozen_word_entered (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (r : Nat) (hf : PeriodHIncidenceChoice.Frozen (word2 R r s)) :
    ∀ i, r ≤ s.k i := by
  intro i
  by_cases h : r ≤ s.k i
  · exact h
  · have hh := hs.coherent.histFuture i r (by change s.k i < r; omega)
    change s.hist i r = none at hh
    have hn := hf i
    exact False.elim (hn (by simp [word2,hh,choiceToWord]))


structure RoundBase (R : VFrame) (r : Nat) (s : GhostRing2 R) : Prop where
  lineage : Lineage2 R s
  entered : ∀ i, r ≤ s.k i
  zero : latentDebt2 R r s = 0
  noSuccess : ¬ VirtualSuccess R r s

theorem RoundBase.toDom {R : VFrame} {r : Nat} {s : GhostRing2 R}
    (h : RoundBase R r s) : Dom R r s :=
  ⟨h.lineage,fun i => Nat.le_trans (Nat.sub_le _ _) (h.entered i),h.noSuccess⟩

/-- Once all owners entered r, generation masking discharges every
round-(r-1) token independently of its retained annotations. -/
theorem all_entered_debt_zero (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (h : ∀ i, r ≤ s.k i) : latentDebt2 R r s = 0 := by
  have ht := all_joined_tokens_done R r (curView R s) h
  simp [latentDebt2,tokens2,ht,LitGapState.hops,ofFn_sum_const]

/-- The converse is the checked normalized-port argument: a lagging
root at zero debt would hold two denials and would already have JOINed. -/
theorem debt0_all_entered (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hn : ¬ VirtualSuccess R r s)
    (hz : latentDebt2 R r s = 0) : ∀ i, r ≤ s.k i := by
  have hd : DenialOnly2 R r s := by
    rcases denial2_or_predecessor_candidate R r s with hd | hc
    · exact hd
    · exact False.elim (hn ⟨r-1,candidate_round_le_maxGen R s hs _ hc,hc⟩)
  exact latentDebt2_zero_all_joined R r s hs hd hz

/-- Base conditions persist until the actual virtual-success port. -/
theorem RoundBase.step {R : VFrame} {r : Nat} {s : GhostRing2 R}
    (h : RoundBase R r s) (e : Vtx R)
    (hn : ¬ VirtualSuccess R r (ghostStep2 R s e)) : RoundBase R r (ghostStep2 R s e) where
  lineage := lineage2_step R s h.lineage e
  entered := fun i => Nat.le_trans (h.entered i) (Nat.le_add_right _ _)
  zero := all_entered_debt_zero R r _ (fun i => Nat.le_trans (h.entered i) (Nat.le_add_right _ _))
  noSuccess := hn

/-- Index-carrying round state; remaining Race excludes both terminals. -/
structure Round (R : VFrame) where
  idx : Nat
  state : GhostRing2 R
  base : RoundBase R idx state
  race : PeriodHIncidenceChoice.HasRace (word2 R idx state)

noncomputable def roundStep (R : VFrame) (s : Round R) (e : Fin R.n) : StopNode (Round R) := by
  classical
  let t := ghostStep2 R s.state (edgeVtx R e)
  exact if hv : VirtualSuccess R s.idx t then .success
    else if hr : PeriodHIncidenceChoice.HasRace (word2 R s.idx t) then
      .active ⟨s.idx,t,s.base.step _ hv,hr⟩ else .failure

def roundPotential (R : VFrame) : StopNode (Round R) → Nat
  | .active s => R.n * PeriodHIncidenceChoice.choiceRaceReserve (word2 R s.idx s.state)
  | .success | .failure => 0


/-- Strict bases have an entered Race, so the reserve-only child sum
follows directly from the joined incidence theorem. -/
theorem reserve_childSum (R : VFrame) (s : Round R) :
    1+(List.ofFn (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
      (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))))).sum ≤
      R.n*PeriodHIncidenceChoice.choiceRaceReserve (word2 R s.idx s.state) := by
  have hr : ∃ i, word2 R s.idx s.state i = .race ∧ genMask2 R s.idx s.state i = true := by
    obtain ⟨i,hi⟩ := s.race
    exact ⟨i,hi,by simp [genMask2,s.base.entered i]⟩
  simpa only [wordOf2_step R s.idx s.state _ s.base.lineage,encode_edgeVtx] using
    joinedReserve_childSum (placement R) (genMask2 R s.idx s.state) (word2 R s.idx s.state) hr
theorem round_bellman (R : VFrame) : NatBellmanSuperSolution (roundStep R) 1 (roundPotential R) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  have hsum : (List.ofFn (fun e => roundPotential R (roundStep R s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => R.n * PeriodHIncidenceChoice.choiceRaceReserve
        (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))))).sum := by
    apply ofFn_sum_le
    intro e
    unfold roundStep
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  rw [ofFn_sum_mul_left] at hsum
  have h := Nat.mul_le_mul_left R.n (reserve_childSum R s)
  rw [Nat.mul_add,Nat.mul_one] at h
  change 1*R.n + _ ≤ R.n * (R.n * _)
  rw [Nat.one_mul]
  omega

theorem roundStep_success_iff (R : VFrame) (s : Round R) (e : Fin R.n) :
    roundStep R s e = .success ↔ VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) := by
  classical
  unfold roundStep
  dsimp only
  split <;> simp_all
  split <;> simp_all

theorem roundStep_failure_iff (R : VFrame) (s : Round R) (e : Fin R.n) :
    roundStep R s e = .failure ↔ RoundFailure R s.idx (ghostStep2 R s.state (edgeVtx R e)) := by
  classical
  have hf : PeriodHIncidenceChoice.Frozen (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))) ↔
      ¬ PeriodHIncidenceChoice.HasRace (word2 R s.idx (ghostStep2 R s.state (edgeVtx R e))) := by
    simp only [PeriodHIncidenceChoice.Frozen,PeriodHIncidenceChoice.HasRace,not_exists]
  unfold roundStep
  dsimp only
  split
  · simp_all [RoundFailure]
  · split <;> simp_all [RoundFailure]

private theorem failureWeight_indicator {S : Type} (x : StopNode S) :
    failureWeight x = @ite Nat (x = .failure) (Classical.propDecidable _) 1 0 := by
  classical
  cases x <;> simp [failureWeight]

private theorem successWeight_indicator {S : Type} (x : StopNode S) :
    successWeight x = @ite Nat (x = .success) (Classical.propDecidable _) 1 0 := by
  classical
  cases x <;> simp [successWeight]

theorem round_balance (R : VFrame) (s : Round R) :
    (List.ofFn (fun e : Fin R.n => failureWeight (roundStep R s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => successWeight (roundStep R s e))).sum := by
  classical
  simp only [failureWeight_indicator,successWeight_indicator,roundStep_failure_iff,roundStep_success_iff]
  exact genPipelined2_localBalance R s.idx s.state s.base.toDom s.race

noncomputable def ghostRoundSpec' (R : VFrame) : PipelinedRoundSpec R.n where
  Round := Round R
  step := roundStep R
  potential := roundPotential R
  bellman := round_bellman R
  balance := round_balance R

theorem roundPotential_le (R : VFrame) (s : Round R) :
    roundPotential R (.active s) ≤ R.n*R.m :=
  Nat.mul_le_mul_left R.n (ShortGapChoiceStopping.choiceRaceReserve_le _)

/-- A resolved history word stays fixed under every ghost step. -/
theorem frozen_word_step (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hf : PeriodHIncidenceChoice.Frozen (word2 R r s)) (e : Vtx R) :
    word2 R r (ghostStep2 R s e) = word2 R r s := by
  funext i
  have hn := hf i
  cases hh : s.hist i r with
  | none => exact False.elim (hn (by simp [word2,hh,choiceToWord]))
  | some c =>
    have hp := history2_monotone R s e i r c hh
    simp only [word2,hh,hp]

/-- Service r drains round r, with debt at index r+1. The zero-debt
state is an exit, so it is excluded from this active domain. -/
structure ServiceDom (R : VFrame) (r : Nat) (s : GhostRing2 R) : Prop where
  lineage : Lineage2 R s
  frozen : PeriodHIncidenceChoice.Frozen (word2 R r s)
  constant : PeriodHIncidenceChoice.Constant (word2 R r s)
  noSuccess : ¬ VirtualSuccess R r s
  positive : 0 < latentDebt2 R (r+1) s

theorem ServiceDom.toDom {R : VFrame} {r : Nat} {s : GhostRing2 R}
    (h : ServiceDom R r s) : Dom R (r+1) s :=
  ⟨h.lineage,by
    intro i
    simpa only [Nat.add_sub_cancel] using
      frozen_word_entered R s h.lineage r h.frozen i,h.noSuccess⟩

theorem ServiceDom.step {R : VFrame} {r : Nat} {s : GhostRing2 R}
    (h : ServiceDom R r s) (e : Vtx R)
    (hn : ¬ VirtualSuccess R r (ghostStep2 R s e))
    (hp : 0 < latentDebt2 R (r+1) (ghostStep2 R s e)) : ServiceDom R r (ghostStep2 R s e) where
  lineage := lineage2_step R s h.lineage e
  frozen := by rw [frozen_word_step R r s h.frozen e]; exact h.frozen
  constant := by rw [frozen_word_step R r s h.frozen e]; exact h.constant
  noSuccess := hn
  positive := hp

private theorem fresh_left_ccw (a : Agent) :
    (row (.root .race .toSend .free) a).1.ccwPort = some .free := by
  cases a with
  | interior t => cases t <;> rfl
  | root c cw ccw => cases ccw <;> rfl

/-- A fresh Race root cannot consume two denials in the same interaction
that first resolves it: one of its two own ports is still clear. -/
theorem fresh_no_join (R : VFrame) (s : GhostRing2 R) (e : Vtx R) (i : Fin R.m)
    (hi : s.cfg (rootV R i) = .root .race .toSend .free) :
    fires R (physical2 R s) e i = false := by
  cases hf : fires R (physical2 R s) e i with
  | false => rfl
  | true =>
    obtain ⟨hinc,c,hraw⟩ := (fires_iff R (physical2 R s) e i).mp hf
    change rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial at hraw
    by_cases hl : rootV R i = e
    · have hh : s.cfg e = .root .race .toSend .free := hl ▸ hi
      have hp := congrArg Agent.ccwPort hraw
      rw [rawAt,if_pos hl,hh,fresh_left_ccw] at hp
      cases hp
    · by_cases hr : rootV R i = rn R e
      · have hh : s.cfg (rn R e) = .root .race .toSend .free := hr ▸ hi
        have hp := congrArg Agent.cwPort hraw
        rw [rawAt,if_neg hl,if_pos hr,hh,row_right_cw] at hp
        cases hp
      · exact False.elim (hinc.elim hl hr)

/-- At a strict base, a Race in word r is a still-unresolved root of
generation exactly r; history cannot revert a recorded choice to Race. -/
theorem race_root_current (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hi : ∀ i, r ≤ s.k i) (i : Fin R.m)
    (hr : word2 R r s i = .race) :
    s.k i = r ∧ s.cfg (rootV R i) = .root .race .toSend .free := by
  have hh : s.hist i r = none := by
    cases he : s.hist i r with
    | none => rfl
    | some c =>
      have hn := hs.coherent.histValues i r c he
      cases c <;> simp_all [word2,choiceToWord]
  have hk : s.k i = r := by
    have hb := hi i
    by_cases h : r < s.k i
    · obtain ⟨c,hc⟩ := hs.coherent.histPast i r h
      change s.hist i r = some c at hc
      rw [hh] at hc; cases hc
    · omega
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots i
  have hnow := hs.coherent.histNow i c cw ccw hroot
  change s.cfg (rootV R i) = .root c cw ccw at hroot
  change s.hist i (s.k i) = resolvedOpt c at hnow
  rw [hk,hh] at hnow
  have hc : c = .race := by cases c <;> first | rfl | cases hnow
  refine ⟨hk,hs.coherent.raceReady i ?_⟩
  change (s.cfg (rootV R i)).choice = some .race
  rw [hroot,hc]; rfl

/-- A newly joined root has no choice recorded yet in its new generation. -/
theorem joined_word_race (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hf : fires R (physical2 R s) e i = true) :
    word2 R ((ghostStep2 R s e).k i) (ghostStep2 R s e) i = .race := by
  have hroot := root_cfg_join R s e i hf
  have hp := (lineage2_step R s hs e).coherent.histNow i .race .toSend .free hroot
  change (ghostStep2 R s e).hist i ((ghostStep2 R s e).k i) = none at hp
  simp [word2,hp,choiceToWord]

/-- A round failure really enters active service: its last unresolved
root could not JOIN in that resolving interaction. -/
theorem failure_service_entry (R : VFrame) (s : Round R) (e : Fin R.n)
    (hf : roundStep R s e = .failure) : ServiceDom R s.idx (ghostStep2 R s.state (edgeVtx R e)) := by
  have ht := lineage2_step R s.state s.base.lineage (edgeVtx R e)
  have hh := (roundStep_failure_iff R s e).mp hf
  have hd : Dom R (s.idx+1) (ghostStep2 R s.state (edgeVtx R e)) := ⟨ht,by
    intro i
    simpa only [Nat.add_sub_cancel] using
      frozen_word_entered R _ ht s.idx hh.1 i,hh.2⟩
  obtain ⟨i,hi⟩ := s.race
  obtain ⟨hk,hroot⟩ := race_root_current R s.idx s.state s.base.lineage s.base.entered i hi
  have hj := fresh_no_join R s.state (edgeVtx R e) i hroot
  have hp : (ghostStep2 R s.state (edgeVtx R e)).k i < s.idx+1 := by
    simp [ghostStep2_k,hj,hk]
  exact ⟨ht,hh.1,roundFailure_uniform R s.idx _ (C4_step R s.state s.base.lineage _) hh,hh.2,
    unjoined_debt_on_dom R (s.idx+1) _ hd i hp⟩

/-- A service exit supplies both the next strict base and a genuine
remaining Race: some last lagging root JOINed on this edge. -/
theorem service_exit (R : VFrame) (r : Nat) (s : GhostRing2 R) (hs : ServiceDom R r s)
    (e : Vtx R) (hn : ¬ VirtualSuccess R r (ghostStep2 R s e))
    (hz : latentDebt2 R (r+1) (ghostStep2 R s e) = 0) :
    RoundBase R (r+1) (ghostStep2 R s e) ∧
      PeriodHIncidenceChoice.HasRace (word2 R (r+1) (ghostStep2 R s e)) := by
  have hpost := lineage2_step R s hs.lineage e
  have hentered := debt0_all_entered R (r+1) _ hpost hn hz
  refine ⟨⟨hpost,hentered,hz,hn⟩,?_⟩
  have hex : ∃ i, s.k i < r+1 := by
    apply Classical.byContradiction
    intro hh
    have ha : ∀ i, r+1 ≤ s.k i := by
      intro i
      have hi : ¬ s.k i < r+1 := fun hi => hh ⟨i,hi⟩
      omega
    have hz := all_entered_debt_zero R (r+1) s ha
    have hp := hs.positive
    omega
  obtain ⟨i,hi⟩ := hex
  have hnew := hentered i
  have hk := ghostStep2_k R s e i
  have hf : fires R (physical2 R s) e i = true := by
    cases hh : fires R (physical2 R s) e i with
    | true => rfl
    | false => simp only [hh,Bool.false_eq_true,if_false,Nat.add_zero] at hk; omega
  have heq : (ghostStep2 R s e).k i = r+1 := by
    simp only [hf,if_true] at hk
    omega
  exact ⟨i,heq ▸ joined_word_race R s hs.lineage e i hf⟩

structure Service (R : VFrame) where
  idx : Nat
  state : GhostRing2 R
  dom : ServiceDom R idx state

noncomputable def serviceStep (R : VFrame) (s : Service R) (e : Fin R.n) :
    ServiceOutcome (Service R) (Round R) := by
  classical
  let t := ghostStep2 R s.state (edgeVtx R e)
  exact if hv : VirtualSuccess R s.idx t then .succeed
    else if hz : latentDebt2 R (s.idx+1) t = 0 then
      .exit ⟨s.idx+1,t,(service_exit R s.idx s.state s.dom _ hv hz).1,
        (service_exit R s.idx s.state s.dom _ hv hz).2⟩
    else .cont ⟨s.idx,t,s.dom.step _ hv (Nat.pos_of_ne_zero hz)⟩

def servicePotential (R : VFrame) (s : Service R) : Nat :=
  R.n * latentDebt2 R (s.idx+1) s.state

private theorem sum_strict {n : Nat} (f g : Fin n → Nat) (i : Fin n)
    (hle : ∀ j, f j ≤ g j) (hlt : f i < g i) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht := ofFn_sum_le (fun j : Fin n => f j.succ) (fun j => g j.succ)
        (fun j => hle j.succ)
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      let j : Fin n := ⟨i.val-1,by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin n => f j.succ) (fun j => g j.succ) j
        (fun j => hle j.succ) (by simpa only [hj] using hlt)
      have h0 := hle 0
      omega

/-- Every service child has nonincreasing debt and one physical edge
strictly advances; service success and exit can only lower its potential. -/
theorem service_bellman (R : VFrame) : ServiceBellman (serviceStep R) 1 (servicePotential R) := by
  classical
  intro s
  have hd := s.dom.toDom
  have hle := latentDebt2_step_le R (s.idx+1) s.state hd
  obtain ⟨e,he⟩ := advancing_edge_lowers_latentDebt2 R (s.idx+1) s.state hd s.dom.positive
  have hlt := sum_strict
    (fun a : Fin R.n => latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R a)))
    (fun _ => latentDebt2 R (s.idx+1) s.state) (encode R e)
    (fun a => hle _) (by rw [edgeVtx_encode]; change latentDebt2 R (s.idx+1) (ghostStep2 R s.state e) < _; omega)
  rw [ofFn_sum_const] at hlt
  have hsum : (List.ofFn (fun a : Fin R.n =>
      serviceOutcomePotential (servicePotential R) (serviceStep R s a))).sum ≤
      (List.ofFn (fun a : Fin R.n => R.n * latentDebt2 R (s.idx+1)
        (ghostStep2 R s.state (edgeVtx R a)))).sum := by
    apply ofFn_sum_le
    intro a
    unfold serviceStep
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
  rw [ofFn_sum_mul_left] at hsum
  have hb : 1 + (List.ofFn (fun a : Fin R.n =>
      latentDebt2 R (s.idx+1) (ghostStep2 R s.state (edgeVtx R a)))).sum ≤
      R.n * latentDebt2 R (s.idx+1) s.state := by omega
  have hm := Nat.mul_le_mul_left R.n hb
  rw [Nat.mul_add,Nat.mul_one] at hm
  change 1*R.n + _ ≤ R.n * (R.n * _)
  rw [Nat.one_mul]
  omega


/-- The service cap is n times the sum of the actual per-gap budgets. -/
theorem servicePotential_le (R : VFrame) (s : Service R) :
    servicePotential R s ≤ R.n*(2*R.n-R.m) :=
  Nat.mul_le_mul_left R.n (latentDebt_total_var_le R (s.idx+1) s.state)


/-- Clean start still owes the uniform-choice round-0 service, now with
one latent token of budget 2 len g-1 in each unequal gap. -/
def initialService (R : VFrame) : Service R where
  idx := 0
  state := ghostStart2 R
  dom := {
    lineage := lineage2_start R
    frozen := by
      intro i
      rcases R.hb with hb | hb <;> simp [word2,ghostStart2,ghostStart,hb,choiceToWord]
    constant := ⟨choiceToWord R.b,fun _ => rfl⟩
    noSuccess := no_virtualSuccess_start R 0
    positive := by rw [latentDebt2_start]; have := m_le_n R; have := n_pos R; omega }
noncomputable def serviceEntry (R : VFrame) (s : Round R) (e : Fin R.n) : Service R := by
  classical
  exact if hf : roundStep R s e = .failure then
    ⟨s.idx,ghostStep2 R s.state (edgeVtx R e),failure_service_entry R s e hf⟩
    else initialService R

theorem serviceEntry_of_failure (R : VFrame) (s : Round R) (e : Fin R.n)
    (hf : roundStep R s e = .failure) :
    (serviceEntry R s e).idx = s.idx ∧
      (serviceEntry R s e).state = ghostStep2 R s.state (edgeVtx R e) := by
  simp [serviceEntry,hf]

/-- Fully instantiated cross-round restart certificate, with round
budget A=nm and literal service budget n(2n-m). -/
noncomputable def ghostRearmSpec (R : VFrame) :
    PipelinedRearmSpec (ghostRoundSpec' R) (R.n*R.m) (R.n*(2*R.n-R.m)) where
  State := Service R
  step := serviceStep R
  entry := serviceEntry R
  potential := servicePotential R
  bellman := service_bellman R
  entry_le := fun s e => servicePotential_le R (serviceEntry R s e)
  exit_le := fun _ _ t _ => roundPotential_le R t

theorem ghostRearm_bellman (R : VFrame) :
    NatBellmanSuperSolution (ghostRearmSpec R).restartStep 1 (ghostRearmSpec R).restartPotential :=
  (ghostRearmSpec R).restart_natBellmanSuperSolution


/-- A full service budget plus one reserve equals 2n². -/
theorem reserve_service_eq (R : VFrame) : R.n*R.m + R.n*(2*R.n-R.m) = 2*R.n*R.n := by
  have h : R.m+(2*R.n-R.m)=2*R.n := by have := m_le_n R; omega
  rw [← Nat.mul_add,h]
  ac_rfl

theorem tightBudget_eq (R : VFrame) :
    2*(R.n*R.m)+R.n*(2*R.n-R.m) = R.n*R.m+2*R.n*R.n := by
  have := reserve_service_eq R
  omega

theorem composed_truncatedCost_le (R : VFrame) (s : Round R) (T : Nat) :
    truncatedActiveCostNumerator (ghostRearmSpec R).restartStep (.active (.round s)) T ≤
      R.n^T*(R.n*R.m+2*R.n*R.n) := by
  have h := (ghostRearmSpec R).base_truncatedCost_le s T
  have hp := roundPotential_le R s
  apply Nat.le_trans h (Nat.mul_le_mul_left _ ?_)
  rw [← tightBudget_eq]
  change roundPotential R (.active s) + _ ≤ _
  omega

theorem initialService_potential (R : VFrame) :
    (ghostRearmSpec R).restartPotential (.active (.reset (initialService R))) = 4*R.n*R.n := by
  change R.n*latentDebt2 R 1 (ghostStart2 R)+R.n*R.m+(R.n*R.m+R.n*(2*R.n-R.m)) = _
  rw [latentDebt2_start,reserve_service_eq]
  have h := reserve_service_eq R
  have h4 : 4*R.n*R.n = 2*R.n*R.n + 2*R.n*R.n := by rw [← Nat.add_mul,← Nat.add_mul]
  omega

theorem cleanStart_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (ghostRearmSpec R).restartStep
      (.active (.reset (initialService R))) T ≤ R.n^T*(4*R.n*R.n) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (ghostRearmSpec R).restartStep 1 (ghostRearmSpec R).restartPotential
    (ghostRearm_bellman R) (.active (.reset (initialService R))) T
  simpa only [Nat.one_mul,initialService_potential] using h
private theorem success_tail_of_cost_bound {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S) (s : S)
    (hn : ∀ s e, step s e ≠ .failure) (hB : 0 < B)
    (hc : ∀ T, truncatedActiveCostNumerator step (.active s) T ≤ n^T*B) (factor : Nat) :
    (factor-1)*n^(factor*B) ≤ factor*successCount step (.active s) (factor*B) := by
  have hd := horizon_mul_activeCount_le_truncatedActiveCostNumerator step (.active s) (factor*B)
  have hb := hc (factor*B)
  have hmul : B * (factor * activeCount step (.active s) (factor*B)) ≤ B*n^(factor*B) := by
    calc
      _ = (factor*B)*activeCount step (.active s) (factor*B) := by ac_rfl
      _ ≤ n^(factor*B)*B := Nat.le_trans hd hb
      _ = _ := Nat.mul_comm _ _
  have hactive := Nat.le_of_mul_le_mul_left hmul hB
  have hfailure := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure step hn s (factor*B)
  have hp := node_count_partition step (.active s) (factor*B)
  have hsum : activeCount step (.active s) (factor*B) + successCount step (.active s) (factor*B) = n^(factor*B) := by omega
  by_cases hf : factor = 0
  · simp [hf]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf
    simp only [Nat.add_sub_cancel,Nat.succ_eq_add_one] at hactive hsum ⊢
    rw [← hsum] at hactive ⊢
    rw [Nat.mul_add]
    simp only [Nat.add_mul,Nat.one_mul] at hactive ⊢
    omega

theorem cleanStart_not_active_round (R : VFrame) (r : Nat) :
    ¬ (RoundBase R r (ghostStart2 R) ∧ PeriodHIncidenceChoice.HasRace (word2 R r (ghostStart2 R))) := by
  rintro ⟨hb,hr⟩
  have hk := hb.entered ⟨0,by have := R.hm; omega⟩
  change r ≤ 0 at hk
  have hz : r = 0 := by omega
  subst r
  obtain ⟨i,hi⟩ := hr
  rcases R.hb with h | h <;> simp [word2,ghostStart2,ghostStart,h,choiceToWord] at hi

/-! The strict round-1 start is the rearmed all-Race configuration,
distinct from ghostStart2, which still owes uniform round-0 service. -/

def strictStart (R : VFrame) : GhostRing2 R where
  cfg v := if v.2.val = 0 then .root .race .toSend .free else .interior .empty
  k _ := 1
  hist _ q := if q = 0 then some R.b else none
  epoch _ := ⟨.idle,.idle⟩

theorem strictStart_root (R : VFrame) (g : Fin R.m) :
    (strictStart R).cfg (rootV R g) = .root .race .toSend .free := rfl

theorem strictStart_view_epoch (R : VFrame) (g : Fin R.m) :
    (view R (strictStart R)).epoch g = .delivered 0 R.b R.b := by
  simp [strictStart,view,prefixView,combinedView]

theorem strictStart_shape (R : VFrame) : C1 R (strictStart R) := by
  intro g
  rw [EpochShape,strictStart_view_epoch]
  refine ⟨Or.inr rfl,Or.inr rfl,rfl,rfl,?_⟩
  intro a ha
  change (strictStart R).cfg ⟨g,a⟩ = _
  change (if a.val = 0 then Agent.root .race .toSend .free else .interior .empty) = _
  rw [if_neg (by omega : a.val ≠ 0)]

/-- A concrete inhabitant of the strict base, retaining the completed
uniform round-0 history and fresh Race ports at generation 1. -/
theorem strictStart_lineage (R : VFrame) : Lineage2 R (strictStart R) := by
  apply (lineage2_iff_clauses R _).mpr
  refine ⟨?_,strictStart_shape R,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨fun i => ⟨.race,.toSend,.free,rfl⟩,fun _ => rfl,fun _ _ => rfl⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro g
      change _ ↔ Live ((view R (strictStart R)).epoch g)
      rw [strictStart_view_epoch]
      exact ⟨(fun h => by cases h),False.elim⟩
    · intro g
      change CwHeld (some .toSend) ↔ DeliveredAt ((view R (strictStart R)).epoch g) 1
      rw [strictStart_view_epoch]
      exact ⟨False.elim,fun h => by change 1 ≤ 0 at h; omega⟩
    · intro g h
      change DeliveredAt ((view R (strictStart R)).epoch g) 1 at h
      rw [strictStart_view_epoch] at h
      change 1 ≤ 0 at h
      omega
    · intro g _; rfl
    · intro g
      exact ⟨(fun h => by cases h),False.elim⟩
  · refine ⟨?_,?_,?_⟩
    · intro g
      change CcwHeld (some .free) ↔ ComparedAt ((view R (strictStart R)).epoch g) 1
      rw [strictStart_view_epoch]
      exact ⟨False.elim,fun h => by change 1 ≤ 0 at h; omega⟩
    · intro g h
      change ComparedAt ((view R (strictStart R)).epoch g) 1 at h
      rw [strictStart_view_epoch] at h
      change 1 ≤ 0 at h
      omega
    · intro g
      exact ⟨False.elim,fun h => h.elim id id⟩
  · refine ⟨?_,?_,?_,?_⟩
    · intro i q c hc
      change (if q = 0 then some R.b else none) = some c at hc
      split at hc
      · cases hc
        rcases R.hb with hb | hb <;> simp [hb]
      · cases hc
    · intro i q hq
      change q < 1 at hq
      have hq0 : q = 0 := by omega
      subst q
      exact ⟨R.b,rfl⟩
    · intro i c cw ccw hc
      change (strictStart R).cfg (rootV R i) = .root c cw ccw at hc
      rw [strictStart_root] at hc
      cases hc
      rfl
    · intro i q hq
      change 1 < q at hq
      change (if q = 0 then some R.b else none) = none
      exact if_neg (by omega)
  · intro g; trivial
  · intro g; trivial
  · apply C7_of_C1_completed_denials R _ (strictStart_shape R)
    intro i q hq
    change q < 1 at hq
    have hq0 : q = 0 := by omega
    subst q
    have hb : res R.b R.b = .denial := by rcases R.hb with hb | hb <;> simp [hb,res]
    exact ⟨⟨R.b,R.b,rfl,rfl,hb⟩,⟨R.b,R.b,rfl,rfl,hb⟩⟩

theorem strictStart_no_success (R : VFrame) : ¬ VirtualSuccess R 1 (strictStart R) := by
  rintro ⟨q,_,g,hg⟩
  have hw : ∀ i, word2 R q (strictStart R) i = choiceToWord
      ((if q = 0 then some R.b else none).getD .race) := fun _ => rfl
  have h0 := hg.1
  have h1 := hg.2
  change word2 R q (strictStart R) g = .out1 at h0
  change word2 R q (strictStart R) ((ring R).rightNeighbor g) = .in0 at h1
  rw [ring_next] at h1
  rw [hw] at h0 h1
  rw [h0] at h1
  cases h1

def strictRoundStart (R : VFrame) : Round R where
  idx := 1
  state := strictStart R
  base := ⟨strictStart_lineage R,fun _ => Nat.le_refl _,
    all_entered_debt_zero R 1 _ (fun _ => Nat.le_refl _),strictStart_no_success R⟩
  race := ⟨⟨0,by have := R.hm; omega⟩,rfl⟩


/-- The strict all-Race base realizes the advertised initial credit. -/
theorem strictRoundStart_potential (R : VFrame) :
    (ghostRearmSpec R).restartPotential (.active (.round (strictRoundStart R))) =
      R.n*R.m+2*R.n*R.n := by
  have hw : word2 R 1 (strictStart R) = fun _ => .race := rfl
  change R.n*PeriodHIncidenceChoice.choiceRaceReserve (word2 R 1 (strictStart R)) +
    (R.n*R.m+R.n*(2*R.n-R.m)) = _
  have hr : PeriodHIncidenceChoice.choiceRaceReserve (fun _ : Fin R.m => .race) = R.m :=
    ShortGapChoiceStopping.choiceRaceReserve_allRace R.m
  rw [hw,hr,reserve_service_eq]

theorem strictStart_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (ghostRearmSpec R).restartStep
      (.active (.round (strictRoundStart R))) T ≤ R.n^T*(R.n*R.m+2*R.n*R.n) :=
  composed_truncatedCost_le R (strictRoundStart R) T

theorem composed_success_one_minus_inv_factor (R : VFrame) (s : Round R) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m+2*R.n*R.n)) ≤
      factor*successCount (ghostRearmSpec R).restartStep (.active (.round s))
        (factor*(R.n*R.m+2*R.n*R.n)) := by
  apply success_tail_of_cost_bound _ _ (ghostRearmSpec R).restartStep_ne_failure _
    (composed_truncatedCost_le R s) factor
  have h := Nat.mul_pos (n_pos R) (by have := R.hm; omega : 0 < R.m)
  omega


/-! The more general cohort cut charges both reserve and predecessor debt.
Strict bases above are its zero-debt specialization. -/

def roundDebt2 (R : VFrame) (r : Nat) (s : GhostRing2 R) : Nat :=
  PeriodHIncidenceChoice.choiceRaceReserve (word2 R r s)+latentDebt2 R r s

theorem potential2_le_cut_budget (R : VFrame) (r : Nat) (s : GhostRing2 R) :
    R.n*roundDebt2 R r s ≤ 2*R.n*R.n := by
  have hr := ShortGapChoiceStopping.choiceRaceReserve_le (word2 R r s)
  have hd := latentDebt_total_var_le R r s
  have hm := m_le_n R
  have h : roundDebt2 R r s ≤ 2*R.n := by unfold roundDebt2; omega
  have hn := Nat.mul_le_mul_left R.n h
  have he : R.n*(2*R.n)=2*R.n*R.n := by ac_rfl
  rw [he] at hn
  exact hn

theorem genPipelined2_childSum (R : VFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    1+(List.ofFn (fun e : Fin R.n => roundDebt2 R r (ghostStep2 R s (edgeVtx R e)))).sum ≤
      R.n*roundDebt2 R r s := by
  have hres : ∀ e : Fin R.n, PeriodHIncidenceChoice.choiceRaceReserve (word2 R r (ghostStep2 R s (edgeVtx R e))) ≤
      PeriodHIncidenceChoice.choiceRaceReserve (word2 R r s) := by
    intro e
    rw [wordOf2_step R r s _ hs.1]
    exact choiceRaceReserve_joinedIncidenceStep_le _ _ _ _
  have hdebt := latentDebt2_step_le R r s hs
  have hsumR := ofFn_sum_le _ _ hres
  have hsumD := ofFn_sum_le _ _ (fun e : Fin R.n => hdebt (edgeVtx R e))
  rw [ofFn_sum_const] at hsumR hsumD
  unfold roundDebt2
  rw [ofFn_sum_add,Nat.mul_add]
  by_cases hj : ∃ i, word2 R r s i = .race ∧ genMask2 R r s i = true
  · have h := joinedReserve_childSum (placement R) (genMask2 R r s) (word2 R r s) hj
    have he : (fun e : Fin R.n => joinedIncidenceStep (placement R) (genMask2 R r s) (word2 R r s) e) =
        (fun e => word2 R r (ghostStep2 R s (edgeVtx R e))) := by
      funext e
      rw [wordOf2_step R r s _ hs.1,encode_edgeVtx]
    have hsumeq := ofFn_sum_eq
      (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
        (joinedIncidenceStep (placement R) (genMask2 R r s) (word2 R r s) e))
      (fun e => PeriodHIncidenceChoice.choiceRaceReserve (word2 R r (ghostStep2 R s (edgeVtx R e))))
      (fun e => congrArg PeriodHIncidenceChoice.choiceRaceReserve (congrFun he e))
    rw [hsumeq] at h
    omega
  · obtain ⟨i,hi⟩ := hr
    have hk : s.k i < r := by
      by_cases hh : r ≤ s.k i
      · exact False.elim (hj ⟨i,hi,by simp [genMask2,hh]⟩)
      · omega
    obtain ⟨e,he⟩ := advancing_edge_lowers_latentDebt2 R r s hs (unjoined_debt_on_dom R r s hs i hk)
    have h := sum_strict
      (fun a : Fin R.n => latentDebt2 R r (ghostStep2 R s (edgeVtx R a)))
      (fun _ => latentDebt2 R r s) (encode R e) (fun a => hdebt _)
      (by rw [edgeVtx_encode]; omega)
    rw [ofFn_sum_const] at h
    omega

abbrev CutState (R : VFrame) (r : Nat) :=
  {s : GhostRing2 R // Dom R r s ∧ PeriodHIncidenceChoice.HasRace (word2 R r s)}

noncomputable def cutStep (R : VFrame) (r : Nat) (s : CutState R r) (e : Fin R.n) : StopNode (CutState R r) := by
  classical
  let t := ghostStep2 R s.val (edgeVtx R e)
  exact if hv : VirtualSuccess R r t then .success
    else if hr : PeriodHIncidenceChoice.HasRace (word2 R r t) then
      .active ⟨t,⟨lineage2_step R s.val s.property.1.1 _,
        fun i => Nat.le_trans (s.property.1.2.1 i) (Nat.le_add_right _ _),hv⟩,hr⟩
      else .failure

def cutPotential (R : VFrame) (r : Nat) : StopNode (CutState R r) → Nat
  | .active s => R.n*roundDebt2 R r s.val
  | .success | .failure => 0

theorem cut_reserveDebt_bellman_var (R : VFrame) (r : Nat) :
    NatBellmanSuperSolution (cutStep R r) 1 (cutPotential R r) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  have hsum : (List.ofFn (fun e => cutPotential R r (cutStep R r s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => R.n*roundDebt2 R r (ghostStep2 R s.val (edgeVtx R e)))).sum := by
    apply ofFn_sum_le
    intro e
    unfold cutStep
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  rw [ofFn_sum_mul_left] at hsum
  have h := Nat.mul_le_mul_left R.n (genPipelined2_childSum R r s.val s.property.1 s.property.2)
  rw [Nat.mul_add,Nat.mul_one] at h
  change 1*R.n + _ ≤ R.n*(R.n*_)
  rw [Nat.one_mul]
  omega


structure Locked10 (R : VFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m) : Prop where
  lineage : Lineage2 R s
  left : s.hist g q = some .out1
  right : s.hist (next R g) q = some .in0

def BothCandidate (R : VFrame) (s : GhostRing2 R) (g : Fin R.m) : Prop :=
  (s.cfg (rootV R g)).cwPort = some .heldCandidate ∧
    (s.cfg (rootV R (next R g))).ccwPort = some .heldCandidate

theorem candidate10_to_Locked10 (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (g : Fin R.m) (hc : PeriodHIncidenceChoice.Candidate10 (ring R) (word2 R q s) g) :
    Locked10 R s q g := by
  refine ⟨hs,?_,?_⟩
  · have h := hc.1
    cases he : s.hist g q with
    | none => simp [word2,he,choiceToWord] at h
    | some c => cases c <;> simp_all [word2,choiceToWord]
  · have h := hc.2
    rw [ring_next] at h
    change word2 R q s (next R g) = .in0 at h
    cases he : s.hist (next R g) q with
    | none => simp [word2,he,choiceToWord] at h
    | some c => cases c <;> simp_all [word2,choiceToWord]

theorem Locked10.step {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) (e : Vtx R) : Locked10 R (ghostStep2 R s e) q g :=
  ⟨lineage2_step R s h.lineage e,history2_monotone R s e g q .out1 h.left,
    history2_monotone R s e (next R g) q .in0 h.right⟩

/-- Historical candidate endpoints cannot have completed this round:
either completion would supply a contradictory historical denial. -/
theorem Locked10.generations {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) : s.k g = q ∧ s.k (next R g) = q := by
  have noDenial : ¬ HistoricalDenial R (view R s) g q := by
    rintro ⟨c,d,hc,hd,hv⟩
    change s.hist g q = some c at hc
    change s.hist (next R g) q = some d at hd
    rw [h.left] at hc
    rw [h.right] at hd
    cases hc; cases hd; cases hv
  have hL : q ≤ s.k g := by
    by_cases hh : s.k g < q
    · have hn := h.lineage.coherent.histFuture g q hh
      change s.hist g q = none at hn
      rw [h.left] at hn; cases hn
    · omega
  have hR : q ≤ s.k (next R g) := by
    by_cases hh : s.k (next R g) < q
    · have hn := h.lineage.coherent.histFuture (next R g) q hh
      change s.hist (next R g) q = none at hn
      rw [h.right] at hn; cases hn
    · omega
  constructor
  · by_cases hh : q < s.k g
    · exact False.elim (noDenial (h.lineage.coherent.joinedDenials g q hh).2.2.1)
    · omega
  · by_cases hh : q < s.k (next R g)
    · have hd := (h.lineage.coherent.joinedDenials (next R g) q hh).2.2.2
      rw [prev_next] at hd
      exact False.elim (noDenial hd)
    · omega

theorem Locked10.no_join {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) (e : Vtx R) :
    fires R (physical2 R s) e g = false ∧ fires R (physical2 R s) e (next R g) = false := by
  have hb := h.generations
  have ha := (h.step e).generations
  have hl := ghostStep2_k R s e g
  have hr := ghostStep2_k R s e (next R g)
  constructor
  · cases hf : fires R (physical2 R s) e g with
    | false => rfl
    | true => simp only [hf,if_true] at hl; omega
  · cases hf : fires R (physical2 R s) e (next R g) with
    | false => rfl
    | true => simp only [hf,if_true] at hr; omega

/-- Both endpoint choices are the recorded locked values. -/
theorem Locked10.root_choices {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) :
    (∃ cw ccw, s.cfg (rootV R g) = .root .out1 cw ccw) ∧
    (∃ cw ccw, s.cfg (rootV R (next R g)) = .root .in0 cw ccw) := by
  have hk := h.generations
  constructor
  · obtain ⟨c,cw,ccw,hc⟩ := h.lineage.coherent.roots g
    have hh := h.lineage.coherent.histNow g c cw ccw hc
    change s.hist g (s.k g) = resolvedOpt c at hh
    rw [hk.1,h.left] at hh
    cases c <;> first | exact ⟨cw,ccw,hc⟩ | cases hh
  · obtain ⟨c,cw,ccw,hc⟩ := h.lineage.coherent.roots (next R g)
    have hh := h.lineage.coherent.histNow (next R g) c cw ccw hc
    change s.hist (next R g) (s.k (next R g)) = resolvedOpt c at hh
    rw [hk.2,h.right] at hh
    cases c <;> first | exact ⟨cw,ccw,hc⟩ | cases hh

/-- Before comparison the right port is free. After comparison the
returning/delivered locked result holds candidate, never denial. -/
theorem Locked10.right_port {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) :
    (s.cfg (rootV R (next R g))).ccwPort =
      if ComparedAt ((view R s).epoch g) q then some .heldCandidate else some .free := by
  classical
  by_cases hc : ComparedAt ((view R s).epoch g) q
  · rw [if_pos hc]
    obtain ⟨c,d,hl,hr,hv⟩ := h.lineage.coherent.incomingValue g (by
      change ComparedAt ((view R s).epoch g) (s.k (next R g))
      rw [h.generations.2]; exact hc)
    change s.hist g (s.k (next R g)) = some c at hl
    change s.hist (next R g) (s.k (next R g)) = some d at hr
    rw [h.generations.2,h.left] at hl
    rw [h.generations.2,h.right] at hr
    cases hl; cases hr
    exact hv
  · rw [if_neg hc]
    have hn : ¬ CcwHeld (s.cfg (rootV R (next R g))).ccwPort := by
      intro hh
      have hv := (h.lineage.coherent.incoming g).mp hh
      change ComparedAt ((view R s).epoch g) (s.k (next R g)) at hv
      rw [h.generations.2] at hv
      exact hc hv
    obtain ⟨cw,ccw,hr⟩ := h.root_choices.2
    rw [hr] at hn ⊢
    cases ccw with
    | free => rfl
    | heldDenial => exact False.elim (hn trivial)
    | heldCandidate => exact False.elim (hn trivial)

/-- The literal selected-gap debt includes prelaunch and is zero only
after the candidate reply has reached the owner. -/
def latchDebt (R : VFrame) (q : Nat) (g : Fin R.m) (s : GhostRing2 R) : Nat :=
  (tokens2 R (q+1) s g).hops

theorem latchDebt_start_le (R : VFrame) (q : Nat) (g : Fin R.m) (s : GhostRing2 R) :
    latchDebt R q g s ≤ 2*(R.len g)-1 := ShortGapCohortCut.token_hops_le _

theorem Locked10.delivered_latches {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g) (hd : DeliveredAt ((view R s).epoch g) q) : BothCandidate R s g := by
  have hc : ComparedAt ((view R s).epoch g) q := by
    cases he : (view R s).epoch g <;> simp only [he,DeliveredAt] at hd <;>
      simp only [ComparedAt] <;> omega
  constructor
  · obtain ⟨c,d,hl,hr,hv⟩ := h.lineage.coherent.outgoingValue g (by
      change DeliveredAt ((view R s).epoch g) (s.k g)
      rw [h.generations.1]; exact hd)
    change s.hist g (s.k g) = some c at hl
    change s.hist (next R g) (s.k g) = some d at hr
    rw [h.generations.1,h.left] at hl
    rw [h.generations.1,h.right] at hr
    cases hl; cases hr
    exact hv
  · classical
    simpa only [if_pos hc] using h.right_port

theorem latchDebt_positive (R : VFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (hn : ¬ BothCandidate R s g) : 0 < latchDebt R q g s := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact hn (h.delivered_latches (zero_token2_completed R q s h.lineage g hz))

private theorem sum_focus_cancel {n : Nat} (f g : Fin n → Nat) (i : Fin n)
    (ho : ∀ j, j ≠ i → f j = g j) :
    (List.ofFn f).sum + g i = (List.ofFn g).sum + f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht := ofFn_sum_eq (fun j : Fin n => f j.succ) (fun j => g j.succ)
        (fun j => ho j.succ (by intro h; have := congrArg Fin.val h; simp at this))
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      let j : Fin n := ⟨i.val-1,by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin n => f j.succ) (fun j => g j.succ) j (by
        intro k hk
        apply ho k.succ
        intro he
        rw [← hj] at he
        exact hk (Fin.succ_inj.mp he))
      have h0 := ho 0 (Ne.symm hi)
      rw [hj] at ht
      omega

/-- Other gaps' exact token stutter lets a total-debt row theorem yield
the selected latch's own one-hop decrease without a denial-only premise. -/
private theorem latch_drop_of_total (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (g : Fin R.m) (e : Vtx R) (hg : g = e.1)
    (hd : latentDebt2 R (q+1) (ghostStep2 R s e) + 1 = latentDebt2 R (q+1) s) :
    latchDebt R q g (ghostStep2 R s e) + 1 = latchDebt R q g s := by
  have hh := sum_focus_cancel
    (fun j => (tokens2 R (q+1) (ghostStep2 R s e) j).hops)
    (fun j => (tokens2 R (q+1) s j).hops) g (by
      intro j hj
      rw [other_gap_token_eq_lineage R (q+1) s hs e j (by simpa only [← hg] using hj)])
  change latentDebt2 R (q+1) (ghostStep2 R s e) + latchDebt R q g s =
    latentDebt2 R (q+1) s + latchDebt R q g (ghostStep2 R s e) at hh
  omega

private theorem locked_right_free {R : VFrame} {s : GhostRing2 R} {q : Nat} {g : Fin R.m}
    (h : Locked10 R s q g)
    (hc : (s.epoch g).cur = .idle ∨ ∃ c, (s.epoch g).cur = .outbound q c) :
    (s.cfg (rootV R (next R g))).ccwPort = some .free := by
  classical
  have hn : ¬ ComparedAt ((view R s).epoch g) q := by
    rcases hc with hi | ⟨c,hc⟩
    · have hh := (idle_prefix R s h.lineage g hi).2 q
      rw [h.generations.1] at hh
      exact fun hn => Nat.lt_irrefl q (hh.mp hn)
    · simp [view,prefixView,combinedView,hc,ComparedAt]
  simpa only [if_neg hn] using h.right_port

/-- The selected locked comparison has a free receiver and no JOIN,
so replacing the declaration by its reply consumes exactly one hop. -/
private theorem latch_comparison_drop (R : VFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (p : Fin (R.len g)) (hp : 0 < p.val) (hlast : p.val+1 = (R.len g))
    (c : Choice) (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty)) :
    latchDebt R q g (ghostStep2 R s ⟨g,p⟩) + 1 = latchDebt R q g s := by
  obtain ⟨cw,ccw,hr⟩ := h.root_choices.2
  have hf := locked_right_free h (Or.inr ⟨c,he⟩)
  rw [hr] at hf
  have hc : ccw = .free := Option.some.inj hf
  subst ccw
  have hl : s.cfg ⟨g,p⟩ = .interior (.decl c) := by simpa using hslots p hp
  have hx := boundary_comparison R s h.lineage g p hp hlast c .in0 cw hl hr
  have hrn : rn R ⟨g,p⟩ = rootV R (next R g) := rn_of_last R ⟨g,p⟩ (by change ¬ p.val+1 < (R.len g); omega)
  have hpost := boundary_token_replace R s g p hp hlast
    (.decl c) (.reply .in0) hslots (by rw [hrn,hl,hr]; rfl)
  have hp0 := tokenPos2_of_unique R s g p hp (.decl c) (by intro h; cases h) hslots
  have hp1 := tokenPos2_of_unique R (ghostStep2 R s ⟨g,p⟩) g p hp (.reply .in0)
    (by intro h; cases h) hpost
  have hk0 : (curView R s).k g = q := h.generations.1
  have hk1 : (curView R (ghostStep2 R s ⟨g,p⟩)).k g = q := (h.step ⟨g,p⟩).generations.1
  have he0 : (curView R s).epoch g = .outbound q c := he
  have he1 : (curView R (ghostStep2 R s ⟨g,p⟩)).epoch g = .returning q c .in0 := by
    simpa [curView,h.generations.1,resolveResp] using hx.1
  simp [latchDebt,tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hp0,hp1,ofPhase,p.isLt,
    (by omega : 1 ≤ p.val),(by omega : p.val ≤ (R.len g)-1),LitGapState.hops]
  omega

/-- Every literal edge is nonincreasing for the selected locked gap.
This uses local row laws, not the denial-only accounting domain. -/
theorem latchDebt_step_le (R : VFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (e : Vtx R) :
    latchDebt R q g (ghostStep2 R s e) ≤ latchDebt R q g s := by
  by_cases hg : g = e.1
  · rcases e with ⟨j,a⟩
    change g = j at hg
    subst j
    have hk := h.generations.1
    have ht := h.lineage.current g
    have hshape := current_token_shape R s h.lineage g
    cases he : (s.epoch g).cur with
    | idle => exact idle_gap_token_debt_le R (q+1) s ⟨g,a⟩ g he
    | delivered t c d =>
      unfold latchDebt
      rw [delivered_selected_token_eq R (q+1) s h.lineage ⟨g,a⟩ t c d he]
      exact Nat.le_refl _
    | outbound t c =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty) at hslots
      by_cases hap : a = p
      · subst a
        by_cases hn : p.val+1 < (R.len g)
        · have hd := latch_drop_of_total R s h.lineage q g ⟨g,p⟩ rfl
            (forwarding_lowers_latentDebt2 R q s h.lineage g c p hp hn hk he hslots)
          omega
        · have hlast : p.val+1 = (R.len g) := by have := p.isLt; omega
          have hd := latch_comparison_drop R s q g h p hp hlast c he hslots
          omega
      · unfold latchDebt
        rw [outbound_wrong_edge R (q+1) s h.lineage g a p q c hp hap he hslots]
        exact Nat.le_refl _
    | returning t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty) at hslots
      by_cases hap : a.val+1 = p.val
      · by_cases hp1 : p.val = 1
        · have ha : ⟨g,a⟩ = rootV R g := vtx_eq R _ _ rfl (by change a.val = 0; omega)
          rw [ha]
          have hd := latch_drop_of_total R s h.lineage q g (rootV R g) rfl
            (delivery_lowers_latentDebt2 R q s h.lineage g c d p hp1 hk he hslots)
          omega
        · have hp2 : 1 < p.val := by omega
          let p' : Fin (R.len g) := ⟨p.val-1,by have := p.isLt; omega⟩
          have hd := latch_drop_of_total R s h.lineage q g ⟨g,p'⟩ rfl
            (backward_lowers_latentDebt2 R q s h.lineage g c d p hp2 hk he hslots)
          have ha : a = p' := Fin.ext (by change a.val = p.val-1; omega)
          rw [ha]
          omega
      · unfold latchDebt
        rw [returning_wrong_edge R (q+1) s h.lineage g a p q c d hp hap he hslots]
        exact Nat.le_refl _
  · unfold latchDebt
    rw [other_gap_token_eq_lineage R (q+1) s h.lineage e g hg]
    exact Nat.le_refl _

private theorem latch_launch_drop (R : VFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (hi : (s.epoch g).cur = .idle) :
    latchDebt R q g (ghostStep2 R s (rootV R g)) + 1 = latchDebt R q g s := by
  obtain ⟨cw,ccw,hroot⟩ := h.root_choices.1
  have hs := h.lineage.idleSend g hi
  rw [hroot] at hs
  have hc : cw = .toSend := Option.some.inj hs
  subst cw
  by_cases hh : 1 < (R.len g)
  · exact prelaunch_token_debt_drop R q s h.lineage g .out1 ccw hroot hh h.generations.1 hi
  · have h1 : (R.len g) = 1 := by have := R.len_pos g; omega
    obtain ⟨dw,dd,hr⟩ := h.root_choices.2
    have hf := locked_right_free h (Or.inl hi)
    rw [hr] at hf
    have hd : dd = .free := Option.some.inj hf
    subst dd
    have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬ 0+1 < (R.len g); omega)
    have hraw : rawEpochs R (curView R s) (rootV R g) g = .delivered q .out1 .in0 := by
      rw [rawEpochs,if_pos rfl]
      change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
      rw [hroot,hrn,hr,h.generations.1]; rfl
    have hz := token_zero_of_raw_delivered R q s (rootV R g) g .out1 .in0 h.generations.1 hraw
    have hk0 : (curView R s).k g = q := h.generations.1
    have he0 : (curView R s).epoch g = .idle := hi
    change (tokens2 R (q+1) (ghostStep2 R s (rootV R g)) g).hops + 1 = _
    rw [hz]
    simp [latchDebt,tokens2,tokensOf',cohortToken,hk0,he0,h1,LitGapState.hops]

/-- One designated physical edge advances every nonzero selected debt. -/
theorem latchDebt_advancing_edge (R : VFrame) (s : GhostRing2 R) (q : Nat) (g : Fin R.m)
    (h : Locked10 R s q g) (hp : 0 < latchDebt R q g s) :
    ∃ e : Fin R.n, latchDebt R q g (ghostStep2 R s (edgeVtx R e)) + 1 = latchDebt R q g s := by
  have hk := h.generations.1
  have ht := h.lineage.current g
  have hshape := current_token_shape R s h.lineage g
  have hex : ∃ e : Vtx R, latchDebt R q g (ghostStep2 R s e) + 1 = latchDebt R q g s := by
    cases he : (s.epoch g).cur with
    | idle => exact ⟨rootV R g,latch_launch_drop R s q g h he⟩
    | delivered t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      have hk0 : (curView R s).k g = q := hk
      have he0 : (curView R s).epoch g = .delivered q c d := hq ▸ he
      simp [latchDebt,tokens2,tokensOf',cohortToken,hk0,he0,LitGapState.hops] at hp
    | outbound t c =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .decl c else .empty) at hslots
      by_cases hn : p.val+1 < (R.len g)
      · exact ⟨⟨g,p⟩,latch_drop_of_total R s h.lineage q g ⟨g,p⟩ rfl
          (forwarding_lowers_latentDebt2 R q s h.lineage g c p hp hn hk he hslots)⟩
      · exact ⟨⟨g,p⟩,latch_comparison_drop R s q g h p hp (by have := p.isLt; omega) c he hslots⟩
    | returning t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      change ∀ x : Fin (R.len g), 0 < x.val → s.cfg ⟨g,x⟩ = .interior (if x = p then .reply d else .empty) at hslots
      by_cases hp1 : p.val = 1
      · exact ⟨rootV R g,latch_drop_of_total R s h.lineage q g (rootV R g) rfl
          (delivery_lowers_latentDebt2 R q s h.lineage g c d p hp1 hk he hslots)⟩
      · let p' : Fin (R.len g) := ⟨p.val-1,by have := p.isLt; omega⟩
        exact ⟨⟨g,p'⟩,latch_drop_of_total R s h.lineage q g ⟨g,p'⟩ rfl
          (backward_lowers_latentDebt2 R q s h.lineage g c d p (by omega) hk he hslots)⟩
  obtain ⟨e,he⟩ := hex
  exact ⟨encode R e,by rw [edgeVtx_encode]; exact he⟩

structure RealizeCore (R : VFrame) where
  idx : Nat
  gap : Fin R.m
  state : GhostRing2 R

def RealizeInv (R : VFrame) (x : RealizeCore R) : Prop :=
  Locked10 R x.state x.idx x.gap ∧ ¬ BothCandidate R x.state x.gap

abbrev RealizeState (R : VFrame) := {x : RealizeCore R // RealizeInv R x}

noncomputable def realizeStep (R : VFrame) (s : RealizeState R) (e : Fin R.n) : StopNode (RealizeState R) := by
  classical
  let t := ghostStep2 R s.val.state (edgeVtx R e)
  exact if ht : BothCandidate R t s.val.gap then .success
    else .active ⟨⟨s.val.idx,s.val.gap,t⟩,s.property.1.step _,ht⟩

def realizePotential (R : VFrame) : StopNode (RealizeState R) → Nat
  | .active s => R.n * latchDebt R s.val.idx s.val.gap s.val.state
  | .success | .failure => 0

theorem realize_bellman (R : VFrame) : NatBellmanSuperSolution (realizeStep R) 1 (realizePotential R) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  have hle := latchDebt_step_le R s.val.state s.val.idx s.val.gap s.property.1
  obtain ⟨e,he⟩ := latchDebt_advancing_edge R s.val.state s.val.idx s.val.gap s.property.1
    (latchDebt_positive R s.val.state s.val.idx s.val.gap s.property.1 s.property.2)
  have ht := sum_strict (fun a => latchDebt R s.val.idx s.val.gap (ghostStep2 R s.val.state (edgeVtx R a)))
    (fun _ => latchDebt R s.val.idx s.val.gap s.val.state) e (fun a => hle _) (by omega)
  rw [ofFn_sum_const] at ht
  have hsum : (List.ofFn (fun a : Fin R.n => realizePotential R (realizeStep R s a))).sum ≤
      (List.ofFn (fun a : Fin R.n => R.n*latchDebt R s.val.idx s.val.gap
        (ghostStep2 R s.val.state (edgeVtx R a)))).sum := by
    apply ofFn_sum_le
    intro a
    unfold realizeStep
    dsimp only
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  rw [ofFn_sum_mul_left] at hsum
  have hb : 1 + (List.ofFn (fun a : Fin R.n =>
      latchDebt R s.val.idx s.val.gap (ghostStep2 R s.val.state (edgeVtx R a)))).sum ≤
      R.n*latchDebt R s.val.idx s.val.gap s.val.state := by omega
  have hm := Nat.mul_le_mul_left R.n hb
  rw [Nat.mul_add,Nat.mul_one] at hm
  change 1*R.n + _ ≤ R.n*(R.n*_)
  rw [Nat.one_mul]
  omega

theorem switch_potential_le (R : VFrame) (s : RealizeState R) (credit : Nat) :
    realizePotential R (.active s) ≤ credit + R.n*(2*hMax R-1) := by
  have h := Nat.mul_le_mul_left R.n (latchDebt_hMax_le R s.val.idx s.val.state s.val.gap)
  change R.n*latchDebt R s.val.idx s.val.gap s.val.state ≤ _ at h
  change R.n*latchDebt R s.val.idx s.val.gap s.val.state ≤ _
  omega

/-- Scan a fixed finite list in order, using only immutable payloads. -/
def findLockedPairs (R : VFrame) (s : GhostRing2 R) : List (Nat × Fin R.m) → Option (Nat × Fin R.m)
  | [] => none
  | p :: ps => if s.hist p.2 p.1 = some .out1 ∧ s.hist (next R p.2) p.1 = some .in0
      then some p else findLockedPairs R s ps

def lockedPairs (R : VFrame) (s : GhostRing2 R) : List (Nat × Fin R.m) :=
  (List.range (maxGen R s+1)).flatMap (fun q => (List.finRange R.m).map (fun g => (q,g)))

/-- Deterministic lexicographic search: generation first, gap second. -/
def firstLocked10 (R : VFrame) (s : GhostRing2 R) : Option (Nat × Fin R.m) :=
  findLockedPairs R s (lockedPairs R s)

private theorem findLockedPairs_sound (R : VFrame) (s : GhostRing2 R) (xs : List (Nat × Fin R.m))
    (p : Nat × Fin R.m) (h : findLockedPairs R s xs = some p) :
    s.hist p.2 p.1 = some .out1 ∧ s.hist (next R p.2) p.1 = some .in0 := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rw [findLockedPairs] at h
    split at h
    · rename_i ha
      cases h
      exact ha
    · exact ih h

private theorem findLockedPairs_complete (R : VFrame) (s : GhostRing2 R) (xs : List (Nat × Fin R.m))
    (h : ∃ p, p ∈ xs ∧ s.hist p.2 p.1 = some .out1 ∧ s.hist (next R p.2) p.1 = some .in0) :
    ∃ p, findLockedPairs R s xs = some p := by
  induction xs with
  | nil => obtain ⟨p,hp,_⟩ := h; cases hp
  | cons a xs ih =>
    rw [findLockedPairs]
    split
    · exact ⟨a,rfl⟩
    · rename_i hn
      apply ih
      obtain ⟨p,hp,hp'⟩ := h
      rcases List.mem_cons.mp hp with he | he
      · subst p; exact False.elim (hn hp')
      · exact ⟨p,he,hp'⟩

theorem firstLocked10_sound (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (q : Nat) (g : Fin R.m) (h : firstLocked10 R s = some (q,g)) : Locked10 R s q g :=
  ⟨hs,(findLockedPairs_sound R s (lockedPairs R s) (q,g) h).1,
    (findLockedPairs_sound R s (lockedPairs R s) (q,g) h).2⟩

theorem firstLocked10_complete (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) : ∃ p, firstLocked10 R s = some p := by
  obtain ⟨q,hq,g,hg⟩ := hv
  have hc : PeriodHIncidenceChoice.Candidate10 (ring R) (word2 R q s) g := hg
  have hl := candidate10_to_Locked10 R s hs q g hc
  apply findLockedPairs_complete
  refine ⟨(q,g),?_,hl.left,hl.right⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨g,List.mem_finRange g,rfl⟩

theorem realizeStep_success_iff (R : VFrame) (s : RealizeState R) (e : Fin R.n) :
    realizeStep R s e = .success ↔ BothCandidate R (ghostStep2 R s.val.state (edgeVtx R e)) s.val.gap := by
  classical
  unfold realizeStep
  dsimp only
  split <;> simp_all

/-- Select a lock after actual virtual success. The impossible none
branch is eliminated by finite-search completeness, never reseeded. -/
noncomputable def switchToRealize (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) : StopNode (RealizeState R) := by
  classical
  exact match he : firstLocked10 R s with
    | none => False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rw [he] at hp; cases hp)
    | some (q,g) => if hb : BothCandidate R s g then .success
      else .active ⟨⟨q,g,s⟩,firstLocked10_sound R s hs q g he,hb⟩

theorem switchToRealize_le (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) :
    realizePotential R (switchToRealize R s hs hv) ≤ R.n*(2*hMax R-1) := by
  classical
  unfold switchToRealize
  split
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul_left R.n (latchDebt_hMax_le R _ s _)



abbrev AccountState (R : VFrame) := (ghostRearmSpec R).RestartState

def accountGhost (R : VFrame) : AccountState R → GhostRing2 R
  | .round s => s.state
  | .reset s => s.state

theorem account_lineage (R : VFrame) (s : AccountState R) : Lineage2 R (accountGhost R s) := by
  cases s with
  | round s => exact s.base.lineage
  | reset s => exact s.dom.lineage

theorem serviceStep_success_iff (R : VFrame) (s : Service R) (e : Fin R.n) :
    serviceStep R s e = .succeed ↔ VirtualSuccess R 0 (ghostStep2 R s.state (edgeVtx R e)) := by
  classical
  change serviceStep R s e = .succeed ↔ VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e))
  unfold serviceStep
  dsimp only
  split <;> simp_all
  split <;> simp_all

theorem account_success_iff (R : VFrame) (s : AccountState R) (e : Fin R.n) :
    (ghostRearmSpec R).restartStep s e = .success ↔
      VirtualSuccess R 0 (ghostStep2 R (accountGhost R s) (edgeVtx R e)) := by
  cases s with
  | round s =>
    have hh := roundStep_success_iff R s e
    change BalancedFailureRestart.liftRoundOutcome (serviceEntry R s e) (roundStep R s e) = .success ↔ _
    cases he : roundStep R s e <;> simpa only [he,BalancedFailureRestart.liftRoundOutcome,reduceCtorEq,accountGhost,VirtualSuccess] using hh
  | reset s =>
    have hh := serviceStep_success_iff R s e
    change liftServiceOutcome (serviceStep R s e) = .success ↔ _
    cases he : serviceStep R s e <;> simpa only [he,liftServiceOutcome,reduceCtorEq,accountGhost,VirtualSuccess] using hh

inductive CandidateRunState (R : VFrame) where
  | account : AccountState R → CandidateRunState R
  | realize : RealizeState R → CandidateRunState R

def candidateGhost (R : VFrame) : CandidateRunState R → GhostRing2 R
  | .account s => accountGhost R s
  | .realize s => s.val.state

def embedRealize (R : VFrame) : StopNode (RealizeState R) → StopNode (CandidateRunState R)
  | .active s => .active (.realize s)
  | .success => .success
  | .failure => .failure

/-- The account virtual-success port switches to a selected lock in its
actual ghost child. No extra physical interaction is charged for the
mode switch, and success is exposed only after both candidate latches. -/
noncomputable def physicalCandidateStep (R : VFrame) (s : CandidateRunState R) (e : Fin R.n) :
    StopNode (CandidateRunState R) := by
  classical
  exact match s with
    | .realize x => embedRealize R (realizeStep R x e)
    | .account x => match he : (ghostRearmSpec R).restartStep x e with
      | .active y => .active (.account y)
      | .failure => False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
      | .success => embedRealize R (switchToRealize R (ghostStep2 R (accountGhost R x) (edgeVtx R e))
        (lineage2_step R _ (account_lineage R x) _) ((account_success_iff R x e).mp he))

/-- Every account state retains one full latch budget, while realize
states charge only the selected physical gap's remaining hops. -/
noncomputable def physicalCandidatePotential (R : VFrame) : StopNode (CandidateRunState R) → Nat
  | .active (.account s) => (ghostRearmSpec R).restartPotential (.active s) + R.n*(2*hMax R-1)
  | .active (.realize s) => realizePotential R (.active s)
  | .success | .failure => 0

theorem embedRealize_potential (R : VFrame) (x : StopNode (RealizeState R)) :
    physicalCandidatePotential R (embedRealize R x) = realizePotential R x := by cases x <;> rfl

/-- The reserved latch credit pays every switched success child. All
other account children retain that credit, so the uniform Bellman sum
is bounded by the accounting sum plus n times the latch budget. -/
theorem physicalCandidate_bellman (R : VFrame) :
    NatBellmanSuperSolution (physicalCandidateStep R) 1 (physicalCandidatePotential R) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  cases s with
  | realize x =>
    have h := (realize_bellman R).2.2 x
    change 1*R.n + (List.ofFn (fun e => physicalCandidatePotential R (embedRealize R (realizeStep R x e)))).sum ≤
      R.n * realizePotential R (.active x)
    simpa only [embedRealize_potential] using h
  | account x =>
    have h := (ghostRearm_bellman R).2.2 x
    have hpoint : ∀ e : Fin R.n, physicalCandidatePotential R (physicalCandidateStep R (.account x) e) ≤
        (ghostRearmSpec R).restartPotential ((ghostRearmSpec R).restartStep x e) + R.n*(2*hMax R-1) := by
      intro e
      unfold physicalCandidateStep
      dsimp only
      split
      · rename_i y he
        rw [he]
        exact Nat.le_refl _
      · rename_i he
        exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
      · rw [embedRealize_potential]
        exact Nat.le_trans (switchToRealize_le R _ _ _) (Nat.le_add_left _ _)
    have hsum := ofFn_sum_le _ _ hpoint
    rw [ofFn_sum_add,ofFn_sum_const] at hsum
    change 1*R.n + _ ≤ R.n*((ghostRearmSpec R).restartPotential (.active x)+R.n*(2*hMax R-1))
    rw [Nat.mul_add]
    omega

theorem switchToRealize_no_failure (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) : switchToRealize R s hs hv ≠ .failure := by
  classical
  unfold switchToRealize
  split
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split <;> intro h <;> cases h

theorem embedRealize_no_failure (R : VFrame) (x : StopNode (RealizeState R)) (hx : x ≠ .failure) :
    embedRealize R x ≠ .failure := by
  cases x with
  | active x => intro h; cases h
  | success => intro h; cases h
  | failure => exact False.elim (hx rfl)

theorem physicalCandidate_no_failure (R : VFrame) (s : CandidateRunState R) (e : Fin R.n) :
    physicalCandidateStep R s e ≠ .failure := by
  classical
  cases s with
  | realize x =>
    apply embedRealize_no_failure
    unfold realizeStep
    dsimp only
    split <;> intro h <;> cases h
  | account x =>
    unfold physicalCandidateStep
    dsimp only
    split
    · intro h; cases h
    · rename_i he
      exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
    · exact embedRealize_no_failure R _ (switchToRealize_no_failure R _ _ _)

theorem switchToRealize_success_sound (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) (h : switchToRealize R s hs hv = .success) : ∃ g, BothCandidate R s g := by
  classical
  unfold switchToRealize at h
  split at h
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split at h
    · rename_i q g he hb
      exact ⟨g,hb⟩
    · cases h

theorem physicalCandidate_success_sound (R : VFrame) (s : CandidateRunState R) (e : Fin R.n)
    (h : physicalCandidateStep R s e = .success) :
    ∃ g, BothCandidate R (ghostStep2 R (candidateGhost R s) (edgeVtx R e)) g := by
  classical
  have hemb : ∀ x : StopNode (RealizeState R), embedRealize R x = .success → x = .success := by
    intro x hx; cases x <;> first | rfl | cases hx
  cases s with
  | realize x =>
    exact ⟨x.val.gap,(realizeStep_success_iff R x e).mp (hemb _ h)⟩
  | account x =>
    unfold physicalCandidateStep at h
    dsimp only at h
    split at h
    · cases h
    · rename_i he
      exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
    ·
      exact switchToRealize_success_sound R _ _ _ (hemb _ h)

def physicalCandidateStart (R : VFrame) : CandidateRunState R := .account (.round (strictRoundStart R))
def physicalCandidateCleanStart (R : VFrame) : CandidateRunState R := .account (.reset (initialService R))

/-- Erasing the accounting mode yields exactly one literal interaction,
including the failure-to-service transition. -/
theorem account_step_erases (R : VFrame) (s t : AccountState R) (e : Fin R.n)
    (h : (ghostRearmSpec R).restartStep s e = .active t) :
    accountGhost R t = ghostStep2 R (accountGhost R s) (edgeVtx R e) := by
  classical
  cases s with
  | round s =>
    change BalancedFailureRestart.liftRoundOutcome (serviceEntry R s e) (roundStep R s e) = .active t at h
    cases he : roundStep R s e with
    | active y =>
      simp only [he,BalancedFailureRestart.liftRoundOutcome] at h
      cases h
      unfold roundStep at he
      dsimp only at he
      split at he
      · cases he
      · split at he
        · cases he; rfl
        · cases he
    | failure =>
      simp only [he,BalancedFailureRestart.liftRoundOutcome] at h
      cases h
      exact (serviceEntry_of_failure R s e he).2
    | success =>
      simp only [he,BalancedFailureRestart.liftRoundOutcome] at h
      cases h
  | reset s =>
    change liftServiceOutcome (serviceStep R s e) = .active t at h
    unfold serviceStep at h
    dsimp only at h
    split at h
    · cases h
    · split at h <;> cases h <;> rfl

theorem switchToRealize_active_state (R : VFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hv : VirtualSuccess R 0 s) (x : RealizeState R) (h : switchToRealize R s hs hv = .active x) :
    x.val.state = s := by
  classical
  unfold switchToRealize at h
  split at h
  · exact False.elim (by obtain ⟨p,hp⟩ := firstLocked10_complete R s hs hv; rename_i he; rw [he] at hp; cases hp)
  · split at h
    · cases h
    · cases h; rfl

theorem embedRealize_active_state (R : VFrame) (x : StopNode (RealizeState R))
    (y : CandidateRunState R) (h : embedRealize R x = .active y) :
    ∃ z, x = .active z ∧ y = .realize z := by
  cases x with
  | active z => cases h; exact ⟨z,rfl,rfl⟩
  | success => cases h
  | failure => cases h

/-- Neither entering service nor switching to realization inserts a
synthetic state update or an extra interaction. -/
theorem physicalCandidate_step_erases (R : VFrame) (s t : CandidateRunState R) (e : Fin R.n)
    (h : physicalCandidateStep R s e = .active t) :
    candidateGhost R t = ghostStep2 R (candidateGhost R s) (edgeVtx R e) := by
  classical
  cases s with
  | realize x =>
    obtain ⟨z,hz,rfl⟩ := embedRealize_active_state R _ _ h
    unfold realizeStep at hz
    dsimp only at hz
    split at hz
    · cases hz
    · cases hz; rfl
  | account x =>
    unfold physicalCandidateStep at h
    dsimp only at h
    split at h
    · rename_i y he
      cases h
      exact account_step_erases R x y e he
    · rename_i he
      exact False.elim ((ghostRearmSpec R).restartStep_ne_failure x e he)
    · obtain ⟨z,hz,rfl⟩ := embedRealize_active_state R _ _ h
      exact switchToRealize_active_state R _ _ _ z hz

theorem physicalCandidate_start_le (R : VFrame) :
    physicalCandidatePotential R (.active (physicalCandidateStart R)) ≤
      (R.n*R.m+2*R.n*R.n)+R.n*(2*hMax R-1) := by
  change (ghostRearmSpec R).restartPotential (.active (.round (strictRoundStart R))) + _ ≤ _
  rw [strictRoundStart_potential]
  exact Nat.le_refl _

theorem physicalCandidate_cleanStart_le (R : VFrame) :
    physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) ≤
      4*R.n*R.n+R.n*(2*hMax R-1) := by
  change (ghostRearmSpec R).restartPotential (.active (.reset (initialService R))) + _ ≤ _
  rw [initialService_potential]
  exact Nat.le_refl _

theorem physicalCandidate_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateStart R)) T ≤
      R.n^T*((R.n*R.m+2*R.n*R.n)+R.n*(2*hMax R-1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (physicalCandidateStart R)) T
  simp only [Nat.one_mul] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (physicalCandidate_start_le R))

theorem physicalCandidate_clean_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.n+R.n*(2*hMax R-1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (physicalCandidateCleanStart R)) T
  simp only [Nat.one_mul] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (physicalCandidate_cleanStart_le R))

theorem physicalCandidate_success_one_minus_inv_factor (R : VFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*((R.n*R.m+2*R.n*R.n)+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateStart R))
        (factor*((R.n*R.m+2*R.n*R.n)+R.n*(2*hMax R-1))) := by
  apply success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) _
    (physicalCandidate_truncatedCost_le R) factor
  have h : 0 < R.n*R.m := Nat.mul_pos (n_pos R) (by have := R.hm; omega)
  omega

theorem physicalCandidate_clean_success_one_minus_inv_factor (R : VFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.n+R.n*(2*hMax R-1))) := by
  apply success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) _
    (physicalCandidate_clean_truncatedCost_le R) factor
  have h : 0 < 4*R.n*R.n := Nat.mul_pos (Nat.mul_pos (by decide) (n_pos R)) (n_pos R)
  omega


/-! ## Variable-length end-to-end capstones

The strict start is round 1 with fresh Race roots and zero predecessor
debt. The original clean start must first service its fixed round-0 word.
Both use exactly one uniformly selected physical edge per charged step.
-/

theorem physicalCandidateVar_bellman (R : VFrame) :
    NatBellmanSuperSolution (physicalCandidateStep R) 1 (physicalCandidatePotential R) :=
  physicalCandidate_bellman R

theorem physicalCandidateVar_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateStart R)) T ≤
      R.n^T*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) :=
  physicalCandidate_truncatedCost_le R T

theorem physicalCandidateVar_clean_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.n+R.n*(2*hMax R-1)) :=
  physicalCandidate_clean_truncatedCost_le R T

/-- In counting form, success probability at factor times the strict
budget is at least 1-1/factor for every positive integer factor. -/
theorem physicalCandidateVar_success_one_minus_inv_factor (R : VFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateStart R))
        (factor*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) :=
  physicalCandidate_success_one_minus_inv_factor R factor

theorem physicalCandidateVar_clean_success_one_minus_inv_factor (R : VFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.n+R.n*(2*hMax R-1))) :=
  physicalCandidate_clean_success_one_minus_inv_factor R factor

/-- Erasing every sidecar yields the unchanged literal row and JOIN. -/
theorem physicalCandidateVar_step_erases (R : VFrame) (s t : CandidateRunState R) (e : Fin R.n)
    (h : physicalCandidateStep R s e = .active t) :
    (candidateGhost R t).cfg = ringStepU R (candidateGhost R s).cfg (edgeVtx R e) := by
  rw [physicalCandidate_step_erases R s t e h]
  exact ghostStep2_physical R _ _

theorem success_sound (R : VFrame) (s : CandidateRunState R) (e : Fin R.n)
    (h : physicalCandidateStep R s e = .success) :
    ∃ g, (ringStepU R (candidateGhost R s).cfg (edgeVtx R e) (rootV R g)).cwPort = some .heldCandidate ∧
      (ringStepU R (candidateGhost R s).cfg (edgeVtx R e) (rootV R (next R g))).ccwPort = some .heldCandidate :=
  physicalCandidate_success_sound R s e h

theorem no_failure (R : VFrame) (s : CandidateRunState R) (e : Fin R.n) :
    physicalCandidateStep R s e ≠ .failure := physicalCandidate_no_failure R s e

/-- A concrete unequal-length frame includes both a direct root edge
and a gap with an interior transport site. -/
def unequalExample : VFrame where
  m := 2
  n := 3
  len g := g.val+1
  hm := by decide
  len_pos g := Nat.zero_lt_succ _
  total := by decide
  b := .out1
  hb := Or.inl rfl

theorem unequalExample_lengths :
    unequalExample.len ⟨0,by decide⟩ = 1 ∧ unequalExample.len ⟨1,by decide⟩ = 2 := by decide

theorem unequalExample_budgets :
    unequalExample.n*unequalExample.m+2*unequalExample.n*unequalExample.n+
        unequalExample.n*(2*hMax unequalExample-1) = 33 ∧
      4*unequalExample.n*unequalExample.n+unequalExample.n*(2*hMax unequalExample-1) = 45 := by decide

#print axioms sum_two_len_sub_one
#print axioms gap_noninterference
#print axioms encode_rn
#print axioms lineage2_step
#print axioms wordOf2_step
#print axioms latentDebt_total_var_le
#print axioms latentDebt2_step_le
#print axioms advancing_edge_lowers_latentDebt2
#print axioms genPipelined2_childSum
#print axioms genPipelined2_localBalance
#print axioms potential2_le_cut_budget
#print axioms cut_reserveDebt_bellman_var
#print axioms round_bellman
#print axioms round_balance
#print axioms service_exit
#print axioms service_bellman
#print axioms ghostRearm_bellman
#print axioms composed_truncatedCost_le
#print axioms strictStart_lineage
#print axioms strictRoundStart_potential
#print axioms cleanStart_not_active_round
#print axioms cleanStart_truncatedCost_le
#print axioms firstLocked10_complete
#print axioms latchDebt_step_le
#print axioms latchDebt_advancing_edge
#print axioms realize_bellman
#print axioms switch_potential_le
#print axioms physicalCandidateVar_bellman
#print axioms physicalCandidateVar_step_erases
#print axioms success_sound
#print axioms no_failure
#print axioms physicalCandidateVar_truncatedCost_le
#print axioms physicalCandidateVar_clean_truncatedCost_le
#print axioms physicalCandidateVar_success_one_minus_inv_factor
#print axioms physicalCandidateVar_clean_success_one_minus_inv_factor
#print axioms unequalExample_budgets

end ShortGapGhostVarLength
