import Leader.Wu.ShortGap.LiteralRingRows
import Leader.Wu.ShortGap.CandidatePersistence
import Leader.Wu.ShortGap.PipelinedRearm

/-!
# Owner-round slices: projection and a literal/abstract clock obstruction

Stage 1, uniform gap length, old cohort at a fixed base with denial-only
receipts. The physical step is UNFROZEN. Counters are proof bookkeeping and
increment exactly at a post-row JOIN. No historical word is added.

The requested exact simulation with `multiLocalStep` is false: its compare
step produces `denyLeft h`, whereas the literal compare already places the
reply at `h-1` (and delivers immediately for `h=1`). The counterexample below
starts with two clean, equal-base roots at round q, stays in the slice, and
uses no dirty rows, candidates, duplicate tokens, or cut exit.

`Coherent` states the receipt/owner-lineage facts needed to read the join mask.
Its separate second-round barrier is an explicit UNPROVED global invariant,
not a consequence asserted here of adjacent skew. Closure of this coherence
predicate and a repaired abstract transport simulation remain OPEN. The
negative simulation theorem does not establish a Bellman pullback.
-/

namespace ShortGapOwnerRoundSlice
open ShortGapLiteralGapRows ShortGapLiteralRingRows
open ShortGapDenialTransport ShortGapTwoDenialJoin ShortGapJoinedIncidenceBalance
set_option autoImplicit false

abbrev rootV (R : RFrame) (i : Fin R.m) : Vtx R := (i, ⟨0, R.hh⟩)

/-- Flattening uses the existing ring encoding, with no extra scheduler edges. -/
def encode (R : RFrame) (v : Vtx R) : Fin R.n := encE R v.1 v.2

theorem encode_injective (R : RFrame) : Function.Injective (encode R) := by
  intro v w he
  have h := congrArg (edgeVtx R) he
  simpa only [encode, edgeVtx_encE] using h

def layout (R : RFrame) : GapLayout R.n R.h R.m where
  hpos := R.hh
  edgeAt g a := encode R (g, a)
  edgeAt_injective g a g' a' h := by
    have he := encode_injective R h
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem ring (R : RFrame) : DirectedRing R.m := ⟨by have := R.hm; omega⟩

def placement (R : RFrame) : PeriodHIncidenceChoice.Placement R.n R.m where
  physicalRing := ⟨R.n_pos⟩
  root i := encode R (rootV R i)
  root_injective := by
    intro i j he
    exact congrArg Prod.fst (encode_injective R he)

/-- The encoding identifies actual neighbouring vertices with the placement's
physical ring; this rules out an abstract relabelling of boundary edges. -/
theorem encode_rn (R : RFrame) (v : Vtx R) :
    encode R (rn R v) = (placement R).physicalRing.rightNeighbor (encode R v) := by
  apply Fin.ext
  change (encode R (rn R v)).val = ((encode R v).val + 1) % R.n
  by_cases hl : v.2.val + 1 < R.h
  · rw [rn_of_lt R v hl]
    have hb := (encE R v.1 ⟨v.2.val + 1, hl⟩).isLt
    change R.h * v.1.val + (v.2.val + 1) = (R.h * v.1.val + v.2.val + 1) % R.n
    rw [Nat.mod_eq_of_lt (by simpa [encE, Nat.add_assoc] using hb)]
    omega
  · have ha : v.2.val + 1 = R.h := by have := v.2.isLt; omega
    rw [rn_of_last R v hl]
    have he : R.h * v.1.val + v.2.val + 1 = R.h * (v.1.val + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    change R.h * (next R v.1).val + 0 = (R.h * v.1.val + v.2.val + 1) % R.n
    rw [he, next_val]
    by_cases hg : v.1.val + 1 = R.m
    · simp [hg, RFrame.n, Nat.mul_comm]
    · have hb := (encE R (next R v.1) ⟨0, R.hh⟩).isLt
      have hb' : R.h * (v.1.val + 1) < R.n := by
        simpa [encE, next_val, hg] using hb
      simp [hg, Nat.mod_eq_of_lt hb']

/-- Both endpoints are first rewritten by the actual pair table. -/
def rawAt (R : RFrame) (cfg : Vtx R → Agent) (e w : Vtx R) : Agent :=
  if w = e then (row (cfg e) (cfg (rn R e))).1
  else if w = rn R e then (row (cfg e) (cfg (rn R e))).2
  else cfg w

def incident (R : RFrame) (e w : Vtx R) : Prop := w = e ∨ w = rn R e
instance (R : RFrame) (e w : Vtx R) : Decidable (incident R e w) :=
  inferInstanceAs (Decidable (w = e ∨ w = rn R e))

/-- A raw root with both denial ports is exactly a JOIN event. -/
def joinReady : Agent → Bool
  | .root _ .heldDenial .heldDenial => true
  | _ => false

/-- Factor JOIN and the counter increment through one common test. -/
def joinTick (a : Agent) (k : Nat) : Agent × Nat :=
  (ShortGapLiteralRingRows.joinA a, k + if joinReady a then 1 else 0)

theorem joinReady_iff (a : Agent) :
    joinReady a = true ↔ ∃ c, a = .root c .heldDenial .heldDenial := by
  cases a with
  | interior s => simp [joinReady]
  | root c cw ccw => cases cw <;> cases ccw <;> simp [joinReady]

/-- Radius-one pair update followed by JOIN, with no freeze guard. -/
def ringStepU (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R) : Vtx R → Agent :=
  fun w => if incident R e w then (joinTick (rawAt R cfg e w) 0).1 else cfg w

structure SliceState (R : RFrame) where
  cfg : Vtx R → Agent
  k : Fin R.m → Nat

/-- The event is read from the raw output at an incident physical root. -/
def fires (R : RFrame) (s : SliceState R) (e : Vtx R) (i : Fin R.m) : Bool :=
  decide (incident R e (rootV R i)) && joinReady (rawAt R s.cfg e (rootV R i))

def liftedStep (R : RFrame) (s : SliceState R) (e : Vtx R) : SliceState R where
  cfg := ringStepU R s.cfg e
  k i := s.k i + if fires R s e i then 1 else 0

def Slice (R : RFrame) (q : Nat) (s : SliceState R) : Prop :=
  ∀ i, s.k i = q ∨ s.k i = q + 1

/-- Exact characterization: this raw interaction supplies both denials. -/
theorem fires_iff (R : RFrame) (s : SliceState R) (e : Vtx R) (i : Fin R.m) :
    fires R s e i = true ↔ incident R e (rootV R i) ∧
      ∃ c, rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial := by
  simp [fires, joinReady_iff]

/-- Erasing the lifted counters recovers exactly the unfrozen physical step. -/
theorem liftedStep_erases (R : RFrame) (s : SliceState R) (e : Vtx R) :
    (liftedStep R s e).cfg = ringStepU R s.cfg e := rfl

/-- At each incident root, both the physical output and the counter are the
same `joinTick` result. For h=1 this applies to both root endpoints. -/
theorem liftedStep_root_tick (R : RFrame) (s : SliceState R) (e : Vtx R)
    (i : Fin R.m) (hi : incident R e (rootV R i)) :
    ((liftedStep R s e).cfg (rootV R i), (liftedStep R s e).k i) =
      joinTick (rawAt R s.cfg e (rootV R i)) (s.k i) := by
  simp [liftedStep, ringStepU, fires, hi, joinTick]

/-- No outer freeze or global normalization is hidden in `ringStepU`. -/
theorem ringStepU_pair (R : RFrame) (cfg : Vtx R → Agent) (e w : Vtx R) :
    ringStepU R cfg e w =
      if w = e then ShortGapLiteralRingRows.joinA (row (cfg e) (cfg (rn R e))).1
      else if w = rn R e then ShortGapLiteralRingRows.joinA (row (cfg e) (cfg (rn R e))).2
      else cfg w := by
  by_cases hl : w = e <;> by_cases hr : w = rn R e <;>
    simp [ringStepU, incident, rawAt, joinTick, hl, hr, rn_ne_self R e]

/-- An old-cohort K1 supplies the second denial and JOINs to Race;
`resolveResp` is semantically the identity on the old base. -/
theorem old_K1_join (R : RFrame) (q : Nat) :
    joinTick (row (.interior (.decl R.b)) (.root R.b .heldDenial .free)).2 q =
      (.root .race .toSend .free, q + 1) := by
  rw [row_K1]
  rfl

/-- V1 also preserves the old choice before the post-row JOIN. -/
theorem old_V1_join (R : RFrame) (q : Nat) :
    joinTick (row (.root R.b .waiting .heldDenial) (.interior (.reply R.b))).1 q =
      (.root .race .toSend .free, q + 1) := by
  rw [row_V1]
  rfl

/-- K2 really can resolve the current word and immediately erase it in JOIN.
At round q+1 this is a cut exit, not a same-cut incidence simulation. -/
theorem current_K2_resolve_join (q : Nat) :
    (row (.interior (.decl .in0)) (.root .race .heldDenial .free)).2 =
      .root .in0 .heldDenial .heldDenial ∧
    joinTick (row (.interior (.decl .in0)) (.root .race .heldDenial .free)).2 (q + 1) =
      (.root .race .toSend .free, q + 2) := by
  constructor <;> rfl

/-- The direct uniform row may perform two JOINs simultaneously. -/
theorem direct_two_joins (R : RFrame) (q r : Nat) :
    let out := row (.root R.b .toSend .heldDenial) (.root R.b .heldDenial .free)
    joinTick out.1 q = (.root .race .toSend .free, q + 1) ∧
    joinTick out.2 r = (.root .race .toSend .free, r + 1) := by
  dsimp only
  rw [row_P1]
  exact ⟨rfl, rfl⟩

/-- No root can advance by more than one in one interaction. -/
theorem counter_step (R : RFrame) (s : SliceState R) (e : Vtx R) (i : Fin R.m) :
    (liftedStep R s e).k i = s.k i ∨ (liftedStep R s e).k i = s.k i + 1 := by
  simp only [liftedStep]
  cases fires R s e i <;> simp

/-- A slice exit is exactly a JOIN by an already advanced root. -/
theorem slice_preserved (R : RFrame) (q : Nat) (s : SliceState R)
    (hs : Slice R q s) (e : Vtx R) :
    ¬ Slice R q (liftedStep R s e) ↔
      ∃ i, s.k i = q + 1 ∧ fires R s e i = true ∧
        (liftedStep R s e).k i = q + 2 := by
  classical
  constructor
  · intro hn
    have hex : ∃ i, ¬ ((liftedStep R s e).k i = q ∨
        (liftedStep R s e).k i = q + 1) := by
      exact Classical.byContradiction (fun hh => hn (fun i =>
        Classical.byContradiction (fun hi => hh ⟨i, hi⟩)))
    obtain ⟨i, hi⟩ := hex
    have hsi := hs i
    cases hf : fires R s e i with
    | false =>
      have he : (liftedStep R s e).k i = s.k i := by simp [liftedStep, hf]
      exact False.elim (hi (he ▸ hsi))
    | true =>
      have he : (liftedStep R s e).k i = s.k i + 1 := by simp [liftedStep, hf]
      have hk : s.k i = q + 1 := by rw [he] at hi; omega
      exact ⟨i, hk, hf, by rw [he, hk]⟩
  · rintro ⟨i, _, _, hi⟩ h
    have := h i
    omega

/-- This is the precise global barrier needed to prohibit early cut exits.
It is NOT inferred from adjacent skew: it must be established by a lineage
or reachability argument in a subsequent layer. -/
def SecondRoundBarrier (R : RFrame) (q : Nat) (s : SliceState R) : Prop :=
  (∃ j, s.k j = q) → ∀ e i, s.k i = q + 1 →
    incident R e (rootV R i) →
    ∀ c, rawAt R s.cfg e (rootV R i) ≠ .root c .heldDenial .heldDenial

/-- Only the old, uniform cohort is decoded by this shape relation. The
receiver may already have JOINed; its ccw port is not a permanent history bit. -/
def PhysicalGapForm (R : RFrame) (cfg : Vtx R → Agent) (g : Fin R.m)
    (p : Phase) : Prop :=
  PhaseOk (F0 R) p ∧ (cfg (rootV R g)).cwPort = some (cwOf p) ∧
    ∀ a : Fin R.h, 0 < a.val → cfg (g, a) = slotAgent R p a.val

/-- Ports distinguish idle/delivered/mobile; the occupied slot distinguishes
both mobile directions and their positions. -/
theorem physicalGapForm_unique (R : RFrame) (cfg : Vtx R → Agent) (g : Fin R.m)
    (p p' : Phase) (hp : PhysicalGapForm R cfg g p)
    (hp' : PhysicalGapForm R cfg g p') : p = p' := by
  obtain ⟨hok, hcw, hslots⟩ := hp
  obtain ⟨hok', hcw', hslots'⟩ := hp'
  have hc : cwOf p = cwOf p' := Option.some.inj (hcw.symm.trans hcw')
  cases p <;> cases p' <;> simp only [cwOf] at hc <;> try cases hc
  all_goals try rfl
  all_goals
    rename_i j l
    have hj := hok.2
    have hj0 := hok.1
    have he := (hslots ⟨j, hj⟩ (show 0 < j from hj0)).symm.trans (hslots' ⟨j, hj⟩ (show 0 < j from hj0))
    by_cases heq : j = l <;> simp [slotAgent, heq] at he
    all_goals subst l; rfl

open Classical in
/-- Total fallback outside the clean domain; `decode_of_form` proves that
this fallback is never used on any permitted old gap. -/
noncomputable def decode (R : RFrame) (cfg : Vtx R → Agent) (g : Fin R.m) : Phase :=
  if hp : ∃ p, PhysicalGapForm R cfg g p then hp.choose else .prelaunch

theorem decode_of_form (R : RFrame) (cfg : Vtx R → Agent) (g : Fin R.m)
    (p : Phase) (hp : PhysicalGapForm R cfg g p) : decode R cfg g = p := by
  classical
  have hex : ∃ p, PhysicalGapForm R cfg g p := ⟨p, hp⟩
  rw [decode, dif_pos hex]
  exact physicalGapForm_unique R cfg g _ _ hex.choose_spec hp

/-- Preserve physical positions when reading the abstract denial alphabet.
The fallback branches concern malformed positions only. -/
def phaseToken (R : RFrame) : Phase → GapDenialState R.h
  | .prelaunch => .declareRight 0 R.hh
  | .declAt j => if hj : j < R.h then .declareRight j hj else .denyLeft 0 (Nat.zero_le _)
  | .replyAt j => if hj : j ≤ R.h then .denyLeft j hj else .denyLeft 0 (Nat.zero_le _)
  | .delivered => .denyLeft 0 (Nat.zero_le _)

/-- The owner's round labels the untagged carrier. A later owner's traffic
is hidden, since its old outgoing service was already delivered. -/
noncomputable def tokens (R : RFrame) (q : Nat) (s : SliceState R) :
    Fin R.m → GapDenialState R.h := fun g =>
  if s.k g = q then phaseToken R (decode R s.cfg g) else .denyLeft 0 (Nat.zero_le _)

def abstractChoice : Agent → PeriodHIncidenceChoice.Choice
  | .root .out1 _ _ => .out1
  | .root .in0 _ _ => .in0
  | _ => .race

def word (R : RFrame) (q : Nat) (s : SliceState R) : PeriodHIncidenceChoice.Configuration R.m :=
  fun i => if s.k i = q + 1 then abstractChoice (s.cfg (rootV R i)) else .race

noncomputable def pi (R : RFrame) (q : Nat) (s : SliceState R) :
    PeriodHIncidenceChoice.Configuration R.m × (Fin R.m → GapDenialState R.h) :=
  (word R q s, tokens R q s)

/-- Explicit coherence obligations, not a carried simulation equality.
The incoming-receipt clauses state the old cohort's causal receipt history;
normalization then derives the joined-mask equivalence. The second-round
barrier is carried openly, and its reachability proof remains outstanding. -/
structure Coherent (R : RFrame) (q : Nat) (s : SliceState R) : Prop where
  roots : ∀ i, ∃ c cw ccw, s.cfg (rootV R i) = .root c cw ccw
  normalized : ∀ i, ShortGapLiteralRingRows.joinA (s.cfg (rootV R i)) = s.cfg (rootV R i)
  oldBase : ∀ i, s.k i = q → (s.cfg (rootV R i)).choice = some R.b
  oldGap : ∀ i, s.k i = q → ∃ p, PhysicalGapForm R s.cfg i p
  oldIncoming : ∀ i, s.k i = q → (s.cfg (rootV R i)).ccwPort =
    some (if isDenying (tokens R q s ((ring R).leftNeighbor i)) then .heldDenial else .free)
  advancedIncoming : ∀ i, s.k i = q + 1 →
    isDenying (tokens R q s ((ring R).leftNeighbor i)) = true
  secondBarrier : SecondRoundBarrier R q s

/-- The requested within-band statement under the explicitly isolated barrier. -/
theorem slice_preserved_of_coherent (R : RFrame) (q : Nat) (s : SliceState R)
    (hs : Slice R q s) (hc : Coherent R q s) (hold : ∃ i, s.k i = q) (e : Vtx R) :
    Slice R q (liftedStep R s e) := by
  classical
  apply Classical.byContradiction
  intro hn
  obtain ⟨i, hi, hf, _⟩ := (slice_preserved R q s hs e).1 hn
  obtain ⟨he, c, hr⟩ := (fires_iff R s e i).1 hf
  exact hc.secondBarrier hold e i hi he c hr

/-- Every old phase is unique; the projection agrees with every valid
physical reading, and every advanced owner projects to a discharged gap. -/
theorem pi_wellDefined (R : RFrame) (q : Nat) (s : SliceState R)
    (hs : Slice R q s) (hc : Coherent R q s) :
    ∀ g, (s.k g = q → ∃ p, PhysicalGapForm R s.cfg g p ∧
      (∀ p', PhysicalGapForm R s.cfg g p' → p' = p) ∧
      (pi R q s).2 g = phaseToken R p) ∧
    (s.k g = q + 1 → (pi R q s).2 g = .denyLeft 0 (Nat.zero_le _)) := by
  intro g
  have _ := hs g
  constructor
  · intro hk
    obtain ⟨p, hp⟩ := hc.oldGap g hk
    refine ⟨p, hp, fun p' hp' => physicalGapForm_unique R s.cfg g p' p hp' hp, ?_⟩
    simp [pi, tokens, hk, decode_of_form R s.cfg g p hp]
  · intro hk
    simp [pi, tokens, hk]

private theorem phaseToken_discharged (R : RFrame) (p : Phase)
    (hp : PhaseOk (F0 R) p) : isDischarged (phaseToken R p) = true ↔ p = .delivered := by
  cases p with
  | prelaunch => simp [phaseToken, isDischarged]
  | delivered => simp [phaseToken, isDischarged]
  | declAt j => simp [phaseToken, hp.2, isDischarged]
  | replyAt j =>
    have hj0 := hp.1
    have hjh := hp.2
    cases j <;> simp_all [phaseToken, isDischarged, Nat.le_of_lt hjh]

/-- The joined mask is derived from the decoded old receipts and normalized
physical ports, not supplied as a field of `Coherent`. -/
theorem joined_iff_k (R : RFrame) (q : Nat) (s : SliceState R)
    (hs : Slice R q s) (hc : Coherent R q s) (i : Fin R.m) :
    rearmedOf (ring R) (tokens R q s) i = true ↔ s.k i = q + 1 := by
  constructor
  · intro hj
    rcases hs i with hi | hi
    · obtain ⟨p, hp⟩ := hc.oldGap i hi
      have ht : tokens R q s i = phaseToken R p := by
        simp [tokens, hi, decode_of_form R s.cfg i p hp]
      have hboth : isDischarged (phaseToken R p) = true ∧
          isDenying (tokens R q s ((ring R).leftNeighbor i)) = true := by
        simpa [rearmedOf, rightReceiptOf, leftReceiptOf, ht] using hj
      have hpd := (phaseToken_discharged R p hp.1).1 hboth.1
      have hw := hp.2.1
      have hz := hc.oldIncoming i hi
      rw [hpd] at hw
      rw [hboth.2] at hz
      obtain ⟨c, cw, ccw, hr⟩ := hc.roots i
      rw [hr] at hw hz
      simp only [Agent.cwPort, Agent.ccwPort, cwOf, if_true, Option.some.injEq] at hw hz
      subst cw; subst ccw
      have hn := hc.normalized i
      rw [hr] at hn
      simp [ShortGapLiteralRingRows.joinA] at hn
    · exact hi
  · intro hi
    have ht : tokens R q s i = .denyLeft 0 (Nat.zero_le _) := by
      simp [tokens, hi]
    simp [rearmedOf, rightReceiptOf, leftReceiptOf, ht, isDischarged, hc.advancedIncoming i hi]

/-! The specified transport has one extra boundary interaction. -/

/-- Already at `h=1`, the two clocks disagree at the compare boundary. -/
theorem direct_phase_clock_mismatch (R : RFrame) (hh : R.h = 1) :
    phaseToken R (nextPhase (F0 R) .prelaunch ⟨0, R.hh⟩) ≠
      GapDenialState.advance (phaseToken R .prelaunch) := by
  simp [nextPhase, phaseToken, hh, GapDenialState.advance]

/-- An explicit clean witness; both frozen bases would work. -/
abbrev witnessFrame : RFrame := ⟨2, 1, by decide, by decide, .in0, Or.inr rfl⟩

/-- The witness is a normal uniform initial state, with no prior JOINs. -/
def witnessStart (q : Nat) : SliceState witnessFrame where
  cfg _ := .root .in0 .toSend .free
  k _ := q

def witnessAfter (q : Nat) : SliceState witnessFrame where
  cfg v := if v.1 = 0 then .root .in0 .heldDenial .free
    else .root .in0 .toSend .heldDenial
  k _ := q

private theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 := by omega
  exact h.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

theorem witness_start_form (q : Nat) (g : Fin witnessFrame.m) :
    PhysicalGapForm witnessFrame (witnessStart q).cfg g .prelaunch := by
  refine ⟨trivial, rfl, ?_⟩
  intro a ha
  have hh : a.val < 1 := a.isLt
  omega

theorem witness_start_tokens (q : Nat) (g : Fin witnessFrame.m) :
    tokens witnessFrame q (witnessStart q) g = .declareRight 0 (by decide) := by
  rw [tokens, if_pos (show (witnessStart q).k g = q from rfl),
    decode_of_form _ _ g _ (witness_start_form q g)]
  rfl

theorem witness_start_slice (q : Nat) : Slice witnessFrame q (witnessStart q) :=
  fun _ => Or.inl rfl

/-- The mismatch satisfies every stated coherence hypothesis, including the
isolated second-round barrier (vacuously: all roots are still old). -/
theorem witness_start_coherent (q : Nat) : Coherent witnessFrame q (witnessStart q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨.in0, .toSend, .free, rfl⟩
  · intro i; rfl
  · intro i _; rfl
  · intro i _; exact ⟨.prelaunch, witness_start_form q i⟩
  · intro i _
    rw [witness_start_tokens]
    rfl
  · intro i hi
    change q = q + 1 at hi
    omega
  · intro _ e i hi
    change q = q + 1 at hi
    omega

/-- The literal P1 row writes both receipts in one interaction, without
joining either endpoint in this initial two-root configuration. -/
theorem witness_step (q : Nat) :
    liftedStep witnessFrame (witnessStart q) (rootV witnessFrame 0) = witnessAfter q := by
  have hcfg : ringStepU witnessFrame (witnessStart q).cfg (rootV witnessFrame 0) =
      (witnessAfter q).cfg := by
    funext v
    obtain ⟨i, a⟩ := v
    have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
    subst a
    rcases fin_two_cases i with rfl | rfl <;>
      simp [ringStepU, incident, rawAt, joinTick, witnessStart, witnessAfter,
        rn, next, witnessFrame, row, resolveInit, resolveResp, resCw, resCcw,
        res, Verdict.cw, Verdict.ccw, ShortGapLiteralRingRows.joinA]
  have hk : ∀ i, (liftedStep witnessFrame (witnessStart q) (rootV witnessFrame 0)).k i = q := by
    intro i
    rcases fin_two_cases i with rfl | rfl <;>
      simp [liftedStep, fires, incident, rawAt, witnessStart,
        rn, next, witnessFrame, row, resolveInit, resolveResp, resCw, resCcw,
        res, Verdict.cw, Verdict.ccw, joinReady]
  exact (congrArg (fun cfg => SliceState.mk cfg
    (liftedStep witnessFrame (witnessStart q) (rootV witnessFrame 0)).k) hcfg).trans
      (congrArg (SliceState.mk (witnessAfter q).cfg) (funext hk))

theorem witness_after_form_zero (q : Nat) :
    PhysicalGapForm witnessFrame (witnessAfter q).cfg 0 .delivered := by
  refine ⟨trivial, ?_, ?_⟩
  · simp [witnessAfter, Agent.cwPort, cwOf]
  · intro a ha
    have hh : a.val < 1 := a.isLt
    omega

theorem witness_after_form_one (q : Nat) :
    PhysicalGapForm witnessFrame (witnessAfter q).cfg 1 .prelaunch := by
  refine ⟨trivial, ?_, ?_⟩
  · simp [witnessAfter, Agent.cwPort, cwOf]
  · intro a ha
    have hh : a.val < 1 := a.isLt
    omega

theorem witness_after_tokens (q : Nat) (g : Fin witnessFrame.m) :
    tokens witnessFrame q (witnessAfter q) g =
      if g = 0 then .denyLeft 0 (by decide) else .declareRight 0 (by decide) := by
  rcases fin_two_cases g with rfl | rfl
  · rw [tokens, if_pos (show (witnessAfter q).k 0 = q from rfl),
      decode_of_form _ _ _ _ (witness_after_form_zero q)]
    simp [phaseToken]
  · rw [tokens, if_pos (show (witnessAfter q).k 1 = q from rfl),
      decode_of_form _ _ _ _ (witness_after_form_one q)]
    simp [phaseToken]

/-- Both pre- and post-states stay in the same cut. This mismatch cannot be
explained away as a q+1-to-q+2 exit. -/
theorem witness_stays (q : Nat) :
    Slice witnessFrame q (liftedStep witnessFrame (witnessStart q) (rootV witnessFrame 0)) := by
  rw [witness_step]
  exact fun _ => Or.inl rfl

/-- The post-state also has the expected old-cohort receipt coherence. -/
theorem witness_after_coherent (q : Nat) : Coherent witnessFrame q (witnessAfter q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases fin_two_cases i with rfl | rfl
    · exact ⟨.in0, .heldDenial, .free, by simp [witnessAfter]⟩
    · exact ⟨.in0, .toSend, .heldDenial, by simp [witnessAfter]⟩
  · intro i
    rcases fin_two_cases i with rfl | rfl <;> simp [witnessAfter, ShortGapLiteralRingRows.joinA]
  · intro i _
    rcases fin_two_cases i with rfl | rfl <;> simp [witnessAfter, Agent.choice]
  · intro i _
    rcases fin_two_cases i with rfl | rfl
    · exact ⟨.delivered, witness_after_form_zero q⟩
    · exact ⟨.prelaunch, witness_after_form_one q⟩
  · intro i _
    rw [witness_after_tokens]
    rcases fin_two_cases i with rfl | rfl <;>
      simp [witnessAfter, Agent.ccwPort, DirectedRing.leftNeighbor, witnessFrame, isDenying]
  · intro i hi
    change q = q + 1 at hi
    omega
  · intro _ e i hi
    change q = q + 1 at hi
    omega

/-- Exact coordinates of the failure: literal delivered, abstract at the
right endpoint. The word component is irrelevant to this inequality. -/
theorem unfrozen_token_mismatch (q : Nat) :
    (pi witnessFrame q
      (liftedStep witnessFrame (witnessStart q) (rootV witnessFrame 0))).2 0 =
        .denyLeft 0 (by decide) ∧
    multiLocalStep (layout witnessFrame) (tokens witnessFrame q (witnessStart q))
      (encode witnessFrame (rootV witnessFrame 0)) 0 = .denyLeft 1 (by decide) := by
  constructor
  · rw [witness_step]
    exact (witness_after_tokens q 0).trans (if_pos rfl)
  · simp [multiLocalStep, witness_start_tokens, GapDenialState.localStep,
      GapDenialState.advanceEdge, GapDenialState.advance, layout, witnessFrame]
    rfl

/-- Negative form of the requested headline, permitted by the spec's
"exact mismatch" alternative. The two states are coherent and remain in
Slice q, yet the specified equality fails already at one direct-gap edge. -/
theorem unfrozen_step_simulates (q : Nat) :
    let R := witnessFrame
    let s := witnessStart q
    let e := rootV R 0
    Coherent R q s ∧ Slice R q s ∧
    Coherent R q (liftedStep R s e) ∧ Slice R q (liftedStep R s e) ∧
    pi R q (liftedStep R s e) ≠
      (joinedIncidenceStep (placement R) (rearmedOf (ring R) (tokens R q s)) (word R q s) (encode R e),
       multiLocalStep (layout R) (tokens R q s) (encode R e)) := by
  refine ⟨witness_start_coherent q, witness_start_slice q, ?_, witness_stays q, ?_⟩
  · rw [witness_step]
    exact witness_after_coherent q
  · intro he
    have ht := congrArg (fun z => z.2 (0 : Fin witnessFrame.m)) he
    obtain ⟨hl, hr⟩ := unfrozen_token_mismatch q
    simp only at ht
    rw [hl, hr] at ht
    cases ht

#print axioms unfrozen_step_simulates
#print axioms joined_iff_k
#print axioms slice_preserved
#print axioms pi_wellDefined

end ShortGapOwnerRoundSlice

