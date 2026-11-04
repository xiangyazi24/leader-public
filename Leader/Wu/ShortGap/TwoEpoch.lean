import Leader.Wu.ShortGap.CohortCut

/-!
# Two epoch records per gap

The current transaction and the result retained across the owner's JOIN
are separate records. A physical row first annotates cur; a comparison
retires prev; the owner's JOIN transfers cur to prev and clears cur; the
right root's JOIN finally clears prev. In particular a simultaneous pair
of JOINs does not resurrect a result just cleared at the right endpoint.
The ghosts never select or modify a physical row.

Right-port agreement tests each record against the right root's current
generation. A returning record may survive a right JOIN until delivery at
its owner; its old generation then prevents it from claiming a held port.

The old overwrite trace satisfies the full two-record invariant on both
sides. A different reachable trace exposes the stopped-domain index issue:
DenialOnly2 r constrains predecessor comparisons, while the requested
success predicate tests only word2 r. Its next predecessor comparison can
exit that subtype without satisfying either stipulated round-r stop.
-/
namespace ShortGapTwoEpoch
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapLineage ShortGapLineageRetained
open ShortGapDenialTransportLiteral ShortGapGenerationMask
open ShortGapJoinedIncidenceBalance FiniteUniformStoppingTree
set_option autoImplicit false

/-- The previous delivered result and the current transaction can coexist. -/
structure GapLineage where
  prev : GapEpoch
  cur : GapEpoch
  deriving DecidableEq

structure GhostRing2 (R : RFrame) where
  cfg : Vtx R → Agent
  k : Fin R.m → Nat
  hist : History R
  epoch : Fin R.m → GapLineage

/-- Erase the previous archive when an API only reads physical fields or
the owner's current transaction. -/
def curView (R : RFrame) (s : GhostRing2 R) : GhostRing R :=
  ⟨s.cfg,s.k,s.hist,fun g => (s.epoch g).cur⟩

private theorem curView_epoch (R : RFrame) (s : GhostRing2 R) (g : Fin R.m) :
    (curView R s).epoch g = (s.epoch g).cur := rfl

/-- The newest stored epoch determines the completed historical prefix.
An idle cur can expose prev, but a new outbound never destroys prev. -/
def combinedView (R : RFrame) (s : GhostRing2 R) : GhostRing R :=
  ⟨s.cfg,s.k,s.hist,fun g => match (s.epoch g).cur with
    | .idle => (s.epoch g).prev
    | E => E⟩

def physical2 (R : RFrame) (s : GhostRing2 R) : SliceState R := ⟨s.cfg,s.k⟩

/-- Exactly the comparison branches of the literal row, including direct
P1 where launch, comparison and delivery occur in one interaction. -/
def compares : Agent → Agent → Bool
  | .interior (.decl _), .root _ _ .free => true
  | .root _ .toSend _, .root _ _ .free => true
  | _, _ => false

/-- Event order: raw annotation, owner transfer, right-root retirement.
The unconditional owner transfer follows the spec even if the right root
cleared this result earlier; current-generation port tests ignore such a
stale previous result. No extra guard is silently added to the transfer. -/
def epochStep2 (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m) : GapLineage :=
  let old := s.epoch g
  let current := rawEpochs R (curView R s) e g
  let previous := if g = e.1 ∧ compares (s.cfg e) (s.cfg (rn R e)) = true
    then .idle else old.prev
  let joined := if fires R (physical2 R s) e g then
    {prev := current, cur := .idle} else {prev := previous, cur := current}
  if fires R (physical2 R s) e (next R g) then {joined with prev := .idle} else joined

def ghostStep2 (R : RFrame) (s : GhostRing2 R) (e : Vtx R) : GhostRing2 R where
  cfg := (ghostStep R (curView R s) e).cfg
  k := (ghostStep R (curView R s) e).k
  hist := (ghostStep R (curView R s) e).hist
  epoch := epochStep2 R s e

def ghostStart2 (R : RFrame) : GhostRing2 R :=
  ⟨(ghostStart R).cfg,(ghostStart R).k,(ghostStart R).hist,fun _ => ⟨.idle,.idle⟩⟩

def run2 (R : RFrame) : GhostRing2 R → List (Vtx R) → GhostRing2 R
  | s, [] => s
  | s, e :: es => run2 R (ghostStep2 R s e) es

def Reachable2 (R : RFrame) (s : GhostRing2 R) : Prop :=
  ∃ es, run2 R (ghostStart2 R) es = s

/-- Erasure is the actual unfrozen literal row followed by physical JOIN. -/
theorem ghostStep2_physical (R : RFrame) (s : GhostRing2 R) (e : Vtx R) :
    (ghostStep2 R s e).cfg = ShortGapOwnerRoundSlice.ringStepU R s.cfg e := rfl

theorem ghostStep2_erases (R : RFrame) (s : GhostRing2 R) (e : Vtx R) :
    physical2 R (ghostStep2 R s e) = liftedStep R (physical2 R s) e := rfl

theorem run2_erases (R : RFrame) (s : GhostRing2 R) (es : List (Vtx R)) :
    physical2 R (run2 R s es) = run R (physical2 R s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

theorem run2_append (R : RFrame) (s : GhostRing2 R) (xs ys : List (Vtx R)) :
    run2 R s (xs ++ ys) = run2 R (run2 R s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

theorem reachable2_erases (R : RFrame) (s : GhostRing2 R) (hs : Reachable2 R s) :
    Reachable R (physical2 R s) := by
  obtain ⟨es,rfl⟩ := hs
  exact ⟨es,(run2_erases R (ghostStart2 R) es).symm⟩

def CohortEntered2 (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  ∀ i, r-1 ≤ s.k i

theorem cohortEntered2_step (R : RFrame) (r : Nat) (s : GhostRing2 R) (e : Vtx R)
    (hc : CohortEntered2 R r s) : CohortEntered2 R r (ghostStep2 R s e) :=
  fun i => Nat.le_trans (hc i) (Nat.le_add_right _ _)

theorem cohortEntered2_start (R : RFrame) : CohortEntered2 R 1 (ghostStart2 R) :=
  fun _ => Nat.zero_le _

/-- Previous results have exactly the owner's preceding generation and
immutable endpoint payloads. Both endpoint-clear orders are permitted. -/
def PrevShape (R : RFrame) (s : GhostRing2 R) (g : Fin R.m) : Prop :=
  match (s.epoch g).prev with
  | .idle => True
  | .delivered q c d => s.k g = q+1 ∧
      (s.k (next R g) = q ∨ s.k (next R g) = q+1) ∧
      s.hist g q = some c ∧ s.hist (next R g) q = some d
  | _ => False

def CurrentTag (k : Nat) : GapEpoch → Prop
  | .idle => True
  | .outbound q _ | .returning q _ _ | .delivered q _ _ => q = k

def PreviousResult : GapEpoch → Nat → Prop
  | .delivered q _ _, k => q = k
  | _, _ => False

/-- Physical history/shape coherence is interpreted through the newest
record and its completed prefix. No closure, skew, row simulation or debt
law is stored as a field. Live-token uniqueness is already part of the
coherent epoch shape and is exposed by current_token_shape below. -/
structure Lineage2 (R : RFrame) (s : GhostRing2 R) : Prop where
  coherent : Lineage R (prefixView R (combinedView R s))
  previous : ∀ g, PrevShape R s g
  current : ∀ g, CurrentTag (s.k g) (s.epoch g).cur
  idleSend : ∀ g, (s.epoch g).cur = .idle →
    (s.cfg (rootV R g)).cwPort = some .toSend
  waiting : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live (s.epoch g).cur
  incoming : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g).cur (s.k (next R g)) ∨
    PreviousResult (s.epoch g).prev (s.k (next R g))

theorem lineage2_start (R : RFrame) : Lineage2 R (ghostStart2 R) := by
  refine ⟨lineage_start R, ?_, ?_, ?_, ?_, ?_⟩
  · intro g; trivial
  · intro g; trivial
  · intro g _; rfl
  · intro g
    constructor
    · intro h; cases h
    · intro h; exact False.elim h
  · intro g; exact ⟨False.elim,fun h => h.elim id id⟩

theorem provenance_of_lineage2 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) : RawReceiptProvenance R (physical2 R s) e :=
  provenance_of_lineage R (prefixView R (combinedView R s)) hs.coherent e

theorem neighborSkew_of_lineage2 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) :
    NeighborSkew R (physical2 R s) :=
  neighborSkew_of_lineage R (prefixView R (combinedView R s)) hs.coherent

/-- Every live cur has exactly one token of its stated kind. Idle and
delivered cur have empty interiors; the archive never creates another token. -/
theorem current_token_shape (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
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

def word2 (R : RFrame) (r : Nat) (s : GhostRing2 R) := wordOf R r (curView R s)
def genMask2 (R : RFrame) (r : Nat) (s : GhostRing2 R) := genMask R r (curView R s)
def DenialOnly2 (R : RFrame) (r : Nat) (s : GhostRing2 R) :=
  DenialOnly R r (combinedView R s)
def VirtualCandidate2 (R : RFrame) (r : Nat) (s : GhostRing2 R) :=
  VirtualCandidate R r (curView R s)

/-- Exact pre-step generation mask; neither archive alters the history word. -/
theorem wordOf2_step (R : RFrame) (r : Nat) (s : GhostRing2 R) (e : Vtx R)
    (hs : Lineage2 R s) : word2 R r (ghostStep2 R s e) =
      joinedIncidenceStep (placement R) (genMask2 R r s) (word2 R r s) (encode R e) :=
  wordOf_step R r (prefixView R (combinedView R s)) e hs.coherent

theorem history2_monotone (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (i : Fin R.m) (r : Nat) (c : Choice) (hc : s.hist i r = some c) :
    (ghostStep2 R s e).hist i r = some c :=
  hist_monotone R (curView R s) e i r c hc

/-- The previous record is relevant to right-port provenance. An owner
already beyond q has no remaining own q debt; an owner at q with cur idle
still owes a latent declaration. Thus the carrier reads cur and counters. -/
def tokens2 (R : RFrame) (r : Nat) (s : GhostRing2 R) := tokensOf' R r (curView R s)
def latentDebt2 (R : RFrame) (r : Nat) (s : GhostRing2 R) := litTotalHops (tokens2 R r s)
def roundDebt2 (R : RFrame) (r : Nat) (s : GhostRing2 R) :=
  PeriodHIncidenceChoice.choiceRaceReserve (word2 R r s) + latentDebt2 R r s

/-- Bounded scans still compute the unique occupied slot exactly. -/
theorem tokenPos2_of_unique (R : RFrame) (s : GhostRing2 R) (g : Fin R.m)
    (p : Fin R.h) (hp : 0 < p.val) (t : Slot) (ht : t ≠ .empty)
    (hs : ∀ a : Fin R.h, 0 < a.val →
      s.cfg (g,a) = .interior (if a = p then t else .empty)) :
    tokenPos R (curView R s) g = p.val :=
  tokenPos_of_unique R (curView R s) g p hp t ht hs

theorem latentDebt2_le (R : RFrame) (r : Nat) (s : GhostRing2 R) :
    latentDebt2 R r s ≤ R.m * (2*R.h-1) :=
  ShortGapCohortCut.latentDebt_le R r (curView R s)

theorem potential2_le_cut_budget (R : RFrame) (r : Nat) (s : GhostRing2 R) :
    R.n * roundDebt2 R r s ≤ R.n * R.m * (2*R.h) :=
  ShortGapCohortCut.potential_le_literal_budget R r (curView R s)

/-! Reachable regression for the old epoch-overwrite obstruction. -/

private theorem forall_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hv with h | h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1
  · have he : i = 2 := Fin.ext h; exact he ▸ h2

private theorem forall_two {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1

private theorem ghost2_ext {R : RFrame} {s t : GhostRing2 R}
    (hc : ∀ v, s.cfg v = t.cfg v) (hk : ∀ i, s.k i = t.k i)
    (hh : ∀ i r, s.hist i r = t.hist i r) (he : ∀ i, s.epoch i = t.epoch i) : s = t := by
  cases s; cases t
  have hc' := funext hc; have hk' := funext hk
  have hh' := funext (fun i => funext (hh i)); have he' := funext he
  cases hc'; cases hk'; cases hh'; cases he'; rfl

private theorem ghost_ext {R : RFrame} {s t : GhostRing R}
    (hc : ∀ v, s.cfg v = t.cfg v) (hk : ∀ i, s.k i = t.k i)
    (hh : ∀ i r, s.hist i r = t.hist i r) (he : ∀ i, s.epoch i = t.epoch i) : s = t := by
  cases s; cases t
  have hc' := funext hc; have hk' := funext hk
  have hh' := funext (fun i => funext (hh i)); have he' := funext he
  cases hc'; cases hk'; cases hh'; cases he'; rfl

def launchReady2 : GhostRing2 T where
  cfg := launchReady.cfg
  k := launchReady.k
  hist := launchReady.hist
  epoch g := [GapLineage.mk .idle (.returning 0 .out1 .out1),
    ⟨.delivered 0 .out1 .out1,.idle⟩,⟨.idle,.idle⟩].getD g.val ⟨.idle,.idle⟩

theorem launchReady2_trace : run2 T (ghostStart2 T) launchTrace = launchReady2 := by
  apply ghost2_ext
  · intro ⟨i,a⟩; revert i a; apply forall_three <;> apply forall_two <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> intro r
    all_goals by_cases h0 : r = 0
    all_goals first | (subst r; rfl) |
      simp [run2,launchTrace,ghostStep2,ghostStep,ghostStart2,ghostStart,curView,
        updateHistory,tickHistory,observeHistory,record,physical,liftedStep,fires,incident,
        rawAt,rn,rootV,row,resolveInit,resolveResp,joinReady,
        ShortGapCurrentCohort.uniformStart,ShortGapOwnerRoundSlice.ringStepU,
        joinTick,ShortGapLiteralRingRows.joinA,next,resCw,resCcw,res,Verdict.cw,Verdict.ccw,
        E,ShortGapLineageRetained.F,T,launchReady2,launchReady,snapshot,h0]
  · apply forall_three <;> decide

theorem launchReady2_reachable : Reachable2 T launchReady2 :=
  ⟨launchTrace,launchReady2_trace⟩

theorem launchReady2_view : combinedView T launchReady2 = launchReady := by
  apply ghost_ext
  · intro v; rfl
  · intro i; rfl
  · intro i r; rfl
  · apply forall_three <;> rfl

theorem launchReady2_lineage : Lineage2 T launchReady2 := by
  constructor
  · rw [launchReady2_view]; exact launchReady_lineage.coherent
  · apply forall_three
    · trivial
    · exact ⟨rfl,Or.inl rfl,rfl,rfl⟩
    · trivial
  · apply forall_three <;> trivial
  · apply forall_three
    · intro h; cases h
    · intro _; rfl
    · intro _; rfl
  · apply forall_three
    · exact ⟨fun _ => trivial,fun _ => rfl⟩
    · exact ⟨(fun h => by cases h),False.elim⟩
    · exact ⟨(fun h => by cases h),False.elim⟩
  · apply forall_three
    · exact ⟨False.elim,fun h => h.elim (by change 0 ≠ 1; decide) id⟩
    · exact ⟨fun _ => Or.inr rfl,fun _ => trivial⟩
    · exact ⟨False.elim,fun h => h.elim id id⟩

/-- The sixth event now stores both records simultaneously. The old right
denial remains attributed to prev even though cur is the new declaration. -/
theorem relaunch_retains_both :
    (ghostStep2 T launchReady2 (E 1)).epoch 1 =
      ⟨.delivered 0 .out1 .out1,.outbound 1 .out1⟩ ∧
    (ghostStep2 T launchReady2 (E 1)).k 2 = 0 ∧
    ((ghostStep2 T launchReady2 (E 1)).cfg (rootV T 2)).ccwPort = some .heldDenial := by
  decide

def relaunchView : GhostRing T := snapshot T
  [waitRoot,waitRoot,sendDenial] [.reply .out1,.decl .out1,.empty] [0,1,0]
  [.returning 0 .out1 .out1,.outbound 1 .out1,.idle] [none,some .out1,none]

def relaunch2 : GhostRing2 T where
  cfg := relaunchView.cfg
  k := relaunchView.k
  hist := relaunchView.hist
  epoch g := [GapLineage.mk .idle (.returning 0 .out1 .out1),
    ⟨.delivered 0 .out1 .out1,.outbound 1 .out1⟩,⟨.idle,.idle⟩].getD g.val ⟨.idle,.idle⟩

theorem relaunch2_step : ghostStep2 T launchReady2 (E 1) = relaunch2 := by
  apply ghost2_ext
  · intro ⟨i,a⟩; revert i a; apply forall_three <;> apply forall_two <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> intro r
    all_goals by_cases h0 : r = 0
    all_goals first | (subst r; rfl) |
      simp [ghostStep2,ghostStep,curView,launchReady2,launchReady,relaunch2,relaunchView,
        snapshot,updateHistory,tickHistory,observeHistory,record,physical,liftedStep,fires,
        incident,rawAt,rn,rootV,row,resolveInit,joinReady,E,T,h0]
  · apply forall_three <;> decide

theorem relaunch2_reachable : Reachable2 T relaunch2 := by
  refine ⟨launchTrace ++ [E 1],?_⟩
  rw [run2_append,launchReady2_trace]
  exact relaunch2_step

private theorem relaunch_prefix : prefixView T (combinedView T relaunch2) = relaunchView := by
  apply ghost_ext
  · intro v; rfl
  · intro i; rfl
  · intro i r; rfl
  · apply forall_three <;> rfl

private theorem relaunch_one_slot (g : Fin 3) (t : Slot)
    (h : relaunchView.cfg (g,1) = .interior t) : OneToken T relaunchView g t := by
  refine ⟨1,by decide,?_⟩
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a
  exact h

private theorem relaunch_empty_slot (g : Fin 3)
    (h : relaunchView.cfg (g,1) = .interior .empty) : EmptyGap T relaunchView g := by
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a
  exact h

theorem relaunch_coherent : Lineage T relaunchView := by
  constructor
  · apply forall_three
    · exact ⟨.out1,.waiting,.free,rfl⟩
    · exact ⟨.out1,.waiting,.free,rfl⟩
    · exact ⟨.out1,.toSend,.heldDenial,rfl⟩
  · apply forall_three <;> decide
  · intro i r c h
    have hb : relaunchView.hist i r = some .out1 ∨ relaunchView.hist i r = none := by
      clear h
      revert i
      apply forall_three
      all_goals by_cases h0 : r = 0
      all_goals by_cases h1 : r = 1
      all_goals simp [relaunchView,snapshot,h0,h1]
    rcases hb with hb | hb
    · rw [hb] at h; cases h; decide
    · rw [hb] at h; cases h
  · apply forall_three
    · intro r h; change r < 0 at h; omega
    · intro r h
      have hr : r = 0 := by change r < 1 at h; omega
      subst r; exact ⟨.out1,rfl⟩
    · intro r h; change r < 0 at h; omega
  · apply forall_three
    all_goals intro c cw ccw h
    all_goals cases h
    all_goals rfl
  · apply forall_three
    · intro r h
      have hr : r ≠ 0 := by change 0 < r at h; omega
      simp [relaunchView,snapshot,hr]
    · intro r h
      have hr : r ≠ 0 ∧ r ≠ 1 := by change 1 < r at h; omega
      simp [relaunchView,snapshot,hr.1,hr.2]
    · intro r h
      have hr : r ≠ 0 := by change 0 < r at h; omega
      simp [relaunchView,snapshot,hr]
  · apply forall_three <;> intro h <;> cases h
  · apply forall_three
    · exact ⟨rfl,Or.inr rfl,rfl,rfl,relaunch_one_slot 0 (.reply .out1) rfl⟩
    · exact ⟨rfl,Or.inr rfl,rfl,relaunch_one_slot 1 (.decl .out1) rfl⟩
    · exact ⟨rfl,rfl,relaunch_empty_slot 2 rfl⟩
  · apply forall_three <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> decide
  · apply forall_three
    · intro r h
      have hr : r = 0 := by change r ≤ 0 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl⟩
    · intro r h
      have hr : r = 0 := by change r < 1 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl⟩
    · intro r h; exact False.elim h
  · apply forall_three
    · intro r h; change r < 0 at h; omega
    · intro r h
      have hr : r = 0 := by change r < 1 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl,rfl⟩
    · intro r h; exact False.elim h
  · apply forall_three
    · intro r h; change r < 0 at h; omega
    · intro r h
      have hr : r = 0 := by change r < 1 at h; omega
      subst r
      exact ⟨by decide,by decide,⟨.out1,.out1,rfl,rfl,rfl⟩,⟨.out1,.out1,rfl,rfl,rfl⟩⟩
    · intro r h; change r < 0 at h; omega
  · apply forall_three
    · intro h; change 0 < 0 at h; omega
    · intro h; change 1 < 1 at h; omega
    · intro h; exact False.elim h
  · apply forall_three
    · intro h; change 1 ≤ 0 at h; omega
    · intro _; exact ⟨.out1,.out1,rfl,rfl,rfl⟩
    · intro h; exact False.elim h

/-- Full invariant check of the formerly failing successor, including
its completed prefix, immutable histories, and both port directions. -/
theorem relaunch2_lineage : Lineage2 T relaunch2 := by
  constructor
  · rw [relaunch_prefix]; exact relaunch_coherent
  · apply forall_three
    · trivial
    · exact ⟨rfl,Or.inl rfl,rfl,rfl⟩
    · trivial
  · apply forall_three <;> trivial
  · apply forall_three
    · intro h; cases h
    · intro h; cases h
    · intro _; rfl
  · apply forall_three
    · exact ⟨fun _ => trivial,fun _ => rfl⟩
    · exact ⟨fun _ => trivial,fun _ => rfl⟩
    · exact ⟨(fun h => by cases h),False.elim⟩
  · apply forall_three
    · exact ⟨False.elim,fun h => h.elim (by change 0 ≠ 1; decide) id⟩
    · exact ⟨fun _ => Or.inr rfl,fun _ => trivial⟩
    · exact ⟨False.elim,fun h => h.elim id id⟩

/-- A positive, reachable repair regression; it is not the universally
quantified lineage2_step theorem. Both states are on the denial-only cut. -/
theorem relaunch_closure_repaired :
    Reachable2 T launchReady2 ∧ Lineage2 T launchReady2 ∧
    DenialOnly2 T 1 launchReady2 ∧ CohortEntered2 T 1 launchReady2 ∧
    Lineage2 T (ghostStep2 T launchReady2 (E 1)) ∧
    DenialOnly2 T 1 (ghostStep2 T launchReady2 (E 1)) ∧
    CohortEntered2 T 1 (ghostStep2 T launchReady2 (E 1)) := by
  refine ⟨launchReady2_reachable,launchReady2_lineage,?_,fun _ => Nat.zero_le _,?_,?_,
    fun _ => Nat.zero_le _⟩
  · exact uniform_history_denial T 0 (combinedView T launchReady2) .out1 (fun _ => rfl)
  · rw [relaunch2_step]; exact relaunch2_lineage
  · rw [relaunch2_step]
    exact uniform_history_denial T 0 (combinedView T relaunch2) .out1 (fun _ => rfl)

/-! Generic zero-debt and generation bridge; no carrier simulation premise. -/

private theorem latent_pos (R : RFrame) : 0 < (LitGapState.declareAt 0 R.hh).hops := by
  change 0 < 2*R.h-1-0
  have := R.hh
  omega

/-- A zero current-cohort token implies genuine historical delivery.
The live branches use the bounded scan and unique physical token, so an
invalid fallback scan cannot be mistaken for a completed transaction. -/
theorem zero_token2_completed (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (hz : (tokens2 R (q+1) s g).hops = 0) :
    DeliveredAt ((prefixView R (combinedView R s)).epoch g) q := by
  by_cases hpast : q < (curView R s).k g
  · exact (hs.coherent.joinedDenials g q hpast).1
  · by_cases hfuture : (curView R s).k g < q
    · have hh := latent_pos R
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
        have hh := latent_pos R
        omega
      | outbound t c =>
        simp only [CurrentTag,he,hk] at ht
        simp only [he] at hp
        have hb := tokenPos_bounds R (curView R s) g (.decl c) (by intro h; cases h) hp
        simp only [he,if_pos ht] at hz
        change (ofPhase R (.declAt (tokenPos R (curView R s) g))).hops = 0 at hz
        have hh := R.hh
        simp [ofPhase,hb.2,LitGapState.hops] at hz
        omega
      | returning t c d =>
        simp only [CurrentTag,he,hk] at ht
        simp only [he] at hp
        have hb := tokenPos_bounds R (curView R s) g (.reply d) (by intro h; cases h) hp
        have hle : tokenPos R (curView R s) g ≤ R.h-1 := by omega
        have hge : 1 ≤ tokenPos R (curView R s) g := by omega
        simp only [he,if_pos ht] at hz
        change (ofPhase R (.replyAt (tokenPos R (curView R s) g))).hops = 0 at hz
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

private theorem view_k (R : RFrame) (s : GhostRing2 R) :
    (prefixView R (combinedView R s)).k = s.k := rfl
private theorem view_hist (R : RFrame) (s : GhostRing2 R) :
    (prefixView R (combinedView R s)).hist = s.hist := rfl
private theorem view_cfg (R : RFrame) (s : GhostRing2 R) :
    (prefixView R (combinedView R s)).cfg = s.cfg := rfl

/-- Any root not yet JOINed into r forces positive predecessor debt.
Neither Race nor an entry-cut assumption is needed for this bridge. -/
theorem unjoined_gen_has_debt2 (R : RFrame) (r : Nat) (s : GhostRing2 R)
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

theorem latentDebt2_zero_all_joined (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hd : DenialOnly2 R r s) (hz : latentDebt2 R r s = 0) :
    ∀ i, r ≤ s.k i := by
  intro i
  by_cases hi : s.k i < r
  · have hp := unjoined_gen_has_debt2 R r s hs hd i hi
    omega
  · omega

/-- The zero-debt case of nonincrease is fully physical and needs no
post-step invariant or carrier-simulation hypothesis. -/
theorem latentDebt2_zero_step (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hd : DenialOnly2 R r s) (hz : latentDebt2 R r s = 0)
    (e : Vtx R) : latentDebt2 R r (ghostStep2 R s e) = 0 := by
  have hj := latentDebt2_zero_all_joined R r s hs hd hz
  have ht := all_joined_tokens_done R r (curView R (ghostStep2 R s e))
    (fun i => Nat.le_trans (hj i) (Nat.le_add_right _ _))
  simp [latentDebt2,tokens2,litTotalHops,ht,LitGapState.hops,ofFn_sum_const]

/-! Arbitrary-gap side activity. These lemmas isolate the scheduled gap
as the remaining place where a carrier row proof is needed. -/

theorem epochStep2_cur (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m) :
    (epochStep2 R s e g).cur =
      if fires R (physical2 R s) e g then .idle else rawEpochs R (curView R s) e g := by
  cases ho : fires R (physical2 R s) e g
  all_goals cases hr : fires R (physical2 R s) e (next R g)
  all_goals simp [epochStep2,ho,hr]

theorem ghostStep2_k (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m) :
    (ghostStep2 R s e).k g = s.k g + if fires R (physical2 R s) e g then 1 else 0 := rfl

/-- A step cannot change a positive interior slot in a different gap. -/
theorem other_gap_interior (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (hg : g ≠ e.1) (a : Fin R.h) (ha : 0 < a.val) :
    (ghostStep2 R s e).cfg (g,a) = s.cfg (g,a) := by
  have hn : ¬ incident R e (g,a) := by
    rintro (h | h)
    · exact hg (congrArg Prod.fst h)
    · by_cases he : e.2.val+1 < R.h
      · rw [rn_of_lt R e he] at h
        exact hg (congrArg Prod.fst h)
      · rw [rn_of_last R e he] at h
        have hz := congrArg (fun v : Vtx R => v.2.val) h
        change a.val = 0 at hz
        omega
  rw [ghostStep2_physical]
  exact if_neg hn

/-- In particular, the bounded physical scan of every other gap stutters. -/
theorem other_gap_tokenPos (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (hg : g ≠ e.1) :
    tokenPos R (curView R (ghostStep2 R s e)) g = tokenPos R (curView R s) g := by
  have hp : (fun a : Fin R.h => decide (0 < a.val) &&
      match (ghostStep2 R s e).cfg (g,a) with
      | .interior (.decl _) | .interior (.reply _) => true | _ => false) =
    (fun a : Fin R.h => decide (0 < a.val) &&
      match s.cfg (g,a) with
      | .interior (.decl _) | .interior (.reply _) => true | _ => false) := by
    funext a
    by_cases ha : 0 < a.val
    · rw [other_gap_interior R s e g hg a ha]
    · simp [ha]
  exact congrArg (fun p : Fin R.h → Bool =>
    (((List.finRange R.h).find? p).map Fin.val).getD 0) hp

/-- The current token of another gap stutters unless its owner JOINs.
The entry cut makes such a JOIN discharge its token, never create debt.
This theorem is unconditional in Lineage2 and in denial history. -/
theorem other_gap_token_debt_le (R : RFrame) (r : Nat) (s : GhostRing2 R)
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
theorem idle_gap_token_debt_le (R : RFrame) (r : Nat) (s : GhostRing2 R)
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
    · have ht : tokens2 R (q+1) s g = .declareAt 0 R.hh := by
        simp only [tokens2,tokensOf',cohortToken,if_neg hp,curView_epoch,hi,ite_self]
      rw [ht]
      exact ShortGapCohortCut.token_hops_le _

/-- The total nonincrease theorem reduces to its single scheduled gap.
All other gaps are discharged by the unconditional side-activity lemma. -/
theorem latentDebt2_step_le_of_scheduled_gap (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (hc : CohortEntered2 R r s)
    (hselected : (tokens2 R r (ghostStep2 R s e) e.1).hops ≤ (tokens2 R r s e.1).hops) :
    latentDebt2 R r (ghostStep2 R s e) ≤ latentDebt2 R r s := by
  apply ofFn_sum_le
  intro g
  by_cases hg : g = e.1
  · subst g; exact hselected
  · exact other_gap_token_debt_le R r s e g hg hc

/-! A distinct stopped-domain issue: comparison of a predecessor candidate
can exit DenialOnly2 r before word2 r has any candidate or frozen completion. -/

def cleanView : GhostRing T := snapshot T
  [freshRoot,freshRoot,freshRoot] [.empty,.empty,.empty] [1,1,1]
  [.delivered 0 .out1 .out1,.idle,.delivered 0 .out1 .out1] []

def clean2 : GhostRing2 T where
  cfg := cleanView.cfg
  k := cleanView.k
  hist := cleanView.hist
  epoch g := [GapLineage.mk (.delivered 0 .out1 .out1) .idle,
    ⟨.idle,.idle⟩,⟨.delivered 0 .out1 .out1,.idle⟩].getD g.val ⟨.idle,.idle⟩

def finishOld : List (Vtx T) := [E 0,E 2,ShortGapLineageRetained.F 2,E 2]

theorem clean2_trace : run2 T launchReady2 finishOld = clean2 := by
  apply ghost2_ext
  · intro ⟨i,a⟩; revert i a; apply forall_three <;> apply forall_two <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> intro r
    all_goals by_cases h0 : r = 0
    all_goals first | (subst r; rfl) |
      simp [run2,finishOld,ghostStep2,ghostStep,curView,launchReady2,launchReady,
        clean2,cleanView,snapshot,updateHistory,tickHistory,observeHistory,record,
        physical,liftedStep,fires,incident,rawAt,rn,rootV,row,resolveInit,resolveResp,
        joinReady,ShortGapOwnerRoundSlice.ringStepU,joinTick,ShortGapLiteralRingRows.joinA,
        next,resCw,resCcw,res,Verdict.cw,Verdict.ccw,E,ShortGapLineageRetained.F,T,h0]
  · apply forall_three <;> decide

def beforeCandidateView : GhostRing T := snapshot T
  [waitRoot,.root .in0 .toSend .free,freshRoot] [.decl .out1,.empty,.empty] [1,1,1]
  [.outbound 1 .out1,.delivered 0 .out1 .out1,.delivered 0 .out1 .out1]
  [some .out1,some .in0,none]

def beforeCandidate2 : GhostRing2 T where
  cfg := beforeCandidateView.cfg
  k := beforeCandidateView.k
  hist := beforeCandidateView.hist
  epoch g := [GapLineage.mk (.delivered 0 .out1 .out1) (.outbound 1 .out1),
    ⟨.idle,.idle⟩,⟨.delivered 0 .out1 .out1,.idle⟩].getD g.val ⟨.idle,.idle⟩

/-- Empty-gap receiver resolution precedes launch. This creates a virtual
round-1 candidate before the corresponding physical comparison. -/
theorem beforeCandidate2_trace :
    run2 T clean2 [ShortGapLineageRetained.F 0,E 0] = beforeCandidate2 := by
  apply ghost2_ext
  · intro ⟨i,a⟩; revert i a; apply forall_three <;> apply forall_two <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> intro r
    all_goals by_cases h0 : r = 0
    all_goals first | (subst r; rfl) |
      simp [run2,ghostStep2,ghostStep,curView,clean2,cleanView,beforeCandidate2,beforeCandidateView,
        snapshot,updateHistory,tickHistory,observeHistory,record,physical,liftedStep,
        fires,incident,rawAt,rn,rootV,row,resolveInit,resolveResp,joinReady,
        ShortGapOwnerRoundSlice.ringStepU,joinTick,ShortGapLiteralRingRows.joinA,
        next,E,ShortGapLineageRetained.F,T,h0]
  · apply forall_three <;> decide

theorem beforeCandidate2_reachable : Reachable2 T beforeCandidate2 := by
  refine ⟨launchTrace ++ finishOld ++ [ShortGapLineageRetained.F 0,E 0],?_⟩
  rw [run2_append,run2_append,launchReady2_trace,clean2_trace,beforeCandidate2_trace]

theorem candidate_trace_length :
    (launchTrace ++ finishOld ++ [ShortGapLineageRetained.F 0,E 0]).length = 11 := by decide

private theorem beforeCandidate_prefix :
    prefixView T (combinedView T beforeCandidate2) = beforeCandidateView := by
  apply ghost_ext
  · intro v; rfl
  · intro i; rfl
  · intro i r; rfl
  · apply forall_three <;> rfl

private theorem beforeCandidate_hist (i : Fin 3) (r : Nat) :
    beforeCandidateView.hist i r = if r = 0 then some .out1 else
      if r = 1 then [some .out1,some .in0,none].getD i.val none else none := rfl

private theorem beforeCandidate_k (i : Fin 3) : beforeCandidateView.k i = 1 := by
  revert i; apply forall_three <;> rfl

private theorem beforeCandidate_empty (g : Fin 3)
    (h : beforeCandidateView.cfg (g,1) = .interior .empty) :
    EmptyGap T beforeCandidateView g := by
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a; exact h

private theorem beforeCandidate_token : OneToken T beforeCandidateView 0 (.decl .out1) := by
  refine ⟨1,by decide,?_⟩
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a; rfl

theorem beforeCandidate_coherent : Lineage T beforeCandidateView := by
  constructor
  · apply forall_three
    · exact ⟨.out1,.waiting,.free,rfl⟩
    · exact ⟨.in0,.toSend,.free,rfl⟩
    · exact ⟨.race,.toSend,.free,rfl⟩
  · apply forall_three <;> decide
  · intro i r c h
    by_cases h0 : r = 0
    · subst r; change some Choice.out1 = some c at h; cases h; decide
    · by_cases h1 : r = 1
      · subst r
        revert i; apply forall_three <;> intro h <;> cases h <;> decide
      · simp [beforeCandidate_hist,h0,h1] at h
  · intro i r h
    rw [beforeCandidate_k] at h
    have hr : r = 0 := by omega
    subst r; exact ⟨.out1,rfl⟩
  · apply forall_three
    all_goals intro c cw ccw h
    all_goals cases h
    all_goals rfl
  · intro i r h
    rw [beforeCandidate_k] at h
    have hr : r ≠ 0 ∧ r ≠ 1 := by omega
    simp [beforeCandidate_hist,hr.1,hr.2]
  · apply forall_three
    · intro h; cases h
    · intro h; cases h
    · intro _; rfl
  · apply forall_three
    · exact ⟨rfl,Or.inl rfl,rfl,beforeCandidate_token⟩
    · exact ⟨Or.inr rfl,Or.inr rfl,rfl,rfl,beforeCandidate_empty 1 rfl⟩
    · exact ⟨Or.inr rfl,Or.inr rfl,rfl,rfl,beforeCandidate_empty 2 rfl⟩
  · apply forall_three <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> decide
  · apply forall_three
    · intro r h
      have hr : r = 0 := by change r < 1 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl⟩
    · intro r h
      have hr : r = 0 := by change r ≤ 0 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl⟩
    · intro r h
      have hr : r = 0 := by change r ≤ 0 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl⟩
  · apply forall_three
    · intro r h
      have hr : r = 0 := by change r < 1 at h; omega
      subst r; exact ⟨.out1,.out1,rfl,rfl,rfl⟩
    · intro r h; change r < 0 at h; omega
    · intro r h; change r < 0 at h; omega
  · intro i r h
    rw [beforeCandidate_k] at h
    have hr : r = 0 := by omega
    subst r
    revert i; apply forall_three
    all_goals exact ⟨by decide,by decide,⟨.out1,.out1,rfl,rfl,rfl⟩,⟨.out1,.out1,rfl,rfl,rfl⟩⟩
  · apply forall_three
    · intro h; change 1 < 1 at h; omega
    · intro h; change 1 ≤ 0 at h; omega
    · intro h; change 1 ≤ 0 at h; omega
  · apply forall_three
    · intro h; change 1 < 1 at h; omega
    · intro h; change 1 ≤ 0 at h; omega
    · intro h; change 1 ≤ 0 at h; omega

theorem beforeCandidate2_lineage : Lineage2 T beforeCandidate2 := by
  constructor
  · rw [beforeCandidate_prefix]; exact beforeCandidate_coherent
  · apply forall_three
    · exact ⟨rfl,Or.inr rfl,rfl,rfl⟩
    · trivial
    · exact ⟨rfl,Or.inr rfl,rfl,rfl⟩
  · apply forall_three <;> trivial
  · apply forall_three
    · intro h; cases h
    · intro _; rfl
    · intro _; rfl
  · apply forall_three
    · exact ⟨fun _ => trivial,fun _ => rfl⟩
    · exact ⟨(fun h => by cases h),False.elim⟩
    · exact ⟨(fun h => by cases h),False.elim⟩
  · apply forall_three
    · exact ⟨False.elim,fun h => h.elim id (by change 0 ≠ 1; decide)⟩
    · exact ⟨False.elim,fun h => h.elim id id⟩
    · exact ⟨False.elim,fun h => h.elim id (by change 0 ≠ 1; decide)⟩

abbrev candidateEdge : Vtx T := ShortGapLineageRetained.F 0
def afterCandidate2 : GhostRing2 T := ghostStep2 T beforeCandidate2 candidateEdge

theorem beforeCandidate2_denial : DenialOnly2 T 2 beforeCandidate2 := by
  have hn : ∀ g, ¬ ComparedAt ((prefixView T (combinedView T beforeCandidate2)).epoch g) 1 := by
    apply forall_three <;> decide
  intro g c d h
  exact False.elim (hn g h)

theorem beforeCandidate2_cut : CohortEntered2 T 2 beforeCandidate2 := by
  intro i
  change 1 ≤ beforeCandidateView.k i
  rw [beforeCandidate_k]
  exact Nat.le_refl _

/-- The predecessor's choices already form a virtual candidate before
its comparison. DenialOnly2 constrains completed comparisons, so permits it. -/
theorem predecessor_virtual_candidate : VirtualCandidate2 T 1 beforeCandidate2 := by
  refine ⟨0,rfl,?_⟩
  change word2 T 1 beforeCandidate2 ((ring T).rightNeighbor 0) = .in0
  rw [ring_next]
  rfl

/-- The next physical comparison exits denial-only accounting round 2. -/
theorem afterCandidate2_not_denial : ¬ DenialOnly2 T 2 afterCandidate2 := by
  intro hd
  have h := hd 0 .out1 .in0 (by decide) rfl rfl
  cases h

/-- The denial-domain exit is an actual candidate receipt write, with
the corresponding returning transaction and retired previous record. -/
theorem candidate_comparison_record :
    afterCandidate2.epoch 0 = ⟨.idle,.returning 1 .out1 .in0⟩ ∧
    afterCandidate2.cfg (rootV T 1) = .root .in0 .toSend .heldCandidate := by decide

/-- Every accounting-round-2 choice is still Race after that comparison;
there is neither a round-2 candidate nor a uniform frozen round-2 word. -/
theorem afterCandidate2_word : ∀ i, word2 T 2 afterCandidate2 i = .race := by
  apply forall_three <;> rfl

theorem afterCandidate2_active :
    PeriodHIncidenceChoice.HasRace (word2 T 2 afterCandidate2) ∧
    ¬ VirtualCandidate2 T 2 afterCandidate2 := by
  refine ⟨⟨0,afterCandidate2_word 0⟩,?_⟩
  rintro ⟨g,hg⟩
  have h := hg.1
  change word2 T 2 afterCandidate2 g = .out1 at h
  rw [afterCandidate2_word] at h
  cases h

theorem beforeCandidate2_active :
    PeriodHIncidenceChoice.HasRace (word2 T 2 beforeCandidate2) ∧
    ¬ VirtualCandidate2 T 2 beforeCandidate2 := by
  have hw : ∀ i, word2 T 2 beforeCandidate2 i = .race := by
    apply forall_three <;> rfl
  refine ⟨⟨0,hw 0⟩,?_⟩
  rintro ⟨g,hg⟩
  have h := hg.1
  change word2 T 2 beforeCandidate2 g = .out1 at h
  rw [hw] at h
  cases h

/-- REACHABLE COUNTEREXAMPLE to invariance of the full requested service
domain, despite entry into the predecessor cohort and two epoch records.
It is the denial-only component that fails, not a claimed Lineage2 failure. -/
theorem denial2_cut_not_closed :
    Reachable2 T beforeCandidate2 ∧ Lineage2 T beforeCandidate2 ∧
    DenialOnly2 T 2 beforeCandidate2 ∧ CohortEntered2 T 2 beforeCandidate2 ∧
    ¬ DenialOnly2 T 2 (ghostStep2 T beforeCandidate2 candidateEdge) ∧
    PeriodHIncidenceChoice.HasRace (word2 T 2 (ghostStep2 T beforeCandidate2 candidateEdge)) ∧
    ¬ VirtualCandidate2 T 2 (ghostStep2 T beforeCandidate2 candidateEdge) :=
  ⟨beforeCandidate2_reachable,beforeCandidate2_lineage,beforeCandidate2_denial,
    beforeCandidate2_cut,afterCandidate2_not_denial,afterCandidate2_active⟩

/-- Active round states in the specified invariant subtype. The accounting
word is unresolved and candidate-free at the input as well as on the
successor used in the counterexample. -/
def RoundState2 (R : RFrame) (r : Nat) :=
  {s : GhostRing2 R // Lineage2 R s ∧ DenialOnly2 R r s ∧ CohortEntered2 R r s ∧
    PeriodHIncidenceChoice.HasRace (word2 R r s) ∧ ¬ VirtualCandidate2 R r s}

/-- A necessary property of any physical stopped process using only the
specified round-r success and failure conditions. An unresolved,
candidate-free successor must remain active and must erase to the real step. -/
def PhysicalStoppedRefinement2 (R : RFrame) (r : Nat)
    (step : RoundState2 R r → Fin R.n → StopNode (RoundState2 R r)) : Prop :=
  ∀ s e, ¬ VirtualCandidate2 R r (ghostStep2 R s.val (edgeVtx R e)) →
    PeriodHIncidenceChoice.HasRace (word2 R r (ghostStep2 R s.val (edgeVtx R e))) →
    ∃ t, step s e = .active t ∧ t.val = ghostStep2 R s.val (edgeVtx R e)

/-- COUNTEREXAMPLE to constructing the requested round-r stopped carrier.
Stopping at a round-(r-1) candidate would change the stipulated success
predicate; this theorem keeps that distinction explicit. -/
theorem no_two_epoch_stopped_refinement :
    ¬ ∃ step, PhysicalStoppedRefinement2 T 2 step := by
  rintro ⟨step,hstep⟩
  let s : RoundState2 T 2 := ⟨beforeCandidate2,beforeCandidate2_lineage,
    beforeCandidate2_denial,beforeCandidate2_cut,beforeCandidate2_active⟩
  have he : edgeVtx T (encode T candidateEdge) = candidateEdge := edgeVtx_encE T 0 1
  have h := hstep s (encode T candidateEdge)
  change (¬ VirtualCandidate2 T 2 (ghostStep2 T beforeCandidate2 _)) → _ at h
  rw [he] at h
  obtain ⟨t,_,ht⟩ := h afterCandidate2_active.2 afterCandidate2_active.1
  have hd := t.property.2.1
  rw [ht] at hd
  exact afterCandidate2_not_denial hd

/-- The stopped-domain counterexample is not a child-sum counterexample:
its six literal children satisfy the requested numerical inequality. -/
theorem candidate_childSum :
    1 + (List.ofFn (fun e : Fin T.n =>
      roundDebt2 T 2 (ghostStep2 T beforeCandidate2 (edgeVtx T e)))).sum ≤
        T.n * roundDebt2 T 2 beforeCandidate2 := by decide

/-- The denial classifier exposes a candidate in the predecessor word,
which is a different index from the success predicate in the spec. -/
theorem denial2_or_predecessor_candidate (R : RFrame) (r : Nat) (s : GhostRing2 R) :
    DenialOnly2 R r s ∨ VirtualCandidate2 R (r-1) s := by
  classical
  cases r with
  | zero => exact Or.inl trivial
  | succ q =>
    by_cases hd : DenialOnly2 R (q+1) s
    · exact Or.inl hd
    · apply Or.inr
      apply Classical.byContradiction
      intro hv
      apply hd
      intro g c d _ hc hd'
      have hn : res c d = .denial ∨ (c = .out1 ∧ d = .in0) := by
        cases c <;> cases d <;> simp [res]
      rcases hn with hn | ⟨rfl,rfl⟩
      · exact hn
      · change s.hist g q = some Choice.out1 at hc
        change s.hist (next R g) q = some Choice.in0 at hd'
        exact False.elim (hv ⟨g,by simp [wordOf,choiceToWord,curView,hc],
          by simp [wordOf,choiceToWord,curView,ring_next,hd']⟩)

theorem virtualCandidate2_persists (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (hc : VirtualCandidate2 R r s) :
    VirtualCandidate2 R r (ghostStep2 R s e) :=
  virtualCandidate_persists R r (curView R s) e hc

/-- A uniform frozen predecessor history, if separately established at
the accounting cut, excludes the candidate counterexample and preserves
denial-only membership under every physical edge. This extra domain
condition is not inserted into Lineage2 or the requested debt laws. -/
theorem uniform_predecessor_denial2_step (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (b : Choice) (hb : ∀ i, s.hist i q = some b) (e : Vtx R) :
    DenialOnly2 R (q+1) (ghostStep2 R s e) :=
  uniform_history_denial R q (combinedView R (ghostStep2 R s e)) b
    (fun i => history2_monotone R s e i q b (hb i))

/-- Finite carrier regressions: every physical edge at launchReady2 in
accounting round 1, and at relaunch2 in accounting round 2. They are not
the generic debt laws for arbitrary h. -/
theorem repaired_trace_token_steps : ∀ e : Vtx T,
    (tokens2 T 1 (ghostStep2 T launchReady2 e) =
      multiLitLocalStep (layout T) (tokens2 T 1 launchReady2) (encode T e) ∨
      tokens2 T 1 (ghostStep2 T launchReady2 e) = tokens2 T 1 launchReady2) ∧
    (tokens2 T 2 (ghostStep2 T relaunch2 e) =
      multiLitLocalStep (layout T) (tokens2 T 2 relaunch2) (encode T e) ∨
      tokens2 T 2 (ghostStep2 T relaunch2 e) = tokens2 T 2 relaunch2) := by
  intro ⟨g,a⟩
  revert g a
  apply forall_three <;> apply forall_two <;> constructor
  all_goals first |
    (apply Or.inl; funext i; revert i; apply forall_three <;> rfl) |
    (apply Or.inr; funext i; revert i; apply forall_three <;> rfl)

theorem latentDebt2_start (R : RFrame) :
    latentDebt2 R 1 (ghostStart2 R) = R.m * (2*R.h-1) :=
  ShortGapCohortCut.latentDebt_start R

theorem potential2_start (R : RFrame) :
    R.n * roundDebt2 R 1 (ghostStart2 R) = R.n * R.m * (2*R.h) :=
  ShortGapCohortCut.potential_start R

theorem cut2_service_budget (R : RFrame) (r : Nat) (s : GhostRing2 R) :
    R.n * (R.m + latentDebt2 R r s) ≤ R.n * R.m * (2*R.h) :=
  ShortGapCohortCut.cut_budget_le R r (curView R s)

theorem cut2_budget_comparison (R : RFrame) :
    R.n * R.m * (2*R.h) + 2*R.n*R.m = 2*R.n*R.m*(1+R.h) :=
  ShortGapCohortCut.cut_budget_comparison R

/-! The algebraic capstone, with the remaining carrier obligations explicit. -/

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

/-- Conditional, not the requested unconditional child sum. The joined
Race branch uses the exact word simulation and joinedReserve_childSum;
the other branch uses the proved positive-debt bridge and the explicitly
supplied useful-edge law. No simulation law is hidden in Lineage2. -/
theorem genPipelined2_childSum_of_debt_laws (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hd : DenialOnly2 R r s)
    (hr : PeriodHIncidenceChoice.HasRace (word2 R r s))
    (hnoninc : ∀ e, latentDebt2 R r (ghostStep2 R s e) ≤ latentDebt2 R r s)
    (hprogress : 0 < latentDebt2 R r s →
      ∃ e, latentDebt2 R r (ghostStep2 R s e) + 1 = latentDebt2 R r s) :
    1 + (List.ofFn (fun e : Fin R.n => roundDebt2 R r (ghostStep2 R s (edgeVtx R e)))).sum ≤
      R.n * roundDebt2 R r s := by
  classical
  by_cases hj : ∃ i, word2 R r s i = .race ∧ genMask2 R r s i = true
  · have hw := joinedReserve_childSum (placement R) (genMask2 R r s) (word2 R r s) hj
    have hsum : (List.ofFn (fun e : Fin R.n =>
        PeriodHIncidenceChoice.choiceRaceReserve (word2 R r (ghostStep2 R s (edgeVtx R e))))).sum =
      (List.ofFn (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
        (joinedIncidenceStep (placement R) (genMask2 R r s) (word2 R r s) e))).sum := by
      apply ofFn_sum_eq
      intro e
      rw [wordOf2_step R r s _ hs,encode_edgeVtx]
    have hdebt := ofFn_sum_le
      (fun e : Fin R.n => latentDebt2 R r (ghostStep2 R s (edgeVtx R e)))
      (fun _ => latentDebt2 R r s) (fun e => hnoninc (edgeVtx R e))
    rw [ofFn_sum_const] at hdebt
    unfold roundDebt2
    rw [ofFn_sum_add,hsum,Nat.mul_add]
    omega
  · obtain ⟨i,hi⟩ := hr
    have hk : s.k i < r := by
      have hn : ¬ r ≤ s.k i := by
        intro hk
        exact hj ⟨i,hi,by change decide (r ≤ s.k i) = true; simp [hk]⟩
      omega
    obtain ⟨e,he⟩ := hprogress (unjoined_gen_has_debt2 R r s hs hd i hk)
    have hw : ∀ a : Fin R.n,
        PeriodHIncidenceChoice.choiceRaceReserve (word2 R r (ghostStep2 R s (edgeVtx R a))) ≤
          PeriodHIncidenceChoice.choiceRaceReserve (word2 R r s) := by
      intro a
      rw [wordOf2_step R r s _ hs]
      exact choiceRaceReserve_joinedIncidenceStep_le _ _ _ _
    have he' : edgeVtx R (encode R e) = e := edgeVtx_encE R e.1 e.2
    have hl := sum_strict
      (fun a : Fin R.n => roundDebt2 R r (ghostStep2 R s (edgeVtx R a)))
      (fun _ => roundDebt2 R r s) (encode R e)
      (fun a => Nat.add_le_add (hw a) (hnoninc (edgeVtx R a))) (by
        have hv := hw (encode R e)
        rw [he'] at hv ⊢
        unfold roundDebt2
        omega)
    rw [ofFn_sum_const] at hl
    omega

/-!
Acceptance boundary:

* The two-record update, erasure, start, static provenance/skew, exact word
  step and the full reachable overwrite repair are proved. General
  lineage2_step is not declared: its raw-row closure proof remains open.
* latentDebt2_step_le is not declared as a general result. Zero total
  debt, idle current transactions, and every nonscheduled gap are handled.
  The scheduled outbound/returning/delivered cases remain to be proved.
* advancing_edge_lowers_latentDebt2 is not declared. The scan and token
  uniqueness infrastructure is proved, but the general useful-edge row
  simulation and exact single-unit total decrease remain open.
* genPipelined2_childSum is not declared as unconditional; the theorem
  suffixed of_debt_laws is explicitly conditional on the two debt laws.
* genPipelined2_natBellmanSuperSolution is not declared. The requested
  stopped physical carrier is refuted by no_two_epoch_stopped_refinement:
  DenialOnly2 r can fail through a predecessor candidate while word2 r
  remains entirely Race. This is separate from the open lineage/debt laws.

The numerical budget is 2*n*m*h, attained at the initial round-1 cut,
and smaller than 2*n*m*(1+h) by exactly 2*n*m. It is not promoted to an
expected-time bound without the missing carrier and Bellman proof.
-/

#print axioms ghostStep2_physical
#print axioms lineage2_start
#print axioms provenance_of_lineage2
#print axioms neighborSkew_of_lineage2
#print axioms wordOf2_step
#print axioms tokenPos2_of_unique
#print axioms latentDebt2_le
#print axioms potential2_le_cut_budget
#print axioms current_token_shape
#print axioms relaunch_closure_repaired
#print axioms zero_token2_completed
#print axioms unjoined_gen_has_debt2
#print axioms latentDebt2_zero_step
#print axioms other_gap_token_debt_le
#print axioms beforeCandidate2_reachable
#print axioms denial2_cut_not_closed
#print axioms no_two_epoch_stopped_refinement
#print axioms candidate_comparison_record
#print axioms idle_gap_token_debt_le
#print axioms latentDebt2_step_le_of_scheduled_gap
#print axioms denial2_or_predecessor_candidate
#print axioms uniform_predecessor_denial2_step
#print axioms repaired_trace_token_steps
#print axioms candidate_childSum
#print axioms potential2_start
#print axioms cut2_budget_comparison
#print axioms genPipelined2_childSum_of_debt_laws
end ShortGapTwoEpoch
