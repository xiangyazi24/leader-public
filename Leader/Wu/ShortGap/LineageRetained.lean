import Leader.Wu.ShortGap.Lineage

/-!
# Retained delivery, latent service, and the remaining receipt obstruction

The specified right-JOIN cleanup is implemented after the raw event and
physical JOIN. Only a delivered epoch belonging to the right root's departing
generation can be cleared, and only when the post-step owner is toSend.
This differs from the never-clear-until-next-launch representation.

Lineage' interprets a cleared idle gap's completed prefix using its owner
counter and immutable history. It also imposes the spec's strict current
returning/delivered equivalence. The latter is stronger than the prefix
predicate: a successor outbound can coexist with the receiver's OLD denial.
The closure test below uses the requested stronger condition literally.

The token view has a latent state, including when an older delivered epoch
remains after its owner entered the accounting cohort. Accounting round zero
uses a virtual completed predecessor.
-/
namespace ShortGapLineageRetained
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapDenialTransportLiteral ShortGapJoinedIncidenceBalance
open ShortGapLineage
set_option autoImplicit false

/-- Cleanup observes the right JOIN and the owner's post-step port. It never
erases a live reply or a successor declaration waiting on an older receiver. -/
def epochStep' (R : RFrame) (s : GhostRing R) (e : Vtx R) (g : Fin R.m) : GapEpoch :=
  let E := rawEpochs R s e g
  match E with
  | .delivered t _ _ =>
    if fires R (physical R s) e (next R g) && decide (s.k (next R g) = t) &&
        decide (((liftedStep R (physical R s) e).cfg (rootV R g)).cwPort = some .toSend)
    then .idle else E
  | _ => E

def ghostStep' (R : RFrame) (s : GhostRing R) (e : Vtx R) : GhostRing R :=
  { ShortGapLineage.ghostStep R s e with epoch := epochStep' R s e }

theorem ghostStep'_physical (R : RFrame) (s : GhostRing R) (e : Vtx R) :
    physical R (ghostStep' R s e) = liftedStep R (physical R s) e := rfl

def run' (R : RFrame) : GhostRing R → List (Vtx R) → GhostRing R
  | s, [] => s
  | s, e :: es => run' R (ghostStep' R s e) es

def Reachable' (R : RFrame) (s : GhostRing R) : Prop :=
  ∃ es, run' R (ghostStart R) es = s

theorem run'_append (R : RFrame) (s : GhostRing R) (xs ys : List (Vtx R)) :
    run' R s (xs ++ ys) = run' R (run' R s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

theorem run'_erases (R : RFrame) (s : GhostRing R) (es : List (Vtx R)) :
    physical R (run' R s es) = run R (physical R s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

theorem reachable'_erases (R : RFrame) (s : GhostRing R) (hs : Reachable' R s) :
    Reachable R (physical R s) := by
  obtain ⟨es,rfl⟩ := hs
  exact ⟨es,(run'_erases R (ghostStart R) es).symm⟩

/-- Restore only the completed-prefix information of a cleared idle gap.
No physical field or history value changes. This is an interpretation used
by Lineage', not an additional protocol transition. -/
def prefixView (R : RFrame) (s : GhostRing R) : GhostRing R :=
  { s with epoch := fun g => match s.epoch g with
    | .idle => if s.k g = 0 then .idle else
        .delivered (s.k g - 1) ((s.hist g (s.k g - 1)).getD .race)
          ((s.hist (next R g) (s.k g - 1)).getD .race)
    | E => E }

def CurrentResult : GapEpoch → Nat → Prop
  | .returning t _ _, r | .delivered t _ _, r => t = r
  | _, _ => False

instance (E : GapEpoch) (r : Nat) : Decidable (CurrentResult E r) := by
  cases E <;> unfold CurrentResult <;> infer_instance

structure Lineage' (R : RFrame) (s : GhostRing R) : Prop where
  coherent : Lineage R (prefixView R s)
  idleReady : ∀ g, s.epoch g = .idle → s.k g = s.k (next R g) ∧
    (s.cfg (rootV R g)).cwPort = some .toSend ∧
    (s.cfg (rootV R (next R g))).ccwPort = some .free
  incomingCurrent : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g) (s.k (next R g))

theorem lineage'_start (R : RFrame) : Lineage' R (ghostStart R) := by
  constructor
  · exact lineage_start R
  · intro g _; exact ⟨rfl, rfl, rfl⟩
  · intro g; exact Iff.rfl

theorem provenance_of_lineage' (R : RFrame) (s : GhostRing R) (hs : Lineage' R s) (e : Vtx R) :
    RawReceiptProvenance R (physical R s) e :=
  provenance_of_lineage R (prefixView R s) hs.coherent e

theorem neighborSkew_of_lineage' (R : RFrame) (s : GhostRing R) (hs : Lineage' R s) :
    NeighborSkew R (physical R s) := neighborSkew_of_lineage R (prefixView R s) hs.coherent

theorem join_requires_neighbors_of_lineage' (R : RFrame) (s : GhostRing R)
    (hs : Lineage' R s) (e : Vtx R) (i : Fin R.m) (hj : fires R (physical R s) e i = true) :
    s.k i ≤ s.k (next R i) ∧ s.k i ≤ s.k (prev R i) :=
  join_requires_neighbors R (physical R s) e (provenance_of_lineage' R s hs e) i hj

theorem wordOf'_step (R : RFrame) (r : Nat) (s : GhostRing R) (hs : Lineage' R s) (e : Vtx R) :
    wordOf R r (ghostStep' R s e) =
      joinedIncidenceStep (placement R) (mask R r s) (wordOf R r s) (encode R e) :=
  wordOf_step R r (prefixView R s) e hs.coherent

theorem hist'_monotone (R : RFrame) (s : GhostRing R) (e : Vtx R)
    (i : Fin R.m) (r : Nat) (c : Choice) (hh : s.hist i r = some c) :
    (ghostStep' R s e).hist i r = some c := ShortGapLineage.hist_monotone R s e i r c hh

theorem virtualCandidate'_persists (R : RFrame) (r : Nat) (s : GhostRing R)
    (e : Vtx R) (hc : VirtualCandidate R r s) : VirtualCandidate R r (ghostStep' R s e) :=
  virtualCandidate_persists R r s e hc

/-- Unentered cohorts are latent too; this completes the total view in the
case not specified by owner=q / owner>=q+1. The q=0 predecessor is separate. -/
def cohortToken (R : RFrame) (q : Nat) (s : GhostRing R) (g : Fin R.m) : LitGapState R.h :=
  if q < s.k g then .delivered else
  if s.k g < q then .declareAt 0 R.hh else
  match s.epoch g with
  | .idle => .declareAt 0 R.hh
  | .outbound t _ => if t = q then ofPhase R (.declAt (tokenPos R s g)) else .declareAt 0 R.hh
  | .returning t _ _ => if t = q then ofPhase R (.replyAt (tokenPos R s g)) else .declareAt 0 R.hh
  | .delivered t _ _ => if t = q then .delivered else .declareAt 0 R.hh

def tokensOf' (R : RFrame) : Nat → GhostRing R → Fin R.m → LitGapState R.h
  | 0, _, _ => .delivered
  | q+1, s, g => cohortToken R q s g

theorem tokensOf'_start (R : RFrame) (g : Fin R.m) :
    tokensOf' R 1 (ghostStart R) g = .declareAt 0 R.hh := rfl

theorem tokensOf'_past (R : RFrame) (q : Nat) (s : GhostRing R) (g : Fin R.m)
    (hq : q < s.k g) : tokensOf' R (q+1) s g = .delivered := by
  simp [tokensOf', cohortToken, hq]

private theorem forall_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
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

abbrev T : RFrame := ⟨3,2,by decide,by decide,.out1,Or.inl rfl⟩
abbrev E (i : Fin 3) : Vtx T := (i,0)
abbrev F (i : Fin 3) : Vtx T := (i,1)

/-- The old first-launch obstruction is repaired: latent debt 3 advances to
debt 2 under the same physical edge and the independent literal kernel. -/
theorem first_launch_simulates :
    tokensOf' T 1 (ghostStep' T (ghostStart T) (E 0)) =
      multiLitLocalStep (layout T) (tokensOf' T 1 (ghostStart T)) (encode T (E 0)) := by
  funext i
  revert i; apply forall_three <;> rfl

/-- The old two-direct-edge obstruction is repaired: the owner's JOIN does
not discard the receipt still held by its right neighbor. -/
theorem owner_join_retains :
    let s := run' DirectFrame (ghostStart DirectFrame) [directEdge 0, directEdge 1]
    s.epoch 1 = .delivered 0 .out1 .out1 ∧ s.k 1 = 1 ∧ s.k 2 = 0 ∧
      (s.cfg (rootV DirectFrame 2)).ccwPort = some .heldDenial := by decide

abbrev baseRoot : Agent := .root .out1 .toSend .free
abbrev waitRoot : Agent := .root .out1 .waiting .free
abbrev sendDenial : Agent := .root .out1 .toSend .heldDenial
abbrev waitDenial : Agent := .root .out1 .waiting .heldDenial
abbrev freshRoot : Agent := .root .race .toSend .free

def snapshot (R : RFrame) (rs : List Agent) (ts : List Slot) (ks : List Nat)
    (es : List GapEpoch) (h1 : List (Option Choice)) : GhostRing R where
  cfg v := if v.2.val = 0 then rs.getD v.1.val (.interior .empty)
    else .interior (ts.getD v.1.val .empty)
  k i := ks.getD i.val 0
  hist i r := if r = 0 then some .out1 else if r = 1 then h1.getD i.val none else none
  epoch i := es.getD i.val .idle

/-- Five physical interactions, with a still-held old denial at root 2. -/
def launchReady : GhostRing T := snapshot T
  [waitRoot,freshRoot,sendDenial] [.reply .out1,.empty,.empty] [0,1,0]
  [.returning 0 .out1 .out1,.delivered 0 .out1 .out1,.idle] []

def launchTrace : List (Vtx T) := [E 0,F 0,E 1,F 1,E 1]

private theorem ghost_ext {R : RFrame} {s t : GhostRing R}
    (hc : ∀ v, s.cfg v = t.cfg v) (hk : ∀ i, s.k i = t.k i)
    (hh : ∀ i r, s.hist i r = t.hist i r) (he : ∀ i, s.epoch i = t.epoch i) : s = t := by
  cases s; cases t
  have hc' := funext hc; have hk' := funext hk
  have hh' := funext (fun i => funext (hh i)); have he' := funext he
  cases hc'; cases hk'; cases hh'; cases he'; rfl

theorem launchReady_trace : run' T (ghostStart T) launchTrace = launchReady := by
  apply ghost_ext
  · intro ⟨i,a⟩; revert i a; apply forall_three <;> apply forall_two <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> intro r
    all_goals by_cases h0 : r = 0
    all_goals first | (subst r; rfl) |
      simp [run', launchTrace, ghostStep', ghostStep, ghostStart, updateHistory,
        tickHistory, observeHistory, record, physical, liftedStep, fires, incident,
        rawAt, rn, rootV, row, resolveInit, resolveResp, joinReady,
        ShortGapCurrentCohort.uniformStart, ShortGapOwnerRoundSlice.ringStepU,
        joinTick, ShortGapLiteralRingRows.joinA, next, resCw, resCcw, res, Verdict.cw, Verdict.ccw,
        E, F, T, launchReady, snapshot, h0]
  · apply forall_three <;> decide

theorem launchReady_reachable : Reachable' T launchReady := ⟨launchTrace, launchReady_trace⟩

private theorem launchReady_hist (i : Fin 3) (r : Nat) :
    launchReady.hist i r = if r = 0 then some .out1 else none := by
  simp [launchReady, snapshot]

private theorem launchReady_view : prefixView T launchReady = launchReady := by
  apply ghost_ext
  · intro v; rfl
  · intro i; rfl
  · intro i r; rfl
  · apply forall_three <;> rfl

private theorem one_slot_reply (g : Fin 3)
    (h : launchReady.cfg (g,1) = .interior (.reply .out1)) :
    OneToken T launchReady g (.reply .out1) := by
  refine ⟨1, by decide, ?_⟩
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a
  exact h

private theorem empty_slot (g : Fin 3) (h : launchReady.cfg (g,1) = .interior .empty) :
    EmptyGap T launchReady g := by
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a; exact h

theorem launchReady_lineage : Lineage' T launchReady := by
  constructor
  · rw [launchReady_view]
    constructor
    · apply forall_three
      · exact ⟨.out1,.waiting,.free,rfl⟩
      · exact ⟨.race,.toSend,.free,rfl⟩
      · exact ⟨.out1,.toSend,.heldDenial,rfl⟩
    · apply forall_three <;> decide
    · intro i r c h; rw [launchReady_hist] at h
      split at h
      · cases h; decide
      · contradiction
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
    · intro i r h
      have hr : r ≠ 0 := by omega
      simp [launchReady_hist, hr]
    · apply forall_three
      · intro h; cases h
      · intro _; rfl
      · intro h; cases h
    · apply forall_three
      · exact ⟨rfl,Or.inr rfl,rfl,rfl,one_slot_reply 0 rfl⟩
      · exact ⟨Or.inr rfl,Or.inl rfl,rfl,rfl,empty_slot 1 rfl⟩
      · exact ⟨rfl,rfl,empty_slot 2 rfl⟩
    · apply forall_three <;> decide
    · apply forall_three <;> decide
    · apply forall_three <;> decide
    · apply forall_three
      all_goals intro r h
      all_goals first | (exact False.elim h) |
        (have hr : r = 0 := by change r ≤ 0 at h; omega
         subst r; exact ⟨.out1,.out1,rfl,rfl⟩)
    · apply forall_three
      all_goals intro r h
      all_goals first | exact False.elim h | (change r < 0 at h; omega)
    · apply forall_three
      · intro r h; change r < 0 at h; omega
      · intro r h
        have hr : r = 0 := by change r < 1 at h; omega
        subst r
        exact ⟨by decide,by decide,⟨.out1,.out1,rfl,rfl,rfl⟩,⟨.out1,.out1,rfl,rfl,rfl⟩⟩
      · intro r h; change r < 0 at h; omega
    · apply forall_three
      all_goals intro h
      all_goals first | exact False.elim h | (change 0 < 0 at h; omega) | (change 1 ≤ 0 at h; omega)
    · apply forall_three
      · intro h; change 1 ≤ 0 at h; omega
      · intro _; exact ⟨.out1,.out1,rfl,rfl,rfl⟩
      · intro h; exact False.elim h
  · apply forall_three
    · intro h; cases h
    · intro h; cases h
    · intro _; exact ⟨rfl,rfl,rfl⟩
  · apply forall_three <;> decide

/-- COUNTEREXAMPLE: a fresh successor declaration replaces the delivered
epoch, while the lagging receiver still holds the old round's denial. -/
theorem lineage'_step : Reachable' T launchReady ∧ Lineage' T launchReady ∧
    ¬ Lineage' T (ghostStep' T launchReady (E 1)) := by
  refine ⟨launchReady_reachable,launchReady_lineage,?_⟩
  intro h
  have hh := (h.incomingCurrent 1).mp (show CcwHeld
    ((ghostStep' T launchReady (E 1)).cfg (rootV T (next T 1))).ccwPort from trivial)
  exact hh

theorem relaunch_old_receipt :
    (ghostStep' T launchReady (E 1)).epoch 1 = .outbound 1 .out1 ∧
    (ghostStep' T launchReady (E 1)).k 2 = 0 ∧
    ((ghostStep' T launchReady (E 1)).cfg (rootV T 2)).ccwPort = some .heldDenial := by decide

/-- Three direct interactions finish the uniform old cohort; edge 0 then
creates a candidate and edge 2 supplies root 0's incoming denial. -/
def candidateTrace : List (Vtx DirectFrame) :=
  [directEdge 0,directEdge 1,directEdge 2,directEdge 0,directEdge 2]

def candidateState : GhostRing DirectFrame := snapshot DirectFrame
  [.root .out1 .heldCandidate .heldDenial,
   .root .in0 .toSend .heldCandidate,
   .root .out1 .heldDenial .free] [] [1,1,1]
  [.delivered 1 .out1 .in0,.idle,.delivered 1 .out1 .out1]
  [some .out1,some .in0,some .out1]

def candidateView : GhostRing DirectFrame := snapshot DirectFrame
  [.root .out1 .heldCandidate .heldDenial,
   .root .in0 .toSend .heldCandidate,
   .root .out1 .heldDenial .free] [] [1,1,1]
  [.delivered 1 .out1 .in0,.delivered 0 .out1 .out1,.delivered 1 .out1 .out1]
  [some .out1,some .in0,some .out1]

private theorem forall_one {P : Fin 1 → Prop} (h : P 0) : ∀ i, P i := by
  intro i
  have he : i = 0 := Fin.ext (by have := i.isLt; change i.val = 0; omega)
  exact he ▸ h

theorem candidate_trace : run' DirectFrame (ghostStart DirectFrame) candidateTrace = candidateState := by
  apply ghost_ext
  · intro ⟨i,a⟩; revert i a; apply forall_three <;> apply forall_one <;> decide
  · apply forall_three <;> decide
  · apply forall_three <;> intro r
    all_goals by_cases h0 : r = 0
    all_goals first | (subst r; rfl) | skip
    all_goals by_cases h1 : r = 1
    all_goals first | (subst r; rfl) |
      simp [run', candidateTrace, ghostStep', ghostStep, ghostStart, updateHistory,
        tickHistory, observeHistory, record, physical, liftedStep, fires, incident,
        rawAt, rn, rootV, row, resolveInit, resolveResp, joinReady,
        ShortGapCurrentCohort.uniformStart, ShortGapOwnerRoundSlice.ringStepU,
        joinTick, ShortGapLiteralRingRows.joinA, next, resCw, resCcw, res,
        Verdict.cw, Verdict.ccw, directEdge, DirectFrame, candidateState, snapshot, h0, h1]
  · apply forall_three <;> decide

theorem candidate_reachable : Reachable' DirectFrame candidateState := ⟨candidateTrace,candidate_trace⟩

private theorem candidate_view : prefixView DirectFrame candidateState = candidateView := by
  apply ghost_ext
  · intro v; rfl
  · intro i; rfl
  · intro i r; rfl
  · apply forall_three <;> rfl

private theorem candidate_k : ∀ i, candidateView.k i = 1 := by
  apply forall_three <;> rfl

private theorem candidate_hist0 : ∀ i, candidateView.hist i 0 = some .out1 := fun _ => rfl

private theorem candidate_hist1 : ∀ i, candidateView.hist i 1 =
    some (if i = 1 then .in0 else .out1) := by
  apply forall_three <;> rfl

private theorem candidate_hist_later (i : Fin 3) (r : Nat) (hr : 1 < r) :
    candidateView.hist i r = none := by
  simp [candidateView, snapshot, show r ≠ 0 by omega, show r ≠ 1 by omega]

private theorem candidate_empty (g : Fin 3) : EmptyGap DirectFrame candidateView g := by
  intro a ha
  have hh : a.val < 1 := a.isLt
  omega

private theorem candidate_old_denial (g : Fin 3) : HistoricalDenial DirectFrame candidateView g 0 :=
  ⟨.out1,.out1,rfl,rfl,rfl⟩

theorem candidate_lineage : Lineage' DirectFrame candidateState := by
  constructor
  · rw [candidate_view]
    constructor
    · apply forall_three
      · exact ⟨.out1,.heldCandidate,.heldDenial,rfl⟩
      · exact ⟨.in0,.toSend,.heldCandidate,rfl⟩
      · exact ⟨.out1,.heldDenial,.free,rfl⟩
    · apply forall_three <;> decide
    · intro i r c hc
      by_cases h0 : r = 0
      · subst r; rw [candidate_hist0] at hc; cases hc; decide
      · by_cases h1 : r = 1
        · subst r; rw [candidate_hist1] at hc
          split at hc <;> cases hc <;> decide
        · rw [candidate_hist_later i r (by omega)] at hc; cases hc
    · intro i r hr
      rw [candidate_k] at hr
      have he : r = 0 := by omega
      subst r; exact ⟨.out1,rfl⟩
    · apply forall_three
      all_goals intro c cw ccw h
      all_goals cases h
      all_goals rfl
    · intro i r hr
      rw [candidate_k] at hr
      exact candidate_hist_later i r hr
    · apply forall_three <;> intro h <;> cases h
    · apply forall_three
      · exact ⟨Or.inl rfl,Or.inl rfl,rfl,rfl,candidate_empty 0⟩
      · exact ⟨Or.inr rfl,Or.inr rfl,rfl,rfl,candidate_empty 1⟩
      · exact ⟨Or.inl rfl,Or.inl rfl,rfl,rfl,candidate_empty 2⟩
    · apply forall_three <;> decide
    · apply forall_three <;> decide
    · apply forall_three <;> decide
    · apply forall_three
      · intro r hr
        have he : r = 0 ∨ r = 1 := by change r ≤ 1 at hr; omega
        rcases he with h | h <;> subst r
        · exact ⟨.out1,.out1,rfl,rfl⟩
        · exact ⟨.out1,.in0,rfl,rfl⟩
      · intro r hr
        have he : r = 0 := by change r ≤ 0 at hr; omega
        subst r; exact ⟨.out1,.out1,rfl,rfl⟩
      · intro r hr
        have he : r = 0 ∨ r = 1 := by change r ≤ 1 at hr; omega
        rcases he with h | h <;> subst r
        · exact ⟨.out1,.out1,rfl,rfl⟩
        · exact ⟨.out1,.out1,rfl,rfl⟩
    · apply forall_three
      · intro r hr
        have he : r = 0 := by change r < 1 at hr; omega
        subst r; exact candidate_old_denial 0
      · intro r hr; change r < 0 at hr; omega
      · intro r hr
        have he : r = 0 := by change r < 1 at hr; omega
        subst r; exact candidate_old_denial 2
    · intro i r hr
      rw [candidate_k] at hr
      have he : r = 0 := by omega
      subst r
      refine ⟨?_,?_,candidate_old_denial i,candidate_old_denial _⟩
      · revert i; apply forall_three <;> decide
      · revert i; apply forall_three <;> decide
    · apply forall_three
      · intro _; exact ⟨.out1,.in0,rfl,rfl,rfl⟩
      · intro h; change 1 ≤ 0 at h; omega
      · intro _; exact ⟨.out1,.out1,rfl,rfl,rfl⟩
    · apply forall_three
      · intro _; exact ⟨.out1,.in0,rfl,rfl,rfl⟩
      · intro h; change 1 ≤ 0 at h; omega
      · intro _; exact ⟨.out1,.out1,rfl,rfl,rfl⟩
  · apply forall_three
    · intro h; cases h
    · intro _; exact ⟨rfl,rfl,rfl⟩
    · intro h; cases h
  · apply forall_three <;> decide

/-- COUNTEREXAMPLE on a reachable Lineage' state. The carrier view records
completion but not verdict: a delivered candidate plus an incoming denial
makes litRearmedOf true, while the candidate port prevents JOIN. -/
theorem litRearmedOf_iff_gen : Reachable' DirectFrame candidateState ∧
    Lineage' DirectFrame candidateState ∧
    litRearmedOf (ring DirectFrame) (tokensOf' DirectFrame 2 candidateState) 0 = true ∧
    ¬ candidateState.k 0 ≥ 2 := by
  exact ⟨candidate_reachable,candidate_lineage,by decide,by decide⟩

theorem bridge_counterexample_has_virtual_candidate : VirtualCandidate DirectFrame 1 candidateState :=
  ⟨0,rfl,rfl⟩

/-- Exact proposed law, exposed as a proposition so the remaining general
obligation is unambiguous. A definition of this proposition is not its proof. -/
def TokenSimulation (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R) : Prop :=
  tokensOf' R r (ghostStep' R s e) =
      multiLitLocalStep (layout R) (tokensOf' R r s) (encode R e) ∨
    tokensOf' R r (ghostStep' R s e) = tokensOf' R r s

/-- All six scheduler edges checked at the closure counterexample's prestate,
for both its predecessor service and its current owner cohort. This is a
finite regression, not the general tokensOf'_step theorem. -/
theorem token_steps_launchReady : ∀ e : Vtx T,
    TokenSimulation T 1 launchReady e ∧ TokenSimulation T 2 launchReady e := by
  intro ⟨i,a⟩
  revert i a
  apply forall_three <;> apply forall_two
  all_goals constructor
  all_goals first | (apply Or.inl; funext g; revert g; apply forall_three <;> rfl) |
    (apply Or.inr; funext g; revert g; apply forall_three <;> rfl)

/-- Candidate receipts break the mask bridge, not this checked local
transport law. All three physical edges satisfy the proposed simulation. -/
theorem token_steps_candidate : ∀ e : Vtx DirectFrame,
    TokenSimulation DirectFrame 2 candidateState e := by
  intro ⟨i,a⟩
  revert i a
  apply forall_three <;> apply forall_one
  all_goals first | (apply Or.inl; funext g; revert g; apply forall_three <;> rfl) |
    (apply Or.inr; funext g; revert g; apply forall_three <;> rfl)

/-- The reachable successor declaration is blocked by the receiver's old
denial. K3 leaves both accounting views unchanged, even though the strict
Lineage' predicate has already failed at this state. -/
theorem tokensOf'_K3_stutter :
    let s := ghostStep' T launchReady (E 1)
    tokensOf' T 1 (ghostStep' T s (F 1)) = tokensOf' T 1 s ∧
    tokensOf' T 2 (ghostStep' T s (F 1)) = tokensOf' T 2 s := by
  constructor <;> funext g
  all_goals revert g; apply forall_three <;> rfl

/-- Later-round launch is invisible to predecessor service, even with other
old-cohort work still pending in the ring. -/
theorem later_launch_stutter : tokensOf' T 1 (ghostStep' T launchReady (E 1)) =
    tokensOf' T 1 launchReady := by
  funext g; revert g; apply forall_three <;> rfl

theorem blocked_successor_not_locked :
    let s := ghostStep' T launchReady (E 1)
    s.k 1 = 1 ∧ s.k 2 = 0 ∧ s.hist 2 1 = none := by decide

/-- Occupied launches cannot occur in Lineage' states: the prefix view has
the same physical fields, so the proved clean gap framing applies. -/
theorem toSend_empty_gap' (R : RFrame) (s : GhostRing R) (hs : Lineage' R s)
    (g : Fin R.m) (hc : (s.cfg (rootV R g)).cwPort = some .toSend) : EmptyGap R s g :=
  toSend_empty_gap R (prefixView R s) hs.coherent g hc

theorem wordOf'_side_stutter (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hside : ∀ i, incident R e (rootV R i) → r ≠ s.k i) :
    wordOf R r (ghostStep' R s e) = wordOf R r s := wordOf_side_stutter R r s e hside

theorem all_joined_tokens_done (R : RFrame) (r : Nat) (s : GhostRing R)
    (ha : ∀ i, r ≤ s.k i) : ∀ g, tokensOf' R r s g = .delivered := by
  cases r with
  | zero => intro g; rfl
  | succ q => intro g; exact tokensOf'_past R q s g (by have := ha g; omega)

/-- A valid direction of the failed bridge: after every owner has joined,
all predecessor tokens are terminal and every abstract receipt mask is true. -/
theorem all_joined_rearmed (R : RFrame) (r : Nat) (s : GhostRing R)
    (ha : ∀ i, r ≤ s.k i) : ∀ g, litRearmedOf (ring R) (tokensOf' R r s) g = true := by
  intro g
  simp [litRearmedOf, all_joined_tokens_done R r s ha, litIsDischarged, litIsDenying]

/-!
Stall report. The general statement still to prove is

  Lineage' R s -> forall r e, TokenSimulation R r s e.

The completed proofs cover the initial launch, all scheduler edges at two
reachable regression states, and the reachable mixed-round K3 wait. They do
not discharge arbitrary-gap token-position scan preservation through F1/B1
and the compare/return boundary rows. No theorem named tokensOf'_step is
declared for these restricted checks, and no dependency output for such a theorem
is claimed. Slot-occupied launches are excluded, not universally stutters;
L3 may resolve Race on malformed inputs. Later carrier work is invisible once
all owners passed the tracked cohort, by all_joined_tokens_done.

The prerequisite "all of 2-4 hold" for the composed interface is false:
lineage'_step and litRearmedOf_iff_gen are reachable counterexamples. The
latter needs a denial-only service domain or a virtual-success stop before
using the receipt mask. No composed Bellman budget or latch-drain theorem is
claimed here. The distinction between free-before-comparison and
heldCandidate-during-return is respected; neither means a denial JOIN.
-/

#print axioms lineage'_step
#print axioms lineage'_start
#print axioms litRearmedOf_iff_gen
#print axioms wordOf'_step
#print axioms provenance_of_lineage'
#print axioms neighborSkew_of_lineage'
#print axioms first_launch_simulates
#print axioms token_steps_launchReady
#print axioms token_steps_candidate
#print axioms tokensOf'_K3_stutter

end ShortGapLineageRetained
