import Leader.Wu.ShortGap.LiteralRingRows
import Leader.Wu.ShortGap.CandidatePersistence

/-!
Unfrozen candidate-port persistence.

IMPORTANT TYPE CORRECTION: the whole-root equalities requested in items 2
and 3 are false. A responder holding cw=heldCandidate may still receive a
comparison on ccw; an initiator holding ccw=heldCandidate may still launch
on cw. The corrected theorems retain the SAME choice and candidate port,
but existentially quantify the opposite port. The final two theorems give
ring-level counterexamples to the stronger, whole-root statements.

This uses row_preserves_heldCandidate_cw and
row_preserves_heldCandidate_ccw in ShortGapLiteralGapRows, available
through the import. Every post-row JOIN below
is ShortGapLiteralRingRows.joinA, not the gap namespace's similarly named
function. No definition of row or of the original ringStep is changed.
-/

namespace ShortGapLiteralGapRows

set_option autoImplicit false

/-- Before JOIN, a responder root always retains its clockwise port. -/
theorem row_responder_keeps_cw
    (a : Agent) (ch : Choice) (cw : CwPort) (ccw : CcwPort) :
    ∃ ch' ccw',
      (row a (.root ch cw ccw)).2 = .root ch' cw ccw' := by
  cases a with
  | root ch2 cw2 ccw2 =>
      by_cases hsend : cw2 = CwPort.toSend <;>
        by_cases hfree : ccw = CcwPort.free <;>
          simp [row, hsend, hfree]
  | interior slot =>
      cases slot <;>
        by_cases hfree : ccw = CcwPort.free <;>
          simp [row, hfree]

/-- If its choice is already resolved, a responder keeps that choice too.
The existential witness is only the possibly updated counterclockwise port. -/
theorem row_responder_keeps_cw_of_ne_race
    (a : Agent) (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hch : ch ≠ Choice.race) :
    ∃ ccw',
      (row a (.root ch cw ccw)).2 = .root ch cw ccw' := by
  cases a with
  | root ch2 cw2 ccw2 =>
      by_cases hsend : cw2 = CwPort.toSend <;>
        by_cases hfree : ccw = CcwPort.free <;>
          simp [row, resolveResp, hch, hsend, hfree]
  | interior slot =>
      cases slot <;>
        by_cases hfree : ccw = CcwPort.free <;>
          simp [row, resolveResp, hch, hfree]

/-- Before JOIN, an initiator root always retains its counterclockwise port. -/
theorem row_initiator_keeps_ccw
    (ch : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent) :
    ∃ ch' cw',
      (row (.root ch cw ccw) b).1 = .root ch' cw' ccw := by
  cases b with
  | root ch2 cw2 ccw2 =>
      by_cases hsend : cw = CwPort.toSend <;>
        by_cases hfree : ccw2 = CcwPort.free <;>
          simp [row, hsend, hfree]
  | interior slot =>
      cases slot <;>
        by_cases hsend : cw = CwPort.toSend <;>
          by_cases hwait : cw = CwPort.waiting <;>
            simp [row, hsend, hwait]

/-- If its choice is already resolved, an initiator keeps that choice too.
The existential witness is only the possibly updated clockwise port. -/
theorem row_initiator_keeps_ccw_of_ne_race
    (ch : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent)
    (hch : ch ≠ Choice.race) :
    ∃ cw',
      (row (.root ch cw ccw) b).1 = .root ch cw' ccw := by
  cases b with
  | root ch2 cw2 ccw2 =>
      by_cases hsend : cw = CwPort.toSend <;>
        by_cases hfree : ccw2 = CcwPort.free <;>
          simp [row, resolveInit, hch, hsend, hfree]
  | interior slot =>
      cases slot <;>
        by_cases hsend : cw = CwPort.toSend <;>
          by_cases hwait : cw = CwPort.waiting <;>
            simp [row, resolveInit, hch, hsend, hwait]

/-- A clockwise candidate does not freeze the incoming port. -/
theorem row_cw_opposite_port_changes :
    (row (.interior (Slot.decl Choice.in0))
      (.root Choice.out1 CwPort.heldCandidate CcwPort.free)).2 =
        .root Choice.out1 CwPort.heldCandidate CcwPort.heldDenial := by
  rfl

/-- A counterclockwise candidate does not freeze the outgoing port. -/
theorem row_ccw_opposite_port_changes :
    (row (.root Choice.in0 CwPort.toSend CcwPort.heldCandidate)
      (.interior Slot.empty)).1 =
        .root Choice.in0 CwPort.waiting CcwPort.heldCandidate := by
  rfl

end ShortGapLiteralGapRows

namespace ShortGapLiteralRingRows

open ShortGapLiteralGapRows

set_option autoImplicit false

/-- The physical ring step with the race-endpoint freeze removed. -/
def ringStepU (R : RFrame) (cfg : Vtx R → Agent)
    (e : Vtx R) : Vtx R → Agent :=
  fun w =>
    if w = e then
      ShortGapLiteralRingRows.joinA (row (cfg e) (cfg (rn R e))).1
    else if w = rn R e then
      ShortGapLiteralRingRows.joinA (row (cfg e) (cfg (rn R e))).2
    else cfg w

/-- An unscheduled vertex is unchanged. -/
theorem ringStepU_frame
    {R : RFrame} {cfg : Vtx R → Agent} {e w : Vtx R}
    (hw : w ≠ e) (hw' : w ≠ rn R e) :
    ringStepU R cfg e w = cfg w := by
  simp [ringStepU, hw, hw']

theorem ringStepU_at_initiator
    (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R) :
    ringStepU R cfg e e =
      ShortGapLiteralRingRows.joinA (row (cfg e) (cfg (rn R e))).1 := by
  simp [ringStepU]

theorem ringStepU_at_responder
    (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R) :
    ringStepU R cfg e (rn R e) =
      ShortGapLiteralRingRows.joinA (row (cfg e) (cfg (rn R e))).2 := by
  simp [ringStepU, rn_ne_self]

private theorem joinA_fixes_cw_candidate
    (ch : Choice) (ccw : CcwPort) :
    ShortGapLiteralRingRows.joinA
      (.root ch CwPort.heldCandidate ccw) =
        .root ch CwPort.heldCandidate ccw := by
  rfl

private theorem joinA_fixes_ccw_candidate
    (ch : Choice) (cw : CwPort) :
    ShortGapLiteralRingRows.joinA
      (.root ch cw CcwPort.heldCandidate) =
        .root ch cw CcwPort.heldCandidate := by
  cases cw <;> rfl

/-- Corrected item 2: the clockwise candidate and its choice persist.
The counterclockwise port may change when this root is the responder. -/
theorem ringStepU_preserves_heldCandidate_cw
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (ccw : CcwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch CwPort.heldCandidate ccw)
    (e : Vtx R) :
    ∃ ccw', ringStepU R cfg e v =
      .root ch CwPort.heldCandidate ccw' := by
  by_cases hi : v = e
  · subst v
    refine ⟨ccw, ?_⟩
    simpa only [ringStepU_at_initiator, hv,
      row_preserves_heldCandidate_cw ch ccw (cfg (rn R e)) hch] using
        joinA_fixes_cw_candidate ch ccw
  · by_cases hr : v = rn R e
    · subst v
      obtain ⟨ccw', hrow⟩ :=
        row_responder_keeps_cw_of_ne_race
          (cfg e) ch CwPort.heldCandidate ccw hch
      refine ⟨ccw', ?_⟩
      simpa only [ringStepU_at_responder, hv, hrow] using
        joinA_fixes_cw_candidate ch ccw'
    · exact ⟨ccw, (ringStepU_frame hi hr).trans hv⟩

/-- Corrected item 3: the counterclockwise candidate and its choice persist.
The clockwise port may change when this root is the initiator. -/
theorem ringStepU_preserves_heldCandidate_ccw
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (cw : CwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch cw CcwPort.heldCandidate)
    (e : Vtx R) :
    ∃ cw', ringStepU R cfg e v =
      .root ch cw' CcwPort.heldCandidate := by
  by_cases hi : v = e
  · subst v
    obtain ⟨cw', hrow⟩ :=
      row_initiator_keeps_ccw_of_ne_race
        ch cw CcwPort.heldCandidate (cfg (rn R e)) hch
    refine ⟨cw', ?_⟩
    simpa only [ringStepU_at_initiator, hv, hrow] using
      joinA_fixes_ccw_candidate ch cw'
  · by_cases hr : v = rn R e
    · subst v
      refine ⟨cw, ?_⟩
      simpa only [ringStepU_at_responder, hv,
        row_preserves_heldCandidate_ccw ch cw (cfg e) hch] using
          joinA_fixes_ccw_candidate ch cw
    · exact ⟨cw, (ringStepU_frame hi hr).trans hv⟩

private theorem nonrace_root_ne_race
    (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hch : ch ≠ Choice.race) (cw' : CwPort) (ccw' : CcwPort) :
    Agent.root ch cw ccw ≠ Agent.root Choice.race cw' ccw' := by
  intro h
  have hchoice : some ch = some Choice.race := congrArg Agent.choice h
  exact hch (Option.some.inj hchoice)

/-- Either candidate port prevents a resolved root from joining. -/
theorem ringStepU_candidate_never_joins
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch cw ccw)
    (hcand : cw = CwPort.heldCandidate ∨ ccw = CcwPort.heldCandidate)
    (e : Vtx R) :
    ∀ (cw' : CwPort) (ccw' : CcwPort),
      ringStepU R cfg e v ≠ .root Choice.race cw' ccw' := by
  intro cw' ccw'
  cases hcand with
  | inl hcw =>
      subst cw
      obtain ⟨ccwNext, hkeep⟩ :=
        ringStepU_preserves_heldCandidate_cw R cfg v ch ccw hch hv e
      rw [hkeep]
      exact nonrace_root_ne_race
        ch CwPort.heldCandidate ccwNext hch cw' ccw'
  | inr hccw =>
      subst ccw
      obtain ⟨cwNext, hkeep⟩ :=
        ringStepU_preserves_heldCandidate_ccw R cfg v ch cw hch hv e
      rw [hkeep]
      exact nonrace_root_ne_race
        ch cwNext CcwPort.heldCandidate hch cw' ccw'

/-- Arbitrary finite edge words preserve the clockwise candidate and choice. -/
theorem foldl_ringStepU_preserves_heldCandidate_cw
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (ccw : CcwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch CwPort.heldCandidate ccw)
    (es : List (Vtx R)) :
    ∃ ccw', (es.foldl (ringStepU R) cfg) v =
      .root ch CwPort.heldCandidate ccw' := by
  induction es generalizing cfg ccw with
  | nil => exact ⟨ccw, hv⟩
  | cons e es ih =>
      obtain ⟨ccwNext, hstep⟩ :=
        ringStepU_preserves_heldCandidate_cw R cfg v ch ccw hch hv e
      simpa only [List.foldl_cons] using
        ih (cfg := ringStepU R cfg e) (ccw := ccwNext) hstep

/-- Arbitrary finite edge words preserve the counterclockwise candidate
and choice. -/
theorem foldl_ringStepU_preserves_heldCandidate_ccw
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (cw : CwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch cw CcwPort.heldCandidate)
    (es : List (Vtx R)) :
    ∃ cw', (es.foldl (ringStepU R) cfg) v =
      .root ch cw' CcwPort.heldCandidate := by
  induction es generalizing cfg cw with
  | nil => exact ⟨cw, hv⟩
  | cons e es ih =>
      obtain ⟨cwNext, hstep⟩ :=
        ringStepU_preserves_heldCandidate_ccw R cfg v ch cw hch hv e
      simpa only [List.foldl_cons] using
        ih (cfg := ringStepU R cfg e) (cw := cwNext) hstep

/-- Explicit choice projection of the iterated candidate invariant. -/
theorem foldl_ringStepU_candidate_choice
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch cw ccw)
    (hcand : cw = CwPort.heldCandidate ∨ ccw = CcwPort.heldCandidate)
    (es : List (Vtx R)) :
    Agent.choice ((es.foldl (ringStepU R) cfg) v) = some ch := by
  cases hcand with
  | inl hcw =>
      subst cw
      obtain ⟨ccwNext, hkeep⟩ :=
        foldl_ringStepU_preserves_heldCandidate_cw
          R cfg v ch ccw hch hv es
      exact congrArg Agent.choice hkeep
  | inr hccw =>
      subst ccw
      obtain ⟨cwNext, hkeep⟩ :=
        foldl_ringStepU_preserves_heldCandidate_ccw
          R cfg v ch cw hch hv es
      exact congrArg Agent.choice hkeep

/-- No finite execution prefix turns a resolved candidate root into race. -/
theorem foldl_ringStepU_candidate_never_joins
    (R : RFrame) (cfg : Vtx R → Agent)
    (v : Vtx R) (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (hch : ch ≠ Choice.race)
    (hv : cfg v = .root ch cw ccw)
    (hcand : cw = CwPort.heldCandidate ∨ ccw = CcwPort.heldCandidate)
    (es : List (Vtx R)) :
    ∀ (cw' : CwPort) (ccw' : CcwPort),
      (es.foldl (ringStepU R) cfg) v ≠ .root Choice.race cw' ccw' := by
  intro cw' ccw' hbad
  have hchoice :=
    foldl_ringStepU_candidate_choice R cfg v ch cw ccw hch hv hcand es
  have hsome : some ch = some Choice.race :=
    hchoice.symm.trans (congrArg Agent.choice hbad)
  exact hch (Option.some.inj hsome)

/-- Nonvacuous counterexample to the whole-root version of item 2.
The root at rn(e) keeps out1 and cw=C, but ccw changes from free to denial. -/
theorem ringStepU_cw_whole_root_counterexample
    (R : RFrame) (e : Vtx R) :
    ∃ cfg : Vtx R → Agent,
      cfg (rn R e) =
        .root Choice.out1 CwPort.heldCandidate CcwPort.free ∧
      ringStepU R cfg e (rn R e) ≠ cfg (rn R e) := by
  let cfg : Vtx R → Agent := fun w =>
    if w = e then .interior (Slot.decl Choice.in0)
    else .root Choice.out1 CwPort.heldCandidate CcwPort.free
  have he : cfg e = .interior (Slot.decl Choice.in0) := by
    simp [cfg]
  have hr : cfg (rn R e) =
      .root Choice.out1 CwPort.heldCandidate CcwPort.free := by
    simp [cfg, rn_ne_self]
  have hstep : ringStepU R cfg e (rn R e) =
      .root Choice.out1 CwPort.heldCandidate CcwPort.heldDenial := by
    calc
      ringStepU R cfg e (rn R e) =
          ShortGapLiteralRingRows.joinA
            (row (.interior (Slot.decl Choice.in0))
              (.root Choice.out1 CwPort.heldCandidate CcwPort.free)).2 := by
                rw [ringStepU_at_responder, he, hr]
      _ = ShortGapLiteralRingRows.joinA
          (.root Choice.out1 CwPort.heldCandidate CcwPort.heldDenial) :=
            congrArg ShortGapLiteralRingRows.joinA row_cw_opposite_port_changes
      _ = .root Choice.out1 CwPort.heldCandidate CcwPort.heldDenial := rfl
  refine ⟨cfg, hr, ?_⟩
  simp [hstep, hr]

/-- Nonvacuous counterexample to the whole-root version of item 3.
The root at e keeps in0 and ccw=C, but cw changes from toSend to waiting. -/
theorem ringStepU_ccw_whole_root_counterexample
    (R : RFrame) (e : Vtx R) :
    ∃ cfg : Vtx R → Agent,
      cfg e = .root Choice.in0 CwPort.toSend CcwPort.heldCandidate ∧
      ringStepU R cfg e e ≠ cfg e := by
  let cfg : Vtx R → Agent := fun w =>
    if w = e then .root Choice.in0 CwPort.toSend CcwPort.heldCandidate
    else .interior Slot.empty
  have he : cfg e =
      .root Choice.in0 CwPort.toSend CcwPort.heldCandidate := by
    simp [cfg]
  have hr : cfg (rn R e) = .interior Slot.empty := by
    simp [cfg, rn_ne_self]
  have hstep : ringStepU R cfg e e =
      .root Choice.in0 CwPort.waiting CcwPort.heldCandidate := by
    calc
      ringStepU R cfg e e =
          ShortGapLiteralRingRows.joinA
            (row (.root Choice.in0 CwPort.toSend CcwPort.heldCandidate)
              (.interior Slot.empty)).1 := by
                rw [ringStepU_at_initiator, he, hr]
      _ = ShortGapLiteralRingRows.joinA
          (.root Choice.in0 CwPort.waiting CcwPort.heldCandidate) :=
            congrArg ShortGapLiteralRingRows.joinA row_ccw_opposite_port_changes
      _ = .root Choice.in0 CwPort.waiting CcwPort.heldCandidate := rfl
  refine ⟨cfg, he, ?_⟩
  simp [hstep, he]

#print axioms ringStepU_preserves_heldCandidate_cw
#print axioms ringStepU_preserves_heldCandidate_ccw
#print axioms ringStepU_candidate_never_joins
#print axioms foldl_ringStepU_preserves_heldCandidate_cw
#print axioms foldl_ringStepU_preserves_heldCandidate_ccw
#print axioms foldl_ringStepU_candidate_choice
#print axioms foldl_ringStepU_candidate_never_joins
#print axioms ringStepU_cw_whole_root_counterexample
#print axioms ringStepU_ccw_whole_root_counterexample

end ShortGapLiteralRingRows
