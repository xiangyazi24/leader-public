import Leader.Wu.ShortGap.DenialTransportLiteral

/-!
# Current-cohort readiness, reachable cut exits, and persistent history

No theorem in this file assumes SecondRoundBarrier. The old Coherent
structure contains that false field, so ReceiptCoherent below retains only
its six receipt clauses. The stronger incident-token readiness requested in
the spec is tested literally; an incoming declaration can reach a still-Race
root, so this condition is not closed even along a clean all-denial trace.

The general neighbor theorem remains conditional on RawReceiptProvenance.
Coherent' cannot supply it: a separate, not-claimed-reachable counterexample
violates neighbor support and skew under the actual V1+JOIN row. Deriving
provenance from clean reachability remains OPEN.

All finite traces use the actual unfrozen liftedStep. No transition is
replaced by a macro service. Round-indexed history records the choice erased
by JOIN, without changing physical states or counter updates.
-/
namespace ShortGapCurrentCohort
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapDenialTransportLiteral ShortGapTwoDenialJoin ShortGapJoinedIncidenceBalance
set_option autoImplicit false

/-- The old receipt conditions with the false global barrier removed. -/
structure ReceiptCoherent (R : RFrame) (q : Nat) (s : SliceState R) : Prop where
  roots : ∀ i, ∃ c cw ccw, s.cfg (rootV R i) = .root c cw ccw
  normalized : ∀ i, ShortGapLiteralRingRows.joinA (s.cfg (rootV R i)) = s.cfg (rootV R i)
  oldBase : ∀ i, s.k i = q → (s.cfg (rootV R i)).choice = some R.b
  oldGap : ∀ i, s.k i = q → ∃ p, PhysicalGapForm R s.cfg i p
  oldIncoming : ∀ i, s.k i = q → (s.cfg (rootV R i)).ccwPort =
    some (if isDenying (tokens R q s ((ring R).leftNeighbor i)) then .heldDenial else .free)
  advancedIncoming : ∀ i, s.k i = q + 1 →
    isDenying (tokens R q s ((ring R).leftNeighbor i)) = true

/-- Adjacent counters differ by at most one; no global band is imposed. -/
def NeighborSkew (R : RFrame) (s : SliceState R) : Prop :=
  ∀ i, s.k i ≤ s.k (next R i) + 1 ∧ s.k (next R i) ≤ s.k i + 1

/-- A mobile marker, with its cohort supplied by its owner's counter. -/
def Mobile : Agent → Prop
  | .interior (.decl _) => True
  | .interior (.reply _) => True
  | _ => False

def NoCurrentToken (R : RFrame) (q : Nat) (s : SliceState R) (g : Fin R.m) : Prop :=
  s.k g = q + 1 → ∀ a : Fin R.h, 0 < a.val → ¬ Mobile (s.cfg (g,a))

/-- The incident-token version of readiness requested in the spec. Incoming
current declarations make its closure false; coherent'_step certifies this. -/
def CurrentRaceReady (R : RFrame) (q : Nat) (s : SliceState R) : Prop :=
  ∀ i, s.k i = q + 1 → (s.cfg (rootV R i)).choice = some .race →
    (s.cfg (rootV R i)).cwPort = some .toSend ∧
    (s.cfg (rootV R i)).ccwPort = some .free ∧
    NoCurrentToken R q s i ∧ NoCurrentToken R q s (prev R i)

def Coherent' (R : RFrame) (q : Nat) (s : SliceState R) : Prop :=
  ReceiptCoherent R q s ∧ CurrentRaceReady R q s ∧ NeighborSkew R s

/-- Natural uniform entry: choices already frozen at the old base. -/
def uniformStart (R : RFrame) : SliceState R where
  cfg v := if v.2.val = 0 then .root R.b .toSend .free else .interior .empty
  k _ := 0

theorem start_form (R : RFrame) (g : Fin R.m) :
    PhysicalGapForm R (uniformStart R).cfg g .prelaunch := by
  refine ⟨trivial, rfl, ?_⟩
  intro a ha
  simp [uniformStart, slotAgent, Nat.ne_of_gt ha]

theorem start_tokens (R : RFrame) (g : Fin R.m) :
    tokens R 0 (uniformStart R) g = .declareRight 0 R.hh := by
  rw [tokens, if_pos (show (uniformStart R).k g = 0 from rfl), decode_of_form R _ g _ (start_form R g)]
  rfl

/-- Nonvacuous producer for the barrier-free coherence predicate. -/
theorem coherent'_start (R : RFrame) : Coherent' R 0 (uniformStart R) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i; exact ⟨R.b, .toSend, .free, rfl⟩
  · intro i; rfl
  · intro i _; rfl
  · intro i _; exact ⟨.prelaunch, start_form R i⟩
  · intro i _; rw [start_tokens]; rfl
  · intro i hi; change 0 = 1 at hi; omega
  · intro i hi; change 0 = 1 at hi; omega
  · intro i; exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- Finite execution of the actual radius-one lifted transition. -/
def run (R : RFrame) : SliceState R → List (Vtx R) → SliceState R
  | s, [] => s
  | s, e :: es => run R (liftedStep R s e) es

theorem run_append (R : RFrame) (s : SliceState R) (xs ys : List (Vtx R)) :
    run R s (xs ++ ys) = run R (run R s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

def Reachable (R : RFrame) (s : SliceState R) : Prop :=
  ∃ es, run R (uniformStart R) es = s

private theorem state_ext {R : RFrame} {s t : SliceState R}
    (hc : ∀ v, s.cfg v = t.cfg v) (hk : ∀ i, s.k i = t.k i) : s = t := by
  cases s; cases t
  have hc' := funext hc
  have hk' := funext hk
  cases hc'; cases hk'; rfl

private theorem forall_four {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hv with h | h | h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1
  · have he : i = 2 := Fin.ext h; exact he ▸ h2
  · have he : i = 3 := Fin.ext h; exact he ▸ h3

private theorem forall_two {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1

/-! Checked as an explicit eighteen-interaction execution. -/
abbrev F : RFrame := ⟨4, 2, by decide, by decide, .out1, Or.inl rfl⟩
abbrev edge (g : Fin 4) (a : Fin 2) : Vtx F := (g,a)
abbrev B : Agent := .root .out1 .toSend .free
abbrev W : Agent := .root .out1 .waiting .free
abbrev WD : Agent := .root .out1 .waiting .heldDenial
abbrev DF : Agent := .root .out1 .heldDenial .free
abbrev J : Agent := .root .race .toSend .free
abbrev decl : Slot := .decl .out1
abbrev reply : Slot := .reply .out1

def snap (rs : List Agent) (ts : List Slot) (ks : List Nat) : SliceState F where
  cfg v := if v.2.val = 0 then rs.getD v.1.val (.interior .empty)
    else .interior (ts.getD v.1.val .empty)
  k i := ks.getD i.val 0

def t4 := snap [W,W,W,W] [decl,decl,decl,decl] [0,0,0,0]
def t8 := snap [WD,WD,WD,WD] [reply,reply,reply,reply] [0,0,0,0]
def t11 := snap [J,J,WD,J] [.empty,.empty,reply,.empty] [1,1,0,1]
def t12 := snap [W,J,WD,J] [decl,.empty,reply,.empty] [1,1,0,1]
def t14 := snap [W,W,WD,W] [decl,decl,reply,decl] [1,1,0,1]
def t16 := snap [WD,W,WD,DF] [decl,decl,reply,.empty] [1,1,0,1]
def t17 := snap [WD,WD,WD,DF] [reply,decl,reply,.empty] [1,1,0,1]
def t18 := snap [J,WD,WD,DF] [.empty,decl,reply,.empty] [2,1,0,1]

def launchEdges : List (Vtx F) := [edge 0 0, edge 1 0, edge 2 0, edge 3 0]
def compareEdges : List (Vtx F) := [edge 0 1, edge 1 1, edge 2 1, edge 3 1]
def returnEdges : List (Vtx F) := [edge 0 0, edge 1 0, edge 3 0]
def relaunchEdges : List (Vtx F) := [edge 0 0, edge 1 0, edge 3 0]
def beforeExit : List (Vtx F) := launchEdges ++ compareEdges ++ returnEdges ++
  relaunchEdges ++ [edge 3 1, edge 3 0] ++ [edge 0 1]

private theorem state_ext4 {s t : SliceState F}
    (hc : ∀ i : Fin 4, ∀ a : Fin 2, s.cfg (i,a) = t.cfg (i,a))
    (hk : ∀ i : Fin 4, s.k i = t.k i) : s = t :=
  state_ext (fun ⟨i,a⟩ => hc i a) hk

theorem step4 : run F (uniformStart F) launchEdges = t4 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step8 : run F t4 compareEdges = t8 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step11 : run F t8 returnEdges = t11 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step12 : liftedStep F t11 (edge 0 0) = t12 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step14 : run F t11 relaunchEdges = t14 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step16 : run F t14 [edge 3 1, edge 3 0] = t16 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step17 : run F t16 [edge 0 1] = t17 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide
theorem step18 : liftedStep F t17 (edge 0 0) = t18 := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide

theorem trace17 : run F (uniformStart F) beforeExit = t17 := by
  simp only [beforeExit, run_append, step4, step8, step11, step14, step16, step17]

theorem reachable11 : Reachable F t11 := by
  refine ⟨launchEdges ++ compareEdges ++ returnEdges, ?_⟩
  simp only [run_append, step4, step8, step11]

theorem reachable17 : Reachable F t17 := ⟨beforeExit, trace17⟩

theorem trace18 : run F (uniformStart F) (beforeExit ++ [edge 0 0]) = t18 := by
  rw [run_append, trace17]
  exact step18

/-- The four-root clean trace reaches rounds (2,1,0,1), with root C still
in round 0. Local skew survives; a global two-level barrier does not. -/
theorem reachable_cut_exit : Reachable F t18 ∧ t18.k 0 = 2 ∧ t18.k 2 = 0 ∧
    NeighborSkew F t18 ∧ ¬ Slice F 0 t18 := by
  refine ⟨⟨_, trace18⟩, rfl, rfl, ?_, ?_⟩
  · apply forall_four <;> decide
  · intro h; have := h 0; change 2 = 0 ∨ 2 = 1 at this; omega

/-! Receipt coherence at the two counterexample checkpoints. -/
private theorem old_reply_form (s : SliceState F)
    (hw : (s.cfg (rootV F 2)).cwPort = some .waiting)
    (ht : s.cfg (2,1) = .interior reply) : PhysicalGapForm F s.cfg 2 (.replyAt 1) := by
  refine ⟨⟨by decide, by decide⟩, hw, ?_⟩
  intro a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a
  exact ht

private theorem trace_receipt (s : SliceState F)
    (hk : ∀ i, s.k i = if i = 2 then 0 else 1)
    (hr : ∀ i, ∃ c cw ccw, s.cfg (rootV F i) = .root c cw ccw)
    (hn : ∀ i, ShortGapLiteralRingRows.joinA (s.cfg (rootV F i)) = s.cfg (rootV F i))
    (hc : s.cfg (rootV F 2) = WD) (ht : s.cfg (2,1) = .interior reply) :
    ReceiptCoherent F 0 s := by
  have hp := old_reply_form s (by rw [hc]; rfl) ht
  have hdeny : ∀ g, isDenying (tokens F 0 s g) = true := by
    apply forall_four
    all_goals simp only [tokens, hk]
    all_goals simp only [show (0 : Fin 4) ≠ 2 from by decide,
      show (1 : Fin 4) ≠ 2 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      if_false, if_true]
    all_goals simp [decode_of_form F s.cfg 2 (.replyAt 1) hp, phaseToken, isDenying]
  refine ⟨hr, hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have he : i = 2 := by by_cases he : i = 2; exact he; simp [hk, he] at hi
    subst i; rw [hc]; rfl
  · intro i hi
    have he : i = 2 := by by_cases he : i = 2; exact he; simp [hk, he] at hi
    subst i; exact ⟨.replyAt 1, hp⟩
  · intro i hi
    have he : i = 2 := by by_cases he : i = 2; exact he; simp [hk, he] at hi
    subst i; rw [hc, hdeny]; rfl
  · intro i _; exact hdeny _

private theorem receipt11 : ReceiptCoherent F 0 t11 := by
  apply trace_receipt
  · apply forall_four <;> decide
  · apply forall_four
    · exact ⟨.race, .toSend, .free, rfl⟩
    · exact ⟨.race, .toSend, .free, rfl⟩
    · exact ⟨.out1, .waiting, .heldDenial, rfl⟩
    · exact ⟨.race, .toSend, .free, rfl⟩
  · apply forall_four <;> decide
  · rfl
  · rfl

private theorem receipt17 : ReceiptCoherent F 0 t17 := by
  apply trace_receipt
  · apply forall_four <;> decide
  · apply forall_four
    · exact ⟨.out1, .waiting, .heldDenial, rfl⟩
    · exact ⟨.out1, .waiting, .heldDenial, rfl⟩
    · exact ⟨.out1, .waiting, .heldDenial, rfl⟩
    · exact ⟨.out1, .heldDenial, .free, rfl⟩
  · apply forall_four <;> decide
  · rfl
  · rfl

private theorem noCurrent_cell (s : SliceState F) (g : Fin 4)
    (ht : s.k g = 1 → s.cfg (g,1) = .interior .empty) : NoCurrentToken F 0 s g := by
  intro hk a ha
  have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
  subst a
  rw [ht hk]
  exact id

private theorem ready11 : CurrentRaceReady F 0 t11 := by
  apply forall_four
  · intro _ _; refine ⟨rfl, rfl, noCurrent_cell _ _ (fun _ => rfl), noCurrent_cell _ _ (fun _ => rfl)⟩
  · intro _ _; refine ⟨rfl, rfl, noCurrent_cell _ _ (fun _ => rfl), noCurrent_cell _ _ (fun _ => rfl)⟩
  · intro hi; change 0 = 1 at hi; omega
  · intro _ _; refine ⟨rfl, rfl, noCurrent_cell _ _ (fun _ => rfl), noCurrent_cell _ _ ?_⟩
    intro hi; change 0 = 1 at hi; omega

theorem coherent11 : Coherent' F 0 t11 := by
  refine ⟨receipt11, ready11, ?_⟩
  apply forall_four <;> decide

theorem coherent17 : Coherent' F 0 t17 := by
  refine ⟨receipt17, ?_, ?_⟩
  · apply forall_four <;> intro _ hi <;> change some Choice.out1 = some Choice.race at hi <;> cases hi
  · apply forall_four <;> decide

/-- A launches a current declaration toward B; B has not interacted and is
still Race. The prohibition on incoming current tokens fails immediately. -/
theorem incoming_token_violates_readiness : ¬ CurrentRaceReady F 0 t12 := by
  intro h
  have hh := h 1 rfl rfl
  have hn := hh.2.2.2 rfl (1 : Fin 2) (by decide)
  exact hn trivial

/-- NEGATIVE closure result, as allowed by the spec: a single literal edge
from a reachable Coherent' state violates the requested incident-token guard. -/
theorem coherent'_step : Reachable F t11 ∧ Coherent' F 0 t11 ∧
    ¬ Coherent' F 0 (liftedStep F t11 (edge 0 0)) := by
  refine ⟨reachable11, coherent11, ?_⟩
  rw [step12]
  exact fun h => incoming_token_violates_readiness h.2.1

/-- Even after permitting incoming declarations, a history-free whole-step
slice equality cannot cross this reachable q+1-to-q+2 JOIN. -/
theorem unfrozen_step_simulates' :
    Reachable F t17 ∧ Coherent' F 0 t17 ∧ Slice F 0 t17 ∧
    piLit F 0 (liftedStep F t17 (edge 0 0)) ≠
      (joinedIncidenceStep (placement F) (litRearmedOf (ring F) (sliceTokensLit F 0 t17))
        (word F 0 t17) (encode F (edge 0 0)),
       multiLitLocalStep (layout F) (sliceTokensLit F 0 t17) (encode F (edge 0 0))) := by
  refine ⟨reachable17, coherent17, ?_, ?_⟩
  · apply forall_four <;> decide
  · intro he
    have hw := congrArg (fun z => z.1 (0 : Fin 4)) he
    simp only at hw
    have hl : (piLit F 0 (liftedStep F t17 (edge 0 0))).1 0 = .race := by
      rw [step18]; rfl
    have hr := joinedIncidenceStep_of_ne_race (placement F)
      (litRearmedOf (ring F) (sliceTokensLit F 0 t17)) (word F 0 t17)
      (encode F (edge 0 0)) 0 (by decide)
    rw [hl, hr] at hw
    change PeriodHIncidenceChoice.Choice.race = .out1 at hw
    cases hw

/-! What is required to derive local skew, and why readiness is insufficient. -/

/-- Per-port provenance at the raw row output. These are the two missing
lineage obligations, not an assumed global barrier. The generic theorem
below is conditional on this evidence; no closure producer is claimed. -/
structure RawReceiptProvenance (R : RFrame) (s : SliceState R) (e : Vtx R) : Prop where
  outgoing : ∀ i, (rawAt R s.cfg e (rootV R i)).cwPort = some .heldDenial →
    s.k i ≤ s.k (next R i)
  incoming : ∀ i, (rawAt R s.cfg e (rootV R i)).ccwPort = some .heldDenial →
    s.k i ≤ s.k (prev R i)

/-- CONDITIONAL neighbor theorem. A real JOIN reads both raw denial ports;
their generation provenance implies both neighbors have entered the round
being completed. Deriving RawReceiptProvenance from clean reachability is
still OPEN, and the counterexample below shows Coherent' cannot supply it. -/
theorem join_requires_neighbors (R : RFrame) (s : SliceState R) (e : Vtx R)
    (hp : RawReceiptProvenance R s e) (i : Fin R.m) (hf : fires R s e i = true) :
    s.k i ≤ s.k (next R i) ∧ s.k i ≤ s.k (prev R i) := by
  obtain ⟨_, c, hc⟩ := (fires_iff R s e i).1 hf
  exact ⟨hp.outgoing i (by rw [hc]; rfl), hp.incoming i (by rw [hc]; rfl)⟩

/-- Local skew is preserved once the per-interaction provenance obligations
are available. Simultaneous adjacent JOINs are included in the four cases. -/
theorem neighborSkew_step (R : RFrame) (s : SliceState R) (e : Vtx R)
    (hs : NeighborSkew R s) (hp : RawReceiptProvenance R s e) :
    NeighborSkew R (liftedStep R s e) := by
  intro i
  have hbefore := hs i
  have hl : fires R s e i = true → s.k i ≤ s.k (next R i) :=
    fun h => (join_requires_neighbors R s e hp i h).1
  have hr : fires R s e (next R i) = true → s.k (next R i) ≤ s.k i := by
    intro h
    simpa only [prev_next] using (join_requires_neighbors R s e hp (next R i) h).2
  cases h1 : fires R s e i <;> cases h2 : fires R s e (next R i) <;>
    simp_all [liftedStep] <;> omega

/-- A deliberately unsound current reply: the old receipt conditions and
Race-readiness do not authenticate replies of an already advanced owner.
This state is not claimed reachable from uniformStart. -/
def badLineage := snap [WD,WD,WD,WD] [reply,reply,reply,reply] [1,0,0,0]
def badLineageAfter := snap [J,WD,WD,WD] [.empty,reply,reply,reply] [2,0,0,0]

private theorem bad_forms (g : Fin 4) : PhysicalGapForm F badLineage.cfg g (.replyAt 1) := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_⟩
  · apply forall_four (P := fun g => (badLineage.cfg (rootV F g)).cwPort = some .waiting) <;> decide
  · intro a ha
    have he : a = 1 := Fin.ext (by have hh : a.val < 2 := a.isLt; change a.val = 1; omega)
    subst a
    revert g; apply forall_four <;> decide

private theorem bad_denying (g : Fin 4) : isDenying (tokens F 0 badLineage g) = true := by
  by_cases hk : badLineage.k g = 0
  · rw [tokens, if_pos hk, decode_of_form F _ g _ (bad_forms g)]
    rfl
  · simp [tokens, hk, isDenying]

theorem badLineage_coherent : Coherent' F 0 badLineage := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    refine ⟨.out1, .waiting, .heldDenial, ?_⟩
    revert i; apply forall_four <;> decide
  · apply forall_four <;> decide
  · intro i _
    revert i; apply forall_four <;> decide
  · intro i _; exact ⟨.replyAt 1, bad_forms i⟩
  · intro i _; rw [bad_denying]
    revert i; apply forall_four <;> decide
  · intro i _; exact bad_denying _
  · intro i _ hi
    have hn : (badLineage.cfg (rootV F i)).choice ≠ some .race :=
      forall_four (P := fun j => (badLineage.cfg (rootV F j)).choice ≠ some .race)
        (by decide) (by decide) (by decide) (by decide) i
    exact False.elim (hn hi)
  · apply forall_four <;> decide

theorem badLineage_step : liftedStep F badLineage (edge 0 0) = badLineageAfter := by
  apply state_ext4
  · apply forall_four <;> apply forall_two <;> decide
  · apply forall_four <;> decide

/-- Coherent' alone does not imply join_requires_neighbors or skew closure:
the real V1+JOIN row increments 1 to 2 beside neighbors still at 0. -/
theorem coherence_insufficient_for_neighbors :
    Coherent' F 0 badLineage ∧ fires F badLineage (edge 0 0) 0 = true ∧
    ¬ badLineage.k 0 ≤ badLineage.k (next F 0) ∧
    ¬ NeighborSkew F (liftedStep F badLineage (edge 0 0)) ∧
    ¬ RawReceiptProvenance F badLineage (edge 0 0) := by
  refine ⟨badLineage_coherent, by decide, by decide, ?_, ?_⟩
  · rw [badLineage_step]
    intro hs
    have hh := (hs 0).1
    change 2 ≤ 0 + 1 at hh
    omega
  · intro hp
    have hh := (join_requires_neighbors F badLineage (edge 0 0) hp 0 (by decide)).1
    change 1 ≤ 0 at hh
    omega

/-- A checked producer on the reachable cut-exit interaction. The generic
conditional skew theorem is usable here; it does not impose a global barrier. -/
theorem trace_exit_provenance : RawReceiptProvenance F t17 (edge 0 0) := by
  constructor <;> apply forall_four <;> decide

theorem trace_exit_local_skew : NeighborSkew F (liftedStep F t17 (edge 0 0)) :=
  neighborSkew_step F t17 (edge 0 0) coherent17.2.2 trace_exit_provenance

/-! Append-only round-indexed history, erased by the physical projection. -/
abbrev History (R : RFrame) := Fin R.m → Nat → Option Choice

/-- A past recorded value is never replaced, even on malformed lifted inputs. -/
def record (H : Nat → Option Choice) (r : Nat) (c : Choice) : Nat → Option Choice :=
  fun t => if t = r ∧ H t = none then some c else H t

theorem record_monotone (H : Nat → Option Choice) (r t : Nat) (c d : Choice)
    (ht : H t = some d) : record H r c t = some d := by
  simp [record, ht]

theorem record_fresh (H : Nat → Option Choice) (r : Nat) (c : Choice) (hr : H r = none) :
    record H r c r = some c := by simp [record, hr]

/-- JOIN erases the raw root choice of the completed round, so store it at
that round's index. No write occurs for any other raw agent. -/
def tickHistory (a : Agent) (r : Nat) (H : Nat → Option Choice) : Nat → Option Choice :=
  match a with
  | .root c .heldDenial .heldDenial => record H r c
  | _ => H

def joinTickWithHistory (a : Agent) (r : Nat) (H : Nat → Option Choice) :
    Agent × Nat × (Nat → Option Choice) :=
  let t := joinTick a r
  (t.1, t.2, tickHistory a r H)

/-- Exact new record at a fresh history slot, including K2's raw resolved
choice before JOIN resets the physical choice to Race. -/
theorem joinTick_records (c : Choice) (r : Nat) (H : Nat → Option Choice) (hr : H r = none) :
    (joinTickWithHistory (.root c .heldDenial .heldDenial) r H).2.2 r = some c :=
  record_fresh H r c hr

theorem tickHistory_monotone (a : Agent) (r t : Nat) (H : Nat → Option Choice)
    (d : Choice) (ht : H t = some d) : tickHistory a r H t = some d := by
  cases a with
  | interior slot => exact ht
  | root c cw ccw =>
    cases cw <;> cases ccw <;>
      first | exact ht | exact record_monotone H r t c d ht

structure HistoryState (R : RFrame) where
  state : SliceState R
  hist : History R

/-- The physical update and counters are exactly the old liftedStep;
only incident roots can append their erased choice to ghost history. -/
def historyStep (R : RFrame) (s : HistoryState R) (e : Vtx R) : HistoryState R where
  state := liftedStep R s.state e
  hist i := if incident R e (rootV R i) then
    tickHistory (rawAt R s.state.cfg e (rootV R i)) (s.state.k i) (s.hist i)
    else s.hist i

theorem historyStep_erases (R : RFrame) (s : HistoryState R) (e : Vtx R) :
    (historyStep R s e).state = liftedStep R s.state e := rfl

/-- Once a historical choice has been recorded, every future single step
keeps it, regardless of which physical row fires. -/
theorem hist_monotone (R : RFrame) (s : HistoryState R) (e : Vtx R)
    (i : Fin R.m) (r : Nat) (c : Choice) (hr : s.hist i r = some c) :
    (historyStep R s e).hist i r = some c := by
  simp only [historyStep]
  split
  · exact tickHistory_monotone _ _ _ _ _ hr
  · exact hr

def historyRun (R : RFrame) : HistoryState R → List (Vtx R) → HistoryState R
  | s, [] => s
  | s, e :: es => historyRun R (historyStep R s e) es

theorem hist_run_monotone (R : RFrame) (s : HistoryState R) (es : List (Vtx R))
    (i : Fin R.m) (r : Nat) (c : Choice) (hr : s.hist i r = some c) :
    (historyRun R s es).hist i r = some c := by
  induction es generalizing s with
  | nil => exact hr
  | cons e es ih => exact ih _ (hist_monotone R s e i r c hr)

/-- The reachable exit's raw choice out1 can be retained for round 1 even
though the post-JOIN root stores Race at round 2. -/
theorem exit_history_record :
    let s : HistoryState F := ⟨t17, fun _ _ => none⟩
    (historyStep F s (edge 0 0)).hist 0 1 = some .out1 ∧
    (historyStep F s (edge 0 0)).state.cfg (rootV F 0) = J ∧
    (historyStep F s (edge 0 0)).state.k 0 = 2 := by
  decide

/-- Uncompleted rounds have no recorded completion value. This freshness
property makes append-only history faithfully record each erased choice. -/
def HistoryFresh (R : RFrame) (s : HistoryState R) : Prop :=
  ∀ i r, s.state.k i ≤ r → s.hist i r = none

private theorem tickHistory_fresh (a : Agent) (k : Nat) (H : Nat → Option Choice)
    (hf : ∀ r, k ≤ r → H r = none) :
    ∀ r, (joinTick a k).2 ≤ r → tickHistory a k H r = none := by
  cases a with
  | interior slot => exact hf
  | root c cw ccw =>
    cases cw <;> cases ccw
    all_goals intro r hr
    all_goals first | exact hf r hr |
      (have hkr : k + 1 ≤ r := hr
       have hne : r ≠ k := by omega
       simp [tickHistory, record, hne, hf r (by omega)])

/-- Future history stays empty as the counter increases; fresh slots are
therefore available at every later JOIN from an initially empty history. -/
theorem historyFresh_step (R : RFrame) (s : HistoryState R) (e : Vtx R)
    (hf : HistoryFresh R s) : HistoryFresh R (historyStep R s e) := by
  intro i r hr
  by_cases hi : incident R e (rootV R i)
  · simp only [historyStep, if_pos hi]
    apply tickHistory_fresh _ _ _ (hf i) r
    have hk := congrArg Prod.snd (liftedStep_root_tick R s.state e i hi)
    rw [← hk]
    exact hr
  · simp only [historyStep, if_neg hi]
    apply hf i r
    have hk : (liftedStep R s.state e).k i = s.state.k i := by simp [liftedStep, fires, hi]
    change (liftedStep R s.state e).k i ≤ r at hr
    rwa [hk] at hr

/-- Every fresh JOIN stores exactly the raw choice being erased. -/
theorem historyStep_records (R : RFrame) (s : HistoryState R) (e : Vtx R)
    (hf : HistoryFresh R s) (i : Fin R.m) (c : Choice)
    (hi : incident R e (rootV R i))
    (hc : rawAt R s.state.cfg e (rootV R i) = .root c .heldDenial .heldDenial) :
    (historyStep R s e).hist i (s.state.k i) = some c := by
  simp only [historyStep, if_pos hi, hc, tickHistory]
  exact record_fresh _ _ _ (hf i _ (Nat.le_refl _))

def historyStart (R : RFrame) : HistoryState R := ⟨uniformStart R, fun _ _ => none⟩

theorem historyFresh_start (R : RFrame) : HistoryFresh R (historyStart R) := fun _ _ _ => rfl

/-- All finite runs preserve future freshness as well as past recorded values. -/
theorem historyFresh_run (R : RFrame) (s : HistoryState R) (es : List (Vtx R))
    (hf : HistoryFresh R s) : HistoryFresh R (historyRun R s es) := by
  induction es generalizing s with
  | nil => exact hf
  | cons e es ih => exact ih _ (historyFresh_step R s e hf)

/-- The history extension is a conservative lift of the full physical execution. -/
theorem historyRun_erases (R : RFrame) (s : HistoryState R) (es : List (Vtx R)) :
    (historyRun R s es).state = run R s.state es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

#print axioms coherent'_step
#print axioms unfrozen_step_simulates'
#print axioms join_requires_neighbors
#print axioms neighborSkew_step
#print axioms coherence_insufficient_for_neighbors
#print axioms hist_monotone
#print axioms historyFresh_step
#print axioms historyStep_records
#print axioms reachable_cut_exit

end ShortGapCurrentCohort

