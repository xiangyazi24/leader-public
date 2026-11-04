import Leader.Wu.ShortGap.OwnerRoundSlice

/-!
# Literal-faithful denial transport with 2h-1 useful firings

The compare step turns the declaration in place at h-1; h=1 delivers
atomically. This is the uniform, all-denial carrier. The service Bellman
certificate and sequential CandidateRearmSpec capstone use n*m*(2h-1),
without changing any literal row or any existing transport consumer.

The frozen ring simulation is positive. The unfrozen slice retry is negative
under the existing Coherent predicate, which permits an orphaned current-round
Race/waiting owner. The witness is not claimed reachable from a clean start.
A stronger current-cohort invariant and its closure remain OPEN; the service
certificate alone supplies no pipelined capstone.
-/
namespace ShortGapDenialTransportLiteral
open FiniteUniformStoppingTree PeriodHIncidenceChoice ShortGapChoiceStopping
open ShortGapDenialTransport
set_option autoImplicit false

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-- j=0 is prelaunch; positive declarations and all replies occupy actual
interior slots. There is no abstract reply position h. -/
inductive LitGapState (h : Nat) where
  | declareAt (j : Nat) (hj : j < h)
  | replyAt (j : Nat) (hj : 1 ≤ j ∧ j ≤ h - 1)
  | delivered

namespace LitGapState

def hops {h : Nat} : LitGapState h → Nat
  | .declareAt j _ => 2 * h - 1 - j
  | .replyAt j _ => j
  | .delivered => 0

def advanceEdge {h : Nat} : LitGapState h → Option (Fin h)
  | .declareAt j hj => some ⟨j, hj⟩
  | .replyAt j hj => some ⟨j - 1, by omega⟩
  | .delivered => none

/-- Comparison consumes the last outward firing and starts the reply in
that same slot; delivery consumes the last return firing. -/
def advance {h : Nat} : LitGapState h → LitGapState h
  | .declareAt j hj =>
    if hn : j + 1 < h then .declareAt (j + 1) hn
    else if hh : h = 1 then .delivered
    else .replyAt (h - 1) ⟨by omega, Nat.le_refl _⟩
  | .replyAt j hj =>
    if hn : 2 ≤ j then .replyAt (j - 1) ⟨by omega, by omega⟩ else .delivered
  | .delivered => .delivered

theorem advanceEdge_of_hops_pos {h : Nat} (s : LitGapState h)
    (hp : 0 < s.hops) : ∃ a, s.advanceEdge = some a := by
  cases s with
  | declareAt j hj => exact ⟨⟨j, hj⟩, rfl⟩
  | replyAt j hj => exact ⟨⟨j - 1, by omega⟩, rfl⟩
  | delivered => simp [hops] at hp

/-- Exactly one unit of debt disappears on the unique useful edge. -/
theorem hops_advance_of_some {h : Nat} (s : LitGapState h) (a : Fin h)
    (ha : s.advanceEdge = some a) : s.advance.hops + 1 = s.hops := by
  cases s with
  | declareAt j hj =>
    simp only [advance]
    split
    · simp only [hops]; omega
    · split <;> simp only [hops] <;> omega
  | replyAt j hj =>
    simp only [advance]
    split <;> simp only [hops] <;> omega
  | delivered => simp [advanceEdge] at ha

/-- This countdown uniquely identifies every well-typed carrier state. -/
theorem hops_injective {h : Nat} (hh : 0 < h) : Function.Injective (@hops h) := by
  intro s t he
  cases s <;> cases t <;> simp only [hops] at he
  all_goals first | rfl | (have : False := by omega; contradiction) |
    (have hj : _ := he; congr 1 <;> omega)

def localStep {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (e : Fin n) : LitGapState h :=
  match s.advanceEdge with
  | some a => if edgeAt a = e then s.advance else s
  | none => s

theorem hops_localStep_le {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (e : Fin n) :
    (localStep edgeAt s e).hops ≤ s.hops := by
  unfold localStep
  split
  · rename_i a ha
    split
    · have := hops_advance_of_some s a ha
      omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem localStep_advanceEdge {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (a : Fin h) (ha : s.advanceEdge = some a) :
    localStep edgeAt s (edgeAt a) = s.advance := by
  simp [localStep, ha]

theorem hops_localStep_advance {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (a : Fin h) (ha : s.advanceEdge = some a) :
    (localStep edgeAt s (edgeAt a)).hops + 1 = s.hops := by
  rw [localStep_advanceEdge edgeAt s a ha]
  exact hops_advance_of_some s a ha

/-- Every edge other than the advancing edge leaves the gap unchanged. -/
theorem localStep_eq_of_ne {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (e : Fin n)
    (hne : ∀ a, s.advanceEdge = some a → edgeAt a ≠ e) :
    localStep edgeAt s e = s := by
  unfold localStep
  split
  · rename_i a ha
    rw [if_neg (hne a ha)]
  · rfl

end LitGapState

/-- Joint carrier state with at least one gap still in transit. -/
structure MultiLitGapState (h m : Nat) where
  gap : Fin m → LitGapState h
  hasActive : ∃ g, 0 < (gap g).hops

/-- Total remaining carrier hops over all gaps. -/
def litTotalHops {h m : Nat} (gap : Fin m → LitGapState h) : Nat :=
  (List.ofFn (fun g => (gap g).hops)).sum

/-- One scheduler edge acting on every gap through its own edge set. -/
def multiLitLocalStep {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → LitGapState h) (e : Fin n) :
    Fin m → LitGapState h :=
  fun g => LitGapState.localStep (L.edgeAt g) (gap g) e

theorem litTotalHops_multiLitLocalStep_le {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → LitGapState h) (e : Fin n) :
    litTotalHops (multiLitLocalStep L gap e) ≤ litTotalHops gap :=
  ofFn_sum_le _ _
    (fun g => LitGapState.hops_localStep_le (L.edgeAt g) (gap g) e)

/-- The advancing edge of any in-transit gap strictly lowers the total. -/
theorem litTotalHops_multiLitLocalStep_lt {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → LitGapState h) (g : Fin m) (a : Fin h)
    (ha : (gap g).advanceEdge = some a) :
    litTotalHops (multiLitLocalStep L gap (L.edgeAt g a)) < litTotalHops gap := by
  apply ofFn_sum_lt_of_single_lt _ _ g
  · intro g'
    exact LitGapState.hops_localStep_le (L.edgeAt g') (gap g') _
  · have := LitGapState.hops_localStep_advance (L.edgeAt g) (gap g) a ha
    show (multiLitLocalStep L gap (L.edgeAt g a) g).hops < (gap g).hops
    simp only [multiLitLocalStep]
    omega

/-- A gap's advancing edge leaves every other gap unchanged. -/
theorem multiLitLocalStep_other {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → LitGapState h) (g g' : Fin m) (hne : g' ≠ g)
    (a : Fin h) :
    multiLitLocalStep L gap (L.edgeAt g a) g' = gap g' := by
  apply LitGapState.localStep_eq_of_ne
  intro a' _ heq
  exact hne (L.edgeAt_injective g' a' g a heq).1

/-- The token-walk rearm service stops only after every gap is discharged. -/
noncomputable def multiLitGapStep {n h m : Nat} (L : GapLayout n h m) :
    MultiLitGapState h m → Fin n → StopNode (MultiLitGapState h m) :=
  fun state edge =>
    let next := multiLitLocalStep L state.gap edge
    if hnext : ∃ g, 0 < (next g).hops then
      .active ⟨next, hnext⟩
    else .success

def multiLitGapPotential {n h m : Nat} :
    StopNode (MultiLitGapState h m) → Nat
  | .active state => n * litTotalHops state.gap
  | .success => 0
  | .failure => 0

private theorem multiLitGapPotential_step_le
    {n h m : Nat} (L : GapLayout n h m)
    (state : MultiLitGapState h m) (edge : Fin n) :
    multiLitGapPotential (n := n) (multiLitGapStep L state edge) ≤
      n * litTotalHops (multiLitLocalStep L state.gap edge) := by
  classical
  simp only [multiLitGapStep]
  split <;> simp [multiLitGapPotential]

/-- The exact child-sum inequality for remaining carrier hops. -/
theorem litTotalHops_childSum {n h m : Nat} (L : GapLayout n h m)
    (state : MultiLitGapState h m) :
    1 + (List.ofFn (fun edge : Fin n =>
      litTotalHops (multiLitLocalStep L state.gap edge))).sum ≤
        n * litTotalHops state.gap := by
  obtain ⟨g, hg⟩ := state.hasActive
  obtain ⟨a, ha⟩ := LitGapState.advanceEdge_of_hops_pos _ hg
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n => litTotalHops (multiLitLocalStep L state.gap edge))
    (fun _ : Fin n => litTotalHops state.gap) (L.edgeAt g a)
    (fun edge => litTotalHops_multiLitLocalStep_le L state.gap edge)
    (litTotalHops_multiLitLocalStep_lt L state.gap g a ha)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- The token-walk rearm service has expected work at most `n` times the
initial total number of carrier hops. -/
theorem multiLitGap_natBellmanSuperSolution
    {n h m : Nat} (L : GapLayout n h m) :
    NatBellmanSuperSolution (multiLitGapStep L) 1
      (multiLitGapPotential (n := n)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := litTotalHops_childSum L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        multiLitGapPotential (n := n) (multiLitGapStep L state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          litTotalHops (multiLitLocalStep L state.gap edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          multiLitGapPotential (n := n) (multiLitGapStep L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          n * litTotalHops (multiLitLocalStep L state.gap edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact multiLitGapPotential_step_le L state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          litTotalHops (multiLitLocalStep L state.gap edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        multiLitGapPotential (n := n) (multiLitGapStep L state edge))).sum ≤
      n + n * (List.ofFn (fun edge : Fin n =>
        litTotalHops (multiLitLocalStep L state.gap edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
        litTotalHops (multiLitLocalStep L state.gap edge))).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * litTotalHops state.gap) := hscaled
    _ = n * multiLitGapPotential (n := n) (.active state) := rfl

theorem multiLitGapStep_ne_failure {n h m : Nat} (L : GapLayout n h m) :
    ∀ state edge, multiLitGapStep L state edge ≠ .failure := by
  classical
  intro state edge
  simp only [multiLitGapStep]
  split <;> simp

/-- Every gap starts with its left root's declaration at position `0`. -/
def allLitDeclareStart {n h m : Nat} (L : GapLayout n h m) (hm : 0 < m) :
    MultiLitGapState h m :=
  ⟨fun _ => .declareAt 0 L.hpos,
    ⟨⟨0, hm⟩, by
      have := L.hpos
      simp only [LitGapState.hops]
      omega⟩⟩

@[simp] theorem litTotalHops_allDeclare {h m : Nat} (hpos : 0 < h) :
    litTotalHops (fun _ : Fin m => LitGapState.declareAt 0 hpos) =
      m * (2 * h - 1) := by
  simp only [litTotalHops, LitGapState.hops, ofFn_sum_const, Nat.sub_zero]

@[simp] theorem multiLitGapPotential_allDeclare
    {n h m : Nat} (L : GapLayout n h m) (hm : 0 < m) :
    multiLitGapPotential (n := n) (.active (allLitDeclareStart L hm)) =
      n * (m * (2 * h - 1)) := by
  simp [multiLitGapPotential, allLitDeclareStart]

/-- Token-walk implementation of the candidate rearm interface for `m` gaps
of physical length `h` on disjoint edge sets. -/
noncomputable def multiLitGapDenialRearmSpec
    {n h m : Nat} (L : GapLayout n h m) (hm : 0 < m) :
    CandidateRearmSpec n where
  State := MultiLitGapState h m
  step := multiLitGapStep L
  start := allLitDeclareStart L hm
  potential := multiLitGapPotential (n := n)
  bellman := multiLitGap_natBellmanSuperSolution L
  noFailure := multiLitGapStep_ne_failure L

/-- Complete candidate process with token-walk rearm: bare incidence choice,
charged denial transport across every gap, and repetition until the first
persistent candidate. -/
noncomputable def multiLitGapCandidateRestartStep
    {n h m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (L : GapLayout n h m) (hm : 0 < m) :=
  (multiLitGapDenialRearmSpec L hm).restartStep ring P hm

/-- Sequential candidate restart with the literal service, at the exact
interface budget 2*n*m + n*m*(2h-1). This does not assert pipelined refinement. -/
theorem multiLitGapCandidateRestart_truncatedCost_le
    {n h m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) (T : Nat) :
    truncatedActiveCostNumerator
      (multiLitGapCandidateRestartStep ring P L (by omega))
      (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
        n ^ T * (2 * (n * m) + n * (m * (2 * h - 1))) := by
  have hc := (multiLitGapDenialRearmSpec L (by omega)).allRace_truncatedCost_le ring hm P hn T
  simpa only [multiLitGapCandidateRestartStep, multiLitGapDenialRearmSpec,
    multiLitGapPotential_allDeclare] using hc

/-- Reciprocal success tail for the same sequential composition. -/
theorem multiLitGapCandidateRestart_success_one_minus_inv_factor
    {n h m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) :
    (factor - 1) * n ^ (factor * (2 * (n * m) + n * (m * (2 * h - 1)))) ≤
      factor * successCount (multiLitGapCandidateRestartStep ring P L (by omega))
      (.active (.round (allRaceCandidateDrainState ring (by omega))))
      (factor * (2 * (n * m) + n * (m * (2 * h - 1)))) := by
  have hc := CandidateRearmSpec.allRace_success_one_minus_inv_factor
    (multiLitGapDenialRearmSpec L (by omega)) ring hm P hn (factor := factor)
  simpa only [multiLitGapCandidateRestartStep, multiLitGapDenialRearmSpec,
    multiLitGapPotential_allDeclare] using hc

/-! Receipt view and terminal configurations. -/
def litIsDischarged {h : Nat} : LitGapState h → Bool
  | .delivered => true
  | _ => false

def litIsDenying {h : Nat} : LitGapState h → Bool
  | .declareAt _ _ => false
  | _ => true

def litRearmedOf {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → LitGapState h) (i : Fin m) : Bool :=
  litIsDischarged (gap i) && litIsDenying (gap (ring.leftNeighbor i))

theorem litIsDischarged_iff_hops {h : Nat} (s : LitGapState h) :
    litIsDischarged s = true ↔ s.hops = 0 := by
  cases s <;> simp [litIsDischarged, LitGapState.hops] <;> omega

theorem litIsDischarged_localStep {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (e : Fin n) (hs : litIsDischarged s = true) :
    litIsDischarged (s.localStep edgeAt e) = true := by
  cases s <;> simp_all [litIsDischarged, LitGapState.localStep, LitGapState.advanceEdge]

theorem litIsDenying_localStep {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : LitGapState h) (e : Fin n) (hs : litIsDenying s = true) :
    litIsDenying (s.localStep edgeAt e) = true := by
  cases s with
  | declareAt j hj => simp [litIsDenying] at hs
  | delivered => rfl
  | replyAt j hj =>
    simp only [LitGapState.localStep, LitGapState.advanceEdge]
    split
    · simp only [LitGapState.advance]
      split <;> rfl
    · rfl

theorem litRearmedOf_multiLitLocalStep {n h m : Nat} (ring : DirectedRing m)
    (L : GapLayout n h m) (gap : Fin m → LitGapState h) (e : Fin n) (i : Fin m)
    (hi : litRearmedOf ring gap i = true) :
    litRearmedOf ring (multiLitLocalStep L gap e) i = true := by
  have hb : litIsDischarged (gap i) = true ∧ litIsDenying (gap (ring.leftNeighbor i)) = true :=
    Bool.and_eq_true_iff.mp hi
  exact Bool.and_eq_true_iff.mpr ⟨litIsDischarged_localStep _ _ e hb.1,
    litIsDenying_localStep _ _ e hb.2⟩

/-- A missing incident old receipt always certifies positive carrier debt. -/
theorem exists_hops_pos_of_not_litRearmed {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → LitGapState h) (i : Fin m) (hi : litRearmedOf ring gap i = false) :
    ∃ g, 0 < (gap g).hops := by
  by_cases hr : litIsDischarged (gap i) = true
  · have hl : litIsDenying (gap (ring.leftNeighbor i)) = false := by
      simpa [litRearmedOf, hr] using hi
    refine ⟨ring.leftNeighbor i, ?_⟩
    cases he : gap (ring.leftNeighbor i) <;> simp_all [litIsDenying, LitGapState.hops] <;> omega
  · refine ⟨i, ?_⟩
    have hn : (gap i).hops ≠ 0 := fun he => hr ((litIsDischarged_iff_hops _).2 he)
    omega

def allLitDischarged (h m : Nat) : Fin m → LitGapState h := fun _ => .delivered

@[simp] theorem litTotalHops_allDischarged (h m : Nat) :
    litTotalHops (allLitDischarged h m) = 0 := by
  simp [litTotalHops, allLitDischarged, LitGapState.hops, ofFn_sum_const]

@[simp] theorem litRearmedOf_allDischarged {h m : Nat} (ring : DirectedRing m) (i : Fin m) :
    litRearmedOf ring (allLitDischarged h m) i = true := rfl

theorem multiLitLocalStep_allDischarged {n h m : Nat} (L : GapLayout n h m) (e : Fin n) :
    multiLitLocalStep L (allLitDischarged h m) e = allLitDischarged h m := rfl

/-! Positive simulation on the frozen uniform ring. -/
open ShortGapLiteralGapRows ShortGapLiteralRingRows

/-- Total phase translation, with malformed positions mapped to delivered.
The clean-domain theorems prove that no fallback branch is used. -/
def ofPhase (R : RFrame) : Phase → LitGapState R.h
  | .prelaunch => .declareAt 0 R.hh
  | .declAt j => if hj : j < R.h then .declareAt j hj else .delivered
  | .replyAt j => if hj : 1 ≤ j ∧ j ≤ R.h - 1 then .replyAt j hj else .delivered
  | .delivered => .delivered

theorem hops_ofPhase (R : RFrame) (p : Phase) (hp : PhaseOk (F0 R) p) :
    (ofPhase R p).hops = phaseDebt (F0 R) p := by
  cases p with
  | prelaunch => rfl
  | delivered => rfl
  | declAt j => simp [ofPhase, hp.2, LitGapState.hops, phaseDebt]
  | replyAt j =>
    have hb : 1 ≤ j ∧ j ≤ R.h - 1 := by have h1 : 1 ≤ j := hp.1; have h2 : j < R.h := hp.2; omega
    simp [ofPhase, hb, LitGapState.hops, phaseDebt]

private theorem fin_eq_val {h : Nat} (a b : Fin h) : a = b ↔ a.val = b.val :=
  ⟨congrArg Fin.val, Fin.ext⟩

/-- The literal Phase clock and the repaired token clock agree on every edge. -/
theorem ofPhase_nextPhase (R : RFrame) (p : Phase) (hp : PhaseOk (F0 R) p) (a : Fin R.h) :
    ofPhase R (nextPhase (F0 R) p a) = LitGapState.localStep (fun j => j) (ofPhase R p) a := by
  apply LitGapState.hops_injective R.hh
  rw [hops_ofPhase R _ (nextPhase_phaseOk (F0 R) p hp a)]
  have ha := a.isLt
  have hh := R.hh
  cases p with
  | prelaunch =>
    by_cases ha0 : a.val = 0 <;> by_cases hh1 : R.h = 1 <;>
      simp (disch := omega) [if_pos, if_neg, dif_pos, nextPhase, phaseDebt, ofPhase,
        LitGapState.localStep, LitGapState.advanceEdge, LitGapState.advance,
        LitGapState.hops, fin_eq_val, ha0, hh1] <;> omega
  | declAt j =>
    have hj0 : 1 ≤ j := hp.1
    have hjh : j < R.h := hp.2
    by_cases haj : a.val = j <;> by_cases hjlast : j + 1 = R.h <;>
      simp (disch := omega) [if_neg, dif_pos, dif_neg, nextPhase, phaseDebt, ofPhase,
        LitGapState.localStep, LitGapState.advanceEdge, LitGapState.advance,
        LitGapState.hops, fin_eq_val, haj, hjlast] <;> omega
  | replyAt j =>
    have hj0 : 1 ≤ j := hp.1
    have hjh : j < R.h := hp.2
    by_cases haj : a.val + 1 = j <;> by_cases hj1 : j = 1 <;>
      simp (disch := omega) [if_pos, if_neg, dif_pos, nextPhase, phaseDebt, ofPhase,
        LitGapState.localStep, LitGapState.advanceEdge, LitGapState.advance,
        LitGapState.hops, fin_eq_val, haj, hj1] <;> omega
  | delivered => rfl

/-- Injectively encoding the local edge changes no transition. -/
theorem localStep_encode {n h : Nat} (f : Fin h → Fin n) (hf : Function.Injective f)
    (s : LitGapState h) (a : Fin h) :
    s.localStep f (f a) = s.localStep (fun j => j) a := by
  have he : ∀ j, f j = f a ↔ j = a := fun j => ⟨fun he => hf he, congrArg f⟩
  unfold LitGapState.localStep
  cases s.advanceEdge <;> simp [he]

/-- A token's useful edge cannot have been removed by the old freeze guard. -/
theorem litAdvance_not_frozen (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (g : Fin R.m) (a : Fin R.h)
    (ha : (ofPhase R (P g)).advanceEdge = some a) :
    ¬ (frozen R (cfgOf R P) (g, a) = true) := by
  have hp := hP g
  cases he : P g with
  | prelaunch =>
    simp only [he, ofPhase, LitGapState.advanceEdge, Option.some.injEq] at ha
    subst a
    apply not_frozen_edge R P g _
    · intro _; simp [joined, he, IsDelivered]
    · intro _; simp [joined, prev_next, he, Compared]
  | delivered => simp [he, ofPhase, LitGapState.advanceEdge] at ha
  | declAt j =>
    rw [he] at hp
    simp only [he, ofPhase, dif_pos hp.2, LitGapState.advanceEdge, Option.some.injEq] at ha
    subst a
    apply not_frozen_edge R P g _
    · intro hz; have := hp.1; simp only at hz; omega
    · intro _; simp [joined, prev_next, he, Compared]
  | replyAt j =>
    rw [he] at hp
    have hb : 1 ≤ j ∧ j ≤ R.h - 1 := by have h1 : 1 ≤ j := hp.1; have h2 : j < R.h := hp.2; omega
    simp only [he, ofPhase, dif_pos hb, LitGapState.advanceEdge, Option.some.injEq] at ha
    subst a
    apply not_frozen_edge R P g _
    · intro _; simp [joined, he, IsDelivered]
    · intro hz; have := hp.1; have := hp.2; simp only at hz; omega

/-- Exact phase-vector simulation, including frozen scheduler stutters. -/
theorem phaseVector_simulates (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (e : Vtx R) :
    (fun g => ofPhase R (nextP R P e g)) =
      multiLitLocalStep (ShortGapOwnerRoundSlice.layout R) (fun g => ofPhase R (P g)) (ShortGapOwnerRoundSlice.encode R e) := by
  funext g
  by_cases hg : g = e.1
  · subst g
    by_cases hfr : frozen R (cfgOf R P) e = true
    · rw [nextP_of_frozen R P e hfr]
      symm
      apply LitGapState.localStep_eq_of_ne
      intro a ha he
      have heq := ShortGapOwnerRoundSlice.encode_injective R he
      have hea : a = e.2 := congrArg Prod.snd heq
      subst a
      exact litAdvance_not_frozen R P hP e.1 e.2 ha hfr
    · rw [nextP_self R P e hfr, ofPhase_nextPhase R (P e.1) (hP e.1) e.2]
      symm
      exact localStep_encode (fun a => ShortGapOwnerRoundSlice.encode R (e.1, a))
        (fun _ _ he => congrArg Prod.snd (ShortGapOwnerRoundSlice.encode_injective R he)) _ e.2
  · have hn : nextP R P e g = P g := by
      by_cases hf : frozen R (cfgOf R P) e = true
      · rw [nextP_of_frozen R P e hf]
      · exact nextP_other R P e hf g hg
    rw [hn]
    symm
    exact multiLitLocalStep_other (ShortGapOwnerRoundSlice.layout R) _ e.1 g hg e.2

open Classical in
/-- A configuration-only projection. On RingClean its value is independent
of the chosen phase witness, proved by the physical per-gap debt readout. -/
noncomputable def tokensLit (R : RFrame) (cfg : Vtx R → Agent) : Fin R.m → LitGapState R.h :=
  if hc : RingClean R cfg then fun g => ofPhase R (hc.choose g) else fun _ => .delivered

theorem tokensLit_cfgOf (R : RFrame) (P : PV R) (hP : ∀ g, PhaseOk (F0 R) (P g)) :
    tokensLit R (cfgOf R P) = fun g => ofPhase R (P g) := by
  classical
  have hc : RingClean R (cfgOf R P) := ⟨P, hP, rfl⟩
  rw [tokensLit, dif_pos hc]
  funext g
  apply LitGapState.hops_injective R.hh
  rw [hops_ofPhase R _ (hc.choose_spec.1 g), hops_ofPhase R _ (hP g)]
  rw [← gapDebt_cfgOf R _ g (hc.choose_spec.1 g), ← gapDebt_cfgOf R P g (hP g),
    ← hc.choose_spec.2]

/-- POSITIVE forward simulation of the actual frozen uniform ring on every
physical scheduler edge. No extra boundary firing is inserted. -/
theorem frozen_step_simulates (R : RFrame) (cfg : Vtx R → Agent)
    (hc : RingClean R cfg) (e : Vtx R) :
    tokensLit R (ringStep R cfg e) =
      multiLitLocalStep (ShortGapOwnerRoundSlice.layout R) (tokensLit R cfg) (ShortGapOwnerRoundSlice.encode R e) := by
  obtain ⟨P, hP, rfl⟩ := hc
  rw [ringStep_cfgOf R P hP e, tokensLit_cfgOf R _ (nextP_phaseOk R P hP e),
    tokensLit_cfgOf R P hP]
  exact phaseVector_simulates R P hP e

/-! Owner-round slice projection: receipts agree, but current-round
cleanliness is absent from the existing Coherent predicate. -/
open ShortGapOwnerRoundSlice ShortGapTwoDenialJoin ShortGapJoinedIncidenceBalance

/-- Same owner-round convention as the prior slice, now in the repaired alphabet. -/
noncomputable def sliceTokensLit (R : RFrame) (q : Nat) (s : SliceState R) :
    Fin R.m → LitGapState R.h := fun g =>
  if s.k g = q then ofPhase R (decode R s.cfg g) else .delivered

noncomputable def piLit (R : RFrame) (q : Nat) (s : SliceState R) :
    PeriodHIncidenceChoice.Configuration R.m × (Fin R.m → LitGapState R.h) :=
  (word R q s, sliceTokensLit R q s)

/-- Removing the spurious boundary hop preserves both receipt readouts. -/
theorem ofPhase_receipts (R : RFrame) (p : Phase) (hp : PhaseOk (F0 R) p) :
    litIsDischarged (ofPhase R p) = isDischarged (phaseToken R p) ∧
    litIsDenying (ofPhase R p) = isDenying (phaseToken R p) := by
  cases p with
  | prelaunch => exact ⟨rfl, rfl⟩
  | delivered => exact ⟨rfl, rfl⟩
  | declAt j => simp [ofPhase, phaseToken, hp.2, litIsDischarged, litIsDenying, isDischarged, isDenying]
  | replyAt j =>
    have hj0 : 1 ≤ j := hp.1
    have hjh : j < R.h := hp.2
    have hb : 1 ≤ j ∧ j ≤ R.h - 1 := by omega
    have hjle : j ≤ R.h := by omega
    rw [ofPhase, dif_pos hb, phaseToken, dif_pos hjle]
    cases j <;> simp_all [litIsDischarged, litIsDenying, isDischarged, isDenying] <;> omega


theorem slice_receipts (R : RFrame) (q : Nat) (s : SliceState R) (hc : Coherent R q s) (g : Fin R.m) :
    litIsDischarged (sliceTokensLit R q s g) = isDischarged (tokens R q s g) ∧
    litIsDenying (sliceTokensLit R q s g) = isDenying (tokens R q s g) := by
  by_cases hk : s.k g = q
  · obtain ⟨p, hp⟩ := hc.oldGap g hk
    simp only [sliceTokensLit, tokens, if_pos hk, decode_of_form R s.cfg g p hp]
    exact ofPhase_receipts R p hp.1
  · simp [sliceTokensLit, tokens, hk, litIsDischarged, litIsDenying, isDischarged, isDenying]

theorem litJoined_iff_k (R : RFrame) (q : Nat) (s : SliceState R)
    (hs : Slice R q s) (hc : Coherent R q s) (i : Fin R.m) :
    litRearmedOf (ring R) (sliceTokensLit R q s) i = true ↔ s.k i = q + 1 := by
  rw [litRearmedOf, (slice_receipts R q s hc i).1,
    (slice_receipts R q s hc ((ring R).leftNeighbor i)).2]
  exact joined_iff_k R q s hs hc i

/-- The prior h=1 clock counterexample is eliminated in the repaired carrier. -/
theorem direct_clock_repaired (R : RFrame) (hh : R.h = 1) :
    ofPhase R (nextPhase (F0 R) .prelaunch ⟨0, R.hh⟩) =
      (ofPhase R .prelaunch).advance := by
  simp [ofPhase, nextPhase, hh, LitGapState.advance]

/-- Two roots and two slots: a Race root is already stuck waiting in the
current cohort. This is permitted by Coherent, which checks old gaps only.
It is NOT claimed reachable from a clean physical current-round start. -/
abbrev residualFrame : RFrame := ⟨2, 2, by decide, by decide, .in0, Or.inr rfl⟩

def residualState (q : Nat) : SliceState residualFrame where
  cfg v := if v.2 = 0 then .root .race .waiting .free else .interior .empty
  k _ := q + 1

private theorem two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi := i.isLt
  have hh : i.val = 0 ∨ i.val = 1 := by omega
  exact hh.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

theorem residual_slice (q : Nat) : Slice residualFrame q (residualState q) := fun _ => Or.inr rfl

theorem residual_coherent (q : Nat) : Coherent residualFrame q (residualState q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨.race, .waiting, .free, by simp [residualState]⟩
  · intro i; simp [residualState, ShortGapLiteralRingRows.joinA]
  · intro i hi; change q + 1 = q at hi; omega
  · intro i hi; change q + 1 = q at hi; omega
  · intro i hi; change q + 1 = q at hi; omega
  · intro i _; simp [tokens, residualState, isDenying]
  · rintro ⟨j, hj⟩; change q + 1 = q at hj; omega

/-- The outgoing root/empty-slot row stutters when cw=waiting, even though
the root is still Race. Thus the physical word does not resolve. -/
theorem residual_step (q : Nat) :
    liftedStep residualFrame (residualState q) (rootV residualFrame 0) = residualState q := by
  have hc : ringStepU residualFrame (residualState q).cfg (rootV residualFrame 0) =
      (residualState q).cfg := by
    funext v
    obtain ⟨i,a⟩ := v
    rcases two_cases i with rfl | rfl <;> rcases two_cases a with rfl | rfl <;>
      simp [ringStepU, incident, rawAt, joinTick, residualState, rn,
        row, ShortGapLiteralRingRows.joinA]
  have hk : (liftedStep residualFrame (residualState q) (rootV residualFrame 0)).k =
      (residualState q).k := by
    funext i
    rcases two_cases i with rfl | rfl <;>
      simp [liftedStep, fires, incident, rawAt, residualState, rn, row, joinReady]
  exact (congrArg (fun cfg => SliceState.mk cfg
    (liftedStep residualFrame (residualState q) (rootV residualFrame 0)).k) hc).trans
      (congrArg (SliceState.mk (residualState q).cfg) hk)

/-- The missing next-cohort owner invariant exposed by this counterexample.
This condition alone is not advertised as sufficient for full simulation. -/
def CurrentRaceReady (R : RFrame) (q : Nat) (s : SliceState R) : Prop :=
  ∀ i, s.k i = q + 1 → (s.cfg (rootV R i)).choice = some .race →
    (s.cfg (rootV R i)).cwPort = some .toSend

theorem residual_not_currentRaceReady (q : Nat) : ¬ CurrentRaceReady residualFrame q (residualState q) := by
  intro hc
  have he := hc 0 rfl (by simp [residualState, Agent.choice])
  simp [residualState, Agent.cwPort] at he

/-- Exact remaining discrepancy: the pre-step joined mask is true, so the
abstract incidence step resolves root 0 to out1, while the literal row stutters. -/
theorem residual_word_mismatch (q : Nat) :
    (piLit residualFrame q (liftedStep residualFrame (residualState q) (rootV residualFrame 0))).1 0 = .race ∧
    joinedIncidenceStep (placement residualFrame)
      (litRearmedOf (ring residualFrame) (sliceTokensLit residualFrame q (residualState q)))
      (word residualFrame q (residualState q)) (encode residualFrame (rootV residualFrame 0)) 0 = .out1 := by
  rw [residual_step]
  constructor
  · simp [piLit, word, residualState, abstractChoice]
  · simp [joinedIncidenceStep, litRearmedOf, sliceTokensLit, residualState,
      litIsDischarged, litIsDenying, word, abstractChoice, incidenceStep, placement]

/-- NEGATIVE retry under the exact previously defined Coherent hypotheses.
The carrier clock is now correct; what remains missing is current-cohort
cleanliness/owner locking. Both states stay in the slice and satisfy Coherent.
This theorem does not refute simulation under a stronger reachable invariant. -/
theorem unfrozen_slice_residual_mismatch (q : Nat) :
    let R := residualFrame
    let s := residualState q
    let e := rootV R 0
    Coherent R q s ∧ Slice R q s ∧
    Coherent R q (liftedStep R s e) ∧ Slice R q (liftedStep R s e) ∧
    piLit R q (liftedStep R s e) ≠
      (joinedIncidenceStep (placement R) (litRearmedOf (ring R) (sliceTokensLit R q s))
        (word R q s) (encode R e), multiLitLocalStep (layout R) (sliceTokensLit R q s) (encode R e)) := by
  refine ⟨residual_coherent q, residual_slice q, ?_, ?_, ?_⟩
  · rw [residual_step]; exact residual_coherent q
  · rw [residual_step]; exact residual_slice q
  · intro he
    have hw := congrArg (fun z => z.1 (0 : Fin 2)) he
    simp only at hw
    obtain ⟨hl, hr⟩ := residual_word_mismatch q
    rw [hl, hr] at hw
    cases hw

#print axioms multiLitGap_natBellmanSuperSolution
#print axioms multiLitGapCandidateRestart_truncatedCost_le
#print axioms frozen_step_simulates
#print axioms unfrozen_slice_residual_mismatch
#print axioms litJoined_iff_k

end ShortGapDenialTransportLiteral


