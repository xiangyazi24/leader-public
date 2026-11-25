import Leader.L4.ShortMISSheetParked
import Leader.L4.ShortGuardedNOR
import Leader.L4.ShortFiveGuardTour

namespace L4.ShortMISPublicationLift
open AllSizeProtocol PhysicalCustody PhysicalShortSheet
open ShortMISEngine ShortResetChart ShortResetCycle ShortResetWatch
open MISByteCodec ShortResetFlow ShortResetMIS1Ring ShortResetForwardH2
open ShortMISLift (Geometry)
open ShortMISSheetParked

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {s n : Nat}

@[simp] theorem view_byte (P : Params s n) (x : Raw s n) (i : Fin n) :
    (view P x i).mis1=P.byte x i := rfl

theorem n_large (G : Geometry s n) : 5≤n := by
  have A := G.P.Bpos
  have B := G.seven
  omega

open ReportStaticSpacing (Lower)

-- CHECK: ShortH2Final.lean: selected_readout; ShortGuardedNOR.lean:
-- observe, classifyFixed, fixed_some, raw_step_conditional.
theorem observe_rep (P : Params s n) (x : Raw s n) :
    ShortGuardedNOR.observe (h:=P.h) (view P x) =
      ShortMISLift.observe P x := by
  funext i
  exact ShortH2Final.selected_readout (P.byte x i.val)

theorem observe_step_rep (P : Params s n) (x : Raw s n)
    (X : Cached P x) (e : Fin n) :
    ShortGuardedNOR.observe (h:=P.h) (rawNext s (view P x) e) =
      ShortMISLift.observe P (rawNext s x e) := by
  funext i
  change ShortReaderMIS1.selectedValue
      (rawNext s (view P x) e i.val).mis1 = _
  rw [view_next P x X e]
  exact ShortH2Final.selected_readout _

-- CHECK: ShortMISLift.lean: classify; ShortPublicationClassifier.lean:
-- classify (old responder header and actual selector flip).
theorem classify_rep (P : Params s n) (x : Raw s n)
    (X : Cached P x) (e : Fin n) :
    ShortGuardedNOR.classifyFixed P.h (view P x) e =
      ShortMISLift.classify P x e := by
  by_cases H : P.h (rightNeighbor e) = true
  · by_cases F : (P.byte (rawNext s x e) (rightNeighbor e))[92] =
        (P.byte x (rightNeighbor e))[92] <;>
      simp [ShortGuardedNOR.classifyFixed, ShortPublicationClassifier.classify,
        ShortMISLift.classify, view_header, view_byte, view_next P x X e, H, F]
  · simp [ShortGuardedNOR.classifyFixed, ShortPublicationClassifier.classify,
      ShortMISLift.classify, view_header, H]

-- Actual guard, actual old initiator byte, actual old responder byte.
-- CHECK: ShortPublicationClassifier.lean: recorded_guard.
theorem recorded_guard_on (P : Params s n) (x : Raw s n)
    (X : Cached P x) (e : Fin n) (i : Lower P.h)
    (E : ShortMISLift.classify P x e = some i) :
    i.val = rightNeighbor e ∧ P.h i.val = true ∧
      ShortResetRow.selectorGuard (P.h e) (P.byte x e) (P.byte x i.val) := by
  have V := E
  rw [← classify_rep P x X e] at V
  obtain ⟨R,H,B⟩ := ShortPublicationClassifier.recorded_guard
    (view P x) e i.val ((ShortGuardedNOR.fixed_some _ _ _).mp V)
  exact ⟨R.symm,i.property,by simpa only [view_header,view_byte] using B⟩

-- CHECK: ShortBankProjection.lean: selector_stutter;
-- ShortPublicationClassifier.lean: unrecorded_selector_stutters.
theorem notPublisher_stutters (P : Params s n) (x : Raw s n)
    (X : Cached P x) (e : Fin n) (i : Lower P.h)
    (H : ShortMISLift.classify P x e ≠ some i) :
    ShortMISLift.observe P (rawNext s x e) i =
      ShortMISLift.observe P x i := by
  have Hd : ShortResetMIS1Ring.header (view P x) i.val = true :=
    (view_header P x _).trans i.property
  have no : ShortPublicationClassifier.classify (view P x) e ≠ some i.val := by
    intro S
    apply H
    rw [← classify_rep P x X e]
    exact (ShortGuardedNOR.fixed_some _ _ _).mpr S
  have K := ShortBankProjection.selector_stutter (view P x) e i.val Hd
    (ShortPublicationClassifier.unrecorded_selector_stutters
      (view P x) e i.val Hd no)
  rw [view_next P x X e,view_byte,ShortH2Final.selected_readout,
    ShortH2Final.selected_readout] at K
  exact K

theorem auth_none (P : Params s n) (x : Raw s n) (X : Cached P x)
    (e : Fin n) (H : ShortMISLift.classify P x e = none) :
    ShortMISLift.observe P (rawNext s x e) = ShortMISLift.observe P x := by
  funext i
  apply notPublisher_stutters P x X e i
  rw [H]
  simp

-- The exact local protected-read obligation left by the MIS1 producer.
-- This is not an assumption about all bytes or about the NEXT state.
def ProtectedAt (G : Geometry s n) (x : Raw s n) (e : Fin n)
    (i : Lower G.P.h) : Prop :=
  ShortPublicationClassifier.FromProtectedBits
    (ShortMISLift.observe G.P x (G.ring.left i))
    (ShortMISLift.observe G.P x (G.ring.right i))
    (oldK (G.P.h e) (G.P.byte x e) 0).payload

theorem auth_if_protected (G : Geometry s n) (x : Raw s n)
    (e : Fin n) (X : Cached G.P x)
    (A : ∀ i, ShortMISLift.classify G.P x e = some i →
      ProtectedAt G x e i) :
    ShortMISLift.observe G.P (rawNext s x e) =
      match ShortMISLift.classify G.P x e with
      | none => ShortMISLift.observe G.P x
      | some i => ShortNORCover.update G.ring (ShortMISLift.observe G.P x) i := by
  have N := n_large G
  have K := ShortGuardedNOR.raw_step_conditional G.ring (view G.P x) e
    (edge_sep (by omega) e) (view_header G.P x) (by
      intro i E
      rw [classify_rep G.P x X e] at E
      rw [observe_rep G.P x,view_header,view_byte]
      exact A i E)
  rw [observe_step_rep G.P x X e,observe_rep G.P x,
      classify_rep G.P x X e] at K
  cases E : ShortMISLift.classify G.P x e <;> simpa only [E] using K

-- CHECK: ShortPublicationClassifier.lean: guard_recorded;
-- ShortGuardedNOR.lean: fixed_some.
theorem guard_classified_on (P : Params s n) (x : Raw s n)
    (X : Cached P x) (e : Fin n) (S : e ≠ rightNeighbor e)
    (H : P.h (rightNeighbor e) = true)
    (A : ShortResetRow.selectorGuard (P.h e) (P.byte x e)
      (P.byte x (rightNeighbor e))) :
    ShortMISLift.classify P x e =
      some (⟨rightNeighbor e,H⟩ : Lower P.h) := by
  rw [← classify_rep P x X e]
  apply (ShortGuardedNOR.fixed_some _ _ _).mpr
  exact ShortPublicationClassifier.guard_recorded (view P x) e S
    ((view_header P x _).trans H)
    (by simpa only [view_header,view_byte] using A)

-- CHECK: ShortNORCover.lean:128–136, publications.
theorem publication_of_prefix (P : Params s n) (i : Lower P.h)
    (x : Raw s n) (lead tail : List (Fin n)) (e : Fin n)
    (H : ShortMISLift.classify P (rawRun x lead) e = some i) :
    i ∈ ShortNORCover.publications (rawNext s) (ShortMISLift.classify P)
      x (lead ++ e :: tail) := by
  induction lead generalizing x with
  | nil =>
    change ShortMISLift.classify P x e=some i at H
    simp [ShortNORCover.publications,H]
  | cons a lead ih =>
    have I := ih (rawNext s x a) H
    cases K : ShortMISLift.classify P x a <;>
      simp [ShortNORCover.publications,K,I]

-- CHECK: ShortMISEngine.lean: Cached, cached_closed.
theorem cached_run_on (P : Params s n) (x : Raw s n)
    (X : Cached P x) (w : List (Fin n)) :
    Cached P (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih =>
    exact ih (rawNext s x e) (P.cached_closed x e X)

-- CHECK: ShortMISLift.lean:127–146, family_target, chart_gate;
-- ShortFiveGuardTour.lean: Layout.
theorem target_layout (G : Geometry s n) (A : 2 ≤ G.A)
    (i : Lower G.P.h) : ShortFiveGuardTour.Layout (G.family i 2) := by
  let C := G.family i 2
  let r := G.rootAt (G.start i) 2
  have Ha : C.a = G.width r := rfl
  have Hb : C.b = G.width (G.ring.right r) := rfl
  have a := (G.width_spec r).1
  have b := (G.width_spec (G.ring.right r)).1
  have a2 : 2 ≤ C.a := by omega
  have b2 : 2 ≤ C.b := by omega
  have room := (G.P.chart_gate C).2.1
  have P0 : C.route.port (C.a-1) = 0 := by
    change ShortResetChart.lane C.a C.b (C.a-1) = 0
    simp [ShortResetChart.lane,show C.a-1<C.a by omega]
  have P1 : C.route.port C.a = 1 := by
    change ShortResetChart.lane C.a C.b C.a = 1
    simp [ShortResetChart.lane,show C.a<C.a+C.b by omega]
  have H : G.P.h (ShortFiveGuardTour.centre C) = true := by
    change G.P.h (nextAt C.root C.a) = true
    rw [(G.family_target i).2.2]
    exact i.property
  exact ⟨a2,room,P0,P1,H⟩

def wordPre {h : Fin n → Bool} (C : Chart h) : List (Fin n) :=
  (((ShortFiveWinningWord.tour C ++
      ShortFiveWinningWord.admit C C.a) ++
      ShortFiveWinningWord.tour C) ++
      ShortFiveWinningWord.tour C) ++ ShortFiveWinningWord.tour C

def wordLead {h : Fin n → Bool} (C : Chart h) : List (Fin n) :=
  wordPre C ++ ShortFiveGuardTour.tourPrefix C (C.a-1)

-- CHECK: ShortFiveGuardTour.lean: tour_split, ingress_right;
-- mis1_fenced_word_actual_publication (last part of file).
theorem word_split_on (G : Geometry s n) (A : 2 ≤ G.A)
    (i : Lower G.P.h) :
    ∃ tail : List (Fin n), G.word i =
      wordLead (G.family i 2) ++
        ShortFiveGuardTour.ingress (G.family i 2) :: tail := by
  let C := G.family i 2
  obtain ⟨tail,T⟩ := ShortFiveGuardTour.tour_split C (target_layout G A i)
  have W : G.word i = wordPre C ++ ShortFiveWinningWord.tour C := by
    simp [ShortMISLift.Geometry.word,ShortFiveWinningWord.winningWord,
      wordPre,C,List.append_assoc]
  refine ⟨tail,?_⟩
  calc
    G.word i = wordPre C ++ ShortFiveWinningWord.tour C := W
    _ = _ := by rw [T]; simp [wordLead,C,List.append_assoc]

def GuardedWordAt (G : Geometry s n) (i : Lower G.P.h)
    (x : Raw s n) : Prop :=
  let C := G.family i 2
  let e := ShortFiveGuardTour.ingress C
  let z := rawRun x (wordLead C)
  ShortResetRow.selectorGuard (G.P.h e) (G.P.byte z e)
    (G.P.byte z (rightNeighbor e))

theorem win_if_guard (G : Geometry s n) (A : 2 ≤ G.A)
    (i : Lower G.P.h) (x : Raw s n) (X : Cached G.P x)
    (H : GuardedWordAt G i x) :
    i ∈ ShortNORCover.publications (rawNext s) (ShortMISLift.classify G.P)
      x (G.word i) := by
  let C := G.family i 2
  let e := ShortFiveGuardTour.ingress C
  let z := rawRun x (wordLead C)
  have L := target_layout G A i
  have R : rightNeighbor e = i.val :=
    (ShortFiveGuardTour.ingress_right C L).trans (G.family_target i).2.2
  have Hr : G.P.h (rightNeighbor e) = true := R.symm ▸ i.property
  have Y : Cached G.P z := cached_run_on G.P x X (wordLead C)
  have N := n_large G
  have K := guard_classified_on G.P z Y e (edge_sep (by omega) e) Hr H
  have E : (⟨rightNeighbor e,Hr⟩ : Lower G.P.h) = i := Subtype.ext R
  rw [E] at K
  obtain ⟨tail,W⟩ := word_split_on G A i
  rw [W]
  exact publication_of_prefix G.P i x (wordLead C) tail e K

end L4.ShortMISPublicationLift
