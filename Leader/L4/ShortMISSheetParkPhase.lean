import Leader.L4.ShortMISSheetRank
import Leader.L4.ShortMISSheetReset

namespace L4.ShortMISSheetParkPhase
open AllSizeProtocol PhysicalCustody PhysicalShortSheet MISByteCodec ShortMISEngine
open ShortResetCycle ShortResetWatch ShortResetChart ShortMISLift
open ShortMISSheetParked ShortMISSheetRank ShortMISSheetReset
open ShortControllerEntrance ShortPhaseRank ShortInheritedRankParam

variable {s n : Nat}
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem step_complete (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (e : Fin n) :
    ShortResetCycle.Complete C (rawNext s (view P x) e) ↔ ShortResetCycle.Complete C (view P (rawNext s x e)) := by
  simp only [ShortResetCycle.Complete,ShortResetForwardH2.bits,view_next P x X e]
  rfl

private def phaseMode (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (m : Option Stage) (e : Fin n) : Option Stage :=
  ShortSimulLocal.modeNext C (view P x) m e

private def phaseValid (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (m : Option Stage) : Prop :=
  ShortFiveParked.ValidReleased C (view P x) m

private def phaseDone (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (m : Option Stage) : Prop :=
  m=some .done ∧ ShortMISLift.Parked P C x

private def phaseScore (G : Geometry s n) (C : Chart G.P.h)
    (x : Raw s n) (m : Option Stage) : Nat :=
  ShortSimulLocalParam.score C G.D (view G.P x) m

private theorem phase_advance (G : Geometry s n) (C : Chart G.P.h)
    (x : Raw s n) (m : Option Stage) (e : Fin n) (X : Cached G.P x)
    (V : phaseValid G.P C x m) :
    phaseDone G.P C (rawNext s x e) (phaseMode G.P C x m e) ∨
    phaseValid G.P C (rawNext s x e) (phaseMode G.P C x m e) := by
  cases m with
  | none =>
    change _ ∨ phaseValid G.P C (rawNext s x e) (phaseMode G.P C x none e)
    by_cases I : ShortActualIssueClock.Issuable C (view G.P x) ∧
        e=RearTrace.predecessor C.root
    · have eq : phaseMode G.P C x none e=some (.fwd 0) := if_pos I
      rw [eq]
      apply Or.inr
      have A := actual_issue G.P C x X I.1 e I.2
      exact ⟨⟨by decide,A⟩,ShortResetReleased.released_at_issue C _⟩
    · have eq : phaseMode G.P C x none e=none := if_neg I
      rw [eq]
      exact .inr ⟨trivial,trivial⟩
  | some st =>
    obtain ⟨A,R⟩ := actual_step G.P C x X e st V.1.1 V.1.2 V.2
    change phaseDone G.P C (rawNext s x e) (some (nextStage C e st)) ∨
      phaseValid G.P C (rawNext s x e) (some (nextStage C e st))
    by_cases D : nextStage C e st=.done
    · rw [D] at A R ⊢
      exact .inl ⟨rfl,⟨A,fun k K H => R k K H trivial⟩⟩
    · exact .inr ⟨⟨D,A⟩,R⟩

private theorem score_step_rep (G : Geometry s n) (C : Chart G.P.h)
    (x : Raw s n) (X : Cached G.P x) (e : Fin n) (m : Option Stage) :
    ShortSimulLocalParam.score C G.D (rawNext s (view G.P x) e) m =
      phaseScore G C (rawNext s x e) m := by
  cases m with
  | none =>
    simp only [phaseScore,ShortSimulLocalParam.score,ShortSimulLocalParam.seeking,
      ShortActualIssueClock.Issuable,view_next G.P x X e,
      view_project,view_next_project G.P C x X]
    rfl
  | some st => rfl

private theorem stage_drop {h : Fin n→Bool} (C : Chart h) (st : Stage)
    (valid : match st with | .done => False | .fwd k | .rev k => k<C.L) :
    ∃ e∈watch C, debt C.L (nextStage C e st)<debt C.L st := by
  cases st with
  | done => exact False.elim valid
  | fwd i =>
    change i<C.L at valid
    refine ⟨nextAt C.root i,(mem_watch C _).mpr (.inr ⟨i,valid,rfl⟩),?_⟩
    by_cases H : i+1<C.L
    · simp only [nextStage,if_true,if_pos H,debt]; omega
    · simp only [nextStage,if_true,if_neg H,debt]; omega
  | rev i =>
    cases i with
    | zero =>
      exact ⟨RearTrace.predecessor C.root,ShortSimulLocal.door_mem C,
        by simp [nextStage,debt,RearTrace.right_predecessor]⟩
    | succ j =>
      change j+1<C.L at valid
      exact ⟨nextAt C.root j,(mem_watch C _).mpr (.inr ⟨j,by omega,rfl⟩),
        by simp [nextStage,debt]⟩

private theorem phase_nominate (G : Geometry s n) (C : Chart G.P.h)
    (x : Raw s n) (m : Option Stage) (X : Cached G.P x)
    (V : phaseValid G.P C x m) :
    ∃ e∈watch C, phaseScore G C (rawNext s x e) (phaseMode G.P C x m e) <
      phaseScore G C x m := by
  cases m with
  | none =>
    by_cases I : ShortActualIssueClock.Issuable C (view G.P x)
    · let d := RearTrace.predecessor C.root
      refine ⟨d,ShortSimulLocal.door_mem C,?_⟩
      have Q : phaseMode G.P C x none d=some (.fwd 0) := if_pos ⟨I,rfl⟩
      rw [Q]
      change 2*C.L-0 < ShortSimulLocalParam.seeking C G.D (view G.P x)
      unfold ShortSimulLocalParam.seeking
      rw [if_pos I]
      omega
    · let pr := ShortSheetRankClock.project (s:=s) G.P.sheet C
      have off : pc (rootByte C (pr x))≠8 := I
      obtain ⟨e,W,drop⟩ :
          ∃ e∈watch C, chartRank C (railCap G.D) (rail C G.D) (pr (rawNext s x e)) <
            chartRank C (railCap G.D) (rail C G.D) (pr x) := by
        have room : 5≤n := by
          obtain ⟨i,I⟩ := G.P.hh
          obtain ⟨k,K,J⟩ := G.P.gap i I
          have := J.positive
          have := G.seven
          omega
        rcases (rank_rows G.P C room G.D (G.chart_small C)).descent x X off with ⟨e,W,D⟩|⟨e,W,S,D⟩
        · exact ⟨e,W,chartRank_phase_drop C _ _ _ _
            (rail_cap C G.D (G.chart_small C) _) D⟩
        · exact ⟨e,W,chartRank_rail_drop C _ _ _ _ S D⟩
      refine ⟨e,W,?_⟩
      have Q : phaseMode G.P C x none e=none := if_neg (fun H=>I H.1)
      rw [Q]
      change ShortSimulLocalParam.seeking C G.D (view G.P (rawNext s x e)) <
        ShortSimulLocalParam.seeking C G.D (view G.P x)
      unfold ShortSimulLocalParam.seeking
      rw [if_neg I,view_project,view_project]
      -- CHECK: ShortSimulLocalParam.lean:15–23. pr is the exact
      -- projection, including the joined PC fields. The rank is Nat.
      change 2*C.L+1+(if ShortActualIssueClock.Issuable C (view G.P (rawNext s x e))
        then 0 else chartRank C (railCap G.D) (rail C G.D) (pr (rawNext s x e))) <
        2*C.L+1+chartRank C (railCap G.D) (rail C G.D) (pr x)
      split <;> omega
  | some st =>
    exact stage_drop C st (by
      cases st
      · exact V.1.2.1
      · exact V.1.2.1
      · exact V.1.1 rfl)

-- CHECK: ShortFiveParkedParam.lean:34–54; Phase fields
-- RestartRankClock.lean:5–24. ValidReleased on the representative
-- is the exact old Valid (not an H2Ready assumption).
def parkPhase (G : Geometry s n) (C : Chart G.P.h) :
    RestartRankClock.Phase (rawNext s) (Cached G.P) (Option Stage)
      (ShortSimulLocalParam.phaseCap G.D) where
  init := none
  advance := phaseMode G.P C
  done := phaseDone G.P C
  goal := ShortMISLift.Parked G.P C
  valid := phaseValid G.P C
  score := phaseScore G C
  watch := watch C
  init_valid _ _ := ⟨trivial,trivial⟩
  next_valid := phase_advance G C
  done_goal _ _ D := D.2
  score_pos x m _ V := (ShortSimulLocalParam.score_bounds C G.D
    (G.chart_small C) (view G.P x) m V.1).1
  score_lt x m _ V := (ShortSimulLocalParam.score_bounds C G.D
    (G.chart_small C) (view G.P x) m V.1).2
  nominate x m X V := by
    obtain ⟨e,W,D⟩ := phase_nominate G C x m X V
    exact ⟨e,W,.inr D⟩
  idle x m e X V W := by
    obtain ⟨A,B⟩ := ShortSimulLocalParam.idle C G.D
      (view G.P x) m e V.1 W
    constructor
    · intro D
      apply A
      have K : ShortResetCycle.Complete C (view G.P (rawNext s x e)) := D.2.1
      exact ⟨D.1,(step_complete G.P C x X e).mpr K⟩
    · have eq := score_step_rep G C x X e (phaseMode G.P C x m e)
      change phaseScore G C (rawNext s x e) (phaseMode G.P C x m e) ≤ phaseScore G C x m
      rw [←eq]
      exact Nat.le_of_eq B

theorem parkGoal (G : Geometry s n) (C : Chart G.P.h) :
    (parkPhase G C).goal=ShortMISLift.Parked G.P C := rfl

theorem parkWatch (G : Geometry s n) (C : Chart G.P.h) :
    (parkPhase G C).watch=watch C := rfl

#print axioms parkPhase
#print axioms parkGoal
#print axioms parkWatch

end L4.ShortMISSheetParkPhase
