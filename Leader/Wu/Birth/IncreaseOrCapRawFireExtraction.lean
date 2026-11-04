import Leader.Wu.Birth.IncreaseOrCapRawTerminalBounds
import Leader.Wu.Birth.IncreaseOrCapCarrierBridge

namespace BirthPhaseB3RawFireExtraction

open PPLL PPLLRepair
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthShortDoneTerminalPassiveLocal3Rotation

set_option autoImplicit false
set_option Elab.async false

variable {n psi kappa tau : Nat}

/-- A net terminal increase along a raw word contains a first strict step. -/
private theorem first_strict_terminal_step
    {n : Nat} (hfit : 2 < n) (cap : Nat)
    (C : Fin n -> AgentState 2) (es : List (Fin n))
    (hc : (C (BirthPhaseB3RawTerminalBounds.p1 hfit)).count <= cap)
    (hinc : (C (BirthPhaseB3RawTerminalBounds.p1 hfit)).count <
      (rawRun hfit (by decide : 2 <= 2) cap C es
        (BirthPhaseB3RawTerminalBounds.p1 hfit)).count) :
    exists pre e post,
      es = pre ++ (e :: post) /\
      (let S := rawRun hfit (by decide : 2 <= 2) cap C pre
       (S (BirthPhaseB3RawTerminalBounds.p1 hfit)).count <
         (rawStep hfit (by decide : 2 <= 2) cap S e
           (BirthPhaseB3RawTerminalBounds.p1 hfit)).count) := by
  induction es generalizing C with
  | nil =>
      simp only [rawRun] at hinc
      omega
  | cons e es ih =>
      have hs := BirthPhaseB3RawTerminalBounds.rawStep_terminal_bounds
        hfit cap C e hc
      by_cases hhead :
          (C (BirthPhaseB3RawTerminalBounds.p1 hfit)).count <
            (rawStep hfit (by decide : 2 <= 2) cap C e
              (BirthPhaseB3RawTerminalBounds.p1 hfit)).count
      · refine ⟨[], e, es, rfl, ?_⟩
        simpa only [rawRun] using hhead
      · have heq :
          (C (BirthPhaseB3RawTerminalBounds.p1 hfit)).count =
            (rawStep hfit (by decide : 2 <= 2) cap C e
              (BirthPhaseB3RawTerminalBounds.p1 hfit)).count := by
          have hmono := hs.1
          omega
        have htail :
          (rawStep hfit (by decide : 2 <= 2) cap C e
              (BirthPhaseB3RawTerminalBounds.p1 hfit)).count <
            (rawRun hfit (by decide : 2 <= 2) cap
              (rawStep hfit (by decide : 2 <= 2) cap C e) es
              (BirthPhaseB3RawTerminalBounds.p1 hfit)).count := by
          have h := hinc
          simp only [rawRun] at h
          omega
        rcases ih
            (rawStep hfit (by decide : 2 <= 2) cap C e)
            hs.2.2.1 htail with
          ⟨pre, e', post, hpre, hstrict⟩
        refine ⟨e :: pre, e', post, ?_, ?_⟩
        · simpa only [List.cons_append] using congrArg (List.cons e) hpre
        · simpa only [rawRun] using hstrict

/-- Stage-A's named raw-fire extraction gap. -/
theorem dirtySuccessRawFireExtraction
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor) :
    BirthPhaseB3BridgeStageA.DirtySuccessRawFireExtraction
      hpsi h2 hn ring anchor x := by
  unfold BirthPhaseB3BridgeStageA.DirtySuccessRawFireExtraction
  intro u hu
  have hfit : 2 < n := by omega
  have hdirty :
      BirthWaitClockMass.DirtyMass.DirtyIncreaseWithin
        (w := 2) (n := n) (by decide : 2 <= 2) hfit kappa
        (BirthPhaseB3DirtySuccess.projectedSeed
          hpsi h2 hn ring anchor x)
        (unrotateWord ring anchor u) := by
    unfold BirthPhaseB3DirtySuccess.DirtySuccess at hu
    unfold BirthPhaseB3DirtySuccess.dirtySuccessBit at hu
    split at hu
    · assumption
    · simp at hu
  rcases hdirty with ⟨pre, post, hword, hnet⟩
  let C0 := BirthPhaseB3DirtySuccess.projectedSeed
    hpsi h2 hn ring anchor x
  have hp0 :
      BirthPhaseB3RawTerminalBounds.p0 hfit =
        BirthShortDoneTerminalPassiveLocal3.p0 hn := by
    apply Fin.ext
    rfl
  have hp1 :
      BirthPhaseB3RawTerminalBounds.p1 hfit =
        BirthShortDoneTerminalPassiveLocal3.p1 hn := by
    apply Fin.ext
    rfl
  have hterminal :
      site hfit (BirthWaitClockMass.Line.last (by decide : 2 <= 2)) =
        BirthPhaseB3RawTerminalBounds.p1 hfit := by
    apply Fin.ext
    rfl
  change
    (C0 (site hfit (BirthWaitClockMass.Line.last (by decide : 2 <= 2)))).count <
      (rawRun hfit (by decide : 2 <= 2) kappa C0 pre
        (site hfit (BirthWaitClockMass.Line.last (by decide : 2 <= 2)))).count at hnet
  rw [hterminal] at hnet
  have hc0 :
      (C0 (BirthPhaseB3RawTerminalBounds.p1 hfit)).count <= kappa := by
    have hx := x.2
    unfold BirthPhaseWait2BlockProgress.Carrier at hx
    rw [hp1]
    exact Nat.le_of_lt (by
      simpa [C0, BirthPhaseB3DirtySuccess.projectedSeed,
        BirthPhaseWait2BlockProgress.shortCountAt,
        BirthWaitPassive.raw, BoundedAgentState.erase] using hx.2)
  rcases first_strict_terminal_step hfit kappa C0 pre hc0 hnet with
    ⟨rpre, e, rpost, hpre, hstrict⟩
  have hcap :=
    (BirthPhaseB3RawTerminalBounds.rawRun_terminal_bounds
      hfit kappa C0 rpre hc0).2.2
  have hedge :=
    BirthPhaseB3RawTerminalBounds.rawStep_terminal_strict_only_p0
      hfit kappa
      (rawRun hfit (by decide : 2 <= 2) kappa C0 rpre)
      e hcap hstrict
  unfold BirthPhaseB3BridgeStageA.RawWidthTwoServiceFire
  refine ⟨rpre, rpost ++ post, ?_, ?_⟩
  · calc
      unrotateWord ring anchor u = pre ++ post := hword
      _ = (rpre ++ (e :: rpost)) ++ post := by rw [hpre]
      _ = rpre ++ (e :: (rpost ++ post)) := by
        simp only [List.append_assoc, List.cons_append]
      _ = rpre ++
          (BirthShortDoneTerminalPassiveLocal3.p0 hn ::
            (rpost ++ post)) := by
        rw [hedge.1, hp0]
  · rw [hedge.1] at hstrict
    simpa only [C0, hp0, hp1] using hstrict

end BirthPhaseB3RawFireExtraction

#print axioms BirthPhaseB3RawFireExtraction.dirtySuccessRawFireExtraction
