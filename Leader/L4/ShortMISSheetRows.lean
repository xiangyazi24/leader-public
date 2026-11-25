import Leader.L4.ShortMISSheetParkPhase
import Leader.L4.ShortMIS3Entrance

namespace L4.ShortMISSheetRows
open AllSizeProtocol PhysicalCustody ShortMISLift ShortMIS3Entrance
open ShortMISSheetParked ShortMISSheetParkPhase

variable {s n : Nat}

def Auth (G : Geometry s n) : Prop :=
  ∀ x e, Good G.P x → observe G.P (rawNext s x e)=
    match classify G.P x e with
    | none => observe G.P x
    | some j => ShortNORCover.update G.ring (observe G.P x) j

def Win (G : Geometry s n) : Prop :=
  ∀ i x, Good G.P x → FiveParked G.P (G.family i) x →
    i∈ShortNORCover.publications (rawNext s) (classify G.P) x (G.word i)

def assemble (G : Geometry s n) (auth : Auth G) (win : Win G) : LocalRows G where
  rank C := ShortMISSheetRank.rank_rows G.P C (by
    obtain ⟨i,I⟩ := G.P.hh
    obtain ⟨k,K,J⟩ := G.P.gap i I
    have := J.positive
    have := G.seven
    omega) G.D (G.chart_small C)
  clean := ShortMISSheetReset.clean G.P
  firstHit := ShortMISSheetReset.firstHit G.P
  parkPhase := parkPhase G
  parkGoal := parkGoal G
  parkWatch := parkWatch G
  parkedNondoor := parked_nondoor G.P
  auth := auth
  win := win

theorem mis2_from_h2 (N : 63<n) (x : Raw s n)
    (H : ShortH2RawEntrance.PermanentH2 (by omega : 21<n) x)
    (auth : Auth (mis2Geometry N x H)) (win : Win (mis2Geometry N x H)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH3 N) x (K_H3*n^2) :=
  permanent_h3_from_h2 N x H (assemble _ auth win)

theorem mis3_from_h3 (N : 189<n) (x : Raw s n)
    (H : PermanentH3 (by omega : 63<n) x)
    (auth : Auth (mis3Geometry N x H)) (win : Win (mis3Geometry N x H)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x (K_H4*n^2) :=
  permanent_h4_from_h3 N x H (assemble _ auth win)

end L4.ShortMISSheetRows
