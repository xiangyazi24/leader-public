import Leader.L4.ShortMISPublicationClosed
import Leader.L4.ReportOwnerResetDrain
import Leader.L4.ReportPrelaunchK1Geometry
import Leader.L4.ReportOwnerSerial

namespace L4.ReportFirstRawEntrance
open AllSizeProtocol PhysicalCustody
open ShortH2Final ShortMISLift ShortMIS3Entrance ShortMISPublicationClosed
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportResetRawHooks

set_option exponentiation.threshold 40575
variable {s n : Nat}

theorem report1Fibre (N : 189<n) (base : Raw s n) :
    Fibre (h:=ReportStaticSpacing.h4 base) .first (H4Fibre N base) :=
  ⟨h4_fibre_closed N base,fun _y Y i => congrFun Y.2 i⟩

def report1Geometry (N : 243<n) (base : Raw s n) (H : PermanentH4 (by omega) base) :
    GapInput (ReportStaticSpacing.h4 base) where
  B := 81
  room := N
  gaps i I := by
    obtain ⟨k,L,U,G⟩ := permanent_h4_gaps (by omega) base H i I
    exact ⟨k,by omega,U,G⟩

/-- Anchored lower layout and correct report1 cache, not a custody or
publication claim. The original mark process reaches it from any bytes. -/
def Report1Ready (N : 189<n) (y : Raw s n) : Prop :=
  ∃ base : Raw s n, ∃ H : PermanentH4 N base,
    Cached (h:=ReportStaticSpacing.h4 base) .first
      (permanent_h4_nonempty N base H) (H4Fibre N base) y

theorem report1_ready_closed (N : 189<n) (y : Raw s n) (e : Fin n) (Y : Report1Ready N y) :
    Report1Ready N (rawNext s y e) := by
  obtain ⟨base,H,C⟩ := Y
  exact ⟨base,H,(cached_fibre .first (by omega) _ _ (report1Fibre N base)).closed y e C⟩

theorem report1_ready_from_raw (N : 189<n) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Report1Ready N) x
      ((5+2*6^9)*n^2 + (10^8095+19+2*publicationScale)*n^2 +
        (K_H3+K_H4)*n^2 + 4*n^2) := by
  apply AllSizeComposition.additive_stage _ (PermanentH4 N) _ _ _ x
    (permanent_h4_from_raw N x)
  intro y H t
  exact Nat.le_trans (RankRenewal.cost_mono_target
    (next:=rawNext s)
    (Cached .first (permanent_h4_nonempty N y H) (H4Fibre N y))
    (Report1Ready N) (fun z Z => ⟨y,H,Z⟩) t y) ((report1_cache_from_h4 N y H).2 t)

/-- First-cover endpoint on the actual permanent H4 fibre.
Semantic captures and grant histories are still absent. -/
def Report1Serial (N : 243<n) (y : Raw s n) : Prop :=
  ∃ base : Raw s n, ∃ H : PermanentH4 (by omega) base,
    ReportOwnerSerial.AllSerial .first (permanent_h4_nonempty (by omega) base H)
      (H4Fibre (by omega) base) (report1Geometry N base H) y

theorem report1_serial_closed (N : 243<n) (S : 0<s) (y : Raw s n) (e : Fin n)
    (Y : Report1Serial N y) : Report1Serial N (rawNext s y e) := by
  obtain ⟨base,H,A⟩ := Y
  exact ⟨base,H,ReportOwnerSerial.all_serial_closed .first (by omega) _
    (report1Geometry N base H) (report1Fibre (by omega) base)
    (ReportPrelaunchDoorProducer.digits_positive .first S) y e A⟩

theorem report1_serial_from_raw (N : 243<n) (S : 0<s) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Report1Serial N) x
      ((5+2*6^9)*n^2 + (10^8095+19+2*publicationScale)*n^2 +
        (K_H3+K_H4)*n^2 + 4*n^2 +
        ReportResetEventClock.resetCoefficient 243 1*n^2) := by
  apply AllSizeComposition.additive_stage _ (Report1Ready (by omega)) _ _ _ x
    (report1_ready_from_raw (by omega) x)
  intro y H t
  obtain ⟨base,B,C⟩ := H
  let G := report1Geometry N base B
  have A := ReportOwnerSerial.all_serial_from_cached .first (by omega) S
    (permanent_h4_nonempty (by omega) base B) G (report1Fibre (by omega) base)
    ⟨y,C⟩
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s) _
    (Report1Serial N) (fun z Z => ⟨base,B,Z⟩) t y) (A t)

#print axioms report1_serial_closed
#print axioms report1_serial_from_raw
#print axioms report1Geometry
#print axioms report1_ready_from_raw
#print axioms report1_ready_closed
end L4.ReportFirstRawEntrance
