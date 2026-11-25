import Leader.L4.ShortH2Final
import Leader.L4.AllSizeComposition

namespace L4.ShortH2RawEntrance
open PhysicalCustody ShortH2Final ShortGuardedNOR ShortResetMIS1Ring

set_option exponentiation.threshold 40575

/-- A permanent H2 cut anchored at a genuine H2Ready geometry.
The anchor is a fixed layout witness, not an alternative replay. -/
def PermanentH2 {s n : Nat} (N : 21<n) (y : Raw s n) : Prop :=
  ∃ z : Raw s n, ∃ Z : H2Ready z, PermanentH2At z Z N y

theorem permanent_h2_from_raw {s n : Nat} (N : 21<n) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH2 N) x
      ((5+2*6^9)*n^2 + (10^8095+19+2*publicationScale)*n^2) := by
  apply AllSizeComposition.additive_stage (rawNext s) H2Ready (PermanentH2 N) _ _ x
    (raw_h2_ready_expected (by omega) x)
  intro y Y t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s) (PermanentH2At y Y N) (PermanentH2 N)
    (fun z Z=>⟨y,Y,Z⟩) t y) (permanent_h2_expected N y Y t)

theorem permanent_h2_closed {s n : Nat} (N : 21<n) (x : Raw s n)
    (P : PermanentH2 N x) (w : List (Fin n)) : PermanentH2 N (rawRun x w) := by
  obtain ⟨z,Z,H⟩ := P
  exact ⟨z,Z,(permanent_frozen N z Z x H w).1⟩

end L4.ShortH2RawEntrance
