import Leader.L4.ShortH2RawEntrance
import Leader.L4.ShortMISEngine

namespace L4.ShortMIS2Entrance
open PhysicalCustody ShortH2Final ShortH2RawEntrance
open PhysicalShortSheet ShortMISEngine SelectedMISLayers

variable {s n : Nat}
set_option exponentiation.threshold 40575

/-- Anchor the MIS2 lower fibre at one reached permanent H2 cut. -/
def Lower (N : 21<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (z : Raw s n) : Prop :=
  PermanentH2At x0 A N z ∧ h2 z=h2 y

theorem lower_closed (N : 21<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) : AllSizeComposition.Closed (rawNext s) (Lower N x0 A y) := by
  intro z e Z
  have V := physical_suffix N x0 A z Z.1 [e]
  exact ⟨V.1,V.2.2.1.trans Z.2⟩

def params (N : 27<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (Y : PermanentH2At x0 A (by omega) y) : Params s n :=
  let G : Layer (h1_gaps A.1) (h2 y) := by
    simpa only [show rawRun y [] = y from rfl] using
      (physical_suffix (by omega) x0 A y Y []).2.2.2
  Params.ofGapBounds .mis2 (Lower (by omega) x0 A y)
    (lower_closed (by omega) x0 A y) (h2 y) (fun _ Z=>Z.2)
    (layer_nonempty G (h1_nonempty A.1 (by omega)))
    4 9 (layer_gaps G) (by omega)

theorem cache_from_cut (N : 27<n) (x0 : Raw s n) (A : H2Ready x0)
    (y : Raw s n) (Y : PermanentH2At x0 A (by omega) y) :
    let p := params N x0 A y Y
    CacheFacts p ∧
      L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cached p) y (3*n^2) :=
  ⟨(params N x0 A y Y).cacheFacts,
    (params N x0 A y Y).cached_expected y ⟨Y,rfl⟩⟩

end L4.ShortMIS2Entrance
