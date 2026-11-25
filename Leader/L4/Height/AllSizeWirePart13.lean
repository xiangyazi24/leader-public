import Leader.L4.Height.AllSizeWirePart12
set_option Elab.async false
set_option maxHeartbeats 1200000

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section PackedFrontier

open BStarCycleGeometry BStarEpochLift PhysicalCustody

variable {s n : Nat}

theorem packed_origin_reservation_margin (hn : 4 ≤ n) (hs : 6 ≤ s)
    (j : (packedData s n hn hs).Chart) (z : (packedData s n hn hs).State j)
    {lo opening : Nat} {level : List (Fin n) → Fin ((packedData s n hn hs).m j) → Nat}
    (hOrigin : packedOrigin hn hs j z lo opening level)
    (i : Fin ((packedData s n hn hs).m j)) {key : Nat}
    (hKey : key ≤ level [] i + 1) : key + 2 ≤ opening := by
  obtain ⟨start, G, hOpening, hUpper, hLevel, _⟩ := hOrigin
  let g := extendWitness j.2 z.1
  let tape := (g.u ++ g.v) ++ g.past
  let loc := (atIndex g.hh i).val
  have hStopped : level [] i ≤ G := by
    rw [hLevel [] i]
    exact Eq.mpr (congrArg (fun w : List (Fin n) =>
      traceCount (show 0 < 2 by decide) g.base g.initial g.hh start w loc ≤ G)
      (List.append_nil tape)) (hUpper loc)
  rw [hOpening]
  exact physical_reservation_margin hStopped hKey

end PackedFrontier

end L4.Height.AllSizeWire
