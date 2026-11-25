import Leader.L4.Height.G9WirePart09
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section PackedService

open Classical
open PhysicalCustody
open AllSizeProtocol BStarH6WordChart BStarAcquireAnchors BStarCycleGeometry
open BStarGrantWriterHistory (NoPublication)

variable {s n : Nat}

/-- The literal block estimate applies at each chart endpoint by extending
its original custody history by exactly the raw suffix consumed so far. -/
theorem packed_strict_block (hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = AllSizeProtocol.ell (AllSizeProtocol.ell n))
    (hBlock : ClockServiceSpec.ProductionStrictBlock) :
    StrictPublicationBlock (packedData s n hn hs) (by omega)
      (packedPublication s) packedHeader := by
  classical
  intro j i z
  let D := packedData s n hn hs
  let y := rawRun j.1 z.1
  let g := extendWitness j.2 z.1
  let t := 2 * (2^20 * n * ClockServiceSpec.maxWordWidth j.2)
  let h := packedHeader j i
  have hCount := hBlock g (packed_service_production hn hs ha g) (atIndex g.hh i)
  have hEqual :
      (fun w => if publishes (D.next (by omega)) (packedPublication s) y h w
        then 1 else 0) =
      (fun w => if ClockServiceSpec.publishes y h w then 1 else 0) := by
    funext w
    have hEvent : publishes (D.next (by omega)) (packedPublication s) y h w ↔
        ClockServiceSpec.publishes y h w := by
      change publishes ((packedData s n hn hs).next (by omega)) (packedPublication s) y h w ↔ _
      rw [packed_next hn hs]
      unfold publishes ClockServiceSpec.publishes RawServiceCore.publishes
      simp only [packedPublication, rawRun, physical_run_eq_fold]
    by_cases hp : ClockServiceSpec.publishes y h w
    · simp only [if_pos hp, if_pos (hEvent.mpr hp)]
    · simp only [if_neg hp, if_neg (fun hp' => hp (hEvent.mp hp'))]
  have transport (d : Nat)
      (hc : n^t ≤ d * wordSum (fun w =>
        if ClockServiceSpec.publishes y h w then 1 else 0) t) :
      n^t ≤ d * wordSum (fun w =>
        if publishes (D.next (by omega)) (packedPublication s) y h w then 1 else 0) t := by
    rw [hEqual]
    exact hc
  exact transport _ hCount

/-- The strict literal service count supplies the packed clock's block field. -/
theorem packed_service (hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = AllSizeProtocol.ell (AllSizeProtocol.ell n))
    (hBlock : ClockServiceSpec.ProductionStrictBlock) :
    let D := packedData s n hn hs
    ∀ j i z, n^(D.block j) ≤ 2^(5*(2^32 : Nat)+1) *
      RawService.publicationMass (D.clock j).next ((D.clock j).served i) z (D.block j) := by
  exact service_of_strict_publication_block (packedData s n hn hs) (by omega) (packedPublication s)
    packedHeader (packed_rawStep hn hs)
    (fun j z e i => chooseMark_matches j.2 hn hs z.1 e i)
    (packed_strict_block hn hs ha hBlock)

end PackedService

end L4.Height.G9Wire
