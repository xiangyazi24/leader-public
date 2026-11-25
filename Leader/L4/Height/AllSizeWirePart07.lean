import Leader.L4.Height.AllSizeWirePart06
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section PhysicalQuiet

open L4.Compiler.Native
open PhysicalCustody
open BStarH6WordChart BStarAcquireAnchors BStarCycleGeometry
open BStarNativePortGeometry (neighborHeader)

theorem physical_adjacent_of_quiet {m M : Nat} (hm : 0 < m)
    (cfg : Fin m → NativeRecord)
    (errFree : ∀ i, (cfg i).err = false)
    (quiet : Recover.StageThree.Quiet M hm cfg)
    (range : ∀ i, (cfg i).tick < M)
    {i j : Fin m} (edge : Adjacent hm i j) :
    BStarPhysicalLiftAlignment.Adjacent M (cfg i).tick (cfg j).tick := by
  rcases coset_edge hm cfg errFree quiet range edge with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem indexed_legitimate_of_quiet {n r : Nat} {h : Fin n → Bool}
    (hh : ∃ i, h i = true) (read : Header h → NativeRecord)
    (errFree : ∀ i, (read (atIndex hh i)).err = false)
    (quiet : Recover.StageThree.Quiet (modulus r) (total_pos h hh)
      (fun i => read (atIndex hh i)))
    (well : Recover.StageTwo.WellFormed (modulus r) (fun i => read (atIndex hh i))) :
    BStarPhysicalLegitimate.Legitimate (r := r) hh read := by
  let hm := total_pos h hh
  let cfg := fun i => read (atIndex hh i)
  have range (i : Fin (total h)) : (cfg i).tick < modulus r := (well i).1
  constructor
  · intro i
    simpa only [atIndex_index] using errFree (BStarCycleGeometry.index hh i)
  · intro i q
    let j := BStarCycleGeometry.index hh i
    have hj : atIndex hh j = i := atIndex_index hh i
    have ports : q = 0 ∨ q = 1 ∨ q = 2 := by
      have hq := q.isLt
      by_cases hz : q.val = 0
      · exact Or.inl (Fin.ext hz)
      · by_cases ho : q.val = 1
        · exact Or.inr (Or.inl (Fin.ext ho))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rw [← hj]
    rcases ports with rfl | rfl | rfl
    · rw [← BStarLogicalConjugacy.atIndex_left hh j]
      change BStarPhysicalLiftAlignment.Adjacent (modulus r) (cfg j).tick (cfg (left hm j)).tick
      exact physical_adjacent_of_quiet hm cfg errFree quiet range (Or.inl rfl)
    · rw [← BStarLogicalConjugacy.atIndex_center hh j]
      exact Or.inl rfl
    · rw [← BStarLogicalConjugacy.atIndex_right hh j]
      change BStarPhysicalLiftAlignment.Adjacent (modulus r) (cfg j).tick (cfg (right hm j)).tick
      exact physical_adjacent_of_quiet hm cfg errFree quiet range (Or.inr rfl)

/-- Every indexed quiet clock with correct records induces the literal
legitimate clock on physical headers and all three of their ports. -/
theorem packed_quiet : ClockDisplaySpec.RawLegitOfQuiet := by
  intro s n x g errFree quiet well
  exact indexed_legitimate_of_quiet (r := radWidth s) g.hh
    (fun i => BStarNativePointwise.readRecord (r := radWidth s) x i.val) errFree quiet well

end PhysicalQuiet

end L4.Height.AllSizeWire
