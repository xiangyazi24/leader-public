import Leader.L4.PhysicalClockDisplayMask
import Leader.L4.BStarAcquireAnchors

namespace L4.PhysicalClockDisplay
open AllSizeProtocol PhysicalCustody BStarTrace BStarH6WordChart BStarAcquireAnchors

/-- The indexed H6 readout on the same custody tape is enough for the
actual all-site reference observer. The reference winner is that
indexed header, not merely some site with a true stored field. -/
theorem of_indexed_original {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (headerAt : Fin (total (oldH6 (rows s) g.base)) → Header (oldH6 (rows s) g.base))
    (injective : ∀ {j k}, headerAt j=headerAt k → j=k)
    (onto : ∀ i : Header (oldH6 (rows s) g.base), ∃ j,headerAt j=i)
    (winner : Fin (total (oldH6 (rows s) g.base)))
    (display : ∀ w (j : Fin (total (oldH6 (rows s) g.base))),
      selectedAnchor (rawRun g.initial (((g.u++g.v)++g.past)++w) (headerAt j).val).long =
        decide (j=winner)) :
    PermanentReference x := by
  classical
  let a := headerAt winner
  apply of_custody_headers g a.val a.property
  intro w i H
  let b : Header (oldH6 (rows s) g.base) := ⟨i,H⟩
  obtain ⟨j,id⟩ := onto b
  have same : (j=winner) ↔ i=a.val := by
    constructor
    · intro E
      exact congrArg Subtype.val (id.symm.trans (congrArg headerAt E))
    · intro E
      have V : b=a := Subtype.ext E
      exact injective (id.trans V)
  have D := display w j
  rw [id] at D
  change selectedAnchor (rawRun g.initial (((g.u++g.v)++g.past)++w) i).long =
    decide (j=winner) at D
  rw [D]
  by_cases J : j=winner
  · simp [J,same.mp J]
  · have Hn : i≠a.val := fun e=>J (same.mpr e)
    simp [J,Hn]

end L4.PhysicalClockDisplay
