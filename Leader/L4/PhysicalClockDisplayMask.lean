import Leader.L4.PhysicalCustody
import Leader.L4.BStarLongPublication

namespace L4.PhysicalClockDisplay
open AllSizeProtocol PhysicalCustody BStarTrace BStarLongLayout BStarLongPublication
open BStarH6WordChart

def refBit {s n : Nat} (x : Raw s n) (i : Fin n) : Bool :=
  H5.seesReference (AllSizeProtocol.reference (rows s) (x i))

def PermanentReference {s n : Nat} (x : Raw s n) : Prop :=
  ∃ winner : Fin n, ∀ (w : List (Fin n)) (i : Fin n),
    refBit (rawRun x w) i = true ↔ i = winner

def selectedAnchor (x : BitVec LW) : Bool :=
  (((bankHeader (readSel x) 5).read x).getLsbD 0)

theorem currHL_selected (x : BitVec LW) : currHL x=selectedAnchor x := by
  unfold currHL selectedAnchor readSel
  change _ = _
  simp only [selector,Field.read,bankHeader,bankPart,bankBase,BitVec.getLsbD_extractLsb']
  simp only [BitVec.extractLsb'_toNat]
  have five : (5 : Fin 9).val = 5 := rfl
  split
  · rename_i H
    simp [H, five]
  · rename_i H
    simp [H, five]

theorem reference_mask {s n : Nat} (x : Raw s n) (i : Fin n) :
    refBit x i=(oldH6 (rows s) x i && selectedAnchor (x i).long) := by
  change (_ && currHL (x i).long) = _
  exact congrArg (fun b => oldH6 (rows s) x i && b) (currHL_selected (x i).long)

theorem permanent_reference_closed {s n : Nat} {x : Raw s n} (e : Fin n)
    (H : PermanentReference x) : PermanentReference (rawNext s x e) := by
  obtain ⟨winner,hw⟩ := H
  exact ⟨winner,fun w i=>hw (e::w) i⟩

/-- A unique selected anchor on a frozen H6 set is a unique actual
reference over every physical site, including nonheaders. -/
theorem of_frozen_headers {s n : Nat} {x base : Raw s n} (winner : Fin n)
    (owner : oldH6 (rows s) base winner = true)
    (members : ∀ w i, oldH6 (rows s) (rawRun x w) i = oldH6 (rows s) base i)
    (display : ∀ w i, oldH6 (rows s) base i = true →
      selectedAnchor (rawRun x w i).long = decide (i=winner)) :
    PermanentReference x := by
  classical
  refine ⟨winner, ?_⟩
  intro w i
  rw [reference_mask, members]
  by_cases hi : oldH6 (rows s) base i = true
  · rw [display w i hi]
    simp [hi]
  · have ne : i≠winner := fun e => hi (e.symm ▸ owner)
    simp [Bool.eq_false_iff.mpr hi,ne]

/-- Custody fixes H6 membership on the actual continuation of the original
history, so the H6-only display certificate can use this exact observer. -/
theorem of_custody_headers {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (winner : Fin n) (owner : oldH6 (rows s) g.base winner = true)
    (display : ∀ w i, oldH6 (rows s) g.base i = true →
      selectedAnchor (rawRun g.initial (((g.u++g.v)++g.past)++w) i).long =
        decide (i=winner)) : PermanentReference x := by
  have qrun : ∀ w y, g.Q y → g.Q (rawRun y w) := by
    intro w
    induction w with
    | nil => exact fun _ q=>q
    | cons e w ih => exact fun y q=>ih _ (g.closed _ e q)
  have same (w : List (Fin n)) : rawRun g.initial (((g.u++g.v)++g.past)++w)=rawRun x w := by
    unfold rawRun
    rw [BStarResetSchedule.run_append]
    exact congrArg (fun y=>rawRun y w) g.here
  apply of_frozen_headers winner owner
  · intro w i
    have Q := qrun (((g.u++g.v)++g.past)++w) g.initial g.init
    rw [same w] at Q
    exact (congrArg Prod.fst (g.fiber _ Q i)).symm
  · intro w i H
    have D := display w i H
    rw [same w] at D
    exact D

end L4.PhysicalClockDisplay
