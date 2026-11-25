import Leader.L4.Height.G9WirePart03
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section LiteralLedger

open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarAcquireAnchors BStarCycleGeometry BStarGrantWriterHistory
open BStarPhysicalCoset BStarPhysicalLegitimate BStarPhysicalIncrementLedger
open BStarPhysicalLiftAlignment BStarEpochLift

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "Raw" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "rows" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "rawRun" => BStarResetSchedule.run (AllSizeS1Geometry.step rows)

/-- A coherent physical ledger projects to the accepted legitimate coset
on the indexed native records at the same raw state. -/
theorem literal_legitCoset {base x : Raw} (hh : ∃ i, oldH6 rows base i = true)
    (ticks : Fin n → Nat)
    (hRep : RepresentsCoset hp base x (modulus r / 2) ticks)
    (hCoherent : Coherent hh ticks)
    (hQuiet : Recover.StageThree.Quiet (modulus r) (total_pos (oldH6 rows base) hh)
      (literalClockCfg hh x))
    (hRange : Recover.StageTwo.WellFormed (modulus r) (literalClockCfg hh x)) :
    LegitCoset (modulus r) (total_pos (oldH6 rows base) hh)
      ⟨literalClockCfg hh x, fun i => ticks (atIndex hh i).val⟩ := by
  refine ⟨fun i => (hRep (atIndex hh i)).1, fun i => (hRep (atIndex hh i)).2,
    ?_, fun i => (hRange i).1, hQuiet⟩
  intro i j hj
  rcases hj with rfl | rfl
  · change Near (ticks (atIndex hh i).val)
      (ticks (atIndex hh (left (total_pos (oldH6 rows base) hh) i)).val)
    rw [BStarLogicalConjugacy.atIndex_left]
    exact hCoherent _ 0
  · change Near (ticks (atIndex hh i).val)
      (ticks (atIndex hh (right (total_pos (oldH6 rows base) hh) i)).val)
    rw [BStarLogicalConjugacy.atIndex_right]
    exact hCoherent _ 2

/-- The physical INC detector agrees with the clock guard read at the same
indexed header and old raw state. Its result is independent of the bit. -/
theorem literal_incAt (base old : Raw) (hh : ∃ i, oldH6 rows base i = true)
    (lift : Fin (total (oldH6 rows base)) → Nat) (i : Fin (total (oldH6 rows base)))
    (hPub : ¬ NoPublication hp old (atIndex hh i).val (atIndex hh i).val) :
    incAt hp base hh old (atIndex hh i).val =
      match clockAction (modulus r) (total_pos (oldH6 rows base) hh)
        ⟨literalClockCfg hh old, lift⟩ i with
      | .inc _ => some (atIndex hh i).val
      | _ => none := by
  let port := fun q : Fin 3 => BStarNativePointwise.readRecord (r := r) old
    (BStarNativePortGeometry.neighborHeader hh (atIndex hh i) q).val
  have hAct : nativeClock (modulus r) (port 0) (port 1) (port 2) =
      clockAction (modulus r) (total_pos (oldH6 rows base) hh)
        ⟨literalClockCfg hh old, lift⟩ i := by
    unfold clockAction
    dsimp only [port, literalClockCfg]
    rw [← BStarLogicalConjugacy.atIndex_center hh i, BStarLogicalConjugacy.atIndex_left,
      BStarLogicalConjugacy.atIndex_right]
  rw [incAt, dif_pos (atIndex hh i).property, if_neg hPub]
  change (match nativeClock (modulus r) (port 0) (port 1) (port 2) with
    | .inc _ => some (atIndex hh i).val
    | _ => none) = _
  rw [hAct]

/-- Appending one raw letter to the physical tape updates the indexed
natural ledger by exactly the increment of the matching native action. -/
theorem literal_traceCount_snoc (base initial : Raw)
    (hh : ∃ i, oldH6 rows base i = true)
    (start : Fin n → Nat) (hist : List (Fin n)) (e : Fin n)
    (a : Option (Fin (total (oldH6 rows base)) × Bool))
    (hMatch : ∀ i, (∃ b, a = some (i,b)) ↔
      e = (atIndex hh i).val ∧ ¬ NoPublication hp (rawRun initial hist) e e) :
    (fun j => traceCount hp base initial hh start (hist ++ [e]) (atIndex hh j).val) =
      let lift := fun j => traceCount hp base initial hh start hist (atIndex hh j).val
      match a with
      | none => lift
      | some (i,b) => (L4.Height.activate (heightMod r) (modulus r)
          (total_pos (oldH6 rows base) hh) ⟨literalClockCfg hh (rawRun initial hist), lift⟩ i b).lift := by
  classical
  let old := rawRun initial hist
  let h := oldH6 rows base
  let m := total h
  let hm : 0 < m := total_pos h hh
  let lift := fun j : Fin m => traceCount hp base initial hh start hist (atIndex hh j).val
  let s : WordState m := ⟨literalClockCfg hh old, lift⟩
  have hCount (j : Fin m) :
      traceCount hp base initial hh start (hist ++ [e]) (atIndex hh j).val =
        lift j + if incAt hp base hh old e = some (atIndex hh j).val then 1 else 0 :=
    count_append_mark hp base hh initial start hist e (atIndex hh j).val
  funext j
  rw [hCount]
  cases a with
  | none =>
    change lift j + (if incAt hp base hh old e = some (atIndex hh j).val then 1 else 0) = lift j
    have hNoInc : incAt hp base hh old e ≠ some (atIndex hh j).val := by
      intro hInc
      have he := incAt_value hp hh e _ hInc
      by_cases hQuiet : NoPublication hp old e e
      · have hHead : oldH6 rows base e = true := by
          rw [he]
          exact (atIndex hh j).property
        rw [incAt, dif_pos hHead, if_pos hQuiet] at hInc
        cases hInc
      · obtain ⟨b, hb⟩ := (hMatch j).2 ⟨he, hQuiet⟩
        cases hb
    simp only [if_neg hNoInc, Nat.add_zero]
  | some pair =>
    rcases pair with ⟨i,b⟩
    obtain ⟨he,hPub⟩ := (hMatch i).1 ⟨b,rfl⟩
    change lift j + (if incAt hp base hh old e = some (atIndex hh j).val then 1 else 0) =
      (L4.Height.activate (heightMod r) (modulus r) hm s i b).lift j
    by_cases hij : j = i
    · subst j
      have hPubAt : ¬ NoPublication hp old (atIndex hh i).val (atIndex hh i).val := by
        simpa only [he] using hPub
      have hInc := literal_incAt hp base old hh lift i hPubAt
      rw [he, hInc]
      change (lift i + (if (match clockAction (modulus r) hm s i with
        | .inc _ => some (atIndex hh i).val
        | _ => none) = some (atIndex hh i).val then 1 else 0)) =
        setAt lift i (advanceLift (clockAction (modulus r) hm s i) (lift i)) i
      rw [setAt_self]
      cases clockAction (modulus r) hm s i <;> simp [advanceLift]
    · have hNoInc : incAt hp base hh old e ≠ some (atIndex hh j).val := by
        intro hInc
        exact hij (BStarLogicalConjugacy.physical_injective hh
          ((incAt_value hp hh e _ hInc).symm.trans he))
      change lift j + (if incAt hp base hh old e = some (atIndex hh j).val then 1 else 0) =
        setAt lift i (advanceLift (clockAction (modulus r) hm s i) (lift i)) j
      rw [if_neg hNoInc, Nat.add_zero, setAt_other _ _ _ _ hij]

end LiteralLedger

end L4.Height.G9Wire
