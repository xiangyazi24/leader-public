import Leader.L4.Height.AllSizeWirePart04
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section Production

open PhysicalCustody ClockServiceSpec ClockDisplaySpec
open AllSizeProtocol BStarH6WordChart BStarCycleGeometry BStarAcquireAnchors
open Classical

abbrev PackedSite (s : Nat) := LargeSite (BStarTrace.production s (radiusTwo s)
  (ell (radiusTwo s+1)) (streak s) (streak (radiusTwo s)) (radWidth s) (s+11) 2 12)

variable {s n : Nat}

theorem pair_distinct (hn : 4 ≤ n) (e : Fin n) : e ≠ rightNeighbor e := by
  intro h
  have E := congrArg Fin.val h
  change e.val = (e.val+1)%n at E
  have hlt := e.isLt
  by_cases H : e.val+1<n
  · rw [Nat.mod_eq_of_lt H] at E
    omega
  · rw [show e.val+1=n by omega, Nat.mod_self] at E
    omega

theorem packed_advice_iff (n : Nat) : 6 ≤ ell (ell n) ↔ 2^32 < n := by
  have A := ell_le_iff (ell n) 5
  have B := ell_le_iff n 32
  change (ell (ell n) ≤ 5 ↔ ell n ≤ 32) at A
  omega

theorem packed_radius_large (hs : 6 ≤ s) : 3 ≤ radWidth s := by
  have h : 2^6 ≤ 2^s := Nat.pow_le_pow_right (by decide) hs
  unfold radWidth
  omega

theorem physical_run_eq_fold {X : Type} (next : X → Fin n → X) (x : X) (w : List (Fin n)) :
    BStarResetSchedule.run next x w = runWord next x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (next x e)

theorem run_eq_public_run {X : Type} (next : X → Fin n → X) (x : X) (w : List (Fin n)) :
    RootedProduct.runProduct next x w = runWord next x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (next x e)

theorem bit_eq_decide_iff {b : Bool} {p : Prop} [Decidable p] :
    b = decide p ↔ (b = true ↔ p) := by
  cases b <;> by_cases h : p <;> simp [h]

theorem productSafe_iff_permanent {X : Type} (next : X → Fin n → X)
    (read : X → Fin n → Bool) (x : X) :
    RootedProduct.ProductSafe next read x ↔ Permanent next read x := by
  unfold Permanent RootedProduct.ProductSafe
  simp only [run_eq_public_run, bit_eq_decide_iff]

noncomputable def packedRead (s : Nat) (a : PackedSite s) : Bool :=
  H5.seesReference (AllSizeProtocol.reference (rows s) a)

noncomputable def packedOutput (s : Nat) (a : PackedSite s) : Bool :=
  (BStarPublicCodec.readPub (p := 2) (c := 12) (by decide) a.publicRow).leader

theorem reference_iff_permanent (x : Raw s n) :
    PermanentReference x ↔ Permanent (rawNext s) (fun y i => packedRead s (y i)) x := by
  unfold PermanentReference Permanent refBit rawRun packedRead
  simp only [physical_run_eq_fold, bit_eq_decide_iff]

end Production

end L4.Height.AllSizeWire
