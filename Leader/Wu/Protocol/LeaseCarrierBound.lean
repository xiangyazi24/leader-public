import Leader.Wu.Protocol.SixTokenCarrierBound
import Leader.Wu.Coherence.WriterLease
import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false

namespace FinalCarrierBoundV31

open PPLLExpiringComparisonRepair

private theorem injective_of_codec {A B : Type}
    (f : A → B) (g : B → A) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  exact (h x).symm.trans ((congrArg g hxy).trans (h y))

/-! ## The three coordinates added/replaced after the accepted base cell -/

/-- Current R2F producer fuel: exactly `Fin (24*ψ+1)`. -/
abbrev Fuel (ψ : Nat) := R2F.Credit ψ

def fuelStates (ψ : Nat) : ExhaustiveList (Fuel ψ) :=
  ExhaustiveList.fin (R2F.fuelCap ψ + 1)

theorem fuelStates_values_nodup (ψ : Nat) :
    (fuelStates ψ).values.Nodup := by
  unfold fuelStates
  exact ExhaustiveList.values_nodup_fin _

theorem fuelStates_length (ψ : Nat) :
    (fuelStates ψ).values.length = 24 * ψ + 1 := by
  rw [fuelStates, ExhaustiveList.values_length_fin]
  rfl

/-- Two values, matching `R2WriterLease.Cell.mode`. -/
def modeStates : ExhaustiveList R2WriterLease.Mode where
  values := [.scrub, .run]
  complete := by
    intro x
    cases x <;> simp

theorem modeStates_values_nodup : modeStates.values.Nodup := by
  decide

theorem modeStates_length : modeStates.values.length = 2 := by
  rfl

/-- Exactly the five lease-metadata fields, separated from physical state:
lease × trusted × allowBirth × tainted × mode. -/
abbrev LeaseMetadata (ψ : Nat) :=
  R2WriterLease.Lease ψ ×
    (Bool × (Bool × (Bool × R2WriterLease.Mode)))

def leaseMetaStates (ψ : Nat) : ExhaustiveList (LeaseMetadata ψ) :=
  ExhaustiveList.prod
    (ExhaustiveList.fin (R2WriterLease.leaseCap ψ + 1))
    (ExhaustiveList.prod ExhaustiveList.bool
      (ExhaustiveList.prod ExhaustiveList.bool
        (ExhaustiveList.prod ExhaustiveList.bool modeStates)))

theorem leaseMetaStates_values_nodup (ψ : Nat) :
    (leaseMetaStates ψ).values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · exact ExhaustiveList.values_nodup_fin _
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_bool
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_bool
      · apply ExhaustiveList.values_nodup_prod
        · exact ExhaustiveList.values_nodup_bool
        · exact modeStates_values_nodup

theorem leaseMetaStates_length (ψ : Nat) :
    (leaseMetaStates ψ).values.length = 128 * ψ + 16 := by
  calc
    (leaseMetaStates ψ).values.length =
        (R2WriterLease.leaseCap ψ + 1) * (2 * (2 * (2 * 2))) := by
      simp only [leaseMetaStates, ExhaustiveList.values_length_prod,
        ExhaustiveList.values_length_fin, ExhaustiveList.values_length_bool,
        modeStates_length]
    _ = R2WriterLease.leaseMetadataStates ψ := by
      unfold R2WriterLease.leaseMetadataStates
      -- Normalize the RHS coefficient `16` to the four binary factors;
      -- the remaining equality is just commutativity around the lease factor.
      rw [show (16 : Nat) = 2 * (2 * (2 * 2)) by decide]
      exact Nat.mul_comm _ _
    _ = 128 * ψ + 16 := R2WriterLease.leaseMetadataStates_exact ψ

/-- The seven V3.1 token values. -/
def tokenV3States : ExhaustiveList R2CoherenceV31.TokenV3 where
  values := [.none, .seek, .sweep, .commit, .release, .scrubL, .openR]
  complete := by
    intro x
    cases x <;> simp

theorem tokenV3States_values_nodup : tokenV3States.values.Nodup := by
  decide

theorem tokenV3States_length : tokenV3States.values.length = 7 := by
  rfl

abbrev ControlV3Code := R2Coherence.Mark × R2CoherenceV31.TokenV3

def controlV3OfCode (x : ControlV3Code) : R2CoherenceV31.ControlV3 :=
  ⟨x.1, x.2⟩

def codeOfControlV3 (u : R2CoherenceV31.ControlV3) : ControlV3Code :=
  (u.mark, u.tok)

theorem controlV3OfCode_codeOfControlV3
    (u : R2CoherenceV31.ControlV3) :
    controlV3OfCode (codeOfControlV3 u) = u := by
  rcases u with ⟨m, t⟩
  rfl

theorem codeOfControlV3_controlV3OfCode (x : ControlV3Code) :
    codeOfControlV3 (controlV3OfCode x) = x := by
  rcases x with ⟨m, t⟩
  rfl

private theorem controlV3OfCode_surjective :
    Function.Surjective controlV3OfCode := by
  intro u
  exact ⟨codeOfControlV3 u, controlV3OfCode_codeOfControlV3 u⟩

private theorem controlV3OfCode_injective :
    Function.Injective controlV3OfCode :=
  injective_of_codec controlV3OfCode codeOfControlV3
    codeOfControlV3_controlV3OfCode

private def controlV3Source : ExhaustiveList ControlV3Code :=
  ExhaustiveList.prod FinalCarrierBoundR2C.markStates tokenV3States

private theorem controlV3Source_values_nodup :
    controlV3Source.values.Nodup :=
  ExhaustiveList.values_nodup_prod
    FinalCarrierBoundR2C.markStates tokenV3States
    FinalCarrierBoundR2C.markStates_values_nodup
    tokenV3States_values_nodup

def controlV3States : ExhaustiveList R2CoherenceV31.ControlV3 :=
  ExhaustiveList.mapSurjective controlV3Source controlV3OfCode
    controlV3OfCode_surjective

theorem controlV3States_values_nodup : controlV3States.values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    controlV3Source controlV3OfCode controlV3OfCode_surjective
    controlV3Source_values_nodup controlV3OfCode_injective

theorem controlV3States_length : controlV3States.values.length = 28 := by
  calc
    controlV3States.values.length = 4 * 7 := by
      simp only [controlV3States, controlV3Source,
        ExhaustiveList.values_length_mapSurjective,
        ExhaustiveList.values_length_prod,
        FinalCarrierBoundR2C.markStates_length, tokenV3States_length]
    _ = R2CoherenceV31.controllerStateCountV3 := by
      rfl
    _ = 28 := R2CoherenceV31.controllerStateCountV3_eq

/-! ## Exact current per-cell product -/

/-- `FinalCarrierBound.Cell` is used only as the already-certified product
`ExpiringAgentState × outer-B9(16)`.  The old R2C fuel/control are not present
in this base, so the new coordinates below are counted exactly once. -/
abbrev CurrentCell (ψ κ τ : Nat) :=
  FinalCarrierBound.Cell ψ κ τ ×
    (R2F.Credit ψ × (LeaseMetadata ψ × R2CoherenceV31.ControlV3))

def currentStates (ψ κ τ : Nat) : ExhaustiveList (CurrentCell ψ κ τ) :=
  ExhaustiveList.prod (FinalCarrierBound.cellStates ψ κ τ)
    (ExhaustiveList.prod (fuelStates ψ)
      (ExhaustiveList.prod (leaseMetaStates ψ) controlV3States))

theorem currentStates_values_nodup (ψ κ τ : Nat) :
    (currentStates ψ κ τ).values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · exact FinalCarrierBound.cellStates_values_nodup ψ κ τ
  · apply ExhaustiveList.values_nodup_prod
    · exact fuelStates_values_nodup ψ
    · apply ExhaustiveList.values_nodup_prod
      · exact leaseMetaStates_values_nodup ψ
      · exact controlV3States_values_nodup

/-- The current product has an exact finite-index decoder, just as the
accepted base carrier does. -/
theorem currentCarrier_decode_bijective (ψ κ τ : Nat) :
    Function.Injective (currentStates ψ κ τ).decode ∧
      Function.Surjective (currentStates ψ κ τ).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (currentStates_values_nodup ψ κ τ),
    ExhaustiveList.decode_surjective _⟩

theorem currentStates_length_as_baseCell (ψ κ τ : Nat) :
    (currentStates ψ κ τ).values.length =
      28 * (((24 * ψ + 1) * (128 * ψ + 16)) *
        (FinalCarrierBound.cellStates ψ κ τ).values.length) := by
  unfold currentStates
  rw [ExhaustiveList.values_length_prod]
  rw [ExhaustiveList.values_length_prod]
  rw [ExhaustiveList.values_length_prod]
  rw [fuelStates_length ψ, leaseMetaStates_length ψ,
    controlV3States_length]
  let B := (FinalCarrierBound.cellStates ψ κ τ).values.length
  let F := 24 * ψ + 1
  let M := 128 * ψ + 16
  change B * (F * (M * 28)) = 28 * ((F * M) * B)
  calc
    B * (F * (M * 28)) = B * ((F * M) * 28) := by
      exact congrArg (fun x : Nat => B * x) (Nat.mul_assoc F M 28).symm
    _ = (B * (F * M)) * 28 := by
      exact (Nat.mul_assoc B (F * M) 28).symm
    _ = 28 * (B * (F * M)) := by
      exact Nat.mul_comm _ _
    _ = 28 * ((F * M) * B) := by
      exact congrArg (fun x : Nat => 28 * x) (Nat.mul_comm B (F * M))

theorem currentStates_length (ψ κ τ : Nat) :
    (currentStates ψ κ τ).values.length =
      (16 * 28 * (24 * ψ + 1) * (128 * ψ + 16)) *
        (ExpiringK2Projection.states ψ κ τ).values.length := by
  let F := 24 * ψ + 1
  let M := 128 * ψ + 16
  let E := (ExpiringK2Projection.states ψ κ τ).values.length
  calc
    (currentStates ψ κ τ).values.length =
        28 * ((F * M) *
          (FinalCarrierBound.cellStates ψ κ τ).values.length) := by
      exact currentStates_length_as_baseCell ψ κ τ
    _ = 28 * ((F * M) * (16 * E)) := by
      exact congrArg (fun x : Nat => 28 * ((F * M) * x))
        (FinalCarrierBound.cellStates_length ψ κ τ)
    _ = 28 * (((F * M) * 16) * E) := by
      exact congrArg (fun x : Nat => 28 * x)
        (Nat.mul_assoc (F * M) 16 E).symm
    _ = (28 * ((F * M) * 16)) * E := by
      exact (Nat.mul_assoc 28 ((F * M) * 16) E).symm
    _ = ((28 * (F * M)) * 16) * E := by
      exact congrArg (fun x : Nat => x * E)
        (Nat.mul_assoc 28 (F * M) 16).symm
    _ = (16 * (28 * (F * M))) * E := by
      exact congrArg (fun x : Nat => x * E)
        (Nat.mul_comm (28 * (F * M)) 16)
    _ = ((16 * 28) * (F * M)) * E := by
      exact congrArg (fun x : Nat => x * E)
        (Nat.mul_assoc 16 28 (F * M)).symm
    _ = (((16 * 28) * F) * M) * E := by
      exact congrArg (fun x : Nat => x * E)
        (Nat.mul_assoc (16 * 28) F M).symm

theorem currentCarrier_card_le (ψ κ τ : Nat) :
    (currentStates ψ κ τ).values.length ≤
      (16 * 28 * (24 * ψ + 1) * (128 * ψ + 16)) *
        ExpiringK2Projection.localBound ψ κ τ := by
  rw [currentStates_length]
  exact Nat.mul_le_mul_left
    (16 * 28 * (24 * ψ + 1) * (128 * ψ + 16))
    (ExpiringK2Projection.state_bound ψ κ τ)

/-! ## Same log-log witness: explicit polynomial and degree-11 monomial -/

/-- The accepted degree-nine base polynomial times the two new linear-in-ψ
coordinates and the constant 28-state V3.1 controller. -/
def currentPoly (s : Nat) : Nat :=
  28 * (24 * (s + 1) + 1) * (128 * (s + 1) + 16) *
    FinalCarrierBound.cellPoly s

theorem currentPoly_eq (s : Nat) :
    currentPoly s =
      28 * (24 * (s + 1) + 1) * (128 * (s + 1) + 16) *
        (32 * 6606028800 * (s + 2) * (s + 1) * (2 * s + 3) *
          (12 * (s + 1) * (s + 2) + 1) * (4 * s + 5) *
          (2 * s + 5) ^ 2 * (16 * s + 17)) := by
  unfold currentPoly
  rw [FinalCarrierBound.cellPoly_eq]

theorem currentCarrier_card_le_at_witness (s : Nat) :
    (currentStates (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤ currentPoly s := by
  calc
    (currentStates (s + 1) (s + 1)
        (16 * (s + 1))).values.length =
        28 * (((24 * (s + 1) + 1) * (128 * (s + 1) + 16)) *
          (FinalCarrierBound.cellStates (s + 1) (s + 1)
            (16 * (s + 1))).values.length) :=
      currentStates_length_as_baseCell
        (s + 1) (s + 1) (16 * (s + 1))
    _ ≤ 28 * (((24 * (s + 1) + 1) * (128 * (s + 1) + 16)) *
          FinalCarrierBound.cellPoly s) :=
      Nat.mul_le_mul_left 28
        (Nat.mul_le_mul_left
          ((24 * (s + 1) + 1) * (128 * (s + 1) + 16))
          (FinalCarrierBound.cellCarrier_card_le_at_witness s))
    _ = currentPoly s := by
      unfold currentPoly
      ac_rfl

/-- The degree-nine coefficient already proved for
`FinalCarrierBound.cellStates`. -/
def baseCellMonomialCoeff : Nat :=
  32 * 61931520000000 * 3 ^ 8 * 33

/-- For `s ≥ 1`, `24(s+1)+1 ≤ 49s` and
`128(s+1)+16 ≤ 272s`, hence degree eleven. -/
def currentMonomialCoeff : Nat :=
  28 * 49 * 272 * baseCellMonomialCoeff

private theorem degree11_scalar (C s : Nat) :
    28 * (((49 * s) * (272 * s)) * (C * s ^ 9)) =
      (28 * 49 * 272 * C) * s ^ 11 := by
  rw [show s ^ 11 = s ^ 10 * s from Nat.pow_succ s 10]
  rw [show s ^ 10 = s ^ 9 * s from Nat.pow_succ s 9]
  ac_rfl

theorem currentCarrier_card_le_monomial (s : Nat) (hs : 1 ≤ s) :
    (currentStates (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤
      currentMonomialCoeff * s ^ 11 := by
  have hfuel : 24 * (s + 1) + 1 ≤ 49 * s := by
    omega
  have hmeta : 128 * (s + 1) + 16 ≤ 272 * s := by
    omega
  have hbase :
      (FinalCarrierBound.cellStates (s + 1) (s + 1)
        (16 * (s + 1))).values.length ≤
        baseCellMonomialCoeff * s ^ 9 := by
    simpa [baseCellMonomialCoeff] using
      (FinalCarrierBound.cellCarrier_card_le_monomial s hs)
  have hfm :
      (24 * (s + 1) + 1) * (128 * (s + 1) + 16) ≤
        (49 * s) * (272 * s) :=
    Nat.mul_le_mul hfuel hmeta
  have hprod :
      ((24 * (s + 1) + 1) * (128 * (s + 1) + 16)) *
          (FinalCarrierBound.cellStates (s + 1) (s + 1)
            (16 * (s + 1))).values.length ≤
        ((49 * s) * (272 * s)) *
          (baseCellMonomialCoeff * s ^ 9) :=
    Nat.mul_le_mul hfm hbase
  calc
    (currentStates (s + 1) (s + 1)
        (16 * (s + 1))).values.length =
        28 * (((24 * (s + 1) + 1) * (128 * (s + 1) + 16)) *
          (FinalCarrierBound.cellStates (s + 1) (s + 1)
            (16 * (s + 1))).values.length) :=
      currentStates_length_as_baseCell
        (s + 1) (s + 1) (16 * (s + 1))
    _ ≤ 28 * (((49 * s) * (272 * s)) *
          (baseCellMonomialCoeff * s ^ 9)) :=
      Nat.mul_le_mul_left 28 hprod
    _ = currentMonomialCoeff * s ^ 11 := by
      unfold currentMonomialCoeff
      exact degree11_scalar baseCellMonomialCoeff s

theorem currentCarrier_card_le_polyloglog (n : Nat) :
    let s := BirthShortDoneDispatcher.loglogScale n
    (currentStates (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤
      currentMonomialCoeff * s ^ 11 :=
  currentCarrier_card_le_monomial
    (BirthShortDoneDispatcher.loglogScale n)
    (FinalCarrierBound.loglogScale_ge_one n)

end FinalCarrierBoundV31
