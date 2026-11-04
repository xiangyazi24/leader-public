import Leader.Wu.Protocol.SpliceLineageCarrierBound
import Leader.Wu.Coherence.SixTokenController
import Leader.Wu.Splice.FullCarrierHost


/-!
Finite-state certificates for the successor R2C physical carrier.


Counts are exact certificate lengths.  The three requested duplicate-free
certificates therefore also give exact finite-index decoders:


* R2.Cell:                 (4 * psi + 1) * E
* R2Coherence.Cell:   24 * (4 * psi + 1) * E
* CellP R2C:         384 * (4 * psi + 1) * E


where E is the accepted expiring-K2 certificate length.  The final factor 384
is 24 quarantine controls times the retained 16-state B9 splice controller.
A lease alphabet is left parametric below.
-/


set_option autoImplicit false
set_option Elab.async false


namespace FinalCarrierBoundR2C


open PPLLExpiringComparisonRepair
open WriterProducerRepair
open Q11593SpliceControllerDesign


variable {psi kappa tau : Nat}


private theorem injective_of_codec {A B : Type}
    (f : A -> B) (g : B -> A) (h : forall x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  exact (h x).symm.trans ((congrArg g hxy).trans (h y))


/-! ## R2 fuel extension -/


abbrev R2Code (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau × Credit psi


def r2OfCode (x : R2Code psi kappa tau) : R2.Cell psi kappa tau :=
  ⟨x.1, x.2⟩


def codeOfR2 (u : R2.Cell psi kappa tau) : R2Code psi kappa tau :=
  (u.base, u.fuel)


theorem r2OfCode_codeOfR2 (u : R2.Cell psi kappa tau) :
    r2OfCode (codeOfR2 u) = u := by
  rcases u with ⟨p, f⟩
  rfl


theorem codeOfR2_r2OfCode (x : R2Code psi kappa tau) :
    codeOfR2 (r2OfCode x) = x := by
  rcases x with ⟨p, f⟩
  rfl


theorem r2OfCode_surjective (psi kappa tau : Nat) :
    Function.Surjective (r2OfCode (psi := psi)
      (kappa := kappa) (tau := tau)) := by
  intro u
  exact ⟨codeOfR2 u, r2OfCode_codeOfR2 u⟩


theorem r2OfCode_injective (psi kappa tau : Nat) :
    Function.Injective (r2OfCode (psi := psi)
      (kappa := kappa) (tau := tau)) :=
  injective_of_codec r2OfCode codeOfR2 codeOfR2_r2OfCode


private def r2Source (psi kappa tau : Nat) :
    ExhaustiveList (R2Code psi kappa tau) :=
  ExhaustiveList.prod (ExpiringK2Projection.states psi kappa tau)
    (ExhaustiveList.fin (4 * psi + 1))


private theorem r2Source_values_nodup (psi kappa tau : Nat) :
    (r2Source psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_prod
    (ExpiringK2Projection.states psi kappa tau)
    (ExhaustiveList.fin (4 * psi + 1))
    (expiringAgentState_values_nodup psi kappa tau)
    (ExhaustiveList.values_nodup_fin (4 * psi + 1))


def r2States (psi kappa tau : Nat) :
    ExhaustiveList (R2.Cell psi kappa tau) :=
  ExhaustiveList.mapSurjective (r2Source psi kappa tau)
    r2OfCode (r2OfCode_surjective psi kappa tau)


theorem r2States_values_nodup (psi kappa tau : Nat) :
    (r2States psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    (r2Source psi kappa tau) r2OfCode
    (r2OfCode_surjective psi kappa tau)
    (r2Source_values_nodup psi kappa tau)
    (r2OfCode_injective psi kappa tau)


theorem r2States_length (psi kappa tau : Nat) :
    (r2States psi kappa tau).values.length =
      (4 * psi + 1) *
        (ExpiringK2Projection.states psi kappa tau).values.length := by
  unfold r2States
  rw [ExhaustiveList.values_length_mapSurjective]
  unfold r2Source
  rw [ExhaustiveList.values_length_prod]
  rw [ExhaustiveList.values_length_fin]
  exact Nat.mul_comm _ _



theorem r2Carrier_decode_bijective (psi kappa tau : Nat) :
    Function.Injective (r2States psi kappa tau).decode ∧
      Function.Surjective (r2States psi kappa tau).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (r2States_values_nodup psi kappa tau),
    ExhaustiveList.decode_surjective _⟩


theorem r2Carrier_card_le (psi kappa tau : Nat) :
    (r2States psi kappa tau).values.length ≤
      (4 * psi + 1) * ExpiringK2Projection.localBound psi kappa tau := by
  rw [r2States_length]
  exact Nat.mul_le_mul_left (4 * psi + 1)
    (ExpiringK2Projection.state_bound psi kappa tau)


/-! ## Four marks times six quarantine tokens -/


def markStates : ExhaustiveList R2Coherence.Mark where
  values := [.open, .closing, .sealed, .releasing]
  complete := by
    intro x
    cases x <;> simp


theorem markStates_values_nodup : markStates.values.Nodup := by
  decide


theorem markStates_length : markStates.values.length = 4 := by
  rfl


def tokenStates : ExhaustiveList R2Coherence.Token where
  values := [.none, .seek, .sweep, .commit, .release, .reopen]
  complete := by
    intro x
    cases x <;> simp


theorem tokenStates_values_nodup : tokenStates.values.Nodup := by
  decide


theorem tokenStates_length : tokenStates.values.length = 6 := by
  rfl


abbrev ControlCode := R2Coherence.Mark × R2Coherence.Token


def controlOfCode (x : ControlCode) : R2Coherence.Control :=
  ⟨x.1, x.2⟩


def codeOfControl (u : R2Coherence.Control) : ControlCode :=
  (u.mark, u.tok)


theorem controlOfCode_codeOfControl (u : R2Coherence.Control) :
    controlOfCode (codeOfControl u) = u := by
  rcases u with ⟨m, t⟩
  rfl


theorem codeOfControl_controlOfCode (x : ControlCode) :
    codeOfControl (controlOfCode x) = x := by
  rcases x with ⟨m, t⟩
  rfl


private theorem controlOfCode_surjective :
    Function.Surjective controlOfCode := by
  intro u
  exact ⟨codeOfControl u, controlOfCode_codeOfControl u⟩


private theorem controlOfCode_injective :
    Function.Injective controlOfCode :=
  injective_of_codec controlOfCode codeOfControl
    codeOfControl_controlOfCode


private def controlSource : ExhaustiveList ControlCode :=
  ExhaustiveList.prod markStates tokenStates


private theorem controlSource_values_nodup :
    controlSource.values.Nodup :=
  ExhaustiveList.values_nodup_prod markStates tokenStates
    markStates_values_nodup tokenStates_values_nodup


def controlStates : ExhaustiveList R2Coherence.Control :=
  ExhaustiveList.mapSurjective controlSource controlOfCode
    controlOfCode_surjective


theorem controlStates_values_nodup : controlStates.values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    controlSource controlOfCode controlOfCode_surjective
    controlSource_values_nodup controlOfCode_injective


theorem controlStates_length : controlStates.values.length = 24 := by
  calc
    controlStates.values.length = 4 * 6 := by
      simp only [controlStates, controlSource,
        ExhaustiveList.values_length_mapSurjective,
        ExhaustiveList.values_length_prod,
        markStates_length, tokenStates_length]
    _ = 24 := rfl


abbrev CoherenceCode (psi kappa tau : Nat) :=
  R2.Cell psi kappa tau × R2Coherence.Control


def coherenceOfCode (x : CoherenceCode psi kappa tau) :
    R2Coherence.Cell psi kappa tau :=
  ⟨x.1, x.2⟩


def codeOfCoherence (u : R2Coherence.Cell psi kappa tau) :
    CoherenceCode psi kappa tau :=
  (u.phys, u.ctl)


theorem coherenceOfCode_codeOfCoherence
    (u : R2Coherence.Cell psi kappa tau) :
    coherenceOfCode (codeOfCoherence u) = u := by
  rcases u with ⟨p, c⟩
  rfl


theorem codeOfCoherence_coherenceOfCode
    (x : CoherenceCode psi kappa tau) :
    codeOfCoherence (coherenceOfCode x) = x := by
  rcases x with ⟨p, c⟩
  rfl


theorem coherenceOfCode_surjective (psi kappa tau : Nat) :
    Function.Surjective (coherenceOfCode (psi := psi)
      (kappa := kappa) (tau := tau)) := by
  intro u
  exact ⟨codeOfCoherence u, coherenceOfCode_codeOfCoherence u⟩


theorem coherenceOfCode_injective (psi kappa tau : Nat) :
    Function.Injective (coherenceOfCode (psi := psi)
      (kappa := kappa) (tau := tau)) :=
  injective_of_codec coherenceOfCode codeOfCoherence
    codeOfCoherence_coherenceOfCode


private def coherenceSource (psi kappa tau : Nat) :
    ExhaustiveList (CoherenceCode psi kappa tau) :=
  ExhaustiveList.prod (r2States psi kappa tau) controlStates


private theorem coherenceSource_values_nodup (psi kappa tau : Nat) :
    (coherenceSource psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_prod
    (r2States psi kappa tau) controlStates
    (r2States_values_nodup psi kappa tau) controlStates_values_nodup


def coherenceStates (psi kappa tau : Nat) :
    ExhaustiveList (R2Coherence.Cell psi kappa tau) :=
  ExhaustiveList.mapSurjective (coherenceSource psi kappa tau)
    coherenceOfCode (coherenceOfCode_surjective psi kappa tau)


theorem coherenceStates_values_nodup (psi kappa tau : Nat) :
    (coherenceStates psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    (coherenceSource psi kappa tau) coherenceOfCode
    (coherenceOfCode_surjective psi kappa tau)
    (coherenceSource_values_nodup psi kappa tau)
    (coherenceOfCode_injective psi kappa tau)


private theorem factor24_right (a L : Nat) :
    (a * L) * 24 = (24 * a) * L := by
  ac_rfl

theorem coherenceStates_length (psi kappa tau : Nat) :
    (coherenceStates psi kappa tau).values.length =
      (24 * (4 * psi + 1)) *
        (ExpiringK2Projection.states psi kappa tau).values.length := by
  unfold coherenceStates
  rw [ExhaustiveList.values_length_mapSurjective]
  unfold coherenceSource
  rw [ExhaustiveList.values_length_prod]
  rw [r2States_length, controlStates_length]
  exact factor24_right (4 * psi + 1)
    (ExpiringK2Projection.states psi kappa tau).values.length



theorem coherenceCarrier_decode_bijective (psi kappa tau : Nat) :
    Function.Injective (coherenceStates psi kappa tau).decode ∧
      Function.Surjective (coherenceStates psi kappa tau).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (coherenceStates_values_nodup psi kappa tau),
    ExhaustiveList.decode_surjective _⟩


theorem coherenceCarrier_card_le (psi kappa tau : Nat) :
    (coherenceStates psi kappa tau).values.length ≤
      (24 * (4 * psi + 1)) *
        ExpiringK2Projection.localBound psi kappa tau := by
  rw [coherenceStates_length]
  exact Nat.mul_le_mul_left (24 * (4 * psi + 1))
    (ExpiringK2Projection.state_bound psi kappa tau)


/-! ## Retained B9 controller over the complete R2C physical cell -/


private def twoBits : ExhaustiveList (Bool × Bool) :=
  ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool


private theorem twoBits_values_nodup : twoBits.values.Nodup :=
  ExhaustiveList.values_nodup_prod
    ExhaustiveList.bool ExhaustiveList.bool
    ExhaustiveList.values_nodup_bool ExhaustiveList.values_nodup_bool


private theorem twoBits_length : twoBits.values.length = 4 := by
  calc
    twoBits.values.length = 2 * 2 := by
      simp only [twoBits, ExhaustiveList.values_length_prod,
        ExhaustiveList.values_length_bool]
    _ = 4 := rfl


/-- Exactly the accepted splice-role x repairPending x acquireTicket product. -/
private def cellPControlStates :
    ExhaustiveList (SpliceRole × (Bool × Bool)) :=
  ExhaustiveList.prod FinalCarrierBound.spliceStates twoBits


private theorem cellPControlStates_values_nodup :
    cellPControlStates.values.Nodup :=
  ExhaustiveList.values_nodup_prod
    FinalCarrierBound.spliceStates twoBits
    FinalCarrierBound.spliceStates_values_nodup twoBits_values_nodup


private theorem cellPControlStates_length :
    cellPControlStates.values.length = 16 := by
  calc
    cellPControlStates.values.length = 4 * 4 := by
      simp only [cellPControlStates,
        ExhaustiveList.values_length_prod,
        FinalCarrierBound.spliceStates_length, twoBits_length]
    _ = 16 := rfl


abbrev SuccessorCell (psi kappa tau : Nat) :=
  B9FullCarrierHost.CellP (R2Coherence.Cell psi kappa tau)


abbrev CellPCode (psi kappa tau : Nat) :=
  R2Coherence.Cell psi kappa tau × (SpliceRole × (Bool × Bool))


def cellPOfCode (x : CellPCode psi kappa tau) :
    SuccessorCell psi kappa tau :=
  ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩


def codeOfCellP (u : SuccessorCell psi kappa tau) :
    CellPCode psi kappa tau :=
  (u.phys, (u.spliceRole, (u.repairPending, u.acquireTicket)))


theorem cellPOfCode_codeOfCellP (u : SuccessorCell psi kappa tau) :
    cellPOfCode (codeOfCellP u) = u := by
  rcases u with ⟨p, r, b, t⟩
  rfl


theorem codeOfCellP_cellPOfCode (x : CellPCode psi kappa tau) :
    codeOfCellP (cellPOfCode x) = x := by
  rcases x with ⟨p, r, b, t⟩
  rfl


theorem cellPOfCode_surjective (psi kappa tau : Nat) :
    Function.Surjective (cellPOfCode (psi := psi)
      (kappa := kappa) (tau := tau)) := by
  intro u
  exact ⟨codeOfCellP u, cellPOfCode_codeOfCellP u⟩


theorem cellPOfCode_injective (psi kappa tau : Nat) :
    Function.Injective (cellPOfCode (psi := psi)
      (kappa := kappa) (tau := tau)) :=
  injective_of_codec cellPOfCode codeOfCellP codeOfCellP_cellPOfCode


private def cellPSource (psi kappa tau : Nat) :
    ExhaustiveList (CellPCode psi kappa tau) :=
  ExhaustiveList.prod (coherenceStates psi kappa tau) cellPControlStates


private theorem cellPSource_values_nodup (psi kappa tau : Nat) :
    (cellPSource psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_prod
    (coherenceStates psi kappa tau) cellPControlStates
    (coherenceStates_values_nodup psi kappa tau)
    cellPControlStates_values_nodup


/-- Complete successor carrier before the separately-designed lease register. -/
def cellPStates (psi kappa tau : Nat) :
    ExhaustiveList (SuccessorCell psi kappa tau) :=
  ExhaustiveList.mapSurjective (cellPSource psi kappa tau)
    cellPOfCode (cellPOfCode_surjective psi kappa tau)


theorem cellPStates_values_nodup (psi kappa tau : Nat) :
    (cellPStates psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    (cellPSource psi kappa tau) cellPOfCode
    (cellPOfCode_surjective psi kappa tau)
    (cellPSource_values_nodup psi kappa tau)
    (cellPOfCode_injective psi kappa tau)


private theorem factor384_right (a L : Nat) :
    ((24 * a) * L) * 16 = (384 * a) * L := by
  calc
    ((24 * a) * L) * 16 = ((24 * 16) * a) * L := by ac_rfl
    _ = (384 * a) * L := rfl

private theorem factor_old_cell (a L : Nat) :
    (384 * a) * L = (24 * a) * (16 * L) := by
  rw [show 384 = 24 * 16 by decide]
  ac_rfl

private theorem factor_lease_right (a E L : Nat) :
    ((384 * a) * E) * L = (384 * a * L) * E := by
  ac_rfl

theorem cellPStates_length (psi kappa tau : Nat) :
    (cellPStates psi kappa tau).values.length =
      (384 * (4 * psi + 1)) *
        (ExpiringK2Projection.states psi kappa tau).values.length := by
  unfold cellPStates
  rw [ExhaustiveList.values_length_mapSurjective]
  unfold cellPSource
  rw [ExhaustiveList.values_length_prod]
  rw [coherenceStates_length, cellPControlStates_length]
  exact factor384_right (4 * psi + 1)
    (ExpiringK2Projection.states psi kappa tau).values.length



theorem cellPCarrier_decode_bijective (psi kappa tau : Nat) :
    Function.Injective (cellPStates psi kappa tau).decode ∧
      Function.Surjective (cellPStates psi kappa tau).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (cellPStates_values_nodup psi kappa tau),
    ExhaustiveList.decode_surjective _⟩


theorem cellPCarrier_card_le (psi kappa tau : Nat) :
    (cellPStates psi kappa tau).values.length ≤
      (384 * (4 * psi + 1)) *
        ExpiringK2Projection.localBound psi kappa tau := by
  rw [cellPStates_length]
  exact Nat.mul_le_mul_left (384 * (4 * psi + 1))
    (ExpiringK2Projection.state_bound psi kappa tau)


theorem cellPStates_length_as_oldCell (psi kappa tau : Nat) :
    (cellPStates psi kappa tau).values.length =
      (24 * (4 * psi + 1)) *
        (FinalCarrierBound.cellStates psi kappa tau).values.length := by
  rw [cellPStates_length, FinalCarrierBound.cellStates_length]
  exact factor_old_cell (4 * psi + 1)
    (ExpiringK2Projection.states psi kappa tau).values.length



/-! ## Parametric writer lease alphabet -/


abbrev LeasedCell (Lease : Type) (psi kappa tau : Nat) :=
  SuccessorCell psi kappa tau × Lease


def leasedStates {Lease : Type} (lease : ExhaustiveList Lease)
    (psi kappa tau : Nat) :
    ExhaustiveList (LeasedCell Lease psi kappa tau) :=
  ExhaustiveList.prod (cellPStates psi kappa tau) lease


theorem leasedStates_values_nodup {Lease : Type}
    (lease : ExhaustiveList Lease) (hlease : lease.values.Nodup)
    (psi kappa tau : Nat) :
    (leasedStates lease psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_prod
    (cellPStates psi kappa tau) lease
    (cellPStates_values_nodup psi kappa tau) hlease


theorem leasedCarrier_decode_bijective {Lease : Type}
    (lease : ExhaustiveList Lease) (hlease : lease.values.Nodup)
    (psi kappa tau : Nat) :
    Function.Injective (leasedStates lease psi kappa tau).decode ∧
      Function.Surjective (leasedStates lease psi kappa tau).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (leasedStates_values_nodup lease hlease psi kappa tau),
    ExhaustiveList.decode_surjective _⟩


theorem leasedStates_length {Lease : Type}
    (lease : ExhaustiveList Lease) (L psi kappa tau : Nat)
    (hL : lease.values.length = L) :
    (leasedStates lease psi kappa tau).values.length =
      (384 * (4 * psi + 1) * L) *
        (ExpiringK2Projection.states psi kappa tau).values.length := by
  unfold leasedStates
  rw [ExhaustiveList.values_length_prod]
  rw [cellPStates_length, hL]
  exact factor_lease_right (4 * psi + 1)
    (ExpiringK2Projection.states psi kappa tau).values.length L



theorem leasedStates_length_as_cellP {Lease : Type}
    (lease : ExhaustiveList Lease) (L psi kappa tau : Nat)
    (hL : lease.values.length = L) :
    (leasedStates lease psi kappa tau).values.length =
      L * (cellPStates psi kappa tau).values.length := by
  unfold leasedStates
  rw [ExhaustiveList.values_length_prod]
  rw [hL]
  exact Nat.mul_comm _ _



theorem leasedCarrier_card_le {Lease : Type}
    (lease : ExhaustiveList Lease) (L psi kappa tau : Nat)
    (hL : lease.values.length = L) :
    (leasedStates lease psi kappa tau).values.length ≤
      (384 * (4 * psi + 1) * L) *
        ExpiringK2Projection.localBound psi kappa tau := by
  rw [leasedStates_length lease L psi kappa tau hL]
  exact Nat.mul_le_mul_left (384 * (4 * psi + 1) * L)
    (ExpiringK2Projection.state_bound psi kappa tau)


/-! ## Witness scale: degree ten -/


/-- The accepted degree-nine B9 polynomial times quarantine and R2 fuel. -/
def cellPPoly (s : Nat) : Nat :=
  24 * (4 * s + 5) * FinalCarrierBound.cellPoly s


/-- Any finite lease certificate of length L multiplies the bound by L. -/
def leasedPoly (L s : Nat) : Nat := L * cellPPoly s


/-- This expansion makes the extra linear fuel factor visible; the remaining
factor is exactly the accepted degree-nine polynomial. -/
theorem cellPPoly_eq (s : Nat) :
    cellPPoly s =
      24 * (4 * s + 5) *
        (32 * 6606028800 * (s + 2) * (s + 1) * (2 * s + 3) *
          (12 * (s + 1) * (s + 2) + 1) * (4 * s + 5) *
          (2 * s + 5) ^ 2 * (16 * s + 17)) := by
  unfold cellPPoly
  rw [FinalCarrierBound.cellPoly_eq]


theorem leasedPoly_eq (L s : Nat) :
    leasedPoly L s =
      L * (24 * (4 * s + 5) *
        (32 * 6606028800 * (s + 2) * (s + 1) * (2 * s + 3) *
          (12 * (s + 1) * (s + 2) + 1) * (4 * s + 5) *
          (2 * s + 5) ^ 2 * (16 * s + 17))) := by
  unfold leasedPoly
  rw [cellPPoly_eq]


theorem cellPCarrier_card_le_at_witness (s : Nat) :
    (cellPStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      cellPPoly s := by
  rw [cellPStates_length_as_oldCell]
  have hfuel : 4 * (s + 1) + 1 = 4 * s + 5 := by omega
  rw [hfuel]
  unfold cellPPoly
  exact Nat.mul_le_mul_left (24 * (4 * s + 5))
    (FinalCarrierBound.cellCarrier_card_le_at_witness s)


theorem leasedCarrier_card_le_at_witness {Lease : Type}
    (lease : ExhaustiveList Lease) (L s : Nat)
    (hL : lease.values.length = L) :
    (leasedStates lease (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤ leasedPoly L s := by
  rw [leasedStates_length_as_cellP lease L]
  · unfold leasedPoly
    exact Nat.mul_le_mul_left L (cellPCarrier_card_le_at_witness s)
  · exact hL


/-- A convenient explicit coefficient for the degree-ten monomial bound. -/
def cellPMonomialCoeff : Nat :=
  24 * 9 * (32 * 61931520000000 * 3 ^ 8 * 33)


private theorem degree10_scalar (C s : Nat) :
    24 * ((9 * s) * (C * s ^ 9)) =
      (24 * 9 * C) * s ^ 10 := by
  rw [show s ^ 10 = s ^ 9 * s from Nat.pow_succ s 9]
  ac_rfl

theorem cellPCarrier_card_le_monomial (s : Nat) (hs : 1 ≤ s) :
    (cellPStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      cellPMonomialCoeff * s ^ 10 := by
  have hfuel : 4 * (s + 1) + 1 ≤ 9 * s := by omega
  have hold :
      (FinalCarrierBound.cellStates (s + 1) (s + 1)
        (16 * (s + 1))).values.length ≤
        (32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 :=
    FinalCarrierBound.cellCarrier_card_le_monomial s hs
  have hprod :
      (4 * (s + 1) + 1) *
          (FinalCarrierBound.cellStates (s + 1) (s + 1)
            (16 * (s + 1))).values.length ≤
        (9 * s) *
          ((32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9) :=
    Nat.mul_le_mul hfuel hold
  calc
    (cellPStates (s + 1) (s + 1)
        (16 * (s + 1))).values.length =
        24 * (4 * (s + 1) + 1) *
          (FinalCarrierBound.cellStates (s + 1) (s + 1)
            (16 * (s + 1))).values.length :=
      cellPStates_length_as_oldCell
        (s + 1) (s + 1) (16 * (s + 1))
    _ = 24 * ((4 * (s + 1) + 1) *
          (FinalCarrierBound.cellStates (s + 1) (s + 1)
            (16 * (s + 1))).values.length) := by
      exact Nat.mul_assoc 24 (4 * (s + 1) + 1)
        (FinalCarrierBound.cellStates (s + 1) (s + 1)
          (16 * (s + 1))).values.length
    _ ≤ 24 * ((9 * s) *
          ((32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9)) :=
      Nat.mul_le_mul_left 24 hprod
    _ = cellPMonomialCoeff * s ^ 10 := by
      unfold cellPMonomialCoeff
      exact degree10_scalar
        (32 * 61931520000000 * 3 ^ 8 * 33) s



theorem leasedCarrier_card_le_monomial {Lease : Type}
    (lease : ExhaustiveList Lease) (L s : Nat)
    (hL : lease.values.length = L) (hs : 1 ≤ s) :
    (leasedStates lease (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤
      (L * cellPMonomialCoeff) * s ^ 10 := by
  calc
    (leasedStates lease (s + 1) (s + 1)
        (16 * (s + 1))).values.length =
        L * (cellPStates (s + 1) (s + 1)
          (16 * (s + 1))).values.length :=
      leasedStates_length_as_cellP lease L
        (s + 1) (s + 1) (16 * (s + 1)) hL
    _ ≤ L * (cellPMonomialCoeff * s ^ 10) :=
      Nat.mul_le_mul_left L (cellPCarrier_card_le_monomial s hs)
    _ = (L * cellPMonomialCoeff) * s ^ 10 := by ac_rfl


theorem cellPCarrier_card_le_polyloglog (n : Nat) :
    let s := BirthShortDoneDispatcher.loglogScale n
    (cellPStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      cellPMonomialCoeff * s ^ 10 :=
  cellPCarrier_card_le_monomial
    (BirthShortDoneDispatcher.loglogScale n)
    (FinalCarrierBound.loglogScale_ge_one n)


theorem leasedCarrier_card_le_polyloglog {Lease : Type}
    (lease : ExhaustiveList Lease) (L n : Nat)
    (hL : lease.values.length = L) :
    let s := BirthShortDoneDispatcher.loglogScale n
    (leasedStates lease (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤
      (L * cellPMonomialCoeff) * s ^ 10 :=
  leasedCarrier_card_le_monomial lease L
    (BirthShortDoneDispatcher.loglogScale n) hL
    (FinalCarrierBound.loglogScale_ge_one n)


/-!
`leasedStates` is exhaustive for every supplied lease certificate.  Exact
finite-index decode bijectivity additionally assumes `lease.values.Nodup`, as
stated by `leasedCarrier_decode_bijective`; none of the cardinality upper
bounds needs that extra premise.
-/


end FinalCarrierBoundR2C
