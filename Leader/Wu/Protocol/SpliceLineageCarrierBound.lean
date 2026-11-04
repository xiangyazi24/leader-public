import Leader.Wu.Splice.HostTable
import Leader.Wu.Birth.DoneLineageQuarantine
import Leader.Wu.Comparison.ExpiringK2ProjectionFinite
import Leader.Wu.Birth.ShortDoneStateBound

/-!
Constructive local-state certificates for two distinct carriers.
No transition is unfolded, and no enormous list is evaluated.
The planned product does not assert integration of a lineage-aware row.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FinalCarrierBound

open PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open BirthDoneLineageQuarantineDesign

abbrev Cell (psi kappa tau : Nat) :=
  B9SpliceTableHost.Cell psi kappa tau

abbrev PlannedFinalAgent (psi kappa tau : Nat) :=
  Cell psi kappa tau × LineageRole

variable {psi kappa tau : Nat}

private theorem injective_of_codec {A B : Type}
    (f : A → B) (g : B → A) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  exact (h x).symm.trans ((congrArg g hxy).trans (h y))

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

private def spliceOfBits : Bool × Bool → SpliceRole
  | (false, false) => .none
  | (false, true) => .predecessorArmed
  | (true, false) => .victimArmed
  | (true, true) => .front

private def bitsOfSplice : SpliceRole → Bool × Bool
  | .none => (false, false)
  | .predecessorArmed => (false, true)
  | .victimArmed => (true, false)
  | .front => (true, true)

private theorem splice_roundtrip (r : SpliceRole) :
    spliceOfBits (bitsOfSplice r) = r := by
  cases r <;> rfl

private theorem splice_code_roundtrip (p : Bool × Bool) :
    bitsOfSplice (spliceOfBits p) = p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

private theorem splice_surjective : Function.Surjective spliceOfBits := by
  intro r
  exact ⟨bitsOfSplice r, splice_roundtrip r⟩

def spliceStates : ExhaustiveList SpliceRole :=
  ExhaustiveList.mapSurjective twoBits spliceOfBits splice_surjective

theorem spliceStates_values_nodup : spliceStates.values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    twoBits spliceOfBits splice_surjective twoBits_values_nodup
    (injective_of_codec spliceOfBits bitsOfSplice splice_code_roundtrip)

theorem spliceStates_length : spliceStates.values.length = 4 := by
  rw [spliceStates, ExhaustiveList.values_length_mapSurjective,
    twoBits_length]

private def lineageOfBits : Bool × Bool → LineageRole
  | (false, false) => .none
  | (false, true) => .sourceArmed
  | (true, false) => .predecessorPermit
  | (true, true) => .frontier

private def bitsOfLineage : LineageRole → Bool × Bool
  | .none => (false, false)
  | .sourceArmed => (false, true)
  | .predecessorPermit => (true, false)
  | .frontier => (true, true)

private theorem lineage_roundtrip (r : LineageRole) :
    lineageOfBits (bitsOfLineage r) = r := by
  cases r <;> rfl

private theorem lineage_code_roundtrip (p : Bool × Bool) :
    bitsOfLineage (lineageOfBits p) = p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

private theorem lineage_surjective : Function.Surjective lineageOfBits := by
  intro r
  exact ⟨bitsOfLineage r, lineage_roundtrip r⟩

def lineageStates : ExhaustiveList LineageRole :=
  ExhaustiveList.mapSurjective twoBits lineageOfBits lineage_surjective

theorem lineageStates_values_nodup : lineageStates.values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    twoBits lineageOfBits lineage_surjective twoBits_values_nodup
    (injective_of_codec lineageOfBits bitsOfLineage lineage_code_roundtrip)

theorem lineageStates_length : lineageStates.values.length = 4 := by
  rw [lineageStates, ExhaustiveList.values_length_mapSurjective,
    twoBits_length]

/-- Physical state, splice role, repairPending, acquireTicket. -/
abbrev CellCode (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau × (SpliceRole × (Bool × Bool))

def cellOfCode (x : CellCode psi kappa tau) : Cell psi kappa tau :=
  ⟨⟨⟨x.1, x.2.1⟩, x.2.2.1⟩, x.2.2.2⟩

def codeOfCell (u : Cell psi kappa tau) : CellCode psi kappa tau :=
  (u.carrier.splice.base,
    (u.carrier.splice.spliceRole,
      (u.carrier.repairPending, u.acquireTicket)))

theorem cellOfCode_codeOfCell (u : Cell psi kappa tau) :
    cellOfCode (codeOfCell u) = u := by
  rcases u with ⟨⟨⟨p, r⟩, b⟩, t⟩
  rfl

theorem codeOfCell_cellOfCode (x : CellCode psi kappa tau) :
    codeOfCell (cellOfCode x) = x := by
  rcases x with ⟨p, r, b, t⟩
  rfl

theorem cellOfCode_surjective (psi kappa tau : Nat) :
    Function.Surjective (cellOfCode (psi := psi)
      (kappa := kappa) (tau := tau)) := by
  intro u
  exact ⟨codeOfCell u, cellOfCode_codeOfCell u⟩

theorem cellOfCode_injective (psi kappa tau : Nat) :
    Function.Injective (cellOfCode (psi := psi)
      (kappa := kappa) (tau := tau)) :=
  injective_of_codec cellOfCode codeOfCell codeOfCell_cellOfCode

private def cellSource (psi kappa tau : Nat) :
    ExhaustiveList (CellCode psi kappa tau) :=
  ExhaustiveList.prod (ExpiringK2Projection.states psi kappa tau)
    (ExhaustiveList.prod spliceStates twoBits)

private theorem cellSource_values_nodup (psi kappa tau : Nat) :
    (cellSource psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_prod
    (ExpiringK2Projection.states psi kappa tau)
    (ExhaustiveList.prod spliceStates twoBits)
    (expiringAgentState_values_nodup psi kappa tau)
    (ExhaustiveList.values_nodup_prod spliceStates twoBits
      spliceStates_values_nodup twoBits_values_nodup)

/-- Covers every V6 record, not only well-formed or reachable controllers. -/
def cellStates (psi kappa tau : Nat) :
    ExhaustiveList (Cell psi kappa tau) :=
  ExhaustiveList.mapSurjective (cellSource psi kappa tau)
    cellOfCode (cellOfCode_surjective psi kappa tau)

theorem cellStates_values_nodup (psi kappa tau : Nat) :
    (cellStates psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_mapSurjective
    (cellSource psi kappa tau) cellOfCode
    (cellOfCode_surjective psi kappa tau)
    (cellSource_values_nodup psi kappa tau)
    (cellOfCode_injective psi kappa tau)

-- Do the scalar normalization on an abstract Nat, not on a state list.
private theorem factor16 (L : Nat) : L * (4 * 4) = 16 * L := by
  change L * 16 = 16 * L
  ac_rfl

theorem cellStates_length (psi kappa tau : Nat) :
    (cellStates psi kappa tau).values.length =
      16 * (ExpiringK2Projection.states psi kappa tau).values.length := by
  calc
    (cellStates psi kappa tau).values.length =
        (ExpiringK2Projection.states psi kappa tau).values.length *
          (4 * 4) := by
      simp only [cellStates, cellSource,
        ExhaustiveList.values_length_mapSurjective,
        ExhaustiveList.values_length_prod,
        spliceStates_length, twoBits_length]
    _ = 16 * (ExpiringK2Projection.states psi kappa tau).values.length :=
      factor16 _

theorem cellCarrier_decode_bijective (psi kappa tau : Nat) :
    Function.Injective (cellStates psi kappa tau).decode ∧
      Function.Surjective (cellStates psi kappa tau).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (cellStates_values_nodup psi kappa tau),
    ExhaustiveList.decode_surjective _⟩

theorem cellCarrier_card_le (psi kappa tau : Nat) :
    (cellStates psi kappa tau).values.length ≤
      16 * ExpiringK2Projection.localBound psi kappa tau := by
  calc
    (cellStates psi kappa tau).values.length =
        16 * (ExpiringK2Projection.states psi kappa tau).values.length :=
      cellStates_length psi kappa tau
    _ ≤ 16 * ExpiringK2Projection.localBound psi kappa tau :=
      Nat.mul_le_mul_left 16 (ExpiringK2Projection.state_bound psi kappa tau)
/-- One shared physical/controller cell and one four-valued lineage role. -/
def finalStates (psi kappa tau : Nat) :
    ExhaustiveList (PlannedFinalAgent psi kappa tau) :=
  ExhaustiveList.prod (cellStates psi kappa tau) lineageStates

theorem finalStates_values_nodup (psi kappa tau : Nat) :
    (finalStates psi kappa tau).values.Nodup :=
  ExhaustiveList.values_nodup_prod (cellStates psi kappa tau) lineageStates
    (cellStates_values_nodup psi kappa tau) lineageStates_values_nodup

private theorem factor64 (L : Nat) : (16 * L) * 4 = 64 * L := by
  calc
    (16 * L) * 4 = (16 * 4) * L := by ac_rfl
    _ = 64 * L := rfl

theorem finalStates_length (psi kappa tau : Nat) :
    (finalStates psi kappa tau).values.length =
      64 * (ExpiringK2Projection.states psi kappa tau).values.length := by
  calc
    (finalStates psi kappa tau).values.length =
        (cellStates psi kappa tau).values.length * 4 := by
      simp only [finalStates, ExhaustiveList.values_length_prod,
        lineageStates_length]
    _ = (16 * (ExpiringK2Projection.states psi kappa tau).values.length) * 4 := by
      rw [cellStates_length]
    _ = 64 * (ExpiringK2Projection.states psi kappa tau).values.length :=
      factor64 _

theorem finalCarrier_decode_bijective (psi kappa tau : Nat) :
    Function.Injective (finalStates psi kappa tau).decode ∧
      Function.Surjective (finalStates psi kappa tau).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (finalStates_values_nodup psi kappa tau),
    ExhaustiveList.decode_surjective _⟩

theorem finalCarrier_card_le (psi kappa tau : Nat) :
    (finalStates psi kappa tau).values.length ≤
      64 * ExpiringK2Projection.localBound psi kappa tau := by
  calc
    (finalStates psi kappa tau).values.length =
        64 * (ExpiringK2Projection.states psi kappa tau).values.length :=
      finalStates_length psi kappa tau
    _ ≤ 64 * ExpiringK2Projection.localBound psi kappa tau :=
      Nat.mul_le_mul_left 64 (ExpiringK2Projection.state_bound psi kappa tau)

private def witnessPoly (m s : Nat) : Nat :=
  (2 * m) * 6606028800 * (s + 2) * (s + 1) * (2 * s + 3) *
    (12 * (s + 1) * (s + 2) + 1) * (4 * s + 5) *
    (2 * s + 5) ^ 2 * (16 * s + 17)

/-- P16: the implemented carrier's degree-nine factored bound. -/
def cellPoly (s : Nat) : Nat := witnessPoly 16 s

/-- P64: the planned shared-base product's degree-nine factored bound. -/
def finalPoly (s : Nat) : Nat := witnessPoly 64 s

theorem cellPoly_eq (s : Nat) :
    cellPoly s =
      32 * 6606028800 * (s + 2) * (s + 1) * (2 * s + 3) *
        (12 * (s + 1) * (s + 2) + 1) * (4 * s + 5) *
        (2 * s + 5) ^ 2 * (16 * s + 17) := rfl

theorem finalPoly_eq (s : Nat) :
    finalPoly s =
      128 * 6606028800 * (s + 2) * (s + 1) * (2 * s + 3) *
        (12 * (s + 1) * (s + 2) + 1) * (4 * s + 5) *
        (2 * s + 5) ^ 2 * (16 * s + 17) := rfl

-- Only an explicit Nat polynomial is unfolded here, never a certificate.
private theorem localBound_witness_scaled (m s : Nat) :
    m * ExpiringK2Projection.localBound (s + 1) (s + 1)
      (16 * (s + 1)) = witnessPoly m s := by
  have hp : (s + 1) + 1 = s + 2 := by omega
  have h2 : 2 * (s + 1) + 1 = 2 * s + 3 := by omega
  have h4 : 4 * (s + 1) + 1 = 4 * s + 5 := by omega
  have hc : 2 * (s + 1) + 3 = 2 * s + 5 := by omega
  have ht : 16 * (s + 1) + 1 = 16 * s + 17 := by omega
  unfold ExpiringK2Projection.localBound witnessPoly
  rw [hp, h2, h4, hc, ht]
  ac_rfl

theorem cellCarrier_card_le_at_witness (s : Nat) :
    (cellStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      cellPoly s := by
  calc
    (cellStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
        16 * ExpiringK2Projection.localBound (s + 1) (s + 1)
          (16 * (s + 1)) :=
      cellCarrier_card_le (s + 1) (s + 1) (16 * (s + 1))
    _ = cellPoly s := localBound_witness_scaled 16 s

theorem finalCarrier_card_le_at_witness (s : Nat) :
    (finalStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      finalPoly s := by
  calc
    (finalStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
        64 * ExpiringK2Projection.localBound (s + 1) (s + 1)
          (16 * (s + 1)) :=
      finalCarrier_card_le (s + 1) (s + 1) (16 * (s + 1))
    _ = finalPoly s := localBound_witness_scaled 64 s

-- state_bound_poly already composes state_bound with carrier_le_poly.
-- This proof uses the uncapped witness psi=kappa=s+1, not psiChoice.
private theorem scaled_witness_monomial (m s : Nat) (hs : 1 ≤ s) :
    m * (ExpiringK2Projection.states (s + 1) (s + 1)
      (16 * (s + 1))).values.length ≤
      (m * 2 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 := by
  have hp :
      (ExpiringK2Projection.states (s + 1) (s + 1)
        (16 * (s + 1))).values.length ≤
        2 * 61931520000000 * (s + 2) ^ 8 * (16 * (s + 1) + 1) :=
    ExpiringK2Projection.state_bound_poly
      (ψ := s + 1) (κ := s + 1) (τ := 16 * (s + 1))
      (by omega) (by omega)
  have hk : s + 2 ≤ 3 * s := by omega
  have ht : 16 * (s + 1) + 1 ≤ 33 * s := by omega
  have hk8 : (s + 2) ^ 8 ≤ (3 * s) ^ 8 :=
    Nat.pow_le_pow_left hk 8
  calc
    m * (ExpiringK2Projection.states (s + 1) (s + 1)
        (16 * (s + 1))).values.length ≤
        m * (2 * 61931520000000 * (s + 2) ^ 8 *
          (16 * (s + 1) + 1)) := Nat.mul_le_mul_left m hp
    _ ≤ m * (2 * 61931520000000 * (3 * s) ^ 8 * (33 * s)) :=
      Nat.mul_le_mul_left m
        (Nat.mul_le_mul (Nat.mul_le_mul_left (2 * 61931520000000) hk8) ht)
    _ = (m * 2 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 := by
      rw [Nat.mul_pow, show s ^ 9 = s ^ 8 * s from Nat.pow_succ s 8]
      ac_rfl

theorem cellCarrier_card_le_monomial (s : Nat) (hs : 1 ≤ s) :
    (cellStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      (32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 := by
  calc
    (cellStates (s + 1) (s + 1) (16 * (s + 1))).values.length =
        16 * (ExpiringK2Projection.states (s + 1) (s + 1)
          (16 * (s + 1))).values.length :=
      cellStates_length (s + 1) (s + 1) (16 * (s + 1))
    _ ≤ (32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 :=
      scaled_witness_monomial 16 s hs

theorem finalCarrier_card_le_monomial (s : Nat) (hs : 1 ≤ s) :
    (finalStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      (128 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 := by
  calc
    (finalStates (s + 1) (s + 1) (16 * (s + 1))).values.length =
        64 * (ExpiringK2Projection.states (s + 1) (s + 1)
          (16 * (s + 1))).values.length :=
      finalStates_length (s + 1) (s + 1) (16 * (s + 1))
    _ ≤ (128 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 :=
      scaled_witness_monomial 64 s hs

theorem loglogScale_ge_one (n : Nat) :
    1 ≤ BirthShortDoneDispatcher.loglogScale n := by
  unfold BirthShortDoneDispatcher.loglogScale
  omega

theorem cellCarrier_card_le_polyloglog (n : Nat) :
    let s := BirthShortDoneDispatcher.loglogScale n
    (cellStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      (32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 :=
  cellCarrier_card_le_monomial
    (BirthShortDoneDispatcher.loglogScale n) (loglogScale_ge_one n)

theorem finalCarrier_card_le_polyloglog (n : Nat) :
    let s := BirthShortDoneDispatcher.loglogScale n
    (finalStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      (128 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9 :=
  finalCarrier_card_le_monomial
    (BirthShortDoneDispatcher.loglogScale n) (loglogScale_ge_one n)
-- A single bounded record proves nonemptiness without enumerating anything.
private def samplePhysical (psi kappa tau : Nat) (hpsi : 0 < psi) :
    ExpiringAgentState psi kappa tau :=
  let b : BoundedAgentState psi kappa := {
    leader := false
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := ⟨0, hpsi⟩
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false
  }
  ⟨⟨b, false⟩, 0⟩

private def sampleCell (psi kappa tau : Nat) (hpsi : 0 < psi) :
    Cell psi kappa tau :=
  cellOfCode (samplePhysical psi kappa tau hpsi, (.none, (false, false)))

private theorem positive_of_index (L : Nat) (i : Fin L) : 0 < L := by
  have hi := i.isLt
  omega

theorem cellStates_length_pos (psi kappa tau : Nat) (hpsi : 0 < psi) :
    0 < (cellStates psi kappa tau).values.length := by
  obtain ⟨i, _⟩ := ExhaustiveList.decode_surjective
    (cellStates psi kappa tau) (sampleCell psi kappa tau hpsi)
  exact positive_of_index _ i

theorem finalStates_length_pos (psi kappa tau : Nat) (hpsi : 0 < psi) :
    0 < (finalStates psi kappa tau).values.length := by
  obtain ⟨i, _⟩ := ExhaustiveList.decode_surjective
    (finalStates psi kappa tau) (sampleCell psi kappa tau hpsi, .none)
  exact positive_of_index _ i

/-- At s=0 the carrier still exists, but a constant times s^9 is zero. -/
theorem cellCarrier_monomial_zero_fails :
    ¬ (cellStates 1 1 16).values.length ≤
      (32 * 61931520000000 * 3 ^ 8 * 33) * (0 : Nat) ^ 9 := by
  have hpos := cellStates_length_pos 1 1 16 (by decide : 0 < 1)
  intro h
  have hz : (0 : Nat) ^ 9 = 0 :=
    Nat.zero_pow_of_pos 9 (by decide : 0 < 9)
  have hle : (cellStates 1 1 16).values.length ≤ 0 := by
    simpa only [hz, Nat.mul_zero] using h
  exact Nat.not_le_of_gt hpos hle

theorem finalCarrier_monomial_zero_fails :
    ¬ (finalStates 1 1 16).values.length ≤
      (128 * 61931520000000 * 3 ^ 8 * 33) * (0 : Nat) ^ 9 := by
  have hpos := finalStates_length_pos 1 1 16 (by decide : 0 < 1)
  intro h
  have hz : (0 : Nat) ^ 9 = 0 :=
    Nat.zero_pow_of_pos 9 (by decide : 0 < 9)
  have hle : (finalStates 1 1 16).values.length ≤ 0 := by
    simpa only [hz, Nat.mul_zero] using h
  exact Nat.not_le_of_gt hpos hle

/-- The factored bounds, unlike the monomial bounds, also cover s=0. -/
theorem zero_scale_factored_bounds :
    (cellStates 1 1 16).values.length ≤ cellPoly 0 ∧
      (finalStates 1 1 16).values.length ≤ finalPoly 0 :=
  ⟨cellCarrier_card_le_at_witness 0, finalCarrier_card_le_at_witness 0⟩

/-- This exactly characterizes the natural scales where the monomial holds. -/
theorem cellCarrier_monomial_iff (s : Nat) :
    ((cellStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      (32 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9) ↔ 1 ≤ s := by
  constructor
  · intro h
    by_cases hs : 1 ≤ s
    · exact hs
    · have hz : s = 0 := by omega
      subst s
      exact (cellCarrier_monomial_zero_fails h).elim
  · exact cellCarrier_card_le_monomial s

theorem finalCarrier_monomial_iff (s : Nat) :
    ((finalStates (s + 1) (s + 1) (16 * (s + 1))).values.length ≤
      (128 * 61931520000000 * 3 ^ 8 * 33) * s ^ 9) ↔ 1 ≤ s := by
  constructor
  · intro h
    by_cases hs : 1 ≤ s
    · exact hs
    · have hz : s = 0 := by omega
      subst s
      exact (finalCarrier_monomial_zero_fails h).elim
  · exact finalCarrier_card_le_monomial s

/-!
All witnesses above are carrier inhabitants, not reachable-state assertions.
At s=0, psi=1 is below the width-two R1 row's admissible psi range;
the carrier and its state-count certificates are nevertheless well-defined.
Neither planned-product finiteness nor its size bound proves that a
lineage-aware final transition has been integrated or is ghost-independent.
-/

end FinalCarrierBound
