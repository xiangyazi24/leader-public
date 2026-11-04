import Leader.Wu.Carrier.ValidatorPackedCarrier
import Leader.Wu.Carrier.ActiveStaging
import Leader.Wu.Carrier.RoleThreePostRoute

/-!
# QMAT payload boundary and two-block footprint

The literal validator changes only its reserved mode tags.  This module lifts
that local fact to arbitrary finite QMAT schedules and states the exact
two-full-block payload relation needed by a later AAFJ courier.  It deliberately
does not postulate a courier producer: if the desired prepared staging bank is
different initially, pure QMAT execution cannot create it.
-/

namespace PPLLV2ValidatorPhysicalRefinement

open PPLLLinearCarrierPacking
open PPLLParallelGeometryLift
open PPLLParallelGeometryPacked
open PPLLFixedActiveStaging
open PPLLRole3PostRoute

set_option autoImplicit false
set_option warningAsError true

/-- The complete physical staging bank, before choosing any block footprint. -/
def packedStaging {n h : Nat} (q : Fin n → PackedCell h) : Fin n → Bool :=
  fun i ↦ (q i).stagingBit

/-- On the complete actual-grid transition, the QMAT row preserves every
cell's staging payload bit.  Thus a prepared full bank is an invariant of
validation, not something validation can produce. -/
theorem packed_qmat_staging_framed {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (q : Fin n → PackedCell h) (edge : Fin n) :
    packedStaging
        (packedParallelStep hh ring (packedQmatControlRow h) q edge) =
      packedStaging q := by
  funext i
  simp only [packedStaging, packedParallelStep, joinPacked, parallelStep]
  by_cases hie : i = edge
  · subst i
    simp only [if_pos]
    exact (packedLiteralStep_payload_framed
      (splitPacked (q edge)).2
      (splitPacked (q (ring.rightNeighbor edge))).2).2.2.1
  · by_cases hir : i = ring.rightNeighbor edge
    · rw [if_neg hie, if_pos hir]
      change (packedLiteralStep
          (splitPacked (q edge)).2
          (splitPacked (q (ring.rightNeighbor edge))).2).2.stagingBit =
        (q i).stagingBit
      rw [hir]
      exact (packedLiteralStep_payload_framed
        (splitPacked (q edge)).2
        (splitPacked (q (ring.rightNeighbor edge))).2).2.2.2.1
    · rw [if_neg hie, if_neg hir]
      rfl

/-- Iteration of the actual parallel position/QMAT row on a finite schedule. -/
def runPackedQmat {n h : Nat} (hh : 0 < h) (ring : DirectedRing n) :
    (Fin n → PackedCell h) → List (Fin n) → Fin n → PackedCell h
  | q, [] => q
  | q, edge :: rest =>
      runPackedQmat hh ring
        (packedParallelStep hh ring (packedQmatControlRow h) q edge) rest

/-- Every finite pure-QMAT schedule preserves the complete staging function,
including cells outside the currently represented corridor. -/
theorem runPackedQmat_staging_framed {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (q : Fin n → PackedCell h)
    (schedule : List (Fin n)) :
    packedStaging (runPackedQmat hh ring q schedule) = packedStaging q := by
  induction schedule generalizing q with
  | nil => rfl
  | cons edge rest ih =>
      rw [runPackedQmat, ih]
      exact packed_qmat_staging_framed hh ring q edge

/-- If a target staging function differs from the initial one, no finite
schedule containing only QMAT rows can produce that target. -/
theorem pure_qmat_schedule_cannot_produce_staging
    {n h : Nat} (hh : 0 < h) (ring : DirectedRing n)
    (q : Fin n → PackedCell h) (target : Fin n → Bool)
    (hdifferent : packedStaging q ≠ target)
    (schedule : List (Fin n)) :
    packedStaging (runPackedQmat hh ring q schedule) ≠ target := by
  rw [runPackedQmat_staging_framed]
  exact hdifferent

/-! ## Phase-specific courier code budget -/

/-- During label comparison the auxiliary nibble stores the four comparison
flags; during the write phase it stores the finite AAFJ branch code.  They are
not stored simultaneously.  The route nibble and one carried bit are common. -/
inductive CourierMicrostate where
  | compare (route flags : Fin 16) (carried : Bool)
  | write (route branch : Fin 16) (carried : Bool)
  deriving DecidableEq, Repr

private def courierHalfIndex (route auxiliary : Fin 16)
    (carried : Bool) : Nat :=
  route.val * 32 + auxiliary.val * 2 + carried.toNat

private theorem courierHalfIndex_lt (route auxiliary : Fin 16)
    (carried : Bool) : courierHalfIndex route auxiliary carried < 512 := by
  cases carried <;> simp [courierHalfIndex] <;> omega

/-- Exact ten-bit phase-specific index: `0..511` is comparison and
`512..1023` is writing. -/
def courierStateCode : CourierMicrostate → Fin 1024
  | .compare route flags carried =>
      ⟨courierHalfIndex route flags carried, by
        exact Nat.lt_trans (courierHalfIndex_lt route flags carried) (by omega)⟩
  | .write route branch carried =>
      ⟨512 + courierHalfIndex route branch carried, by
        have := courierHalfIndex_lt route branch carried
        omega⟩

theorem courierStateCode_injective : Function.Injective courierStateCode := by
  intro left right hcode
  cases left with
  | compare leftRoute leftAux leftBit =>
      cases right with
      | compare rightRoute rightAux rightBit =>
          have hval := congrArg Fin.val hcode
          have hroute : leftRoute = rightRoute := by
            apply Fin.ext
            cases leftBit <;> cases rightBit <;>
              simp [courierStateCode, courierHalfIndex] at hval <;> omega
          have haux : leftAux = rightAux := by
            apply Fin.ext
            cases leftBit <;> cases rightBit <;>
              simp [courierStateCode, courierHalfIndex] at hval <;> omega
          subst rightRoute
          subst rightAux
          cases leftBit <;> cases rightBit <;>
            simp [courierStateCode, courierHalfIndex] at hcode ⊢
      | write rightRoute rightAux rightBit =>
          have hval := congrArg Fin.val hcode
          have hleft := courierHalfIndex_lt leftRoute leftAux leftBit
          simp [courierStateCode] at hval
          omega
  | write leftRoute leftAux leftBit =>
      cases right with
      | compare rightRoute rightAux rightBit =>
          have hval := congrArg Fin.val hcode
          have hright := courierHalfIndex_lt rightRoute rightAux rightBit
          simp [courierStateCode] at hval
          omega
      | write rightRoute rightAux rightBit =>
          have hval := congrArg Fin.val hcode
          have hroute : leftRoute = rightRoute := by
            apply Fin.ext
            cases leftBit <;> cases rightBit <;>
              simp [courierStateCode, courierHalfIndex] at hval <;> omega
          have haux : leftAux = rightAux := by
            apply Fin.ext
            cases leftBit <;> cases rightBit <;>
              simp [courierStateCode, courierHalfIndex] at hval <;> omega
          subst rightRoute
          subst rightAux
          cases leftBit <;> cases rightBit <;>
            simp [courierStateCode, courierHalfIndex] at hcode ⊢

/-- The courier reserves precisely role `3`, root controls `0..3`, arbitrary
messages, and trails `0..7`.  This is `4*32*8 = 1024` codes, leaving the
existing leases `12/13` and post-route controls `27..29` untouched. -/
def encodeCourierControl (base : PackedControl) (state : CourierMicrostate) :
    PackedControl :=
  let code := courierStateCode state
  { base with
    role := stagingRole
    rootCtl := ⟨code.val / 256, by have := code.isLt; omega⟩
    message := ⟨(code.val / 8) % 32, Nat.mod_lt _ (by omega)⟩
    trail := ⟨code.val % 8, by
      have hmod := Nat.mod_lt code.val (by omega : 0 < 8)
      omega⟩ }

/-- Decode the reserved courier box to its raw ten-bit code. -/
def decodeCourierCode (control : PackedControl) : Option (Fin 1024) :=
  if hreserved : control.role = stagingRole ∧
      control.rootCtl.val < 4 ∧ control.trail.val < 8 then
    some ⟨control.rootCtl.val * 256 + control.message.val * 8 +
      control.trail.val, by
        have hmessage := control.message.isLt
        omega⟩
  else none

@[simp] theorem decodeCourierCode_encodeCourierControl
    (base : PackedControl) (state : CourierMicrostate) :
    decodeCourierCode (encodeCourierControl base state) =
      some (courierStateCode state) := by
  have hcode := (courierStateCode state).isLt
  unfold decodeCourierCode
  split
  · apply congrArg some
    apply Fin.ext
    dsimp [encodeCourierControl]
    omega
  · rename_i hnot
    exfalso
    apply hnot
    dsimp [encodeCourierControl]
    refine ⟨rfl, ?_, ?_⟩
    · omega
    · exact Nat.mod_lt _ (by omega)

theorem decodeLiteralTag_encodeCourierControl
    (base : PackedControl) (state : CourierMicrostate) :
    decodeLiteralTag (encodeCourierControl base state).role
        (encodeCourierControl base state).rootCtl = none := by
  exact decodeLiteralTag_role_three _

theorem decodePostRoute_encodeCourierControl
    (base : PackedControl) (state : CourierMicrostate) :
    decodePostRoute (encodeCourierControl base state) = none := by
  have htrail : (encodeCourierControl base state).trail.val < 8 := by
    exact Nat.mod_lt _ (by omega)
  have hpost : (encodeCourierControl base state).trail ≠ postLease := by
    intro heq
    have hval := congrArg Fin.val heq
    change _ = 13 at hval
    omega
  simp [decodePostRoute, hpost]

theorem courier_code_capacity_exact :
    2 * (16 * 16 * 2) = 4 * 32 * 8 := by decide

/-! ## Exact two-full-block payload footprint -/

/-- Two consecutive full `h`-cell blocks.  The source-to-target boundary is
included, while the edge leaving the target block is deliberately outside the
footprint.  Injectivity excludes wrap coincidence inside these `2*h` sites. -/
structure TwoBlockFootprint {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) where
  site : BlockSide → Fin h → Fin n
  injective : Function.Injective (fun p : BlockSide × Fin h ↦ site p.1 p.2)
  sourceSuccessor : ∀ (slot : Fin h) (hnext : slot.val + 1 < h),
    site .source ⟨slot.val + 1, hnext⟩ =
      ring.rightNeighbor (site .source slot)
  sourceTargetBoundary :
    site .target ⟨0, hh⟩ =
      ring.rightNeighbor (site .source ⟨h - 1, by omega⟩)
  targetSuccessor : ∀ (slot : Fin h) (hnext : slot.val + 1 < h),
    site .target ⟨slot.val + 1, hnext⟩ =
      ring.rightNeighbor (site .target slot)

/-- The stabilized stored position agrees with the logical slot throughout
both blocks. -/
def TwoBlockFootprint.PositionAligned
    {n h : Nat} {hh : 0 < h} {ring : DirectedRing n}
    (footprint : TwoBlockFootprint hh ring)
    (q : Fin n → PackedCell h) : Prop :=
  ∀ side slot, (q (footprint.site side slot)).pos = slot

/-- Active source words physically read from the two full blocks. -/
def footprintActive {n k : Nat} {ring : DirectedRing n}
    (footprint : TwoBlockFootprint (width_pos k) ring)
    (q : Fin n → PackedCell (width k)) : BlockSide → SpatialWord k :=
  fun side slot ↦ (q (footprint.site side slot)).activeBit

/-- Staging source words physically read from the two full blocks. -/
def footprintStaging {n k : Nat} {ring : DirectedRing n}
    (footprint : TwoBlockFootprint (width_pos k) ring)
    (q : Fin n → PackedCell (width k)) : BlockSide → SpatialWord k :=
  fun side slot ↦ (q (footprint.site side slot)).stagingBit

/-- Exact current-payload premise before a virtual AAFJ transaction. -/
def RepresentsActivePair {n k : Nat} {ring : DirectedRing n}
    (footprint : TwoBlockFootprint (width_pos k) ring)
    (q : Fin n → PackedCell (width k)) (old : AAFJPK.State k × AAFJPK.State k) :
    Prop :=
  footprintActive footprint q = pairWord old

/-- Exact full successor-payload obligation which a physical producer, not
the validator, must establish before linearization. -/
def PreparedStagingPair {n k : Nat} (hk : 0 < k)
    {ring : DirectedRing n}
    (footprint : TwoBlockFootprint (width_pos k) ring)
    (q : Fin n → PackedCell (width k)) (old : AAFJPK.State k × AAFJPK.State k) :
    Prop :=
  footprintStaging footprint q = (preparedBanks hk old).staging

/-- Pure QMAT preserves, but cannot establish, the exact prepared-bank
predicate on a two-block footprint. -/
theorem preparedStagingPair_runPackedQmat_iff
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (footprint : TwoBlockFootprint (width_pos k) ring)
    (q : Fin n → PackedCell (width k)) (old : AAFJPK.State k × AAFJPK.State k)
    (schedule : List (Fin n)) :
    PreparedStagingPair hk footprint
        (runPackedQmat (width_pos k) ring q schedule) old ↔
      PreparedStagingPair hk footprint q old := by
  unfold PreparedStagingPair footprintStaging
  have hframe := runPackedQmat_staging_framed
    (width_pos k) ring q schedule
  have hfootprint :
      (fun side slot ↦
          (runPackedQmat (width_pos k) ring q schedule
            (footprint.site side slot)).stagingBit) =
        (fun side slot ↦ (q (footprint.site side slot)).stagingBit) := by
    funext side slot
    exact congrFun hframe (footprint.site side slot)
  rw [hfootprint]

/-- Direct two-block no-go: a mismatching initial staging bank cannot become
the proof-level `preparedBanks` target under any pure-QMAT schedule. -/
theorem pure_qmat_cannot_prepare_pair
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (footprint : TwoBlockFootprint (width_pos k) ring)
    (q : Fin n → PackedCell (width k)) (old : AAFJPK.State k × AAFJPK.State k)
    (hdifferent : ¬ PreparedStagingPair hk footprint q old)
    (schedule : List (Fin n)) :
    ¬ PreparedStagingPair hk footprint
      (runPackedQmat (width_pos k) ring q schedule) old := by
  rwa [preparedStagingPair_runPackedQmat_iff]

#print axioms runPackedQmat_staging_framed
#print axioms pure_qmat_schedule_cannot_produce_staging
#print axioms courierStateCode_injective
#print axioms decodeCourierCode_encodeCourierControl
#print axioms decodeLiteralTag_encodeCourierControl
#print axioms decodePostRoute_encodeCourierControl
#print axioms preparedStagingPair_runPackedQmat_iff
#print axioms pure_qmat_cannot_prepare_pair

end PPLLV2ValidatorPhysicalRefinement
