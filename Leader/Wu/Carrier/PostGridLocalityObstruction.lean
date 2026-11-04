import Leader.Wu.Safety.CorrectedFormulation
import Leader.Wu.Carrier.FivePassStateCount
import Leader.Wu.Carrier.LinearPacking
import Leader.Wu.Carrier.ActiveStaging
import Leader.Wu.Carrier.PostGridScrub
import Leader.Wu.Epoch.VoterPeriodColors

/-!
# Post-grid sanitation boundary

This module does not claim an integrated arbitrary-soup compiler.  It proves
the exact locality obstruction that such a compiler must cross after the
period grid has stabilized.

There are two independent facts.  First, no row selected from the current two
endpoint states can authenticate a historical sweep or decide a remote bank
predicate on arbitrary configurations.  The three-cell witness uses the
literal `PackedCell` controls and is sharp for a hidden current-state cell.
Second, a periodic headless `preLease` carpet is a bottom configuration when
both of its alternating rows stutter.  Hence every total sanitizer must give
at least one such row a consumptive transition.  A proof-only lineage mark
cannot replace this physical transition-table obligation.

`PPLLStandalonePostGridScrub` supplies a length-`n` scrub word and strict rank,
but that transition would erase live transactions forever.  It is only the
cleanup kernel, not the missing writer handoff.
-/

namespace PPLLPostGridSanitationBoundary

open PPLLResearchFormulation PPLLLinearCarrierPacking
  PPLLPairedFivePassCarrier PPLLFixedActiveStaging
  PPLLStandalonePostGridScrub PPLLPeriodHColorVoter

set_option autoImplicit false
set_option warningAsError true

abbrev Config (n : Nat) (Q : Type) := Fin n -> Q

def edgeInput {n : Nat} {Q : Type} (ring : DirectedRing n)
    (C : Config n Q) (e : Fin n) : Q × Q :=
  (C e, C (ring.rightNeighbor e))

def rowFires {Q : Type} (T : Q -> Q -> Q × Q)
    (fires : (Q × Q) -> (Q × Q) -> Prop) (p : Q × Q) : Prop :=
  fires p (T p.1 p.2)

def PairLocalOn {n : Nat} {Q : Type} (ring : DirectedRing n)
    (Inv : Config n Q -> Prop)
    (Complete : Config n Q -> Fin n -> Prop) : Prop :=
  forall C D e, Inv C -> Inv D -> edgeInput ring C e = edgeInput ring D e ->
    (Complete C e <-> Complete D e)

/-- Exactness of a pairwise release row forces the purported completion
predicate to factor through the ordered endpoint view. -/
theorem exact_row_implies_pairLocalOn {n : Nat} {Q : Type}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (fires : (Q × Q) -> (Q × Q) -> Prop)
    (Inv : Config n Q -> Prop) (Complete : Config n Q -> Fin n -> Prop)
    (hexact : forall C, Inv C -> forall e,
      Complete C e <-> rowFires T fires (edgeInput ring C e)) :
    PairLocalOn ring Inv Complete := by
  intro C D e hC hD hp
  rw [hexact C hC e, hexact D hD e, hp]

/-- A ready state itself is an allowed initial state.  Thus no current local
tag, of any finite size, authenticates that a nonempty sweep occurred. -/
theorem arbitrary_initialization_forbids_history_authentication
    {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q -> Q -> Q × Q)
    (fires : (Q × Q) -> (Q × Q) -> Prop)
    (Swept : List (Fin n) -> Prop) (ready : Config n Q) (e : Fin n)
    (hready : rowFires T fires (edgeInput ring ready e))
    (hempty : ¬Swept []) :
    ¬(forall C initialWord edge,
      rowFires T fires
        (edgeInput ring (runLocalSchedule ring T C initialWord) edge) ->
      Swept initialWord) := by
  intro hs
  apply hempty
  exact hs ready [] e (by simpa [runLocalSchedule] using hready)

/-! ## Exact current-state premise for release -/

def BanksEqual {h : Nat} (q : PackedCell h) : Prop :=
  q.activeBit = q.stagingBit

instance decidableBanksEqual {h : Nat} (q : PackedCell h) :
    Decidable (BanksEqual q) := by
  unfold BanksEqual
  infer_instance

def AllBanksEqual {n h : Nat} (C : Config n (PackedCell h)) : Prop :=
  forall i, BanksEqual (C i)

def OutsideBanksEqual {n h : Nat} (ring : DirectedRing n) (e : Fin n)
    (C : Config n (PackedCell h)) : Prop :=
  forall i, i ≠ e -> i ≠ ring.rightNeighbor e -> BanksEqual (C i)

/-- Scrubbing the selected pair makes the whole ring bank-equal exactly when
the unselected footprint was already bank-equal. -/
theorem allBanksEqual_scrub_iff_outside {n h : Nat}
    (ring : DirectedRing n) (C : Config n (PackedCell h)) (e : Fin n) :
    AllBanksEqual (localStep ring scrubTransition C e) <->
      OutsideBanksEqual ring e C := by
  constructor
  · intro hall i hie hir
    simpa [BanksEqual, localStep, hie, hir] using hall i
  · intro hout i
    by_cases hie : i = e
    · subst i
      simp [BanksEqual, localStep, scrubTransition]
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        simp [BanksEqual, localStep, scrubTransition, hie]
      · simpa [BanksEqual, localStep, hie, hir] using hout i hie hir

/-! ## Sharp three-cell forged-return witness -/

theorem ringTwo : DirectedRing 2 := ⟨by omega⟩

@[simp] theorem ringTwo_right_zero :
    ringTwo.rightNeighbor (0 : Fin 2) = 1 := by
  apply Fin.ext
  decide

/-- No current-state cell is hidden from edge zero on two vertices. -/
theorem ringTwo_edge_zero_covers (i : Fin 2) :
    i = (0 : Fin 2) ∨ i = ringTwo.rightNeighbor 0 := by
  by_cases hi : i = 0
  · exact Or.inl hi
  · right
    rw [ringTwo_right_zero]
    apply Fin.ext
    omega

theorem ringThree : DirectedRing 3 := ⟨by omega⟩

@[simp] theorem ringThree_right_zero :
    ringThree.rightNeighbor (0 : Fin 3) = 1 := by
  apply Fin.ext
  decide

def auditCell3 (pos : Fin 3) (active staging : Bool)
    (control : RootCtl32) (lease : Trail16) : PackedCell 3 :=
  { pos := pos, activeBit := active, stagingBit := staging, role := 0,
    rootCtl := control, message := 0, trail := lease }

def returnRoot : PackedCell 3 :=
  auditCell3 0 false false releasePhase postLease

def returnNeighbor : PackedCell 3 := auditCell3 1 false false 0 0
def hiddenGood : PackedCell 3 := auditCell3 2 false false 0 0
def hiddenMismatch : PackedCell 3 := auditCell3 2 false true 0 0

def completedReturnConfig : Config 3 (PackedCell 3) :=
  fun i => if i = 0 then returnRoot
    else if i = 1 then returnNeighbor else hiddenGood

def forgedReturnConfig : Config 3 (PackedCell 3) :=
  fun i => if i = 0 then returnRoot
    else if i = 1 then returnNeighbor else hiddenMismatch

theorem completedReturnConfig_banksEqual :
    AllBanksEqual completedReturnConfig := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    decide

theorem forgedReturnConfig_not_banksEqual :
    ¬AllBanksEqual forgedReturnConfig := by
  intro hall
  have h := hall 2
  simp [BanksEqual, forgedReturnConfig, hiddenMismatch, auditCell3] at h

@[simp] theorem return_edge_same_view :
    edgeInput ringThree completedReturnConfig 0 =
      edgeInput ringThree forgedReturnConfig 0 := by
  simp [edgeInput, completedReturnConfig, forgedReturnConfig]

/-- Even a predicate of the complete endpoint states (hence a fortiori one of
only `rootCtl`/`trail`) cannot fire exactly when the remote bank is complete. -/
theorem no_exact_pair_release_for_global_banks
    (T : PackedCell 3 -> PackedCell 3 -> PackedCell 3 × PackedCell 3)
    (fires : (PackedCell 3 × PackedCell 3) ->
      (PackedCell 3 × PackedCell 3) -> Prop) :
    ¬(forall C e, AllBanksEqual C <->
      rowFires T fires (edgeInput ringThree C e)) := by
  intro hexact
  have hgood := (hexact completedReturnConfig 0).mp
    completedReturnConfig_banksEqual
  have hbad : rowFires T fires
      (edgeInput ringThree forgedReturnConfig 0) := by
    simpa using hgood
  exact forgedReturnConfig_not_banksEqual
    ((hexact forgedReturnConfig 0).mpr hbad)

/-- A hidden pseudo-head survives a disjoint release row.  Therefore head
re-emission must tolerate duplicates and provide a consuming collision rule. -/
def IsRollHead (q : PackedCell 3) : Prop := q.rootCtl = rollForwardPhase

def hiddenRollHead : PackedCell 3 :=
  auditCell3 2 false false rollForwardPhase 0

def duplicateHeadConfig : Config 3 (PackedCell 3) :=
  fun i => if i = 0 then returnRoot
    else if i = 1 then returnNeighbor else hiddenRollHead

theorem local_reemit_leaves_hidden_head
    (T : PackedCell 3 -> PackedCell 3 -> PackedCell 3 × PackedCell 3)
    (hemit : IsRollHead
      (localStep ringThree T completedReturnConfig 0 1)) :
    let out := localStep ringThree T duplicateHeadConfig 0
    IsRollHead (out 1) ∧ IsRollHead (out 2) := by
  dsimp
  constructor
  · simpa [IsRollHead, localStep, completedReturnConfig,
      duplicateHeadConfig] using hemit
  · simp [IsRollHead, localStep, duplicateHeadConfig,
      hiddenRollHead, auditCell3]

/-! ## Periodic headless-lease bottom class -/

theorem ringFour : DirectedRing 4 := ⟨by omega⟩

@[simp] theorem ringFour_right_zero :
    ringFour.rightNeighbor (0 : Fin 4) = 1 := by apply Fin.ext; decide
@[simp] theorem ringFour_right_one :
    ringFour.rightNeighbor (1 : Fin 4) = 2 := by apply Fin.ext; decide
@[simp] theorem ringFour_right_two :
    ringFour.rightNeighbor (2 : Fin 4) = 3 := by apply Fin.ext; decide
@[simp] theorem ringFour_right_three :
    ringFour.rightNeighbor (3 : Fin 4) = 0 := by apply Fin.ext; decide

def carpetCell (pos : Fin 2) : PackedCell 2 :=
  { pos := pos, activeBit := false, stagingBit := true, role := 0,
    rootCtl := 0, message := 0, trail := preLease }

def headlessLeaseCarpet : Config 4 (PackedCell 2) :=
  fun i => if i = 0 then carpetCell 0
    else if i = 1 then carpetCell 1
    else if i = 2 then carpetCell 0 else carpetCell 1

/-- The hostile carpet already lies on the stabilized period-two grid; no
grid-repair corridor argument is hidden in the obstruction. -/
theorem headlessLeaseCarpet_successorGrid :
    SuccessorGrid (by omega) ringFour (fun i => (headlessLeaseCarpet i).pos) := by
  intro e
  have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl <;>
    decide

theorem localStep_eq_of_all_rows_stutter {n : Nat} {Q : Type}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q) (C : Config n Q)
    (hstutter : forall e, T (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) (e : Fin n) :
    localStep ring T C e = C := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [localStep, hstutter e]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp [localStep, hstutter e, hie]
    · simp [localStep, hstutter e, hie, hir]

theorem run_eq_of_all_rows_stutter {n : Nat} {Q : Type}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q) (C : Config n Q)
    (hstutter : forall e, T (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) (word : DetSchedule n) :
    runLocalSchedule ring T C word = C := by
  induction word with
  | nil => rfl
  | cons e rest ih =>
      rw [runLocalSchedule, localStep_eq_of_all_rows_stutter ring T C
        hstutter e, ih]

theorem carpet_rows_stutter
    (T : PackedCell 2 -> PackedCell 2 -> PackedCell 2 × PackedCell 2)
    (h01 : T (carpetCell 0) (carpetCell 1) =
      (carpetCell 0, carpetCell 1))
    (h10 : T (carpetCell 1) (carpetCell 0) =
      (carpetCell 1, carpetCell 0)) (e : Fin 4) :
    T (headlessLeaseCarpet e)
      (headlessLeaseCarpet (ringFour.rightNeighbor e)) =
      (headlessLeaseCarpet e,
        headlessLeaseCarpet (ringFour.rightNeighbor e)) := by
  have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl
  · simpa [headlessLeaseCarpet] using h01
  · simpa [headlessLeaseCarpet] using h10
  · simpa [headlessLeaseCarpet] using h01
  · simpa [headlessLeaseCarpet] using h10

theorem headlessLeaseCarpet_not_scrubbed :
    ¬ConfigScrubbed headlessLeaseCarpet := by
  intro hall
  have h := hall 0
  simp [CellScrubbed, scrubCell, headlessLeaseCarpet, carpetCell] at h

/-- If both periodic interior rows stutter, the hostile carpet is a bottom
singleton under every finite schedule, including every iid sample path. -/
theorem headlessLeaseCarpet_bottom
    (T : PackedCell 2 -> PackedCell 2 -> PackedCell 2 × PackedCell 2)
    (h01 : T (carpetCell 0) (carpetCell 1) =
      (carpetCell 0, carpetCell 1))
    (h10 : T (carpetCell 1) (carpetCell 0) =
      (carpetCell 1, carpetCell 0)) (word : DetSchedule 4) :
    runLocalSchedule ringFour T headlessLeaseCarpet word =
      headlessLeaseCarpet := by
  exact run_eq_of_all_rows_stutter ringFour T headlessLeaseCarpet
    (carpet_rows_stutter T h01 h10) word

/-- Any transition that reaches any predicate excluding the hostile carpet
must consume at least one alternating row.  This is independent of how the
eventual clean compiler domain is defined. -/
theorem escape_carpet_requires_consumptive_lease_row
    (T : PackedCell 2 -> PackedCell 2 -> PackedCell 2 × PackedCell 2)
    (Done : Config 4 (PackedCell 2) -> Prop)
    (hnotDone : ¬Done headlessLeaseCarpet)
    (hreaches : exists word : DetSchedule 4,
      Done (runLocalSchedule ringFour T headlessLeaseCarpet word)) :
    T (carpetCell 0) (carpetCell 1) ≠ (carpetCell 0, carpetCell 1) ∨
      T (carpetCell 1) (carpetCell 0) ≠ (carpetCell 1, carpetCell 0) := by
  by_cases h01 : T (carpetCell 0) (carpetCell 1) =
      (carpetCell 0, carpetCell 1)
  · by_cases h10 : T (carpetCell 1) (carpetCell 0) =
        (carpetCell 1, carpetCell 0)
    · exfalso
      obtain ⟨word, hclean⟩ := hreaches
      rw [headlessLeaseCarpet_bottom T h01 h10 word] at hclean
      exact hnotDone hclean
    · exact Or.inr h10
  · exact Or.inl h01

/-- Canonical-idle specialization of the generic obstruction. -/
theorem total_sanitation_requires_consumptive_lease_row
    (T : PackedCell 2 -> PackedCell 2 -> PackedCell 2 × PackedCell 2)
    (hreaches : exists word : DetSchedule 4,
      ConfigScrubbed
        (runLocalSchedule ringFour T headlessLeaseCarpet word)) :
    T (carpetCell 0) (carpetCell 1) ≠ (carpetCell 0, carpetCell 1) ∨
      T (carpetCell 1) (carpetCell 0) ≠ (carpetCell 1, carpetCell 0) := by
  exact escape_carpet_requires_consumptive_lease_row T ConfigScrubbed
    headlessLeaseCarpet_not_scrubbed hreaches

/-! The five numerically distinct closing codes fit in the existing `Fin 32`
only by reinterpreting 27--31.  This proves numeric capacity, not semantic
noncollision with the unformalized older five-pass table. -/

def postForwardSecondPhase : RootCtl32 := ⟨28, by omega⟩
def postReturnPhase : RootCtl32 := ⟨29, by omega⟩
def abortRightPhase : RootCtl32 := ⟨30, by omega⟩
def abortLeftPhase : RootCtl32 := ⟨31, by omega⟩
def spentRightTrail : Trail16 := ⟨14, by omega⟩
def spentLeftTrail : Trail16 := ⟨15, by omega⟩

@[simp] theorem postForwardSecondPhase_eq_releasePhase :
    postForwardSecondPhase = releasePhase := rfl

theorem closing_phase_codes_pairwise_distinct :
    [rollForwardPhase, postForwardSecondPhase, postReturnPhase,
      abortRightPhase, abortLeftPhase].Nodup := by
  decide

theorem transaction_trail_codes_pairwise_distinct :
    [preLease, postLease, spentRightTrail, spentLeftTrail].Nodup := by
  decide

theorem sanitation_boundary_base_carrier_count (h : Nat) :
    (packedCellStates h).values.length = 262144 * h :=
  packedCellStates_length h

end PPLLPostGridSanitationBoundary
