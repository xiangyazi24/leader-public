import Leader.AAFJ.Centered.BarrierCycle
import Leader.AAFJ.Centered.CoalescenceFrame
import Leader.Core.SymmetricKilledWalkFiniteTree

/-!
# Trial-local lineage for centered AAFJ barrier coalescence

This module keeps lineage tags only while the charged-support count is fixed.
Every physical step is classified for a support drop before any tag transport;
merger and cancellation branches therefore terminate without selecting a
surviving ancestor.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace CoalescenceTrial

open BarrierAlgebra CoalescenceFrame
open CoalescenceCycle

set_option autoImplicit false

abbrev Config (n k : Nat) := Fin n → State k

/-- One raw centered-protocol interaction. -/
def rawStep {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) (edge : Fin n) : Config n k :=
  (protocol k hk).step ring C edge

/-- Charged-support count of a physical configuration. -/
def supportCount {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) : Nat :=
  barrierCount hk ring (labelsOf C)

/-- A trial-local rear/front pair.  The tags name current charged edges, not
historical charge particles. -/
structure Tags (n : Nat) where
  rear : Fin n
  front : Fin n
  ne : rear ≠ front

/-- A tag advances exactly on its own phase-one barrier interaction.  This
function is used only after a proof that support count did not drop. -/
def transportTag {n k : Nat} (_hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) (selected tag : Fin n) : Fin n :=
  if selected = tag then
    if (C selected).phase = true then ring.rightNeighbor tag else tag
  else tag

/-- The exact support-drop predicate. -/
def Drops {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) (selected : Fin n) : Prop :=
  supportCount hk ring (rawStep hk ring C selected) <
    supportCount hk ring C

instance instDecidableDrops {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k) (selected : Fin n) :
    Decidable (Drops hk ring C selected) := by
  unfold Drops supportCount
  infer_instance

/-- A no-drop step has exactly the old support cardinality. -/
theorem supportCount_eq_of_not_drops {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (hnodrop : ¬ Drops hk ring C selected) :
    supportCount hk ring (rawStep hk ring C selected) =
      supportCount hk ring C := by
  have hle := protocol_step_barrierCount_le hk ring hn2 C selected
  change ¬ supportCount hk ring (rawStep hk ring C selected) <
    supportCount hk ring C at hnodrop
  change supportCount hk ring (rawStep hk ring C selected) ≤
    supportCount hk ring C at hle
  omega

/-- Exact collision classification, including cancellation and nonzero
mergers. -/
theorem drops_iff_ready_and_occupied {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) :
    Drops hk ring C selected ↔
      AdvanceReady hk ring C selected ∧
        BarrierAt hk ring (labelsOf C) (ring.rightNeighbor selected) := by
  exact protocol_barrierCount_lt_iff_ready_and_successor_barrier
    hk ring hn2 C selected

/-- An outside ready barrier entering either tagged charged edge is a support
drop.  The trial must terminate before touching either lineage tag. -/
theorem outside_move_into_tag_drops {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected tag : Fin n) (hready : AdvanceReady hk ring C selected)
    (htag : BarrierAt hk ring (labelsOf C) tag)
    (hhead : ring.rightNeighbor selected = tag) :
    Drops hk ring C selected := by
  rw [drops_iff_ready_and_occupied hk ring hn2 C selected]
  exact ⟨hready, by simpa [hhead] using htag⟩

/-- A merger always drops support, whether the summed residue cancels or
remains nonzero.  The second conjunct records which of those two outcomes
occupies the successor after the terminating step. -/
theorem merger_drops_and_successor_charge_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (hready : AdvanceReady hk ring C selected)
    (hoccupied : BarrierAt hk ring (labelsOf C)
      (ring.rightNeighbor selected)) :
    Drops hk ring C selected ∧
      (BarrierAt hk ring
          (labelsOf (rawStep hk ring C selected))
          (ring.rightNeighbor selected) ↔
        defect hk ring (labelsOf C) selected +
            defect hk ring (labelsOf C) (ring.rightNeighbor selected) ≠
          zeroResidue hk) := by
  constructor
  · exact (drops_iff_ready_and_occupied hk ring hn2 C selected).2
      ⟨hready, hoccupied⟩
  · have hcases := protocol_ready_barrierAt_cases hk ring hn2 C selected hready
    exact hcases.2.1

/-- No-drop transport preserves the charged status of a tagged edge.  If the
tagged barrier itself advances, the tag moves to the successor; otherwise the
old physical edge remains charged. -/
theorem transportTag_charged_of_no_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected tag : Fin n)
    (htag : BarrierAt hk ring (labelsOf C) tag)
    (hnodrop : ¬ Drops hk ring C selected) :
    BarrierAt hk ring (labelsOf (rawStep hk ring C selected))
      (transportTag hk ring C selected tag) := by
  by_cases hready : AdvanceReady hk ring C selected
  · have hfree : ¬ BarrierAt hk ring (labelsOf C)
        (ring.rightNeighbor selected) := by
      intro hoccupied
      exact hnodrop ((drops_iff_ready_and_occupied hk ring hn2 C selected).2
        ⟨hready, hoccupied⟩)
    by_cases hsel : selected = tag
    · subst tag
      have hphase : (C selected).phase = true := hready.2
      simp only [transportTag, hphase, if_true]
      have htransport := protocol_ready_transport_into_free_successor
        hk ring hn2 C selected hready hfree
      exact htransport.2.1
    · have htagHead : tag ≠ ring.rightNeighbor selected := by
        intro heq
        apply hfree
        simpa [← heq] using htag
      simp only [transportTag, hsel, if_false]
      have hcases := protocol_ready_barrierAt_cases
        hk ring hn2 C selected hready
      exact (hcases.2.2 tag (Ne.symm hsel) htagHead).2 htag
  · by_cases hsel : selected = tag
    · subst tag
      have hbar : IsBarrier hk (C selected)
          (C (ring.rightNeighbor selected)) :=
        (barrierAt_labelsOf_iff hk ring C selected).1 htag
      have hphase : (C selected).phase = false := by
        cases hp : (C selected).phase
        · rfl
        · exact (hready ⟨hbar, hp⟩).elim
      simp only [transportTag, hphase, Bool.false_eq_true, if_false, if_true]
      have hlabels := labelsOf_step_eq_self_of_not_ready
        hk ring C selected hready
      unfold rawStep
      rw [hlabels]
      exact htag
    · simp only [transportTag, hsel, if_false]
      have hlabels := labelsOf_step_eq_self_of_not_ready
        hk ring C selected hready
      unfold rawStep
      rw [hlabels]
      exact htag

/-! ## Hostile local branch audit -/

/-- A phase-zero hit on a tagged barrier advances only its clock: the tag
stays on the same charged physical edge and support count is unchanged. -/
theorem tagged_phase_zero_hit {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k) (tag : Fin n)
    (htag : BarrierAt hk ring (labelsOf C) tag)
    (hphase : (C tag).phase = false) :
    ((rawStep hk ring C tag) tag).phase = true ∧
      transportTag hk ring C tag tag = tag ∧
      supportCount hk ring (rawStep hk ring C tag) =
        supportCount hk ring C := by
  have hbar : IsBarrier hk (C tag) (C (ring.rightNeighbor tag)) :=
    (barrierAt_labelsOf_iff hk ring C tag).1 htag
  have hnotready : ¬ AdvanceReady hk ring C tag := by
    intro hready
    exact Bool.noConfusion (hready.2.symm.trans hphase)
  have hpair : transition hk (C tag) (C (ring.rightNeighbor tag)) =
      ({ probeHitsBarrier (C tag) with phase := true },
        if (C (ring.rightNeighbor tag)).leader = false then
          { C (ring.rightNeighbor tag) with probe := true }
        else C (ring.rightNeighbor tag)) := by
    rw [transition_of_barrier hk _ _ hbar]
    exact barrierStep_phase_zero hk _ _ hphase
  have hcount := protocol_barrierCount_eq_of_no_collision hk ring hn2 C tag
    (by exact fun hcollision => hnotready hcollision.1)
  constructor
  · simp [rawStep, PopulationProtocol.step, protocol, hpair]
  constructor
  · simp [transportTag, hphase]
  · exact hcount

/-- A no-drop phase-one hit moves the tag to the successor, resets that new
tail clock to phase zero, and preserves its charged status. -/
theorem tagged_phase_one_hit_no_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k) (tag : Fin n)
    (htag : BarrierAt hk ring (labelsOf C) tag)
    (hphase : (C tag).phase = true)
    (hnodrop : ¬ Drops hk ring C tag) :
    transportTag hk ring C tag tag = ring.rightNeighbor tag ∧
      ((rawStep hk ring C tag) (ring.rightNeighbor tag)).phase = false ∧
      BarrierAt hk ring (labelsOf (rawStep hk ring C tag))
        (ring.rightNeighbor tag) ∧
      supportCount hk ring (rawStep hk ring C tag) =
        supportCount hk ring C := by
  have hbar : IsBarrier hk (C tag) (C (ring.rightNeighbor tag)) :=
    (barrierAt_labelsOf_iff hk ring C tag).1 htag
  have hready : AdvanceReady hk ring C tag := ⟨hbar, hphase⟩
  have hre : ring.rightNeighbor tag ≠ tag :=
    BarrierAlgebra.rightNeighbor_ne_self ring hn2 tag
  have hpair : transition hk (C tag) (C (ring.rightNeighbor tag)) =
      (probeHitsBarrier (C tag),
        { C (ring.rightNeighbor tag) with
          label := succLabel hk (C tag).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [transition_of_barrier hk _ _ hbar]
    exact barrierStep_phase_one hk _ _ hphase
  have htransport : transportTag hk ring C tag tag =
      ring.rightNeighbor tag := by simp [transportTag, hphase]
  refine ⟨htransport, ?_, ?_, supportCount_eq_of_not_drops
    hk ring hn2 C tag hnodrop⟩
  · simp [rawStep, PopulationProtocol.step, protocol, hpair, hre]
  · rw [← htransport]
    exact transportTag_charged_of_no_drop hk ring hn2 C tag tag htag hnodrop

/-- A site outside both endpoints of the selected physical edge is unchanged,
including its phase and every control bit. -/
theorem rawStep_at_of_ne_endpoints {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k) (selected site : Fin n)
    (hsource : site ≠ selected)
    (hhead : site ≠ ring.rightNeighbor selected) :
    rawStep hk ring C selected site = C site := by
  simp [rawStep, PopulationProtocol.step, hsource, hhead]

theorem unrelated_tag_phase_unchanged {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k) (selected tag : Fin n)
    (hsource : tag ≠ selected)
    (hhead : tag ≠ ring.rightNeighbor selected) :
    ((rawStep hk ring C selected) tag).phase = (C tag).phase := by
  rw [rawStep_at_of_ne_endpoints hk ring C selected tag hsource hhead]

theorem transition_snd_phase_of_not_ready {k : Nat} (hk : 0 < k)
    (u v : State k) (hnot : ¬ PairAdvanceReady hk u v) :
    (transition hk u v).2.phase = v.phase := by
  by_cases hbar : IsBarrier hk u v
  · cases hphase : u.phase with
    | false =>
        rw [transition_of_barrier hk u v hbar]
        rw [barrierStep_phase_zero hk u v hphase]
        split <;> rfl
    | true => exact (hnot ⟨hbar, hphase⟩).elim
  · rw [transition_of_nonbarrier hk u v hbar]
    cases hv : v.leader <;>
      cases hb : v.bullet <;>
      cases hp : u.probe <;>
      simp [nonBarrierStep, hv, hb, hp]

/-- A charged site different from the selected edge keeps its phase on every
no-drop step, including the responder case. -/
theorem charged_tag_phase_unchanged_of_no_drop {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Config n k) (selected tag : Fin n)
    (htag : BarrierAt hk ring (labelsOf C) tag)
    (hne : selected ≠ tag) (hnodrop : ¬ Drops hk ring C selected) :
    ((rawStep hk ring C selected) tag).phase = (C tag).phase := by
  by_cases hhead : tag = ring.rightNeighbor selected
  · subst tag
    have hnotready : ¬ AdvanceReady hk ring C selected := by
      intro hready
      apply hnodrop
      exact outside_move_into_tag_drops hk ring hn2 C selected
        (ring.rightNeighbor selected) hready htag rfl
    have hphase := transition_snd_phase_of_not_ready hk
      (C selected) (C (ring.rightNeighbor selected)) hnotready
    have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 selected
    simpa [rawStep, PopulationProtocol.step, protocol, hre] using hphase
  · exact unrelated_tag_phase_unchanged hk ring C selected tag
      (Ne.symm hne) hhead

/-- A different charged tag keeps its clock during a no-drop hit on a charged
selected edge.  If it is the responder of a phase-one hit, that hit would be
an occupied-head collision and hence would already have terminated. -/
theorem other_charged_tag_phase_unchanged_of_no_drop {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Config n k) (selected tag : Fin n)
    (hselected : BarrierAt hk ring (labelsOf C) selected)
    (htag : BarrierAt hk ring (labelsOf C) tag)
    (hne : selected ≠ tag) (hnodrop : ¬ Drops hk ring C selected) :
    ((rawStep hk ring C selected) tag).phase = (C tag).phase := by
  cases hphase : (C selected).phase with
  | false =>
      by_cases hhead : tag = ring.rightNeighbor selected
      · subst tag
        have hbar : IsBarrier hk (C selected)
            (C (ring.rightNeighbor selected)) :=
          (barrierAt_labelsOf_iff hk ring C selected).1 hselected
        have hpair : transition hk (C selected)
            (C (ring.rightNeighbor selected)) =
            ({ probeHitsBarrier (C selected) with phase := true },
              if (C (ring.rightNeighbor selected)).leader = false then
                { C (ring.rightNeighbor selected) with probe := true }
              else C (ring.rightNeighbor selected)) := by
          rw [transition_of_barrier hk _ _ hbar]
          exact barrierStep_phase_zero hk _ _ hphase
        have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 selected
        simp [rawStep, PopulationProtocol.step, protocol, hpair, hre]
        split <;> rfl
      · exact unrelated_tag_phase_unchanged hk ring C selected tag
          (Ne.symm hne) hhead
  | true =>
      have hbar : IsBarrier hk (C selected)
          (C (ring.rightNeighbor selected)) :=
        (barrierAt_labelsOf_iff hk ring C selected).1 hselected
      have hready : AdvanceReady hk ring C selected := ⟨hbar, hphase⟩
      have hhead : tag ≠ ring.rightNeighbor selected := by
        intro heq
        apply hnodrop
        exact outside_move_into_tag_drops hk ring hn2 C selected tag hready
          htag heq.symm
      exact unrelated_tag_phase_unchanged hk ring C selected tag
        (Ne.symm hne) hhead

/-- Under no drop, transported distinct charged tags stay distinct.  The only
way one transported tag could land on the other is precisely an occupied-head
collision, which was already classified as terminal. -/
theorem transported_tags_ne_of_no_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hnodrop : ¬ Drops hk ring C selected) :
    transportTag hk ring C selected tags.rear ≠
      transportTag hk ring C selected tags.front := by
  intro heq
  unfold transportTag at heq
  by_cases hsr : selected = tags.rear
  · subst selected
    by_cases hpr : (C tags.rear).phase = true
    · have hready : AdvanceReady hk ring C tags.rear :=
        ⟨(barrierAt_labelsOf_iff hk ring C tags.rear).1 hrear, hpr⟩
      have hsf : tags.rear ≠ tags.front := tags.ne
      simp only [hpr, if_true, hsf, if_false] at heq
      exact hnodrop (outside_move_into_tag_drops hk ring hn2 C
        tags.rear tags.front hready hfront heq)
    · simp only [hpr] at heq
      by_cases hsame : tags.rear = tags.front
      · exact tags.ne hsame
      · simp [hsame] at heq
  · by_cases hsf : selected = tags.front
    · subst selected
      by_cases hpf : (C tags.front).phase = true
      · have hready : AdvanceReady hk ring C tags.front :=
          ⟨(barrierAt_labelsOf_iff hk ring C tags.front).1 hfront, hpf⟩
        have hfr : tags.front ≠ tags.rear := Ne.symm tags.ne
        simp only [hsr, if_false, hpf, if_true] at heq
        exact hnodrop (outside_move_into_tag_drops hk ring hn2 C
          tags.front tags.rear hready hrear heq.symm)
      · simp only [hsr, if_false, hpf] at heq
        exact tags.ne heq
    · simp only [hsr, hsf, if_false] at heq
      exact tags.ne heq

/-- Construct transported tags only after receiving the no-drop certificate. -/
def transportTagsAfterNoDrop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hnodrop : ¬ Drops hk ring C selected) : Tags n where
  rear := transportTag hk ring C selected tags.rear
  front := transportTag hk ring C selected tags.front
  ne := transported_tags_ne_of_no_drop hk ring hn2 C selected tags
    hrear hfront hnodrop

/-! ## Drop-first tagged transition -/

/-- A trial step either terminates on a support drop or returns transported
tags.  There is no tag payload on the drop branch. -/
inductive TagStep (n : Nat) where
  | success
  | continued (tags : Tags n)

/-- Support count is inspected before `transportTagsAfterNoDrop` is called.
This definition is the lineage firewall for both cancellation and nonzero
merger branches. -/
def tagStep {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Config n k) (selected : Fin n) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front) : TagStep n :=
  if hdrop : Drops hk ring C selected then
    .success
  else
    .continued (transportTagsAfterNoDrop hk ring hn2 C selected tags
      hrear hfront hdrop)

theorem tagStep_eq_success_of_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hdrop : Drops hk ring C selected) :
    tagStep hk ring hn2 C selected tags hrear hfront = .success := by
  simp [tagStep, hdrop]

theorem tagStep_eq_continued_of_no_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hnodrop : ¬ Drops hk ring C selected) :
    tagStep hk ring hn2 C selected tags hrear hfront =
      .continued (transportTagsAfterNoDrop hk ring hn2 C selected tags
        hrear hfront hnodrop) := by
  simp [tagStep, hnodrop]

/-- Both returned tags are charged in the post-step configuration. -/
theorem continued_tags_charged {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Config n k)
    (selected : Fin n) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hnodrop : ¬ Drops hk ring C selected) :
    let next := transportTagsAfterNoDrop hk ring hn2 C selected tags
      hrear hfront hnodrop
    BarrierAt hk ring (labelsOf (rawStep hk ring C selected)) next.rear ∧
      BarrierAt hk ring (labelsOf (rawStep hk ring C selected)) next.front := by
  dsimp only
  exact ⟨transportTag_charged_of_no_drop hk ring hn2 C selected tags.rear
      hrear hnodrop,
    transportTag_charged_of_no_drop hk ring hn2 C selected tags.front
      hfront hnodrop⟩

/-! ## Adjacent tags selected from a support cycle -/

/-- The cyclic successor of a support index. -/
def cycleSucc {m : Nat} (hm : 0 < m) (j : Fin m) : Fin m :=
  ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩

theorem cycleSucc_ne {m : Nat} (hm2 : 2 ≤ m) (j : Fin m) :
    cycleSucc (by omega) j ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  unfold cycleSucc at hv
  dsimp only at hv
  by_cases hlt : j.val + 1 < m
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : j.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- The indexed support enumeration is injective; this is the function-level
form of the cycle's strict physical order. -/
theorem cycle_edge_injective {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (cycle : CoalescenceCycle.BarrierCycle hk ring C m) :
    Function.Injective cycle.edge := by
  intro i j hij
  apply Fin.ext
  apply Classical.byContradiction
  intro hval
  have hi : i.val < cycle.support.length := by
    have hi0 := i.isLt
    have hlen := cycle.length_eq
    omega
  have hj : j.val < cycle.support.length := by
    have hj0 := j.isLt
    have hlen := cycle.length_eq
    omega
  have hedgeVal := congrArg Fin.val hij
  unfold CoalescenceCycle.BarrierCycle.edge at hedgeVal
  simp only [List.get_eq_getElem] at hedgeVal
  have hcases : i.val < j.val ∨ j.val < i.val := by omega
  rcases hcases with hijlt | hjilt
  · have horder := (List.pairwise_iff_getElem.mp cycle.ordered)
      i.val j.val hi hj hijlt
    omega
  · have horder := (List.pairwise_iff_getElem.mp cycle.ordered)
      j.val i.val hj hi hjilt
    omega

/-- Consecutive support indices give distinct charged rear/front tags. -/
def adjacentTags {n k m : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Config n k} (cycle : CoalescenceCycle.BarrierCycle hk ring C m)
    (hm2 : 2 ≤ m) (j : Fin m) : Tags n where
  rear := cycle.edge j
  front := cycle.edge (cycleSucc (by omega) j)
  ne := by
    apply (cycle_edge_injective cycle).ne
    exact Ne.symm (cycleSucc_ne hm2 j)

theorem adjacentTags_charged {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (cycle : CoalescenceCycle.BarrierCycle hk ring C m)
    (hm2 : 2 ≤ m) (j : Fin m) :
    BarrierAt hk ring (labelsOf C) (adjacentTags cycle hm2 j).rear ∧
      BarrierAt hk ring (labelsOf C) (adjacentTags cycle hm2 j).front := by
  exact ⟨cycle.edge_charged j,
    cycle.edge_charged (cycleSucc (by omega) j)⟩

theorem correctedForward_getElem_eq {n k : Nat} (C : Config n k)
    (first : Fin n) (rest : List (Fin n)) (i : Nat)
    (hi : i < rest.length) :
    (CoalescenceCycle.correctedForward C first rest)[i]'(by
        simpa using hi) =
      2 * (((first :: rest)[i + 1]'(by simp; omega)).val -
          ((first :: rest)[i]'(by simp; omega)).val) +
        CoalescenceCycle.phaseBit C
          ((first :: rest)[i + 1]'(by simp; omega)) -
        CoalescenceCycle.phaseBit C
          ((first :: rest)[i]'(by simp; omega)) := by
  induction rest generalizing first i with
  | nil => simp at hi
  | cons edge rest ih =>
      cases i with
      | zero => simp [CoalescenceCycle.correctedForward]
      | succ i =>
          simp only [CoalescenceCycle.correctedForward,
            List.getElem_cons_succ]
          simpa [Nat.add_assoc] using ih edge i (by simpa using hi)

theorem getElem_last_eq_endEdge {n : Nat} (first : Fin n)
    (rest : List (Fin n)) :
    (first :: rest)[rest.length]'(by simp) =
      CoalescenceCycle.endEdge first rest := by
  induction rest generalizing first with
  | nil => simp [CoalescenceCycle.endEdge]
  | cons edge rest ih =>
      simpa [CoalescenceCycle.endEdge] using ih edge

theorem first_val_le_endEdge {n : Nat} (first : Fin n)
    (rest : List (Fin n))
    (horder : (first :: rest).Pairwise (fun a b => a.val < b.val)) :
    first.val ≤ (CoalescenceCycle.endEdge first rest).val := by
  induction rest generalizing first with
  | nil => simp [CoalescenceCycle.endEdge]
  | cons edge rest ih =>
      rw [List.pairwise_cons] at horder
      have hfirst : first.val < edge.val := horder.1 edge (by simp)
      have htail : (edge :: rest).Pairwise (fun a b => a.val < b.val) :=
        horder.2
      simp only [CoalescenceCycle.endEdge]
      exact Nat.le_trans (Nat.le_of_lt hfirst) (ih edge htail)

/-! ## Physical coordinate seam and killed-walk assembly -/

/-- Canonical clockwise distance from rear to front. -/
def clockwiseDistance {n : Nat} (_ring : DirectedRing n)
    (rear front : Fin n) : Nat :=
  (front.val + n - rear.val) % n

/-- Physical phase-corrected doubled distance of two live tags. -/
def correctedTagGap {n k : Nat} (ring : DirectedRing n)
    (C : Config n k) (tags : Tags n) : Nat :=
  2 * clockwiseDistance ring tags.rear tags.front +
    CoalescenceCycle.phaseBit C tags.front -
    CoalescenceCycle.phaseBit C tags.rear

theorem clockwiseDistance_eq_forward {n : Nat} (ring : DirectedRing n)
    (rear front : Fin n) (hle : rear.val ≤ front.val) :
    clockwiseDistance ring rear front = front.val - rear.val := by
  unfold clockwiseDistance
  have hsum : front.val + n - rear.val = n + (front.val - rear.val) := by
    omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add]
  have hlt : front.val - rear.val < n := by
    have hf := front.isLt
    omega
  simp [Nat.mod_eq_of_lt hlt]

theorem clockwiseDistance_eq_wrap {n : Nat} (ring : DirectedRing n)
    (rear front : Fin n) (hlt : front.val < rear.val) :
    clockwiseDistance ring rear front = front.val + n - rear.val := by
  unfold clockwiseDistance
  exact Nat.mod_eq_of_lt (by omega)

theorem clockwiseDistance_pos_of_ne {n : Nat} (ring : DirectedRing n)
    (rear front : Fin n) (hne : rear ≠ front) :
    0 < clockwiseDistance ring rear front := by
  by_cases hle : rear.val ≤ front.val
  · rw [clockwiseDistance_eq_forward ring rear front hle]
    have hv : rear.val ≠ front.val := by
      intro h
      apply hne
      exact Fin.ext h
    omega
  · rw [clockwiseDistance_eq_wrap ring rear front (by omega)]
    omega

theorem correctedTagGap_pos {n k : Nat} (ring : DirectedRing n)
    (C : Config n k) (tags : Tags n) :
    0 < correctedTagGap ring C tags := by
  have hd := clockwiseDistance_pos_of_ne ring tags.rear tags.front tags.ne
  have hrear := CoalescenceCycle.phaseBit_le_one C tags.rear
  unfold correctedTagGap
  omega

theorem clockwiseDistance_move_rear {n : Nat} (ring : DirectedRing n)
    (rear front : Fin n) (htags : rear ≠ front)
    (hne : ring.rightNeighbor rear ≠ front) :
    clockwiseDistance ring (ring.rightNeighbor rear) front =
      clockwiseDistance ring rear front - 1 := by
  have htagsVal : rear.val ≠ front.val := by
    intro heq
    exact htags (Fin.ext heq)
  by_cases hr : rear.val + 1 < n
  · have hrn : ring.rightNeighbor rear = ⟨rear.val + 1, hr⟩ := by
      apply Fin.ext
      simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hr]
    rw [hrn] at hne ⊢
    by_cases hle : rear.val ≤ front.val
    · have hnextLe : rear.val + 1 ≤ front.val := by
        have hnextNe : rear.val + 1 ≠ front.val := by
          intro heq
          apply hne
          exact Fin.ext heq
        omega
      rw [clockwiseDistance_eq_forward ring rear front hle]
      rw [clockwiseDistance_eq_forward ring ⟨rear.val + 1, hr⟩ front
        (by change rear.val + 1 ≤ front.val; exact hnextLe)]
      change front.val - (rear.val + 1) = front.val - rear.val - 1
      omega
    · rw [clockwiseDistance_eq_wrap ring rear front (by omega)]
      rw [clockwiseDistance_eq_wrap ring ⟨rear.val + 1, hr⟩ front
        (by change front.val < rear.val + 1; omega)]
      change front.val + n - (rear.val + 1) =
        (front.val + n - rear.val) - 1
      omega
  · have hre : rear.val + 1 = n := by omega
    have hrn : ring.rightNeighbor rear = ⟨0, ring.hn⟩ := by
      apply Fin.ext
      simp [DirectedRing.rightNeighbor, hre]
    rw [hrn] at hne ⊢
    have hfrontPos : 0 < front.val := by
      have hfrontNe : front.val ≠ 0 := by
        intro hz
        apply hne
        apply Fin.ext
        simpa using hz.symm
      omega
    rw [clockwiseDistance_eq_wrap ring rear front (by omega)]
    rw [clockwiseDistance_eq_forward ring ⟨0, ring.hn⟩ front
      (by change 0 ≤ front.val; omega)]
    change front.val = (front.val + n - rear.val) - 1
    omega

theorem clockwiseDistance_move_front {n : Nat} (ring : DirectedRing n)
    (rear front : Fin n) (htags : rear ≠ front)
    (hne : ring.rightNeighbor front ≠ rear) :
    clockwiseDistance ring rear (ring.rightNeighbor front) =
      clockwiseDistance ring rear front + 1 := by
  have htagsVal : rear.val ≠ front.val := by
    intro heq
    exact htags (Fin.ext heq)
  by_cases hf : front.val + 1 < n
  · have hfn : ring.rightNeighbor front = ⟨front.val + 1, hf⟩ := by
      apply Fin.ext
      simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hf]
    rw [hfn] at hne ⊢
    by_cases hle : rear.val ≤ front.val
    · rw [clockwiseDistance_eq_forward ring rear front hle]
      rw [clockwiseDistance_eq_forward ring rear ⟨front.val + 1, hf⟩
        (by change rear.val ≤ front.val + 1; omega)]
      change front.val + 1 - rear.val = front.val - rear.val + 1
      omega
    · have hstrict : front.val + 1 < rear.val := by
        have hnotEq : front.val + 1 ≠ rear.val := by
          intro heq
          apply hne
          exact Fin.ext heq
        omega
      rw [clockwiseDistance_eq_wrap ring rear front (by omega)]
      rw [clockwiseDistance_eq_wrap ring rear ⟨front.val + 1, hf⟩
        (by change front.val + 1 < rear.val; exact hstrict)]
      change front.val + 1 + n - rear.val =
        (front.val + n - rear.val) + 1
      omega
  · have hfe : front.val + 1 = n := by omega
    have hfn : ring.rightNeighbor front = ⟨0, ring.hn⟩ := by
      apply Fin.ext
      simp [DirectedRing.rightNeighbor, hfe]
    rw [hfn] at hne ⊢
    have hrpos : 0 < rear.val := by
      have hrne : rear.val ≠ 0 := by
        intro hz
        apply hne
        apply Fin.ext
        simpa using hz.symm
      omega
    rw [clockwiseDistance_eq_forward ring rear front (by omega)]
    rw [clockwiseDistance_eq_wrap ring rear ⟨0, ring.hn⟩ hrpos]
    simp only [Nat.zero_add]
    change n - rear.val = front.val - rear.val + 1
    omega

/-- A physical edge lies strictly inside the clockwise rear-to-front arc. -/
def StrictlyBetween {n : Nat} (ring : DirectedRing n)
    (rear front edge : Fin n) : Prop :=
  0 < clockwiseDistance ring rear edge ∧
    clockwiseDistance ring rear edge < clockwiseDistance ring rear front

/-- Current charged tags are adjacent when no third charged edge lies in their
open clockwise arc. -/
def SupportAdjacent {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) (tags : Tags n) : Prop :=
  BarrierAt hk ring (labelsOf C) tags.rear ∧
    BarrierAt hk ring (labelsOf C) tags.front ∧
    ∀ edge, StrictlyBetween ring tags.rear tags.front edge →
      ¬ BarrierAt hk ring (labelsOf C) edge

/-- Active physical trial states.  Both tags are current charged edges and the
support count is the fixed trial level `m`. -/
structure Active {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (m L : Nat) where
  config : Config n k
  tags : Tags n
  rear_charged : BarrierAt hk ring (labelsOf config) tags.rear
  front_charged : BarrierAt hk ring (labelsOf config) tags.front
  count_eq : supportCount hk ring config = m
  coord_pos : 1 ≤ correctedTagGap ring config tags
  coord_lt : correctedTagGap ring config tags < L

/-- Exact snapshot bridge between the list-defined doubled gap and the two
adjacent physical tags extracted at the same support index. -/
def CycleGapAligned {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (cycle : CoalescenceCycle.BarrierCycle hk ring C m)
    (hm2 : 2 ≤ m) (j : Fin m) : Prop :=
  correctedTagGap ring C (adjacentTags cycle hm2 j) = cycle.doubledGap j

theorem cycleGapAligned {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (cycle : CoalescenceCycle.BarrierCycle hk ring C m)
    (hm2 : 2 ≤ m) (j : Fin m) : CycleGapAligned cycle hm2 j := by
  cases hs : cycle.support with
  | nil => exact (cycle.nonempty hs).elim
  | cons first rest =>
      have hlen : (first :: rest).length = m := by
        simpa [hs] using cycle.length_eq
      have horder : (first :: rest).Pairwise
          (fun a b => a.val < b.val) := by
        simpa [hs] using cycle.ordered
      by_cases hj : j.val < rest.length
      · have hnextLt : j.val + 1 < m := by
          simp only [List.length_cons] at hlen
          omega
        have hsuccVal : (cycleSucc (by omega) j).val = j.val + 1 := by
          simp [cycleSucc, Nat.mod_eq_of_lt hnextLt]
        have hrear : cycle.edge j =
            (first :: rest)[j.val]'(by rw [hlen]; exact j.isLt) := by
          unfold CoalescenceCycle.BarrierCycle.edge
          rw [List.get_eq_getElem]
          simp only [hs]
        have hfront : cycle.edge (cycleSucc (by omega) j) =
            (first :: rest)[j.val + 1]'(by rw [hlen]; exact hnextLt) := by
          unfold CoalescenceCycle.BarrierCycle.edge
          rw [List.get_eq_getElem]
          simp only [hs, hsuccVal]
        have hedgeOrder := (List.pairwise_iff_getElem.mp horder)
          j.val (j.val + 1) (by rw [hlen]; exact j.isLt)
          (by rw [hlen]; exact hnextLt) (by omega)
        have hforward := correctedForward_getElem_eq C first rest j.val hj
        have hgap : cycle.doubledGap j =
            (CoalescenceCycle.correctedForward C first rest)[j.val]'(by
              simpa using hj) := by
          simp [CoalescenceCycle.BarrierCycle.doubledGap,
            CoalescenceCycle.BarrierCycle.doubledGaps, hs,
            CoalescenceCycle.correctedCyclicGaps, List.get_eq_getElem,
            List.getElem_append_left, hj]
        unfold CycleGapAligned correctedTagGap adjacentTags
        change 2 * clockwiseDistance ring (cycle.edge j)
              (cycle.edge (cycleSucc (by omega) j)) +
              CoalescenceCycle.phaseBit C
                (cycle.edge (cycleSucc (by omega) j)) -
              CoalescenceCycle.phaseBit C (cycle.edge j) =
            cycle.doubledGap j
        rw [hrear, hfront]
        rw [clockwiseDistance_eq_forward ring _ _ (Nat.le_of_lt hedgeOrder)]
        rw [hgap, hforward]
      · have hjlast : j.val = rest.length := by
          have hjlt := j.isLt
          simp only [List.length_cons] at hlen
          omega
        have hsuccVal : (cycleSucc (by omega) j).val = 0 := by
          unfold cycleSucc
          dsimp only
          rw [hjlast]
          have hm : m = rest.length + 1 := by
            simpa using hlen.symm
          rw [hm, Nat.mod_self]
        have hrear : cycle.edge j = CoalescenceCycle.endEdge first rest := by
          simpa [CoalescenceCycle.BarrierCycle.edge, List.get_eq_getElem,
            hs, hjlast] using getElem_last_eq_endEdge first rest
        have hfront : cycle.edge (cycleSucc (by omega) j) = first := by
          simp [CoalescenceCycle.BarrierCycle.edge, List.get_eq_getElem,
            hs, hsuccVal]
        have hendLt : (CoalescenceCycle.endEdge first rest).val < n :=
          (CoalescenceCycle.endEdge first rest).isLt
        have hfirstLeEnd : first.val ≤
            (CoalescenceCycle.endEdge first rest).val :=
          first_val_le_endEdge first rest horder
        have hgap : cycle.doubledGap j =
            2 * (n - (CoalescenceCycle.endEdge first rest).val + first.val) +
              CoalescenceCycle.phaseBit C first -
              CoalescenceCycle.phaseBit C
                (CoalescenceCycle.endEdge first rest) := by
          simp [CoalescenceCycle.BarrierCycle.doubledGap,
            CoalescenceCycle.BarrierCycle.doubledGaps, hs,
            CoalescenceCycle.correctedCyclicGaps, List.get_eq_getElem,
            List.getElem_append_right, hjlast,
            CoalescenceCycle.correctedForward_length]
        unfold CycleGapAligned correctedTagGap adjacentTags
        change 2 * clockwiseDistance ring (cycle.edge j)
              (cycle.edge (cycleSucc (by omega) j)) +
              CoalescenceCycle.phaseBit C
                (cycle.edge (cycleSucc (by omega) j)) -
              CoalescenceCycle.phaseBit C (cycle.edge j) =
            cycle.doubledGap j
        rw [hrear, hfront]
        rw [clockwiseDistance_eq_wrap ring _ _ (by
          have hne := (adjacentTags cycle hm2 j).ne
          change cycle.edge j ≠ cycle.edge (cycleSucc (by omega) j) at hne
          rw [hrear, hfront] at hne
          have hneVal : (CoalescenceCycle.endEdge first rest).val ≠
              first.val := by
            intro heq
            exact hne (Fin.ext heq)
          omega)]
        rw [hgap]
        omega

/-- Every support-cycle gap seeds the active killed walk at `q₀` with upper
boundary `2q₀`; alignment is now internal. -/
def activeOfCycle {n k m : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (cycle : CoalescenceCycle.BarrierCycle hk ring C m)
    (hm2 : 2 ≤ m) (j : Fin m) :
    Active hk ring m (2 * cycle.doubledGap j) where
  config := C
  tags := adjacentTags cycle hm2 j
  rear_charged := (adjacentTags_charged cycle hm2 j).1
  front_charged := (adjacentTags_charged cycle hm2 j).2
  count_eq := by
    unfold supportCount barrierCount
    rw [← cycle.support_eq, cycle.length_eq]
  coord_pos := by
    rw [cycleGapAligned cycle hm2 j]
    exact cycle.doubledGap_pos j
  coord_lt := by
    rw [cycleGapAligned cycle hm2 j]
    have hpos := cycle.doubledGap_pos j
    omega

/-- Seed one cycle gap below a common fixed-level upper half-width `Q`.
Unlike `activeOfCycle`, the killed upper endpoint is `2Q`, independent of the
currently selected minimum gap. -/
def activeOfCycleAtUpper {n k m Q : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (cycle : CoalescenceCycle.BarrierCycle hk ring C m)
    (hm2 : 2 ≤ m) (j : Fin m) (hgap : cycle.doubledGap j ≤ Q) :
    Active hk ring m (2 * Q) where
  config := C
  tags := adjacentTags cycle hm2 j
  rear_charged := (adjacentTags_charged cycle hm2 j).1
  front_charged := (adjacentTags_charged cycle hm2 j).2
  count_eq := by
    unfold supportCount barrierCount
    rw [← cycle.support_eq, cycle.length_eq]
  coord_pos := by
    rw [cycleGapAligned cycle hm2 j]
    exact cycle.doubledGap_pos j
  coord_lt := by
    rw [cycleGapAligned cycle hm2 j]
    have hpos := cycle.doubledGap_pos j
    omega

/-- Canonical support cycle plus a certified minimum-gap index for one fixed
support level. -/
structure FixedLevelSeed {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k) (Q : Nat) where
  cycle : CoalescenceCycle.BarrierCycle hk ring C m
  index : Fin m
  mul_le : m * cycle.doubledGap index ≤ 2 * n
  gap_le : cycle.doubledGap index ≤ Q

namespace FixedLevelSeed

def active {n k m Q : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Config n k} (seed : FixedLevelSeed (m := m) hk ring C Q)
    (hm2 : 2 ≤ m) : Active hk ring m (2 * Q) :=
  activeOfCycleAtUpper seed.cycle hm2 seed.index seed.gap_le

end FixedLevelSeed

/-- Deterministic choice of the canonical support cycle and one minimum gap at
the common half-width `Q=(2n)/m`. -/
noncomputable def fixedLevelSeed {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k)
    (hm2 : 2 ≤ m) (hcount : supportCount hk ring C = m) :
    FixedLevelSeed (m := m) hk ring C ((2 * n) / m) := by
  have hmpos : 0 < m := by omega
  have hbarCount : barrierCount hk ring (labelsOf C) = m := by
    simpa [supportCount] using hcount
  let cycle := Classical.choice
    (exists_barrierCycle hk ring C hbarCount hmpos)
  have hex := cycle.exists_min_doubledGap_mul_le
  let index := Classical.choose hex
  have hmul : m * cycle.doubledGap index ≤ 2 * n :=
    Classical.choose_spec hex
  have hgap : cycle.doubledGap index ≤ (2 * n) / m := by
    apply (Nat.le_div_iff_mul_le hmpos).2
    simpa [Nat.mul_comm] using hmul
  exact { cycle := cycle, index := index, mul_le := hmul, gap_le := hgap }

namespace Active

def coord {n k m L : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    Active hk ring m L → Nat :=
  fun state => correctedTagGap ring state.config state.tags

def downEdge {n k m L : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    Active hk ring m L → Fin n := fun state => state.tags.rear

def upEdge {n k m L : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    Active hk ring m L → Fin n := fun state => state.tags.front

end Active

/-- The local physical coordinate contract.  It is deliberately stated only
under no support drop: an untagged ready edge may collide with a tag (or two
untagged charges may cancel), and that branch is terminal success rather than
a framed active child. -/
structure CoordinateTransportLaw {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) : Prop where
  rear : ∀ (C : Config n k) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hnodrop : ¬ Drops hk ring C tags.rear),
    let next := transportTagsAfterNoDrop hk ring hn2 C tags.rear tags
      hrear hfront hnodrop
    correctedTagGap ring (rawStep hk ring C tags.rear) next =
      correctedTagGap ring C tags - 1
  front : ∀ (C : Config n k) (tags : Tags n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (hnodrop : ¬ Drops hk ring C tags.front),
    let next := transportTagsAfterNoDrop hk ring hn2 C tags.front tags
      hrear hfront hnodrop
    correctedTagGap ring (rawStep hk ring C tags.front) next =
      correctedTagGap ring C tags + 1
  frame : ∀ (C : Config n k) (tags : Tags n) (selected : Fin n)
    (hrear : BarrierAt hk ring (labelsOf C) tags.rear)
    (hfront : BarrierAt hk ring (labelsOf C) tags.front)
    (_hselRear : selected ≠ tags.rear) (_hselFront : selected ≠ tags.front)
    (hnodrop : ¬ Drops hk ring C selected),
    let next := transportTagsAfterNoDrop hk ring hn2 C selected tags
      hrear hfront hnodrop
    correctedTagGap ring (rawStep hk ring C selected) next =
      correctedTagGap ring C tags

/-- Literal centered-renewal dynamics satisfy the full coordinate transport
law; no abstract physical seam remains. -/
theorem coordinateTransportLaw {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) :
    CoordinateTransportLaw hk ring hn2 := by
  refine { rear := ?_, front := ?_, frame := ?_ }
  · intro C tags hrear hfront hnodrop
    dsimp only
    cases hphase : (C tags.rear).phase with
    | false =>
        have hhit := tagged_phase_zero_hit hk ring hn2 C tags.rear
          hrear hphase
        have hother := charged_tag_phase_unchanged_of_no_drop hk ring hn2 C
          tags.rear tags.front hfront tags.ne hnodrop
        have hdpos := clockwiseDistance_pos_of_ne ring tags.rear tags.front
          tags.ne
        simp only [transportTagsAfterNoDrop, transportTag,
          hphase, Bool.false_eq_true, if_false, if_neg tags.ne,
          if_true,
          correctedTagGap, CoalescenceCycle.phaseBit,
          CenteredRenewal.phaseNat]
        rw [hhit.1, hother]
        cases hfrontPhase : (C tags.front).phase <;> simp <;> omega
    | true =>
        have hhit := tagged_phase_one_hit_no_drop hk ring hn2 C tags.rear
          hrear hphase hnodrop
        have hother := charged_tag_phase_unchanged_of_no_drop hk ring hn2 C
          tags.rear tags.front hfront tags.ne hnodrop
        have hready : AdvanceReady hk ring C tags.rear :=
          ⟨(barrierAt_labelsOf_iff hk ring C tags.rear).1 hrear, hphase⟩
        have hnextNe : ring.rightNeighbor tags.rear ≠ tags.front := by
          intro heq
          apply hnodrop
          exact outside_move_into_tag_drops hk ring hn2 C tags.rear
            tags.front hready hfront heq
        have hdist := clockwiseDistance_move_rear ring tags.rear tags.front
          tags.ne hnextNe
        have hnewPos := clockwiseDistance_pos_of_ne ring
          (ring.rightNeighbor tags.rear) tags.front hnextNe
        simp only [transportTagsAfterNoDrop, transportTag,
          hphase, if_true, if_neg tags.ne, correctedTagGap,
          CoalescenceCycle.phaseBit, CenteredRenewal.phaseNat]
        rw [hhit.2.1, hother, hdist]
        cases hfrontPhase : (C tags.front).phase <;> simp <;> omega
  · intro C tags hrear hfront hnodrop
    dsimp only
    cases hphase : (C tags.front).phase with
    | false =>
        have hhit := tagged_phase_zero_hit hk ring hn2 C tags.front
          hfront hphase
        have hother := charged_tag_phase_unchanged_of_no_drop hk ring hn2 C
          tags.front tags.rear hrear (Ne.symm tags.ne) hnodrop
        have hdpos := clockwiseDistance_pos_of_ne ring tags.rear tags.front
          tags.ne
        simp only [transportTagsAfterNoDrop, transportTag,
          if_neg (Ne.symm tags.ne), hphase,
          Bool.false_eq_true, if_false, if_true,
          correctedTagGap, CoalescenceCycle.phaseBit,
          CenteredRenewal.phaseNat]
        rw [hhit.1, hother]
        cases hrearPhase : (C tags.rear).phase <;> simp <;> omega
    | true =>
        have hhit := tagged_phase_one_hit_no_drop hk ring hn2 C tags.front
          hfront hphase hnodrop
        have hother := charged_tag_phase_unchanged_of_no_drop hk ring hn2 C
          tags.front tags.rear hrear (Ne.symm tags.ne) hnodrop
        have hready : AdvanceReady hk ring C tags.front :=
          ⟨(barrierAt_labelsOf_iff hk ring C tags.front).1 hfront, hphase⟩
        have hnextNe : ring.rightNeighbor tags.front ≠ tags.rear := by
          intro heq
          apply hnodrop
          exact outside_move_into_tag_drops hk ring hn2 C tags.front
            tags.rear hready hrear heq
        have hdist := clockwiseDistance_move_front ring tags.rear tags.front
          tags.ne hnextNe
        have hrearBit := CoalescenceCycle.phaseBit_le_one C tags.rear
        simp only [transportTagsAfterNoDrop, transportTag,
          if_neg (Ne.symm tags.ne), hphase, if_true,
          correctedTagGap,
          CoalescenceCycle.phaseBit, CenteredRenewal.phaseNat]
        rw [hhit.2.1, hother, hdist]
        cases hrearPhase : (C tags.rear).phase <;> simp <;> omega
  · intro C tags selected hrear hfront hselRear hselFront hnodrop
    dsimp only
    have hrearPhase := charged_tag_phase_unchanged_of_no_drop hk ring hn2 C
      selected tags.rear hrear hselRear hnodrop
    have hfrontPhase := charged_tag_phase_unchanged_of_no_drop hk ring hn2 C
      selected tags.front hfront hselFront hnodrop
    simp only [transportTagsAfterNoDrop, transportTag, hselRear, hselFront,
      if_false, correctedTagGap, CoalescenceCycle.phaseBit]
    rw [hrearPhase, hfrontPhase]

/-- Separate adjacency seam: after the drop-first check, transporting two
adjacent charged tags must leave them adjacent.  A merger branch is excluded
because it has already returned success. -/
def AdjacencyPreservedOnNoDrop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) : Prop :=
  ∀ (C : Config n k) (tags : Tags n) (selected : Fin n)
    (hadj : SupportAdjacent hk ring C tags)
    (hnodrop : ¬ Drops hk ring C selected),
    SupportAdjacent hk ring (rawStep hk ring C selected)
      (transportTagsAfterNoDrop hk ring hn2 C selected tags
        hadj.1 hadj.2.1 hnodrop)

/-- Every no-drop child lies at or below the killed trial's upper endpoint.
Only the front-tag edge can increase the coordinate, and it does so by one. -/
theorem transported_coord_le_upper {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    let nextTags := transportTagsAfterNoDrop hk ring hn2 state.config selected
      state.tags state.rear_charged state.front_charged hnodrop
    correctedTagGap ring (rawStep hk ring state.config selected) nextTags ≤ L := by
  dsimp only
  by_cases hrear : selected = state.tags.rear
  · subst selected
    have hlaw := (coordinateTransportLaw hk ring hn2).rear state.config
      state.tags state.rear_charged state.front_charged hnodrop
    dsimp only at hlaw
    rw [hlaw]
    have hlt := state.coord_lt
    change correctedTagGap ring state.config state.tags < L at hlt
    omega
  · by_cases hfront : selected = state.tags.front
    · subst selected
      have hlaw := (coordinateTransportLaw hk ring hn2).front state.config
        state.tags state.rear_charged state.front_charged hnodrop
      dsimp only at hlaw
      rw [hlaw]
      have hlt := state.coord_lt
      change correctedTagGap ring state.config state.tags < L at hlt
      omega
    · have hlaw := (coordinateTransportLaw hk ring hn2).frame state.config
        state.tags selected state.rear_charged state.front_charged hrear hfront
        hnodrop
      dsimp only at hlaw
      rw [hlaw]
      exact Nat.le_of_lt state.coord_lt

/-- The bookkeeping zero endpoint is unreachable after a no-drop step:
transported tags remain distinct, so their phase-corrected cyclic gap is
strictly positive. -/
theorem transported_coord_pos {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    let nextTags := transportTagsAfterNoDrop hk ring hn2 state.config selected
      state.tags state.rear_charged state.front_charged hnodrop
    0 < correctedTagGap ring (rawStep hk ring state.config selected)
      nextTags := by
  dsimp only
  exact correctedTagGap_pos ring _ _

/-! ## Failure-preserving stopped node -/

/-- A killed-trial upper exit retaining its exact source interaction.  The
physical endpoint configuration and transported tags are definitions below,
so a restart consumer never has to reconstruct data from a nullary marker. -/
structure FailureEndpoint {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (m L : Nat) where
  source : Active hk ring m L
  selected : Fin n
  no_drop : ¬ Drops hk ring source.config selected
  coord_eq :
    let nextTags := transportTagsAfterNoDrop hk ring hn2 source.config selected
      source.tags source.rear_charged source.front_charged no_drop
    correctedTagGap ring (rawStep hk ring source.config selected) nextTags = L

namespace FailureEndpoint

def config {n k m L : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {hn2 : 1 < n} (endpoint : FailureEndpoint hk ring hn2 m L) :
    Config n k :=
  rawStep hk ring endpoint.source.config endpoint.selected

def tags {n k m L : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {hn2 : 1 < n} (endpoint : FailureEndpoint hk ring hn2 m L) : Tags n :=
  transportTagsAfterNoDrop hk ring hn2 endpoint.source.config
    endpoint.selected endpoint.source.tags endpoint.source.rear_charged
    endpoint.source.front_charged endpoint.no_drop

theorem count_eq {n k m L : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {hn2 : 1 < n} (endpoint : FailureEndpoint hk ring hn2 m L) :
    supportCount hk ring endpoint.config = m := by
  unfold config
  rw [supportCount_eq_of_not_drops hk ring hn2 endpoint.source.config
    endpoint.selected endpoint.no_drop]
  exact endpoint.source.count_eq

theorem tags_charged {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) :
    BarrierAt hk ring (labelsOf endpoint.config) endpoint.tags.rear ∧
      BarrierAt hk ring (labelsOf endpoint.config) endpoint.tags.front := by
  exact continued_tags_charged hk ring hn2 endpoint.source.config
    endpoint.selected endpoint.source.tags endpoint.source.rear_charged
    endpoint.source.front_charged endpoint.no_drop

theorem coordinate_eq {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) :
    correctedTagGap ring endpoint.config endpoint.tags = L := by
  exact endpoint.coord_eq

/-- Fresh fixed-level minimum-gap seed extracted from the actual physical
failure configuration. -/
noncomputable def reseed {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) (hm2 : 2 ≤ m) :
    FixedLevelSeed (m := m) hk ring endpoint.config ((2 * n) / m) :=
  fixedLevelSeed hk ring endpoint.config hm2 endpoint.count_eq

/-- The restarted active state uses the common upper endpoint
`2*((2n)/m)`, regardless of the newly chosen minimum gap. -/
noncomputable def restartedActive {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) (hm2 : 2 ≤ m) :
    Active hk ring m (2 * ((2 * n) / m)) :=
  (endpoint.reseed hm2).active hm2

theorem reseed_support_eq {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) (hm2 : 2 ≤ m) :
    (endpoint.reseed hm2).cycle.support =
      barrierSupport hk ring (labelsOf endpoint.config) :=
  (endpoint.reseed hm2).cycle.support_eq

theorem reseed_mul_le {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) (hm2 : 2 ≤ m) :
    m * (endpoint.reseed hm2).cycle.doubledGap
        (endpoint.reseed hm2).index ≤ 2 * n :=
  (endpoint.reseed hm2).mul_le

theorem reseed_gap_le_common_half {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : FailureEndpoint hk ring hn2 m L) (hm2 : 2 ≤ m) :
    (endpoint.reseed hm2).cycle.doubledGap
        (endpoint.reseed hm2).index ≤ (2 * n) / m :=
  (endpoint.reseed hm2).gap_le

end FailureEndpoint

/-- Protocol-side node retaining an upper failure endpoint. -/
inductive KilledTrialNode {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (m L : Nat) where
  | active : Active hk ring m L → KilledTrialNode hk ring hn2 m L
  | success : KilledTrialNode hk ring hn2 m L
  | failure : FailureEndpoint hk ring hn2 m L →
      KilledTrialNode hk ring hn2 m L

/-- Forget only the failure payload when entering the generic killed-walk
engine. -/
def KilledTrialNode.erase {n k m L : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n} :
    KilledTrialNode hk ring hn2 m L →
      FiniteUniformStoppingTree.StopNode (Active hk ring m L)
  | .active state => .active state
  | .success => .success
  | .failure _ => .failure

/-- Drop-first killed physical trial with a retained upper endpoint. -/
def killedStepWithFailure {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n)
    (hn2 : 1 < n) (state : Active hk ring m L) (selected : Fin n) :
    KilledTrialNode hk ring hn2 m L :=
  if hdrop : Drops hk ring state.config selected then
    .success
  else
    let nextTags := transportTagsAfterNoDrop hk ring hn2 state.config selected
      state.tags state.rear_charged state.front_charged hdrop
    let nextConfig := rawStep hk ring state.config selected
    let nextCoord := correctedTagGap ring nextConfig nextTags
    if hzero : nextCoord = 0 then
      .success
    else if hupper : L ≤ nextCoord then
      .failure {
        source := state
        selected := selected
        no_drop := hdrop
        coord_eq := by
          have hle := transported_coord_le_upper hk ring hn2 state selected
            hdrop
          dsimp only at hle
          change nextCoord ≤ L at hle
          exact Nat.le_antisymm hle hupper }
    else
      .active {
        config := nextConfig
        tags := nextTags
        rear_charged := (continued_tags_charged hk ring hn2 state.config
          selected state.tags state.rear_charged state.front_charged hdrop).1
        front_charged := (continued_tags_charged hk ring hn2 state.config
          selected state.tags state.rear_charged state.front_charged hdrop).2
        count_eq := by
          rw [supportCount_eq_of_not_drops hk ring hn2 state.config
            selected hdrop]
          exact state.count_eq
        coord_pos := by omega
        coord_lt := by omega }

/-- The enriched trial returns success exactly on a real charged-support
drop.  Its syntactic zero-coordinate branch is unreachable. -/
theorem killedStepWithFailure_eq_success_iff_drops
    {n k m L : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n) :
    killedStepWithFailure hk ring hn2 state selected = .success ↔
      Drops hk ring state.config selected := by
  constructor
  · intro hsuccess
    unfold killedStepWithFailure at hsuccess
    split at hsuccess
    · assumption
    · rename_i hnodrop
      have hpos := transported_coord_pos hk ring hn2 state selected hnodrop
      dsimp only at hpos
      dsimp only at hsuccess
      split at hsuccess
      · omega
      · split at hsuccess <;> contradiction
  · intro hdrop
    simp [killedStepWithFailure, hdrop]

/-- Generic killed-walk projection of `killedStepWithFailure`.  The stochastic
engine sees its original nullary failure marker, while protocol-side restart
lemmas retain the endpoint through the enriched step. -/
def killedStep {n k m L : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (state : Active hk ring m L) (selected : Fin n) :
    FiniteUniformStoppingTree.StopNode (Active hk ring m L) :=
  if hdrop : Drops hk ring state.config selected then
    .success
  else
    let nextTags := transportTagsAfterNoDrop hk ring hn2 state.config selected
      state.tags state.rear_charged state.front_charged hdrop
    let nextConfig := rawStep hk ring state.config selected
    let nextCoord := correctedTagGap ring nextConfig nextTags
    if hzero : nextCoord = 0 then
      .success
    else if hupper : L ≤ nextCoord then
      .failure
    else
      .active {
        config := nextConfig
        tags := nextTags
        rear_charged := (continued_tags_charged hk ring hn2 state.config
          selected state.tags state.rear_charged state.front_charged hdrop).1
        front_charged := (continued_tags_charged hk ring hn2 state.config
          selected state.tags state.rear_charged state.front_charged hdrop).2
        count_eq := by
          rw [supportCount_eq_of_not_drops hk ring hn2 state.config
            selected hdrop]
          exact state.count_eq
        coord_pos := by omega
        coord_lt := by omega }

theorem killedStepWithFailure_erase {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n) :
    (killedStepWithFailure hk ring hn2 state selected).erase =
      killedStep hk ring hn2 state selected := by
  by_cases hdrop : Drops hk ring state.config selected
  · simp [killedStepWithFailure, killedStep, KilledTrialNode.erase, hdrop]
  · by_cases hzero : correctedTagGap ring
        (rawStep hk ring state.config selected)
        (transportTagsAfterNoDrop hk ring hn2 state.config selected state.tags
          state.rear_charged state.front_charged hdrop) = 0
    · simp [killedStepWithFailure, killedStep, KilledTrialNode.erase, hdrop,
        hzero]
    · by_cases hupper : L ≤ correctedTagGap ring
          (rawStep hk ring state.config selected)
          (transportTagsAfterNoDrop hk ring hn2 state.config selected state.tags
            state.rear_charged state.front_charged hdrop)
      · simp [killedStepWithFailure, killedStep, KilledTrialNode.erase, hdrop,
          hzero, hupper]
      · simp [killedStepWithFailure, killedStep, KilledTrialNode.erase, hdrop,
          hzero, hupper]

/-- Exact protocol payload exposed by an upper failure.  In particular the
endpoint is the literal raw successor, the interaction was no-drop, its
canonical charged-support cardinality is still `m`, and its coordinate is
exactly the killed boundary `L`. -/
theorem killedStepWithFailure_failure_payload {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (endpoint : FailureEndpoint hk ring hn2 m L)
    (hfailure : killedStepWithFailure hk ring hn2 state selected =
      .failure endpoint) :
    endpoint.source = state ∧ endpoint.selected = selected ∧
      ¬ Drops hk ring state.config selected ∧
      endpoint.config = rawStep hk ring state.config selected ∧
      supportCount hk ring endpoint.config = m ∧
      correctedTagGap ring endpoint.config endpoint.tags = L := by
  unfold killedStepWithFailure at hfailure
  split at hfailure
  · contradiction
  · rename_i hnodrop
    dsimp only at hfailure
    split at hfailure
    · contradiction
    · split at hfailure
      · injection hfailure with heq
        subst endpoint
        refine ⟨rfl, rfl, hnodrop, rfl, ?_, ?_⟩
        · exact FailureEndpoint.count_eq _
        · exact FailureEndpoint.coordinate_eq _
      · contradiction

/-- A concrete killed-step failure is immediately and deterministically
reseeded at the same support level under the common endpoint
`2*((2n)/m)`. -/
theorem killedStepWithFailure_reseed {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (endpoint : FailureEndpoint hk ring hn2 m L) (hm2 : 2 ≤ m)
    (hfailure : killedStepWithFailure hk ring hn2 state selected =
      .failure endpoint) :
    let seed := endpoint.reseed hm2
    endpoint.config = rawStep hk ring state.config selected ∧
      supportCount hk ring endpoint.config = m ∧
      seed.cycle.support =
        barrierSupport hk ring (labelsOf endpoint.config) ∧
      m * seed.cycle.doubledGap seed.index ≤ 2 * n ∧
      seed.cycle.doubledGap seed.index ≤ (2 * n) / m ∧
      (seed.active hm2).config = endpoint.config := by
  dsimp only
  have hpayload := killedStepWithFailure_failure_payload hk ring hn2 state
    selected endpoint hfailure
  refine ⟨hpayload.2.2.2.1, hpayload.2.2.2.2.1, ?_, ?_, ?_, rfl⟩
  · exact FailureEndpoint.reseed_support_eq endpoint hm2
  · exact FailureEndpoint.reseed_mul_le endpoint hm2
  · exact FailureEndpoint.reseed_gap_le_common_half endpoint hm2

/-- Recover the unique physical failure payload from the generic nullary
failure marker used by the killed-walk engine. -/
theorem exists_failureEndpoint_of_killedStep_eq_failure
    {n k m L : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (hfailure : killedStep hk ring hn2 state selected = .failure) :
    ∃ endpoint : FailureEndpoint hk ring hn2 m L,
      killedStepWithFailure hk ring hn2 state selected = .failure endpoint := by
  have herase := killedStepWithFailure_erase hk ring hn2 state selected
  cases hnode : killedStepWithFailure hk ring hn2 state selected with
  | active next =>
      rw [hnode] at herase
      simp [KilledTrialNode.erase] at herase
      rw [← herase] at hfailure
      contradiction
  | success =>
      rw [hnode] at herase
      simp [KilledTrialNode.erase] at herase
      rw [← herase] at hfailure
      contradiction
  | failure endpoint => exact ⟨endpoint, rfl⟩

/-- Fixed-level splice interface starting from the generic killed-walk
failure marker.  It returns the retained raw endpoint and a fresh minimum-gap
active state under the common upper endpoint `2*((2n)/m)`. -/
theorem killedStep_failure_reseed {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n) (hm2 : 2 ≤ m)
    (hfailure : killedStep hk ring hn2 state selected = .failure) :
    ∃ endpoint : FailureEndpoint hk ring hn2 m L,
      killedStepWithFailure hk ring hn2 state selected = .failure endpoint ∧
      let seed := endpoint.reseed hm2
      endpoint.config = rawStep hk ring state.config selected ∧
        supportCount hk ring endpoint.config = m ∧
        seed.cycle.support =
          barrierSupport hk ring (labelsOf endpoint.config) ∧
        m * seed.cycle.doubledGap seed.index ≤ 2 * n ∧
        seed.cycle.doubledGap seed.index ≤ (2 * n) / m ∧
        (seed.active hm2).config = endpoint.config := by
  obtain ⟨endpoint, hphysical⟩ :=
    exists_failureEndpoint_of_killedStep_eq_failure hk ring hn2 state selected
      hfailure
  exact ⟨endpoint, hphysical,
    killedStepWithFailure_reseed hk ring hn2 state selected endpoint hm2
      hphysical⟩

/-- A support collision wins over every endpoint test, including a front move
which would otherwise touch or cross the upper boundary. -/
theorem killedStep_eq_success_of_drop {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (hdrop : Drops hk ring state.config selected) :
    killedStep hk ring hn2 state selected = .success := by
  simp [killedStep, hdrop]

/-- On the generic stopped process as well, terminal success is equivalent to
an actual support drop; the zero-coordinate bookkeeping branch cannot fire. -/
theorem killedStep_eq_success_iff_drops {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n) :
    killedStep hk ring hn2 state selected = .success ↔
      Drops hk ring state.config selected := by
  constructor
  · intro hsuccess
    unfold killedStep at hsuccess
    split at hsuccess
    · assumption
    · rename_i hnodrop
      have hpos := transported_coord_pos hk ring hn2 state selected hnodrop
      dsimp only at hpos
      dsimp only at hsuccess
      split at hsuccess
      · omega
      · split at hsuccess <;> contradiction
  · exact killedStep_eq_success_of_drop hk ring hn2 state selected

theorem killedStep_down_coord {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) :
    SymmetricKilledWalkFiniteTree.endpointCoord Active.coord L
        (killedStep hk ring hn2 state state.tags.rear) ≤
      Active.coord state - 1 := by
  unfold killedStep
  split
  · simp [SymmetricKilledWalkFiniteTree.endpointCoord]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).rear
      state.config state.tags state.rear_charged
      state.front_charged hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [SymmetricKilledWalkFiniteTree.endpointCoord]
    · split
      · rename_i hupper
        have hlt := state.coord_lt
        change correctedTagGap ring state.config state.tags < L at hlt
        simp [SymmetricKilledWalkFiniteTree.endpointCoord]
        omega
      · simp [SymmetricKilledWalkFiniteTree.endpointCoord, Active.coord]
        exact Nat.le_of_eq hlaw

theorem killedStep_up_coord {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) :
    SymmetricKilledWalkFiniteTree.endpointCoord Active.coord L
        (killedStep hk ring hn2 state state.tags.front) ≤
      Active.coord state + 1 := by
  unfold killedStep
  split
  · simp [SymmetricKilledWalkFiniteTree.endpointCoord]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).front
      state.config state.tags state.rear_charged
      state.front_charged hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [SymmetricKilledWalkFiniteTree.endpointCoord]
    · split
      · rename_i hupper
        simp [SymmetricKilledWalkFiniteTree.endpointCoord]
        change L ≤ correctedTagGap ring state.config state.tags + 1
        omega
      · simp [SymmetricKilledWalkFiniteTree.endpointCoord, Active.coord]
        exact Nat.le_of_eq hlaw

theorem killedStep_frame_coord {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (hrear : selected ≠ state.tags.rear)
    (hfront : selected ≠ state.tags.front) :
    SymmetricKilledWalkFiniteTree.endpointCoord Active.coord L
        (killedStep hk ring hn2 state selected) ≤ Active.coord state := by
  unfold killedStep
  split
  · simp [SymmetricKilledWalkFiniteTree.endpointCoord]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).frame
      state.config state.tags selected
      state.rear_charged state.front_charged hrear hfront hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [SymmetricKilledWalkFiniteTree.endpointCoord]
    · split
      · rename_i hupper
        have hlt := state.coord_lt
        change correctedTagGap ring state.config state.tags < L at hlt
        simp [SymmetricKilledWalkFiniteTree.endpointCoord]
        omega
      · simp [SymmetricKilledWalkFiniteTree.endpointCoord, Active.coord]
        exact Nat.le_of_eq hlaw

theorem killedStep_down_concave {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) :
    SymmetricKilledWalkFiniteTree.endpointConcave Active.coord L
        (killedStep hk ring hn2 state state.tags.rear) ≤
      SymmetricKilledWalkFiniteTree.concave L (Active.coord state - 1) := by
  unfold killedStep
  split
  · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).rear
      state.config state.tags state.rear_charged
      state.front_charged hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
    · split
      · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
      · simp [SymmetricKilledWalkFiniteTree.endpointConcave, Active.coord]
        rw [hlaw]
        exact Nat.le_refl _

theorem killedStep_up_concave {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) :
    SymmetricKilledWalkFiniteTree.endpointConcave Active.coord L
        (killedStep hk ring hn2 state state.tags.front) ≤
      SymmetricKilledWalkFiniteTree.concave L (Active.coord state + 1) := by
  unfold killedStep
  split
  · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).front
      state.config state.tags state.rear_charged
      state.front_charged hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
    · split
      · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
      · simp [SymmetricKilledWalkFiniteTree.endpointConcave, Active.coord]
        rw [hlaw]
        exact Nat.le_refl _

theorem killedStep_frame_concave {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (selected : Fin n)
    (hrear : selected ≠ state.tags.rear)
    (hfront : selected ≠ state.tags.front) :
    SymmetricKilledWalkFiniteTree.endpointConcave Active.coord L
        (killedStep hk ring hn2 state selected) ≤
      SymmetricKilledWalkFiniteTree.concave L (Active.coord state) := by
  unfold killedStep
  split
  · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).frame
      state.config state.tags selected
      state.rear_charged state.front_charged hrear hfront hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
    · split
      · simp [SymmetricKilledWalkFiniteTree.endpointConcave]
      · simp [SymmetricKilledWalkFiniteTree.endpointConcave, Active.coord]
        rw [hlaw]
        exact Nat.le_refl _

/-- The actual killed-walk `Spec` has no external physical assumptions.  All
killing order, charged-tag preservation, edge distinctness, literal coordinate
transport, and endpoint domination are discharged here. -/
def killedWalkSpec {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) :
    SymmetricKilledWalkFiniteTree.Spec (Active hk ring m L) n L where
  step := killedStep hk ring hn2
  coord := Active.coord
  downEdge := Active.downEdge
  upEdge := Active.upEdge
  edge_count := hn2
  coord_pos := fun state => state.coord_pos
  coord_lt := fun state => state.coord_lt
  edges_ne := fun state => state.tags.ne
  down_coord := killedStep_down_coord hk ring hn2
  up_coord := killedStep_up_coord hk ring hn2
  frame_coord := killedStep_frame_coord hk ring hn2
  down_concave := killedStep_down_concave hk ring hn2
  up_concave := killedStep_up_concave hk ring hn2
  frame_concave := killedStep_frame_concave hk ring hn2

/-- Finite-horizon stopped-duration estimate supplied by the generic killed
walk engine once the physical coordinate seam is discharged. -/
theorem finiteDuration_mul_two_le {n k m L : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : Active hk ring m L) (T : Nat) :
    2 * FiniteUniformStoppingTree.truncatedActiveCostNumerator
        (killedStep hk ring hn2) (.active state) T ≤
      n ^ T *
        (n * SymmetricKilledWalkFiniteTree.concave L (Active.coord state)) :=
  SymmetricKilledWalkFiniteTree.duration_mul_two_le
    (killedWalkSpec hk ring hn2) state T

/-! ## Concrete rejection of unconditional frame claims -/

abbrev hostileRing3 : DirectedRing 3 := ⟨by omega⟩

def hostileConfig3 (i : Fin 3) : State 2 := {
  bullet := false
  leader := false
  label := ⟨0, by omega⟩
  probe := false
  phase := if i.val = 1 then false else true }

def hostileTags3 : Tags 3 := {
  rear := 0
  front := 1
  ne := by decide }

/-- The third, untagged edge can be a collision.  In the all-zero-label
three-cycle with phases `(1,0,1)`, selecting edge two advances into tagged rear
edge zero and drops support.  Hence an unconditional “all other edges frame
the coordinate” implication is false; the frame law must assume no drop. -/
theorem hostile_untagged_edge_is_terminal :
    (2 : Fin 3) ≠ hostileTags3.rear ∧
      (2 : Fin 3) ≠ hostileTags3.front ∧
      Drops (by omega) hostileRing3 hostileConfig3 2 := by
  constructor
  · decide
  constructor
  · decide
  · apply (drops_iff_ready_and_occupied (by omega) hostileRing3
      (by omega) hostileConfig3 2).2
    constructor
    · change IsBarrier (by omega) (hostileConfig3 2)
          (hostileConfig3 (hostileRing3.rightNeighbor 2)) ∧
        (hostileConfig3 2).phase = true
      constructor <;> decide
    · apply (barrierAt_labelsOf_iff (by omega) hostileRing3
        hostileConfig3 (hostileRing3.rightNeighbor 2)).2
      decide

end CoalescenceTrial
end CenteredRenewal
end AAFJPK
