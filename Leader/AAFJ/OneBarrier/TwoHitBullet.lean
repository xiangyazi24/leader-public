import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.NonbarrierWord

/-!
# Two-hit transport of an ordinary AAFJ bullet

This file isolates the first local step in the direct one-barrier cleanup
schedule for the journal protocol.  A bullet away from the barrier head is
served twice on its incoming ordinary edge.  The first service either moves
the bullet or removes a leader that is carrying it; the second service then
moves the bullet in the latter case.

The positive cut-coordinate hypothesis is essential.  Merely assuming that
the bullet site differs from the barrier tail is false: on the three-node
configuration in `twoHit_head_counterexample` below, the selected incoming
edge is the barrier itself and two services leave the head bullet in place.
-/

set_option autoImplicit false

namespace AAFJPK.TwoHitBullet

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord

/-- Number of physical bullet bits in a configuration. -/
def BulletCount {n k : Nat} (C : Fin n → State k) : Nat :=
  bitCount (fun i => (C i).bullet)

/-- Moving to the physical predecessor decreases a positive cut coordinate
by exactly one. -/
theorem cutCoord_leftNeighbor_of_pos {n : Nat} (ring : DirectedRing n)
    (b i : Fin n) (hi : 0 < (cutCoord ring b i).val) :
    (cutCoord ring b (ring.leftNeighbor i)).val + 1 =
      (cutCoord ring b i).val := by
  let c := cutCoord ring b i
  have hval := leftNeighbor_val_of_pos ring c hi
  have hphys : ring.leftNeighbor i = cutPos ring b (ring.leftNeighbor c) := by
    apply rightNeighbor_injective ring
    rw [rightNeighbor_leftNeighbor_clean, ← cutPos_rightNeighbor,
      rightNeighbor_leftNeighbor_clean, cutPos_cutCoord]
  rw [hphys, cutCoord_cutPos]
  change (ring.leftNeighbor c).val + 1 = c.val
  omega

private theorem incoming_ne_barrier_of_pos {n : Nat}
    (ring : DirectedRing n) (b p : Fin n)
    (hpos : 0 < (cutCoord ring b p).val) :
    ring.leftNeighbor p ≠ b := by
  intro h
  have hp : p = ring.rightNeighbor b := by
    rw [← h, rightNeighbor_leftNeighbor_clean]
  have hz : (cutCoord ring b p).val = 0 := by
    subst p
    have hzero := cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
    simpa using congrArg Fin.val hzero
  omega

/-- Two services of the incoming ordinary edge transport a bullet one site
toward the unique barrier head.  All sites other than the two endpoints are
unchanged. -/
theorem twoHit_fields
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hbullet : (C p).bullet = true)
    (hpos : 0 < (cutCoord ring b p).val) :
    let e := ring.leftNeighbor p
    let C1 := (protocol k hk).step ring C e
    let D := (protocol k hk).step ring C1 e
    CurrentNonbarrierWord hk ring C [e, e] ∧
      OneBarrierAt hk ring D b ∧
      (D p).bullet = false ∧
      (D e).bullet = true ∧
      (∀ i, i ≠ e → i ≠ p → D i = C i) := by
  have hn2 : 1 < n := by omega
  let e := ring.leftNeighbor p
  let C1 := (protocol k hk).step ring C e
  let D := (protocol k hk).step ring C1 e
  have her : ring.rightNeighbor e = p := by
    simpa [e] using rightNeighbor_leftNeighbor_clean ring p
  have hep : e ≠ p := by
    intro h
    have := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    exact this (her.trans h.symm)
  have heb : e ≠ b := by
    simpa [e] using incoming_ne_barrier_of_pos ring b p hpos
  have hnb0 : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro hbar
    have hphys : BarrierAt hk ring (labelsOf C) e :=
      (barrierAt_labelsOf_iff hk ring C e).2 hbar
    exact heb ((hB e).1 hphys)
  have hnot0 : ¬ AdvanceReady hk ring C e :=
    not_advanceReady_of_nonbarrier hk ring C e hnb0
  have hlabels1 : labelsOf C1 = labelsOf C := by
    dsimp [C1]
    exact labelsOf_step_eq_self_of_not_ready hk ring C e hnot0
  have hB1 : OneBarrierAt hk ring C1 b := by
    intro q
    unfold BarrierAt
    rw [hlabels1]
    exact hB q
  have hnb1 : ¬ IsBarrier hk (C1 e) (C1 (ring.rightNeighbor e)) := by
    intro hbar
    have hphys : BarrierAt hk ring (labelsOf C1) e :=
      (barrierAt_labelsOf_iff hk ring C1 e).2 hbar
    exact heb ((hB1 e).1 hphys)
  have hnot1 : ¬ AdvanceReady hk ring C1 e :=
    not_advanceReady_of_nonbarrier hk ring C1 e hnb1
  have hlabelsD : labelsOf D = labelsOf C1 := by
    dsimp [D]
    exact labelsOf_step_eq_self_of_not_ready hk ring C1 e hnot1
  have hBD : OneBarrierAt hk ring D b := by
    intro q
    unfold BarrierAt
    rw [hlabelsD, hlabels1]
    exact hB q
  have hpair0 : transition hk (C e) (C p) = nonBarrierStep (C e) (C p) := by
    rw [transition_of_nonbarrier]
    simpa [her] using hnb0
  have hpair1 : transition hk (C1 e) (C1 p) =
      nonBarrierStep (C1 e) (C1 p) := by
    apply transition_of_nonbarrier
    simpa [her] using hnb1
  have hfields : (D p).bullet = false ∧ (D e).bullet = true := by
    cases hl : (C p).leader with
    | false =>
        have hC1pBullet : (C1 p).bullet = false := by
          cases hp : (C e).probe <;>
            simp [C1, PopulationProtocol.step, protocol, her,
              hep.symm, hpair0, nonBarrierStep, hl, hbullet, hp]
        have hC1eBullet : (C1 e).bullet = true := by
          cases hp : (C e).probe <;>
            simp [C1, PopulationProtocol.step, protocol, her,
              hpair0, nonBarrierStep, hl, hbullet, hp]
        have hC1pLeader : (C1 p).leader = false := by
          cases hp : (C e).probe <;>
            simp [C1, PopulationProtocol.step, protocol, her,
              hep.symm, hpair0, nonBarrierStep, hl, hbullet, hp]
        have hlocal2 :
            (transition hk (C1 e) (C1 p)).2.bullet = false ∧
              (transition hk (C1 e) (C1 p)).1.bullet = true := by
          rw [hpair1]
          cases hp1 : (C1 e).probe <;>
            simp [nonBarrierStep, hC1pLeader, hC1pBullet,
              hC1eBullet, hp1]
        constructor
        · simpa [D, PopulationProtocol.step, protocol, her, hep,
            hep.symm] using hlocal2.1
        · simpa [D, PopulationProtocol.step, protocol, her, hep,
            hep.symm] using hlocal2.2
    | true =>
        have hC1pBullet : (C1 p).bullet = true := by
          simp [C1, PopulationProtocol.step, protocol, her,
            hep.symm, hpair0, nonBarrierStep, hl, hbullet]
        have hC1pLeader : (C1 p).leader = false := by
          simp [C1, PopulationProtocol.step, protocol, her,
            hep.symm, hpair0, nonBarrierStep, hl, hbullet]
        have hlocal2 :
            (transition hk (C1 e) (C1 p)).2.bullet = false ∧
              (transition hk (C1 e) (C1 p)).1.bullet = true := by
          rw [hpair1]
          cases hp1 : (C1 e).probe <;>
            simp [nonBarrierStep, hC1pLeader, hC1pBullet, hp1]
        constructor
        · simpa [D, PopulationProtocol.step, protocol, her, hep,
            hep.symm] using hlocal2.1
        · simpa [D, PopulationProtocol.step, protocol, her, hep,
            hep.symm] using hlocal2.2
  have hframe : ∀ i, i ≠ e → i ≠ p → D i = C i := by
    intro i hie hip
    simp [D, C1, PopulationProtocol.step, her, hie, hip]
    rfl
  have hword : CurrentNonbarrierWord hk ring C [e, e] := by
    simp only [CurrentNonbarrierWord]
    exact ⟨hnb0, hnb1, trivial⟩
  change CurrentNonbarrierWord hk ring C [e, e] ∧
    OneBarrierAt hk ring D b ∧
    (D p).bullet = false ∧ (D e).bullet = true ∧
    (∀ i, i ≠ e → i ≠ p → D i = C i)
  exact ⟨hword, hBD, hfields.1, hfields.2, hframe⟩

private theorem bitCount_transport
    {n : Nat} (before after : Fin n → Bool) (e p : Fin n)
    (hep : e ≠ p)
    (hpBefore : before p = true)
    (hpAfter : after p = false)
    (heAfter : after e = true)
    (hframe : ∀ i, i ≠ e → i ≠ p → after i = before i) :
    (before e = true ∧ bitCount after + 1 = bitCount before) ∨
      (before e = false ∧ bitCount after = bitCount before) := by
  cases heBefore : before e with
  | true =>
      left
      refine ⟨rfl, bitCount_single_drop before after p hpBefore hpAfter ?_⟩
      intro i hip
      by_cases hie : i = e
      · subst i
        rw [heAfter, heBefore]
      · exact hframe i hie hip
  | false =>
      right
      let mid : Fin n → Bool := fun i => if i = e then true else before i
      have hmidBirth : bitCount mid = bitCount before + 1 := by
        apply bitCount_single_birth before mid e heBefore
        · simp [mid]
        · intro i hie
          simp [mid, hie]
      have hmidP : mid p = true := by
        simp [mid, hep.symm, hpBefore]
      have hdrop : bitCount after + 1 = bitCount mid := by
        apply bitCount_single_drop mid after p hmidP hpAfter
        intro i hip
        by_cases hie : i = e
        · subst i
          simp [mid, heAfter]
        · rw [hframe i hie hip]
          simp [mid, hie]
      refine ⟨rfl, ?_⟩
      omega

/-- Source-facing two-hit bullet transport on an ordinary edge.

The result records the literal word, preservation of the same unique barrier,
the transported endpoint bits, the exact collision/no-collision count law,
and the one-unit cut-distance decrement used by the cleanup induction. -/
theorem twoHit_moves_bullet_left_of_pos
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hbullet : (C p).bullet = true)
    (hpos : 0 < (cutCoord ring b p).val) :
    let e := ring.leftNeighbor p
    let D := rawRun hk ring C [e, e]
    CurrentNonbarrierWord hk ring C [e, e] ∧
      OneBarrierAt hk ring D b ∧
      (D p).bullet = false ∧
      (D e).bullet = true ∧
      BulletCount D ≤ BulletCount C ∧
      (cutCoord ring b e).val + 1 = (cutCoord ring b p).val ∧
      (((C e).bullet = true ∧ BulletCount D + 1 = BulletCount C) ∨
        ((C e).bullet = false ∧ BulletCount D = BulletCount C)) := by
  let e := ring.leftNeighbor p
  let D := rawRun hk ring C [e, e]
  have hf := twoHit_fields hk ring hn3 C b p hB hbullet hpos
  dsimp only at hf
  rcases hf with ⟨hword, hBD, hpD, heD, hframe⟩
  have hn2 : 1 < n := by omega
  have hep : e ≠ p := by
    intro h
    have hr := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    apply hr
    rw [show ring.rightNeighbor e = p by
      simpa [e] using rightNeighbor_leftNeighbor_clean ring p, h.symm]
  have hcount := bitCount_transport
    (fun i => (C i).bullet) (fun i => (D i).bullet) e p hep
    hbullet hpD heD (fun i hie hip => congrArg State.bullet (hframe i hie hip))
  have hle : BulletCount D ≤ BulletCount C := by
    rcases hcount with hdrop | heq
    · change bitCount (fun i => (D i).bullet) ≤
        bitCount (fun i => (C i).bullet)
      omega
    · change bitCount (fun i => (D i).bullet) ≤
        bitCount (fun i => (C i).bullet)
      omega
  have hdist := cutCoord_leftNeighbor_of_pos ring b p hpos
  change CurrentNonbarrierWord hk ring C [e, e] ∧
    OneBarrierAt hk ring D b ∧
    (D p).bullet = false ∧ (D e).bullet = true ∧
    BulletCount D ≤ BulletCount C ∧
    (cutCoord ring b e).val + 1 = (cutCoord ring b p).val ∧
    (((C e).bullet = true ∧ BulletCount D + 1 = BulletCount C) ∨
      ((C e).bullet = false ∧ BulletCount D = BulletCount C))
  exact ⟨hword, hBD, hpD, heD, hle, by simpa [e] using hdist, hcount⟩

/-! ## Closed regression for the excluded barrier-head case -/

private theorem hk2 : 0 < (2 : Nat) := by decide
set_option linter.defProp false in
private def ring3 : DirectedRing 3 := ⟨by decide⟩

private def headCounterConfig (i : Fin 3) : State 2 :=
  if i = 0 then
    { bullet := true, leader := false, label := 0,
      probe := false, phase := false }
  else if i = 1 then
    { bullet := false, leader := false, label := 1,
      probe := false, phase := false }
  else
    { bullet := false, leader := false, label := 0,
      probe := false, phase := false }

/-- At the barrier head, `p ≠ b` does not make the incoming edge ordinary:
on the smallest permitted ring, two services are blocked barrier services and
the head bullet does not move. -/
theorem twoHit_head_counterexample :
    OneBarrierAt hk2 ring3 headCounterConfig (2 : Fin 3) ∧
    (headCounterConfig (0 : Fin 3)).bullet = true ∧
    (0 : Fin 3) ≠ (2 : Fin 3) ∧
    ring3.leftNeighbor (0 : Fin 3) = (2 : Fin 3) ∧
    (cutCoord ring3 (2 : Fin 3) (0 : Fin 3)).val = 0 ∧
    BulletCount headCounterConfig = 1 ∧
    BulletCount (rawRun hk2 ring3 headCounterConfig [2, 2]) = 1 ∧
    (rawRun hk2 ring3 headCounterConfig [2, 2] (0 : Fin 3)).bullet = true ∧
    (rawRun hk2 ring3 headCounterConfig [2, 2] (2 : Fin 3)).bullet = false := by
  decide

#print axioms cutCoord_leftNeighbor_of_pos
#print axioms twoHit_fields
#print axioms twoHit_moves_bullet_left_of_pos
#print axioms twoHit_head_counterexample

end AAFJPK.TwoHitBullet
