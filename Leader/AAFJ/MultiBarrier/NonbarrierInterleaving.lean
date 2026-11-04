import Leader.AAFJ.NonbarrierWord
import Leader.AAFJ.MultiBarrier.NonbarrierReady

set_option autoImplicit false


set_option autoImplicit false


namespace AAFJPK
namespace OriginalNonbarrierFrame


open BarrierAlgebra


/-- On the literal original journal nonbarrier branch, neither endpoint phase
changes; moreover a probe-free initiator stays probe-free. -/
private theorem transition_nonbarrier_control_frames
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v) :
    (transition hk u v).1.phase = u.phase ∧
      (transition hk u v).2.phase = v.phase ∧
      (u.probe = false → (transition hk u v).1.probe = false) := by
  rw [transition_of_nonbarrier hk u v hnon]
  cases hv : v.leader <;> cases hb : v.bullet <;>
    cases hp : u.probe <;>
    simp [nonBarrierStep, hv, hb, hp]


/-- A current-prestate nonbarrier interaction preserves every phase bit.
No non-singleton hypothesis is needed: on a self-loop the packaged step uses
the initiator component, whose phase is also framed. -/
theorem nonbarrier_step_preserves_phase
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hnon : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    ∀ i : Fin n,
      (((protocol k hk).step ring C e) i).phase = (C i).phase := by
  have hlocal := transition_nonbarrier_control_frames hk
    (C e) (C (ring.rightNeighbor e)) hnon
  intro i
  by_cases hie : i = e
  · subst i
    simpa [PopulationProtocol.step, protocol] using hlocal.1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, protocol, hie] using hlocal.2.1
    · simp [PopulationProtocol.step, protocol, hie, hir]


/-- If b is currently charged and its head is probe-free, then any
current-prestate nonbarrier interaction keeps that head probe-free.


The only interaction that could write true to that physical head would have
it as responder. Injectivity of rightNeighbor would then make the selected
edge equal to b, contradicting charged-at-b versus selected-nonbarrier. -/
theorem nonbarrier_step_preserves_probe_free_barrier_head
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e b : Fin n)
    (hnon : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hcharged : BarrierAt hk ring (labelsOf C) b)
    (hprobe : (C (ring.rightNeighbor b)).probe = false) :
    (((protocol k hk).step ring C e) (ring.rightNeighbor b)).probe = false := by
  have hlocal := transition_nonbarrier_control_frames hk
    (C e) (C (ring.rightNeighbor e)) hnon
  by_cases hsource : ring.rightNeighbor b = e
  · have hprobeE : (C e).probe = false := by
      simpa [hsource] using hprobe
    have hleft := hlocal.2.2 hprobeE
    rw [hsource]
    simpa [PopulationProtocol.step, protocol] using hleft
  · by_cases hresp :
      ring.rightNeighbor b = ring.rightNeighbor e
    · have hbe : b = e := rightNeighbor_injective ring hresp
      subst e
      exact
        (hnon ((barrierAt_labelsOf_iff hk ring C b).1 hcharged)).elim
    · simpa [PopulationProtocol.step, protocol, hsource, hresp] using hprobe


/-- AdvanceReady of a charged edge survives one current-prestate nonbarrier
interaction of the original AAFJPK.protocol. -/
theorem nonbarrier_step_preserves_advanceReady
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e b : Fin n)
    (hnon : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hready : AdvanceReady hk ring C b) :
    AdvanceReady hk ring ((protocol k hk).step ring C e) b := by
  let D : Fin n → State k := (protocol k hk).step ring C e
  rcases hready with ⟨hbar, hphase, hprobe⟩
  have hb : BarrierAt hk ring (labelsOf C) b :=
    (barrierAt_labelsOf_iff hk ring C b).2 hbar
  have hnotE : ¬ AdvanceReady hk ring C e := by
    intro he
    exact hnon he.1
  have hlabels : labelsOf D = labelsOf C := by
    dsimp [D]
    exact labelsOf_step_eq_self_of_not_ready hk ring C e hnotE
  have hbD : BarrierAt hk ring (labelsOf D) b := by
    rw [hlabels]
    exact hb
  have hphaseD : (D b).phase = true := by
    dsimp [D]
    exact
      (nonbarrier_step_preserves_phase hk ring C e hnon b).trans hphase
  have hprobeD : (D (ring.rightNeighbor b)).probe = false := by
    dsimp [D]
    exact nonbarrier_step_preserves_probe_free_barrier_head
      hk ring C e b hnon hb hprobe
  exact
    ⟨(barrierAt_labelsOf_iff hk ring D b).1 hbD, hphaseD, hprobeD⟩


#check nonbarrier_step_preserves_phase
#check nonbarrier_step_preserves_probe_free_barrier_head
#check nonbarrier_step_preserves_advanceReady


#print axioms nonbarrier_step_preserves_phase
#print axioms nonbarrier_step_preserves_probe_free_barrier_head
#print axioms nonbarrier_step_preserves_advanceReady


end OriginalNonbarrierFrame
end AAFJPK

namespace AAFJPK.OriginalNonbarrierWord

open BarrierAlgebra
open AAFJPK.OriginalNonbarrierFrame

/-! These are the two frames not exported by the generic NB* modules: a
selected edge outside an adjacent pair leaves the shared node entirely
untouched, and an explicit word-level phase/probe consequence. -/

def OffPairWord {n : Nat} (a b : Fin n) : List (Fin n) → Prop
  | [] => True
  | e :: es => e ≠ a ∧ e ≠ b ∧ OffPairWord a b es

theorem off_pair_step_preserves_shared_node
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b e : Fin n)
    (hab : ring.rightNeighbor a = b)
    (hea : e ≠ a) (heb : e ≠ b) :
    ((protocol k hk).step ring C e) b = C b := by
  have hbe : b ≠ e := fun h => heb h.symm
  have hresp : b ≠ ring.rightNeighbor e := by
    intro h
    have hae : a = e := rightNeighbor_injective ring (hab.trans h)
    exact hea hae.symm
  simp [PopulationProtocol.step, protocol, hbe, hresp]

theorem rawRun_shared_node_eq_of_offPair
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    {a b : Fin n} (hab : ring.rightNeighbor a = b)
    (hoff : OffPairWord a b word) :
    rawRun hk ring C word b = C b := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e es ih =>
      rcases hoff with ⟨hea, heb, htail⟩
      change rawRun hk ring ((protocol k hk).step ring C e) es b = C b
      have htailEq :
          rawRun hk ring ((protocol k hk).step ring C e) es b =
            ((protocol k hk).step ring C e) b := ih htail
      exact htailEq.trans
        (off_pair_step_preserves_shared_node hk ring C a b e hab hea heb)

theorem rawRun_phases_eq
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (hword : CurrentNonbarrierWord hk ring C word) :
    ∀ i : Fin n, (rawRun hk ring C word i).phase = (C i).phase := by
  induction word generalizing C with
  | nil =>
      intro i
      rfl
  | cons e es ih =>
      rcases hword with ⟨hnb, htail⟩
      intro i
      change
        (rawRun hk ring ((protocol k hk).step ring C e) es i).phase =
          (C i).phase
      calc
        (rawRun hk ring ((protocol k hk).step ring C e) es i).phase =
            (((protocol k hk).step ring C e) i).phase := ih htail i
        _ = (C i).phase :=
          nonbarrier_step_preserves_phase hk ring C e hnb i

theorem rawRun_probe_free_barrier_head
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (hword : CurrentNonbarrierWord hk ring C word)
    (b : Fin n) (hcharged : BarrierAt hk ring (labelsOf C) b)
    (hprobe : (C (ring.rightNeighbor b)).probe = false) :
    (rawRun hk ring C word (ring.rightNeighbor b)).probe = false := by
  induction word generalizing C with
  | nil =>
      exact hprobe
  | cons e es ih =>
      rcases hword with ⟨hnb, htail⟩
      have hprobeStep := nonbarrier_step_preserves_probe_free_barrier_head
        hk ring C e b hnb hcharged hprobe
      have hnot : ¬ AdvanceReady hk ring C e :=
        not_advanceReady_of_nonbarrier hk ring C e hnb
      have hlabels :
          labelsOf ((protocol k hk).step ring C e) = labelsOf C :=
        labelsOf_step_eq_self_of_not_ready hk ring C e hnot
      have hchargedStep :
          BarrierAt hk ring
            (labelsOf ((protocol k hk).step ring C e)) b := by
        rw [hlabels]
        exact hcharged
      change
        (rawRun hk ring ((protocol k hk).step ring C e) es
          (ring.rightNeighbor b)).probe = false
      exact ih htail hchargedStep hprobeStep

theorem rawRun_preserves_advanceReady
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (b : Fin n) (hready : AdvanceReady hk ring C b)
    (hword : CurrentNonbarrierWord hk ring C word) :
    AdvanceReady hk ring (rawRun hk ring C word) b := by
  induction word generalizing C with
  | nil =>
      exact hready
  | cons e es ih =>
      rcases hword with ⟨hnb, htail⟩
      have hnon : ¬ BarrierAt hk ring (labelsOf C) e := by
        intro h
        exact hnb ((barrierAt_labelsOf_iff hk ring C e).1 h)
      have hstep :=
        AAFJPK.OriginalNonbarrierRun.step_nonbarrier_preserves_advanceReady
          hk ring C b e hready hnon
      exact ih hstep htail

theorem rawRun_shared_barrier_head_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (hword : CurrentNonbarrierWord hk ring C word)
    (b : Fin n) (hcharged : BarrierAt hk ring (labelsOf C) b)
    (hprobe : (C (ring.rightNeighbor b)).probe = false) :
    BarrierAt hk ring (labelsOf (rawRun hk ring C word)) b ∧
      (rawRun hk ring C word (ring.rightNeighbor b)).probe = false := by
  refine ⟨(barrierAt_rawRun_iff hk ring hword b).2 hcharged,
    rawRun_probe_free_barrier_head hk ring hword b hcharged hprobe⟩

theorem rawRun_incoming_barrier_head_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {D : Fin n → State k} {word : List (Fin n)}
    (a b : Fin n) (hab : ring.rightNeighbor a = b)
    (hword : CurrentNonbarrierWord hk ring D word)
    (hcharged : BarrierAt hk ring (labelsOf D) a)
    (hprobe : (D b).probe = false) :
    BarrierAt hk ring (labelsOf (rawRun hk ring D word)) a ∧
      (rawRun hk ring D word b).probe = false := by
  have hprobe' : (D (ring.rightNeighbor a)).probe = false := by
    simpa [hab] using hprobe
  have hframe := rawRun_shared_barrier_head_frame hk ring hword a
    hcharged hprobe'
  exact ⟨hframe.1, by simpa [hab] using hframe.2⟩

#check off_pair_step_preserves_shared_node
#check rawRun_shared_node_eq_of_offPair
#check rawRun_phases_eq
#check rawRun_preserves_advanceReady
#check rawRun_shared_barrier_head_frame
#check rawRun_incoming_barrier_head_frame

#print axioms off_pair_step_preserves_shared_node
#print axioms rawRun_shared_node_eq_of_offPair
#print axioms rawRun_phases_eq
#print axioms rawRun_preserves_advanceReady
#print axioms rawRun_shared_barrier_head_frame
#print axioms rawRun_incoming_barrier_head_frame

end AAFJPK.OriginalNonbarrierWord
