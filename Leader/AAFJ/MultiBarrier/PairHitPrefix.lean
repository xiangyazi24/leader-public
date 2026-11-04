import Leader.AAFJ.MultiBarrier.SixHitContactBlock
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving

set_option autoImplicit false

namespace AAFJPK.OriginalContactPrefix

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord

/-- Full-state exact support on two tagged physical barrier edges. -/
def ExactTwoAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (rear front : Fin n) : Prop :=
  rear ≠ front ∧
    ∀ e : Fin n,
      BarrierAt hk ring (labelsOf C) e ↔ e = rear ∨ e = front

/-- A hit of either current tagged edge either lowers support immediately or
returns a full-state exact-two endpoint with explicit retagging.  A competing
current tagged edge is represented by the `hhit` disjunction and is never
silently ignored. -/
theorem exactTwoAt_hit_or_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (rear front hit : Fin n)
    (hexact : ExactTwoAt hk ring C rear front)
    (hhit : hit = rear ∨ hit = front) :
    let D := (protocol k hk).step ring C hit
    barrierCount hk ring (labelsOf D) <
        barrierCount hk ring (labelsOf C) ∨
      ∃ rear' front' : Fin n,
        ExactTwoAt hk ring D rear' front' := by
  dsimp
  rcases hexact with ⟨hne, hsupport⟩
  have hhitbar : BarrierAt hk ring (labelsOf C) hit := by
    rcases hhit with h | h
    · rw [h]
      exact (hsupport rear).2 (Or.inl rfl)
    · rw [h]
      exact (hsupport front).2 (Or.inr rfl)
  by_cases hready : AdvanceReady hk ring C hit
  · by_cases hnext : BarrierAt hk ring (labelsOf C)
        (ring.rightNeighbor hit)
    · left
      exact adjacent_ready_barrierCount_lt hk ring hn2 C hit
        (ring.rightNeighbor hit) rfl hhitbar hnext
        hready.2.1 hready.2.2
    · rcases hhit with hhitRear | hhitFront
      · have hreadyRear : AdvanceReady hk ring C rear := by
          simpa [hhitRear] using hready
        have hnextRear : ¬ BarrierAt hk ring (labelsOf C)
            (ring.rightNeighbor rear) := by
          simpa [hhitRear] using hnext
        have hdistinct : ring.rightNeighbor rear ≠ front := by
          intro h
          apply hnextRear
          rw [h]
          exact (hsupport front).2 (Or.inr rfl)
        right
        refine ⟨ring.rightNeighbor rear, front, hdistinct, ?_⟩
        intro e
        rw [hhitRear]
        rw [← mem_barrierSupport_iff hk ring
          (labelsOf ((protocol k hk).step ring C rear)) e]
        rw [protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
          hk ring hn2 C rear hreadyRear hnextRear]
        constructor
        · rintro ⟨i, hi, hred⟩
          have hibar : BarrierAt hk ring (labelsOf C) i :=
            (mem_barrierSupport_iff hk ring (labelsOf C) i).1 hi
          rcases (hsupport i).1 hibar with rfl | rfl
          · left
            simpa [redirectEdge] using hred.symm
          · right
            simpa [redirectEdge, hne.symm] using hred.symm
        · intro he
          rcases he with he | he
          · subst e
            refine ⟨rear, ?_, ?_⟩
            · exact (mem_barrierSupport_iff hk ring
                (labelsOf C) rear).2 ((hsupport rear).2 (Or.inl rfl))
            · simp [redirectEdge]
          · subst e
            refine ⟨front, ?_, ?_⟩
            · exact (mem_barrierSupport_iff hk ring
                (labelsOf C) front).2 ((hsupport front).2 (Or.inr rfl))
            · simp [redirectEdge, hne.symm]
      · have hreadyFront : AdvanceReady hk ring C front := by
          simpa [hhitFront] using hready
        have hnextFront : ¬ BarrierAt hk ring (labelsOf C)
            (ring.rightNeighbor front) := by
          simpa [hhitFront] using hnext
        have hdistinct : rear ≠ ring.rightNeighbor front := by
          intro h
          apply hnextFront
          rw [← h]
          exact (hsupport rear).2 (Or.inl rfl)
        right
        refine ⟨rear, ring.rightNeighbor front, hdistinct, ?_⟩
        intro e
        rw [hhitFront]
        rw [← mem_barrierSupport_iff hk ring
          (labelsOf ((protocol k hk).step ring C front)) e]
        rw [protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
          hk ring hn2 C front hreadyFront hnextFront]
        constructor
        · rintro ⟨i, hi, hred⟩
          have hibar : BarrierAt hk ring (labelsOf C) i :=
            (mem_barrierSupport_iff hk ring (labelsOf C) i).1 hi
          rcases (hsupport i).1 hibar with rfl | rfl
          · left
            simpa [redirectEdge, hne] using hred.symm
          · right
            simpa [redirectEdge] using hred.symm
        · intro he
          rcases he with he | he
          · subst e
            refine ⟨rear, ?_, ?_⟩
            · exact (mem_barrierSupport_iff hk ring
                (labelsOf C) rear).2 ((hsupport rear).2 (Or.inl rfl))
            · simp [redirectEdge, hne]
          · subst e
            refine ⟨front, ?_, ?_⟩
            · exact (mem_barrierSupport_iff hk ring
                (labelsOf C) front).2 ((hsupport front).2 (Or.inr rfl))
            · simp [redirectEdge]
  · have hlabels :
        labelsOf ((protocol k hk).step ring C hit) = labelsOf C :=
      labelsOf_step_eq_self_of_not_ready hk ring C hit hready
    right
    refine ⟨rear, front, hne, ?_⟩
    intro e
    rw [hlabels]
    exact hsupport e

/-! A finite current-pair consumer.  The state machine records the first
strict drop or the first hit outside the currently tagged exact support.  It
does not silently discard a competing hit, and it does not add dummy hits to a
word that has stopped. -/

def hitRun {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :
    (Fin n → State k) → List (Fin n) → Fin n → State k
  | C, [] => C
  | C, hit :: rest =>
      hitRun hk ring ((protocol k hk).step ring C hit) rest

def PairHitDropAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (word : List (Fin n)) : Prop :=
  ∃ pre hit post,
    word = pre ++ hit :: post ∧
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring (hitRun hk ring C pre) hit)) <
      barrierCount hk ring (labelsOf (hitRun hk ring C pre))

def PairHitFailureAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (word : List (Fin n)) : Prop :=
  ∃ pre hit post rear front,
    word = pre ++ hit :: post ∧
    ExactTwoAt hk ring (hitRun hk ring C pre) rear front ∧
    ¬ (hit = rear ∨ hit = front)

theorem pairHitPrefix_drop_or_failure_or_exact
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (rear front : Fin n) (word : List (Fin n))
    (hexact : ExactTwoAt hk ring C rear front) :
    PairHitDropAt hk ring C word ∨
      PairHitFailureAt hk ring C word ∨
      ∃ rear' front',
        ExactTwoAt hk ring (hitRun hk ring C word) rear' front' := by
  induction word generalizing C rear front with
  | nil =>
      exact Or.inr (Or.inr ⟨rear, front, hexact⟩)
  | cons hit rest ih =>
      by_cases hhit : hit = rear ∨ hit = front
      · have hstep := exactTwoAt_hit_or_drop hk ring hn2 C rear front hit
          hexact hhit
        rcases hstep with hdrop | hnext
        · exact Or.inl ⟨[], hit, rest, by simp, by simpa [hitRun] using hdrop⟩
        · rcases hnext with ⟨rear', front', hnext⟩
          rcases ih (C := (protocol k hk).step ring C hit)
              (rear := rear') (front := front') hnext with
            hdrop' | hfail' | hend'
          · rcases hdrop' with ⟨pre, hit', post, hword, hcount⟩
            exact Or.inl ⟨hit :: pre, hit', post, by simpa [hword], by
              simpa [hitRun] using hcount⟩
          · rcases hfail' with
              ⟨pre, hit', post, rear', front', hword, hsupport', hnot⟩
            exact Or.inr (Or.inl ⟨hit :: pre, hit', post, rear', front',
              by simpa [hword], by simpa [hitRun] using hsupport', hnot⟩)
          · rcases hend' with ⟨rear', front', hend'⟩
            exact Or.inr (Or.inr ⟨rear', front', by simpa [hitRun] using hend'⟩)
      · exact Or.inr (Or.inl ⟨[], hit, rest, rear, front, by simp, hexact, hhit⟩)

private theorem barrier_hit_source_controls
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e) :
    ((AAFJPK.protocol k hk).step ring C e e).probe = false ∧
      ((AAFJPK.protocol k hk).step ring C e e).phase = true := by
  have hj :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk _ _ hj]
    cases hp : (C e).phase with
    | false =>
        rw [barrierStep_phase_zero hk _ _ hp]
        cases hprobe : (C e).probe <;>
          simp [probeHitsBarrier, hprobe]
    | true =>
        cases hprobe : (C (ring.rightNeighbor e)).probe with
        | false =>
            rw [barrierStep_phase_one_probe_free hk _ _ hp hprobe]
            cases hu : (C e).probe <;>
              simp [probeHitsBarrier, hu, hp]
        | true =>
            rw [barrierStep_phase_one_probe_blocked hk _ _ hp hprobe]
            cases hu : (C e).probe <;>
              simp [probeHitsBarrier, hu, hp]
  simpa [PopulationProtocol.step, protocol] using hlocal

private theorem nonready_barrier_head_phase
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hnot : ¬ AdvanceReady hk ring C e) :
    (((AAFJPK.protocol k hk).step ring C e)
      (ring.rightNeighbor e)).phase =
      (C (ring.rightNeighbor e)).phase := by
  have hj :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  by_cases hp : (C e).phase = false
  · have hlocal :
        (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
          (C (ring.rightNeighbor e)).phase := by
      rw [transition_of_barrier hk _ _ hj]
      rw [barrierStep_phase_zero hk _ _ hp]
      cases hv : (C (ring.rightNeighbor e)).leader <;> simp [hv]
    simpa [PopulationProtocol.step, protocol,
      rightNeighbor_ne_self ring hn2 e] using hlocal
  · have hp' : (C e).phase = true := by
      cases h : (C e).phase <;> simp_all
    have hprobe : (C (ring.rightNeighbor e)).probe = true := by
      by_cases h : (C (ring.rightNeighbor e)).probe = false
      · exact (hnot ⟨hj, hp', h⟩).elim
      · cases h' : (C (ring.rightNeighbor e)).probe <;> simp_all
    have hlocal :
        (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
          (C (ring.rightNeighbor e)).phase := by
      rw [transition_of_barrier hk _ _ hj]
      rw [barrierStep_phase_one_probe_blocked hk _ _ hp' hprobe]
    simpa [PopulationProtocol.step, protocol,
      rightNeighbor_ne_self ring hn2 e] using hlocal

/-- The first fixed service edge remains a valid stage after a finite current
nonbarrier gap.  A ready hit collides with the other initial barrier; a
nonready hit preserves exact support and exposes the source controls needed by
the next stage. -/
theorem first_gapped_a_stage
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (a b : Fin n) (w0 : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hsupport : ExactTwoBarrierSupport hk ring C a b)
    (hw0 : CurrentNonbarrierWord hk ring C w0) :
    let D := rawRun hk ring C w0
    let E := (AAFJPK.protocol k hk).step ring D a
    ExactTwoBarrierSupport hk ring D a b ∧
      (∀ x, (D x).phase = (C x).phase) ∧
      ((C b).probe = false → (D b).probe = false) ∧
      (barrierCount hk ring (labelsOf E) <
          barrierCount hk ring (labelsOf C) ∨
        (ExactTwoBarrierSupport hk ring E a b ∧
          (E a).phase = true ∧
          (E a).probe = false ∧
          (E b).phase = (C b).phase)) := by
  let D := rawRun hk ring C w0
  let E := (AAFJPK.protocol k hk).step ring D a
  change
    ExactTwoBarrierSupport hk ring D a b ∧
      (∀ x, (D x).phase = (C x).phase) ∧
      ((C b).probe = false → (D b).probe = false) ∧
      (barrierCount hk ring (labelsOf E) <
          barrierCount hk ring (labelsOf C) ∨
        (ExactTwoBarrierSupport hk ring E a b ∧
          (E a).phase = true ∧
          (E a).probe = false ∧
          (E b).phase = (C b).phase))
  have hpreSupport : ExactTwoBarrierSupport hk ring D a b := by
    simpa [D] using
      exactTwoBarrierSupport_rawRun hk ring hw0 hsupport
  have hsD := hpreSupport.2
  have hbarA : BarrierAt hk ring (labelsOf D) a :=
    (hsD a).2 (Or.inl rfl)
  have hbarB : BarrierAt hk ring (labelsOf D) b :=
    (hsD b).2 (Or.inr rfl)
  have hprePhase : ∀ x, (D x).phase = (C x).phase := by
    intro x
    simpa [D] using rawRun_phases_eq hk ring hw0 x
  have hpreHead :
      (C b).probe = false → (D b).probe = false := by
    intro hp
    have ha0 : BarrierAt hk ring (labelsOf C) a :=
      (hsupport.2 a).2 (Or.inl rfl)
    have hh := rawRun_probe_free_barrier_head hk ring hw0 a ha0
      (by simpa [hab] using hp)
    simpa [D, hab] using hh
  have hcountD :
      barrierCount hk ring (labelsOf D) =
        barrierCount hk ring (labelsOf C) := by
    simpa [D] using barrierCount_rawRun_eq hk ring hw0
  refine ⟨hpreSupport, hprePhase, hpreHead, ?_⟩
  by_cases hready : AdvanceReady hk ring D a
  · left
    have hd := original_ready_collision_drops hk ring hn2 D a hready
      (by simpa [hab] using hbarB)
    rw [hcountD] at hd
    simpa [E] using hd
  · right
    have hlabelsE : labelsOf E = labelsOf D := by
      simpa [E] using
        labelsOf_step_eq_self_of_not_ready hk ring D a hready
    have hpostSupport : ExactTwoBarrierSupport hk ring E a b := by
      refine ⟨hpreSupport.1, ?_⟩
      intro e
      rw [hlabelsE]
      exact hsD e
    have hctl := barrier_hit_source_controls hk ring D a hbarA
    have haPhase : (E a).phase = true := by
      simpa [E] using hctl.2
    have haProbe : (E a).probe = false := by
      simpa [E] using hctl.1
    have hbPhaseD :
        (E b).phase = (D b).phase := by
      have hh := nonready_barrier_head_phase hk ring hn2 D a hbarA hready
      simpa [E, hab] using hh
    have hbPhase : (E b).phase = (C b).phase :=
      hbPhaseD.trans (hprePhase b)
    exact ⟨hpostSupport, haPhase, haProbe, hbPhase⟩

#check exactTwoAt_hit_or_drop
#print axioms exactTwoAt_hit_or_drop
#check pairHitPrefix_drop_or_failure_or_exact
#print axioms pairHitPrefix_drop_or_failure_or_exact
#check first_gapped_a_stage
#print axioms first_gapped_a_stage

end AAFJPK.OriginalContactPrefix
