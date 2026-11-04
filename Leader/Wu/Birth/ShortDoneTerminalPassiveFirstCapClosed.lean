import Leader.Wu.Birth.ShortDoneTerminalPassiveFirstCap

namespace BirthShortDoneTerminalPassiveR5

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR3
open BirthShortDoneTerminalPassiveR4

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau n : Nat}

/-- Literal source-level frame: every repaired width-WAIT stage preserves
both physical labels, including the terminal inactive clear. -/
theorem waitWidthEntry_label_frame {psi width cap : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    (waitWidthEntry hpsi hwidth hle cap l r).1.label = l.label ∧
      (waitWidthEntry hpsi hwidth hle cap l r).2.label = r.label := by
  simp [waitWidthEntry, waitSaturatedPrepare, terminalInactiveClear,
    waitWidthCarry, waitWidthReset, waitWidthFinish]

/-- `RowProjection2` already contains enough information to recover the two
actual TerminalHost output labels: project the accepted clock equality to
`Clock.label`, then use the literal WAIT label frame. -/
theorem rowProjection2_label_frame (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau) (e : Fin n)
    (hproj : RowProjection2 hpsi h2 kappa tau ring C e) :
    let q := BirthShortDoneTerminalHost.row
      hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    (raw q.1).label = (raw (C e)).label ∧
      (raw q.2).label = (raw (C (ring.rightNeighbor e))).label := by
  let l := raw (C e)
  let r := raw (C (ring.rightNeighbor e))
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
  let q := BirthShortDoneTerminalHost.row
    hpsi (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  change clock (raw q.1) = clock w.1 ∧
    clock (raw q.2) = clock w.2 at hproj
  have hw := waitWidthEntry_label_frame (cap := kappa)
    hpsi (by decide : 0 < 2) h2 l r
  change w.1.label = l.label ∧ w.2.label = r.label at hw
  have hl := congrArg (fun c : Clock psi => c.label) hproj.1
  have hr := congrArg (fun c : Clock psi => c.label) hproj.2
  change (raw q.1).label = w.1.label at hl
  change (raw q.2).label = w.2.label at hr
  change (raw q.1).label = l.label ∧ (raw q.2).label = r.label
  exact ⟨hl.trans hw.1, hr.trans hw.2⟩

private theorem rightNeighbor_ne_of_two (hn : 2 <= n)
    (ring : DirectedRing n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv : (e.val + 1) % n = e.val := by
    simpa [DirectedRing.rightNeighbor] using congrArg Fin.val h
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- If the current actual row has the accepted repaired-WAIT projection, then
one real `hostStep` preserves the label of every physical site. -/
theorem hostStep_label_frame_of_projection
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 2 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau) (e : Fin n)
    (hproj : RowProjection2 hpsi h2 kappa tau ring C e) :
    ∀ i, (raw (hostStep hpsi h2 ring C e i)).label = (raw (C i)).label := by
  let q := BirthShortDoneTerminalHost.row
    hpsi (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hp := rowProjection2_label_frame hpsi h2 kappa tau ring C e hproj
  change (raw q.1).label = (raw (C e)).label ∧
    (raw q.2).label = (raw (C (ring.rightNeighbor e))).label at hp
  have hne := rightNeighbor_ne_of_two hn ring e
  intro i
  by_cases hie : i = e
  · subst i
    rw [hostStep_left hpsi h2 ring C e]
    simpa [q] using hp.1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [hostStep_right hpsi h2 ring C e hne]
      simpa [q] using hp.2
    · rw [hostStep_other hpsi h2 ring C e i hie hir]

/-- Exact cyclic labels are therefore an actual successor theorem, not an
extra future-closure premise. -/
theorem hostCyclic_hostStep_of_projection
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 2 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau) (e : Fin n)
    (hcyc : HostCyclic hpsi ring C)
    (hproj : RowProjection2 hpsi h2 kappa tau ring C e) :
    HostCyclic hpsi ring (hostStep hpsi h2 ring C e) := by
  have hf := hostStep_label_frame_of_projection
    hpsi h2 hn kappa tau ring C e hproj
  unfold HostCyclic at hcyc ⊢
  intro i
  simpa only [hf (ring.rightNeighbor i), hf i] using hcyc i

/-- Closed one-step adapter from only the actual current pre-cap hypotheses. -/
theorem one_step_preCap2_closed (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 2 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau) (e : Fin n)
    (hpass : HostPassive C) (hcyc : HostCyclic hpsi ring C)
    (hpre : RowPreCap2 hpsi h2 kappa ring C e) :
    HostPassive (hostStep hpsi h2 ring C e) ∧
      HostCyclic hpsi ring (hostStep hpsi h2 ring C e) ∧
      RowProjection2 hpsi h2 kappa tau ring C e := by
  have hs := BirthShortDoneTerminalPassiveR4.one_step_preCap2
    hpsi h2 hn kappa tau ring C e hpass hcyc hpre
  have hc := hostCyclic_hostStep_of_projection
    hpsi h2 hn kappa tau ring C e hcyc hs.2
  exact ⟨hs.1, hc, hs.2⟩

/-- Arbitrary finite actual host word, relative only to the recursively tested
strict pre-cap condition. No successor invariant is supplied by the caller. -/
theorem word_preCap2_closed (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 2 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau) (word : List (Fin n))
    (hpass : HostPassive C) (hcyc : HostCyclic hpsi ring C)
    (hpre : StrictPreCapRows hpsi h2 kappa tau ring C word) :
    PassiveAlong2 hpsi h2 kappa tau ring C word ∧
      ProjectionAlong2 hpsi h2 kappa tau ring C word := by
  induction word generalizing C with
  | nil =>
      change HostPassive C ∧ True
      exact ⟨hpass, trivial⟩
  | cons e rest ih =>
      change
        RowPreCap2 hpsi h2 kappa ring C e ∧
        StrictPreCapRows hpsi h2 kappa tau ring
          (hostStep hpsi h2 ring C e) rest at hpre
      have hs := one_step_preCap2_closed
        hpsi h2 hn kappa tau ring C e hpass hcyc hpre.1
      have ht := ih
        (C := hostStep hpsi h2 ring C e)
        hs.1 hs.2.1 hpre.2
      change
        (HostPassive C ∧
          PassiveAlong2 hpsi h2 kappa tau ring
            (hostStep hpsi h2 ring C e) rest) ∧
        (RowProjection2 hpsi h2 kappa tau ring C e ∧
          ProjectionAlong2 hpsi h2 kappa tau ring
            (hostStep hpsi h2 ring C e) rest)
      exact ⟨⟨hpass, ht.1⟩, ⟨hs.2.2, ht.2⟩⟩

/-- Strictly-before-first-cap adapter on the actual full host. The positive cap
edge is only the endpoint witness inside `FirstCap2`; it is not executed here. -/
theorem stopped_before_first_cap2_closed
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 2 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau) (pre : List (Fin n)) (capEdge : Fin n)
    (hpass : HostPassive C) (hcyc : HostCyclic hpsi ring C)
    (hfirst : FirstCap2 hpsi h2 kappa tau ring C pre capEdge) :
    PassiveAlong2 hpsi h2 kappa tau ring C pre ∧
      ProjectionAlong2 hpsi h2 kappa tau ring C pre := by
  exact word_preCap2_closed hpsi h2 hn kappa tau ring C pre hpass hcyc
    (firstCap2_strict hpsi h2 kappa tau ring C pre capEdge hfirst)

#print axioms BirthShortDoneTerminalPassiveR5.waitWidthEntry_label_frame
#print axioms BirthShortDoneTerminalPassiveR5.rowProjection2_label_frame
#print axioms BirthShortDoneTerminalPassiveR5.hostStep_label_frame_of_projection
#print axioms BirthShortDoneTerminalPassiveR5.one_step_preCap2_closed
#print axioms BirthShortDoneTerminalPassiveR5.word_preCap2_closed
#print axioms BirthShortDoneTerminalPassiveR5.stopped_before_first_cap2_closed

end BirthShortDoneTerminalPassiveR5
