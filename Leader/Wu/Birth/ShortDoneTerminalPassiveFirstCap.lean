import Leader.Wu.Birth.ShortDoneTerminalPassivePreCapRow
import Leader.Wu.Safety.CorrectedFormulation

namespace BirthShortDoneTerminalPassiveR4

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR3

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau n : Nat}

/-- Complete actual full-host carrier. -/
abbrev FullConfig (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

/-- All physical raw cells are in the accepted passive class. -/
def HostPassive (C : FullConfig n psi kappa tau) : Prop :=
  ∀ i, Passive (raw (C i))

/-- Exact cyclic labels on the actual physical carrier. -/
def HostCyclic (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : Prop :=
  ∀ e, (raw (C (ring.rightNeighbor e))).label =
    ⟨((raw (C e)).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩

/-- One actual width-two TerminalHost row inserted into the complete carrier.
This is a proof adapter only; no protocol wrapper or schedule runner is added. -/
def hostStep (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau) (e : Fin n) :
    FullConfig n psi kappa tau :=
  localStep ring
    (fun l r => BirthShortDoneTerminalHost.row
      hpsi (by decide : 0 < 2) h2 l r)
    C e

@[simp] theorem hostStep_left (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau) (e : Fin n) :
    hostStep hpsi h2 ring C e e =
      (BirthShortDoneTerminalHost.row
        hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1 := by
  simp [hostStep, PPLLResearchFormulation.localStep]

theorem hostStep_right (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    hostStep hpsi h2 ring C e (ring.rightNeighbor e) =
      (BirthShortDoneTerminalHost.row
        hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2 := by
  simp [hostStep, PPLLResearchFormulation.localStep, hne]

theorem hostStep_other (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau)
    (e i : Fin n) (hie : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    hostStep hpsi h2 ring C e i = C i := by
  simp [hostStep, PPLLResearchFormulation.localStep, hie, hir]

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

/-- Positive repaired width-two cap test on one actual current row. -/
def RowCap2 (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau) (e : Fin n) : Prop :=
  let s := preFinishEntry2 hpsi h2 kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
  s.2.label = widthTerminal (by decide : 0 < 2) h2 ∧ s.2.count = kappa

/-- Strictly before the real repaired cap, evaluated on the current actual row. -/
def RowPreCap2 (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (C : FullConfig n psi kappa tau) (e : Fin n) : Prop :=
  ¬ RowCap2 hpsi h2 kappa ring C e

theorem rowPreCap2_iff (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (e : Fin n) :
    RowPreCap2 hpsi h2 kappa ring C e ↔
      PreCapEntry2 hpsi h2 kappa
        (raw (C e)) (raw (C (ring.rightNeighbor e))) := by
  rfl

/-- Exact accepted repaired-WAIT observation for one actual pre-cap host row. -/
def RowProjection2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (e : Fin n) : Prop :=
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (raw (C e)) (raw (C (ring.rightNeighbor e)))
  let q := BirthShortDoneTerminalHost.row
    hpsi (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  clock (raw q.1) = clock w.1 ∧ clock (raw q.2) = clock w.2

/-- Every listed edge is pre-cap on the actual full-host prefix reached so far. -/
def StrictPreCapRows (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : List (Fin n) → Prop
  | [] => True
  | e :: rest =>
      RowPreCap2 hpsi h2 kappa ring C e ∧
      StrictPreCapRows hpsi h2 kappa tau ring
        (hostStep hpsi h2 ring C e) rest

/-- Explicit successor-label obligations, also evaluated only on actual host states. -/
def CyclicSuccessors2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : List (Fin n) → Prop
  | [] => True
  | e :: rest =>
      HostCyclic hpsi ring (hostStep hpsi h2 ring C e) ∧
      CyclicSuccessors2 hpsi h2 kappa tau ring
        (hostStep hpsi h2 ring C e) rest

/-- Passivity at every actual prefix, including the state after the last pre-cap row. -/
def PassiveAlong2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : List (Fin n) → Prop
  | [] => HostPassive C
  | e :: rest =>
      HostPassive C ∧
      PassiveAlong2 hpsi h2 kappa tau ring
        (hostStep hpsi h2 ring C e) rest

/-- Exact repaired-WAIT row projection for every strictly pre-cap word position. -/
def ProjectionAlong2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : List (Fin n) → Prop
  | [] => True
  | e :: rest =>
      RowProjection2 hpsi h2 kappa tau ring C e ∧
      ProjectionAlong2 hpsi h2 kappa tau ring
        (hostStep hpsi h2 ring C e) rest

/-- `pre` is strictly pre-cap on its actual physical prefixes and `capEdge` is
positive cap at the resulting actual state. The cap edge is not executed. -/
def FirstCap2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) : List (Fin n) → Fin n → Prop
  | [], capEdge => RowCap2 hpsi h2 kappa ring C capEdge
  | e :: rest, capEdge =>
      RowPreCap2 hpsi h2 kappa ring C e ∧
      FirstCap2 hpsi h2 kappa tau ring
        (hostStep hpsi h2 ring C e) rest capEdge

theorem firstCap2_strict (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (pre : List (Fin n)) (capEdge : Fin n)
    (h : FirstCap2 hpsi h2 kappa tau ring C pre capEdge) :
    StrictPreCapRows hpsi h2 kappa tau ring C pre := by
  induction pre generalizing C with
  | nil =>
      simp [StrictPreCapRows]
  | cons e rest ih =>
      change
        RowPreCap2 hpsi h2 kappa ring C e ∧
        FirstCap2 hpsi h2 kappa tau ring
          (hostStep hpsi h2 ring C e) rest capEdge at h
      change
        RowPreCap2 hpsi h2 kappa ring C e ∧
        StrictPreCapRows hpsi h2 kappa tau ring
          (hostStep hpsi h2 ring C e) rest
      exact ⟨h.1,
        ih (C := hostStep hpsi h2 ring C e) h.2⟩

/-- One actual pre-cap width-two host row preserves physical passivity and has
exactly the accepted repaired-WAIT `clock` projection. -/
theorem one_step_preCap2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 2 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (e : Fin n)
    (hpass : HostPassive C) (hcyc : HostCyclic hpsi ring C)
    (hpre : RowPreCap2 hpsi h2 kappa ring C e) :
    HostPassive (hostStep hpsi h2 ring C e) ∧
      RowProjection2 hpsi h2 kappa tau ring C e := by
  let a := registers (raw (C e))
  let b := registers (raw (C (ring.rightNeighbor e)))
  have hla : raw (C e) = cell a := by
    change raw (C e) = cell (registers (raw (C e)))
    exact (hpass e).1
  have hrb : raw (C (ring.rightNeighbor e)) = cell b := by
    change raw (C (ring.rightNeighbor e)) =
      cell (registers (raw (C (ring.rightNeighbor e))))
    exact (hpass (ring.rightNeighbor e)).1
  have hwa : a.wait = true := by
    simpa [a, registers] using (hpass e).2.1
  have hwb : b.wait = true := by
    simpa [b, registers] using (hpass (ring.rightNeighbor e)).2.1
  have hab : b.label =
      ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    simpa [a, b, registers] using hcyc e
  have hpreRaw : PreCapEntry2 hpsi h2 kappa
      (raw (C e)) (raw (C (ring.rightNeighbor e))) :=
    (rowPreCap2_iff hpsi h2 kappa tau ring C e).1 hpre
  have hpreCell : PreCapEntry2 hpsi h2 kappa (cell a) (cell b) := by
    rw [← hla, ← hrb]
    exact hpreRaw
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (cell a) (cell b)
  let q := BirthShortDoneTerminalHost.row
    hpsi (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow :=
    BirthShortDoneTerminalPassiveR3.full_terminal_row2_preCap
      hpsi h2 kappa tau (C e) (C (ring.rightNeighbor e))
      a b hla hrb hwa hwb hab hpreCell
  change
    clock (raw q.1) = clock w.1 ∧
    clock (raw q.2) = clock w.2 ∧
    Passive (raw q.1) ∧ Passive (raw q.2) at hrow
  have hne := rightNeighbor_ne_of_two hn ring e
  have hp : HostPassive (hostStep hpsi h2 ring C e) := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hostStep_left hpsi h2 ring C e]
      simpa [q] using hrow.2.2.1
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        rw [hostStep_right hpsi h2 ring C e hne]
        simpa [q] using hrow.2.2.2
      · rw [hostStep_other hpsi h2 ring C e i hie hir]
        exact hpass i
  have hproj : RowProjection2 hpsi h2 kappa tau ring C e := by
    unfold RowProjection2
    rw [hla, hrb]
    change
      clock (raw q.1) = clock w.1 ∧
      clock (raw q.2) = clock w.2
    exact ⟨hrow.1, hrow.2.1⟩
  exact ⟨hp, hproj⟩

/-- Finite arbitrary edge word: passivity and exact repaired-WAIT projection
hold on every actual row strictly before cap. No scheduler is selected here. -/
theorem word_preCap2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 2 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (word : List (Fin n))
    (hpass : HostPassive C) (hcyc : HostCyclic hpsi ring C)
    (hpre : StrictPreCapRows hpsi h2 kappa tau ring C word)
    (hcycNext : CyclicSuccessors2 hpsi h2 kappa tau ring C word) :
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
      change
        HostCyclic hpsi ring (hostStep hpsi h2 ring C e) ∧
        CyclicSuccessors2 hpsi h2 kappa tau ring
          (hostStep hpsi h2 ring C e) rest at hcycNext
      have hs := one_step_preCap2 hpsi h2 hn kappa tau ring C e
        hpass hcyc hpre.1
      have ht := ih
        (C := hostStep hpsi h2 ring C e)
        hs.1 hcycNext.1 hpre.2 hcycNext.2
      change
        (HostPassive C ∧
          PassiveAlong2 hpsi h2 kappa tau ring
            (hostStep hpsi h2 ring C e) rest) ∧
        (RowProjection2 hpsi h2 kappa tau ring C e ∧
          ProjectionAlong2 hpsi h2 kappa tau ring
            (hostStep hpsi h2 ring C e) rest)
      exact ⟨⟨hpass, ht.1⟩, ⟨hs.2, ht.2⟩⟩

/-- Actual stopped adapter. The positive cap is only an endpoint test; the cap
row itself is deliberately absent from both conclusions. -/
theorem stopped_before_first_cap2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (hn : 2 <= n) (kappa tau : Nat) (ring : DirectedRing n)
    (C : FullConfig n psi kappa tau) (pre : List (Fin n)) (capEdge : Fin n)
    (hpass : HostPassive C) (hcyc : HostCyclic hpsi ring C)
    (hcycNext : CyclicSuccessors2 hpsi h2 kappa tau ring C pre)
    (hfirst : FirstCap2 hpsi h2 kappa tau ring C pre capEdge) :
    PassiveAlong2 hpsi h2 kappa tau ring C pre ∧
      ProjectionAlong2 hpsi h2 kappa tau ring C pre := by
  exact word_preCap2 hpsi h2 hn kappa tau ring C pre hpass hcyc
    (firstCap2_strict hpsi h2 kappa tau ring C pre capEdge hfirst)
    hcycNext

#print axioms BirthShortDoneTerminalPassiveR4.one_step_preCap2
#print axioms BirthShortDoneTerminalPassiveR4.word_preCap2
#print axioms BirthShortDoneTerminalPassiveR4.stopped_before_first_cap2

end BirthShortDoneTerminalPassiveR4
