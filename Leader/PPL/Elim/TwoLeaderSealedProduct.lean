import Leader.PPL.Elim.CleanReadyDrain
import Leader.PPL.Elim.LocalDeletionCounting

/-!
# LD(736): two-leader sealed product

File 3 is not yet on main.  This file therefore mirrors the File-3 phase
interface and takes its physical one-step theorem as the named Prop
`SealedStepSpec`.  The corrected `PhaseHolds` includes the current strict
sector-interior follower condition.

The two-leader closure itself needs no additional compatibility invariant:
for `F.i = F.k`, the two complementary phase witnesses close independently
under `SealedStepSpec`, while a deletion of either sector endpoint is exactly
a `TaggedDeleted` event.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

/-! ## File-3 interface, mirrored until LDLocalSealed is on main -/

inductive SectorPhase where
  | ready
  | dummy (p : Nat)
  | live (p : Nat)
  | ret (q : Nat)
  deriving DecidableEq

/-- Current strict sector interior is follower-only. -/
def SectorInteriorFollowers
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  ∀ q, 0 < q → q < A.gap →
    (C (advance ring A.left q)).leader = false

/-- Exactly one body bullet, at offset `p`. -/
def OnlySectorBullet
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (b : Fin 3) : Prop :=
  p < A.gap ∧
    (C (advance ring A.left p)).bullet = b ∧
    ∀ q, q < A.gap → q ≠ p →
      (C (advance ring A.left q)).bullet = (0 : Fin 3)

/-- Signal is zero strictly before `q`. -/
def SignalZeroBefore
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (q : Nat) : Prop :=
  ∀ r, r < q →
    (C (advance ring A.left r)).signalB = false

/-- Corrected File-3 checker predicate.  In particular, every phase witness
carries the current strict-interior follower invariant. -/
def PhaseHolds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) :
    SectorPhase → Prop
  | .ready =>
      SectorInteriorFollowers A C ∧
        CleanReady A C
  | .dummy p =>
      SectorInteriorFollowers A C ∧
        OnlySectorBullet A C p (1 : Fin 3) ∧
        (C A.left).shield = false ∧
        ZeroSignalThrough A C p
  | .live p =>
      SectorInteriorFollowers A C ∧
        OnlySectorBullet A C p (2 : Fin 3) ∧
        (C A.left).shield = true ∧
        ZeroSignalThrough A C p
  | .ret q =>
      SectorInteriorFollowers A C ∧
        0 < q ∧
        q < A.gap ∧
        SectorBulletFree A C ∧
        (C A.left).signalB = false ∧
        SignalZeroBefore A C q ∧
        (C (advance ring A.left q)).signalB = true

def sealedIncomingEdge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) : Fin n :=
  ring.leftNeighbor A.left

/-- Deterministic successor phase used by the File-3 executable checker. -/
def nextSectorPhase
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    SectorPhase → Fin n → SectorPhase
  | .ready, e =>
      if e = sealedIncomingEdge A then .dummy 0
      else if e = A.left then
        if A.gap = 1 then .ready else .live 1
      else .ready
  | .dummy p, e =>
      if e = advance ring A.left p then
        if p + 1 < A.gap then .dummy (p + 1)
        else if A.gap = 1 then .ready
        else .ret (A.gap - 1)
      else .dummy p
  | .live p, e =>
      if e = advance ring A.left p then
        if p + 1 < A.gap then .live (p + 1)
        else if A.gap = 1 then .ready
        else .ret (A.gap - 1)
      else .live p
  | .ret q, e =>
      if e = advance ring A.left (q - 1) then
        if q = 1 then .ready else .ret (q - 1)
      else .ret q

def PhaseTransition
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0)
    (ph : SectorPhase) (e : Fin n) (ph' : SectorPhase) : Prop :=
  ph' = nextSectorPhase A ph e

def phaseDebt (d : Nat) : SectorPhase → Nat
  | .ready => 0
  | .dummy p => 2 * d - p - 1
  | .live p => 2 * d - p - 1
  | .ret q => q

def liveHitDebt (d : Nat) : SectorPhase → Nat
  | .live p => d - p
  | _ => 0

/-- Named hypothesis for the corrected File-3 physical closure theorem.
The current-interior condition is carried by `PhaseHolds`. -/
def SealedStepSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase),
    PhaseHolds A C ph →
    ¬ EndpointDeleted A C →
    ∀ e : Fin n,
      EndpointDeleted A (stepE ring C e) ∨
        ∃ ph',
          PhaseHolds A (stepE ring C e) ph' ∧
          PhaseTransition A ph e ph'

/-! ## Two-leader product witness -/

structure TwoLeaderSealed
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n) where
  wrap : F.i = F.k
  aPhase : SectorPhase
  bPhase : SectorPhase
  hA : PhaseHolds F.A C aPhase
  hB : PhaseHolds F.B C bPhase
  alive : ¬ TaggedDeleted F C

/-! ## Endpoint deletion bookkeeping -/

theorem endpointDeletedA_tagged_twoLeader
    {n : Nat} {ring : DirectedRing n} {C0 C : Config n}
    (F : TripleFrame ring C0)
    (h : EndpointDeleted F.A C) :
    TaggedDeleted F C := by
  rcases h with hleft | hright
  · rw [F.A_left] at hleft
    exact .inl hleft
  · rw [F.A_right] at hright
    exact .inr (.inl hright)

theorem endpointDeletedB_tagged_twoLeader
    {n : Nat} {ring : DirectedRing n} {C0 C : Config n}
    (F : TripleFrame ring C0)
    (h : EndpointDeleted F.B C) :
    TaggedDeleted F C := by
  rcases h with hleft | hright
  · rw [F.B_left] at hleft
    exact .inr (.inl hleft)
  · rw [F.B_right] at hright
    exact .inr (.inr hright)

/-! ## Ring geometry for the four shared endpoint roles -/

theorem rightNeighbor_injective_twoLeader
    {n : Nat} (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

theorem rightNeighbor_leftNeighbor_twoLeader
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  show ((i.val + n - 1) % n + 1) % n = i.val
  have hn := ring.hn
  have hi := i.isLt
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 : (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - 1 + 1 = n by omega, Nat.mod_self, h0]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show i.val - 1 + 1 = i.val by omega]
    exact Nat.mod_eq_of_lt hi

theorem advance_succ_twoLeader
    {n : Nat} (ring : DirectedRing n) (i : Fin n) (q : Nat) :
    ring.rightNeighbor (advance ring i q) =
      advance ring i (q + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor advance
  dsimp only
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- The terminal A edge entering j is exactly the exterior incoming edge of B. -/
theorem twoLeader_enter_j_edge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    advance ring F.A.left (F.A.gap - 1) =
      ring.leftNeighbor F.B.left := by
  apply rightNeighbor_injective_twoLeader ring
  calc
    ring.rightNeighbor
        (advance ring F.A.left (F.A.gap - 1)) =
        advance ring F.A.left ((F.A.gap - 1) + 1) :=
      advance_succ_twoLeader ring F.A.left (F.A.gap - 1)
    _ = advance ring F.A.left F.A.gap := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt F.A.gap_pos)]
    _ = F.A.right := F.A.right_eq
    _ = F.j := F.A_right
    _ = F.B.left := F.B_left.symm
    _ = ring.rightNeighbor (ring.leftNeighbor F.B.left) :=
      (rightNeighbor_leftNeighbor_twoLeader ring F.B.left).symm

/-- The site leaving j as A's right endpoint is B's source site. -/
theorem twoLeader_leave_j_edge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    F.A.right = F.B.left := by
  exact F.A_right.trans F.B_left.symm

/-- Under i=k, the terminal B edge entering i is exactly the exterior
incoming edge of A. -/
theorem twoLeader_enter_i_edge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hwrap : F.i = F.k) :
    advance ring F.B.left (F.B.gap - 1) =
      ring.leftNeighbor F.A.left := by
  apply rightNeighbor_injective_twoLeader ring
  calc
    ring.rightNeighbor
        (advance ring F.B.left (F.B.gap - 1)) =
        advance ring F.B.left ((F.B.gap - 1) + 1) :=
      advance_succ_twoLeader ring F.B.left (F.B.gap - 1)
    _ = advance ring F.B.left F.B.gap := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt F.B.gap_pos)]
    _ = F.B.right := F.B.right_eq
    _ = F.k := F.B_right
    _ = F.i := hwrap.symm
    _ = F.A.left := F.A_left.symm
    _ = ring.rightNeighbor (ring.leftNeighbor F.A.left) :=
      (rightNeighbor_leftNeighbor_twoLeader ring F.A.left).symm

/-- Under i=k, the site leaving i as B's right endpoint is A's source site. -/
theorem twoLeader_leave_i_edge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hwrap : F.i = F.k) :
    F.B.right = F.A.left := by
  calc
    F.B.right = F.k := F.B_right
    _ = F.i := hwrap.symm
    _ = F.A.left := F.A_left.symm

/-! ## Adjacent-sector degeneracies -/

/-- If a=1, A's source edge is simultaneously its terminal edge and the
incoming edge of B. -/
theorem twoLeader_a_one_edge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (ha : F.a = 1) :
    advance ring F.A.left (F.A.gap - 1) = F.A.left ∧
      advance ring F.A.left (F.A.gap - 1) =
        ring.leftNeighbor F.B.left := by
  constructor
  · rw [F.A_gap, ha]
    simp
  · exact twoLeader_enter_j_edge F

/-- If b=1 and i=k, B's source edge is simultaneously its terminal edge and
the incoming edge of A. -/
theorem twoLeader_b_one_edge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (hwrap : F.i = F.k) (hb : F.b = 1) :
    advance ring F.B.left (F.B.gap - 1) = F.B.left ∧
      advance ring F.B.left (F.B.gap - 1) =
        ring.leftNeighbor F.A.left := by
  constructor
  · rw [F.B_gap, hb]
    simp
  · exact twoLeader_enter_i_edge F hwrap

/-- On a two-site wrapped frame the only positive complementary split is
a=b=1. -/
theorem twoLeader_n_two_gaps
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (hwrap : F.i = F.k) (hn : n = 2) :
    F.a = 1 ∧ F.b = 1 := by
  have ha0 : 0 < F.a := by
    rw [← F.A_gap]
    exact F.A.gap_pos
  have hb0 : 0 < F.b := by
    rw [← F.B_gap]
    exact F.B.gap_pos
  have hsum : F.a + F.b = n := by
    rcases F.span with hsame | hdistinct
    · exact hsame.2
    · exact False.elim (hdistinct.1 hwrap)
  omega

/-- Explicit n=2 edge-role package: both complementary sectors are
one-edge sectors on the actual two-site ring. -/
theorem twoLeader_n_two_edge_roles
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (hwrap : F.i = F.k) (hn : n = 2) :
    (advance ring F.A.left (F.A.gap - 1) = F.A.left ∧
      advance ring F.A.left (F.A.gap - 1) =
        ring.leftNeighbor F.B.left) ∧
    (advance ring F.B.left (F.B.gap - 1) = F.B.left ∧
      advance ring F.B.left (F.B.gap - 1) =
        ring.leftNeighbor F.A.left) := by
  have hgaps := twoLeader_n_two_gaps F hwrap hn
  exact
    ⟨twoLeader_a_one_edge F hgaps.1,
      twoLeader_b_one_edge F hwrap hgaps.2⟩

/-! ## Product closure -/

/-- Lemma 7 / audited i=k repair.

No cross-sector phase compatibility clause is required.  The successor is
split first on `TaggedDeleted`; on the surviving branch, the File-3 sealed
step is applied separately to A and B.  Any sector-endpoint deletion branch
would contradict the surviving tagged condition. -/
theorem twoLeaderSealed_step
    (hsealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (h : TwoLeaderSealed F C) (e : Fin n) :
    TaggedDeleted F (stepE ring C e) ∨
      ∃ h' : TwoLeaderSealed F (stepE ring C e), True := by
  let D := stepE ring C e
  by_cases htag : TaggedDeleted F D
  · exact .inl htag
  · have hAalive : ¬ EndpointDeleted F.A C := by
      intro hdel
      exact h.alive (endpointDeletedA_tagged_twoLeader F hdel)
    have hBalive : ¬ EndpointDeleted F.B C := by
      intro hdel
      exact h.alive (endpointDeletedB_tagged_twoLeader F hdel)
    rcases hsealed ring F.A C h.aPhase h.hA hAalive e with
      hdelA | ⟨aPhase', hA', _hAtr⟩
    · exact False.elim
        (htag (endpointDeletedA_tagged_twoLeader F hdelA))
    · rcases hsealed ring F.B C h.bPhase h.hB hBalive e with
        hdelB | ⟨bPhase', hB', _hBtr⟩
      · exact False.elim
          (htag (endpointDeletedB_tagged_twoLeader F hdelB))
      · refine .inr ⟨?_, True.intro⟩
        exact {
          wrap := h.wrap
          aPhase := aPhase'
          bPhase := bPhase'
          hA := hA'
          hB := hB'
          alive := htag
        }

#print axioms PPL.Convergence.LDLocal.endpointDeletedA_tagged_twoLeader
#print axioms PPL.Convergence.LDLocal.endpointDeletedB_tagged_twoLeader
#print axioms PPL.Convergence.LDLocal.rightNeighbor_injective_twoLeader
#print axioms PPL.Convergence.LDLocal.rightNeighbor_leftNeighbor_twoLeader
#print axioms PPL.Convergence.LDLocal.advance_succ_twoLeader
#print axioms PPL.Convergence.LDLocal.twoLeader_enter_j_edge
#print axioms PPL.Convergence.LDLocal.twoLeader_leave_j_edge
#print axioms PPL.Convergence.LDLocal.twoLeader_enter_i_edge
#print axioms PPL.Convergence.LDLocal.twoLeader_leave_i_edge
#print axioms PPL.Convergence.LDLocal.twoLeader_a_one_edge
#print axioms PPL.Convergence.LDLocal.twoLeader_b_one_edge
#print axioms PPL.Convergence.LDLocal.twoLeader_n_two_gaps
#print axioms PPL.Convergence.LDLocal.twoLeader_n_two_edge_roles
#print axioms PPL.Convergence.LDLocal.twoLeaderSealed_step

end PPL.Convergence.LDLocal
