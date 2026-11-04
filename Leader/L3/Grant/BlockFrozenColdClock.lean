import Leader.L3.Grant.BlockFrozenAmplification

/-!
G16 C.17, unlatched frozen cold clock.

Every frozen lease reached by the clamped reference is physically
representable. For every UNLATCHED reachable reference, this file
constructs a real cold carrier: protected BANK fields are copied
through actual Fin-clamped copyBank, every PACK role is inherited
from the buffered entrance, and all exterior agents have empty
BANK tokens and no grants. It also proves the exact one-step
physical/frozen four-field and success-latch comparison, and
records the RESET/recovery phase split.

OPEN: converting this one-step field/latch agreement into an
equality of stopped PHASE CREDIT needs a matching physical
grant/RESET terminal classifier and a local C.2 recovery observer.
No unproved Bellman inequality, cost, or G13 mass bound is claimed.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Every local lease fits in the physical compiled Fin range.
This is a predicate on a concrete clamped BANK state. -/
def GrantBlockFrozenColdLeaseBound
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ i : Fin ((compileAdvice q).b + 1),
    (S.fields i).2.2.2 < (compileAdvice q).bankLeaseCap + 1

/-- Every initial arbitrary-scratch clamped reference has
a physically representable lease in each protected slot.
Consumer: C.17 unlatched physical embedding. -/
theorem grantBlockFrozenColdLeaseBoundStart
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n) :
    GrantBlockFrozenColdLeaseBound q
      (GrantBankReference.bankLocalReferenceStart ring root C) := by
  intro i
  change
    (C (Counter.site ring root i.val)).lease.val <
      (compileAdvice q).bankLeaseCap + 1
  exact (C (Counter.site ring root i.val)).lease.isLt

/-- Every field next is either old or the output of actual
physical Fin clamp, including all four BANK coordinates. -/
private theorem grantBlockFrozenColdLeaseFieldStep
    {n q : Nat} (ring : DirectedRing n)
    (root edge : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbound : GrantBlockFrozenColdLeaseBound q S)
    (i : Fin ((compileAdvice q).b + 1)) :
    (GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root edge S i).2.2.2 <
        (compileAdvice q).bankLeaseCap + 1 := by
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  split
  · exact GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _
  split
  · exact GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _
  split
  · exact GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _
  split
  · exact GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _
  exact hbound i

/-- One local BANK step preserves physical representability,
including if that step first sets the success latch. -/
theorem grantBlockFrozenColdLeaseBoundStep
    {n q : Nat} (ring : DirectedRing n)
    (root edge : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbound : GrantBlockFrozenColdLeaseBound q S) :
    GrantBlockFrozenColdLeaseBound q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S edge) := by
  intro i
  by_cases hs : Counter.Support q ring root edge
  · cases hb : S.success with
    | true =>
        simpa [GrantBankReference.bankLocalReferenceStepClamped,
          hs, hb] using hbound i
    | false =>
        simpa [GrantBankReference.bankLocalReferenceStepClamped,
          hs, hb] using
          (grantBlockFrozenColdLeaseFieldStep
            ring root edge S hbound i)
  · simpa [GrantBankReference.bankLocalReferenceStepClamped,
      hs] using hbound i

/-- The Fin lease bound is an invariant of the actual
support-word clamped frozen process, not an assumption
about the elapsed scheduler word. -/
theorem grantBlockFrozenColdLeaseBoundWord
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (word : List (Fin n))
      (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      GrantBlockFrozenColdLeaseBound q S →
      GrantBlockFrozenColdLeaseBound q
        (GrantBankReference.bankLocalReferenceWordClamped
          ring root word S) := by
  intro word
  induction word with
  | nil =>
      intro S hbound
      exact hbound
  | cons edge tail ih =>
      intro S hbound
      exact ih
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge)
        (grantBlockFrozenColdLeaseBoundStep
          ring root edge S hbound)

/-!
The physical template's PACK word is retained everywhere. A site
is protected only when BOTH its PACK value is j <= b and it lies
at the actual root-relative site j. Other agents are blank,
even if they happen to carry a numerically protected PACK role.
-/

/-- Canonical complete full-Agent realization of the frozen
four-field array, with blank native/private exterior scratch. -/
noncomputable def grantBlockFrozenColdEmbedConfig
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Counter.Config q n :=
  fun i =>
    if h : (C i).pack.val ≤ (compileAdvice q).b ∧
        Counter.site ring root (C i).pack.val = i then
      copyBank
        { Agent.blank (compileAdvice q) with pack := (C i).pack }
        (GrantBankReference.bankLocalReferenceCell S
          ⟨(C i).pack.val, Nat.lt_succ_of_le h.1⟩)
    else
      { Agent.blank (compileAdvice q) with pack := (C i).pack }

/-- A field of a dependent if is the common value of both branches. -/
private theorem grantBlockFrozenColdDiteField {α β : Type}
    {P : Prop} [Decidable P] (f : α → β)
    {a : P → α} {b : ¬ P → α} {v : β}
    (ha : ∀ h, f (a h) = v) (hb : ∀ h, f (b h) = v) :
    f (dite P a b) = v := by
  by_cases h : P
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h

/-- The embedding preserves the physical PACK word, including the exterior. -/
theorem grantBlockFrozenColdEmbedPack
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (i : Fin n) :
    (grantBlockFrozenColdEmbedConfig ring C root S i).pack =
      (C i).pack := by
  exact grantBlockFrozenColdDiteField Agent.pack
    (fun _ => rfl) (fun _ => rfl)

/-- Every reconstructed physical Agent begins with grant=false. -/
theorem grantBlockFrozenColdEmbedNoGrants
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (i : Fin n) :
    (grantBlockFrozenColdEmbedConfig ring C root S i).grant =
      false := by
  exact grantBlockFrozenColdDiteField Agent.grant
    (fun _ => rfl) (fun _ => rfl)

/-- Exterior BANK tokens are blank, as required at an incoming seam. -/
theorem grantBlockFrozenColdEmbedOutsideEmpty
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (i : Fin n)
    (hout : ∀ j : Nat, j ≤ (compileAdvice q).b →
      i ≠ Counter.site ring root j) :
    (grantBlockFrozenColdEmbedConfig ring C root S i).tok =
      .E ∧
    (grantBlockFrozenColdEmbedConfig ring C root S i).grant =
      false := by
  have hno : ¬ ((C i).pack.val ≤ (compileAdvice q).b ∧
      Counter.site ring root (C i).pack.val = i) := by
    intro hh
    exact hout (C i).pack.val hh.1 hh.2.symm
  constructor
  · exact grantBlockFrozenColdDiteField Agent.tok
      (fun hh => absurd hh hno) (fun _ => rfl)
  · exact grantBlockFrozenColdEmbedNoGrants ring C root S i

/-- The copy's four fields equal the representable reference slot. -/
private theorem grantBlockFrozenColdCopyQuad
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (a : Agent (compileAdvice q))
    (hbound : GrantBlockFrozenColdLeaseBound q S) :
    GrantBankReference.bankAgentLeaseQuad
      (copyBank a
        (GrantBankReference.bankLocalReferenceCell S i)) =
      S.fields i := by
  have hl : (S.fields i).2.2.2 <
      (compileAdvice q).bankLeaseCap + 1 := hbound i
  simp [GrantBankReference.bankAgentLeaseQuad, copyBank,
    GrantBankReference.bankLocalReferenceCell, hl]

/-- The positive branch of a dependent if. -/
private theorem grantBlockFrozenColdDitePos {α β : Type}
    {P : Prop} [Decidable P] (f : α → β)
    {a : P → α} {b : ¬ P → α} {v : β}
    (hP : P) (ha : f (a hP) = v) :
    f (dite P a b) = v := by
  rw [dif_pos hP]; exact ha

/-- Exact four-field reconstruction for the physical support-step consumer. -/
theorem grantBlockFrozenColdEmbedFields
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (hc : Counter.Complete ring C root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbound : GrantBlockFrozenColdLeaseBound q S) :
    GrantBankReference.bankLocalReferenceFieldsAgree
      ring (grantBlockFrozenColdEmbedConfig ring C root S)
      root S := by
  intro j hj
  have hrole :
      (C (Counter.site ring root j)).pack.val = j :=
    hc j hj
  have hcheck :
      (C (Counter.site ring root j)).pack.val ≤
          (compileAdvice q).b ∧
      Counter.site ring root
          (C (Counter.site ring root j)).pack.val =
        Counter.site ring root j := by
    rw [hrole]
    exact ⟨hj, rfl⟩
  have hindex :
      (⟨(C (Counter.site ring root j)).pack.val,
        Nat.lt_succ_of_le hcheck.1⟩ :
        Fin ((compileAdvice q).b + 1)) =
      (⟨j, Nat.lt_succ_of_le hj⟩ :
        Fin ((compileAdvice q).b + 1)) :=
    Fin.ext hrole
  change
    GrantBankReference.bankAgentLeaseQuad
      (grantBlockFrozenColdEmbedConfig ring C root S
        (Counter.site ring root j)) =
      S.fields ⟨j, Nat.lt_succ_of_le hj⟩
  refine grantBlockFrozenColdDitePos
    GrantBankReference.bankAgentLeaseQuad hcheck ?_
  rw [grantBlockFrozenColdCopyQuad q S _ _ hbound, hindex]

/-- The embedding is an authentic Complete + GrantFree
Counter.ResetClockBankColdCarrier; no CLEAN scratch is assumed. -/
noncomputable def grantBlockFrozenColdEmbedCarrier
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (hc : Counter.Complete ring C root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    Counter.ResetClockBankColdCarrier (q := q) ring root := by
  refine ⟨grantBlockFrozenColdEmbedConfig ring C root S, ?_⟩
  constructor
  · intro j hj
    have hv := congrArg Fin.val
      (grantBlockFrozenColdEmbedPack ring C root S
        (Counter.site ring root j))
    rw [hv]
    exact hc j hj
  · exact grantBlockFrozenColdEmbedNoGrants ring C root S root

/-- Any representable unlatched reference is exactly the canonical seed. -/
theorem grantBlockFrozenColdEmbedSeed
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (hc : Counter.Complete ring C root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbound : GrantBlockFrozenColdLeaseBound q S)
    (hfalse : S.success = false) :
    GrantBankReference.bankLocalReferenceStart ring root
      (grantBlockFrozenColdEmbedCarrier
        ring C root hc S).val = S := by
  have hfields :=
    grantBlockFrozenColdEmbedFields ring C root hc S hbound
  cases S with
  | mk fields success =>
      cases success with
      | true =>
          cases hfalse
      | false =>
          have hf :
              (fun i : Fin ((compileAdvice q).b + 1) =>
                GrantBankReference.bankAgentLeaseQuad
                  ((grantBlockFrozenColdEmbedCarrier ring C
                    root hc
                    (⟨fields, false⟩ :
                      GrantBankReference.BankLocalReference
                        (compileAdvice q).b)).val
                    (Counter.site ring root i.val))) = fields := by
            funext i
            have hi : i.val ≤ (compileAdvice q).b := by
              have hl := i.isLt
              omega
            have heq := hfields i.val hi
            have hindex :
                (⟨i.val, Nat.lt_succ_of_le hi⟩ :
                  Fin ((compileAdvice q).b + 1)) = i := Fin.ext rfl
            rw [hindex] at heq
            exact heq
          change
            (⟨(fun i : Fin ((compileAdvice q).b + 1) =>
              GrantBankReference.bankAgentLeaseQuad
                ((grantBlockFrozenColdEmbedCarrier ring C root hc
                  (⟨fields, false⟩ :
                    GrantBankReference.BankLocalReference
                      (compileAdvice q).b)).val
                    (Counter.site ring root i.val))),
              false⟩ :
                GrantBankReference.BankLocalReference
                  (compileAdvice q).b) =
              ⟨fields, false⟩
          rw [hf]

/-! Good support geometry; G14 reads the full physical PACK. -/

/-- Any good OLD PACK pair stabilizes the actual physical role
word, hence is not a ResetClockBankDefectEntry. -/
private theorem grantBlockFrozenColdGoodNoDefect
    {n q : Nat} (ring : DirectedRing n)
    (D : Counter.Config q n) (root edge : Fin n)
    (hgood : goodPair (compileAdvice q).b
      (D edge).pack (D (ring.rightNeighbor edge)).pack = true) :
    ¬ Counter.ResetClockBankDefectEntry
      ring D root edge := by
  have hroles :
      (fun i : Fin n =>
        (((protocol q).step ring D edge) i).pack) =
      (fun i : Fin n => (D i).pack) := by
    calc
      _ = roleWordStep (compileAdvice q).b ring
          (fun i : Fin n => (D i).pack) edge :=
        role_step ring D edge
      _ = (fun i : Fin n => (D i).pack) :=
        roleWordStep_of_good (compileAdvice q).b ring
          (fun i : Fin n => (D i).pack) edge hgood
  have hstable : Counter.RoleStableEdge ring root D edge := by
    intro j hj
    exact congrArg
      (fun f : Fin n → Fin ((compileAdvice q).b + 2) =>
        f (Counter.site ring root j)) hroles
  intro hd
  rcases hd.2 with hb | hu
  · have hfalse : true = false := hgood.symm.trans hb
    cases hfalse
  · exact hu hstable

/-- The spatial buffer's support-good certificate is precisely
the Bool-valued original goodPair test, including both seams. -/
private theorem grantBlockFrozenColdBufferedGood
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (root : Fin n)
    (radius : Nat)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (edge : Fin n)
    (hs : Counter.Support (ceilLogTwo n) ring root edge) :
    goodPair (compileAdvice (ceilLogTwo n)).b
      (C edge).pack (C (ring.rightNeighbor edge)).pack =
      true := by
  have hzero := hbuffered.2.1 edge hs
  cases hg : goodPair (compileAdvice (ceilLogTwo n)).b
      (C edge).pack (C (ring.rightNeighbor edge)).pack with
  | true =>
      rfl
  | false =>
      have hbad : (1 : Nat) = 0 := by
        simpa [badRoleEdge, roleBadSet, Density.bit, hg]
          using hzero
      cases hbad

/-- The reconstructed carrier retains the buffered entrance's
good PACK pair on every support letter, including incoming-root. -/
theorem grantBlockFrozenColdEmbedGoodSupport
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice (ceilLogTwo n)).b)
    (edge : Fin n)
    (hs : Counter.Support (ceilLogTwo n) ring root edge) :
    goodPair (compileAdvice (ceilLogTwo n)).b
      ((grantBlockFrozenColdEmbedConfig ring C root S) edge).pack
      ((grantBlockFrozenColdEmbedConfig ring C root S)
        (ring.rightNeighbor edge)).pack = true := by
  rw [grantBlockFrozenColdEmbedPack ring C root S edge,
    grantBlockFrozenColdEmbedPack ring C root S
      (ring.rightNeighbor edge)]
  exact grantBlockFrozenColdBufferedGood ring C root radius
    hbuffered edge hs

/-- Every UNLATCHED frozen state reached from a buffered entrance
has an actual physical cold carrier with the same protected
reference, empty exterior BANK tokens and no grants anywhere.
All support pairs, especially the incoming predecessor, are good.

Consumer: the proposed state-uniform frozen C.3 Bellman argument.
There is no assumption of frozen CLEAN scratch. -/
theorem grantBlockFrozenColdReachedUnlatchedEmbed
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (word : List (Fin n))
    (hfalse :
      (GrantBankReference.bankLocalReferenceWordClamped
        ring root word
        (GrantBankReference.bankLocalReferenceStart
          ring root C)).success = false) :
    ∃ x : Counter.ResetClockBankColdCarrier
        (q := ceilLogTwo n) ring root,
      GrantBankReference.bankLocalReferenceStart ring root x.val =
        GrantBankReference.bankLocalReferenceWordClamped
          ring root word
          (GrantBankReference.bankLocalReferenceStart ring root C) ∧
      (∀ i : Fin n, (x.val i).grant = false) ∧
      (∀ i : Fin n,
        (∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
          i ≠ Counter.site ring root j) →
        (x.val i).tok = .E) ∧
      (∀ edge : Fin n,
        Counter.Support (ceilLogTwo n) ring root edge →
        goodPair (compileAdvice (ceilLogTwo n)).b
          (x.val edge).pack
          (x.val (ring.rightNeighbor edge)).pack = true) := by
  have hrepresentable :=
    grantBlockFrozenColdLeaseBoundWord ring root word
      (GrantBankReference.bankLocalReferenceStart ring root C)
      (grantBlockFrozenColdLeaseBoundStart ring C root)
  refine ⟨grantBlockFrozenColdEmbedCarrier ring C root
      hbuffered.1
      (GrantBankReference.bankLocalReferenceWordClamped
        ring root word
        (GrantBankReference.bankLocalReferenceStart ring root C)),
    ?_, ?_, ?_, ?_⟩
  · exact grantBlockFrozenColdEmbedSeed ring C root
      hbuffered.1 _ hrepresentable hfalse
  · intro i
    exact grantBlockFrozenColdEmbedNoGrants ring C root _ i
  · intro i hout
    exact (grantBlockFrozenColdEmbedOutsideEmpty
      ring C root _ i hout).1
  · intro edge hs
    exact grantBlockFrozenColdEmbedGoodSupport
      ring C root radius hbuffered _ edge hs

/-! Local cold, RESET/recovery, and absorbing-success phases. -/

inductive GrantBlockFrozenColdLocalPhase where
  | cold | recovery | success
  deriving DecidableEq

/-- The phase tag reads only local BANK fields and the success
latch. A RESET record starts recovery, not a clean trial. -/
noncomputable def grantBlockFrozenColdLocalPhase
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : GrantBlockFrozenColdLocalPhase :=
  if S.success then .success
  else if (S.fields (⟨0, by omega⟩ :
      Fin ((compileAdvice q).b + 1))).1 = .RESET then
    .recovery
  else .cold

/-- The zero-root RESET branch is an actual recovery handoff. -/
theorem grantBlockFrozenColdLocalResetPhase
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfalse : S.success = false)
    (hreset :
      (S.fields (⟨0, by omega⟩ :
        Fin ((compileAdvice q).b + 1))).1 = .RESET) :
    grantBlockFrozenColdLocalPhase q S = .recovery := by
  have hindex :
      (0 : Fin ((compileAdvice q).b + 1)) =
      (⟨0, by omega⟩ : Fin ((compileAdvice q).b + 1)) := Fin.ext rfl
  have hroot :
      (S.fields (0 : Fin ((compileAdvice q).b + 1))).1 =
        .RESET := by
    rw [hindex]
    exact hreset
  simp [grantBlockFrozenColdLocalPhase, hfalse, hroot]

/-- A non-RESET unlatched local record remains in the cold phase. -/
theorem grantBlockFrozenColdLocalActivePhase
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfalse : S.success = false)
    (hreset :
      (S.fields (⟨0, by omega⟩ :
        Fin ((compileAdvice q).b + 1))).1 ≠ .RESET) :
    grantBlockFrozenColdLocalPhase q S = .cold := by
  have hindex :
      (0 : Fin ((compileAdvice q).b + 1)) =
      (⟨0, by omega⟩ : Fin ((compileAdvice q).b + 1)) := Fin.ext rfl
  have hroot :
      (S.fields (0 : Fin ((compileAdvice q).b + 1))).1 ≠
        .RESET := by
    rw [hindex]
    exact hreset
  simp [grantBlockFrozenColdLocalPhase, hfalse, hroot]

theorem grantBlockFrozenColdLocalSuccessPhase
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hwin : S.success = true) :
    grantBlockFrozenColdLocalPhase q S = .success := by
  simp [grantBlockFrozenColdLocalPhase, hwin]

/-- The local RESET phase matches the existing real
Counter.resetClockBankColdStart zero-time recovery handoff.
Consumer: the future local C.2 renewal interface. -/
theorem grantBlockFrozenColdEmbedResetHandoff
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (hc : Counter.Complete ring C root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbound : GrantBlockFrozenColdLeaseBound q S)
    (hreset :
      (S.fields (⟨0, by omega⟩ :
        Fin ((compileAdvice q).b + 1))).1 = .RESET) :
    Counter.resetClockBankColdRecoveryCut ring root
      (Counter.resetClockBankColdStart ring root
        (grantBlockFrozenColdEmbedCarrier ring C root hc S)) := by
  have hfields := grantBlockFrozenColdEmbedFields
    ring C root hc S hbound
  have hmode := congrArg
    (fun p : Mode × Bool × BTok × Nat => p.1)
    (hfields 0 (by omega))
  change
    ((grantBlockFrozenColdEmbedCarrier ring C root hc S).val
      root).mode =
      (S.fields (⟨0, by omega⟩ :
        Fin ((compileAdvice q).b + 1))).1 at hmode
  exact Counter.resetClockBankColdStartReset ring root
    (grantBlockFrozenColdEmbedCarrier ring C root hc S)
    (hmode.trans hreset)

/-- When the root is not RESET, the authentic cold start
is an active cold carrier rather than a renewal handoff.
Consumer: the C.3 nonterminal first-phase potential. -/
theorem grantBlockFrozenColdEmbedActiveStart
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (hc : Counter.Complete ring C root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbound : GrantBlockFrozenColdLeaseBound q S)
    (hactive :
      (S.fields (⟨0, by omega⟩ :
        Fin ((compileAdvice q).b + 1))).1 ≠ .RESET) :
    ∃ x : Counter.ResetClockBankColdCarrier (q := q) ring root,
      Counter.resetClockBankColdStart ring root
        (grantBlockFrozenColdEmbedCarrier ring C root hc S) =
          .inl x := by
  have hfields := grantBlockFrozenColdEmbedFields
    ring C root hc S hbound
  have hmode := congrArg
    (fun p : Mode × Bool × BTok × Nat => p.1)
    (hfields 0 (by omega))
  change
    ((grantBlockFrozenColdEmbedCarrier ring C root hc S).val
      root).mode =
      (S.fields (⟨0, by omega⟩ :
        Fin ((compileAdvice q).b + 1))).1 at hmode
  have hnot :
      ((grantBlockFrozenColdEmbedCarrier ring C root hc S).val
        root).mode ≠ .RESET := by
    intro hh
    exact hactive (hmode.symm.trans hh)
  unfold Counter.resetClockBankColdStart
    Counter.resetClockBankColdLift
  simp only [dif_neg hnot]
  exact ⟨_, rfl⟩

/-! One-step physical/frozen field and latch projection. -/

/-- Exact one-edge projection from the canonical buffered carrier. -/
theorem grantBlockFrozenColdEmbedOneStepFields
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice (ceilLogTwo n)).b)
    (hbound : GrantBlockFrozenColdLeaseBound
      (ceilLogTwo n) S)
    (hfalse : S.success = false)
    (edge : Fin n) :
    ¬ Counter.ResetClockBankDefectEntry ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val root edge ∧
    GrantBankReference.bankLocalReferenceFieldsAgree ring
      ((protocol (ceilLogTwo n)).step ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val edge) root
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S edge) ∧
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root S edge).success =
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val edge := by
  have hrepr :
      (grantBlockFrozenColdEmbedCarrier ring C root
        hbuffered.1 S).val =
      grantBlockFrozenColdEmbedConfig ring C root S := rfl
  have hno :
      ¬ Counter.ResetClockBankDefectEntry ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val root edge := by
    by_cases hs : Counter.Support (ceilLogTwo n) ring root edge
    · apply grantBlockFrozenColdGoodNoDefect ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val root edge
      rw [hrepr]
      exact grantBlockFrozenColdEmbedGoodSupport
        ring C root radius hbuffered S edge hs
    · intro hd
      exact hs hd.1
  have hfields :
      GrantBankReference.bankLocalReferenceFieldsAgree ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val root S := by
    rw [hrepr]
    exact grantBlockFrozenColdEmbedFields ring C root
      hbuffered.1 S hbound
  have hstep := GrantBankReference.bankLocalReferenceSupportStep
    ring
    (grantBlockFrozenColdEmbedCarrier ring C root
      hbuffered.1 S).val
    root edge S hsp
    (grantBlockFrozenColdEmbedCarrier ring C root
      hbuffered.1 S).property.1
    (grantBlockFrozenColdEmbedCarrier ring C root
      hbuffered.1 S).property.2
    hfields hfalse hno
  exact ⟨hno, hstep.1, hstep.2.2⟩

end L3
#print axioms L3.grantBlockFrozenColdLeaseBoundStart
#print axioms L3.grantBlockFrozenColdLeaseBoundStep
#print axioms L3.grantBlockFrozenColdLeaseBoundWord
#print axioms L3.grantBlockFrozenColdEmbedPack
#print axioms L3.grantBlockFrozenColdEmbedNoGrants
#print axioms L3.grantBlockFrozenColdEmbedOutsideEmpty
#print axioms L3.grantBlockFrozenColdEmbedFields
#print axioms L3.grantBlockFrozenColdEmbedSeed
#print axioms L3.grantBlockFrozenColdEmbedGoodSupport
#print axioms L3.grantBlockFrozenColdReachedUnlatchedEmbed
#print axioms L3.grantBlockFrozenColdLocalResetPhase
#print axioms L3.grantBlockFrozenColdLocalActivePhase
#print axioms L3.grantBlockFrozenColdLocalSuccessPhase
#print axioms L3.grantBlockFrozenColdEmbedResetHandoff
#print axioms L3.grantBlockFrozenColdEmbedActiveStart
#print axioms L3.grantBlockFrozenColdEmbedOneStepFields
