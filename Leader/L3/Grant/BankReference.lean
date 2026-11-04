import Leader.L3.Headline.GrantClock
import Leader.L3.Bank.PairNonroot

/-!
BANK boundary reference maps and the first obstruction to
the proposed unrestricted support-edge congruence.

All statements below use the literal
Counter.resetBankOld / bankPair owner.
-/

namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-- Four BANK coordinates, with the lease retained. -/
def bankCellLeaseQuad (z : BankCell) :
    Mode × Bool × BTok × Nat :=
  (z.mode, z.bit, z.tok, z.lease)

def bankAgentLeaseQuad {c : Compiled} (a : Agent c) :
    Mode × Bool × BTok × Nat :=
  (a.mode, a.bit, a.tok, a.lease.val)

/-- The incoming-root map, for a grant-free old root. The
protected role, bit and grant are unchanged; the token is
emptied, and waiting leases count down. -/
def incomingRootBankMap (y : BankCell) : BankCell :=
  if y.mode == .ARMED then
    { y with mode := .RESET, tok := .E, lease := 0 }
  else if isWaitMode y.mode then
    if 1 < y.lease then
      { y with tok := .E, lease := y.lease - 1 }
    else
      { y with mode := .RESET, tok := .E, lease := 0 }
  else
    { y with tok := .E }

/-- The top-site source loses its waiting mode and lease; an
old IR is erased, while every other token is retained. -/
def topBoundaryBankMap (x : BankCell) : BankCell :=
  { role := x.role, mode := .RESET, bit := x.bit,
    tok := (if x.tok == .IR then .E else x.tok),
    lease := 0, grant := x.grant }

/-- A good incoming-root PACK source has post-role zero. -/
private theorem incomingRootPostRole
    (x y : BankCell) (b : Nat)
    (hx : x.role = b ∨ x.role = b + 1)
    (hy : y.role = 0) :
    packNext x.role y.role b = 0 := by
  have hnotlt : ¬ x.role < b := by
    rcases hx with h | h <;> omega
  simp [packNext, hnotlt, hy]

/-- Literal BANK pair, incoming-root direction.
Even the entire protected BANK cell is a function of y alone,
not just its four-coordinate view. -/
private theorem incomingRootBankSingle
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hb : 0 < b)
    (hx : x.role = b ∨ x.role = b + 1)
    (hy : y.role = 0) (hg : y.grant = false) :
    (bankPair x y (packNext x.role y.role b) b theta).2 =
      incomingRootBankMap y := by
  have hpost := incomingRootPostRole x y b hx hy
  have hxne : x.role ≠ 0 := by
    rcases hx with h | h <;> omega
  have hxge : ¬ x.role < b := by
    rcases hx with h | h <;> omega
  have hbunit : 1 ≤ b := by omega
  have hb0 : b ≠ 0 := by omega
  rw [hpost]
  rcases hx with hrole | hrole
  · cases hmode : y.mode <;>
      by_cases hlease : 1 < y.lease <;>
      simp [bankPair, incomingRootBankMap,
        hrole, hy, hg, hxne, hxge,
        hbunit, hb0, hmode, hlease, isWaitMode] <;>
        (repeat' split) <;> first | rfl | (simp_all [Id.run, isWaitMode]) | omega
  · cases hmode : y.mode <;>
      by_cases hlease : 1 < y.lease <;>
      simp [bankPair, incomingRootBankMap,
        hrole, hy, hg, hxne, hxge,
        hbunit, hb0, hmode, hlease, isWaitMode] <;>
        (repeat' split) <;> first | rfl | (simp_all [Id.run, isWaitMode]) | omega

/-- Item (1): either allowed exterior source yields exactly the
same protected responder, including role and grant. -/
theorem incomingRootBankOutputLocal
    (x u y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hb : 0 < b)
    (hx : x.role = b ∨ x.role = b + 1)
    (hu : u.role = b ∨ u.role = b + 1)
    (hy : y.role = 0) (hg : y.grant = false) :
    (bankPair x y (packNext x.role y.role b) b theta).2 =
      incomingRootBankMap y ∧
    (bankPair u y (packNext u.role y.role b) b theta).2 =
      incomingRootBankMap y := by
  exact ⟨incomingRootBankSingle x y b theta hb hx hy hg,
    incomingRootBankSingle u y b theta hb hu hy hg⟩

/-- Item (1), at Counter.resetBankOld's literal Agent inputs.
No assumption on the two exterior agents' private BANK fields. -/
theorem incomingRootBankOutputAgents {c : Compiled}
    (x u y : Agent c)
    (hx : x.pack.val = c.b ∨ x.pack.val = c.b + 1)
    (hu : u.pack.val = c.b ∨ u.pack.val = c.b + 1)
    (hy : y.pack.val = 0)
    (hg : y.grant = false) :
    (Counter.resetBankOld x y).2 =
      incomingRootBankMap (bankCell y y.pack.val) ∧
    (Counter.resetBankOld u y).2 =
      incomingRootBankMap (bankCell y y.pack.val) := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  exact incomingRootBankOutputLocal
    (bankCell x x.pack.val) (bankCell u u.pack.val)
    (bankCell y y.pack.val) c.b c.theta hb hx hu hy hg

/-- A good top-boundary PACK edge does not change the responder
role, whether the exterior responder is zero or b+1. -/
private theorem topBoundaryPostRole
    (x y : BankCell) (b : Nat)
    (hx : x.role = b)
    (hy : y.role = 0 ∨ y.role = b + 1) :
    packNext x.role y.role b = y.role := by
  rcases hy with h | h
  · rw [hx, h]
    simp [packNext]
  · rw [hx, h]
    simp [packNext]

/-- Literal BANK pair, top-boundary direction. -/
private theorem topBoundaryBankSingle
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hb : 0 < b) (hx : x.role = b)
    (hy : y.role = 0 ∨ y.role = b + 1) :
    (bankPair x y (packNext x.role y.role b) b theta).1 =
      topBoundaryBankMap x := by
  have hpost := topBoundaryPostRole x y b hx hy
  have hxne : x.role ≠ 0 := by omega
  have hxge : ¬ x.role < b := by omega
  have hbunit : 1 ≤ b := by omega
  have hb0 : b ≠ 0 := by omega
  rw [hpost]
  rcases hy with hrole | hrole
  · by_cases ht : x.tok = .IR
    · simp [bankPair, topBoundaryBankMap, hx, hrole,
        hxne, hxge, hbunit, hb0, ht] <;>
        (repeat' split) <;> first | rfl | (simp_all [Id.run, isWaitMode]) | omega
    · simp [bankPair, topBoundaryBankMap, hx, hrole,
        hxne, hxge, hbunit, hb0, ht] <;>
        (repeat' split) <;> first | rfl | (simp_all [Id.run, isWaitMode]) | omega
  · by_cases ht : x.tok = .IR
    · simp [bankPair, topBoundaryBankMap, hx, hrole,
        hxne, hxge, hbunit, hb0, ht] <;>
        (repeat' split) <;> first | rfl | (simp_all [Id.run, isWaitMode]) | omega
    · simp [bankPair, topBoundaryBankMap, hx, hrole,
        hxne, hxge, hbunit, hb0, ht] <;>
        (repeat' split) <;> first | rfl | (simp_all [Id.run, isWaitMode]) | omega

/-- Item (2): either legal exterior responder yields exactly
the same protected top-site source BANK cell. -/
theorem topBoundaryBankOutputLocal
    (x y v : BankCell) (b : Nat) (theta : Nat → Bool)
    (hb : 0 < b)
    (hx : x.role = b)
    (hy : y.role = 0 ∨ y.role = b + 1)
    (hv : v.role = 0 ∨ v.role = b + 1) :
    (bankPair x y (packNext x.role y.role b) b theta).1 =
      topBoundaryBankMap x ∧
    (bankPair x v (packNext x.role v.role b) b theta).1 =
      topBoundaryBankMap x := by
  exact ⟨topBoundaryBankSingle x y b theta hb hx hy,
    topBoundaryBankSingle x v b theta hb hx hv⟩

/-- Item (2), lifted to the actual OLD Agent BANK cells. -/
theorem topBoundaryBankOutputAgents {c : Compiled}
    (x y v : Agent c)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0 ∨ y.pack.val = c.b + 1)
    (hv : v.pack.val = 0 ∨ v.pack.val = c.b + 1) :
    (Counter.resetBankOld x y).1 =
      topBoundaryBankMap (bankCell x x.pack.val) ∧
    (Counter.resetBankOld x v).1 =
      topBoundaryBankMap (bankCell x x.pack.val) := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  exact topBoundaryBankOutputLocal
    (bankCell x x.pack.val) (bankCell y y.pack.val)
    (bankCell v v.pack.val) c.b c.theta hb hx hy hv

/-- Item (3)'s proposed strengthened projection. Completeness
of the role word is a separate premise, as in Counter.Complete.
No claim of one-step closure is made here. -/
def BankLeaseView {n q : Nat}
    (ring : DirectedRing n) (C F : Counter.Config q n)
    (root : Fin n) : Prop :=
  ∀ j : Nat, j ≤ (compileAdvice q).b →
    bankAgentLeaseQuad (C (Counter.site ring root j)) =
      bankAgentLeaseQuad (F (Counter.site ring root j))

/-!
STOP at item (3): Counter.Complete constrains the root and digits
zero through b, but NOT the incoming-root predecessor. Support
contains that incoming edge, irrespective of the predecessor's
PACK role. A role less than b changes the root's post-role, hence
BANK changed=true and RESET/0 rather than a waiting countdown.

The following fully concrete owner-row witness uses b=18 (as in
the q=80 spatial example) and two legal exterior PACK roles.
It is not an assertion that Counter.Complete includes the exterior.
-/

private def incomingBoundaryRootRecord : BankCell :=
  { role := 0, mode := .RWAIT, bit := false, tok := .E,
    lease := 2, grant := false }

private def incomingBoundaryGoodExterior : BankCell :=
  { role := 19, mode := .RESET, bit := false, tok := .E,
    lease := 0, grant := false }

private def incomingBoundaryBadExterior : BankCell :=
  { role := 0, mode := .RESET, bit := false, tok := .E,
    lease := 0, grant := false }

/-- Concrete discrepancy: the protected root outputs differ
on two incoming edges whose protected old records agree. -/
theorem incomingBoundaryRoleDefectWitness :
    (bankPair incomingBoundaryGoodExterior incomingBoundaryRootRecord
      (packNext incomingBoundaryGoodExterior.role
        incomingBoundaryRootRecord.role 18)
      18 (fun _ => false)).2.mode = .RWAIT ∧
    (bankPair incomingBoundaryGoodExterior incomingBoundaryRootRecord
      (packNext incomingBoundaryGoodExterior.role
        incomingBoundaryRootRecord.role 18)
      18 (fun _ => false)).2.lease = 1 ∧
    (bankPair incomingBoundaryBadExterior incomingBoundaryRootRecord
      (packNext incomingBoundaryBadExterior.role
        incomingBoundaryRootRecord.role 18)
      18 (fun _ => false)).2.mode = .RESET ∧
    (bankPair incomingBoundaryBadExterior incomingBoundaryRootRecord
      (packNext incomingBoundaryBadExterior.role
        incomingBoundaryRootRecord.role 18)
      18 (fun _ => false)).2.lease = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-!
The proposed step congruence from BankLeaseView, two Complete
hypotheses, and two GrantFree hypotheses is FALSE without an
additional good-role / no-defect assumption on the incoming
boundary edge. The obstruction occurs before any possible
need for the four-field analogue of resetPhysicalEdgeBankTrip.
The supporting lease-copy code is Base.lean:55-64 and the BANK
selection is Base.lean:470-483. A corrected physical induction
would additionally need those rows lifted from bankPair to
Protocol.transition, just as Counter.resetPhysicalEdgeBankTrip
already lifts the three-field projection.

No false congruence theorem is declared here.
-/

end GrantBankReference
end L3


namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-!
The literal four-field physical BANK frame and a
conditional one-edge congruence.

We stop before asserting the
unconditional bankLeaseViewStep theorem: the still-missing
non-root-grant-insensitivity of the internal bankPair output
must be proved before the selected-pair compatibility premise
can be discharged from BankLeaseView alone.
-/

/-- The triple and the lease equality together determine the
four-field private BANK projection of a real Agent. -/
private theorem bankQuadOfTripAndLease {c : Compiled}
    (x y : Agent c)
    (htrip : Counter.resetAgentBankTrip x =
      Counter.resetAgentBankTrip y)
    (hlease : x.lease = y.lease) :
    bankAgentLeaseQuad x = bankAgentLeaseQuad y := by
  have hm : x.mode = y.mode :=
    congrArg (fun z : Mode × Bool × BTok => z.1) htrip
  have hb : x.bit = y.bit :=
    congrArg (fun z : Mode × Bool × BTok => z.2.1) htrip
  have ht : x.tok = y.tok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip
  change (x.mode, x.bit, x.tok, x.lease.val) =
    (y.mode, y.bit, y.tok, y.lease.val)
  rw [hm, hb, ht, hlease]

/-- CopyBank owns all four fields: its four-field output does
not depend on any preexisting non-BANK field of the target. -/
private theorem bankCopyQuadIndependent {c : Compiled}
    (x y : Agent c) (z : BankCell) :
    bankAgentLeaseQuad (copyBank x z) =
      bankAgentLeaseQuad (copyBank y z) := by
  rfl

/-- Actual selected physical edge, four BANK fields.
This joins Counter.resetPhysicalEdgeBankTrip (mode/bit/tok)
to Counter.resetClockPhysicalEdgeLeasePair (the Fin lease);
there is no assumption that every arbitrary BankCell lease
is in the compiled range. Both right sides use the literal
copyBank clamp and hence remain valid even off the cap. -/
theorem bankLeasePhysicalEdgeQuad {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hsp : (compileAdvice q).useSmall = false) :
    bankAgentLeaseQuad (((protocol q).step ring C e) e) =
      bankAgentLeaseQuad
        (copyBank (C e)
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).1) ∧
    bankAgentLeaseQuad
      (((protocol q).step ring C e)
        (ring.rightNeighbor e)) =
      bankAgentLeaseQuad
        (copyBank (C (ring.rightNeighbor e))
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).2) := by
  have ht := Counter.resetPhysicalEdgeBankTrip ring C e hne hsp
  have hl := Counter.resetClockPhysicalEdgeLeasePair ring C e hne hsp
  constructor
  · have hcopy :
        Counter.resetAgentBankTrip
          (copyBank (C e)
            (Counter.resetBankOld
              (C e) (C (ring.rightNeighbor e))).1) =
        Counter.resetCellBankTrip
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).1 := by
      rfl
    exact bankQuadOfTripAndLease _ _
      (ht.1.trans hcopy.symm) hl.1
  · have hcopy :
        Counter.resetAgentBankTrip
          (copyBank (C (ring.rightNeighbor e))
            (Counter.resetBankOld
              (C e) (C (ring.rightNeighbor e))).2) =
        Counter.resetCellBankTrip
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).2 := by
      rfl
    exact bankQuadOfTripAndLease _ _
      (ht.2.trans hcopy.symm) hl.2

/-- The lease-inclusive view frames on a service not in S_r.
The existing full-Agent outside-frame theorem handles the
fourth field just as it handles the first three. -/
theorem bankLeaseOutsideSupportedFrame {n q : Nat}
    (ring : DirectedRing n)
    (C : Counter.Config q n) (root e : Fin n)
    (hout : ¬ Counter.Support q ring root e) :
    BankLeaseView ring ((protocol q).step ring C e) C root := by
  intro j hj
  have hf := Counter.outside_frame ring C root e
    (HeadlineGrantClock.outsideOfNotSupported ring root e hout)
    j hj
  exact congrArg
    (fun a : Agent (compileAdvice q) => bankAgentLeaseQuad a) hf

/-- On a supported non-defect edge, both the literal OLD PACK
pair and the entire protected role word are good. -/
theorem bankLeaseNoDefectGuard {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (hs : Counter.Support q ring root e)
    (hno : ¬ Counter.ResetClockBankDefectEntry ring C root e) :
    goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true ∧
    Counter.RoleStableEdge ring root C e := by
  constructor
  · cases hgood : goodPair (compileAdvice q).b
        (C e).pack (C (ring.rightNeighbor e)).pack with
    | true => rfl
    | false =>
        exact False.elim (hno ⟨hs, Or.inl hgood⟩)
  · by_cases hstable : Counter.RoleStableEdge ring root C e
    · exact hstable
    · exact False.elim (hno ⟨hs, Or.inr hstable⟩)

/-- Completeness of the protected role interval is preserved
by any supported edge that is not a recorded BANK defect. -/
theorem bankLeaseCompleteNoDefect {n q : Nat}
    (ring : DirectedRing n)
    (C : Counter.Config q n)
    (root e : Fin n)
    (hc : Counter.Complete ring C root)
    (hs : Counter.Support q ring root e)
    (hno : ¬ Counter.ResetClockBankDefectEntry ring C root e) :
    Counter.Complete ring ((protocol q).step ring C e) root := by
  have hstable := (bankLeaseNoDefectGuard ring C root e hs hno).2
  intro j hj
  have hsite := hstable j hj
  rw [hsite]
  exact hc j hj

/-- A complete role interval has at least two different sites.
This supplies the distinct-endpoint premise for the genuine
physical BANK projection without adding an extra ring axiom. -/
theorem bankLeaseCompleteTwoSites {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (hc : Counter.Complete ring C root) :
    2 ≤ n := by
  by_cases hn : 2 ≤ n
  · exact hn
  · have hone : n = 1 := by
      have hpos := ring.hn
      omega
    have hb : 1 ≤ (compileAdvice q).b := by
      change 1 ≤ (compileAdvice q).s + 11
      omega
    have hzero : (C root).pack.val = 0 := by
      simpa only [Counter.site] using hc 0 (by omega)
    have honeRole : (C (ring.rightNeighbor root)).pack.val = 1 := by
      have h := hc 1 hb
      change (C (ring.rightNeighbor root)).pack.val = 1 at h
      exact h
    have hsame : ring.rightNeighbor root = root := by
      apply Fin.ext
      change (root.val + 1) % n = root.val
      have hroot : root.val = 0 := by
        have hlt := root.isLt
        omega
      simp [hone, hroot]
    rw [hsame] at honeRole
    omega

/-- The complete selected physical frame: if both literal
BANK-pair copied four-field outputs are equal, the real
post-edge interval view is equal. No assertion about private
grant bits is inserted by this conditional lemma. -/
theorem bankLeaseSelectedViewOfOwnerQuads {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (C F : Counter.Config q n) (root e : Fin n)
    (hview : BankLeaseView ring C F root)
    (hleft :
      bankAgentLeaseQuad
        (copyBank (C e)
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).1) =
      bankAgentLeaseQuad
        (copyBank (F e)
          (Counter.resetBankOld
            (F e) (F (ring.rightNeighbor e))).1))
    (hright :
      bankAgentLeaseQuad
        (copyBank (C (ring.rightNeighbor e))
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).2) =
      bankAgentLeaseQuad
        (copyBank (F (ring.rightNeighbor e))
          (Counter.resetBankOld
            (F e) (F (ring.rightNeighbor e))).2)) :
    BankLeaseView ring
      ((protocol q).step ring C e)
      ((protocol q).step ring F e) root := by
  have hne := HeadlineGrantClock.physicalNeighborDistinct ring hn e
  have hC := bankLeasePhysicalEdgeQuad ring C e hne hsp
  have hF := bankLeasePhysicalEdgeQuad ring F e hne hsp
  intro j hj
  by_cases hx : Counter.site ring root j = e
  · have hselected :
        bankAgentLeaseQuad (((protocol q).step ring C e) e) =
          bankAgentLeaseQuad (((protocol q).step ring F e) e) :=
      hC.1.trans (hleft.trans hF.1.symm)
    simpa only [hx] using hselected
  · by_cases hy :
        Counter.site ring root j = ring.rightNeighbor e
    · have hselected :
          bankAgentLeaseQuad
            (((protocol q).step ring C e)
              (ring.rightNeighbor e)) =
            bankAgentLeaseQuad
              (((protocol q).step ring F e)
                (ring.rightNeighbor e)) :=
        hC.2.trans (hright.trans hF.2.symm)
      simpa only [hy] using hselected
    · have hfC := Counter.step_frame ring C e
        (Counter.site ring root j) hx hy
      have hfF := Counter.step_frame ring F e
        (Counter.site ring root j) hx hy
      simpa only [hfC, hfF] using hview j hj

/-- Exact sufficient selected-pair compatibility; deliberately
stronger than the desired four-field relation. This is a
conditional certificate, not the requested bankLeaseViewStep. -/
theorem bankLeaseViewStepOfPairCompatibility {n q : Nat}
    (ring : DirectedRing n)
    (hsp : (compileAdvice q).useSmall = false)
    (C F : Counter.Config q n) (root e : Fin n)
    (hview : BankLeaseView ring C F root)
    (hc : Counter.Complete ring C root)
    (hf : Counter.Complete ring F root)
    (hs : Counter.Support q ring root e)
    (hnoC : ¬ Counter.ResetClockBankDefectEntry ring C root e)
    (hnoF : ¬ Counter.ResetClockBankDefectEntry ring F root e)
    (hpair :
      Counter.resetBankOld (C e) (C (ring.rightNeighbor e)) =
      Counter.resetBankOld (F e) (F (ring.rightNeighbor e))) :
    BankLeaseView ring
      ((protocol q).step ring C e)
      ((protocol q).step ring F e) root ∧
    Counter.Complete ring ((protocol q).step ring C e) root ∧
    Counter.Complete ring ((protocol q).step ring F e) root := by
  have hleft :
      bankAgentLeaseQuad
        (copyBank (C e)
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).1) =
      bankAgentLeaseQuad
        (copyBank (F e)
          (Counter.resetBankOld
            (F e) (F (ring.rightNeighbor e))).1) := by
    rw [hpair]
    exact bankCopyQuadIndependent (C e) (F e)
      (Counter.resetBankOld
        (F e) (F (ring.rightNeighbor e))).1
  have hright :
      bankAgentLeaseQuad
        (copyBank (C (ring.rightNeighbor e))
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).2) =
      bankAgentLeaseQuad
        (copyBank (F (ring.rightNeighbor e))
          (Counter.resetBankOld
            (F e) (F (ring.rightNeighbor e))).2) := by
    rw [hpair]
    exact bankCopyQuadIndependent
      (C (ring.rightNeighbor e)) (F (ring.rightNeighbor e))
      (Counter.resetBankOld
        (F e) (F (ring.rightNeighbor e))).2
  exact ⟨bankLeaseSelectedViewOfOwnerQuads ring
      (bankLeaseCompleteTwoSites ring C root hc)
      hsp C F root e hview hleft hright,
    bankLeaseCompleteNoDefect ring C root e hc hs hnoC,
    bankLeaseCompleteNoDefect ring F root e hf hs hnoF⟩

/-- Forgetting the lease gives exactly the three-field view
requested by the consumers of HeadlineGrantClock. -/
theorem bankLeaseViewForgetsLease {n q : Nat}
    (ring : DirectedRing n)
    (C F : Counter.Config q n) (root : Fin n)
    (hview : BankLeaseView ring C F root) :
    HeadlineGrantClock.BankViewEqual ring C F root := by
  intro j hj
  have h := congrArg
    (fun z : Mode × Bool × BTok × Nat =>
      (z.1, z.2.1, z.2.2.1)) (hview j hj)
  change Counter.resetAgentBankTrip
    (C (Counter.site ring root j)) =
      Counter.resetAgentBankTrip
        (F (Counter.site ring root j)) at h
  exact h

/-!
STOP at item (1): the hypothesis hpair in
bankLeaseViewStepOfPairCompatibility is stronger than BankLeaseView
and need not hold, since the output BankCell keeps unprotected
non-root grant fields. To replace it with the user's exact
hypotheses, prove a private-four-field bankPair congruence
for an internal good PACK edge (role j -> j+1, 0 <= j < b):
- source and responder have equal mode/bit/tok/lease;
- root source, if j=0, has grant=false on both sides;
- non-root grant fields may differ arbitrarily;
- the four copied owner output fields agree at both endpoints.

The unary incoming-root and top-boundary maps
already handle the other two geometries. Counter.lean already
provides physical lease projection at 7467-7481, now combined
above with its triple projection; Base.lean needs no editing.
Without the internal private-quad congruence, the exact
bankLeaseViewStep theorem is NOT established. Therefore the
finite-word StageGrantLocalBankCoupling induction and the
consumer-facing implication of that unproved coupling are
not asserted here.
-/

end GrantBankReference
end L3

namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-!
Item (1) only.

This is the internal good PACK edge.  The source has old role j,
the responder has old and post role j+1, and j < b.  Source
grant is fixed to false when j=0; responder grant is unrestricted
because its old role is always nonzero.  The literal bankPair rows
copy grant but never inspect a non-root grant.  We compare exactly
the four fields subsequently copied by copyBank, not entire cells.
-/

/-- The non-root rows of Base.bankPair, with all old private data
shared and with the two grant bits of each record unconstrained.
This is the row-by-row congruence on an internal j -> j+1 edge. -/
private theorem bankPairInternalNonrootGrantCases
    (j b : Nat) (theta : Nat → Bool)
    (hjpos : 0 < j) (hj : j < b)
    (xm ym : Mode) (xb yb : Bool)
    (xt yt : BTok) (xl yl : Nat)
    (xg xg' yg yg' : Bool) :
    bankCellLeaseQuad ((bankPair
        ⟨j, xm, xb, xt, xl, xg⟩
        ⟨j + 1, ym, yb, yt, yl, yg⟩
        (j + 1) b theta).1) =
      bankCellLeaseQuad ((bankPair
        ⟨j, xm, xb, xt, xl, xg'⟩
        ⟨j + 1, ym, yb, yt, yl, yg'⟩
        (j + 1) b theta).1) ∧
    bankCellLeaseQuad ((bankPair
        ⟨j, xm, xb, xt, xl, xg⟩
        ⟨j + 1, ym, yb, yt, yl, yg⟩
        (j + 1) b theta).2) =
      bankCellLeaseQuad ((bankPair
        ⟨j, xm, xb, xt, xl, xg'⟩
        ⟨j + 1, ym, yb, yt, yl, yg'⟩
        (j + 1) b theta).2) := by
  -- On a nonroot source `bankPair` is `bankPairNR` (BankPairNonroot.lean), which never reads a grant, with
  -- the source RESET and the responder's mode from `bankPairModeY`, which reads the grant only at post PACK 0.
  have hxn : j ≠ 0 := by omega
  have hyn : j + 1 ≠ 0 := by omega
  have hxlo : 1 ≤ j := by omega
  have hxhi : j ≤ b := by omega
  have hylo : 1 ≤ j + 1 := by omega
  have hyhi : j + 1 ≤ b := by omega
  have hxtop : j ≠ b := by omega
  rw [bankPair_nonroot ⟨j, xm, xb, xt, xl, xg⟩ ⟨j + 1, ym, yb, yt, yl, yg⟩ (j + 1) b theta hxn,
    bankPair_nonroot ⟨j, xm, xb, xt, xl, xg'⟩ ⟨j + 1, ym, yb, yt, yl, yg'⟩ (j + 1) b theta hxn]
  simp [bankCellLeaseQuad, bankPairModeY, bankPairNR, hxn, hyn, hxlo, hxhi, hylo, hyhi, hxtop, hj,
    apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
    apply_ite BankCell.bit, apply_ite BankCell.role, ite_self]

/-- The internal edge whose source is the root (j=0).  Both
old root grants are false.  The responder's non-root grant can
differ without changing either four-field output. -/
private theorem bankPairInternalRootGrantCases
    (b : Nat) (theta : Nat → Bool) (hb : 0 < b)
    (xm ym : Mode) (xb yb : Bool)
    (xt yt : BTok) (xl yl : Nat)
    (yg yg' : Bool) :
    bankCellLeaseQuad ((bankPair
        ⟨0, xm, xb, xt, xl, false⟩
        ⟨1, ym, yb, yt, yl, yg⟩ 1 b theta).1) =
      bankCellLeaseQuad ((bankPair
        ⟨0, xm, xb, xt, xl, false⟩
        ⟨1, ym, yb, yt, yl, yg'⟩ 1 b theta).1) ∧
    bankCellLeaseQuad ((bankPair
        ⟨0, xm, xb, xt, xl, false⟩
        ⟨1, ym, yb, yt, yl, yg⟩ 1 b theta).2) =
      bankCellLeaseQuad ((bankPair
        ⟨0, xm, xb, xt, xl, false⟩
        ⟨1, ym, yb, yt, yl, yg'⟩ 1 b theta).2) := by
  have hbone : 1 ≤ b := by omega
  cases xm <;> cases yt <;>
    simp [bankPair, bankCellLeaseQuad, hbone,
      isWaitMode, isRetTok, Id.run_pure, Id.run_bind] <;>
    (repeat' split) <;>
    (repeat' (first | rfl | (refine And.intro ?_ ?_)))

/-- On any internal good edge, both protected four-field
projections of bankPair are independent of all non-root
grants.  In the j=0 case the one root grant is false in each
input.  This is only a private BANK statement; no statement
about the full BankCell or about Protocol.transition follows. -/
theorem bankPairQuadIgnoresNonrootGrant
    (x x' y y' : BankCell) (j b : Nat) (theta : Nat → Bool)
    (hj : j < b)
    (hrx : x.role = j) (hrx' : x'.role = j)
    (hry : y.role = j + 1) (hry' : y'.role = j + 1)
    (hxm : x.mode = x'.mode)
    (hxb : x.bit = x'.bit)
    (hxt : x.tok = x'.tok)
    (hxl : x.lease = x'.lease)
    (hym : y.mode = y'.mode)
    (hyb : y.bit = y'.bit)
    (hyt : y.tok = y'.tok)
    (hyl : y.lease = y'.lease)
    (hroot : j = 0 → x.grant = false ∧ x'.grant = false) :
    bankCellLeaseQuad ((bankPair x y (j + 1) b theta).1) =
      bankCellLeaseQuad ((bankPair x' y' (j + 1) b theta).1) ∧
    bankCellLeaseQuad ((bankPair x y (j + 1) b theta).2) =
      bankCellLeaseQuad ((bankPair x' y' (j + 1) b theta).2) := by
  rcases x with ⟨xr, xm, xb, xt, xl, xg⟩
  rcases x' with ⟨xr', xm', xb', xt', xl', xg'⟩
  rcases y with ⟨yr, ym, yb, yt, yl, yg⟩
  rcases y' with ⟨yr', ym', yb', yt', yl', yg'⟩
  change xr = j at hrx
  change xr' = j at hrx'
  change yr = j + 1 at hry
  change yr' = j + 1 at hry'
  change xm = xm' at hxm
  change xb = xb' at hxb
  change xt = xt' at hxt
  change xl = xl' at hxl
  change ym = ym' at hym
  change yb = yb' at hyb
  change yt = yt' at hyt
  change yl = yl' at hyl
  change j = 0 → xg = false ∧ xg' = false at hroot
  subst xr
  subst xr'
  subst yr
  subst yr'
  subst xm'
  subst xb'
  subst xt'
  subst xl'
  subst ym'
  subst yb'
  subst yt'
  subst yl'
  by_cases hz : j = 0
  · subst j
    rcases hroot rfl with ⟨hg, hg'⟩
    subst xg
    subst xg'
    exact bankPairInternalRootGrantCases b theta
      (by omega) xm ym xb yb xt yt xl yl yg yg'
  · exact bankPairInternalNonrootGrantCases j b theta
      (by omega) hj xm ym xb yb xt yt xl yl xg xg' yg yg'

end GrantBankReference
end L3


namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-!
An actual two-configuration BANK coupling on the same
physical scheduler word, in the spatial BANK regime.

Only protected output projections are compared. No whole BankCell
equality is required at either boundary, and no agreement on an
unprotected exterior endpoint is imposed.
-/

/-- The four fields of the agent projection, as separate equations. -/
private theorem bankLeaseAgentQuadFields {c : Compiled}
    (a d : Agent c)
    (h : bankAgentLeaseQuad a = bankAgentLeaseQuad d) :
    a.mode = d.mode ∧ a.bit = d.bit ∧
      a.tok = d.tok ∧ a.lease.val = d.lease.val := by
  exact ⟨congrArg (fun z : Mode × Bool × BTok × Nat => z.1) h,
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.1) h,
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.1) h,
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.2) h⟩

/-- An equality of source four-fields survives the actual Fin
lease clamp in copyBank, even if both destination Agents differ. -/
private theorem bankLeaseCopyQuadOfCellQuad {c : Compiled}
    (a d : Agent c) (x y : BankCell)
    (h : bankCellLeaseQuad x = bankCellLeaseQuad y) :
    bankAgentLeaseQuad (copyBank a x) =
      bankAgentLeaseQuad (copyBank d y) := by
  have hm : x.mode = y.mode :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.1) h
  have hb : x.bit = y.bit :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.1) h
  have ht : x.tok = y.tok :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.1) h
  have hl : x.lease = y.lease :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.2) h
  rcases x with ⟨xr, xm, xb, xt, xl, xg⟩
  rcases y with ⟨yr, ym, yb, yt, yl, yg⟩
  change xm = ym at hm
  change xb = yb at hb
  change xt = yt at ht
  change xl = yl at hl
  subst ym
  subst yb
  subst yt
  subst yl
  rfl

/-- Projection of the root responder's unary boundary map is
independent of the unprotected role and grant fields. -/
private theorem bankLeaseIncomingMapQuad
    (x y : BankCell)
    (h : bankCellLeaseQuad x = bankCellLeaseQuad y) :
    bankCellLeaseQuad (incomingRootBankMap x) =
      bankCellLeaseQuad (incomingRootBankMap y) := by
  have hm : x.mode = y.mode :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.1) h
  have hb : x.bit = y.bit :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.1) h
  have ht : x.tok = y.tok :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.1) h
  have hl : x.lease = y.lease :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.2) h
  rcases x with ⟨xr, xm, xb, xt, xl, xg⟩
  rcases y with ⟨yr, ym, yb, yt, yl, yg⟩
  change xm = ym at hm
  change xb = yb at hb
  change xt = yt at ht
  change xl = yl at hl
  subst ym
  subst yb
  subst yt
  subst yl
  cases xm <;>
    simp [incomingRootBankMap, bankCellLeaseQuad, isWaitMode] <;>
    (repeat' split) <;>
    repeat' (first | rfl | (refine And.intro ?_ ?_))

/-- Projection of the top source's unary boundary map does not
read the responder or the source's non-root grant. -/
private theorem bankLeaseTopMapQuad
    (x y : BankCell)
    (h : bankCellLeaseQuad x = bankCellLeaseQuad y) :
    bankCellLeaseQuad (topBoundaryBankMap x) =
      bankCellLeaseQuad (topBoundaryBankMap y) := by
  have hb : x.bit = y.bit :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.1) h
  have ht : x.tok = y.tok :=
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.1) h
  rcases x with ⟨xr, xm, xb, xt, xl, xg⟩
  rcases y with ⟨yr, ym, yb, yt, yl, yg⟩
  change xb = yb at hb
  change xt = yt at ht
  subst yb
  subst yt
  rfl

/-- Good old PACK rows with a zero-role responder. -/
private theorem bankLeaseGoodIncomingSourceRole {c : Compiled}
    (x y : Agent c)
    (hgood : goodPair c.b x.pack y.pack = true)
    (hy : y.pack.val = 0) :
    x.pack.val = c.b ∨ x.pack.val = c.b + 1 := by
  rcases (goodPair_iff c.b x.pack y.pack).1 hgood with
      h | h | h
  · omega
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Good old PACK rows with a top-role source. -/
private theorem bankLeaseGoodTopResponderRole {c : Compiled}
    (x y : Agent c)
    (hgood : goodPair c.b x.pack y.pack = true)
    (hx : x.pack.val = c.b) :
    y.pack.val = 0 ∨ y.pack.val = c.b + 1 := by
  rcases (goodPair_iff c.b x.pack y.pack).1 hgood with
      h | h | h
  · omega
  · exact h.2
  · omega

/-- Internal j -> j+1: the selected OLD bankPair results agree
on both copied four-field projections, without matching grant
bits at any non-root site. -/
private theorem bankLeaseInternalOwnerQuads {n q : Nat}
    (ring : DirectedRing n)
    (C F : Counter.Config q n) (root e : Fin n)
    (hc : Counter.Complete ring C root)
    (hf : Counter.Complete ring F root)
    (hview : BankLeaseView ring C F root)
    (j : Nat) (hj : j < (compileAdvice q).b)
    (he : e = Counter.site ring root j)
    (hgC : Counter.GrantFree C root)
    (hgF : Counter.GrantFree F root) :
    bankCellLeaseQuad
      ((Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1) =
      bankCellLeaseQuad
        ((Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).1) ∧
    bankCellLeaseQuad
      ((Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).2) =
      bankCellLeaseQuad
        ((Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).2) := by
  have hxC : (C e).pack.val = j := by
    rw [he]
    exact hc j (by omega)
  have hxF : (F e).pack.val = j := by
    rw [he]
    exact hf j (by omega)
  have hyC : (C (ring.rightNeighbor e)).pack.val = j + 1 := by
    rw [he]
    change (C (Counter.site ring root (j + 1))).pack.val = j + 1
    exact hc (j + 1) (by omega)
  have hyF : (F (ring.rightNeighbor e)).pack.val = j + 1 := by
    rw [he]
    change (F (Counter.site ring root (j + 1))).pack.val = j + 1
    exact hf (j + 1) (by omega)
  have hvx : bankAgentLeaseQuad (C e) = bankAgentLeaseQuad (F e) := by
    rw [he]
    exact hview j (by omega)
  have hvy :
      bankAgentLeaseQuad (C (ring.rightNeighbor e)) =
        bankAgentLeaseQuad (F (ring.rightNeighbor e)) := by
    rw [he]
    change bankAgentLeaseQuad
        (C (Counter.site ring root (j + 1))) =
      bankAgentLeaseQuad (F (Counter.site ring root (j + 1)))
    exact hview (j + 1) (by omega)
  have hfx := bankLeaseAgentQuadFields (C e) (F e) hvx
  have hfy := bankLeaseAgentQuadFields
    (C (ring.rightNeighbor e))
    (F (ring.rightNeighbor e)) hvy
  have hpair := bankPairQuadIgnoresNonrootGrant
    (bankCell (C e) (C e).pack.val)
    (bankCell (F e) (F e).pack.val)
    (bankCell (C (ring.rightNeighbor e))
      (C (ring.rightNeighbor e)).pack.val)
    (bankCell (F (ring.rightNeighbor e))
      (F (ring.rightNeighbor e)).pack.val)
    j (compileAdvice q).b (compileAdvice q).theta
    hj hxC hxF hyC hyF
    hfx.1 hfx.2.1 hfx.2.2.1 hfx.2.2.2
    hfy.1 hfy.2.1 hfy.2.2.1 hfy.2.2.2
    (by
      intro hz
      have heRoot : e = root := by
        have hzero := he
        rw [hz] at hzero
        exact hzero
      rw [heRoot]
      exact ⟨hgC, hgF⟩)
  have hpostC :
      packNext (C e).pack.val
        (C (ring.rightNeighbor e)).pack.val
        (compileAdvice q).b = j + 1 := by
    rw [hxC, hyC]
    simp [packNext, hj]
  have hpostF :
      packNext (F e).pack.val
        (F (ring.rightNeighbor e)).pack.val
        (compileAdvice q).b = j + 1 := by
    rw [hxF, hyF]
    simp [packNext, hj]
  simpa only [Counter.resetBankOld, hpostC, hpostF] using hpair

/-- Top source: the first copied BANK output depends only on
the protected top source; the responder may be exterior. -/
private theorem bankLeaseTopOwnerSourceQuad {n q : Nat}
    (ring : DirectedRing n)
    (C F : Counter.Config q n) (root e : Fin n)
    (hc : Counter.Complete ring C root)
    (hf : Counter.Complete ring F root)
    (hview : BankLeaseView ring C F root)
    (he : e = Counter.site ring root (compileAdvice q).b)
    (hgoodC : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true)
    (hgoodF : goodPair (compileAdvice q).b
      (F e).pack (F (ring.rightNeighbor e)).pack = true) :
    bankCellLeaseQuad
      ((Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1) =
      bankCellLeaseQuad
        ((Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).1) := by
  have hb : 0 < (compileAdvice q).b := by
    change 0 < (compileAdvice q).s + 11
    omega
  have hxC : (C e).pack.val = (compileAdvice q).b := by
    rw [he]
    exact hc (compileAdvice q).b (by omega)
  have hxF : (F e).pack.val = (compileAdvice q).b := by
    rw [he]
    exact hf (compileAdvice q).b (by omega)
  have hyC := bankLeaseGoodTopResponderRole
    (C e) (C (ring.rightNeighbor e)) hgoodC hxC
  have hyF := bankLeaseGoodTopResponderRole
    (F e) (F (ring.rightNeighbor e)) hgoodF hxF
  have hC :
      (Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1 =
        topBoundaryBankMap (bankCell (C e) (C e).pack.val) := by
    exact topBoundaryBankSingle
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta hb hxC hyC
  have hF :
      (Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).1 =
        topBoundaryBankMap (bankCell (F e) (F e).pack.val) := by
    exact topBoundaryBankSingle
      (bankCell (F e) (F e).pack.val)
      (bankCell (F (ring.rightNeighbor e))
        (F (ring.rightNeighbor e)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta hb hxF hyF
  have hv :
      bankCellLeaseQuad (bankCell (C e) (C e).pack.val) =
        bankCellLeaseQuad (bankCell (F e) (F e).pack.val) := by
    change bankAgentLeaseQuad (C e) = bankAgentLeaseQuad (F e)
    rw [he]
    exact hview (compileAdvice q).b (by omega)
  calc
    bankCellLeaseQuad
        ((Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1) =
      bankCellLeaseQuad
        (topBoundaryBankMap (bankCell (C e) (C e).pack.val)) :=
      congrArg bankCellLeaseQuad hC
    _ = bankCellLeaseQuad
        (topBoundaryBankMap (bankCell (F e) (F e).pack.val)) :=
      bankLeaseTopMapQuad _ _ hv
    _ = bankCellLeaseQuad
        ((Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).1) :=
      (congrArg bankCellLeaseQuad hF).symm

/-- Incoming root: the second copied BANK output depends only
on the protected, grant-free root. The initiator may be exterior. -/
private theorem bankLeaseIncomingOwnerResponderQuad {n q : Nat}
    (ring : DirectedRing n)
    (C F : Counter.Config q n) (root e : Fin n)
    (hc : Counter.Complete ring C root)
    (hf : Counter.Complete ring F root)
    (hview : BankLeaseView ring C F root)
    (hinc : ring.rightNeighbor e = root)
    (hgoodC : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true)
    (hgoodF : goodPair (compileAdvice q).b
      (F e).pack (F (ring.rightNeighbor e)).pack = true)
    (hgC : Counter.GrantFree C root)
    (hgF : Counter.GrantFree F root) :
    bankCellLeaseQuad
      ((Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).2) =
      bankCellLeaseQuad
        ((Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).2) := by
  have hb : 0 < (compileAdvice q).b := by
    change 0 < (compileAdvice q).s + 11
    omega
  have hrC : (C root).pack.val = 0 := by
    simpa only [Counter.site] using hc 0 (by omega)
  have hrF : (F root).pack.val = 0 := by
    simpa only [Counter.site] using hf 0 (by omega)
  have hgoodRootC :
      goodPair (compileAdvice q).b
        (C e).pack (C root).pack = true := by
    simpa only [hinc] using hgoodC
  have hgoodRootF :
      goodPair (compileAdvice q).b
        (F e).pack (F root).pack = true := by
    simpa only [hinc] using hgoodF
  have hxC := bankLeaseGoodIncomingSourceRole
    (C e) (C root) hgoodRootC hrC
  have hxF := bankLeaseGoodIncomingSourceRole
    (F e) (F root) hgoodRootF hrF
  have hC :
      (Counter.resetBankOld (C e) (C root)).2 =
        incomingRootBankMap (bankCell (C root) (C root).pack.val) := by
    exact incomingRootBankSingle
      (bankCell (C e) (C e).pack.val)
      (bankCell (C root) (C root).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      hb hxC hrC hgC
  have hF :
      (Counter.resetBankOld (F e) (F root)).2 =
        incomingRootBankMap (bankCell (F root) (F root).pack.val) := by
    exact incomingRootBankSingle
      (bankCell (F e) (F e).pack.val)
      (bankCell (F root) (F root).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      hb hxF hrF hgF
  have hv :
      bankCellLeaseQuad (bankCell (C root) (C root).pack.val) =
        bankCellLeaseQuad (bankCell (F root) (F root).pack.val) := by
    change bankAgentLeaseQuad (C root) = bankAgentLeaseQuad (F root)
    simpa only [Counter.site] using hview 0 (by omega)
  rw [hinc]
  calc
    bankCellLeaseQuad ((Counter.resetBankOld (C e) (C root)).2) =
      bankCellLeaseQuad
        (incomingRootBankMap (bankCell (C root) (C root).pack.val)) :=
      congrArg bankCellLeaseQuad hC
    _ = bankCellLeaseQuad
        (incomingRootBankMap (bankCell (F root) (F root).pack.val)) :=
      bankLeaseIncomingMapQuad _ _ hv
    _ = bankCellLeaseQuad ((Counter.resetBankOld (F e) (F root)).2) :=
      (congrArg bankCellLeaseQuad hF).symm

/-- Physical selected-pair congruence with hypotheses only at
selected endpoints that lie in the protected root/digit interval.
Unprotected exterior endpoints need no equality of any field. -/
private theorem bankLeaseSelectedProtectedQuads {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (C F : Counter.Config q n) (root e : Fin n)
    (hview : BankLeaseView ring C F root)
    (hleft :
      (∃ j : Nat, j ≤ (compileAdvice q).b ∧
        e = Counter.site ring root j) →
      bankAgentLeaseQuad
        (copyBank (C e)
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).1) =
      bankAgentLeaseQuad
        (copyBank (F e)
          (Counter.resetBankOld
            (F e) (F (ring.rightNeighbor e))).1))
    (hright :
      (∃ j : Nat, j ≤ (compileAdvice q).b ∧
        ring.rightNeighbor e = Counter.site ring root j) →
      bankAgentLeaseQuad
        (copyBank (C (ring.rightNeighbor e))
          (Counter.resetBankOld
            (C e) (C (ring.rightNeighbor e))).2) =
      bankAgentLeaseQuad
        (copyBank (F (ring.rightNeighbor e))
          (Counter.resetBankOld
            (F e) (F (ring.rightNeighbor e))).2)) :
    BankLeaseView ring
      ((protocol q).step ring C e)
      ((protocol q).step ring F e) root := by
  have hne := HeadlineGrantClock.physicalNeighborDistinct ring hn e
  have hC := bankLeasePhysicalEdgeQuad ring C e hne hsp
  have hF := bankLeasePhysicalEdgeQuad ring F e hne hsp
  intro j hj
  by_cases hx : Counter.site ring root j = e
  · have hselected :
        bankAgentLeaseQuad (((protocol q).step ring C e) e) =
          bankAgentLeaseQuad (((protocol q).step ring F e) e) :=
      hC.1.trans ((hleft ⟨j, hj, hx.symm⟩).trans hF.1.symm)
    simpa only [hx] using hselected
  · by_cases hy :
        Counter.site ring root j = ring.rightNeighbor e
    · have hselected :
          bankAgentLeaseQuad
            (((protocol q).step ring C e)
              (ring.rightNeighbor e)) =
            bankAgentLeaseQuad
              (((protocol q).step ring F e)
                (ring.rightNeighbor e)) :=
        hC.2.trans ((hright ⟨j, hj, hy.symm⟩).trans hF.2.symm)
      simpa only [hy] using hselected
    · have hfC := Counter.step_frame ring C e
        (Counter.site ring root j) hx hy
      have hfF := Counter.step_frame ring F e
        (Counter.site ring root j) hx hy
      simpa only [hfC, hfF] using hview j hj

/-- Corrected one-step physical congruence. Both runs have
complete PACK roles and false OLD root grants; neither chosen
edge is a supported BANK defect. The conclusion concerns the
actual full protocol, and preserves the complete roles. -/
theorem bankLeaseViewStep {n q : Nat}
    (ring : DirectedRing n)
    (hsp : (compileAdvice q).useSmall = false)
    (C F : Counter.Config q n) (root e : Fin n)
    (hview : BankLeaseView ring C F root)
    (hc : Counter.Complete ring C root)
    (hf : Counter.Complete ring F root)
    (hgC : Counter.GrantFree C root)
    (hgF : Counter.GrantFree F root)
    (hnoC : ¬ Counter.ResetClockBankDefectEntry ring C root e)
    (hnoF : ¬ Counter.ResetClockBankDefectEntry ring F root e) :
    BankLeaseView ring
      ((protocol q).step ring C e)
      ((protocol q).step ring F e) root ∧
    Counter.Complete ring ((protocol q).step ring C e) root ∧
    Counter.Complete ring ((protocol q).step ring F e) root := by
  classical
  have hcnext :
      Counter.Complete ring ((protocol q).step ring C e) root := by
    have hstable :=
      Counter.resetClockBankStableOfNoDefect ring C root e hnoC
    intro j hj
    rw [hstable j hj]
    exact hc j hj
  have hfnext :
      Counter.Complete ring ((protocol q).step ring F e) root := by
    have hstable :=
      Counter.resetClockBankStableOfNoDefect ring F root e hnoF
    intro j hj
    rw [hstable j hj]
    exact hf j hj
  have hnext :
      BankLeaseView ring
        ((protocol q).step ring C e)
        ((protocol q).step ring F e) root := by
    by_cases hs : Counter.Support q ring root e
    · have hgoodC :=
        (bankLeaseNoDefectGuard ring C root e hs hnoC).1
      have hgoodF :=
        (bankLeaseNoDefectGuard ring F root e hs hnoF).1
      apply bankLeaseSelectedProtectedQuads ring
        (bankLeaseCompleteTwoSites ring C root hc)
        hsp C F root e hview
      · rintro ⟨j, hj, he⟩
        by_cases hjlt : j < (compileAdvice q).b
        · have hpair := bankLeaseInternalOwnerQuads ring C F root e
            hc hf hview j hjlt he hgC hgF
          exact bankLeaseCopyQuadOfCellQuad
            (C e) (F e)
            (Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1
            (Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).1
            hpair.1
        · have hjtop : j = (compileAdvice q).b := by omega
          subst j
          have htop := bankLeaseTopOwnerSourceQuad ring C F root e
            hc hf hview he hgoodC hgoodF
          exact bankLeaseCopyQuadOfCellQuad
            (C e) (F e)
            (Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1
            (Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).1
            htop
      · rintro ⟨j, hj, hy⟩
        by_cases hz : j = 0
        · subst j
          have hinc : ring.rightNeighbor e = root := by
            exact hy
          have hroot := bankLeaseIncomingOwnerResponderQuad
            ring C F root e hc hf hview hinc
            hgoodC hgoodF hgC hgF
          exact bankLeaseCopyQuadOfCellQuad
            (C (ring.rightNeighbor e))
            (F (ring.rightNeighbor e))
            (Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).2
            (Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).2
            hroot
        · have hsucc : j - 1 + 1 = j := by omega
          have heprev : e = Counter.site ring root (j - 1) := by
            apply Counter.resetTrialSitePredecessor ring root e (j - 1)
            simpa only [hsucc] using hy
          have hpair := bankLeaseInternalOwnerQuads ring C F root e
            hc hf hview (j - 1) (by omega) heprev hgC hgF
          exact bankLeaseCopyQuadOfCellQuad
            (C (ring.rightNeighbor e))
            (F (ring.rightNeighbor e))
            (Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).2
            (Counter.resetBankOld (F e) (F (ring.rightNeighbor e))).2
            hpair.2
    · have hframeC := bankLeaseOutsideSupportedFrame ring C root e hs
      have hframeF := bankLeaseOutsideSupportedFrame ring F root e hs
      intro j hj
      exact ((hframeC j hj).trans (hview j hj)).trans
        (hframeF j hj).symm
  exact ⟨hnext, hcnext, hfnext⟩

/-- Same-word BANK coupling of two real protocol runs. The
reference F is not a frozen/copy-only transition: at every
letter it is advanced by the full actual protocol. The two
runs remain defect-free and grant-free at every intermediate
cut; completeness is propagated by bankLeaseViewStep. -/
theorem stageGrantLocalBankCoupling {n q : Nat}
    (ring : DirectedRing n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (w : List (Fin n)) (C F : Counter.Config q n) (root : Fin n),
      BankLeaseView ring C F root →
      Counter.Complete ring C root →
      Counter.Complete ring F root →
      Counter.GrantFreeWord ring root C w →
      Counter.GrantFreeWord ring root F w →
      HeadlineGrantClock.NoSupportedDefectWord ring root C w →
      HeadlineGrantClock.NoSupportedDefectWord ring root F w →
      BankLeaseView ring
        (Counter.Word ring w C)
        (Counter.Word ring w F) root ∧
      Counter.Complete ring (Counter.Word ring w C) root ∧
      Counter.Complete ring (Counter.Word ring w F) root := by
  intro w
  induction w with
  | nil =>
      intro C F root hview hc hf _ _ _ _
      exact ⟨hview, hc, hf⟩
  | cons e es ih =>
      intro C F root hview hc hf hgC hgF hnoC hnoF
      have hstep := bankLeaseViewStep ring hsp C F root e
        hview hc hf hgC.1 hgF.1 hnoC.1 hnoF.1
      change
        BankLeaseView ring
          (Counter.Word ring es ((protocol q).step ring C e))
          (Counter.Word ring es ((protocol q).step ring F e)) root ∧
        Counter.Complete ring
          (Counter.Word ring es ((protocol q).step ring C e)) root ∧
        Counter.Complete ring
          (Counter.Word ring es ((protocol q).step ring F e)) root
      exact ih _ _ _ hstep.1 hstep.2.1 hstep.2.2
        hgC.2 hgF.2 hnoC.2 hnoF.2

/-- The consumer-visible three-field BANK coupling, obtained
from the real-run lease-inclusive coupling by forgetting lease. -/
theorem stageGrantLocalBankCouplingBankView {n q : Nat}
    (ring : DirectedRing n)
    (hsp : (compileAdvice q).useSmall = false)
    (w : List (Fin n)) (C F : Counter.Config q n) (root : Fin n)
    (hview : BankLeaseView ring C F root)
    (hc : Counter.Complete ring C root)
    (hf : Counter.Complete ring F root)
    (hgC : Counter.GrantFreeWord ring root C w)
    (hgF : Counter.GrantFreeWord ring root F w)
    (hnoC : HeadlineGrantClock.NoSupportedDefectWord ring root C w)
    (hnoF : HeadlineGrantClock.NoSupportedDefectWord ring root F w) :
    HeadlineGrantClock.BankViewEqual ring
      (Counter.Word ring w C)
      (Counter.Word ring w F) root := by
  exact bankLeaseViewForgetsLease ring _ _ root
    (stageGrantLocalBankCoupling ring hsp w C F root
      hview hc hf hgC hgF hnoC hnoF).1

end GrantBankReference
end L3


namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-!
Stopped local BANK reference and support-word locality.

Unlike the previous two-real-run coupling, this reference retains
only the four private BANK fields at offsets 0 through b and an
absorbing success latch. All roles are fixed by their indices.
Root grant is false; non-root grants are canonically set false
because bankPairQuadIgnoresNonrootGrant proved them irrelevant.
The canonical exterior has role b+1. For an incoming-root or
top-source boundary, the previously proved unary BANK maps are
exactly the corresponding dummy-pair projections.

The update is pointwise in the protected interval; thus at the
top-to-root seam (if the ring closes there) the top and root can
both be updated on the same service. This does not presuppose
an exterior configuration or an exterior scheduler history.
-/

/-- Only the four protected BANK fields, plus an absorbing latch.
A Fin (b+1) index represents one of the sites 0,...,b. -/
structure BankLocalReference (b : Nat) where
  fields : Fin (b + 1) → Mode × Bool × BTok × Nat
  success : Bool

/-- Fill a literal BANK cell from one local reference slot.
The physical PACK role is the slot index and all grants used by
the reference are false (including the authoritative root). -/
def bankLocalReferenceCell {b : Nat}
    (S : BankLocalReference b) (i : Fin (b + 1)) :
    BankCell :=
  { role := i.val, mode := (S.fields i).1,
    bit := (S.fields i).2.1, tok := (S.fields i).2.2.1,
    lease := (S.fields i).2.2.2, grant := false }

/-- The canonical dummy exterior, in the allowed spacer role. -/
def bankLocalReferenceDummy (b : Nat) : BankCell :=
  { role := b + 1, mode := .RESET, bit := false,
    tok := .E, lease := 0, grant := false }

private def bankLocalReferenceZero (q : Nat) :
    Fin ((compileAdvice q).b + 1) :=
  ⟨0, by omega⟩

private def bankLocalReferenceOne (q : Nat) :
    Fin ((compileAdvice q).b + 1) :=
  ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩

private def bankLocalReferenceTop (q : Nat) :
    Fin ((compileAdvice q).b + 1) :=
  ⟨(compileAdvice q).b, by omega⟩

/-- Seed the local reference with precisely the observed fields
at the root/digits of a real physical configuration. -/
def bankLocalReferenceStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) :
    BankLocalReference (compileAdvice q).b :=
  { fields := fun i =>
      bankAgentLeaseQuad (C (Counter.site ring root i.val)),
    success := false }

/-- The literal internal BANK row, with fixed old/post roles
j -> j+1. Each input is reconstructed from protected fields;
the root grant is false, and non-root grants are immaterial. -/
def bankLocalReferenceInternalPair (q : Nat)
    (S : BankLocalReference (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) : BankCell × BankCell :=
  bankPair
    (bankLocalReferenceCell S ⟨j.val, by omega⟩)
    (bankLocalReferenceCell S ⟨j.val + 1, by omega⟩)
    (j.val + 1) (compileAdvice q).b (compileAdvice q).theta

/-- The literal owner row with the canonical exterior initiator.
By incomingRootBankSingle it has the same responder as
incomingRootBankMap, with no dependence on exterior private data. -/
def bankLocalReferenceIncomingDummyRow (q : Nat)
    (S : BankLocalReference (compileAdvice q).b) : BankCell :=
  (bankPair
    (bankLocalReferenceDummy (compileAdvice q).b)
    (bankLocalReferenceCell S (bankLocalReferenceZero q))
    0 (compileAdvice q).b (compileAdvice q).theta).2

/-- The literal owner row with the canonical exterior responder.
By topBoundaryBankSingle its source is topBoundaryBankMap. -/
def bankLocalReferenceTopDummyRow (q : Nat)
    (S : BankLocalReference (compileAdvice q).b) : BankCell :=
  (bankPair
    (bankLocalReferenceCell S (bankLocalReferenceTop q))
    (bankLocalReferenceDummy (compileAdvice q).b)
    ((compileAdvice q).b + 1)
    (compileAdvice q).b (compileAdvice q).theta).1

/-- The exact old-state bankSuccess predicate of the fixed
role-zero -> role-one internal edge, with root grant false.
All other directed edges have no BANK-success event. -/
def bankLocalReferenceSuccessEvent {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (e : Fin n) : Bool :=
  if e = root then
    bankSuccess
      (bankLocalReferenceCell S (bankLocalReferenceZero q))
      (bankLocalReferenceCell S (bankLocalReferenceOne q))
      1 (compileAdvice q).b
  else false

/-- Pointwise update of the finite protected interval.
For an internal source/target execute the two literal bankPair
outputs. For the top source and incoming root execute the
unary boundary maps. All other protected slots are framed.
The two boundary tests are independent, allowing the top->root
ring seam to update both endpoints in one step. -/
noncomputable def bankLocalReferenceFieldStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1)) :
    Mode × Bool × BTok × Nat := by
  classical
  exact
    if hx : i.val < (compileAdvice q).b ∧
        e = Counter.site ring root i.val then
      bankCellLeaseQuad
        ((bankLocalReferenceInternalPair q S
          ⟨i.val, hx.1⟩).1)
    else if hy : 0 < i.val ∧
        e = Counter.site ring root (i.val - 1) then
      bankCellLeaseQuad
        ((bankLocalReferenceInternalPair q S
          ⟨i.val - 1, by omega⟩).2)
    else if ht : i.val = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b then
      bankCellLeaseQuad
        (topBoundaryBankMap (bankLocalReferenceCell S i))
    else if hr : i.val = 0 ∧ ring.rightNeighbor e = root then
      bankCellLeaseQuad
        (incomingRootBankMap (bankLocalReferenceCell S i))
    else S.fields i

/-- On a support service, update from the OLD reference fields
and latch the exact OLD BANK success event. Once success is true,
the entire reference becomes absorbing. An unsupported letter
is the identity, including on the latch. -/
noncomputable def bankLocalReferenceStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (e : Fin n) : BankLocalReference (compileAdvice q).b := by
  classical
  exact
    if h : Counter.Support q ring root e then
      if S.success then S
      else
        { fields := fun i =>
            bankLocalReferenceFieldStep ring root e S i,
          success := S.success ||
            bankLocalReferenceSuccessEvent ring root S e }
    else S

/-- Advance the stopped local reference along actual scheduler
letters, rather than along a second full Agent configuration. -/
noncomputable def bankLocalReferenceWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) →
      BankLocalReference (compileAdvice q).b →
        BankLocalReference (compileAdvice q).b
  | [], S => S
  | e :: es, S =>
      bankLocalReferenceWord ring root es
        (bankLocalReferenceStep ring root S e)

/-- Keep exactly the letters in the root's boundary-inclusive
causal support; their original order is preserved. -/
noncomputable def bankLocalReferenceSupportSubword {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (w : List (Fin n)) : List (Fin n) := by
  classical
  exact w.filter (fun e => decide (Counter.Support q ring root e))

/-- The stopped local BANK reference is a deterministic function
of its own support subword, not the entire original scheduler word.
The result includes both every four-field slot and the latch.
No physical-run or no-defect hypothesis is needed for locality. -/
theorem bankLocalReferenceWordLocality {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n))
      (S : BankLocalReference (compileAdvice q).b),
      bankLocalReferenceWord ring root
        (bankLocalReferenceSupportSubword (q := q) ring root w) S =
      bankLocalReferenceWord ring root w S := by
  classical
  intro w
  induction w with
  | nil =>
      intro S
      simp [bankLocalReferenceSupportSubword,
        bankLocalReferenceWord]
  | cons e es ih =>
      intro S
      by_cases hs : Counter.Support q ring root e
      · have hf :
            bankLocalReferenceSupportSubword (q := q)
              ring root (e :: es) =
            e :: bankLocalReferenceSupportSubword (q := q)
              ring root es := by
          simp [bankLocalReferenceSupportSubword, hs]
        rw [hf]
        change bankLocalReferenceWord ring root
            (bankLocalReferenceSupportSubword (q := q)
              ring root es)
            (bankLocalReferenceStep ring root S e) =
          bankLocalReferenceWord ring root es
            (bankLocalReferenceStep ring root S e)
        exact ih _
      · have hf :
            bankLocalReferenceSupportSubword (q := q)
              ring root (e :: es) =
            bankLocalReferenceSupportSubword (q := q)
              ring root es := by
          simp [bankLocalReferenceSupportSubword, hs]
        have hskip :
            bankLocalReferenceStep ring root S e = S := by
          simp [bankLocalReferenceStep, hs]
        rw [hf]
        change bankLocalReferenceWord ring root
            (bankLocalReferenceSupportSubword (q := q)
              ring root es) S =
          bankLocalReferenceWord ring root es
            (bankLocalReferenceStep ring root S e)
        rw [hskip]
        exact ih S

end GrantBankReference
end L3


namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-!
Local-reference/real-run bridge certificates.

The exact finite-word four-field simulation remains incomplete:
the physical copyBank lease is a Fin value, whereas the reference
stores the raw Nat BANK lease. The missing closure is the numeric
in-range bound for all reference BANK outputs, followed by the
pointwise geometry proof for bankLocalReferenceFieldStep.

The declarations below give the actual root-nominated success
event, its equality with the reference event, the latch update,
the outside-support physical frame, internal/top/incoming raw row
compatibility, and the internal selected physical copy result
under its explicit lease-bound premise. No unsupported theorem
claiming the full step or full word coupling is introduced.
-/

/-- Exact agreement of the local fields with the physical BANK
projection at every protected offset. This says nothing about
external Agents, their grants, or their scheduler history. -/
def bankLocalReferenceFieldsAgree {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b) : Prop :=
  ∀ j : Nat, (hj : j ≤ (compileAdvice q).b) →
    bankAgentLeaseQuad (C (Counter.site ring root j)) =
      S.fields ⟨j, Nat.lt_succ_of_le hj⟩

/-- The canonical reference starts from the exact physical view. -/
theorem bankLocalReferenceStartAgrees {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n) :
    bankLocalReferenceFieldsAgree ring C root
      (bankLocalReferenceStart ring root C) := by
  intro j hj
  rfl

/-- Select ONLY the named root's success. Another role-zero
source elsewhere may fire BANK on an unsupported edge; that
different source is not a success of this local reference. -/
def bankLocalReferenceRealSuccessEvent {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (e : Fin n) : Bool :=
  if e = root then
    bankSuccess
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (packNext (C e).pack.val
        (C (ring.rightNeighbor e)).pack.val (compileAdvice q).b)
      (compileAdvice q).b
  else false

/-- Extract the four ordinary fields from equality of BANK
private quads. The grant field is deliberately not inspected. -/
private theorem bankLocalReferenceCellFieldEqual
    (x y : BankCell)
    (h : bankCellLeaseQuad x = bankCellLeaseQuad y) :
    x.mode = y.mode ∧ x.bit = y.bit ∧
      x.tok = y.tok ∧ x.lease = y.lease := by
  exact ⟨congrArg (fun z : Mode × Bool × BTok × Nat => z.1) h,
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.1) h,
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.1) h,
    congrArg (fun z : Mode × Bool × BTok × Nat => z.2.2.2) h⟩

/-- The reconstructed reference cell and actual old cell have
identical private four fields at a protected index. -/
private theorem bankLocalReferenceCellOfMatch {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (j : Nat) (hj : j ≤ (compileAdvice q).b) :
    bankCellLeaseQuad
      (bankCell (C (Counter.site ring root j))
        (C (Counter.site ring root j)).pack.val) =
      bankCellLeaseQuad
        (bankLocalReferenceCell S ⟨j, by omega⟩) := by
  change bankAgentLeaseQuad (C (Counter.site ring root j)) =
    S.fields ⟨j, by omega⟩
  exact hfields j hj

/-- Old-state local success on the root edge is exactly the
literal physical BANK success of the nominated root. -/
theorem bankLocalReferenceEventMatchesReal {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S) :
    bankLocalReferenceSuccessEvent ring root S e =
      bankLocalReferenceRealSuccessEvent ring root C e := by
  have hz : (C root).pack.val = 0 := by
    simpa only [Counter.site] using hc 0 (by omega)
  have ho : (C (ring.rightNeighbor root)).pack.val = 1 := by
    have hh := hc 1 (by
      change 1 ≤ (compileAdvice q).s + 11
      omega)
    change (C (ring.rightNeighbor root)).pack.val = 1 at hh
    exact hh
  have hmode :
      (C root).mode =
        (bankLocalReferenceCell S
          (bankLocalReferenceZero q)).mode := by
    have hh := hfields 0 (by omega)
    exact congrArg
      (fun z : Mode × Bool × BTok × Nat => z.1) hh
  have htok :
      (C (ring.rightNeighbor root)).tok =
        (bankLocalReferenceCell S
          (bankLocalReferenceOne q)).tok := by
    have hh := hfields 1 (by
      change 1 ≤ (compileAdvice q).s + 11
      omega)
    change (C (ring.rightNeighbor root)).tok =
      (bankLocalReferenceCell S (bankLocalReferenceOne q)).tok at *
    exact congrArg
      (fun z : Mode × Bool × BTok × Nat => z.2.2.1) hh
  have hb : 0 < (compileAdvice q).b := by
    change 0 < (compileAdvice q).s + 11
    omega
  have hp :
      packNext (C root).pack.val
        (C (ring.rightNeighbor root)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hz, ho]
    simp [packNext, hb]
  by_cases he : e = root
  · subst e
    rw [bankLocalReferenceSuccessEvent, bankLocalReferenceRealSuccessEvent,
      if_pos rfl, if_pos rfl]
    change
      bankSuccess
        (bankLocalReferenceCell S (bankLocalReferenceZero q))
        (bankLocalReferenceCell S (bankLocalReferenceOne q))
        1 (compileAdvice q).b =
      bankSuccess (bankCell (C root) (C root).pack.val)
        (bankCell (C (ring.rightNeighbor root))
          (C (ring.rightNeighbor root)).pack.val)
        (packNext (C root).pack.val
          (C (ring.rightNeighbor root)).pack.val
          (compileAdvice q).b) (compileAdvice q).b
    rw [hp]
    have hg' : (C root).grant = false := hg
    simp [bankSuccess, bankCell, bankLocalReferenceCell,
      hz, ho, hg', hmode, htok, bankLocalReferenceZero, bankLocalReferenceOne]
  · simp [bankLocalReferenceSuccessEvent,
      bankLocalReferenceRealSuccessEvent, he]

/-- The unsupported case of the exact physical/reference
coupling follows from two genuine frames, independently of
any private field of an exterior Agent. -/
theorem bankLocalReferenceOutsideStepAgrees {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hout : ¬ Counter.Support q ring root e) :
    bankLocalReferenceFieldsAgree ring
      ((protocol q).step ring C e) root
      (bankLocalReferenceStep ring root S e) := by
  classical
  have hskip : bankLocalReferenceStep ring root S e = S := by
    simp [bankLocalReferenceStep, hout]
  rw [hskip]
  intro j hj
  exact (bankLeaseOutsideSupportedFrame ring C root e hout
    j hj).trans (hfields j hj)

/-- The local latch at one service is the nominated root's
literal old-state BANK-success Boolean; this is independent of
whether the selected edge is internal or outside support. -/
theorem bankLocalReferenceLatchStepMatchesReal {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hfalse : S.success = false) :
    (bankLocalReferenceStep ring root S e).success =
      bankLocalReferenceRealSuccessEvent ring root C e := by
  classical
  have hEvent := bankLocalReferenceEventMatchesReal
    ring C root e S hc hg hfields
  by_cases hs : Counter.Support q ring root e
  · simp [bankLocalReferenceStep, hs, hfalse, hEvent]
  · have hne : e ≠ root := by
      intro he
      apply hs
      exact Or.inr ⟨0, by omega, by simpa only [Counter.site] using he⟩
    simp [bankLocalReferenceStep, hs,
      bankLocalReferenceRealSuccessEvent, hne, hfalse]

/-- The local reference becomes completely absorbing once it
has latched a successful root BANK comparison. -/
theorem bankLocalReferenceLatchedStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (h : S.success = true) :
    bankLocalReferenceStep ring root S e = S := by
  classical
  by_cases hs : Counter.Support q ring root e
  · simp [bankLocalReferenceStep, hs, h]
  · simp [bankLocalReferenceStep, hs]

/-- The absorbing property holds for the whole suffix word,
not only for its first letter. -/
theorem bankLocalReferenceLatchedWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n))
      (S : BankLocalReference (compileAdvice q).b),
      S.success = true →
      bankLocalReferenceWord ring root w S = S := by
  intro w
  induction w with
  | nil =>
      intro S _
      rfl
  | cons e es ih =>
      intro S h
      change bankLocalReferenceWord ring root es
        (bankLocalReferenceStep ring root S e) = S
      rw [bankLocalReferenceLatchedStep ring root e S h]
      exact ih S h

/-- The native owner copies the raw four-field output whenever
the numeric lease is within the compiled cap. This is not
assumed for arbitrary BankCells with unbounded Nat lease. -/
private theorem bankLocalReferenceCopyQuadExact {c : Compiled}
    (a : Agent c) (z : BankCell)
    (hz : z.lease < c.bankLeaseCap + 1) :
    bankAgentLeaseQuad (copyBank a z) =
      bankCellLeaseQuad z := by
  simp [bankAgentLeaseQuad, bankCellLeaseQuad, copyBank, hz]

/-- The internal row's two raw four-field outputs agree with
the reference's literal bankPair row. The only grant assumption
is the selected root's grant being false; non-root grants are
unrestricted. No numeric-lease conversion occurs in this lemma. -/
private theorem bankLocalReferenceInternalRawQuads {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (j : Fin (compileAdvice q).b) :
    bankCellLeaseQuad
      ((Counter.resetBankOld
        (C (Counter.site ring root j.val))
        (C (ring.rightNeighbor
          (Counter.site ring root j.val)))).1) =
      bankCellLeaseQuad
        ((bankLocalReferenceInternalPair q S j).1) ∧
    bankCellLeaseQuad
      ((Counter.resetBankOld
        (C (Counter.site ring root j.val))
        (C (ring.rightNeighbor
          (Counter.site ring root j.val)))).2) =
      bankCellLeaseQuad
        ((bankLocalReferenceInternalPair q S j).2) := by
  have hx : (C (Counter.site ring root j.val)).pack.val =
      j.val := hc j.val (by omega)
  have hy :
      (C (ring.rightNeighbor
        (Counter.site ring root j.val))).pack.val =
        j.val + 1 := by
    change (C (Counter.site ring root (j.val + 1))).pack.val =
      j.val + 1
    exact hc (j.val + 1) (by omega)
  have hxquad := bankLocalReferenceCellOfMatch
    ring C root S hfields j.val (by omega)
  have hyquad :
      bankCellLeaseQuad
        (bankCell (C (ring.rightNeighbor
          (Counter.site ring root j.val)))
          (C (ring.rightNeighbor
            (Counter.site ring root j.val))).pack.val) =
      bankCellLeaseQuad
        (bankLocalReferenceCell S ⟨j.val + 1, by omega⟩) := by
    change bankAgentLeaseQuad
      (C (Counter.site ring root (j.val + 1))) =
      S.fields ⟨j.val + 1, by omega⟩
    exact hfields (j.val + 1) (by omega)
  have hfx := bankLocalReferenceCellFieldEqual _ _ hxquad
  have hfy := bankLocalReferenceCellFieldEqual _ _ hyquad
  have hroot :
      j.val = 0 →
        (bankCell (C (Counter.site ring root j.val))
          (C (Counter.site ring root j.val)).pack.val).grant =
          false ∧
        (bankLocalReferenceCell S ⟨j.val, by omega⟩).grant =
          false := by
    intro hz
    change (C (Counter.site ring root j.val)).grant = false ∧
      (false : Bool) = false
    rw [hz]
    exact ⟨hg, rfl⟩
  have hpair := bankPairQuadIgnoresNonrootGrant
    (bankCell (C (Counter.site ring root j.val))
      (C (Counter.site ring root j.val)).pack.val)
    (bankLocalReferenceCell S ⟨j.val, by omega⟩)
    (bankCell (C (ring.rightNeighbor
      (Counter.site ring root j.val)))
      (C (ring.rightNeighbor
        (Counter.site ring root j.val))).pack.val)
    (bankLocalReferenceCell S ⟨j.val + 1, by omega⟩)
    j.val (compileAdvice q).b (compileAdvice q).theta
    j.isLt hx rfl hy rfl
    hfx.1 hfx.2.1 hfx.2.2.1 hfx.2.2.2
    hfy.1 hfy.2.1 hfy.2.2.1 hfy.2.2.2 hroot
  have hpost :
      packNext
        (C (Counter.site ring root j.val)).pack.val
        (C (ring.rightNeighbor
          (Counter.site ring root j.val))).pack.val
        (compileAdvice q).b = j.val + 1 := by
    rw [hx, hy]
    simp [packNext, j.isLt]
  simpa only [Counter.resetBankOld,
    bankLocalReferenceInternalPair, hpost] using hpair

/-- Internal physical selected outputs agree with the raw local
BANK results, provided precisely the two output lease bounds.
The bounds are necessary to replace copyBank's clamp by the
Nat lease field, and are not assumed of arbitrary BankCells. -/
theorem bankLocalReferenceInternalPhysicalCopied {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (j : Fin (compileAdvice q).b)
    (hleft :
      ((bankLocalReferenceInternalPair q S j).1).lease <
        (compileAdvice q).bankLeaseCap + 1)
    (hright :
      ((bankLocalReferenceInternalPair q S j).2).lease <
        (compileAdvice q).bankLeaseCap + 1) :
    bankAgentLeaseQuad
      (((protocol q).step ring C
        (Counter.site ring root j.val))
        (Counter.site ring root j.val)) =
      bankCellLeaseQuad ((bankLocalReferenceInternalPair q S j).1) ∧
    bankAgentLeaseQuad
      (((protocol q).step ring C
        (Counter.site ring root j.val))
        (ring.rightNeighbor (Counter.site ring root j.val))) =
      bankCellLeaseQuad ((bankLocalReferenceInternalPair q S j).2) := by
  have hn := bankLeaseCompleteTwoSites ring C root hc
  have hne := HeadlineGrantClock.physicalNeighborDistinct ring hn
    (Counter.site ring root j.val)
  have hphys := bankLeasePhysicalEdgeQuad ring C
    (Counter.site ring root j.val) hne hsp
  have hraw := bankLocalReferenceInternalRawQuads ring C
    root S hc hg hfields j
  constructor
  · calc
      bankAgentLeaseQuad
          (((protocol q).step ring C
            (Counter.site ring root j.val))
            (Counter.site ring root j.val)) =
        bankAgentLeaseQuad
          (copyBank (C (Counter.site ring root j.val))
            (Counter.resetBankOld
              (C (Counter.site ring root j.val))
              (C (ring.rightNeighbor
                (Counter.site ring root j.val)))).1) := hphys.1
      _ = bankAgentLeaseQuad
          (copyBank (C (Counter.site ring root j.val))
            (bankLocalReferenceInternalPair q S j).1) :=
        bankLeaseCopyQuadOfCellQuad _ _ _ _ hraw.1
      _ = bankCellLeaseQuad
          ((bankLocalReferenceInternalPair q S j).1) :=
        bankLocalReferenceCopyQuadExact _ _ hleft
  · calc
      bankAgentLeaseQuad
          (((protocol q).step ring C
            (Counter.site ring root j.val))
            (ring.rightNeighbor
              (Counter.site ring root j.val))) =
        bankAgentLeaseQuad
          (copyBank (C (ring.rightNeighbor
            (Counter.site ring root j.val)))
            (Counter.resetBankOld
              (C (Counter.site ring root j.val))
              (C (ring.rightNeighbor
                (Counter.site ring root j.val)))).2) := hphys.2
      _ = bankAgentLeaseQuad
          (copyBank (C (ring.rightNeighbor
            (Counter.site ring root j.val)))
            (bankLocalReferenceInternalPair q S j).2) :=
        bankLeaseCopyQuadOfCellQuad _ _ _ _ hraw.2
      _ = bankCellLeaseQuad
          ((bankLocalReferenceInternalPair q S j).2) :=
        bankLocalReferenceCopyQuadExact _ _ hright

/-- A final word letter is evaluated after the whole prefix.
This is the exact scheduler-word recursion used in the
survival argument, independently of any physical coupling. -/
theorem bankLocalReferenceWordAppendSingleton {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (e : Fin n)
      (S : BankLocalReference (compileAdvice q).b),
      bankLocalReferenceWord ring root (w ++ [e]) S =
        bankLocalReferenceStep ring root
          (bankLocalReferenceWord ring root w S) e := by
  intro w
  induction w with
  | nil =>
      intro e S
      rfl
  | cons f fs ih =>
      intro e S
      change bankLocalReferenceWord ring root
        (fs ++ [e]) (bankLocalReferenceStep ring root S f) =
        bankLocalReferenceStep ring root
          (bankLocalReferenceWord ring root fs
            (bankLocalReferenceStep ring root S f)) e
      exact ih e _

/-- First-hit observation at a specified final edge, conditional
on an established physical/reference field relation at that
preterminal cut. This certificate does not assume an unjustified
post-success physical/reference field coupling. -/
theorem bankLocalReferenceFinalLetterSuccess {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (S : BankLocalReference (compileAdvice q).b)
    (w : List (Fin n)) (e : Fin n)
    (hc : Counter.Complete ring
      (Counter.Word ring w C) root)
    (hg : Counter.GrantFree
      (Counter.Word ring w C) root)
    (hfields : bankLocalReferenceFieldsAgree ring
      (Counter.Word ring w C) root
      (bankLocalReferenceWord ring root w S))
    (hbefore :
      (bankLocalReferenceWord ring root w S).success = false) :
    (bankLocalReferenceWord ring root (w ++ [e]) S).success =
      bankLocalReferenceRealSuccessEvent ring root
        (Counter.Word ring w C) e := by
  rw [bankLocalReferenceWordAppendSingleton]
  exact bankLocalReferenceLatchStepMatchesReal ring
    (Counter.Word ring w C) root e
    (bankLocalReferenceWord ring root w S)
    hc hg hfields hbefore

end GrantBankReference
end L3

/-!
Physical-copy-clamped local BANK reference.

The old raw BANK reference and its conditional copying lemmas are as
above; all simulation claims below concern the clamped variant.
No raw bankPair lease-cap case product is asserted.
-/

namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-- Exactly the four coordinates of the physical Fin-clamped copy. -/
def bankLocalReferenceClampedQuad (q : Nat) (z : BankCell) :
    Mode × Bool × BTok × Nat :=
  bankAgentLeaseQuad (copyBank (Agent.blank (compileAdvice q)) z)

/-- No numeric bound is necessary: physical and reference copies
apply the identical clamp, independently of the destination Agent. -/
private theorem bankLocalReferenceCopyQuadClamped
    (q : Nat) (a : Agent (compileAdvice q)) (z : BankCell) :
    bankAgentLeaseQuad (copyBank a z) =
      bankLocalReferenceClampedQuad q z := by
  exact bankLeaseCopyQuadOfCellQuad a
    (Agent.blank (compileAdvice q)) z z rfl


/-- Unary top boundary produces zero lease, with no arithmetic search
through raw bankPair case products. Kept as an independent row fact. -/
private theorem bankLocalReferenceTopMapLeaseCap {c : Compiled}
    (x : BankCell) :
    (topBoundaryBankMap x).lease < c.bankLeaseCap + 1 := by
  simp [topBoundaryBankMap]

/-- Unary incoming boundary either resets the root, preserves its
lease, or decrements it. Split only on root mode and 1 < lease. -/
private theorem bankLocalReferenceIncomingMapLeaseCap
    (x : BankCell) (cap : Nat)
    (h : x.lease < cap + 1) :
    (incomingRootBankMap x).lease < cap + 1 := by
  rcases x with ⟨r, m, bit, tok, lease, grant⟩
  change lease < cap + 1 at h
  cases m <;> by_cases hl : 1 < lease <;>
    simp [incomingRootBankMap, isWaitMode, hl] <;>
    omega

/-- Every clamped reference output is physically representable as
a Fin lease, including the fallback when the raw output exceeds L. -/
theorem bankLocalReferenceClampedQuadLeaseBound
    (q : Nat) (z : BankCell) :
    (bankLocalReferenceClampedQuad q z).2.2.2 <
      (compileAdvice q).bankLeaseCap + 1 := by
  change (copyBank (Agent.blank (compileAdvice q)) z).lease.val <
    (compileAdvice q).bankLeaseCap + 1
  exact (copyBank (Agent.blank (compileAdvice q)) z).lease.isLt

noncomputable def bankLocalReferenceFieldStepClamped {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1)) :
    Mode × Bool × BTok × Nat := by
  classical
  exact
    if hx : i.val < (compileAdvice q).b ∧
        e = Counter.site ring root i.val then
      bankLocalReferenceClampedQuad q
        ((bankLocalReferenceInternalPair q S
          ⟨i.val, hx.1⟩).1)
    else if hy : 0 < i.val ∧
        e = Counter.site ring root (i.val - 1) then
      bankLocalReferenceClampedQuad q
        ((bankLocalReferenceInternalPair q S
          ⟨i.val - 1, by omega⟩).2)
    else if ht : i.val = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b then
      bankLocalReferenceClampedQuad q
        (topBoundaryBankMap (bankLocalReferenceCell S i))
    else if hr : i.val = 0 ∧ ring.rightNeighbor e = root then
      bankLocalReferenceClampedQuad q
        (incomingRootBankMap (bankLocalReferenceCell S i))
    else S.fields i

/-- On a support service, update from the OLD reference fields
and latch the exact OLD BANK success event. Once success is true,
the entire reference becomes absorbing. An unsupported letter
is the identity, including on the latch. -/
noncomputable def bankLocalReferenceStepClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (e : Fin n) : BankLocalReference (compileAdvice q).b := by
  classical
  exact
    if h : Counter.Support q ring root e then
      if S.success then S
      else
        { fields := fun i =>
            bankLocalReferenceFieldStepClamped ring root e S i,
          success := S.success ||
            bankLocalReferenceSuccessEvent ring root S e }
    else S

/-- Advance the stopped local reference along actual scheduler
letters, rather than along a second full Agent configuration. -/
noncomputable def bankLocalReferenceWordClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) →
      BankLocalReference (compileAdvice q).b →
        BankLocalReference (compileAdvice q).b
  | [], S => S
  | e :: es, S =>
      bankLocalReferenceWordClamped ring root es
        (bankLocalReferenceStepClamped ring root S e)


/-- Locality of the clamped reference: only supported scheduler
letters can change the field array or the success latch. -/
theorem bankLocalReferenceWordLocalityClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n))
      (S : BankLocalReference (compileAdvice q).b),
      bankLocalReferenceWordClamped ring root
        (bankLocalReferenceSupportSubword (q := q) ring root w) S =
      bankLocalReferenceWordClamped ring root w S := by
  classical
  intro w
  induction w with
  | nil =>
      intro S
      simp [bankLocalReferenceSupportSubword,
        bankLocalReferenceWordClamped]
  | cons e es ih =>
      intro S
      by_cases hs : Counter.Support q ring root e
      · have hf :
            bankLocalReferenceSupportSubword (q := q)
              ring root (e :: es) =
            e :: bankLocalReferenceSupportSubword (q := q)
              ring root es := by
          simp [bankLocalReferenceSupportSubword, hs]
        rw [hf]
        change bankLocalReferenceWordClamped ring root
            (bankLocalReferenceSupportSubword (q := q)
              ring root es)
            (bankLocalReferenceStepClamped ring root S e) =
          bankLocalReferenceWordClamped ring root es
            (bankLocalReferenceStepClamped ring root S e)
        exact ih _
      · have hf :
            bankLocalReferenceSupportSubword (q := q)
              ring root (e :: es) =
            bankLocalReferenceSupportSubword (q := q)
              ring root es := by
          simp [bankLocalReferenceSupportSubword, hs]
        have hskip :
            bankLocalReferenceStepClamped ring root S e = S := by
          simp [bankLocalReferenceStepClamped, hs]
        rw [hf]
        change bankLocalReferenceWordClamped ring root
            (bankLocalReferenceSupportSubword (q := q)
              ring root es) S =
          bankLocalReferenceWordClamped ring root es
            (bankLocalReferenceStepClamped ring root S e)
        rw [hskip]
        exact ih S

theorem bankLocalReferenceOutsideStepAgreesClamped {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hout : ¬ Counter.Support q ring root e) :
    bankLocalReferenceFieldsAgree ring
      ((protocol q).step ring C e) root
      (bankLocalReferenceStepClamped ring root S e) := by
  classical
  have hskip : bankLocalReferenceStepClamped ring root S e = S := by
    simp [bankLocalReferenceStepClamped, hout]
  rw [hskip]
  intro j hj
  exact (bankLeaseOutsideSupportedFrame ring C root e hout
    j hj).trans (hfields j hj)


theorem bankLocalReferenceLatchStepMatchesRealClamped {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hfalse : S.success = false) :
    (bankLocalReferenceStepClamped ring root S e).success =
      bankLocalReferenceRealSuccessEvent ring root C e := by
  classical
  have hEvent := bankLocalReferenceEventMatchesReal
    ring C root e S hc hg hfields
  by_cases hs : Counter.Support q ring root e
  · simp [bankLocalReferenceStepClamped, hs, hfalse, hEvent]
  · have hne : e ≠ root := by
      intro he
      apply hs
      exact Or.inr ⟨0, by omega, by simpa only [Counter.site] using he⟩
    simp [bankLocalReferenceStepClamped, hs,
      bankLocalReferenceRealSuccessEvent, hne, hfalse]


theorem bankLocalReferenceInternalPhysicalClamped {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (j : Fin (compileAdvice q).b) :
    bankAgentLeaseQuad
      (((protocol q).step ring C
        (Counter.site ring root j.val))
        (Counter.site ring root j.val)) =
      bankLocalReferenceClampedQuad q ((bankLocalReferenceInternalPair q S j).1) ∧
    bankAgentLeaseQuad
      (((protocol q).step ring C
        (Counter.site ring root j.val))
        (ring.rightNeighbor (Counter.site ring root j.val))) =
      bankLocalReferenceClampedQuad q ((bankLocalReferenceInternalPair q S j).2) := by
  have hn := bankLeaseCompleteTwoSites ring C root hc
  have hne := HeadlineGrantClock.physicalNeighborDistinct ring hn
    (Counter.site ring root j.val)
  have hphys := bankLeasePhysicalEdgeQuad ring C
    (Counter.site ring root j.val) hne hsp
  have hraw := bankLocalReferenceInternalRawQuads ring C
    root S hc hg hfields j
  constructor
  · calc
      bankAgentLeaseQuad
          (((protocol q).step ring C
            (Counter.site ring root j.val))
            (Counter.site ring root j.val)) =
        bankAgentLeaseQuad
          (copyBank (C (Counter.site ring root j.val))
            (Counter.resetBankOld
              (C (Counter.site ring root j.val))
              (C (ring.rightNeighbor
                (Counter.site ring root j.val)))).1) := hphys.1
      _ = bankAgentLeaseQuad
          (copyBank (C (Counter.site ring root j.val))
            (bankLocalReferenceInternalPair q S j).1) :=
        bankLeaseCopyQuadOfCellQuad _ _ _ _ hraw.1
      _ = bankLocalReferenceClampedQuad q
          ((bankLocalReferenceInternalPair q S j).1) :=
        bankLocalReferenceCopyQuadClamped q
          (C (Counter.site ring root j.val))
          (bankLocalReferenceInternalPair q S j).1
  · calc
      bankAgentLeaseQuad
          (((protocol q).step ring C
            (Counter.site ring root j.val))
            (ring.rightNeighbor
              (Counter.site ring root j.val))) =
        bankAgentLeaseQuad
          (copyBank (C (ring.rightNeighbor
            (Counter.site ring root j.val)))
            (Counter.resetBankOld
              (C (Counter.site ring root j.val))
              (C (ring.rightNeighbor
                (Counter.site ring root j.val)))).2) := hphys.2
      _ = bankAgentLeaseQuad
          (copyBank (C (ring.rightNeighbor
            (Counter.site ring root j.val)))
            (bankLocalReferenceInternalPair q S j).2) :=
        bankLeaseCopyQuadOfCellQuad _ _ _ _ hraw.2
      _ = bankLocalReferenceClampedQuad q
          ((bankLocalReferenceInternalPair q S j).2) :=
        bankLocalReferenceCopyQuadClamped q
          (C (ring.rightNeighbor (Counter.site ring root j.val)))
          (bankLocalReferenceInternalPair q S j).2


/-- Good top-source service: exact actual physical output equals
the reference's top unary map, including the numeric lease. -/
theorem bankLocalReferenceTopPhysicalCopied {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (he : e = Counter.site ring root (compileAdvice q).b)
    (hgood : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true) :
    bankAgentLeaseQuad (((protocol q).step ring C e) e) =
      bankLocalReferenceClampedQuad q
        (topBoundaryBankMap
          (bankLocalReferenceCell S (bankLocalReferenceTop q))) := by
  have hb : 0 < (compileAdvice q).b := by
    change 0 < (compileAdvice q).s + 11
    omega
  have hrole : (C e).pack.val = (compileAdvice q).b := by
    rw [he]
    exact hc (compileAdvice q).b (by omega)
  have htarget := bankLeaseGoodTopResponderRole
    (C e) (C (ring.rightNeighbor e)) hgood hrole
  have hrow :
      (Counter.resetBankOld (C e) (C (ring.rightNeighbor e))).1 =
        topBoundaryBankMap (bankCell (C e) (C e).pack.val) := by
    exact topBoundaryBankSingle
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      hb hrole htarget
  have hv :
      bankCellLeaseQuad (bankCell (C e) (C e).pack.val) =
        bankCellLeaseQuad
          (bankLocalReferenceCell S (bankLocalReferenceTop q)) := by
    rw [he]
    simpa only [bankLocalReferenceTop] using
      bankLocalReferenceCellOfMatch ring C root S hfields
        (compileAdvice q).b (by omega)
  have hmap := bankLeaseTopMapQuad _ _ hv
  have hne := HeadlineGrantClock.physicalNeighborDistinct ring
    (bankLeaseCompleteTwoSites ring C root hc) e
  have hphys := (bankLeasePhysicalEdgeQuad ring C e hne hsp).1
  calc
    bankAgentLeaseQuad (((protocol q).step ring C e) e) =
      bankAgentLeaseQuad
        (copyBank (C e)
          (Counter.resetBankOld (C e)
            (C (ring.rightNeighbor e))).1) := hphys
    _ = bankAgentLeaseQuad
        (copyBank (C e)
          (topBoundaryBankMap (bankCell (C e) (C e).pack.val))) := by
          rw [hrow]
    _ = bankAgentLeaseQuad
        (copyBank (C e)
          (topBoundaryBankMap
            (bankLocalReferenceCell S (bankLocalReferenceTop q)))) :=
      bankLeaseCopyQuadOfCellQuad _ _ _ _ hmap
    _ = bankLocalReferenceClampedQuad q
        (topBoundaryBankMap
          (bankLocalReferenceCell S (bankLocalReferenceTop q))) :=
      bankLocalReferenceCopyQuadClamped q (C e)
         (topBoundaryBankMap
           (bankLocalReferenceCell S (bankLocalReferenceTop q)))

/-- Good incoming-root service: exact actual physical responder
equals the reference's root unary map, also at the top/root seam. -/
theorem bankLocalReferenceIncomingPhysicalCopied {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hinc : ring.rightNeighbor e = root)
    (hgood : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true) :
    bankAgentLeaseQuad (((protocol q).step ring C e) root) =
      bankLocalReferenceClampedQuad q
        (incomingRootBankMap
          (bankLocalReferenceCell S (bankLocalReferenceZero q))) := by
  have hb : 0 < (compileAdvice q).b := by
    change 0 < (compileAdvice q).s + 11
    omega
  have hrootRole : (C root).pack.val = 0 := by
    simpa only [Counter.site] using hc 0 (by omega)
  have hgoodRoot :
      goodPair (compileAdvice q).b (C e).pack (C root).pack = true := by
    simpa only [hinc] using hgood
  have hsource := bankLeaseGoodIncomingSourceRole
    (C e) (C root) hgoodRoot hrootRole
  have hrow :
      (Counter.resetBankOld (C e) (C root)).2 =
        incomingRootBankMap
          (bankCell (C root) (C root).pack.val) := by
    exact incomingRootBankSingle
      (bankCell (C e) (C e).pack.val)
      (bankCell (C root) (C root).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      hb hsource hrootRole hg
  have hv :
      bankCellLeaseQuad (bankCell (C root) (C root).pack.val) =
        bankCellLeaseQuad
          (bankLocalReferenceCell S (bankLocalReferenceZero q)) := by
    simpa only [Counter.site, bankLocalReferenceZero] using
      bankLocalReferenceCellOfMatch ring C root S hfields 0 (by omega)
  have hmap := bankLeaseIncomingMapQuad _ _ hv
  have hne := HeadlineGrantClock.physicalNeighborDistinct ring
    (bankLeaseCompleteTwoSites ring C root hc) e
  have hphys := (bankLeasePhysicalEdgeQuad ring C e hne hsp).2
  rw [hinc] at hphys
  calc
    bankAgentLeaseQuad (((protocol q).step ring C e) root) =
      bankAgentLeaseQuad
        (copyBank (C root)
          (Counter.resetBankOld (C e) (C root)).2) := hphys
    _ = bankAgentLeaseQuad
        (copyBank (C root)
          (incomingRootBankMap (bankCell (C root) (C root).pack.val))) := by
          rw [hrow]
    _ = bankAgentLeaseQuad
        (copyBank (C root)
          (incomingRootBankMap
            (bankLocalReferenceCell S (bankLocalReferenceZero q)))) :=
      bankLeaseCopyQuadOfCellQuad _ _ _ _ hmap
    _ = bankLocalReferenceClampedQuad q
        (incomingRootBankMap
          (bankLocalReferenceCell S (bankLocalReferenceZero q))) :=
      bankLocalReferenceCopyQuadClamped q (C root)
         (incomingRootBankMap
           (bankLocalReferenceCell S (bankLocalReferenceZero q)))


/-- Each protected site is either a selected internal source,
an internal target, the outgoing top source, the incoming root
target, or a full physical frame. These cases also cover the
one-letter top-to-root seam. -/
private theorem bankLocalReferenceSelectedFieldMatches {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hgood : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true)
    (i : Fin ((compileAdvice q).b + 1)) :
    bankAgentLeaseQuad
      (((protocol q).step ring C e)
        (Counter.site ring root i.val)) =
      bankLocalReferenceFieldStepClamped ring root e S i := by
  classical
  by_cases hx : i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val
  · have hphys := (bankLocalReferenceInternalPhysicalClamped
      ring C root S hsp hc hg hfields
      ⟨i.val, hx.1⟩).1
    have hlocal :
        bankLocalReferenceFieldStepClamped ring root e S i =
        bankLocalReferenceClampedQuad q
          ((bankLocalReferenceInternalPair q S ⟨i.val, hx.1⟩).1) := by
      simp only [bankLocalReferenceFieldStepClamped, dif_pos hx]
    rw [hlocal]
    calc
      bankAgentLeaseQuad
          (((protocol q).step ring C e)
            (Counter.site ring root i.val)) =
        bankAgentLeaseQuad
          (((protocol q).step ring C
            (Counter.site ring root i.val))
            (Counter.site ring root i.val)) :=
          congrArg (fun a : Fin n =>
            bankAgentLeaseQuad
              (((protocol q).step ring C a)
                (Counter.site ring root i.val))) hx.2
      _ = bankLocalReferenceClampedQuad q
          ((bankLocalReferenceInternalPair q S
            ⟨i.val, hx.1⟩).1) := hphys
  · by_cases hy : 0 < i.val ∧
        e = Counter.site ring root (i.val - 1)
    · have hjlt : i.val - 1 < (compileAdvice q).b := by omega
      have hphys := (bankLocalReferenceInternalPhysicalClamped
        ring C root S hsp hc hg hfields
        ⟨i.val - 1, hjlt⟩).2
      have hindex : i.val - 1 + 1 = i.val := by omega
      have hsite :
          ring.rightNeighbor
            (Counter.site ring root (i.val - 1)) =
              Counter.site ring root i.val := by
        change Counter.site ring root (i.val - 1 + 1) =
          Counter.site ring root i.val
        rw [hindex]
      have hlocal :
          bankLocalReferenceFieldStepClamped ring root e S i =
          bankLocalReferenceClampedQuad q
            ((bankLocalReferenceInternalPair q S
              ⟨i.val - 1, hjlt⟩).2) := by
        simp only [bankLocalReferenceFieldStepClamped,
          dif_neg hx, dif_pos hy]
      rw [hlocal]
      have hsource :
          bankAgentLeaseQuad
            (((protocol q).step ring C e)
              (Counter.site ring root i.val)) =
          bankAgentLeaseQuad
            (((protocol q).step ring C
              (Counter.site ring root (i.val - 1)))
              (Counter.site ring root i.val)) :=
        congrArg (fun a : Fin n =>
          bankAgentLeaseQuad
            (((protocol q).step ring C a)
              (Counter.site ring root i.val))) hy.2
      have htarget :
          bankAgentLeaseQuad
            (((protocol q).step ring C
              (Counter.site ring root (i.val - 1)))
              (Counter.site ring root i.val)) =
          bankLocalReferenceClampedQuad q
            ((bankLocalReferenceInternalPair q S
              ⟨i.val - 1, hjlt⟩).2) := by
        simpa only [hsite] using hphys
      exact hsource.trans htarget
    · by_cases ht : i.val = (compileAdvice q).b ∧
          e = Counter.site ring root (compileAdvice q).b
      · have hphys := bankLocalReferenceTopPhysicalCopied
          ring C root e S hsp hc hfields ht.2 hgood
        have hlocal :
            bankLocalReferenceFieldStepClamped ring root e S i =
            bankLocalReferenceClampedQuad q
              (topBoundaryBankMap (bankLocalReferenceCell S i)) := by
          simp only [bankLocalReferenceFieldStepClamped,
            dif_neg hx, dif_neg hy, dif_pos ht]
        have hi : i = bankLocalReferenceTop q := by
          apply Fin.ext
          exact ht.1
        rw [hlocal, hi]
        have hsiteTop :
            Counter.site ring root
              (bankLocalReferenceTop q).val = e := by
          change Counter.site ring root (compileAdvice q).b = e
          exact ht.2.symm
        rw [hsiteTop]
        exact hphys
      · by_cases hr : i.val = 0 ∧
            ring.rightNeighbor e = root
        · have hphys := bankLocalReferenceIncomingPhysicalCopied
            ring C root e S hsp hc hg hfields hr.2 hgood
          have hlocal :
              bankLocalReferenceFieldStepClamped ring root e S i =
              bankLocalReferenceClampedQuad q
                (incomingRootBankMap (bankLocalReferenceCell S i)) := by
            simp only [bankLocalReferenceFieldStepClamped,
              dif_neg hx, dif_neg hy, dif_neg ht, dif_pos hr]
          have hi : i = bankLocalReferenceZero q := by
            apply Fin.ext
            exact hr.1
          have hsi : Counter.site ring root i.val = root := by
            rw [hr.1]
            rfl
          rw [hlocal, hi]
          simpa only [bankLocalReferenceZero, Counter.site] using hphys
        · have hnotx :
              Counter.site ring root i.val ≠ e := by
            intro he
            by_cases ilt : i.val < (compileAdvice q).b
            · exact hx ⟨ilt, he.symm⟩
            · have hitop : i.val = (compileAdvice q).b := by
                have hiBound := i.isLt
                omega
              have heTop :
                  e = Counter.site ring root (compileAdvice q).b := by
                calc
                  e = Counter.site ring root i.val := he.symm
                  _ = Counter.site ring root
                        (compileAdvice q).b := by
                    rw [hitop]
              exact ht ⟨hitop, heTop⟩
          have hnoty :
              Counter.site ring root i.val ≠
                ring.rightNeighbor e := by
            intro he
            by_cases hz : i.val = 0
            · have hroot : ring.rightNeighbor e = root := by
                rw [hz] at he
                change root = ring.rightNeighbor e at he
                exact he.symm
              exact hr ⟨hz, hroot⟩
            · have hindex : i.val - 1 + 1 = i.val := by omega
              have htarget :
                  ring.rightNeighbor e =
                    Counter.site ring root (i.val - 1 + 1) := by
                rw [hindex]
                exact he.symm
              have hprev := Counter.resetTrialSitePredecessor
                ring root e (i.val - 1) htarget
              exact hy ⟨by omega, hprev⟩
          have hframe := Counter.step_frame ring C e
            (Counter.site ring root i.val) hnotx hnoty
          have hlocal :
              bankLocalReferenceFieldStepClamped ring root e S i =
                S.fields i := by
            simp only [bankLocalReferenceFieldStepClamped,
              dif_neg hx, dif_neg hy, dif_neg ht, dif_neg hr]
          have hfieldsI :
              bankAgentLeaseQuad
                (C (Counter.site ring root i.val)) =
                  S.fields i := by
            have hh := hfields i.val (by omega)
            have hfin :
                (⟨i.val, Nat.lt_succ_of_le (by omega)⟩ :
                  Fin ((compileAdvice q).b + 1)) = i := by
              apply Fin.ext
              rfl
            rw [hfin] at hh
            exact hh
          calc
            bankAgentLeaseQuad
                (((protocol q).step ring C e)
                  (Counter.site ring root i.val)) =
              bankAgentLeaseQuad
                (C (Counter.site ring root i.val)) :=
              congrArg bankAgentLeaseQuad hframe
            _ = S.fields i := hfieldsI
            _ = bankLocalReferenceFieldStepClamped ring root e S i :=
              hlocal.symm

/-- One actual full-protocol service agrees with the stopped local
BANK reference before success, on all protected four-field slots. -/
theorem bankLocalReferenceSupportStepFieldsAgree {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hfalse : S.success = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry ring C root e) :
    bankLocalReferenceFieldsAgree ring
      ((protocol q).step ring C e) root
      (bankLocalReferenceStepClamped ring root S e) := by
  classical
  by_cases hs : Counter.Support q ring root e
  · have hgood :=
      (bankLeaseNoDefectGuard ring C root e hs hno).1
    intro j hj
    have hp := bankLocalReferenceSelectedFieldMatches ring C
      root e S hsp hc hg hfields hgood
      (⟨j, Nat.lt_succ_of_le hj⟩)
    have hstep :
        (bankLocalReferenceStepClamped ring root S e).fields
          ⟨j, Nat.lt_succ_of_le hj⟩ =
        bankLocalReferenceFieldStepClamped ring root e S
          ⟨j, Nat.lt_succ_of_le hj⟩ := by
      simp [bankLocalReferenceStepClamped, hs, hfalse]
    exact hp.trans hstep.symm
  · exact bankLocalReferenceOutsideStepAgreesClamped
      ring C root e S hfields hs

/-- The exact one-step physical/reference field-and-latch bridge,
also preserving the complete role interval after no defect. -/
theorem bankLocalReferenceSupportStep {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (hfields : bankLocalReferenceFieldsAgree ring C root S)
    (hfalse : S.success = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry ring C root e) :
    bankLocalReferenceFieldsAgree ring
      ((protocol q).step ring C e) root
      (bankLocalReferenceStepClamped ring root S e) ∧
    Counter.Complete ring ((protocol q).step ring C e) root ∧
    (bankLocalReferenceStepClamped ring root S e).success =
      bankLocalReferenceRealSuccessEvent ring root C e := by
  exact ⟨bankLocalReferenceSupportStepFieldsAgree ring C root e S
      hsp hc hg hfields hfalse hno,
    (by
      have hstable :=
        Counter.resetClockBankStableOfNoDefect ring C root e hno
      intro j hj
      rw [hstable j hj]
      exact hc j hj),
    bankLocalReferenceLatchStepMatchesRealClamped
      ring C root e S hc hg hfields hfalse⟩

end GrantBankReference
end L3

/-!
First-success word coupling and finite survival mass transfer
for the physical-copy-clamped BANK reference.

The final-letter theorem uses
a success-free proper prefix: it does not assume the reference
continues following the physical fields after its latch is set.
-/

namespace L3
namespace GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-- No nominated-root BANK success occurs at any OLD-state
service in the word. In the final-letter theorem this predicate
is imposed only on the proper prefix, not on the last service. -/
def bankLocalReferenceNoRootSuccessWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.Config q n → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      bankLocalReferenceRealSuccessEvent ring root C e = false ∧
      bankLocalReferenceNoRootSuccessWord ring root
        ((protocol q).step ring C e) es

/-- A wholly success-free real word maintains the entire protected
four-field coupling and real PACK completeness; the clamped
reference latch is still false at the final cut. The assumptions
track grant-freedom and supported defects at their actual adapted
cuts, including unsupported scheduler letters. -/
theorem bankLocalReferenceNoSuccessWordCouplingClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (w : List (Fin n)) (C : Counter.Config q n)
      (S : BankLocalReference (compileAdvice q).b),
      Counter.Complete ring C root →
      Counter.GrantFreeWord ring root C w →
      HeadlineGrantClock.NoSupportedDefectWord ring root C w →
      bankLocalReferenceFieldsAgree ring C root S →
      S.success = false →
      bankLocalReferenceNoRootSuccessWord ring root C w →
      bankLocalReferenceFieldsAgree ring
        (Counter.Word ring w C) root
        (bankLocalReferenceWordClamped ring root w S) ∧
      Counter.Complete ring (Counter.Word ring w C) root ∧
      (bankLocalReferenceWordClamped ring root w S).success = false := by
  intro w
  induction w with
  | nil =>
      intro C S hc _ _ hfields hfalse _
      exact ⟨hfields, hc, hfalse⟩
  | cons e es ih =>
      intro C S hc hgrant hdefect hfields hfalse hnone
      have hstep := bankLocalReferenceSupportStep
        ring C root e S hsp hc hgrant.1 hfields hfalse hdefect.1
      have hnextFalse :
          (bankLocalReferenceStepClamped ring root S e).success =
            false :=
        hstep.2.2.trans hnone.1
      exact ih ((protocol q).step ring C e)
        (bankLocalReferenceStepClamped ring root S e)
        hstep.2.1 hgrant.2 hdefect.2 hstep.1 hnextFalse hnone.2

/-- The requested nonempty-word coupling. All real letters,
including the final one, are defect-free and the entire word
has the stated GrantFreeWord condition. Only the proper prefix
is required to have no nominated-root success. The last latch
is true exactly when the actual last OLD-state root comparison
succeeds. The field and completeness conclusions also hold
at the post-last physical cut, without a post-success
grant-freedom requirement in the one-step lemma. -/
theorem bankLocalReferenceFinalLetterSuccessClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (pre : List (Fin n)) (last : Fin n)
      (C : Counter.Config q n)
      (S : BankLocalReference (compileAdvice q).b),
      Counter.Complete ring C root →
      Counter.GrantFreeWord ring root C (pre ++ [last]) →
      HeadlineGrantClock.NoSupportedDefectWord ring root C
        (pre ++ [last]) →
      bankLocalReferenceFieldsAgree ring C root S →
      S.success = false →
      bankLocalReferenceNoRootSuccessWord ring root C pre →
      bankLocalReferenceFieldsAgree ring
        (Counter.Word ring (pre ++ [last]) C) root
        (bankLocalReferenceWordClamped ring root (pre ++ [last]) S) ∧
      Counter.Complete ring
        (Counter.Word ring (pre ++ [last]) C) root ∧
      ((bankLocalReferenceWordClamped ring root
          (pre ++ [last]) S).success = true ↔
        bankLocalReferenceRealSuccessEvent ring root
          (Counter.Word ring pre C) last = true) := by
  intro pre
  induction pre with
  | nil =>
      intro last C S hc hgrant hdefect hfields hfalse _
      have hstep := bankLocalReferenceSupportStep
        ring C root last S hsp hc hgrant.1 hfields
        hfalse hdefect.1
      refine ⟨hstep.1, hstep.2.1, ?_⟩
      change (bankLocalReferenceStepClamped ring root S last).success =
        true ↔ bankLocalReferenceRealSuccessEvent ring root C last = true
      rw [hstep.2.2]
  | cons e es ih =>
      intro last C S hc hgrant hdefect hfields hfalse hnone
      have hstep := bankLocalReferenceSupportStep
        ring C root e S hsp hc hgrant.1 hfields
        hfalse hdefect.1
      have hnextFalse :
          (bankLocalReferenceStepClamped ring root S e).success =
            false :=
        hstep.2.2.trans hnone.1
      exact ih last ((protocol q).step ring C e)
        (bankLocalReferenceStepClamped ring root S e)
        hstep.2.1 hgrant.2 hdefect.2 hstep.1 hnextFalse hnone.2

/-- Word concatenation for the stopped clamped reference, needed
to express prefix survival in the survival-product consumer. -/
theorem bankLocalReferenceWordAppendClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (u v : List (Fin n))
      (S : BankLocalReference (compileAdvice q).b),
      bankLocalReferenceWordClamped ring root (u ++ v) S =
      bankLocalReferenceWordClamped ring root v
        (bankLocalReferenceWordClamped ring root u S) := by
  intro u
  induction u with
  | nil =>
      intro v S
      rfl
  | cons e es ih =>
      intro v S
      change bankLocalReferenceWordClamped ring root
          (es ++ v) (bankLocalReferenceStepClamped ring root S e) =
        bankLocalReferenceWordClamped ring root v
          (bankLocalReferenceWordClamped ring root es
            (bankLocalReferenceStepClamped ring root S e))
      exact ih v _

/-- The clamped reference is absorbing once its success latch is
true; this includes the field array, not just the latch. -/
theorem bankLocalReferenceLatchedStepClamped {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (h : S.success = true) :
    bankLocalReferenceStepClamped ring root S e = S := by
  classical
  by_cases hs : Counter.Support q ring root e
  · simp [bankLocalReferenceStepClamped, hs, h]
  · simp [bankLocalReferenceStepClamped, hs]

theorem bankLocalReferenceLatchedWordClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n))
      (S : BankLocalReference (compileAdvice q).b),
      S.success = true →
      bankLocalReferenceWordClamped ring root w S = S := by
  intro w
  induction w with
  | nil =>
      intro S _
      rfl
  | cons e es ih =>
      intro S h
      change bankLocalReferenceWordClamped ring root es
        (bankLocalReferenceStepClamped ring root S e) = S
      rw [bankLocalReferenceLatchedStepClamped ring root e S h]
      exact ih S h

/-- Boolean survival of the stopped clamped reference. Its input
word will be the filtered support word in the mass comparison. -/
noncomputable def bankLocalReferenceSurvivesClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (w : List (Fin n)) : Bool :=
  decide ((bankLocalReferenceWordClamped ring root w S).success = false)

/-- Prefix survival: a successful latch cannot revert to false
during any continuation. This is the individual PrefixSurvival
premise used by the discrete survival-product lemma. -/
theorem bankLocalReferencePrefixSurvivesClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b) :
    ∀ (u v : List (Fin n)),
      bankLocalReferenceSurvivesClamped ring root S (u ++ v) = true →
      bankLocalReferenceSurvivesClamped ring root S u = true := by
  intro u v h
  cases hp : (bankLocalReferenceWordClamped ring root u S).success with
  | false =>
      simp [bankLocalReferenceSurvivesClamped, hp]
  | true =>
      have hlatched := bankLocalReferenceLatchedWordClamped
        ring root v (bankLocalReferenceWordClamped ring root u S) hp
      have hfull :
          (bankLocalReferenceWordClamped ring root (u ++ v) S).success =
            true := by
        rw [bankLocalReferenceWordAppendClamped ring root u v S,
          hlatched]
        exact hp
      have hbad :
          bankLocalReferenceSurvivesClamped ring root S (u ++ v) =
            false := by
        simp [bankLocalReferenceSurvivesClamped, hfull]
      rw [hbad] at h
      cases h

/-- The real safe event includes a grant-free root at every cut,
no supported defect at each old service, and no nominated-root
BANK success at any service. -/
def bankLocalReferenceSafeWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (w : List (Fin n)) : Prop :=
  Counter.GrantFreeWord ring root C w ∧
  HeadlineGrantClock.NoSupportedDefectWord ring root C w ∧
  bankLocalReferenceNoRootSuccessWord ring root C w

open Classical in
/-- Unnormalized mass of T-letter actual scheduler words satisfying
the three real adapted-path safety predicates. -/
noncomputable def bankLocalReferenceSafeWordMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (T : Nat) : Nat :=
  L3.Prob.scheduleSum n T
    (fun w => if bankLocalReferenceSafeWord ring root C w then 1 else 0)

/-- Unnormalized reference survival mass on the boundary-inclusive
support subword. This is definitionally the localSurvivalMass shape
after unfolding the support filter. -/
noncomputable def bankLocalReferenceClampedSupportSurvivalMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (T : Nat) : Nat :=
  L3.Prob.scheduleSum n T
    (fun w =>
      if bankLocalReferenceSurvivesClamped ring root S
          (bankLocalReferenceSupportSubword (q := q) ring root w)
      then 1 else 0)

/-- The finite uniform scheduler sum is monotone under a
pointwise inequality of nonnegative integer word weights. -/
private theorem bankLocalReferenceOfFnSumLe :
    ∀ {m : Nat} (f g : Fin m → Nat), (∀ i, f i ≤ g i) →
      (List.ofFn f).sum ≤ (List.ofFn g).sum
  | 0, _, _, _ => by simp
  | _ + 1, f, g, h => by
      rw [List.ofFn_succ, List.ofFn_succ, List.sum_cons, List.sum_cons]
      exact Nat.add_le_add (h 0)
        (bankLocalReferenceOfFnSumLe _ _ (fun i => h i.succ))

private theorem bankLocalReferenceScheduleSumMono
    (n T : Nat) (f g : List (Fin n) → Nat)
    (h : ∀ w, f w ≤ g w) :
    L3.Prob.scheduleSum n T f ≤ L3.Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f ≤
    FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact bankLocalReferenceOfFnSumLe _ _ (fun i => h _)

open Classical in
/-- Actual safe words are pointwise contained in the support-filtered
survival event of the clamped reference. In particular no
outside-support physical information enters the right-hand side. -/
private theorem bankLocalReferenceSafeWeightLeClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root)
    (w : List (Fin n)) :
    (if bankLocalReferenceSafeWord ring root C w then 1 else 0) ≤
      (if bankLocalReferenceSurvivesClamped ring root
          (bankLocalReferenceStart ring root C)
          (bankLocalReferenceSupportSubword (q := q) ring root w)
        then 1 else 0) := by
  classical
  by_cases hsafe : bankLocalReferenceSafeWord ring root C w
  · have hgrant : Counter.GrantFreeWord ring root C w := hsafe.1
    have hdefect :
        HeadlineGrantClock.NoSupportedDefectWord ring root C w :=
      hsafe.2.1
    have hnone : bankLocalReferenceNoRootSuccessWord ring root C w :=
      hsafe.2.2
    have hcouple := bankLocalReferenceNoSuccessWordCouplingClamped
      ring root hsp w C (bankLocalReferenceStart ring root C)
      hc hgrant hdefect (bankLocalReferenceStartAgrees ring C root)
      rfl hnone
    have hlocality := bankLocalReferenceWordLocalityClamped
      ring root w (bankLocalReferenceStart ring root C)
    have hsurvival :
        (bankLocalReferenceWordClamped ring root
          (bankLocalReferenceSupportSubword (q := q) ring root w)
          (bankLocalReferenceStart ring root C)).success = false := by
      rw [hlocality]
      exact hcouple.2.2
    have hsurvives :
        bankLocalReferenceSurvivesClamped ring root
          (bankLocalReferenceStart ring root C)
          (bankLocalReferenceSupportSubword (q := q) ring root w) =
            true := by
      simp [bankLocalReferenceSurvivesClamped, hsurvival]
    simp [hsafe, hsurvives]
  · simp [hsafe]

/-- First-success time transfer for EVERY horizon T, as an exact
inequality of unnormalized word masses. Uniform IID probability
follows by division by n^T (when n > 0); the right side has the
local support-product consumer's filtration shape. -/
theorem bankLocalReferenceSafeMassLeClamped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Counter.Complete ring C root) (T : Nat) :
    bankLocalReferenceSafeWordMass ring root C T ≤
      bankLocalReferenceClampedSupportSurvivalMass ring root
        (bankLocalReferenceStart ring root C) T := by
  unfold bankLocalReferenceSafeWordMass
    bankLocalReferenceClampedSupportSurvivalMass
  exact bankLocalReferenceScheduleSumMono n T _ _
    (fun w => bankLocalReferenceSafeWeightLeClamped
      ring root C hsp hc w)

end GrantBankReference
end L3
