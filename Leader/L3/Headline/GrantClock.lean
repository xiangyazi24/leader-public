import Leader.L3.Headline.Grant
import Leader.L3.Bank.CounterCold

/-!
The first physical real/frozen BANK coupling interfaces.

The one-step and conditional finite-word
lemmas use the actual protocol and the actual Counter.resetBankOld.
They do not claim that defect avoidance alone supplies the required
boundary compatibility. That remaining statement is only a Prop.
-/

namespace L3
namespace HeadlineGrantClock

set_option autoImplicit false
set_option Elab.async false

/-- A directed edge has different endpoints for n >= 2. -/
theorem physicalNeighborDistinct {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro he
  have hv := congrArg Fin.val he
  rw [rightNeighbor_val] at hv
  by_cases hsmall : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hsmall] at hv
    omega
  · have hlast : e.val + 1 = n := by
      have hbound := e.isLt
      omega
    rw [hlast, Nat.mod_self] at hv
    have hbound := e.isLt
    omega

/-- From the physical edge-geometry trichotomy. -/
theorem outsideOfNotSupported {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (h : ¬ Counter.Support q ring root e) :
    Counter.OutsideSites q ring root e := by
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hincoming | houtside
  · exact False.elim (h (Or.inr hsource))
  · exact False.elim (h (Or.inl hincoming))
  · exact houtside

/-- Equality of the actual mode/bit/tok triples of sites 0,...,b.
This view makes no assertion about numeric worker ancestry. -/
def BankViewEqual {n q : Nat}
    (ring : DirectedRing n) (C F : Counter.Config q n)
    (root : Fin n) : Prop :=
  ∀ j : Nat, j ≤ (compileAdvice q).b →
    Counter.resetAgentBankTrip
      (C (Counter.site ring root j)) =
    Counter.resetAgentBankTrip
      (F (Counter.site ring root j))

/-- An edge outside the inclusive support frames every actual
root/digit site on the full physical protocol. -/
theorem outsideSupportedBankFrame {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (hout : ¬ Counter.Support q ring root e) :
    BankViewEqual ring ((protocol q).step ring C e) C root := by
  intro j hj
  have hf := Counter.outside_frame ring C root e
    (outsideOfNotSupported ring root e hout) j hj
  exact congrArg
    (fun a : Agent (compileAdvice q) =>
      Counter.resetAgentBankTrip a) hf

/-- If the two literal OLD BANK cells agree, then the full OLD
BANK-pair output agrees. This includes roles, grants and leases. -/
theorem oldBankPairOfCells {c : Compiled}
    (x y u v : Agent c)
    (hx : bankCell x x.pack.val = bankCell u u.pack.val)
    (hy : bankCell y y.pack.val = bankCell v v.pack.val) :
    Counter.resetBankOld x y = Counter.resetBankOld u v := by
  change
    bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext (bankCell x x.pack.val).role
        (bankCell y y.pack.val).role c.b) c.b c.theta =
    bankPair (bankCell u u.pack.val) (bankCell v v.pack.val)
      (packNext (bankCell u u.pack.val).role
        (bankCell v v.pack.val).role c.b) c.b c.theta
  rw [hx, hy]

/-- The first-match physical BANK rows propagate the local view
when their actual selected OLD BANK output agrees. Unselected
protected sites are framed by Counter.step_frame. -/
theorem selectedPhysicalBankCongruence {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (C F : Counter.Config q n) (root e : Fin n)
    (hview : BankViewEqual ring C F root)
    (hpair : Counter.resetBankOld
        (C e) (C (ring.rightNeighbor e)) =
      Counter.resetBankOld
        (F e) (F (ring.rightNeighbor e))) :
    BankViewEqual ring
      ((protocol q).step ring C e)
      ((protocol q).step ring F e) root := by
  have hne := physicalNeighborDistinct ring hn e
  have hC := Counter.resetPhysicalEdgeBankTrip ring C e hne hsp
  have hF := Counter.resetPhysicalEdgeBankTrip ring F e hne hsp
  have hleft := congrArg
    (fun p : BankCell × BankCell =>
      Counter.resetCellBankTrip p.1) hpair
  have hright := congrArg
    (fun p : BankCell × BankCell =>
      Counter.resetCellBankTrip p.2) hpair
  intro j hj
  by_cases hsource : Counter.site ring root j = e
  · have hh :
        Counter.resetAgentBankTrip
          (((protocol q).step ring C e) e) =
        Counter.resetAgentBankTrip
          (((protocol q).step ring F e) e) :=
      hC.1.trans (hleft.trans hF.1.symm)
    simpa only [hsource] using hh
  · by_cases htarget :
        Counter.site ring root j = ring.rightNeighbor e
    · have hh :
          Counter.resetAgentBankTrip
            (((protocol q).step ring C e)
              (ring.rightNeighbor e)) =
          Counter.resetAgentBankTrip
            (((protocol q).step ring F e)
              (ring.rightNeighbor e)) :=
        hC.2.trans (hright.trans hF.2.symm)
      simpa only [htarget] using hh
    · have hframeC := Counter.step_frame ring C e
        (Counter.site ring root j) hsource htarget
      have hframeF := Counter.step_frame ring F e
        (Counter.site ring root j) hsource htarget
      simpa only [hframeC, hframeF] using hview j hj

/-- Actual full protocol on an assigned support; otherwise identity.
Each frozen copy receives the same selected edge e as the real ring.
The definition alone does not give independent clocks. -/
noncomputable def FrozenStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (F : Counter.Config q n) (e : Fin n) :
    Counter.Config q n := by
  classical
  exact if h : Counter.Support q ring root e
    then (protocol q).step ring F e else F

/-- An unconditional, real/frozen FIRST-service BANK coupling from
the identical arbitrary Cartesian state. It does not freeze data
before the adapted cut, nor require arbitrary scratch to be clean. -/
theorem firstServiceFrozenCoupling {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n) :
    BankViewEqual ring
      ((protocol q).step ring C e)
      (FrozenStep ring root C e) root := by
  classical
  intro j hj
  by_cases hs : Counter.Support q ring root e
  · simp only [FrozenStep, dif_pos hs]
  · have hf := Counter.outside_frame ring C root e
      (outsideOfNotSupported ring root e hs) j hj
    have hh := congrArg
      (fun a : Agent (compileAdvice q) =>
        Counter.resetAgentBankTrip a) hf
    simpa only [FrozenStep, dif_neg hs] using hh

/-- More generally the view propagates for one selected edge
conditional on equality of its OLD physical BANK-pair outputs.
No assumption of old endpoint equality on unsupported edges. -/
theorem frozenStepOfPairCompatibility {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (C F : Counter.Config q n) (root e : Fin n)
    (hview : BankViewEqual ring C F root)
    (hpair : Counter.Support q ring root e →
      Counter.resetBankOld
        (C e) (C (ring.rightNeighbor e)) =
      Counter.resetBankOld
        (F e) (F (ring.rightNeighbor e))) :
    BankViewEqual ring
      ((protocol q).step ring C e)
      (FrozenStep ring root F e) root := by
  classical
  by_cases hs : Counter.Support q ring root e
  · have hh := selectedPhysicalBankCongruence ring hn hsp
      C F root e hview (hpair hs)
    simpa only [FrozenStep, dif_pos hs] using hh
  · intro j hj
    have hf := Counter.outside_frame ring C root e
      (outsideOfNotSupported ring root e hs) j hj
    have hh := congrArg
      (fun a : Agent (compileAdvice q) =>
        Counter.resetAgentBankTrip a) hf
    have hlocal := hh.trans (hview j hj)
    simpa only [FrozenStep, dif_neg hs] using hlocal

/-- Freeze along a finite original scheduler word. -/
noncomputable def FrozenWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → Counter.Config q n → Counter.Config q n
  | [], F => F
  | e :: es, F =>
      FrozenWord ring root es (FrozenStep ring root F e)

/-- The explicitly stronger compatibility required by the
one-service BANK-pair theorem at EACH real/frozen adapted cut. -/
noncomputable def PairCompatibleWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.Config q n → Counter.Config q n →
      List (Fin n) → Prop
  | _, _, [] => True
  | C, F, e :: es =>
      (Counter.Support q ring root e →
        Counter.resetBankOld
          (C e) (C (ring.rightNeighbor e)) =
        Counter.resetBankOld
          (F e) (F (ring.rightNeighbor e))) ∧
      PairCompatibleWord ring root
        ((protocol q).step ring C e)
        (FrozenStep ring root F e) es

/-- Exact finite-word coupling under the per-cut OLD-pair condition.
This is a genuine same-IID-word statement, NOT a proof that
a buffered, defect-free trajectory has that condition. -/
theorem frozenWordOfPairCompatibility {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (root : Fin n) :
    ∀ (w : List (Fin n)) (C F : Counter.Config q n),
      BankViewEqual ring C F root →
      PairCompatibleWord ring root C F w →
      BankViewEqual ring
        (Counter.Word ring w C)
        (FrozenWord ring root w F) root := by
  intro w
  induction w with
  | nil =>
      intro C F hview _
      exact hview
  | cons e es ih =>
      intro C F hview hcompatible
      have hfirst := frozenStepOfPairCompatibility
        ring hn hsp C F root e hview hcompatible.1
      change BankViewEqual ring
        (Counter.Word ring es ((protocol q).step ring C e))
        (FrozenWord ring root es
          (FrozenStep ring root F e)) root
      exact ih _ _ hfirst hcompatible.2

/-- An adapted path that has not serviced an actual supported defect
entry. The predicate retains ALL intermediate physical states. -/
def NoSupportedDefectWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.Config q n → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      ¬ Counter.ResetClockBankDefectEntry ring C root e ∧
      NoSupportedDefectWord ring root
        ((protocol q).step ring C e) es

/-- FIRST UNFINISHED NODE. The actual C.11-censored coupling:
a buffered complete physical support stays coupled to its frozen
same-word BANK view, until a supported defect entry or a loss of
root grant-freedom. No theorem assumes or proves this Prop.

PairCompatibleWord is intentionally NOT a premise. The exterior
endpoints of supported boundary edges need not stay identical
after unrelated physical services. Their harmlessness must come
from the literal top and incoming-root BANK rows. -/
def StageGrantFrozenBankCoupling {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat) (w : List (Fin n)),
    HeadlineGrantBufferedCounter ring C radius root →
    Counter.GrantFreeWord ring root C w →
    NoSupportedDefectWord ring root C w →
    BankViewEqual ring
      (Counter.Word ring w C)
      (FrozenWord ring root w C) root

end HeadlineGrantClock
end L3
