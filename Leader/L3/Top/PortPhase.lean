import Leader.L3.LiveTopBlocks
import Leader.L3.Top.ClockAssembly

/-!
P.2 input/carry potential and conditional finite-word drift.

The imported TopClockPortPhase has no complete root-free geometry
hypothesis. Thus the unconditional producer is not asserted here.
The literal physical row obligations are collected in
TopPortPhysicalRows. The potential bound and the stochastic
consequence of those obligations are separate results.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! P.2: all OLD qIn and qCarry states, including co-occupancy. -/

def topPortInputWeight {a : Nat} (r j : Nat) : InTok a → Nat
  | .E => 0
  | .P _ _ => r - j + 2
  | .S _ tail =>
      if tail then r - j + 1
      else if j = 0 then r + 1 else 1
  | .X => r - j

def topPortCarryWeight (r j : Nat) : QCarry → Nat
  | .OFF => 0
  | .L _ _ => r - j

def topPortSiteWeight {a : Nat} (r j : Nat)
    (input : InTok a) (carry : QCarry) : Nat :=
  topPortInputWeight r j input + topPortCarryWeight r j carry

/-- W is a sum of genuine OLD physical target-register weights,
not an invented or certified ghost configuration. -/
def topPortPotential {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Nat :=
  (List.ofFn (fun j : Fin (topClockSpan n) =>
    topPortSiteWeight (topClockSpan n) j.val
      ((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn)
      ((Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry))).sum

theorem topPortInputWeight_le {a : Nat}
    (r j : Nat) (hj : j < r) (input : InTok a) :
    topPortInputWeight r j input ≤ r - j + 2 := by
  cases input with
  | E =>
      change 0 ≤ r - j + 2
      omega
  | P value tail =>
      exact Nat.le_refl _
  | X =>
      change r - j ≤ r - j + 2
      omega
  | S value tail =>
      cases tail with
      | true =>
          change r - j + 1 ≤ r - j + 2
          omega
      | false =>
          change (if j = 0 then r + 1 else 1) ≤ r - j + 2
          split <;> omega

theorem topPortCarryWeight_le
    (r j : Nat) (carry : QCarry) :
    topPortCarryWeight r j carry ≤ r - j := by
  cases carry with
  | OFF =>
      change 0 ≤ r - j
      omega
  | L carryBit errorBit =>
      exact Nat.le_refl _

theorem topPortSiteWeight_le {a : Nat}
    (r j : Nat) (hj : j < r)
    (input : InTok a) (carry : QCarry) :
    topPortSiteWeight r j input carry ≤ 2 * (r - j) + 2 := by
  have hi := topPortInputWeight_le r j hj input
  have hc := topPortCarryWeight_le r j carry
  unfold topPortSiteWeight
  omega

/-- Sum_{0<=j<r} (2(r-j)+2) = r^2+3r. -/
private theorem topPortCapacitySum (r : Nat) :
    (List.ofFn (fun j : Fin r => 2 * (r - j.val) + 2)).sum =
      r ^ 2 + 3 * r := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      rw [List.ofFn_succ, List.sum_cons]
      change
        (2 * (r + 1) + 2) +
          (List.ofFn (fun j : Fin r =>
            2 * ((r + 1) - (j.val + 1)) + 2)).sum =
          (r + 1) ^ 2 + 3 * (r + 1)
      have htail :
          (List.ofFn (fun j : Fin r =>
            2 * ((r + 1) - (j.val + 1)) + 2)).sum =
          (List.ofFn (fun j : Fin r =>
            2 * (r - j.val) + 2)).sum := by
        apply ofFn_sum_eq
        intro j
        have hsub : (r + 1) - (j.val + 1) = r - j.val := by
          omega
        rw [hsub]
      rw [htail, ih]
      have hsq : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by
        rw [Nat.pow_two, Nat.pow_two]
        simp only [Nat.add_mul, Nat.mul_add,
          Nat.one_mul, Nat.mul_one]
        omega
      rw [hsq]
      omega

/-- The uniform W ceiling includes arbitrary forged input and
carry at the same site, with no phase or genealogy assumption. -/
theorem topPortPotential_le {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) :
    topPortPotential s Z ≤
      (topClockSpan n) ^ 2 + 3 * topClockSpan n := by
  unfold topPortPotential
  calc
    (List.ofFn (fun j : Fin (topClockSpan n) =>
      topPortSiteWeight (topClockSpan n) j.val
        ((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn)
        ((Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry))).sum ≤
      (List.ofFn (fun j : Fin (topClockSpan n) =>
        2 * (topClockSpan n - j.val) + 2)).sum := by
          apply ofFn_sum_le
          intro j
          exact topPortSiteWeight_le (topClockSpan n) j.val
            j.isLt
            ((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn)
            ((Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry)
    _ = (topClockSpan n) ^ 2 + 3 * topClockSpan n :=
      topPortCapacitySum (topClockSpan n)

theorem topPortPotentialBudget (r : Nat) :
    r ^ 2 + 3 * r + 1 ≤ topClockB r := by
  unfold topClockB
  omega

/-! The exact first-hit stopped potential and row interface. -/

private noncomputable def topPortStoppedPotential {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (Z : TopFixedTraceState n) : Nat := by
  classical
  exact if topClockStopOr ring C s (topClockPortAccepted s atom) Z
    then 0 else topPortPotential s Z + 1

private theorem topPortStoppedPotential_le {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (Z : TopFixedTraceState n) :
    topPortStoppedPotential ring C s atom Z ≤
      topPortPotential s Z + 1 := by
  classical
  unfold topPortStoppedPotential
  split <;> omega

/-- The missing literal row verification, with ALL scheduler
letters and a history-measurable selected edge. Readiness and
reachability are retained on every nonterminal successor. -/
structure TopPortPhysicalRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) where
  chosen : TopFixedTraceState n → Fin n
  frame : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) ∨
    (topClockReached ring C (topFixedTraceNext ring C Z e) ∧
      topClockPortReady s atom (topFixedTraceNext ring C Z e))
  nonincrease : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topPortPotential s (topFixedTraceNext ring C Z e) ≤
      topPortPotential s Z
  progress : ∀ Z : TopFixedTraceState n,
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z (chosen Z)) ∨
    topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
      topPortPotential s Z

/-- A chosen edge contributes precisely one to the edge sum. -/
private theorem topPortSpikeSum (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- From arbitrary nonterminal OLD rows: the sum of the
scaled potentials has the required one-edge Bellman drift. -/
private theorem topPortBellmanOfRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (rows : TopPortPhysicalRows ring C s atom) :
    ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      n + (List.ofFn (fun e : Fin n =>
        n * topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e))).sum ≤
        n * (n * topPortStoppedPotential ring C s atom Z) := by
  classical
  intro Z hreach hready hnot
  have hmono : ∀ e : Fin n,
      topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e) ≤
        topPortStoppedPotential ring C s atom Z := by
    intro e
    by_cases hstop :
        topClockStopOr ring C s (topClockPortAccepted s atom)
          (topFixedTraceNext ring C Z e)
    · simp only [topPortStoppedPotential,
        if_pos hstop, if_neg hnot]
      omega
    · have hw := rows.nonincrease Z e hreach hready hnot
      simp only [topPortStoppedPotential,
        if_neg hstop, if_neg hnot]
      omega
  have hchosen :
      topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z (rows.chosen Z)) + 1 ≤
        topPortStoppedPotential ring C s atom Z := by
    rcases rows.progress Z hreach hready hnot with hstop | hdrop
    · simp only [topPortStoppedPotential,
        if_pos hstop, if_neg hnot]
      omega
    · by_cases hstop :
          topClockStopOr ring C s (topClockPortAccepted s atom)
            (topFixedTraceNext ring C Z (rows.chosen Z))
      · simp only [topPortStoppedPotential,
          if_pos hstop, if_neg hnot]
        omega
      · simp only [topPortStoppedPotential,
          if_neg hstop, if_neg hnot]
        omega
  have hpoint : ∀ e : Fin n,
      topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e) +
          (if e = rows.chosen Z then 1 else 0) ≤
        topPortStoppedPotential ring C s atom Z := by
    intro e
    by_cases he : e = rows.chosen Z
    · subst e
      rw [if_pos rfl]
      exact hchosen
    · simpa only [if_neg he, Nat.add_zero] using hmono e
  have hsum := ofFn_sum_le
    (fun e : Fin n =>
      topPortStoppedPotential ring C s atom
        (topFixedTraceNext ring C Z e) +
        (if e = rows.chosen Z then 1 else 0))
    (fun _ : Fin n => topPortStoppedPotential ring C s atom Z)
    hpoint
  rw [ofFn_sum_add, topPortSpikeSum n (rows.chosen Z) 1,
    ofFn_sum_const] at hsum
  calc
    n + (List.ofFn (fun e : Fin n =>
        n * topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e))).sum =
      n * ((List.ofFn (fun e : Fin n =>
        topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e))).sum + 1) := by
            rw [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
            omega
    _ ≤ n * (n * topPortStoppedPotential ring C s atom Z) :=
      Nat.mul_le_mul_left n hsum

/-- The first-hit cost argument localized to the reached,
ready pre-hit carrier. No closure of the target is assumed. -/
private theorem topPortLocalFirstHitCost
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (P I : S → Prop) (phi : S → Nat)
    (hstep : ∀ x : S, ∀ e : Fin n,
      I x → ¬ P x → I (next x e) ∨ P (next x e))
    (hdrift : ∀ x : S, I x → ¬ P x →
      n + (List.ofFn (fun e : Fin n => phi (next x e))).sum ≤
        n * phi x) :
    ∀ T : Nat, ∀ x : S, I x →
      costNumerator next P x T ≤ n ^ T * phi x := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
      exact Nat.zero_le _
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · rw [costNumerator_succ next P x hp T]
        have hsum := ofFn_sum_le
          (fun e : Fin n => costNumerator next P (next x e) T)
          (fun e : Fin n => n ^ T * phi (next x e))
          (by
            intro e
            rcases hstep x e hx hp with hgood | hhit
            · exact ih (next x e) hgood
            · rw [costNumerator_terminal next P
                (next x e) hhit T]
              exact Nat.zero_le _)
        calc
          n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next x e) T)).sum ≤
            n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                n ^ T * phi (next x e))).sum :=
              Nat.add_le_add_left hsum _
          _ = n ^ T *
                (n + (List.ofFn
                  (fun e : Fin n => phi (next x e))).sum) := by
                rw [ofFn_sum_mul_left, Nat.mul_add, Nat.pow_succ]
                all_goals ac_rfl
          _ ≤ n ^ T * (n * phi x) :=
            Nat.mul_le_mul_left _ (hdrift x hx hp)
          _ = n ^ (T + 1) * phi x := by
            rw [Nat.pow_succ]
            ac_rfl

/-- Conditional P.2 expected bound: a complete OLD-row
certificate makes the original strong first-hit API available. -/
theorem topPortExpectedOfRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hn : 0 < n)
    (rows : TopPortPhysicalRows ring C s atom)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hready : topClockPortReady s atom Z) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockPortAccepted s atom))
      Z ((n * topClockB (topClockSpan n) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s (topClockPortAccepted s atom))
    hn Z (n * topClockB (topClockSpan n))).2
  have hforward : ∀ Y : TopFixedTraceState n, ∀ e : Fin n,
      (topClockReached ring C Y ∧ topClockPortReady s atom Y) →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Y →
      (topClockReached ring C (topFixedTraceNext ring C Y e) ∧
        topClockPortReady s atom (topFixedTraceNext ring C Y e)) ∨
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Y e) := by
    intro Y e hvalid hnot
    rcases rows.frame Y e hvalid.1 hvalid.2 hnot with
      hstop | hcontinue
    · exact Or.inr hstop
    · exact Or.inl hcontinue
  have hcost := topPortLocalFirstHitCost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s (topClockPortAccepted s atom))
    (fun Y : TopFixedTraceState n =>
      topClockReached ring C Y ∧ topClockPortReady s atom Y)
    (fun Y => n * topPortStoppedPotential ring C s atom Y)
    hforward
    (by
      intro Y hvalid hnot
      exact topPortBellmanOfRows ring C s atom rows
        Y hvalid.1 hvalid.2 hnot)
  have hbudget :
      topPortStoppedPotential ring C s atom Z ≤
        topClockB (topClockSpan n) := by
    have hphi := topPortStoppedPotential_le ring C s atom Z
    have hw := topPortPotential_le s Z
    have hb := topPortPotentialBudget (topClockSpan n)
    omega
  intro T
  calc
    costNumerator (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockPortAccepted s atom))
      Z T ≤
        n ^ T * (n * topPortStoppedPotential ring C s atom Z) :=
      hcost T Z ⟨hreach, hready⟩
    _ ≤ n ^ T * (n * topClockB (topClockSpan n)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n hbudget)

/-- Exactly the imported interface, conditional on a separate
actual-row certificate for every nominated packet. -/
theorem topClockPortPhaseOfRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hn : 0 < n)
    (hrows : ∀ atom : Option (DigitAtom n),
      TopPortPhysicalRows ring C s atom) :
    TopClockPortPhase ring C s := by
  intro atom Z hreach hready
  exact topPortExpectedOfRows ring C s atom hn
    (hrows atom) Z hreach hready

end L3


/-!
Literal TOP owner row branch equations, copied in locally
because the single import cannot reach TopMobileWork.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The exact OLD pair passed to CertRows.liveTopPair by
certificateStep, including the independent SI beta outputs.
The checker guards still read the original x/y beta fields. -/
def topPortLiteralTopOwner {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n) (e : Fin n) :
    TopResult (compileAdvice (ceilLogTwo n)) :=
  let c := compileAdvice (ceilLogTwo n)
  let x := D e
  let y := D (ring.rightNeighbor e)
  let post := postEInfo x y
  let ser := serializerStep c x y post
  let si := siStep c x y post ser.hard
  liveTopPair c x y si.betaX si.betaY

/-- The physical source checker fields coincide with the
exact OLD TOP owner. There is no simplification of an
abstract HeadlineConfiguration into a function. -/
theorem topPortLiteralSourceFields {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n) :
    (topFixedPublicNext ring C D e e).qIn =
        (topPortLiteralTopOwner ring D e).x.qIn ∧
    (topFixedPublicNext ring C D e e).qCarry =
        (topPortLiteralTopOwner ring D e).x.qCarry ∧
    (topFixedPublicNext ring C D e e).qOut =
        (topPortLiteralTopOwner ring D e).x.qOut := by
  have hsource := headlineRendezvousStepAtSource ring D e
  have hi := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qIn) hsource
  have hc := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry) hsource
  have ho := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qOut) hsource
  refine ⟨?_, ?_, ?_⟩
  · change ((headlinePhysicalNext ring D e) e).qIn = _
    exact hi
  · change ((headlinePhysicalNext ring D e) e).qCarry = _
    exact hc
  · change ((headlinePhysicalNext ring D e) e).qOut = _
    exact ho

/-- The analogous real responder fields. The physical
edge endpoints are distinct for n >= 2. -/
theorem topPortLiteralResponderFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n) :
    (topFixedPublicNext ring C D e
       (ring.rightNeighbor e)).qIn =
        (topPortLiteralTopOwner ring D e).y.qIn ∧
    (topFixedPublicNext ring C D e
       (ring.rightNeighbor e)).qCarry =
        (topPortLiteralTopOwner ring D e).y.qCarry ∧
    (topFixedPublicNext ring C D e
       (ring.rightNeighbor e)).qOut =
        (topPortLiteralTopOwner ring D e).y.qOut := by
  have hresponder :=
    headlineRendezvousStepAtResponder ring hn D e
  have hi := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qIn)
    hresponder
  have hc := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
    hresponder
  have ho := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qOut)
    hresponder
  refine ⟨?_, ?_, ?_⟩
  · change ((headlinePhysicalNext ring D e)
        (ring.rightNeighbor e)).qIn = _
    exact hi
  · change ((headlinePhysicalNext ring D e)
        (ring.rightNeighbor e)).qCarry = _
    exact hc
  · change ((headlinePhysicalNext ring D e)
        (ring.rightNeighbor e)).qOut = _
    exact ho

/-- All OTHER physical sites frame the three checker
private fields. The fixed-public step may restore l/u/beta/d,
so full-Agent equality with D i is not the right claim. -/
theorem topPortLiteralAwayFields {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e i : Fin n)
    (he : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    (topFixedPublicNext ring C D e i).qIn = (D i).qIn ∧
    (topFixedPublicNext ring C D e i).qCarry = (D i).qCarry ∧
    (topFixedPublicNext ring C D e i).qOut = (D i).qOut := by
  have haw := headlineRendezvousStepAway ring D e i he hy
  have hi := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qIn) haw
  have hc := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry) haw
  have ho := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qOut) haw
  refine ⟨?_, ?_, ?_⟩
  · change ((headlinePhysicalNext ring D e) i).qIn = (D i).qIn
    exact hi
  · change ((headlinePhysicalNext ring D e) i).qCarry = (D i).qCarry
    exact hc
  · change ((headlinePhysicalNext ring D e) i).qOut = (D i).qOut
    exact ho

/-! The following pure first-match QI branch lemmas return
BOTH updated endpoints. Their OLD guard hypotheses prevent
a higher-priority carry-host or root override. -/

/-- QI pending P moves into an OLD-empty internal target.
Neither P is cloned nor an old settled byte invented. -/
theorem topPortOwnerQIPendingMove
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P v tail) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .P v tail := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
      hyc,
    hxi, hyi, hyb, topTerminal, topInternal,
    topBorder, QCarry.isOff, QCarry.isL,
    InTok.isP, InTok.isS, InTok.isX, InTok.isE,
    inT, inV]

/-- QI P settles immediately before an OLD settled
internal responder. The responder's OLD S is framed. -/
theorem topPortOwnerQIPendingSettles
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v w : Fin c.topA) (tail nextTail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P v tail)
    (hyi : y.qIn = .S w nextTail)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn =
      .S v tail ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .S w nextTail := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
      hyc,
    hxi, hyi, hyb, topTerminal, topInternal,
    topBorder, QCarry.isOff, QCarry.isL,
    InTok.isP, InTok.isS, InTok.isX, InTok.isE,
    inT, inV]

/-- QI internal OLD nonborder tail becomes X, no
second X-advance microstep on the same selected edge.
This reuses the existing owner theorem. -/
theorem topPortOwnerQITailConverts
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .S v true) (hyi : y.qIn = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .X := by
  exact HeadlineDigit.checkerOwnerInternalTailBecomesX
    c x y resolvedX resolvedY v
    hxl hyl hxb hyb hxc hyc hxi hyi

/-- QI front X advances into an OLD internal S.
Its old source clears; its responder becomes X. -/
theorem topPortOwnerQIFrontAdvances
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .X) (hyi : y.qIn = .S v tail)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .X := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
      hyc,
    hxi, hyi, hyb, topInternal, topTerminal,
    QCarry.isOff, QCarry.isL, InTok.isX,
    InTok.isS, InTok.isP, inT]

/-- QI X reaching an empty internal responder retires
without conjuring a new settled input or a new front. -/
theorem topPortOwnerQIFrontDies
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .X) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .E := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
      hyc,
    hxi, hyi, hyb, topInternal, topTerminal,
    QCarry.isOff, QCarry.isL, InTok.isX,
    InTok.isS, InTok.isP]

/-- QI front merger: old source X disappears, while
the already-present resident X remains at the target. -/
theorem topPortOwnerQIFrontMerges
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .X) (hyi : y.qIn = .X)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .X := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
      hyc,
    hxi, hyi, hyb, topInternal, topTerminal,
    QCarry.isOff, QCarry.isL, InTok.isX,
    InTok.isS, InTok.isP]

/-- QI OLD carry-host cleanup wins over P settlement,
tail conversion, and all later input first-match rows. -/
theorem topPortOwnerQICarryHostClears
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .L carry error)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
      hyc,
    hyi, hyb, QCarry.isOff, QCarry.isL,
    InTok.isS, InTok.isX, InTok.isP,
    topTerminal, topInternal]

/-! QC always uses the OLD source carry and OLD destination S.
The checker carry-field lemmas are reused for its
new live values; the QI consumption must be shown separately. -/

/-- QC3: border settled S launches a carry and the
source QI slot is consumed into E on that same edge. -/
theorem topPortOwnerQCLaunch
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v tail) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).x.qCarry =
      .L (HeadlineDigit.checkerCarryNext c (true, false)
        v x.d).1
        (HeadlineDigit.checkerCarryNext c (true, false)
        v x.d).2 := by
  refine ⟨?_, ?_⟩
  · cases hyc : y.qCarry <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
          hxb, hxc, hyc,
        hxi, QCarry.isOff, QCarry.isL,
        InTok.isS, InTok.isX, inT, topBorder] <;>
      (split <;> rfl)
  · exact HeadlineDigit.checkerOwnerCarryLaunch
      c x y resolvedX resolvedY tail v
      hxl hyl hxc hxi hxb

/-- QC2 success: the OLD L is cleared, the OLD S
at the responder is consumed, and one L moves right. -/
theorem topPortOwnerQCAdvances
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error tail : Bool)
    (v : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcy : y.qCarry = .OFF)
    (hcx : x.qCarry = .L carry error)
    (hyi : y.qIn = .S v tail)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry =
      .L (HeadlineDigit.checkerCarryNext c (carry, error)
          v y.d).1
         (HeadlineDigit.checkerCarryNext c (carry, error)
          v y.d).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hcx,
      hcy,
      hyi, hyb, QCarry.isOff, QCarry.isL,
      InTok.isS, topTerminal]
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hcx,
      hcy,
      hyi, hyb, QCarry.isOff, QCarry.isL,
      InTok.isS, topTerminal]
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hcx,
      hcy,
      hyi, hyb, QCarry.isOff, QCarry.isL,
      InTok.isS, topTerminal]
  · exact HeadlineDigit.checkerOwnerCarryAdvance
      c x y resolvedX resolvedY carry error tail v
      hxl hyl hcx hcy hyi hyb

/-- QC2 abort when the old internal target input is E:
the source carry is retired and no new carry is spawned. -/
theorem topPortOwnerQCAborts
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcx : x.qCarry = .L carry error)
    (hcy : y.qCarry = .OFF) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hcx,
      hcy,
    hyi, hyb, topTerminal, QCarry.isL,
    QCarry.isOff, InTok.isS, InTok.isE]

/-- QC2 terminal: an OLD border at the responder retires
the live carry, with no continuation into the next block.
Exclude unrelated QO offers to state an E-valued responder. -/
theorem topPortOwnerQCRetires
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcx : x.qCarry = .L carry error)
    (hcy : y.qCarry = .OFF) (hyi : y.qIn = .E)
    (hyb : y.beta = true) (hqo : x.qOut = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .E := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hcx,
      hcy,
    hyi, hyb, hqo, topTerminal, QCarry.isL,
    QCarry.isOff, InTok.isS, OutTok.isD]

/-! QO uses OLD qOut and OLD target beta, and cannot
materialize or move a second packet on the same service. -/

/-- QO port: an OLD D offered to a marker-border E,
with an OFF carry, creates exactly one target P.
Additional OLD-empty source input/carry assumptions keep
this owner subcase simple; they are not universal port guards. -/
theorem topPortOwnerQOPortAccepts
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxi : x.qIn = .E) (hxc : x.qCarry = .OFF)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF)
    (hyb : y.beta = true)
    (hxo : x.qOut = .D v tail) :
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .P v tail ∧
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      (if tail then .U else .E) ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxi,
      hxc,
    hyi, hyc, hyb, hxo, QCarry.isOff,
    QCarry.isL, InTok.isS, InTok.isE,
    InTok.isX, InTok.isP, OutTok.isD,
    outT, outV, topTerminal]

/-- QO internal D movement into an OLD-empty output
slot; tail leaves U, nontail leaves E at source. -/
theorem topPortOwnerQODataMoves
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxo : x.qOut = .D v tail) (hyo : y.qOut = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      (if tail then .U else .E) ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      .D v tail := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxo,
    hyo, hyb, OutTok.isD, OutTok.isE,
    outT, outV]

/-- QO unread source samples its own OLD digit and marker,
but cannot export that new D in the same service. -/
theorem topPortOwnerQOUnreadSamples
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxo : x.qOut = .U) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      .D x.d x.beta ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
    hxo, OutTok.isD, OutTok.isU]

/-- QO empty marker produces U, not an instantly exported D. -/
theorem topPortOwnerQOMarkerBootstraps
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hxo : x.qOut = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut = .U ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
    hxo, OutTok.isD, OutTok.isU, OutTok.isE]


/-- Actual physical/fixed-public QI pending move,
including source deletion and responder arrival. -/
theorem topPortPhysicalQIPendingMove {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxc : (D e).qCarry = .OFF)
    (hyc : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hxi : (D e).qIn = .P v tail)
    (hyi : (D (ring.rightNeighbor e)).qIn = .E)
    (hyb : (D (ring.rightNeighbor e)).beta = false) :
    (topFixedPublicNext ring C D e e).qIn = .E ∧
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qIn = .P v tail := by
  have hrow :
      (topPortLiteralTopOwner ring D e).x.qIn = .E ∧
      (topPortLiteralTopOwner ring D e).y.qIn =
        .P v tail := by
    unfold topPortLiteralTopOwner
    exact topPortOwnerQIPendingMove _ _ _ _ _ v tail
      hxl hyl hxc hyc hxi hyi hyb
  have hx := topPortLiteralSourceFields ring C D e
  have hy := topPortLiteralResponderFields ring hn C D e
  exact ⟨hx.1.trans hrow.1, hy.1.trans hrow.2⟩

/-- Actual QI internal tail-to-X effect on the selected
target edge; reuse HeadlineDigit's owner theorem. -/
theorem topPortPhysicalQITailConverts {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxb : (D e).beta = false)
    (hyb : (D (ring.rightNeighbor e)).beta = false)
    (hxc : (D e).qCarry = .OFF)
    (hyc : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hxi : (D e).qIn = .S v true)
    (hyi : (D (ring.rightNeighbor e)).qIn = .E) :
    (topFixedPublicNext ring C D e e).qIn = .X := by
  have hrow :
      (topPortLiteralTopOwner ring D e).x.qIn = .X := by
    unfold topPortLiteralTopOwner
    exact HeadlineDigit.checkerOwnerInternalTailBecomesX
      _ _ _ _ _ v
      hxl hyl hxb hyb hxc hyc hxi hyi
  exact (topPortLiteralSourceFields ring C D e).1.trans hrow

/-- Exact QC3 fresh carry field in the real fixed-public
shadow, with both OLD physical-root guards. -/
theorem topPortPhysicalQCLaunch {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (tail : Bool)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxc : (D e).qCarry = .OFF)
    (hxi : (D e).qIn = .S v tail)
    (hmarker : (D e).beta = true) :
    (topFixedPublicNext ring C D e e).qCarry =
      .L (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (true, false)
        v (D e).d).1
         (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (true, false)
        v (D e).d).2 := by
  change ((headlinePhysicalNext ring D e) e).qCarry = _
  exact HeadlineDigit.checkerPhysicalCarryLaunch
    ring D e tail v hxl hyl hxc hxi hmarker

/-- Exact QC2 successful carry transfer in the real
fixed-public shadow, reading OLD settled responder. -/
theorem topPortPhysicalQCAdvance {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (carry error tail : Bool)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hcx : (D e).qCarry = .L carry error)
    (hcy : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hyi : (D (ring.rightNeighbor e)).qIn = .S v tail)
    (hyb : (D (ring.rightNeighbor e)).beta = false) :
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qCarry =
      .L (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (carry, error)
        v (D (ring.rightNeighbor e)).d).1
         (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (carry, error)
        v (D (ring.rightNeighbor e)).d).2 := by
  change ((headlinePhysicalNext ring D e)
    (ring.rightNeighbor e)).qCarry = _
  exact HeadlineDigit.checkerPhysicalCarryAdvance
    ring hn D e carry error tail v
    hxl hyl hcx hcy hyi hyb

/-- A QO source's OLD unread state sampling is a real
fixed-public field equation, not a fresh packet export. -/
theorem topPortPhysicalQOUnreadSamples {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hu : (D e).qOut = .U) :
    (topFixedPublicNext ring C D e e).qOut =
      .D (D e).d (D e).beta := by
  have hrow :
      (topPortLiteralTopOwner ring D e).x.qOut =
        .D (D e).d (D e).beta := by
    unfold topPortLiteralTopOwner
    exact (topPortOwnerQOUnreadSamples
      _ _ _ _ _ hxl hyl hu).1
  exact (topPortLiteralSourceFields ring C D e).2.2.trans hrow




/-! ## P.2 local W arithmetic for actual changing QI/QC branches -/

/-- QC3 consumes one marker-border S and creates one live carry:
both tail values have old weight r+1 and new weight r. -/
theorem topPortWeightQCLaunch {a : Nat} (r : Nat)
    (v : Fin a) (tail carry error : Bool) :
    topPortSiteWeight r 0 (.E : InTok a) (.L carry error) + 1 ≤
      topPortSiteWeight r 0 (.S v tail) .OFF := by
  cases tail <;>
    (simp [topPortSiteWeight, topPortInputWeight, topPortCarryWeight]) <;> omega

/-- An ordinary pending packet moves one step into an OLD empty,
carry-free responder and loses exactly one unit of W. -/
theorem topPortWeightQIPendingMove {a : Nat}
    (r j : Nat) (hj : j + 1 < r)
    (v : Fin a) (tail : Bool) :
    topPortSiteWeight r j (.E : InTok a) .OFF +
        topPortSiteWeight r (j + 1) (.P v tail) .OFF + 1 ≤
      topPortSiteWeight r j (.P v tail) .OFF +
        topPortSiteWeight r (j + 1) (.E : InTok a) .OFF := by
  change (0 + 0) + (r - (j + 1) + 2 + 0) + 1 ≤
    (r - j + 2 + 0) + (0 + 0)
  omega

/-- P settling before an old S loses at least one unit, including
the non-tail special weight at the border offset zero. -/
theorem topPortWeightQIPendingSettle {a : Nat}
    (r j : Nat) (hj : j < r)
    (v : Fin a) (tail : Bool) :
    topPortSiteWeight r j (.S v tail) .OFF + 1 ≤
      topPortSiteWeight r j (.P v tail) .OFF := by
  cases tail with
  | true =>
      change (r - j + 1) + 1 ≤ r - j + 2
      omega
  | false =>
      change (if j = 0 then r + 1 else 1) + 1 ≤
        r - j + 2
      split <;> omega

/-- At an interior offset an OLD settled tail becoming a front
decreases its local charge by one, without any second microstep. -/
theorem topPortWeightQITailFront {a : Nat}
    (r j : Nat) (hj : 0 < j) (hjr : j < r)
    (v : Fin a) :
    topPortSiteWeight r j (.X : InTok a) .OFF + 1 ≤
      topPortSiteWeight r j (.S v true) .OFF := by
  change r - j + 1 ≤ r - j + 1
  exact Nat.le_refl _

/-- A front clearing at a site strictly reduces the potential,
since every in-block delta is at least one. -/
theorem topPortWeightQIFrontRetire {a : Nat}
    (r j : Nat) (hj : j < r) :
    topPortSiteWeight r j (.E : InTok a) .OFF + 1 ≤
      topPortSiteWeight r j (.X : InTok a) .OFF := by
  change 0 + 1 ≤ r - j
  omega

/-- Cleaning an OLD live carry host never increases W, even if
an arbitrary inherited input co-occupied the host. -/
theorem topPortWeightQICarryHost {a : Nat}
    (r j : Nat) (input : InTok a) (carry error : Bool) :
    topPortSiteWeight r j (.E : InTok a) (.L carry error) ≤
      topPortSiteWeight r j input (.L carry error) := by
  change 0 + (r - j) ≤
    topPortInputWeight r j input + (r - j)
  exact Nat.add_le_add_right (Nat.zero_le _) _

/-- QC terminal retirement or abort clears a carry and its host
input, losing at least one unit at every target offset. -/
theorem topPortWeightQCRetire {a : Nat}
    (r j : Nat) (hj : j < r)
    (input : InTok a) (carry error : Bool) :
    topPortSiteWeight r j (.E : InTok a) .OFF + 1 ≤
      topPortSiteWeight r j input (.L carry error) := by
  have hi : 0 ≤ topPortInputWeight r j input :=
    Nat.zero_le _
  change (0 + 0) + 1 ≤
    topPortInputWeight r j input + (r - j)
  omega

/-- Successful QO port acceptance creates new pending weight r+2.
It is therefore essential to zero the STOPPED potential at this
service, rather than demand nonincrease of the raw W at success. -/
theorem topPortWeightAcceptedBirth {a : Nat}
    (r : Nat) (v : Fin a) (tail : Bool) :
    topPortSiteWeight r 0 (.P v tail) .OFF =
      topPortSiteWeight r 0 (.E : InTok a) .OFF + (r + 2) := by
  simp [topPortSiteWeight, topPortInputWeight, topPortCarryWeight]

/-! ## P.1 eligible geometry (source/target markers and leaders) -/

theorem topPortEligibleFollower {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (k : Nat) (hk : k < 2 * topClockSpan n + 1) :
    (C (certSite s k)).l = false := by
  have hroot :
      certFollowerArc (HeadlineDigit.publicWord C) s
        (2 * topClockSpan n + 1) :=
    hbad.1.2.2.2.1
  exact hroot ⟨k, hk⟩

theorem topPortEligibleTargetMarker {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    (C (certSite s (topClockSpan n))).beta = true := by
  exact hbad.1.2.1

theorem topPortEligibleTargetInteriorMarker {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (j : Fin (topClockSpan n)) (hj : 0 < j.val) :
    (C (certSite s (topClockSpan n + j.val))).beta = false := by
  have hmarker := hbad.1.2.2.2.2.2 j hj
  rw [certSite_add] at hmarker
  exact hmarker

/-- One-step fixed-public restoration is independent of all
arbitrary private comparison scratch. -/
theorem topPortFixedPublicMaskStep {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e i : Fin n) :
    ((topFixedTraceNext ring C Z e).1.1 i).l = (C i).l ∧
    ((topFixedTraceNext ring C Z e).1.1 i).beta = (C i).beta := by
  exact ⟨rfl, rfl⟩

/-!
The local owner equations and local W decreases are not an
exhaustive selected-edge proof. The global source-packet retention,
OLD QI/QC simultaneous update, output-export receipt and
rightmost-obstruction choice remain open. No false instance of
TopPortPhysicalRows is asserted here.
-/

end L3


/-!
Finite-support patch accounting for the TOP port potential.

The outstanding literal-row classification is isolated as
TopPortCombinedEndpointRowBound below.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## Generic one- and two-index finite-sum replacement -/

/-- Replacing the value at one Fin index is balanced by adding the
opposite old value. -/
private theorem topPortSumOneSwap {m : Nat}
    (f g : Fin m → Nat) (i : Fin m)
    (hframe : ∀ j : Fin m, j ≠ i → g j = f j) :
    (List.ofFn g).sum + f i = (List.ofFn f).sum + g i := by
  have hpoint : ∀ j : Fin m,
      g j + (if j = i then f i else 0) =
      f j + (if j = i then g i else 0) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [if_pos rfl, if_true, ↓reduceIte]
      omega
    · simp only [if_neg hj, Nat.add_zero]
      exact hframe j hj
  have heq := ofFn_sum_eq
    (fun j : Fin m => g j + (if j = i then f i else 0))
    (fun j : Fin m => f j + (if j = i then g i else 0))
    hpoint
  simpa only [ofFn_sum_add, topPortSpikeSum] using heq

/-- Exact patching when the two changed indices are distinct. -/
private theorem topPortSumDistinctSwap {m : Nat}
    (f g : Fin m → Nat) (i k : Fin m)
    (hneq : i ≠ k)
    (hframe : ∀ j : Fin m, j ≠ i → j ≠ k → g j = f j) :
    (List.ofFn g).sum + (f i + f k) =
      (List.ofFn f).sum + (g i + g k) := by
  have hpoint : ∀ j : Fin m,
      (g j + (if j = i then f i else 0)) +
          (if j = k then f k else 0) =
      (f j + (if j = i then g i else 0)) +
          (if j = k then g k else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [if_pos rfl, if_true, ↓reduceIte, if_neg hneq, Nat.add_zero]
      omega
    · by_cases hjk : j = k
      · subst j
        have hki : k ≠ i := Ne.symm hneq
        simp only [if_neg hki, if_pos rfl, if_true, ↓reduceIte, Nat.add_zero]
        omega
      · simpa only [if_neg hji, if_neg hjk, Nat.add_zero]
          using (hframe j hji hjk)
  have heq := ofFn_sum_eq
    (fun j : Fin m =>
      (g j + (if j = i then f i else 0)) +
        (if j = k then f k else 0))
    (fun j : Fin m =>
      (f j + (if j = i then g i else 0)) +
        (if j = k then g k else 0))
    hpoint
  simpa only [ofFn_sum_add, topPortSpikeSum, Nat.add_assoc]
    using heq

/-- Count a coincident index only once. The published two-site
formula without this branch would be false for i=k. -/
theorem topPortSumTwoSwap {m : Nat}
    (f g : Fin m → Nat) (i k : Fin m)
    (hframe : ∀ j : Fin m, j ≠ i → j ≠ k → g j = f j) :
    (List.ofFn g).sum +
        (if i = k then f i else f i + f k) =
      (List.ofFn f).sum +
        (if i = k then g i else g i + g k) := by
  by_cases he : i = k
  · subst k
    simp only [if_pos rfl]
    exact topPortSumOneSwap f g i
      (by intro j hj; exact hframe j hj hj)
  · simp only [if_neg he]
    exact topPortSumDistinctSwap f g i k he hframe

/-- Nonincrease at the one or two supported indices implies
nonincrease of the full unweighted finite sum. -/
theorem topPortSumTwoLe {m : Nat}
    (f g : Fin m → Nat) (i k : Fin m)
    (hframe : ∀ j : Fin m, j ≠ i → j ≠ k → g j = f j)
    (hlocal :
      (if i = k then g i else g i + g k) ≤
      (if i = k then f i else f i + f k)) :
    (List.ofFn g).sum ≤ (List.ofFn f).sum := by
  have hbalance := topPortSumTwoSwap f g i k hframe
  have hbound :
      (List.ofFn g).sum +
          (if i = k then f i else f i + f k) ≤
        (List.ofFn f).sum +
          (if i = k then f i else f i + f k) := by
    calc
      (List.ofFn g).sum +
          (if i = k then f i else f i + f k) =
        (List.ofFn f).sum +
          (if i = k then g i else g i + g k) := hbalance
      _ ≤ (List.ofFn f).sum +
          (if i = k then f i else f i + f k) :=
        Nat.add_le_add_left hlocal _
  omega

/-! ## Actual fixed-public locality on the cyclic target window -/

def topPortWeightAt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (j : Fin (topClockSpan n)) : Nat :=
  topPortSiteWeight (topClockSpan n) j.val
    ((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn)
    ((Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry)

theorem topPortPotentialAsSum {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) :
    topPortPotential s Z =
      (List.ofFn (topPortWeightAt s Z)).sum := by
  rfl

/-- Every other physical site frames qIn and qCarry under the
REAL topFixedTraceNext. The site is a target certSite offset. -/
theorem topPortTraceAwayChecker {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hx : certSite s (topClockSpan n + j.val) ≠ e)
    (hy : certSite s (topClockSpan n + j.val) ≠
      ring.rightNeighbor e) :
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (topClockSpan n + j.val))).qIn =
        (Z.1.1 (certSite s (topClockSpan n + j.val))).qIn ∧
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (topClockSpan n + j.val))).qCarry =
        (Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry := by
  have haway := topPortLiteralAwayFields
    ring C Z.1.1 e (certSite s (topClockSpan n + j.val))
    hx hy
  exact ⟨haway.1, haway.2.1⟩

theorem topPortWeightAtAway {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hx : certSite s (topClockSpan n + j.val) ≠ e)
    (hy : certSite s (topClockSpan n + j.val) ≠
      ring.rightNeighbor e) :
    topPortWeightAt s (topFixedTraceNext ring C Z e) j =
      topPortWeightAt s Z j := by
  have haway := topPortTraceAwayChecker
    ring C s Z e j hx hy
  unfold topPortWeightAt
  rw [haway.1, haway.2]

/-! ## One named missing combined physical row premise -/

/-- The actual first-match QI/QC joint classification still needed.
It is scoped to a complete, root-free BadCompletePair.

The two indices cover all target sites touched by the real edge,
and their combined OLD-vs-NEW W contribution is nonincreasing.
When they are the same index, that site is charged only once.

The entire port-accepting service is excluded because a new P
may increase raw W exactly when the first-hit process stops.
This is a required future producer, NOT a proved lemma. -/
def TopPortCombinedEndpointRowBound {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) : Prop :=
  HeadlineDigit.BadCompletePair C s →
  ∀ (Z : TopFixedTraceState n) (e : Fin n),
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    ∃ i k : Fin (topClockSpan n),
      (∀ j : Fin (topClockSpan n),
        (certSite s (topClockSpan n + j.val) = e ∨
          certSite s (topClockSpan n + j.val) =
            ring.rightNeighbor e) →
        j = i ∨ j = k) ∧
      (if i = k then
        topPortWeightAt s (topFixedTraceNext ring C Z e) i ≤
          topPortWeightAt s Z i
      else
        topPortWeightAt s (topFixedTraceNext ring C Z e) i +
          topPortWeightAt s (topFixedTraceNext ring C Z e) k ≤
        topPortWeightAt s Z i + topPortWeightAt s Z k)

/-- The exact TopPortPhysicalRows.nonincrease field now follows
from ONE combined endpoint-row obligation plus proven locality. -/
theorem topPortNonincreaseOfCombinedRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hrows : TopPortCombinedEndpointRowBound ring C s atom) :
    ∀ (Z : TopFixedTraceState n) (e : Fin n),
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topPortPotential s (topFixedTraceNext ring C Z e) ≤
        topPortPotential s Z := by
  intro Z e hreach hready hnot
  obtain ⟨i, k, hcover, hlocal⟩ :=
    hrows hbad Z e hreach hready hnot
  have hframe : ∀ j : Fin (topClockSpan n),
      j ≠ i → j ≠ k →
      topPortWeightAt s (topFixedTraceNext ring C Z e) j =
        topPortWeightAt s Z j := by
    intro j hji hjk
    have hx :
        certSite s (topClockSpan n + j.val) ≠ e := by
      intro he
      rcases hcover j (Or.inl he) with hfirst | hsecond
      · exact hji hfirst
      · exact hjk hsecond
    have hy :
        certSite s (topClockSpan n + j.val) ≠
          ring.rightNeighbor e := by
      intro he
      rcases hcover j (Or.inr he) with hfirst | hsecond
      · exact hji hfirst
      · exact hjk hsecond
    exact topPortWeightAtAway ring C s Z e j hx hy
  have hpair :
      (if i = k then
        topPortWeightAt s (topFixedTraceNext ring C Z e) i
      else
        topPortWeightAt s (topFixedTraceNext ring C Z e) i +
          topPortWeightAt s (topFixedTraceNext ring C Z e) k) ≤
      (if i = k then topPortWeightAt s Z i
      else topPortWeightAt s Z i + topPortWeightAt s Z k) := by
    by_cases he : i = k
    · simpa only [if_pos he] using hlocal
    · simpa only [if_neg he] using hlocal
  have hsum := topPortSumTwoLe
    (topPortWeightAt s Z)
    (topPortWeightAt s (topFixedTraceNext ring C Z e))
    i k hframe hpair
  change
    (List.ofFn (topPortWeightAt s
      (topFixedTraceNext ring C Z e))).sum ≤
    (List.ofFn (topPortWeightAt s Z)).sum
  exact hsum

end L3


/-!
Target-window geometry and exact OLD QI/QC product reduction.
The one remaining physical case partition is
TopPortFourCoordinateProduct, using the literal OLD TOP owner.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-! ## Two previously omitted simultaneous two-site W charges -/

/-- QC2 simultaneously clears the initiating carry's OLD input
and consumes a settled input at the responder. -/
theorem topPortWeightQCAdvanceJoint {a : Nat}
    (r j : Nat) (hj : j + 1 < r)
    (sourceInput : InTok a) (v : Fin a)
    (tail carry error newCarry newError : Bool) :
    topPortSiteWeight r j (.E : InTok a) .OFF +
        topPortSiteWeight r (j + 1) (.E : InTok a)
          (.L newCarry newError) + 1 ≤
      topPortSiteWeight r j sourceInput (.L carry error) +
        topPortSiteWeight r (j + 1) (.S v tail) .OFF := by
  have ht : 1 ≤ topPortInputWeight r (j + 1) (.S v tail) := by
    cases tail with
    | true =>
        change 1 ≤ r - (j + 1) + 1
        omega
    | false =>
        change 1 ≤ (if j + 1 = 0 then r + 1 else 1)
        split <;> omega
  change (0 + 0) + (0 + (r - (j + 1))) + 1 ≤
    (topPortInputWeight r j sourceInput + (r - j)) +
      (topPortInputWeight r (j + 1) (.S v tail) + 0)
  omega

/-- An OLD X consumes the responder's OLD S when moving, and
cannot clone the erasure front or increase the two-site charge. -/
theorem topPortWeightQIFrontAdvanceJoint {a : Nat}
    (r j : Nat) (hj : j + 1 < r)
    (v : Fin a) (tail : Bool) :
    topPortSiteWeight r j (.E : InTok a) .OFF +
        topPortSiteWeight r (j + 1) (.X : InTok a) .OFF + 1 ≤
      topPortSiteWeight r j (.X : InTok a) .OFF +
        topPortSiteWeight r (j + 1) (.S v tail) .OFF := by
  have ht : 1 ≤ topPortInputWeight r (j + 1) (.S v tail) := by
    cases tail with
    | true =>
        change 1 ≤ r - (j + 1) + 1
        omega
    | false =>
        change 1 ≤ (if j + 1 = 0 then r + 1 else 1)
        split <;> omega
  change (0 + 0) + (r - (j + 1) + 0) + 1 ≤
    (r - j + 0) +
      (topPortInputWeight r (j + 1) (.S v tail) + 0)
  omega

/-- A QI pending move can occur on the very same physical
interaction as QO unread sampling. Both independent effects
are retained by the one OLD liveTopPair result. -/
theorem topPortOwnerPendingMoveUnreadJoint
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P v tail) (hyi : y.qIn = .E)
    (hyb : y.beta = false) (hxo : x.qOut = .U) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .P v tail ∧
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      .D x.d x.beta := by
  have hqi := topPortOwnerQIPendingMove
    c x y resolvedX resolvedY v tail
    hxl hyl hxc hyc hxi hyi hyb
  have hqo := topPortOwnerQOUnreadSamples
    c x y resolvedX resolvedY hxl hyl hxo
  exact ⟨hqi.1, hqi.2, hqo.1⟩

/-! ## Window embedding, including the cyclic self-pair -/

/-- Production r is >=3 even for the small compiler inputs. -/
private theorem topPortSpanThreeAll (n : Nat) :
    3 ≤ topClockSpan n := by
  by_cases hn : 5 ≤ n
  · exact cert_rho_ge_three n hn
  · have hs : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      omega
    rcases hs with h | h | h | h | h
    · subst n
      unfold topClockSpan Compiled.rho
      decide +kernel
    · subst n
      unfold topClockSpan Compiled.rho
      decide +kernel
    · subst n
      unfold topClockSpan Compiled.rho
      decide +kernel
    · subst n
      unfold topClockSpan Compiled.rho
      decide +kernel
    · subst n
      unfold topClockSpan Compiled.rho
      decide +kernel

/-- If n<r, offset n inside the source block revisits its
marker, contradicting CompleteBlockPair's interior nonmarker. -/
theorem topPortSpanLeOfBad {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    topClockSpan n ≤ n := by
  by_cases hle : topClockSpan n ≤ n
  · exact hle
  · have hlt : n < topClockSpan n := by omega
    have hn : 0 < n := by
      have hs := s.isLt
      omega
    have hinside :
        certMarker (HeadlineDigit.publicWord C) (certSite s n) =
          false :=
      hbad.1.2.2.2.2.1 ⟨n, hlt⟩ hn
    rw [certSite_n s] at hinside
    rw [hbad.1.1] at hinside
    cases hinside

/-- Translation by a fixed start site is injective on offsets
strictly smaller than n. Both possible modular wraps are checked. -/
private theorem topPortCertSiteShortInj {n : Nat}
    (start : Fin n) (a b : Nat)
    (ha : a < n) (hb : b < n)
    (hsite : certSite start a = certSite start b) :
    a = b := by
  have he := congrArg Fin.val hsite
  change (start.val + a) % n = (start.val + b) % n at he
  by_cases hleft : start.val + a < n
  · rw [Nat.mod_eq_of_lt hleft] at he
    by_cases hright : start.val + b < n
    · rw [Nat.mod_eq_of_lt hright] at he
      omega
    · have hge : n ≤ start.val + b := by omega
      have hrem : start.val + b - n < n := by
        have hs := start.isLt
        omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hrem] at he
      omega
  · have hge : n ≤ start.val + a := by omega
    have hrem : start.val + a - n < n := by
      have hs := start.isLt
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hrem] at he
    by_cases hright : start.val + b < n
    · rw [Nat.mod_eq_of_lt hright] at he
      omega
    · have hge' : n ≤ start.val + b := by omega
      have hrem' : start.val + b - n < n := by
        have hs := start.isLt
        omega
      rw [Nat.mod_eq_sub_mod hge',
        Nat.mod_eq_of_lt hrem'] at he
      omega

/-- A target-window offset is unique if the complete block fits. -/
private theorem topPortTargetSiteInj {n : Nat}
    (s : Fin n) (hle : topClockSpan n ≤ n)
    (i j : Fin (topClockSpan n))
    (hsite :
      certSite s (topClockSpan n + i.val) =
        certSite s (topClockSpan n + j.val)) :
    i = j := by
  apply Fin.ext
  have hinner :
      certSite (certSite s (topClockSpan n)) i.val =
        certSite (certSite s (topClockSpan n)) j.val := by
    calc
      certSite (certSite s (topClockSpan n)) i.val =
          certSite s (topClockSpan n + i.val) :=
        certSite_add s (topClockSpan n) i.val
      _ = certSite s (topClockSpan n + j.val) := hsite
      _ = certSite (certSite s (topClockSpan n)) j.val :=
        (certSite_add s (topClockSpan n) j.val).symm
  exact topPortCertSiteShortInj
    (certSite s (topClockSpan n)) i.val j.val
    (by omega) (by omega) hinner

/-- Select the unique target offset of a physical site, if one
exists. Otherwise use the valid default offset zero. -/
private noncomputable def topPortIndexAtSite {n : Nat}
    (s : Fin n) (v : Fin n) : Fin (topClockSpan n) := by
  classical
  exact if h : ∃ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) = v then
    Classical.choose h
  else
    ⟨0, by have hp := topPortSpanThreeAll n; omega⟩

private theorem topPortIndexAtSite_spec {n : Nat}
    (s : Fin n) (v : Fin n)
    (h : ∃ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) = v) :
    certSite s
      (topClockSpan n + (topPortIndexAtSite s v).val) = v := by
  classical
  simpa only [topPortIndexAtSite, dif_pos h] using
    (Classical.choose_spec h)

/-- Every selected edge has at most two target-window offsets,
including the self-pair case where the target wraps around n. -/
theorem topPortSelectedEdgeCover {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (e : Fin n) :
    ∀ j : Fin (topClockSpan n),
      (certSite s (topClockSpan n + j.val) = e ∨
        certSite s (topClockSpan n + j.val) =
          ring.rightNeighbor e) →
      j = topPortIndexAtSite s e ∨
        j = topPortIndexAtSite s (ring.rightNeighbor e) := by
  intro j hj
  have hle := topPortSpanLeOfBad C s hbad
  rcases hj with hj | hj
  · left
    apply topPortTargetSiteInj s hle
    calc
      certSite s (topClockSpan n + j.val) = e := hj
      _ = certSite s
          (topClockSpan n + (topPortIndexAtSite s e).val) :=
        (topPortIndexAtSite_spec s e ⟨j, hj⟩).symm
  · right
    apply topPortTargetSiteInj s hle
    calc
      certSite s (topClockSpan n + j.val) =
          ring.rightNeighbor e := hj
      _ = certSite s
          (topClockSpan n +
            (topPortIndexAtSite s (ring.rightNeighbor e)).val) :=
        (topPortIndexAtSite_spec s (ring.rightNeighbor e)
          ⟨j, hj⟩).symm

/-! ## One OLD pair function owns all four checker coordinates -/

/-- OLD-first-match QI/QC output of the selected source or responder
(or the framed old value if this target site is unrelated). -/
private def topPortOldPairAfterWeight {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n)) : Nat :=
  if certSite s (topClockSpan n + j.val) = e then
    topPortSiteWeight (topClockSpan n) j.val
      (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
      (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry
  else if certSite s (topClockSpan n + j.val) =
      ring.rightNeighbor e then
    topPortSiteWeight (topClockSpan n) j.val
      (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
      (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry
  else
    topPortWeightAt s Z j

/-- The physical full protocol and the locally computed exact
liveTopPair have identical OLD QI/QC outputs at every target site. -/
private theorem topPortOldPairAfterWeight_eq {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n)) :
    topPortWeightAt s (topFixedTraceNext ring C Z e) j =
      topPortOldPairAfterWeight ring s Z e j := by
  unfold topPortOldPairAfterWeight
  by_cases hx : certSite s (topClockSpan n + j.val) = e
  · rw [if_pos hx]
    have hsource := topPortLiteralSourceFields
      ring C Z.1.1 e
    change topPortSiteWeight (topClockSpan n) j.val
      (topFixedPublicNext ring C Z.1.1 e
        (certSite s (topClockSpan n + j.val))).qIn
      (topFixedPublicNext ring C Z.1.1 e
        (certSite s (topClockSpan n + j.val))).qCarry = _
    rw [hx, hsource.1, hsource.2.1]
  · rw [if_neg hx]
    by_cases hy :
        certSite s (topClockSpan n + j.val) =
          ring.rightNeighbor e
    · rw [if_pos hy]
      have hresponder := topPortLiteralResponderFields
        ring hn C Z.1.1 e
      change topPortSiteWeight (topClockSpan n) j.val
        (topFixedPublicNext ring C Z.1.1 e
          (certSite s (topClockSpan n + j.val))).qIn
        (topFixedPublicNext ring C Z.1.1 e
          (certSite s (topClockSpan n + j.val))).qCarry = _
      rw [hy, hresponder.1, hresponder.2.1]
    · rw [if_neg hy]
      exact topPortWeightAtAway ring C s Z e j hx hy

/-- ONE remaining local OLD QI/QC/QO four-coordinate product fact.
The post-values are the exact liveTopPair source/responder fields;
the original trace, packet-ready predicate and first-hit condition
are retained to exclude a port birth that is already accepted.

This is the sole OPEN physical product case partition. -/
def TopPortFourCoordinateProduct {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) : Prop :=
  ∀ (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n),
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    (if topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e) then
      topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s e) ≤
      topPortWeightAt s Z (topPortIndexAtSite s e)
    else
      topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) +
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s (ring.rightNeighbor e)) ≤
      topPortWeightAt s Z (topPortIndexAtSite s e) +
        topPortWeightAt s Z
          (topPortIndexAtSite s (ring.rightNeighbor e)))

/-- The ORIGINAL combined endpoint theorem now follows from
the one local OLD pair-product assertion. -/
theorem topPortCombinedEndpointRowBound_of_product {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hproduct : TopPortFourCoordinateProduct ring C s atom) :
    TopPortCombinedEndpointRowBound ring C s atom := by
  intro hbad Z e hreach hready hnot
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hn : 2 ≤ n := by omega
  refine ⟨topPortIndexAtSite s e,
    topPortIndexAtSite s (ring.rightNeighbor e), ?_, ?_⟩
  · exact topPortSelectedEdgeCover ring C s hbad e
  · have hlocal := hproduct hbad Z e hreach hready hnot
    rw [← topPortOldPairAfterWeight_eq ring hn C s Z e
        (topPortIndexAtSite s e)] at hlocal
    rw [← topPortOldPairAfterWeight_eq ring hn C s Z e
        (topPortIndexAtSite s (ring.rightNeighbor e))] at hlocal
    exact hlocal

end L3

/-!
Stop-aware repair of the P.2 port potential row interface.

The un-stopped
TopPortFourCoordinateProduct above was refuted on the accepting
source-exit/target-border service. A nonterminal OLD cut does not
make its successor nonterminal; the next-cut STOP disjunct is needed.

No unconditional combined physical row producer is claimed.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The same selected edge, frame, and progress interfaces as
TopPortPhysicalRows; only the raw nonincrease field is replaced
by the correct stopped-next disjunction. -/
structure TopPortPhysicalRowsStop {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) where
  chosen : TopFixedTraceState n → Fin n
  frame : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) ∨
    (topClockReached ring C (topFixedTraceNext ring C Z e) ∧
      topClockPortReady s atom (topFixedTraceNext ring C Z e))
  nonincrease : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) ∨
    topPortPotential s (topFixedTraceNext ring C Z e) ≤
      topPortPotential s Z
  progress : ∀ Z : TopFixedTraceState n,
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z (chosen Z)) ∨
    topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
      topPortPotential s Z

/-- The only alteration to the old Bellman argument is in hmono:
a newly stopped successor has stopped potential zero, and a
nonstopped successor uses the numeric half of nonincrease. -/
private theorem topPortBellmanOfStopRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (rows : TopPortPhysicalRowsStop ring C s atom) :
    ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      n + (List.ofFn (fun e : Fin n =>
        n * topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e))).sum ≤
        n * (n * topPortStoppedPotential ring C s atom Z) := by
  classical
  intro Z hreach hready hnot
  have hmono : ∀ e : Fin n,
      topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e) ≤
        topPortStoppedPotential ring C s atom Z := by
    intro e
    by_cases hstop :
        topClockStopOr ring C s (topClockPortAccepted s atom)
          (topFixedTraceNext ring C Z e)
    · simp only [topPortStoppedPotential,
        if_pos hstop, if_neg hnot]
      omega
    · rcases rows.nonincrease Z e hreach hready hnot with hhit | hw
      · exact False.elim (hstop hhit)
      · simp only [topPortStoppedPotential,
          if_neg hstop, if_neg hnot]
        omega
  have hchosen :
      topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z (rows.chosen Z)) + 1 ≤
        topPortStoppedPotential ring C s atom Z := by
    rcases rows.progress Z hreach hready hnot with hstop | hdrop
    · simp only [topPortStoppedPotential,
        if_pos hstop, if_neg hnot]
      omega
    · by_cases hstop :
          topClockStopOr ring C s (topClockPortAccepted s atom)
            (topFixedTraceNext ring C Z (rows.chosen Z))
      · simp only [topPortStoppedPotential,
          if_pos hstop, if_neg hnot]
        omega
      · simp only [topPortStoppedPotential,
          if_neg hstop, if_neg hnot]
        omega
  have hpoint : ∀ e : Fin n,
      topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e) +
          (if e = rows.chosen Z then 1 else 0) ≤
        topPortStoppedPotential ring C s atom Z := by
    intro e
    by_cases he : e = rows.chosen Z
    · subst e
      rw [if_pos rfl]
      exact hchosen
    · simpa only [if_neg he, Nat.add_zero] using hmono e
  have hsum := ofFn_sum_le
    (fun e : Fin n =>
      topPortStoppedPotential ring C s atom
        (topFixedTraceNext ring C Z e) +
        (if e = rows.chosen Z then 1 else 0))
    (fun _ : Fin n => topPortStoppedPotential ring C s atom Z)
    hpoint
  rw [ofFn_sum_add, topPortSpikeSum n (rows.chosen Z) 1,
    ofFn_sum_const] at hsum
  calc
    n + (List.ofFn (fun e : Fin n =>
        n * topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e))).sum =
      n * ((List.ofFn (fun e : Fin n =>
        topPortStoppedPotential ring C s atom
          (topFixedTraceNext ring C Z e))).sum + 1) := by
            rw [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
            omega
    _ ≤ n * (n * topPortStoppedPotential ring C s atom Z) :=
      Nat.mul_le_mul_left n hsum


/-- The same local finite-horizon cost argument, now using
the stopped-row Bellman estimate. -/
theorem topPortExpectedOfStopRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hn : 0 < n)
    (rows : TopPortPhysicalRowsStop ring C s atom)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hready : topClockPortReady s atom Z) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockPortAccepted s atom))
      Z ((n * topClockB (topClockSpan n) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s (topClockPortAccepted s atom))
    hn Z (n * topClockB (topClockSpan n))).2
  have hforward : ∀ Y : TopFixedTraceState n, ∀ e : Fin n,
      (topClockReached ring C Y ∧ topClockPortReady s atom Y) →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Y →
      (topClockReached ring C (topFixedTraceNext ring C Y e) ∧
        topClockPortReady s atom (topFixedTraceNext ring C Y e)) ∨
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Y e) := by
    intro Y e hvalid hnot
    rcases rows.frame Y e hvalid.1 hvalid.2 hnot with
      hstop | hcontinue
    · exact Or.inr hstop
    · exact Or.inl hcontinue
  have hcost := topPortLocalFirstHitCost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s (topClockPortAccepted s atom))
    (fun Y : TopFixedTraceState n =>
      topClockReached ring C Y ∧ topClockPortReady s atom Y)
    (fun Y => n * topPortStoppedPotential ring C s atom Y)
    hforward
    (by
      intro Y hvalid hnot
      exact topPortBellmanOfStopRows ring C s atom rows
        Y hvalid.1 hvalid.2 hnot)
  have hbudget :
      topPortStoppedPotential ring C s atom Z ≤
        topClockB (topClockSpan n) := by
    have hphi := topPortStoppedPotential_le ring C s atom Z
    have hw := topPortPotential_le s Z
    have hb := topPortPotentialBudget (topClockSpan n)
    omega
  intro T
  calc
    costNumerator (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockPortAccepted s atom))
      Z T ≤
        n ^ T * (n * topPortStoppedPotential ring C s atom Z) :=
      hcost T Z ⟨hreach, hready⟩
    _ ≤ n ^ T * (n * topClockB (topClockSpan n)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n hbudget)


/-- The repaired conditional phase producer. -/
theorem topClockPortPhaseOfStopRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hn : 0 < n)
    (hrows : ∀ atom : Option (DigitAtom n),
      TopPortPhysicalRowsStop ring C s atom) :
    TopClockPortPhase ring C s := by
  intro atom Z hreach hready
  exact topPortExpectedOfStopRows ring C s atom hn
    (hrows atom) Z hreach hready

/-! ## Accepting edge creates an actual audit export receipt -/

/-- The Q comparison ghost owner has the same QO1 acceptance guard
as the physical QI/QO owner. Arbitrary source input and carry are
allowed. Every earlier QI branch affecting y is disabled by the
old empty/carry-free target border. -/
private theorem topPortDigitOfferReceipt
    {c : Compiled} {n : Nat}
    (stamp : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (value : Fin c.topA) (tail : Bool)
    (hxl : x.leader = false)
    (hyl : y.leader = false)
    (hyb : y.marker = true)
    (hxo : x.out = .D value tail)
    (hyi : y.input = .E)
    (hyc : y.carryLive = false) :
    (digitLaneReplay .comparison stamp source destination
      x y gx gy).exported =
        some
          { time := stamp
            lane := .comparison
            source := source
            destination := destination
            operand := gx.out.atom
            value := value
            tail := tail } := by
  calc
    (digitLaneReplay .comparison stamp source destination
      x y gx gy).exported =
        some
          ({ time := stamp
             lane := .comparison
             source := source
             destination := destination
             operand := gx.out.atom
             value := value
             tail := tail } : DigitExport c n) := by
      -- First-match priorities: roots; carry; X/S/P input;
      -- finally the boundary offer. No earlier branch consumes y.
      unfold digitLaneReplay
      cases hxb : x.marker with
      | false =>
          cases hxc : x.carryLive with
          | false =>
              cases hxi : x.input with
              | E =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | P sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | S sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | X =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
          | true =>
              cases hxi : x.input with
              | E =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | P sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | S sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | X =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
      | true =>
          cases hxc : x.carryLive with
          | false =>
              cases hxi : x.input with
              | E =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | P sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | S sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | X =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
          | true =>
              cases hxi : x.input with
              | E =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | P sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | S sourceDigit sourceTail =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)
              | X =>
                  simp [hxl, hyl, hyc, hxc, hxi, hyb, hxo, hyi, hxb,
                    OutTok.isD, InTok.isE, InTok.isS, InTok.isX,
                    InTok.isP, outV, outT, inT] <;>
                    (try split) <;> (try rfl)

/-- On the actual offer edge, an OLD ready D and an OLD empty
carry-free target border create the nominated comparison export
on the NEW audit. This is stronger than mere physical QI arrival:
the recorded operand is the one in the OLD ready-port audit. -/
theorem topPortReadyOfferStops {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (Z : TopFixedTraceState n) (e : Fin n)
    (hsource : e = certSite s (topClockSpan n - 1))
    (hdestination : ring.rightNeighbor e =
      certSite s (topClockSpan n))
    (hready : topClockPortReady s atom Z)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) :
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) := by
  rcases hready with ⟨value, tail, houtput, hatom⟩
  have hxo : (Z.1.1 e).qOut = .D value tail := by
    rw [hsource]
    exact houtput
  have hghost :
      (Z.1.2.current e).comparison.out.atom = atom := by
    rw [hsource]
    exact hatom
  have hycview :
      (digitLaneView .comparison
        ((piD Z.1.1) (ring.rightNeighbor e))
        (((piD Z.1.1) (ring.rightNeighbor e)).word.beta)).carryLive =
          false := by
    simp only [digitLaneView]
    change (Z.1.1 (ring.rightNeighbor e)).qCarry.isL = false
    simp only [hyc, QCarry.isL]
  have hreceipt :
      (digitService (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        ((piD Z.1.1) e)
        ((piD Z.1.1) (ring.rightNeighbor e))
        (Z.1.2.current e)
        (Z.1.2.current (ring.rightNeighbor e))).comparison.exported =
        some
          { time := Z.1.2.clock + 1
            lane := .comparison
            source := e
            destination := ring.rightNeighbor e
            operand := atom
            value := value
            tail := tail } := by
    have hlocal := topPortDigitOfferReceipt
      (Z.1.2.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison ((piD Z.1.1) e)
        (((piD Z.1.1) e).word.beta))
      (digitLaneView .comparison
        ((piD Z.1.1) (ring.rightNeighbor e))
        (((piD Z.1.1) (ring.rightNeighbor e)).word.beta))
      ((Z.1.2.current e).comparison)
      ((Z.1.2.current (ring.rightNeighbor e)).comparison)
      value tail
      (by change (Z.1.1 e).l = false; exact hxl)
      (by change (Z.1.1 (ring.rightNeighbor e)).l = false; exact hyl)
      (by change (Z.1.1 (ring.rightNeighbor e)).beta = true; exact hyb)
      (by change (Z.1.1 e).qOut = .D value tail; exact hxo)
      (by change (Z.1.1 (ring.rightNeighbor e)).qIn = .E; exact hyi)
      hycview
    rw [hghost] at hlocal
    change (digitLaneReplay .comparison (Z.1.2.clock + 1)
      e (ring.rightNeighbor e)
      (digitLaneView .comparison ((piD Z.1.1) e)
        (((piD Z.1.1) e).word.beta))
      (digitLaneView .comparison
        ((piD Z.1.1) (ring.rightNeighbor e))
        (((piD Z.1.1) (ring.rightNeighbor e)).word.beta))
      ((Z.1.2.current e).comparison)
      ((Z.1.2.current (ring.rightNeighbor e)).comparison)).exported =
        some
          { time := Z.1.2.clock + 1
            lane := .comparison
            source := e
            destination := ring.rightNeighbor e
            operand := atom
            value := value
            tail := tail }
    exact hlocal
  have hrecord :
      DigitRecordedExport
        (digitAuditStep ring (piD Z.1.1) Z.1.2 e)
        ({ time := Z.1.2.clock + 1
           lane := .comparison
           source := e
           destination := ring.rightNeighbor e
           operand := atom
           value := value
           tail := tail } :
           DigitExport (compileAdvice (ceilLogTwo n)) n) := by
    unfold DigitRecordedExport
    refine ⟨{ time := Z.1.2.clock + 1
              edge := e
              old := piD Z.1.1
              oldGhost := Z.1.2.current
              receipt := digitService (Z.1.2.clock + 1) e
                (ring.rightNeighbor e)
                ((piD Z.1.1) e)
                ((piD Z.1.1) (ring.rightNeighbor e))
                (Z.1.2.current e)
                (Z.1.2.current (ring.rightNeighbor e)) },
       ?_, rfl, rfl, ?_⟩
    · simp [digitAuditStep]
    · change
        (digitService (Z.1.2.clock + 1) e
          (ring.rightNeighbor e)
          ((piD Z.1.1) e)
          ((piD Z.1.1) (ring.rightNeighbor e))
          (Z.1.2.current e)
          (Z.1.2.current (ring.rightNeighbor e))).comparison.exported =
            some
              { time := Z.1.2.clock + 1
                lane := .comparison
                source := e
                destination := ring.rightNeighbor e
                operand := atom
                value := value
                tail := tail }
      exact hreceipt
  apply Or.inr
  unfold topClockPortAccepted
  refine ⟨{ time := Z.1.2.clock + 1
            lane := .comparison
            source := e
            destination := ring.rightNeighbor e
            operand := atom
            value := value
            tail := tail },
    ?_, rfl, rfl, hsource, hdestination, rfl⟩
  change DigitRecordedExport
    (digitAuditStep ring (piD Z.1.1) Z.1.2 e)
    ({ time := Z.1.2.clock + 1
       lane := .comparison
       source := e
       destination := ring.rightNeighbor e
       operand := atom
       value := value
       tail := tail } :
       DigitExport (compileAdvice (ceilLogTwo n)) n)
  exact hrecord

/-! ## Stopped four-coordinate producer and proven reduction -/

/-- Replaces only the false unconditional conclusion of
TopPortFourCoordinateProduct. The OLD accepting service is now
allowed to discharge the NEW first-hit target. The local
four-coordinate case partition is still a separate premise. -/
def TopPortFourCoordinateProductStop {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) : Prop :=
  ∀ (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n),
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) ∨
    (if topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e) then
      topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s e) ≤
        topPortWeightAt s Z (topPortIndexAtSite s e)
    else
      topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) +
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s (ring.rightNeighbor e)) ≤
        topPortWeightAt s Z (topPortIndexAtSite s e) +
        topPortWeightAt s Z
          (topPortIndexAtSite s (ring.rightNeighbor e)))

/-- The earlier selected-edge cover and finite-sum swap eliminate the
local four-coordinate account whenever the NEW target has not
already stopped. No assertion about a falsely increasing accepting
service is needed. -/
theorem topPortNonincreaseOfFourProductStop {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hproduct : TopPortFourCoordinateProductStop ring C s atom) :
    ∀ (Z : TopFixedTraceState n) (e : Fin n),
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e) ∨
      topPortPotential s (topFixedTraceNext ring C Z e) ≤
        topPortPotential s Z := by
  intro Z e hreach hready hnot
  rcases hproduct hbad Z e hreach hready hnot with hhit | hlocal
  · exact Or.inl hhit
  · apply Or.inr
    have hspan := topPortSpanThreeAll n
    have hle := topPortSpanLeOfBad C s hbad
    have hn : 2 ≤ n := by omega
    have hlocal' := hlocal
    rw [← topPortOldPairAfterWeight_eq ring hn C s Z e
      (topPortIndexAtSite s e)] at hlocal'
    rw [← topPortOldPairAfterWeight_eq ring hn C s Z e
      (topPortIndexAtSite s (ring.rightNeighbor e))] at hlocal'
    have hframe : ∀ j : Fin (topClockSpan n),
        j ≠ topPortIndexAtSite s e →
        j ≠ topPortIndexAtSite s (ring.rightNeighbor e) →
        topPortWeightAt s (topFixedTraceNext ring C Z e) j =
          topPortWeightAt s Z j := by
      intro j hji hjk
      have hx :
          certSite s (topClockSpan n + j.val) ≠ e := by
        intro he
        rcases topPortSelectedEdgeCover ring C s hbad e
            j (Or.inl he) with hfirst | hsecond
        · exact hji hfirst
        · exact hjk hsecond
      have hy :
          certSite s (topClockSpan n + j.val) ≠
            ring.rightNeighbor e := by
        intro he
        rcases topPortSelectedEdgeCover ring C s hbad e
            j (Or.inr he) with hfirst | hsecond
        · exact hji hfirst
        · exact hjk hsecond
      exact topPortWeightAtAway ring C s Z e j hx hy
    have hlocalIf :
        (if topPortIndexAtSite s e =
            topPortIndexAtSite s (ring.rightNeighbor e) then
          topPortWeightAt s (topFixedTraceNext ring C Z e)
            (topPortIndexAtSite s e)
        else
          topPortWeightAt s (topFixedTraceNext ring C Z e)
              (topPortIndexAtSite s e) +
            topPortWeightAt s (topFixedTraceNext ring C Z e)
              (topPortIndexAtSite s (ring.rightNeighbor e))) ≤
        (if topPortIndexAtSite s e =
            topPortIndexAtSite s (ring.rightNeighbor e) then
          topPortWeightAt s Z (topPortIndexAtSite s e)
        else
          topPortWeightAt s Z (topPortIndexAtSite s e) +
            topPortWeightAt s Z
              (topPortIndexAtSite s (ring.rightNeighbor e))) := by
      by_cases heq : topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e)
      · simp only [if_pos heq] at hlocal' ⊢
        exact hlocal'
      · simp only [if_neg heq] at hlocal' ⊢
        exact hlocal'
    have hsum := topPortSumTwoLe
      (topPortWeightAt s Z)
      (topPortWeightAt s (topFixedTraceNext ring C Z e))
      (topPortIndexAtSite s e)
      (topPortIndexAtSite s (ring.rightNeighbor e))
      hframe hlocalIf
    change
      (List.ofFn (topPortWeightAt s
        (topFixedTraceNext ring C Z e))).sum ≤
      (List.ofFn (topPortWeightAt s Z)).sum
    exact hsum

/-- Assemble the repaired nonincrease field from its still-open
complete product premise, without transferring or inventing
the separate frame/progress certificates. -/
def topPortPhysicalRowsStopOfFourProduct {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (chosen : TopFixedTraceState n → Fin n)
    (hframe : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e) ∨
      (topClockReached ring C (topFixedTraceNext ring C Z e) ∧
        topClockPortReady s atom (topFixedTraceNext ring C Z e)))
    (hprogress : ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z (chosen Z)) ∨
      topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
        topPortPotential s Z)
    (hproduct : TopPortFourCoordinateProductStop ring C s atom) :
    TopPortPhysicalRowsStop ring C s atom :=
  { chosen := chosen
    frame := hframe
    nonincrease :=
      topPortNonincreaseOfFourProductStop ring C s atom hbad hproduct
    progress := hprogress }

end L3

/-!
Stop-aware first-match offer and untouched-window rows.

The accepting QO service and a selected pair disjoint from the entire
target window are discharged below. All touched, nonaccepting,
nonstopping QI/QC first-match rows remain one explicitly named
hypothesis.
No unconditional four-coordinate product theorem is asserted.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A reached fixed-public trace has exactly the initial leader and
border marker bits, including at time zero. Only the four public
fields are frozen; the private inputs and carries are not. -/
private theorem topPortReachedPublicMask {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (i : Fin n) :
    (Z.1.1 i).l = (C i).l ∧
    (Z.1.1 i).beta = (C i).beta := by
  have hfold : ∀ (word : List (Fin n))
      (F : TopFixedTraceState n),
      (F.1.1 i).l = (C i).l ∧
        (F.1.1 i).beta = (C i).beta →
      ((word.foldl (topFixedTraceNext ring C) F).1.1 i).l =
        (C i).l ∧
      ((word.foldl (topFixedTraceNext ring C) F).1.1 i).beta =
        (C i).beta := by
    intro word
    induction word with
    | nil =>
        intro F hF
        simpa only [List.foldl_nil] using hF
    | cons e rest ih =>
        intro F hF
        have hstep := topPortFixedPublicMaskStep ring C F e i
        simpa only [List.foldl_cons] using
          (ih (topFixedTraceNext ring C F e) hstep)
  have hinit := hfold Z.2
    ((C, digitAuditInitial (piD C)), [])
    ⟨rfl, rfl⟩
  have hrun :
      ((topFixedTraceRun ring C Z.2).1.1 i).l = (C i).l ∧
      ((topFixedTraceRun ring C Z.2).1.1 i).beta =
        (C i).beta := by
    simpa only [topFixedTraceRun] using hinit
  refine ⟨?_, ?_⟩
  · calc
      (Z.1.1 i).l =
          ((topFixedTraceRun ring C Z.2).1.1 i).l :=
        congrArg
          (fun F : TopFixedTraceState n => (F.1.1 i).l) hreach
      _ = (C i).l := hrun.1
  · calc
      (Z.1.1 i).beta =
          ((topFixedTraceRun ring C Z.2).1.1 i).beta :=
        congrArg
          (fun F : TopFixedTraceState n => (F.1.1 i).beta) hreach
      _ = (C i).beta := hrun.2

/-- The exact physical QO first-match acceptance guard under an OLD
ready port: source exit, target border, OLD empty target input and
OLD carry OFF. The source OLD D is supplied by port readiness;
the nonleader/marker tests follow from reached BadCompletePair. -/
def topPortReadyOfferFirstMatch {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) : Prop :=
  e = certSite s (topClockSpan n - 1) ∧
  ring.rightNeighbor e = certSite s (topClockSpan n) ∧
  (Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
  (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF

/-- The complete-block public geometry discharges the three
nonleader/marker binders of topPortReadyOfferStops. This proves the
accepting row without claiming a decrease of raw target potential. -/
theorem topPortReadyOfferFirstMatchStops {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hreach : topClockReached ring C Z)
    (hready : topClockPortReady s atom Z)
    (hfirst : topPortReadyOfferFirstMatch ring s Z e) :
    topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) := by
  rcases hfirst with ⟨hsource, hdestination, hyi, hyc⟩
  have hsourcePublic :=
    topPortReachedPublicMask ring C Z hreach e
  have htargetPublic :=
    topPortReachedPublicMask ring C Z hreach
      (ring.rightNeighbor e)
  have hspan := topPortSpanThreeAll n
  have hxl : (Z.1.1 e).l = false := by
    calc
      (Z.1.1 e).l = (C e).l := hsourcePublic.1
      _ = false := by
        rw [hsource]
        exact topPortEligibleFollower C s hbad
          (topClockSpan n - 1) (by omega)
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    calc
      (Z.1.1 (ring.rightNeighbor e)).l =
          (C (ring.rightNeighbor e)).l := htargetPublic.1
      _ = false := by
        rw [hdestination]
        exact topPortEligibleFollower C s hbad
          (topClockSpan n) (by omega)
  have hyb :
      (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    calc
      (Z.1.1 (ring.rightNeighbor e)).beta =
          (C (ring.rightNeighbor e)).beta := htargetPublic.2
      _ = true := by
        rw [hdestination]
        exact topPortEligibleTargetMarker C s hbad
  exact topPortReadyOfferStops ring C s atom Z e
    hsource hdestination hready hxl hyl hyb hyi hyc

/-- When neither endpoint belongs to the target window, the OLD
pair function is literally the OLD target potential at every index.
This also proves the coincident-fallback-index case; it makes no
assumption on the private input, carry or output fields. -/
theorem topPortUntouchedPairBound {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hsource : ∀ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) ≠ e)
    (htarget : ∀ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) ≠
        ring.rightNeighbor e) :
    (if topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e) then
      topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s e) ≤
        topPortWeightAt s Z (topPortIndexAtSite s e)
    else
      topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) +
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s (ring.rightNeighbor e)) ≤
        topPortWeightAt s Z (topPortIndexAtSite s e) +
        topPortWeightAt s Z
          (topPortIndexAtSite s (ring.rightNeighbor e))) := by
  classical
  have hsame (j : Fin (topClockSpan n)) :
      topPortOldPairAfterWeight ring s Z e j =
        topPortWeightAt s Z j := by
    unfold topPortOldPairAfterWeight
    simp only [if_neg (hsource j), if_neg (htarget j)]
  by_cases heq :
      topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e)
  · simp only [if_pos heq]
    rw [hsame (topPortIndexAtSite s e)]
    exact Nat.le_refl _
  · simp only [if_neg heq]
    rw [hsame (topPortIndexAtSite s e),
      hsame (topPortIndexAtSite s (ring.rightNeighbor e))]
    exact Nat.le_refl _

/-- Exact remaining first-match product obligation. It excludes:
(i) a NEW stop, (ii) the OLD ready-D/border-E/OFF accepting row
proved above, and (iii) a selected pair that misses the target
window entirely. This still contains multiple QI/QC first-match
subrows, including simultaneous carry/input updates. It has not
been proved; users must not treat this predicate as a certificate. -/
def TopPortNonstoppingTouchedRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) : Prop :=
  ∀ (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n),
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
    (∃ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) = e ∨
      certSite s (topClockSpan n + j.val) =
        ring.rightNeighbor e) →
    ¬ topPortReadyOfferFirstMatch ring s Z e →
    ¬ topClockStopOr ring C s (topClockPortAccepted s atom)
      (topFixedTraceNext ring C Z e) →
    (if topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e) then
      topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s e) ≤
        topPortWeightAt s Z (topPortIndexAtSite s e)
    else
      topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) +
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s (ring.rightNeighbor e)) ≤
        topPortWeightAt s Z (topPortIndexAtSite s e) +
        topPortWeightAt s Z
          (topPortIndexAtSite s (ring.rightNeighbor e)))

/-- The accepting row and all geometrically untouched rows are
fully discharged. The remaining touched nonstopping first-match
rows are exactly the named premise above. -/
theorem topPortFourCoordinateProductStopOfTouchedRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hrows : TopPortNonstoppingTouchedRows ring C s atom) :
    TopPortFourCoordinateProductStop ring C s atom := by
  intro hbad Z e hreach hready hnot
  by_cases hstop :
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e)
  · exact Or.inl hstop
  · apply Or.inr
    have hnotoffer :
        ¬ topPortReadyOfferFirstMatch ring s Z e := by
      intro hfirst
      exact hstop (topPortReadyOfferFirstMatchStops
        ring C s atom hbad Z e hreach hready hfirst)
    by_cases htouched :
        ∃ j : Fin (topClockSpan n),
          certSite s (topClockSpan n + j.val) = e ∨
          certSite s (topClockSpan n + j.val) =
            ring.rightNeighbor e
    · exact hrows hbad Z e hreach hready hnot
        htouched hnotoffer hstop
    · apply topPortUntouchedPairBound ring s Z e
      · intro j hj
        apply htouched
        exact ⟨j, Or.inl hj⟩
      · intro j hj
        apply htouched
        exact ⟨j, Or.inr hj⟩

/-- Direct Q7-facing constructor: it accepts only the outstanding
nonstopping touched first-match row certificate and the separate
frame/progress evidence already required by the stop-row interface. -/
def topPortPhysicalRowsStopOfTouchedRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (chosen : TopFixedTraceState n → Fin n)
    (hframe : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e) ∨
      (topClockReached ring C (topFixedTraceNext ring C Z e) ∧
        topClockPortReady s atom (topFixedTraceNext ring C Z e)))
    (hprogress : ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z (chosen Z)) ∨
      topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
        topPortPotential s Z)
    (hrows : TopPortNonstoppingTouchedRows ring C s atom) :
    TopPortPhysicalRowsStop ring C s atom :=
  topPortPhysicalRowsStopOfFourProduct ring C s atom hbad
    chosen hframe hprogress
    (topPortFourCoordinateProductStopOfTouchedRows
      ring C s atom hrows)

end L3

/-!
First-match truth audit and target-window geometry.

The following local row
inequalities are deliberately separated from the global
TopPortNonstoppingTouchedRows assertion. No unconditional
producer is claimed here before the local rows and their
geometric stitching have passed a Lean kernel build.

The selected pair can touch the target window in precisely
three forms: two consecutive interior window sites, the
last target-window site as source, or the target border as
responder. The last two forms overlap if n = topClockSpan n.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- One right neighbor is one modular certificate-site increment.
This statement is independent of the particular ring record. -/
private theorem topPortNeighborCertSite {n : Nat}
    (ring : DirectedRing n) (s : Fin n) (k : Nat) :
    ring.rightNeighbor (certSite s k) =
      certSite s (k + 1) := by
  apply Fin.ext
  change ((s.val + k) % n + 1) % n =
    (s.val + (k + 1)) % n
  calc
    ((s.val + k) % n + 1) % n =
        (s.val + k + 1) % n :=
      Nat.mod_add_mod (s.val + k) n 1
    _ = (s.val + (k + 1)) % n := by
      congr 1

/-- Right-neighbor is injective, including the modular wrap. -/
private theorem topPortNeighborInjective {n : Nat}
    (ring : DirectedRing n) (e f : Fin n)
    (h : ring.rightNeighbor e = ring.rightNeighbor f) :
    e = f := by
  apply Fin.ext
  have heq := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at heq
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at heq
    by_cases hf : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf] at heq
      omega
    · have hfe : f.val + 1 = n := by
        have hh := f.isLt
        omega
      rw [hfe, Nat.mod_self] at heq
      omega
  · have hee : e.val + 1 = n := by
      have hh := e.isLt
      omega
    rw [hee, Nat.mod_self] at heq
    by_cases hf : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf] at heq
      omega
    · have hfe : f.val + 1 = n := by
        have hh := f.isLt
        omega
      omega

/-- Exact three-form target-window incidence classification.
No root assumption is needed to classify touched sites; the
BadCompletePair hypothesis is needed later for the public
beta mask and for uniqueness of target offsets. -/
private theorem topPortTouchedShape {n : Nat}
    (ring : DirectedRing n) (s : Fin n) (e : Fin n)
    (htouched : ∃ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) = e ∨
      certSite s (topClockSpan n + j.val) =
        ring.rightNeighbor e) :
    (∃ j : Fin (topClockSpan n),
      j.val + 1 < topClockSpan n ∧
      e = certSite s (topClockSpan n + j.val) ∧
      ring.rightNeighbor e =
        certSite s (topClockSpan n + (j.val + 1))) ∨
    e = certSite s
      (topClockSpan n + (topClockSpan n - 1)) ∨
    ring.rightNeighbor e = certSite s (topClockSpan n) := by
  rcases htouched with ⟨j, hj | hj⟩
  · by_cases hnext : j.val + 1 < topClockSpan n
    · left
      refine ⟨j, hnext, hj.symm, ?_⟩
      calc
        ring.rightNeighbor e =
            ring.rightNeighbor
              (certSite s (topClockSpan n + j.val)) := by
                rw [hj]
        _ = certSite s (topClockSpan n + j.val + 1) :=
          topPortNeighborCertSite ring s
            (topClockSpan n + j.val)
        _ = certSite s
              (topClockSpan n + (j.val + 1)) := by
                congr 1
    · right
      left
      have hlast : j.val = topClockSpan n - 1 := by
        have hjlt := j.isLt
        omega
      rw [hlast] at hj
      exact hj.symm
  · by_cases hzero : j.val = 0
    · right
      right
      rw [hzero] at hj
      simpa only [Nat.add_zero] using hj.symm
    · left
      have hpos : 0 < j.val := by omega
      have hprev :
          ring.rightNeighbor
            (certSite s (topClockSpan n + (j.val - 1))) =
          certSite s (topClockSpan n + j.val) := by
        rw [topPortNeighborCertSite]
        have hnat :
            topClockSpan n + (j.val - 1) + 1 =
              topClockSpan n + j.val := by omega
        rw [hnat]
      have hsource :
          e = certSite s (topClockSpan n + (j.val - 1)) := by
        apply topPortNeighborInjective ring
        calc
          ring.rightNeighbor e =
              certSite s (topClockSpan n + j.val) := hj.symm
          _ = ring.rightNeighbor
                (certSite s
                  (topClockSpan n + (j.val - 1))) := hprev.symm
      refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_, ?_⟩
      · change j.val - 1 + 1 < topClockSpan n
        omega
      · exact hsource
      · change ring.rightNeighbor e =
          certSite s (topClockSpan n + (j.val - 1 + 1))
        have hnat : j.val - 1 + 1 = j.val := by omega
        rw [hnat]
        exact hj.symm

/-- A target-window member's chosen index is its actual unique
offset under the already-proved complete-block width bound. -/
private theorem topPortMemberIndex {n : Nat}
    (s : Fin n) (hle : topClockSpan n ≤ n)
    (j : Fin (topClockSpan n)) (v : Fin n)
    (hsite : certSite s (topClockSpan n + j.val) = v) :
    topPortIndexAtSite s v = j := by
  apply topPortTargetSiteInj s hle
  calc
    certSite s
        (topClockSpan n + (topPortIndexAtSite s v).val) =
          v := topPortIndexAtSite_spec s v ⟨j, hsite⟩
    _ = certSite s (topClockSpan n + j.val) := hsite.symm

/-- A site wholly outside the target window receives precisely
the default index zero. This is needed for the alias case of
TopPortNonstoppingTouchedRows; default zero is not a physical
site assertion. -/
private theorem topPortOutsideIndex {n : Nat}
    (s v : Fin n)
    (hout : ∀ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) ≠ v) :
    topPortIndexAtSite s v =
      (⟨0, by have hspan := topPortSpanThreeAll n; omega⟩ :
        Fin (topClockSpan n)) := by
  classical
  have hnone : ¬ ∃ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) = v := by
    intro h
    rcases h with ⟨j, hj⟩
    exact hout j hj
  unfold topPortIndexAtSite
  simp only [dif_neg hnone]

/-- QI front merging with a resident OLD front: only the source
front is erased. This arithmetic branch is distinct from the
previously established X/S consumption branch. -/
private theorem topPortWeightQIFrontMergeJoint {a : Nat}
    (r j : Nat) (hj : j + 1 < r) :
    topPortSiteWeight r j (.E : InTok a) .OFF +
        topPortSiteWeight r (j + 1) (.X : InTok a) .OFF ≤
      topPortSiteWeight r j (.X : InTok a) .OFF +
        topPortSiteWeight r (j + 1) (.X : InTok a) .OFF := by
  simp only [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight]
  omega

/-- QI non-tail pending packet settles at a terminal and loses
one unit, including arbitrary target offset j. -/
private theorem topPortWeightQITerminalSettles {a : Nat}
    (r j : Nat) (hj : j < r) (v : Fin a) :
    topPortSiteWeight r j (.S v false) .OFF + 1 ≤
      topPortSiteWeight r j (.P v false) .OFF :=
  topPortWeightQIPendingSettle r j hj v false

/-- Generic QI/QC source inequality for a nonmarker source,
including OLD carry/input co-occupancy, terminal pending settlement,
front retirement, and cases where the responder is a leader.
The QO submap never writes source qIn or qCarry. -/
private theorem topPortOwnerSourceNonmarkerBound
    {c : Compiled} (r j : Nat) (hj : j < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxb : x.beta = false) :
    topPortSiteWeight r j
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry ≤
      topPortSiteWeight r j x.qIn x.qCarry := by
  have hempty (hrow :
      (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
      (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF) :
      topPortSiteWeight r j
          (liveTopPair c x y resolvedX resolvedY).x.qIn
          (liveTopPair c x y resolvedX resolvedY).x.qCarry ≤
        topPortSiteWeight r j x.qIn x.qCarry := by
    rw [hrow.1, hrow.2]
    change 0 ≤ topPortSiteWeight r j x.qIn x.qCarry
    exact Nat.zero_le _
  cases hxl : x.l with
  | true =>
      apply hempty
      cases hxc : x.qCarry with
      | OFF =>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry,
              ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
              ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
                  ↓liveTopPair_y_qOut,
              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
              hxc, QCarry.isL]
      | L carry error =>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry,
              ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
              ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
                  ↓liveTopPair_y_qOut,
              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
              hxc, QCarry.isL]
  | false =>
      cases hyl : y.l with
      | true =>
          apply hempty
          cases hxc : x.qCarry with
          | OFF =>
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
                  QCarry.isL]
          | L carry error =>
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxc,
                  QCarry.isL]
      | false =>
          cases hxc : x.qCarry with
          | L carry error =>
              have hrow :
                  (liveTopPair c x y resolvedX resolvedY).x.qIn =
                    .E ∧
                  (liveTopPair c x y resolvedX resolvedY).x.qCarry =
                    .OFF := by
                cases hyc : y.qCarry <;>
                cases hyi : y.qIn <;>
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxc, hyc, hyi,
                    QCarry.isL, QCarry.isOff, topTerminal,
                    topInternal, topBorder, InTok.isS, InTok.isE,
                    InTok.isX, InTok.isP] <;>
                  (repeat' split) <;> simp at *
              rw [hrow.1, hrow.2]
              change 0 ≤ topPortSiteWeight r j x.qIn (.L carry error)
              exact Nat.zero_le _
          | OFF =>
              have hcarry :
                  (liveTopPair c x y resolvedX resolvedY).x.qCarry =
                    .OFF := by
                simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                    ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                    ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                    ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                    liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                    hxc, hxb,
                  topBorder, QCarry.isL, QCarry.isOff]
              rw [hcarry]
              simp only [topPortSiteWeight, topPortCarryWeight,
                Nat.add_zero]
              cases hxi : x.qIn with
              | P value tail =>
                  simpa only [hxi, topPortInputWeight] using
                    (topPortInputWeight_le r j hj
                      (liveTopPair c x y
                        resolvedX resolvedY).x.qIn)
              | E =>
                  have hnew :
                      (liveTopPair c x y
                        resolvedX resolvedY).x.qIn = .E := by
                    cases hyb : y.beta <;>
                    cases hyc : y.qCarry <;>
                    cases hyi : y.qIn <;>
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hxc,
                        hxi, hyb, hyc, hyi, topInternal,
                        topTerminal, topBorder, QCarry.isL,
                        QCarry.isOff, InTok.isS, InTok.isE,
                        InTok.isX, InTok.isP] <;>
                      (repeat' split) <;> rfl
                  rw [hnew]
                  exact Nat.le_refl _
              | S value tail =>
                  cases tail with
                  | false =>
                      have hnew :
                          (liveTopPair c x y
                            resolvedX resolvedY).x.qIn =
                              .S value false := by
                        cases hyb : y.beta <;>
                        cases hyc : y.qCarry <;>
                        cases hyi : y.qIn <;>
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hxc,
                            hxi, hyb, hyc, hyi, topInternal,
                            topTerminal, topBorder, QCarry.isL,
                            QCarry.isOff, InTok.isS, InTok.isE,
                            InTok.isX, InTok.isP, inT] <;>
                          (repeat' split) <;> rfl
                      rw [hnew]
                      exact Nat.le_refl _
                  | true =>
                      have hnew :
                          (liveTopPair c x y
                            resolvedX resolvedY).x.qIn = .X := by
                        cases hyb : y.beta <;>
                        cases hyc : y.qCarry <;>
                        cases hyi : y.qIn <;>
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hxc,
                            hxi, hyb, hyc, hyi, topInternal,
                            topTerminal, topBorder, QCarry.isL,
                            QCarry.isOff, InTok.isS, InTok.isE,
                            InTok.isX, InTok.isP, inT] <;>
                          (repeat' split) <;> rfl
                      rw [hnew]
                      change r - j ≤ r - j + 1
                      omega
              | X =>
                  have hnew :
                      (liveTopPair c x y
                        resolvedX resolvedY).x.qIn = .E := by
                    cases hyb : y.beta <;>
                    cases hyc : y.qCarry <;>
                    cases hyi : y.qIn <;>
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hxc,
                        hxi, hyb, hyc, hyi, topInternal,
                        topTerminal, topBorder, QCarry.isL,
                        QCarry.isOff, InTok.isS, InTok.isE,
                        InTok.isX, InTok.isP] <;>
                      (repeat' split) <;> rfl
                  rw [hnew]
                  change 0 ≤ r - j
                  exact Nat.zero_le _


/-- The target border cannot gain a new checker pending packet
if its OLD input/carry pair is not the empty/OFF accepting guard.
The right-hand coordinate is conservative even for arbitrary
OLD source scratch and simultaneous non-QO first-match rows. -/
private theorem topPortOwnerTargetBorderBlocked
    {c : Compiled} (r : Nat)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hyb : y.beta = true)
    (hblocked : ¬ (y.qIn = .E ∧ y.qCarry = .OFF)) :
    topPortSiteWeight r 0
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortSiteWeight r 0 y.qIn y.qCarry := by
  have hempty (hrow :
      (liveTopPair c x y resolvedX resolvedY).y.qIn = .E ∧
      (liveTopPair c x y resolvedX resolvedY).y.qCarry = .OFF) :
      topPortSiteWeight r 0
          (liveTopPair c x y resolvedX resolvedY).y.qIn
          (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
        topPortSiteWeight r 0 y.qIn y.qCarry := by
    rw [hrow.1, hrow.2]
    change 0 ≤ topPortSiteWeight r 0 y.qIn y.qCarry
    exact Nat.zero_le _
  cases hxl : x.l with
  | true =>
      apply hempty
      cases hyc : y.qCarry with
      | OFF =>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry,
              ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
              ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
                  ↓liveTopPair_y_qOut,
              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
              hyc, QCarry.isL]
      | L carry error =>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry,
              ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
              ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
                  ↓liveTopPair_y_qOut,
              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
              hyc, QCarry.isL]
  | false =>
      cases hyl : y.l with
      | true =>
          apply hempty
          cases hyc : y.qCarry with
          | OFF =>
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hyc,
                  QCarry.isL]
          | L carry error =>
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hyc,
                  QCarry.isL]
      | false =>
          cases hyc : y.qCarry with
          | L carry error =>
              have hrow :
                  (liveTopPair c x y
                    resolvedX resolvedY).y.qIn = .E ∧
                  (liveTopPair c x y
                    resolvedX resolvedY).y.qCarry =
                      .L carry error := by
                cases hxc : x.qCarry <;>
                cases hxi : x.qIn <;>
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hyb, hyc,
                    hxc, hxi, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff,
                    InTok.isS, InTok.isE, InTok.isX,
                    InTok.isP] <;>
                  (repeat' split) <;> rfl
              rw [hrow.1, hrow.2]
              have hzero :
                  0 + (r - 0) ≤
                    topPortInputWeight r 0 y.qIn + (r - 0) :=
                Nat.add_le_add_right
                  (Nat.zero_le (topPortInputWeight r 0 y.qIn))
                  (r - 0)
              simpa only [topPortSiteWeight,
                topPortInputWeight, topPortCarryWeight]
                using hzero
          | OFF =>
              have hrow :
                  (liveTopPair c x y
                    resolvedX resolvedY).y.qIn = y.qIn ∧
                  (liveTopPair c x y
                    resolvedX resolvedY).y.qCarry = .OFF := by
                cases hyi : y.qIn with
                | E =>
                    exact False.elim (hblocked ⟨hyi, hyc⟩)
                | P value tail =>
                    cases hxc : x.qCarry <;>
                    cases hxi : x.qIn <;>
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hyb, hyc,
                        hyi, hxc, hxi, topTerminal,
                        topInternal, topBorder, QCarry.isL,
                        QCarry.isOff, InTok.isS, InTok.isE,
                        InTok.isX, InTok.isP] <;>
                      (repeat' split) <;> rfl
                | S value tail =>
                    cases hxc : x.qCarry <;>
                    cases hxi : x.qIn <;>
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hyb, hyc,
                        hyi, hxc, hxi, topTerminal,
                        topInternal, topBorder, QCarry.isL,
                        QCarry.isOff, InTok.isS, InTok.isE,
                        InTok.isX, InTok.isP] <;>
                      (repeat' split) <;> rfl
                | X =>
                    cases hxc : x.qCarry <;>
                    cases hxi : x.qIn <;>
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hyb, hyc,
                        hyi, hxc, hxi, topTerminal,
                        topInternal, topBorder, QCarry.isL,
                        QCarry.isOff, InTok.isS, InTok.isE,
                        InTok.isX, InTok.isP] <;>
                      (repeat' split) <;> rfl
              rw [hrow.1, hrow.2]
              exact Nat.le_refl _


/-- Interior charges depend only on remaining distance t=r-j.
This eliminates the exceptional marker charge of S(false), which
does not apply at a strictly positive target offset. -/
private def topPortInteriorInputCharge {a : Nat}
    (t : Nat) : InTok a → Nat
  | .E => 0
  | .X => t
  | .P _ _ => t + 2
  | .S _ tail => if tail then t + 1 else 1

private def topPortInteriorCharge {a : Nat}
    (t : Nat) (input : InTok a) (carry : QCarry) : Nat :=
  topPortInteriorInputCharge t input +
    (match carry with
     | .OFF => 0
     | .L _ _ => t)

/-- Re-express a positive-index physical charge in its closed
linear distance form, for every OLD input and carry co-occupancy. -/
private theorem topPortInteriorChargeAt {a : Nat}
    (r j : Nat) (hj : 0 < j)
    (input : InTok a) (carry : QCarry) :
    topPortSiteWeight r j input carry =
      topPortInteriorCharge (r - j) input carry := by
  cases input with
  | E =>
      cases carry <;> rfl
  | X =>
      cases carry <;> rfl
  | P value tail =>
      cases carry <;> rfl
  | S value tail =>
      cases tail with
      | true =>
          cases carry <;> rfl
      | false =>
          cases carry <;>
            simp [topPortSiteWeight, topPortInputWeight,
              topPortCarryWeight, topPortInteriorCharge,
              topPortInteriorInputCharge, Nat.ne_of_gt hj]

/-- A marked source at offset zero charges S(true) and S(false)
equally at r+1. The carry is independent and additive. -/
private def topPortBorderInputCharge {a : Nat}
    (r : Nat) : InTok a → Nat
  | .E => 0
  | .X => r
  | .P _ _ => r + 2
  | .S _ _ => r + 1

private def topPortBorderCharge {a : Nat}
    (r : Nat) (input : InTok a) (carry : QCarry) : Nat :=
  topPortBorderInputCharge r input +
    (match carry with
     | .OFF => 0
     | .L _ _ => r)

private theorem topPortBorderChargeAt {a : Nat}
    (r : Nat) (input : InTok a) (carry : QCarry) :
    topPortSiteWeight r 0 input carry =
      topPortBorderCharge r input carry := by
  cases input with
  | E =>
      cases carry <;> simp [topPortSiteWeight,
        topPortInputWeight, topPortCarryWeight,
        topPortBorderCharge, topPortBorderInputCharge]
  | X =>
      cases carry <;> simp [topPortSiteWeight,
        topPortInputWeight, topPortCarryWeight,
        topPortBorderCharge, topPortBorderInputCharge]
  | P value tail =>
      cases carry <;> simp [topPortSiteWeight,
        topPortInputWeight, topPortCarryWeight,
        topPortBorderCharge, topPortBorderInputCharge]
  | S value tail =>
      cases tail <;> cases carry <;>
        simp [topPortSiteWeight,
          topPortInputWeight, topPortCarryWeight,
          topPortBorderCharge, topPortBorderInputCharge]

/-- Exhaustive independent OLD-QI/QC first-match row proof:
both endpoints are nonleaders and nonmarkers, both physical
target offsets are strictly positive, and t is the remaining
distance at the source. Every branch is specified explicitly
by OLD qCarry and qIn constructors; S and P tails are split. -/
private theorem topPortInteriorPairDistanceBound
    {c : Compiled} (t : Nat) (ht : 2 ≤ t)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false) :
    topPortInteriorCharge t
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry +
      topPortInteriorCharge (t - 1)
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortInteriorCharge t x.qIn x.qCarry +
        topPortInteriorCharge (t - 1) y.qIn y.qCarry := by
  have hdist : t - 1 + 1 = t := by omega
  have hpositive : 1 ≤ t - 1 := by omega
  cases hxc : x.qCarry with
  | OFF =>
      cases hyc : y.qCarry with
      | OFF =>
          cases hxi : x.qIn with
          | E =>
              -- empty source and empty carries; framed responder
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
          | X =>
              cases hyi : y.qIn with
              | E =>
                  -- source X erases; transfers only into old S; responder E
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
              | X =>
                  -- source X erases; transfers only into old S; responder X
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
              | P value tail =>
                  -- source X erases; transfers only into old S; responder P
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
              | S value tail =>
                  cases tail with
                  | false =>
                      -- source X erases; transfers only into old S; responder S(false)
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | true =>
                      -- source X erases; transfers only into old S; responder S(true)
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
          | P value tail =>
              cases tail with
              | false =>
                  cases hyi : y.qIn with
                  | E =>
                      -- source P(false) first-match; responder E
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | X =>
                      -- source P(false) first-match; responder X
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | P value tail =>
                      -- source P(false) first-match; responder P
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | S value tail =>
                      cases tail with
                      | false =>
                          -- source P(false) first-match; responder S(false)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                            topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                      | true =>
                          -- source P(false) first-match; responder S(true)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                            topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
              | true =>
                  cases hyi : y.qIn with
                  | E =>
                      -- source P(true) first-match; responder E
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | X =>
                      -- source P(true) first-match; responder X
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | P value tail =>
                      -- source P(true) first-match; responder P
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                        topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                  | S value tail =>
                      cases tail with
                      | false =>
                          -- source P(true) first-match; responder S(false)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                            topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
                      | true =>
                          -- source P(true) first-match; responder S(true)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                            topPortInteriorInputCharge, QC, hxc, hyc, hxi, hyi] <;> omega
          | S value tail =>
              cases tail with
              | false =>
                  -- source S(false) first-match
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
              | true =>
                  -- source S(true) first-match
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
      | L carry error =>
          cases hxi : x.qIn with
          | E =>
              -- source E, old responder L consumes its input
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
          | X =>
              -- source X, old responder L consumes its input
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
          | P value tail =>
              cases tail with
              | false =>
                  -- source P(false), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
              | true =>
                  -- source P(true), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
          | S value tail =>
              cases tail with
              | false =>
                  -- source S(false), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
              | true =>
                  -- source S(true), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hxi] <;> omega
  | L carry error =>
      cases hyc : y.qCarry with
      | OFF =>
          cases hyi : y.qIn with
          | E =>
              -- OLD source L cleaned; QC2 iff responder S; responder E
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                topPortInteriorInputCharge, QC, hxc, hyc, hyi] <;> omega
          | X =>
              -- OLD source L cleaned; QC2 iff responder S; responder X
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                topPortInteriorInputCharge, QC, hxc, hyc, hyi] <;> omega
          | P value tail =>
              -- OLD source L cleaned; QC2 iff responder S; responder P
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                topPortInteriorInputCharge, QC, hxc, hyc, hyi] <;> omega
          | S value tail =>
              cases tail with
              | false =>
                  -- OLD source L cleaned; QC2 iff responder S; responder S(false)
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hyi] <;> omega
              | true =>
                  -- OLD source L cleaned; QC2 iff responder S; responder S(true)
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
                    topPortInteriorInputCharge, QC, hxc, hyc, hyi] <;> omega
      | L carryY errorY =>
          -- OLD source and responder live carries; both QI slots cleared
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry,
              ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
              ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
                  ↓liveTopPair_y_qOut,
              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
              hyl, hxb, hyb, topTerminal, topInternal,
            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
            InTok.isE, InTok.isX, inT, inV, topPortInteriorCharge,
            topPortInteriorInputCharge, QC, hxc, hyc] <;> omega

/-- A nonmarker internal source and its nonmarker interior
responder satisfy the complete two-site QI/QC bound for
every OLD qIn and qCarry, including simultaneous QC2/QI
consumption. Here j is strictly positive, so OLD S(false)
at the source has weight one rather than r+1. -/
private theorem topPortOwnerTwoInteriorNonmarkers
    {c : Compiled} (r j : Nat)
    (hj : 0 < j) (hjr : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false) :
    topPortSiteWeight r j
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry +
      topPortSiteWeight r (j + 1)
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortSiteWeight r j x.qIn x.qCarry +
        topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hstep :
      topPortInteriorCharge (r - j)
          (liveTopPair c x y resolvedX resolvedY).x.qIn
          (liveTopPair c x y resolvedX resolvedY).x.qCarry +
        topPortInteriorCharge ((r - j) - 1)
          (liveTopPair c x y resolvedX resolvedY).y.qIn
          (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortInteriorCharge (r - j) x.qIn x.qCarry +
        topPortInteriorCharge ((r - j) - 1) y.qIn y.qCarry :=
    topPortInteriorPairDistanceBound (r - j) (by omega)
      x y resolvedX resolvedY hxl hyl hxb hyb
  have hnext : r - (j + 1) = (r - j) - 1 := by omega
  simpa only [topPortInteriorChargeAt r j hj,
    topPortInteriorChargeAt r (j + 1) (by omega), hnext]
    using hstep

/-- Boundary source has S(false) weight r+1, unlike interior.
QC3 replaces that OLD S with a live carry of weight r,
and it never clones a second carry onto the responder. -/
private theorem topPortBorderPairDistanceBound
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false) :
    topPortBorderCharge r
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry +
      topPortInteriorCharge (r - 1)
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortBorderCharge r x.qIn x.qCarry +
        topPortInteriorCharge (r - 1) y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hpositive : 1 ≤ r - 1 := by omega
  cases hxc : x.qCarry with
  | OFF =>
      cases hyc : y.qCarry with
      | OFF =>
          cases hxi : x.qIn with
          | E =>
              -- empty source and empty carries; framed responder
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                hxi] <;> omega
          | X =>
              cases hyi : y.qIn with
              | E =>
                  -- source X erases; transfers only into old S; responder E
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi, hyi] <;> omega
              | X =>
                  -- source X erases; transfers only into old S; responder X
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi, hyi] <;> omega
              | P value tail =>
                  -- source X erases; transfers only into old S; responder P
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi, hyi] <;> omega
              | S value tail =>
                  cases tail with
                  | false =>
                      -- source X erases; transfers only into old S; responder S(false)
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | true =>
                      -- source X erases; transfers only into old S; responder S(true)
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
          | P value tail =>
              cases tail with
              | false =>
                  cases hyi : y.qIn with
                  | E =>
                      -- source P(false) first-match; responder E
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | X =>
                      -- source P(false) first-match; responder X
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | P value tail =>
                      -- source P(false) first-match; responder P
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | S value tail =>
                      cases tail with
                      | false =>
                          -- source P(false) first-match; responder S(false)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                            topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                            hxi, hyi] <;> omega
                      | true =>
                          -- source P(false) first-match; responder S(true)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                            topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                            hxi, hyi] <;> omega
              | true =>
                  cases hyi : y.qIn with
                  | E =>
                      -- source P(true) first-match; responder E
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | X =>
                      -- source P(true) first-match; responder X
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | P value tail =>
                      -- source P(true) first-match; responder P
                      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                          ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                          ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                          ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC,
                          liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
                          hyl, hxb, hyb, topTerminal, topInternal,
                        topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                        InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                        topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                        hxi, hyi] <;> omega
                  | S value tail =>
                      cases tail with
                      | false =>
                          -- source P(true) first-match; responder S(false)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                            topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                            hxi, hyi] <;> omega
                      | true =>
                          -- source P(true) first-match; responder S(true)
                          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                              ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                              ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
                              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
                              liveTopPair, hxl, hyl, hxb, hyb, topTerminal, topInternal,
                            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                            InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                            topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                            hxi, hyi] <;> omega
          | S value tail =>
              cases tail with
              | false =>
                  -- source S(false) first-match
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi] <;> omega
              | true =>
                  -- source S(true) first-match
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi] <;> omega
      | L carry error =>
          cases hxi : x.qIn with
          | E =>
              -- source E, old responder L consumes its input
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                hxi] <;> omega
          | X =>
              -- source X, old responder L consumes its input
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                hxi] <;> omega
          | P value tail =>
              cases tail with
              | false =>
                  -- source P(false), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi] <;> omega
              | true =>
                  -- source P(true), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi] <;> omega
          | S value tail =>
              cases tail with
              | false =>
                  -- source S(false), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi] <;> omega
              | true =>
                  -- source S(true), old responder L consumes its input
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hxi] <;> omega
  | L carry error =>
      cases hyc : y.qCarry with
      | OFF =>
          cases hyi : y.qIn with
          | E =>
              -- OLD source L cleaned; QC2 iff responder S; responder E
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                hyi] <;> omega
          | X =>
              -- OLD source L cleaned; QC2 iff responder S; responder X
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                hyi] <;> omega
          | P value tail =>
              -- OLD source L cleaned; QC2 iff responder S; responder P
              simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hxb,
                  hyb, topTerminal, topInternal,
                topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                hyi] <;> omega
          | S value tail =>
              cases tail with
              | false =>
                  -- OLD source L cleaned; QC2 iff responder S; responder S(false)
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hyi] <;> omega
              | true =>
                  -- OLD source L cleaned; QC2 iff responder S; responder S(true)
                  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                      ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                      ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                      ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                      liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
                      hxb, hyb, topTerminal, topInternal,
                    topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
                    InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
                    topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc,
                    hyi] <;> omega
      | L carryY errorY =>
          -- OLD source and responder live carries; both QI slots cleared
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry,
              ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
              ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
                  ↓liveTopPair_y_qOut,
              liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl,
              hyl, hxb, hyb, topTerminal, topInternal,
            topBorder, QCarry.isL, QCarry.isOff, InTok.isS, InTok.isP,
            InTok.isE, InTok.isX, inT, inV, topPortBorderCharge,
            topPortBorderInputCharge, topPortInteriorCharge, topPortInteriorInputCharge, QC, hxc, hyc] <;> omega

/-- At target offset zero the OLD S(false) charge is r+1;
QC3 replaces that S by a fresh L of charge r. QI P moves to
offset one; all other first-match branches remain
nonincreasing. The source marker case is deliberately separate
from two nonmarker interiors. -/
private theorem topPortOwnerBorderToInterior
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false) :
    topPortSiteWeight r 0
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry +
      topPortSiteWeight r 1
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
        topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hstep :
      topPortBorderCharge r
          (liveTopPair c x y resolvedX resolvedY).x.qIn
          (liveTopPair c x y resolvedX resolvedY).x.qCarry +
        topPortInteriorCharge (r - 1)
          (liveTopPair c x y resolvedX resolvedY).y.qIn
          (liveTopPair c x y resolvedX resolvedY).y.qCarry ≤
      topPortBorderCharge r x.qIn x.qCarry +
        topPortInteriorCharge (r - 1) y.qIn y.qCarry :=
    topPortBorderPairDistanceBound r hr
      x y resolvedX resolvedY hxl hyl hxb hyb
  simpa only [topPortBorderChargeAt,
    topPortInteriorChargeAt r 1 (by omega)] using hstep

end L3

/-!
OLD pair product stitching over the three actual touched
edge geometries.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

private def topPortZeroIndex (n : Nat) : Fin (topClockSpan n) :=
  ⟨0, by have hspan := topPortSpanThreeAll n; omega⟩

private def topPortLastIndex (n : Nat) : Fin (topClockSpan n) :=
  ⟨topClockSpan n - 1, by
    have hspan := topPortSpanThreeAll n
    omega⟩

private theorem topPortZeroLastNe (n : Nat) :
    topPortLastIndex n ≠ topPortZeroIndex n := by
  intro h
  have hv := congrArg Fin.val h
  change topClockSpan n - 1 = 0 at hv
  have hs := topPortSpanThreeAll n
  omega

private theorem topPortOutsideIndexZero {n : Nat}
    (s v : Fin n)
    (hout : ∀ j : Fin (topClockSpan n),
      certSite s (topClockSpan n + j.val) ≠ v) :
    topPortIndexAtSite s v = topPortZeroIndex n := by
  simpa only [topPortZeroIndex] using
    (topPortOutsideIndex s v hout)

/-- Responder at target border: an in-window predecessor is
the last target position, never a positive earlier offset. -/
private theorem topPortBeforeBorderMemberLast {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (hle : topClockSpan n ≤ n) (e : Fin n)
    (hborder : ring.rightNeighbor e =
      certSite s (topClockSpan n))
    (j : Fin (topClockSpan n))
    (hmember : certSite s (topClockSpan n + j.val) = e) :
    j.val = topClockSpan n - 1 := by
  by_cases hstep : j.val + 1 < topClockSpan n
  · have hwrap :
        certSite s (topClockSpan n + (j.val + 1)) =
          certSite s (topClockSpan n) := by
      calc
        certSite s (topClockSpan n + (j.val + 1)) =
            certSite s (topClockSpan n + j.val + 1) := by
              congr 1
        _ = ring.rightNeighbor
              (certSite s (topClockSpan n + j.val)) :=
          (topPortNeighborCertSite ring s
            (topClockSpan n + j.val)).symm
        _ = ring.rightNeighbor e := by rw [hmember]
        _ = certSite s (topClockSpan n) := hborder
    have hindex :
        (⟨j.val + 1, hstep⟩ : Fin (topClockSpan n)) =
          topPortZeroIndex n := by
      apply topPortTargetSiteInj s hle
      change certSite s (topClockSpan n + (j.val + 1)) =
        certSite s (topClockSpan n + 0)
      simpa only [Nat.add_zero] using hwrap
    have hv := congrArg Fin.val hindex
    change j.val + 1 = 0 at hv
    omega
  · have hjlt := j.isLt
    omega

/-- A successor of the target-window last site can be an
in-window site only if it is offset zero. -/
private theorem topPortAfterLastMemberBorder {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (hle : topClockSpan n ≤ n) (e : Fin n)
    (hlast : e =
      certSite s (topClockSpan n + (topClockSpan n - 1)))
    (j : Fin (topClockSpan n))
    (hmember : certSite s (topClockSpan n + j.val) =
      ring.rightNeighbor e) :
    j.val = 0 := by
  by_cases hz : j.val = 0
  · exact hz
  · have hpos : 0 < j.val := by omega
    have hprev :
        certSite s (topClockSpan n + (j.val - 1)) = e := by
      apply topPortNeighborInjective ring
      calc
        ring.rightNeighbor
            (certSite s (topClockSpan n + (j.val - 1))) =
            certSite s (topClockSpan n + (j.val - 1) + 1) :=
          topPortNeighborCertSite ring s
            (topClockSpan n + (j.val - 1))
        _ = certSite s (topClockSpan n + j.val) := by
              congr 1
              omega
        _ = ring.rightNeighbor e := hmember
    have hindex :
        (⟨j.val - 1, by have hjlt := j.isLt; omega⟩ :
          Fin (topClockSpan n)) = topPortLastIndex n := by
      apply topPortTargetSiteInj s hle
      change
        certSite s (topClockSpan n + (j.val - 1)) =
          certSite s
            (topClockSpan n + (topClockSpan n - 1))
      exact hprev.trans hlast
    have hv := congrArg Fin.val hindex
    change j.val - 1 = topClockSpan n - 1 at hv
    have hjlt := j.isLt
    have hspan := topPortSpanThreeAll n
    omega

private theorem topPortAfterAtSource {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (hsite : certSite s (topClockSpan n + j.val) = e) :
    topPortOldPairAfterWeight ring s Z e j =
      topPortSiteWeight (topClockSpan n) j.val
        (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry := by
  unfold topPortOldPairAfterWeight
  simp only [if_pos hsite]

private theorem topPortAfterAtResponder {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (hsite : certSite s (topClockSpan n + j.val) =
      ring.rightNeighbor e) :
    topPortOldPairAfterWeight ring s Z e j =
      topPortSiteWeight (topClockSpan n) j.val
        (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hx : certSite s (topClockSpan n + j.val) ≠ e := by
    rw [hsite]
    exact hne
  unfold topPortOldPairAfterWeight
  simp only [if_neg hx, if_pos hsite]

private theorem topPortBeforeAtSource {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (hsite : certSite s (topClockSpan n + j.val) = e) :
    topPortWeightAt s Z j =
      topPortSiteWeight (topClockSpan n) j.val
        (Z.1.1 e).qIn (Z.1.1 e).qCarry := by
  unfold topPortWeightAt
  rw [hsite]

private theorem topPortBeforeAtResponder {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (hsite : certSite s (topClockSpan n + j.val) =
      ring.rightNeighbor e) :
    topPortWeightAt s Z j =
      topPortSiteWeight (topClockSpan n) j.val
        (Z.1.1 (ring.rightNeighbor e)).qIn
        (Z.1.1 (ring.rightNeighbor e)).qCarry := by
  unfold topPortWeightAt
  rw [hsite]

private theorem topPortAfterAway {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (j : Fin (topClockSpan n))
    (hx : certSite s (topClockSpan n + j.val) ≠ e)
    (hy : certSite s (topClockSpan n + j.val) ≠
      ring.rightNeighbor e) :
    topPortOldPairAfterWeight ring s Z e j =
      topPortWeightAt s Z j := by
  unfold topPortOldPairAfterWeight
  simp only [if_neg hx, if_neg hy]

private def topPortPairLocalBound {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) : Prop :=
  if topPortIndexAtSite s e =
      topPortIndexAtSite s (ring.rightNeighbor e) then
    topPortOldPairAfterWeight ring s Z e
      (topPortIndexAtSite s e) ≤
      topPortWeightAt s Z (topPortIndexAtSite s e)
  else
    topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s e) +
      topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s (ring.rightNeighbor e)) ≤
      topPortWeightAt s Z (topPortIndexAtSite s e) +
      topPortWeightAt s Z
        (topPortIndexAtSite s (ring.rightNeighbor e))

private theorem topPortTwoIndexBound {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (i k : Fin (topClockSpan n))
    (hsource : topPortIndexAtSite s e = i)
    (htarget : topPortIndexAtSite s (ring.rightNeighbor e) = k)
    (hneq : i ≠ k)
    (hpair : topPortOldPairAfterWeight ring s Z e i +
        topPortOldPairAfterWeight ring s Z e k ≤
      topPortWeightAt s Z i + topPortWeightAt s Z k) :
    topPortPairLocalBound ring s Z e := by
  unfold topPortPairLocalBound
  rw [hsource, htarget]
  simp only [if_neg hneq]
  exact hpair

private theorem topPortOneIndexBound {n : Nat}
    (ring : DirectedRing n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hcoincide :
      topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e))
    (hpoint :
      topPortOldPairAfterWeight ring s Z e
        (topPortIndexAtSite s e) ≤
      topPortWeightAt s Z (topPortIndexAtSite s e)) :
    topPortPairLocalBound ring s Z e := by
  unfold topPortPairLocalBound
  simp only [if_pos hcoincide]
  exact hpoint

private theorem topPortLiteralSourceNonmarkerBound {n : Nat}
    (ring : DirectedRing n) (Z : TopFixedTraceState n)
    (e : Fin n) (r j : Nat) (hj : j < r)
    (hxb : (Z.1.1 e).beta = false) :
    topPortSiteWeight r j
        (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry ≤
      topPortSiteWeight r j
        (Z.1.1 e).qIn (Z.1.1 e).qCarry := by
  unfold topPortLiteralTopOwner
  exact topPortOwnerSourceNonmarkerBound r j hj
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    _ _ hxb

private theorem topPortLiteralBorderBlockedBound {n : Nat}
    (ring : DirectedRing n) (Z : TopFixedTraceState n)
    (e : Fin n) (r : Nat)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true)
    (hblocked : ¬
      ((Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
       (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF)) :
    topPortSiteWeight r 0
        (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry ≤
      topPortSiteWeight r 0
        (Z.1.1 (ring.rightNeighbor e)).qIn
        (Z.1.1 (ring.rightNeighbor e)).qCarry := by
  unfold topPortLiteralTopOwner
  exact topPortOwnerTargetBorderBlocked r
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    _ _ hyb hblocked

private theorem topPortLiteralInteriorPairBound {n : Nat}
    (ring : DirectedRing n) (Z : TopFixedTraceState n)
    (e : Fin n) (r j : Nat)
    (hj : 0 < j) (hnext : j + 1 < r)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxb : (Z.1.1 e).beta = false)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    topPortSiteWeight r j
        (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry +
      topPortSiteWeight r (j + 1)
        (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry ≤
      topPortSiteWeight r j
        (Z.1.1 e).qIn (Z.1.1 e).qCarry +
      topPortSiteWeight r (j + 1)
        (Z.1.1 (ring.rightNeighbor e)).qIn
        (Z.1.1 (ring.rightNeighbor e)).qCarry := by
  unfold topPortLiteralTopOwner
  exact topPortOwnerTwoInteriorNonmarkers r j hj hnext
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    _ _ hxl hyl hxb hyb

private theorem topPortLiteralBorderPairBound {n : Nat}
    (ring : DirectedRing n) (Z : TopFixedTraceState n)
    (e : Fin n) (r : Nat) (hr : 2 ≤ r)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxb : (Z.1.1 e).beta = true)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    topPortSiteWeight r 0
        (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry +
      topPortSiteWeight r 1
        (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
        (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry ≤
      topPortSiteWeight r 0
        (Z.1.1 e).qIn (Z.1.1 e).qCarry +
      topPortSiteWeight r 1
        (Z.1.1 (ring.rightNeighbor e)).qIn
        (Z.1.1 (ring.rightNeighbor e)).qCarry := by
  unfold topPortLiteralTopOwner
  exact topPortOwnerBorderToInterior r hr
    (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))
    _ _ hxl hyl hxb hyb

private theorem topPortReachedTargetFollower {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (j : Fin (topClockSpan n)) :
    (Z.1.1 (certSite s (topClockSpan n + j.val))).l =
      false := by
  calc
    (Z.1.1 (certSite s (topClockSpan n + j.val))).l =
      (C (certSite s (topClockSpan n + j.val))).l :=
        (topPortReachedPublicMask ring C Z hreach _).1
    _ = false := topPortEligibleFollower C s hbad
      (topClockSpan n + j.val) (by have hjlt := j.isLt; omega)

private theorem topPortReachedTargetInteriorMarker {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (j : Fin (topClockSpan n)) (hj : 0 < j.val) :
    (Z.1.1 (certSite s (topClockSpan n + j.val))).beta =
      false := by
  calc
    (Z.1.1 (certSite s (topClockSpan n + j.val))).beta =
      (C (certSite s (topClockSpan n + j.val))).beta :=
        (topPortReachedPublicMask ring C Z hreach _).2
    _ = false :=
      topPortEligibleTargetInteriorMarker C s hbad j hj

private theorem topPortReachedBorderMarker {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) :
    (Z.1.1 (certSite s (topClockSpan n))).beta =
      true := by
  calc
    (Z.1.1 (certSite s (topClockSpan n))).beta =
      (C (certSite s (topClockSpan n))).beta :=
        (topPortReachedPublicMask ring C Z hreach _).2
    _ = true := topPortEligibleTargetMarker C s hbad

private theorem topPortEligibleSourceExitNonmarker {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    (C (certSite s (topClockSpan n - 1))).beta =
      false := by
  have hs := topPortSpanThreeAll n
  have hmark := hbad.1.2.2.2.2.1
    (⟨topClockSpan n - 1, by omega⟩ : Fin (topClockSpan n))
    (by show 0 < topClockSpan n - 1; omega)
  exact hmark

private theorem topPortPreBorderSite {n : Nat}
    (ring : DirectedRing n) (s : Fin n) (e : Fin n)
    (hborder : ring.rightNeighbor e =
      certSite s (topClockSpan n)) :
    e = certSite s (topClockSpan n - 1) := by
  have hs := topPortSpanThreeAll n
  have hsuccessor :
      ring.rightNeighbor (certSite s (topClockSpan n - 1)) =
        certSite s (topClockSpan n) := by
    rw [topPortNeighborCertSite]
    have harr : (topClockSpan n - 1) + 1 =
      topClockSpan n := by omega
    rw [harr]
  apply topPortNeighborInjective ring
  calc
    ring.rightNeighbor e = certSite s (topClockSpan n) :=
      hborder
    _ = ring.rightNeighbor (certSite s (topClockSpan n - 1)) :=
      hsuccessor.symm

/-- Both endpoints are consecutive sites within the target block.
Offset zero is special because its source is a marker; otherwise
the two interior endpoints both use the nonmarker joint bound. -/
private theorem topPortInternalTouchedBound {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hnext : j.val + 1 < topClockSpan n)
    (hsource : e = certSite s (topClockSpan n + j.val))
    (htarget : ring.rightNeighbor e =
      certSite s (topClockSpan n + (j.val + 1))) :
    topPortPairLocalBound ring s Z e := by
  classical
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hn : 2 ≤ n := by omega
  have hsiteX :
      certSite s (topClockSpan n + j.val) = e :=
    hsource.symm
  have hsiteY :
      certSite s (topClockSpan n + (j.val + 1)) =
        ring.rightNeighbor e := htarget.symm
  have hindexX : topPortIndexAtSite s e = j :=
    topPortMemberIndex s hle j e hsiteX
  have hindexY :
      topPortIndexAtSite s (ring.rightNeighbor e) =
        (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
    topPortMemberIndex s hle
      ⟨j.val + 1, hnext⟩ (ring.rightNeighbor e) hsiteY
  have hneq :
      j ≠ (⟨j.val + 1, hnext⟩ :
        Fin (topClockSpan n)) := by
    intro h
    have hv := congrArg Fin.val h
    change j.val = j.val + 1 at hv
    omega
  have hxl : (Z.1.1 e).l = false := by
    rw [hsource]
    exact topPortReachedTargetFollower ring C s hbad Z hreach j
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [htarget]
    exact topPortReachedTargetFollower ring C s hbad Z hreach
      ⟨j.val + 1, hnext⟩
  have hyb :
      (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    rw [htarget]
    exact topPortReachedTargetInteriorMarker ring C s hbad
      Z hreach ⟨j.val + 1, hnext⟩ (Nat.succ_pos j.val)
  have hraw :
      topPortSiteWeight (topClockSpan n) j.val
          (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
          (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry +
        topPortSiteWeight (topClockSpan n) (j.val + 1)
          (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
          (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry ≤
      topPortSiteWeight (topClockSpan n) j.val
          (Z.1.1 e).qIn (Z.1.1 e).qCarry +
        topPortSiteWeight (topClockSpan n) (j.val + 1)
          (Z.1.1 (ring.rightNeighbor e)).qIn
          (Z.1.1 (ring.rightNeighbor e)).qCarry := by
    by_cases hzero : j.val = 0
    · have hxb : (Z.1.1 e).beta = true := by
        rw [hsource, hzero]
        simpa only [Nat.add_zero] using
          (topPortReachedBorderMarker ring C s hbad Z hreach)
      simpa only [hzero, Nat.zero_add] using
        (topPortLiteralBorderPairBound ring Z e
          (topClockSpan n) (by omega) hxl hyl hxb hyb)
    · have hpos : 0 < j.val := by omega
      have hxb : (Z.1.1 e).beta = false := by
        rw [hsource]
        exact topPortReachedTargetInteriorMarker ring C s
          hbad Z hreach j hpos
      exact topPortLiteralInteriorPairBound ring Z e
        (topClockSpan n) j.val hpos hnext hxl hyl hxb hyb
  have hpair :
      topPortOldPairAfterWeight ring s Z e j +
        topPortOldPairAfterWeight ring s Z e
          (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) ≤
      topPortWeightAt s Z j +
        topPortWeightAt s Z
          (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) := by
    calc
      topPortOldPairAfterWeight ring s Z e j +
          topPortOldPairAfterWeight ring s Z e
            (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) =
        topPortSiteWeight (topClockSpan n) j.val
            (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry +
          topPortSiteWeight (topClockSpan n) (j.val + 1)
            (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry := by
              rw [topPortAfterAtSource ring s Z e j hsiteX,
                topPortAfterAtResponder ring hn s Z e
                  ⟨j.val + 1, hnext⟩ hsiteY]
      _ ≤ topPortSiteWeight (topClockSpan n) j.val
              (Z.1.1 e).qIn (Z.1.1 e).qCarry +
            topPortSiteWeight (topClockSpan n) (j.val + 1)
              (Z.1.1 (ring.rightNeighbor e)).qIn
              (Z.1.1 (ring.rightNeighbor e)).qCarry := hraw
      _ = topPortWeightAt s Z j +
            topPortWeightAt s Z
              (⟨j.val + 1, hnext⟩ :
                Fin (topClockSpan n)) := by
              rw [topPortBeforeAtSource s Z e j hsiteX,
                topPortBeforeAtResponder ring s Z e
                  ⟨j.val + 1, hnext⟩ hsiteY]
  exact topPortTwoIndexBound ring s Z e j
    ⟨j.val + 1, hnext⟩ hindexX hindexY hneq hpair

/-- A selected responder at the target border is the only
possible accepting service. Once that OLD offer is excluded,
the border is nonincreasing. Its source is either outside
the target window (coincident fallback index zero) or the
last target-window site (two distinct charged indices). -/
private theorem topPortBorderTouchedBound {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hnotoffer : ¬ topPortReadyOfferFirstMatch ring s Z e)
    (hborder : ring.rightNeighbor e =
      certSite s (topClockSpan n)) :
    topPortPairLocalBound ring s Z e := by
  classical
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hn : 2 ≤ n := by omega
  have hsourceExit :=
    topPortPreBorderSite ring s e hborder
  have htargetSite :
      certSite s
        (topClockSpan n + (topPortZeroIndex n).val) =
          ring.rightNeighbor e := by
    change certSite s (topClockSpan n + 0) =
      ring.rightNeighbor e
    rw [Nat.add_zero]
    exact hborder.symm
  have hindexY :
      topPortIndexAtSite s (ring.rightNeighbor e) =
        topPortZeroIndex n :=
    topPortMemberIndex s hle (topPortZeroIndex n)
      (ring.rightNeighbor e) htargetSite
  have hblocked :
      ¬ ((Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
         (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) := by
    intro h
    apply hnotoffer
    exact ⟨hsourceExit, hborder, h.1, h.2⟩
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hborder]
    exact topPortReachedBorderMarker ring C s hbad Z hreach
  have hdestRaw :=
    topPortLiteralBorderBlockedBound ring Z e
      (topClockSpan n) hyb hblocked
  have hdest :
      topPortOldPairAfterWeight ring s Z e
          (topPortZeroIndex n) ≤
        topPortWeightAt s Z (topPortZeroIndex n) := by
    calc
      topPortOldPairAfterWeight ring s Z e
          (topPortZeroIndex n) =
        topPortSiteWeight (topClockSpan n) 0
          (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
          (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry :=
        topPortAfterAtResponder ring hn s Z e
          (topPortZeroIndex n) htargetSite
      _ ≤ topPortSiteWeight (topClockSpan n) 0
          (Z.1.1 (ring.rightNeighbor e)).qIn
          (Z.1.1 (ring.rightNeighbor e)).qCarry := hdestRaw
      _ = topPortWeightAt s Z (topPortZeroIndex n) :=
        (topPortBeforeAtResponder ring s Z e
          (topPortZeroIndex n) htargetSite).symm
  by_cases hmember :
      ∃ j : Fin (topClockSpan n),
        certSite s (topClockSpan n + j.val) = e
  · rcases hmember with ⟨j, hj⟩
    have hjlast := topPortBeforeBorderMemberLast
      ring s hle e hborder j hj
    have htargetLast :
        certSite s
            (topClockSpan n + (topPortLastIndex n).val) =
          e := by
      change certSite s
        (topClockSpan n + (topClockSpan n - 1)) = e
      rw [← hjlast]
      exact hj
    have hindexX : topPortIndexAtSite s e =
        topPortLastIndex n :=
      topPortMemberIndex s hle (topPortLastIndex n)
        e htargetLast
    have hxb : (Z.1.1 e).beta = false := by
      rw [hsourceExit]
      exact (topPortReachedPublicMask ring C Z hreach
        (certSite s (topClockSpan n - 1))).2.trans
        (topPortEligibleSourceExitNonmarker C s hbad)
    have hsourceRaw :=
      topPortLiteralSourceNonmarkerBound ring Z e
        (topClockSpan n) (topClockSpan n - 1)
        (by omega) hxb
    have hsourceBound :
        topPortOldPairAfterWeight ring s Z e
            (topPortLastIndex n) ≤
          topPortWeightAt s Z (topPortLastIndex n) := by
      calc
        topPortOldPairAfterWeight ring s Z e
            (topPortLastIndex n) =
          topPortSiteWeight (topClockSpan n)
            (topClockSpan n - 1)
            (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry :=
          topPortAfterAtSource ring s Z e
            (topPortLastIndex n) htargetLast
        _ ≤ topPortSiteWeight (topClockSpan n)
              (topClockSpan n - 1)
              (Z.1.1 e).qIn (Z.1.1 e).qCarry := hsourceRaw
        _ = topPortWeightAt s Z (topPortLastIndex n) :=
          (topPortBeforeAtSource s Z e
            (topPortLastIndex n) htargetLast).symm
    have hpair :
        topPortOldPairAfterWeight ring s Z e
            (topPortLastIndex n) +
          topPortOldPairAfterWeight ring s Z e
            (topPortZeroIndex n) ≤
        topPortWeightAt s Z (topPortLastIndex n) +
          topPortWeightAt s Z (topPortZeroIndex n) := by
      omega
    exact topPortTwoIndexBound ring s Z e
      (topPortLastIndex n) (topPortZeroIndex n)
      hindexX hindexY (topPortZeroLastNe n) hpair
  · have hout :
        ∀ j : Fin (topClockSpan n),
          certSite s (topClockSpan n + j.val) ≠ e := by
      intro j hj
      exact hmember ⟨j, hj⟩
    have hindexX :
        topPortIndexAtSite s e = topPortZeroIndex n :=
      topPortOutsideIndexZero s e hout
    have hcoincide :
        topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e) :=
      hindexX.trans hindexY.symm
    apply topPortOneIndexBound ring s Z e hcoincide
    rw [hindexX]
    exact hdest

/-- Last target source, with a responder outside the target window.
The source is genuinely at r-1, while the responder's default
index zero refers to an untouched target-border site. -/
private theorem topPortLastSourceOutsideBound {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hlast : e =
      certSite s (topClockSpan n + (topClockSpan n - 1)))
    (hnoborder : ring.rightNeighbor e ≠
      certSite s (topClockSpan n)) :
    topPortPairLocalBound ring s Z e := by
  classical
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hout :
      ∀ j : Fin (topClockSpan n),
        certSite s (topClockSpan n + j.val) ≠
          ring.rightNeighbor e := by
    intro j hj
    have hjzero := topPortAfterLastMemberBorder
      ring s hle e hlast j hj
    apply hnoborder
    calc
      ring.rightNeighbor e =
          certSite s (topClockSpan n + j.val) := hj.symm
      _ = certSite s (topClockSpan n) := by
        rw [hjzero, Nat.add_zero]
  have hlastSite :
      certSite s
          (topClockSpan n + (topPortLastIndex n).val) =
        e := by
    change
      certSite s (topClockSpan n + (topClockSpan n - 1)) = e
    exact hlast.symm
  have hindexX :
      topPortIndexAtSite s e = topPortLastIndex n :=
    topPortMemberIndex s hle (topPortLastIndex n) e hlastSite
  have hindexY :
      topPortIndexAtSite s (ring.rightNeighbor e) =
        topPortZeroIndex n :=
    topPortOutsideIndexZero s (ring.rightNeighbor e) hout
  have hnonzero := topPortZeroLastNe n
  have hnotSourceZero :
      certSite s (topClockSpan n + (topPortZeroIndex n).val) ≠
        e := by
    intro h
    have hidx :
        topPortZeroIndex n = topPortLastIndex n := by
      apply topPortTargetSiteInj s hle
      calc
        certSite s
            (topClockSpan n + (topPortZeroIndex n).val) =
          e := h
        _ = certSite s
            (topClockSpan n + (topPortLastIndex n).val) :=
              hlastSite.symm
    exact hnonzero hidx.symm
  have hzeroFrame :
      topPortOldPairAfterWeight ring s Z e
        (topPortZeroIndex n) =
        topPortWeightAt s Z (topPortZeroIndex n) :=
    topPortAfterAway ring s Z e (topPortZeroIndex n)
      hnotSourceZero (hout (topPortZeroIndex n))
  have hxb : (Z.1.1 e).beta = false := by
    rw [hlast]
    exact topPortReachedTargetInteriorMarker ring C s hbad
      Z hreach (topPortLastIndex n) (by
        change 0 < topClockSpan n - 1
        omega)
  have hsourceRaw :=
    topPortLiteralSourceNonmarkerBound ring Z e
      (topClockSpan n) (topClockSpan n - 1)
      (by omega) hxb
  have hsourceBound :
      topPortOldPairAfterWeight ring s Z e
          (topPortLastIndex n) ≤
        topPortWeightAt s Z (topPortLastIndex n) := by
    calc
      topPortOldPairAfterWeight ring s Z e
          (topPortLastIndex n) =
        topPortSiteWeight (topClockSpan n)
            (topClockSpan n - 1)
            (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry :=
          topPortAfterAtSource ring s Z e
            (topPortLastIndex n) hlastSite
      _ ≤ topPortSiteWeight (topClockSpan n)
              (topClockSpan n - 1)
              (Z.1.1 e).qIn (Z.1.1 e).qCarry := hsourceRaw
      _ = topPortWeightAt s Z (topPortLastIndex n) :=
        (topPortBeforeAtSource s Z e
          (topPortLastIndex n) hlastSite).symm
  have hpair :
      topPortOldPairAfterWeight ring s Z e
          (topPortLastIndex n) +
        topPortOldPairAfterWeight ring s Z e
          (topPortZeroIndex n) ≤
      topPortWeightAt s Z (topPortLastIndex n) +
        topPortWeightAt s Z (topPortZeroIndex n) := by
    omega
  exact topPortTwoIndexBound ring s Z e
    (topPortLastIndex n) (topPortZeroIndex n)
    hindexX hindexY hnonzero hpair

/-- Unconditional touched-row result. No extra history predicate is
needed beyond topClockReached, the OLD ready port, and the
nonstopping cut assumptions already quantified by the Prop. -/
theorem topPortNonstoppingTouchedRows_holds {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) :
    TopPortNonstoppingTouchedRows ring C s atom := by
  intro hbad Z e hreach hready hnot htouched hnotoffer hnotnext
  change topPortPairLocalBound ring s Z e
  rcases topPortTouchedShape ring s e htouched with
    ⟨j, hnext, hsource, htarget⟩ | hlast | hborder
  · exact topPortInternalTouchedBound ring C s hbad Z
      hreach e j hnext hsource htarget
  · by_cases hborder :
        ring.rightNeighbor e = certSite s (topClockSpan n)
    · exact topPortBorderTouchedBound ring C s hbad Z
        hreach e hnotoffer hborder
    · exact topPortLastSourceOutsideBound ring C s hbad Z
        hreach e hlast hborder
  · exact topPortBorderTouchedBound ring C s hbad Z
      hreach e hnotoffer hborder

theorem topPortFourCoordinateProductStop_holds {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n)) :
    TopPortFourCoordinateProductStop ring C s atom :=
  topPortFourCoordinateProductStopOfTouchedRows ring C s atom
    (topPortNonstoppingTouchedRows_holds ring C s atom)

/-- Q7-facing constructor. These hframe/hprogress binders are
independent of the nonincrease proof and are intentionally not
claimed as corollaries of the four-coordinate product. -/
def topPortPhysicalRowsStop {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (chosen : TopFixedTraceState n → Fin n)
    (hframe : ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e) ∨
      (topClockReached ring C (topFixedTraceNext ring C Z e) ∧
        topClockPortReady s atom (topFixedTraceNext ring C Z e)))
    (hprogress : ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z (chosen Z)) ∨
      topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
        topPortPotential s Z) :
    TopPortPhysicalRowsStop ring C s atom :=
  topPortPhysicalRowsStopOfFourProduct ring C s atom hbad
    chosen hframe hprogress
    (topPortFourCoordinateProductStop_holds ring C s atom)

end L3


/-!
P.2 actual ready-port frame on nonstopping edges.

The frame hypothesis in topPortPhysicalRowsStop (line 4524)
quantifies only over reached fixed-public traces, a currently
ready qOut D and its current DigitAudit atom, and an OLD
nonstop. It does NOT assume TopMobilePendingBarrier, so a
barrier lemma cannot be silently applied to this generality.

The only touched port cases are the outgoing border offer
and the immediately preceding incoming edge to the source
port. In the former a D is either accepted or physically
blocked and remains paired with its unchanged ghost atom.
In the latter it is the OLD occupied responder output and
remains in place. In every other case, both slots frame.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Fold-snoc on precisely the existing chronological edge
list, without referring to the private lemma in RequestStage. -/
private theorem topPortFrameFoldSnoc
    {A B : Type} (f : B → A → B) (start : B)
    (word : List A) (e : A) :
    (word ++ [e]).foldl f start =
      f (word.foldl f start) e := by
  induction word generalizing start with
  | nil =>
      rfl
  | cons a tail ih =>
      exact ih (f start a)

/-- Reached is invariant under every actual fixed-trace edge.
The new audit and the selected edge are not erased or reset. -/
theorem topPortReachedNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hreach : topClockReached ring C Z) :
    topClockReached ring C (topFixedTraceNext ring C Z e) := by
  have happend :
      topFixedTraceRun ring C (Z.2 ++ [e]) =
        topFixedTraceNext ring C
          (topFixedTraceRun ring C Z.2) e := by
    unfold topFixedTraceRun
    exact topPortFrameFoldSnoc
      (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), []) Z.2 e
  change
    topFixedTraceNext ring C Z e =
      topFixedTraceRun ring C (Z.2 ++ [e])
  rw [happend, ← hreach]

/-- The source QO D does not disappear on a BLOCKED marker
offer; this is the literal source coordinate of LIVE-TOP. -/
private theorem topPortFrameSourceLiteralBlocked
    (c : Compiled) (x y : Agent c)
    (betaX betaY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hyb : y.beta = true) (hxo : x.qOut = .D v tail)
    (hblock : y.qIn.isE = false ∨ y.qCarry.isOff = false) :
    (liveTopPair c x y betaX betaY).x.qOut = .D v tail := by
  -- Expose the OLD input/carry constructor before simplifying
  -- the independently computed QI flags in the QO accept guard.
  rcases hblock with hi | hc
  · cases hiy : y.qIn with
    | E =>
        simp [hiy, InTok.isE] at hi
    | P value stamp =>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
            hyb, hxo, hiy,
          OutTok.isD, InTok.isE]
    | S value stamp =>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
            hyb, hxo, hiy,
          OutTok.isD, InTok.isE]
    | X =>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
            hyb, hxo, hiy,
          OutTok.isD, InTok.isE]
  · cases hcy : y.qCarry with
    | OFF =>
        simp [hcy, QCarry.isOff] at hc
    | L carry error =>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl,
            hyb, hxo, hcy,
          OutTok.isD, QCarry.isOff]

/-- An occupied OLD responder output D is never overwritten
by an incoming QO movement: that row needs responder E. -/
private theorem topPortFrameResponderLiteralOccupied
    (c : Compiled) (x y : Agent c)
    (betaX betaY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hyo : y.qOut = .D v tail) :
    (liveTopPair c x y betaX betaY).y.qOut = .D v tail := by
  simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hxl, hyl, hyo,
    OutTok.isD, OutTok.isE]

/-- QO provenance for a BLOCKED source offer is unchanged
on the exact OLD-digit audit replay. Other simultaneous
QI/QC choices do not replace the output ghost coordinate. -/
private theorem topPortFrameReplaySourceBlocked
    {c : Compiled} {n : Nat}
    (clock : Nat) (e ysite : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hxo : x.out = .D v tail) (hyb : y.marker = true)
    (hblock : y.input.isE = false ∨ y.carryLive = true) :
    (digitLaneReplay .comparison clock e ysite x y gx gy).x.out.atom =
      gx.out.atom := by
  -- Concrete OLD input/carry cases collapse the export gate.
  rcases hblock with hi | hc
  · cases hiy : y.input with
    | E =>
        simp [hiy, InTok.isE] at hi
    | P value stamp =>
        simp [digitLaneReplay, hxl, hyl, hxo, hyb, hiy,
          OutTok.isD, InTok.isE]
    | S value stamp =>
        simp [digitLaneReplay, hxl, hyl, hxo, hyb, hiy,
          OutTok.isD, InTok.isE]
    | X =>
        simp [digitLaneReplay, hxl, hyl, hxo, hyb, hiy,
          OutTok.isD, InTok.isE]
  · cases hyc : y.carryLive with
    | false =>
        rw [hyc] at hc
        cases hc
    | true =>
        simp [digitLaneReplay, hxl, hyl, hxo, hyb, hyc,
          OutTok.isD]

/-- An occupied old responder D and its OLD provenance remain
paired, regardless of the independent source QI/QC branches. -/
private theorem topPortFrameReplayResponderOccupied
    {c : Compiled} {n : Nat}
    (clock : Nat) (e ysite : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hyo : y.out = .D v tail) :
    (digitLaneReplay .comparison clock e ysite x y gx gy).y.out.atom =
      gy.out.atom := by
  simp [digitLaneReplay, hxl, hyl, hyo,
    OutTok.isD, OutTok.isE]

/-- The selected full physical TOP owner has the same BLOCKED
source-D equation regardless of the SI-resolved writer betas:
comparison QO reads the OLD marker. -/
private theorem topPortFrameSourceOwnerBlocked {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hyb : (D (ring.rightNeighbor e)).beta = true)
    (hxo : (D e).qOut = .D v tail)
    (hblock :
      (D (ring.rightNeighbor e)).qIn.isE = false ∨
      (D (ring.rightNeighbor e)).qCarry.isOff = false) :
    (topPortLiteralTopOwner ring D e).x.qOut = .D v tail := by
  unfold topPortLiteralTopOwner
  exact topPortFrameSourceLiteralBlocked
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _
    v tail hxl hyl hyb hxo hblock

/-- The selected full physical TOP owner keeps a pre-existing
responder-D output, even in a simultaneous input/carry service. -/
private theorem topPortFrameResponderOwnerOccupied {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hyo : (D (ring.rightNeighbor e)).qOut = .D v tail) :
    (topPortLiteralTopOwner ring D e).y.qOut = .D v tail := by
  unfold topPortLiteralTopOwner
  exact topPortFrameResponderLiteralOccupied
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _
    v tail hxl hyl hyo

/-- A blocked source offer preserves BOTH the actual qOut D
and the OLD audit comparison packet atom. The primitive
source projection is used in the equality's hypothesis. -/
private theorem topPortFrameSourcePair {n : Nat}
    (ring : DirectedRing n) (C D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hyb : (D (ring.rightNeighbor e)).beta = true)
    (hxo : (D e).qOut = .D v tail)
    (hblock :
      (D (ring.rightNeighbor e)).qIn.isE = false ∨
      (D (ring.rightNeighbor e)).qCarry.isOff = false) :
    (topFixedPublicNext ring C D e e).qOut = .D v tail ∧
    ((digitAuditStep ring (piD D) A e).current e).comparison.out.atom =
      (A.current e).comparison.out.atom := by
  constructor
  · calc
      (topFixedPublicNext ring C D e e).qOut =
          (topPortLiteralTopOwner ring D e).x.qOut :=
        (topPortLiteralSourceFields ring C D e).2.2
      _ = .D v tail :=
        topPortFrameSourceOwnerBlocked
          ring D e v tail hxl hyl hyb hxo hblock
  · simp only [digitAuditStep, digitGhostStep, if_pos rfl]
    change
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison (piD D e)
          (piD D e).word.beta)
        (digitLaneView .comparison (piD D (ring.rightNeighbor e))
          (piD D (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).x.out.atom =
      (A.current e).comparison.out.atom
    have hblockView :
      (digitLaneView .comparison (piD D (ring.rightNeighbor e))
        (piD D (ring.rightNeighbor e)).word.beta).input.isE = false ∨
      (digitLaneView .comparison (piD D (ring.rightNeighbor e))
        (piD D (ring.rightNeighbor e)).word.beta).carryLive = true := by
      rcases hblock with hinput | hcarry
      · exact Or.inl hinput
      · apply Or.inr
        cases hc : (D (ring.rightNeighbor e)).qCarry with
        | OFF =>
            rw [hc] at hcarry
            cases hcarry
        | L bit err =>
            change (D (ring.rightNeighbor e)).qCarry.isL = true
            rw [hc]
            rfl
    exact topPortFrameReplaySourceBlocked
      (A.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison (piD D e) (piD D e).word.beta)
      (digitLaneView .comparison (piD D (ring.rightNeighbor e))
        (piD D (ring.rightNeighbor e)).word.beta)
      (A.current e).comparison
      (A.current (ring.rightNeighbor e)).comparison
      v tail hxl hyl hxo hyb hblockView

/-- When the old ready port is the RESPONDER, its occupied
output and provenance frame on the true physical and audit pair.
The adjacent endpoint distinction is explicit. -/
private theorem topPortFrameResponderPair {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hyo : (D (ring.rightNeighbor e)).qOut = .D v tail) :
    (topFixedPublicNext ring C D e (ring.rightNeighbor e)).qOut =
      .D v tail ∧
    ((digitAuditStep ring (piD D) A e).current
      (ring.rightNeighbor e)).comparison.out.atom =
      (A.current (ring.rightNeighbor e)).comparison.out.atom := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  constructor
  · calc
      (topFixedPublicNext ring C D e (ring.rightNeighbor e)).qOut =
          (topPortLiteralTopOwner ring D e).y.qOut :=
        (topPortLiteralResponderFields ring hn C D e).2.2
      _ = .D v tail :=
        topPortFrameResponderOwnerOccupied
          ring D e v tail hxl hyl hyo
  · simp only [digitAuditStep, digitGhostStep,
      if_neg hne, if_pos rfl]
    change
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison (piD D e)
          (piD D e).word.beta)
        (digitLaneView .comparison (piD D (ring.rightNeighbor e))
          (piD D (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).y.out.atom =
      (A.current (ring.rightNeighbor e)).comparison.out.atom
    exact topPortFrameReplayResponderOccupied
      (A.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison (piD D e) (piD D e).word.beta)
      (digitLaneView .comparison (piD D (ring.rightNeighbor e))
        (piD D (ring.rightNeighbor e)).word.beta)
      (A.current e).comparison
      (A.current (ring.rightNeighbor e)).comparison
      v tail hxl hyl hyo

/-- If the ready packet's host is not selected at either
endpoint, both its physical D and its atom literally frame. -/
private theorem topPortFrameAwayPair {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e p : Fin n) (he : p ≠ e)
    (hy : p ≠ ring.rightNeighbor e) :
    (topFixedPublicNext ring C D e p).qOut = (D p).qOut ∧
    ((digitAuditStep ring (piD D) A e).current p).comparison.out.atom =
      (A.current p).comparison.out.atom := by
  constructor
  · exact (topPortLiteralAwayFields ring C D e p he hy).2.2
  · simp only [digitAuditStep, digitGhostStep,
      if_neg he, if_neg hy]

/-- The actual accepting service can only be the original
source exit -> beta-marked target-border edge. -/
private theorem topPortFrameBorderGeometry {n : Nat}
    (ring : DirectedRing n) (s : Fin n) :
    ring.rightNeighbor (certSite s (topClockSpan n - 1)) =
      certSite s (topClockSpan n) := by
  rw [topPortNeighborCertSite]
  have hr : 3 ≤ topClockSpan n := topPortSpanThreeAll n
  have hindex :
      topClockSpan n - 1 + 1 = topClockSpan n := by omega
  rw [hindex]

/-- Complete-pair public geometry identifies the unique
predecessor of the old source port without ordering Fin.val. -/
private theorem topPortFrameBeforeSource {n : Nat}
    (ring : DirectedRing n) (s e : Fin n)
    (hnext : ring.rightNeighbor e =
      certSite s (topClockSpan n - 1)) :
    e = certSite s (topClockSpan n - 2) := by
  have hr : 3 ≤ topClockSpan n := topPortSpanThreeAll n
  have hbefore :
      ring.rightNeighbor (certSite s (topClockSpan n - 2)) =
        certSite s (topClockSpan n - 1) := by
    rw [topPortNeighborCertSite]
    have hindex :
        topClockSpan n - 2 + 1 = topClockSpan n - 1 := by omega
    rw [hindex]
  exact topPortNeighborInjective ring e
    (certSite s (topClockSpan n - 2))
    (hnext.trans hbefore.symm)

/-- The first requested hframe, on the exact original
fixed-public TOP observer and OLD digit-audit receipts.
All nonstopping edges preserve the ready packet and its atom.
No coloured suffix or pending-barrier assumption is inserted. -/
theorem topPortPhysicalFrame_holds {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s) :
    ∀ Z : TopFixedTraceState n, ∀ e : Fin n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e) ∨
      (topClockReached ring C (topFixedTraceNext ring C Z e) ∧
       topClockPortReady s atom (topFixedTraceNext ring C Z e)) := by
  intro Z e hreach hready hnot
  by_cases hstop :
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z e)
  · exact Or.inl hstop
  · apply Or.inr
    have hnextReach := topPortReachedNext ring C Z e hreach
    constructor
    · exact hnextReach
    · obtain ⟨v, tail, houtput, hatom⟩ := hready
      have hr : 3 ≤ topClockSpan n := topPortSpanThreeAll n
      have hport : ring.rightNeighbor
          (certSite s (topClockSpan n - 1)) =
          certSite s (topClockSpan n) :=
        topPortFrameBorderGeometry ring s
      have hpFollower :
          (Z.1.1 (certSite s (topClockSpan n - 1))).l = false := by
        calc
          (Z.1.1 (certSite s (topClockSpan n - 1))).l =
            (C (certSite s (topClockSpan n - 1))).l :=
              (topPortReachedPublicMask ring C Z hreach _).1
          _ = false :=
            topPortEligibleFollower C s hbad
              (topClockSpan n - 1) (by omega)
      by_cases he : e = certSite s (topClockSpan n - 1)
      · subst e
        have htargetFollower :
            (Z.1.1 (ring.rightNeighbor
              (certSite s (topClockSpan n - 1)))).l = false := by
          rw [hport]
          exact topPortReachedTargetFollower ring C s hbad Z
            hreach ⟨0, by omega⟩
        have htargetBeta :
            (Z.1.1 (ring.rightNeighbor
              (certSite s (topClockSpan n - 1)))).beta = true := by
          rw [hport]
          exact topPortReachedBorderMarker ring C s hbad Z hreach
        have hblock :
            (Z.1.1 (ring.rightNeighbor
              (certSite s (topClockSpan n - 1)))).qIn.isE = false ∨
            (Z.1.1 (ring.rightNeighbor
              (certSite s (topClockSpan n - 1)))).qCarry.isOff = false := by
          cases hi : (Z.1.1 (ring.rightNeighbor
              (certSite s (topClockSpan n - 1)))).qIn with
          | E =>
              cases hc : (Z.1.1 (ring.rightNeighbor
                  (certSite s (topClockSpan n - 1)))).qCarry with
              | OFF =>
                  have hfirst : topPortReadyOfferFirstMatch ring s Z
                      (certSite s (topClockSpan n - 1)) :=
                    ⟨rfl, hport, hi, hc⟩
                  exact False.elim
                    (hstop (topPortReadyOfferFirstMatchStops
                      ring C s atom hbad Z
                      (certSite s (topClockSpan n - 1))
                      hreach ⟨v, tail, houtput, hatom⟩ hfirst))
              | L bit err =>
                  exact Or.inr rfl
          | P value tailFlag =>
              exact Or.inl rfl
          | S value tailFlag =>
              exact Or.inl rfl
          | X =>
              exact Or.inl rfl
        have hpair := topPortFrameSourcePair ring C Z.1.1 Z.1.2
          (certSite s (topClockSpan n - 1)) v tail
          hpFollower htargetFollower htargetBeta houtput hblock
        exact ⟨v, tail, hpair.1, hpair.2.trans hatom⟩
      · by_cases hy : ring.rightNeighbor e =
            certSite s (topClockSpan n - 1)
        · have hsourceBefore :=
            topPortFrameBeforeSource ring s e hy
          have hprevFollower : (Z.1.1 e).l = false := by
            rw [hsourceBefore]
            calc
              (Z.1.1 (certSite s (topClockSpan n - 2))).l =
                (C (certSite s (topClockSpan n - 2))).l :=
                  (topPortReachedPublicMask ring C Z hreach _).1
              _ = false :=
                topPortEligibleFollower C s hbad
                  (topClockSpan n - 2) (by omega)
          have hpair := topPortFrameResponderPair ring
            (by have hs := topPortSpanLeOfBad C s hbad; omega)
            C Z.1.1 Z.1.2 e v tail hprevFollower
            (by rw [hy]; exact hpFollower)
            (by rw [hy]; exact houtput)
          have hportOutput :
              (topFixedPublicNext ring C Z.1.1 e
                (certSite s (topClockSpan n - 1))).qOut =
                  .D v tail := by
            rw [← hy]
            exact hpair.1
          have hportAtom :
              ((digitAuditStep ring (piD Z.1.1) Z.1.2 e).current
                (certSite s (topClockSpan n - 1))).comparison.out.atom =
                  (Z.1.2.current
                    (certSite s (topClockSpan n - 1))).comparison.out.atom := by
            rw [← hy]
            exact hpair.2
          exact ⟨v, tail, hportOutput, hportAtom.trans hatom⟩
        · have hpair := topPortFrameAwayPair
            ring C Z.1.1 Z.1.2 e
            (certSite s (topClockSpan n - 1))
            (by intro eq; exact he eq.symm)
            (by intro eq; exact hy eq.symm)
          exact ⟨v, tail, hpair.1.trans houtput,
            hpair.2.trans hatom⟩

/-- The touched-row product plus the new frame makes
progress the only remaining LOCAL P.2 row input. -/
def topPortPhysicalRowsStopOfProgress {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s)
    (chosen : TopFixedTraceState n → Fin n)
    (hprogress : ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z (chosen Z)) ∨
      topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
        topPortPotential s Z) :
    TopPortPhysicalRowsStop ring C s atom := by
  exact topPortPhysicalRowsStop ring C s atom
    hbad chosen (topPortPhysicalFrame_holds ring C s atom hbad)
    hprogress

/-- Conditional full P.2 producer: the original frame and
the nonincrease are accounted for, leaving ONLY
the nominated progress edge as a source obligation. -/
theorem topClockPortPhaseOfProgress {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (hchosen : ∀ atom : Option (DigitAtom n),
      ∃ chosen : TopFixedTraceState n → Fin n,
        ∀ Z : TopFixedTraceState n,
          topClockReached ring C Z →
          topClockPortReady s atom Z →
          ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
          topClockStopOr ring C s (topClockPortAccepted s atom)
            (topFixedTraceNext ring C Z (chosen Z)) ∨
          topPortPotential s (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤
            topPortPotential s Z) :
    TopClockPortPhase ring C s := by
  classical
  have hpositive : 0 < n := by
    have hspan : 3 ≤ topClockSpan n := topPortSpanThreeAll n
    have hle : topClockSpan n ≤ n := topPortSpanLeOfBad C s hbad
    omega
  apply topClockPortPhaseOfStopRows ring C s hpositive
  intro atom
  -- A Type-valued row must use a chosen witness, not
  -- large elimination of an existential proof.
  exact topPortPhysicalRowsStopOfProgress ring C s atom hbad
    (Classical.choose (hchosen atom))
    (Classical.choose_spec (hchosen atom))

end L3



/-!
Frontier-edge candidate for the remaining P.2 progress field.

The edge is selected
from OLD physical target QI/QC (and the ready source port), not
from the audit future.  A free target border calls the actual source
offer; otherwise the greatest mobile target offset is serviced.
If none is mobile, the blocked border must be settled non-tail, so
its QC3 launch edge is serviced.  The last-offset case uses the third
public beta marker and treats the cyclic self-pair separately.

All statements below use the actual topFixedTraceNext.  No change
is made to the existing 5080-line prefix.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- An OLD target slot requires active service unless it is empty
or an internal settled non-tail with no live carry. -/
private def topPortMobile {a : Nat}
    (input : InTok a) (carry : QCarry) : Bool :=
  match carry with
  | .L _ _ => true
  | .OFF =>
      match input with
      | .P _ _ => true
      | .X => true
      | .S _ true => true
      | _ => false

private theorem topPortMobileFalse {a : Nat}
    (input : InTok a) (carry : QCarry)
    (h : topPortMobile input carry = false) :
    carry = .OFF ∧
      (input = .E ∨ ∃ v : Fin a, input = .S v false) := by
  cases carry with
  | L bit err =>
      simp [topPortMobile] at h
  | OFF =>
      constructor
      · rfl
      · cases input with
        | E => exact Or.inl rfl
        | X => simp [topPortMobile] at h
        | P v tail => simp [topPortMobile] at h
        | S v tail =>
            cases tail with
            | true => simp [topPortMobile] at h
            | false => exact Or.inr ⟨v, rfl⟩

private def topPortMobileAt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) : Bool :=
  topPortMobile
    (Z.1.1 (certSite s (topClockSpan n + j))).qIn
    (Z.1.1 (certSite s (topClockSpan n + j))).qCarry

/-- The largest active offset in [0,k), with zero fallback.
The recursion checks k-1 first. -/
private def topPortRightmost {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      if topPortMobileAt s Z k = true then k
      else topPortRightmost s Z k

private theorem topPortRightmostLt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) :
    ∀ k : Nat, 0 < k → topPortRightmost s Z k < k := by
  intro k
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro hk
      by_cases hm : topPortMobileAt s Z k = true
      · simp only [topPortRightmost, if_pos hm]
        omega
      · simp only [topPortRightmost, if_neg hm]
        by_cases hzero : k = 0
        · subst k
          simp [topPortRightmost]
        · have hbound := ih (by omega)
          omega

private theorem topPortRightmostUpper {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) :
    ∀ k i : Nat, i < k →
      topPortMobileAt s Z i = true →
      i ≤ topPortRightmost s Z k := by
  intro k
  induction k with
  | zero =>
      intro i hi hm
      omega
  | succ k ih =>
      intro i hi hm
      by_cases hilast : i = k
      · subst i
        simp only [topPortRightmost, if_pos hm]
        exact Nat.le_refl k
      · have hiprev : i < k := by omega
        by_cases hcur : topPortMobileAt s Z k = true
        · simp only [topPortRightmost, if_pos hcur]
          omega
        · simp only [topPortRightmost, if_neg hcur]
          exact ih i hiprev hm

private theorem topPortRightmostActiveOrZero {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) :
    ∀ k : Nat,
      topPortRightmost s Z k = 0 ∨
      topPortMobileAt s Z (topPortRightmost s Z k) = true := by
  intro k
  induction k with
  | zero =>
      exact Or.inl rfl
  | succ k ih =>
      by_cases hm : topPortMobileAt s Z k = true
      · right
        simpa only [topPortRightmost, if_pos hm] using hm
      · simpa only [topPortRightmost, if_neg hm] using ih

/-- The next OLD slot to the right of the frontier is passive;
otherwise the choice would not have been rightmost. -/
private theorem topPortRightmostNextPassive {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) (k : Nat)
    (hnext : topPortRightmost s Z k + 1 < k) :
    topPortMobileAt s Z (topPortRightmost s Z k + 1) =
      false := by
  cases hm : topPortMobileAt s Z
      (topPortRightmost s Z k + 1) with
  | false => rfl
  | true =>
      have hmax := topPortRightmostUpper s Z k
        (topPortRightmost s Z k + 1) hnext hm
      omega

/-! OLD joint checker rows. The independent writer fields
never enter these charges; checker QO cannot birth into a
nonmarker responder. All tail/old-carry combinations are covered. -/

/-! Mechanically separated QI/QC row calculations. The
old source/target charges are deliberately unchanged. Each result
is computed from the literal `liveTopPair` checker owner at one
specified pair of OLD token tags (no enormous product split). -/

private def topPortInteriorAfter {c : Compiled} (r j : Nat)
    (x y : Agent c) (resolvedX resolvedY : Bool) : Nat :=
  topPortSiteWeight r j
      (liveTopPair c x y resolvedX resolvedY).x.qIn
      (liveTopPair c x y resolvedX resolvedY).x.qCarry +
    topPortSiteWeight r (j + 1)
      (liveTopPair c x y resolvedX resolvedY).y.qIn
      (liveTopPair c x y resolvedX resolvedY).y.qCarry

private def topPortBorderAfter {c : Compiled} (r : Nat)
    (x y : Agent c) (resolvedX resolvedY : Bool) : Nat :=
  topPortSiteWeight r 0
      (liveTopPair c x y resolvedX resolvedY).x.qIn
      (liveTopPair c x y resolvedX resolvedY).x.qCarry +
    topPortSiteWeight r 1
      (liveTopPair c x y resolvedX resolvedY).y.qIn
      (liveTopPair c x y resolvedX resolvedY).y.qCarry

private def topPortTerminalAfter {c : Compiled} (r : Nat)
    (x y : Agent c) (resolvedX resolvedY : Bool) : Nat :=
  topPortSiteWeight r (r - 1)
    (liveTopPair c x y resolvedX resolvedY).x.qIn
    (liveTopPair c x y resolvedX resolvedY).x.qCarry

/-- One literal interior QI/QC row: old source OFF,
source Front, responder Empty. -/
private theorem topPortInteriorRowOffFrontEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source Front, responder Settled. -/
private theorem topPortInteriorRowOffFrontSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source PendingNonTail, responder Empty. -/
private theorem topPortInteriorRowOffPendingNonTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) + 2 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source PendingNonTail, responder Settled. -/
private theorem topPortInteriorRowOffPendingNonTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 2 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte] <;> omega
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source PendingTail, responder Empty. -/
private theorem topPortInteriorRowOffPendingTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) + 2 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source PendingTail, responder Settled. -/
private theorem topPortInteriorRowOffPendingTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - j + 2 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source SettledTail, responder Empty. -/
private theorem topPortInteriorRowOffSettledTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - j := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source OFF,
source SettledTail, responder Settled. -/
private theorem topPortInteriorRowOffSettledTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - j + 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source Empty, responder Empty. -/
private theorem topPortInteriorRowLiveEmptyEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .E)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source Empty, responder Settled. -/
private theorem topPortInteriorRowLiveEmptySettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .E)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source Front, responder Empty. -/
private theorem topPortInteriorRowLiveFrontEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source Front, responder Settled. -/
private theorem topPortInteriorRowLiveFrontSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source PendingNonTail, responder Empty. -/
private theorem topPortInteriorRowLivePendingNonTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source PendingNonTail, responder Settled. -/
private theorem topPortInteriorRowLivePendingNonTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source PendingTail, responder Empty. -/
private theorem topPortInteriorRowLivePendingTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source PendingTail, responder Settled. -/
private theorem topPortInteriorRowLivePendingTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source SettledNonTail, responder Empty. -/
private theorem topPortInteriorRowLiveSettledNonTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source SettledNonTail, responder Settled. -/
private theorem topPortInteriorRowLiveSettledNonTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source SettledTail, responder Empty. -/
private theorem topPortInteriorRowLiveSettledTailEmpty
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal interior QI/QC row: old source live carry,
source SettledTail, responder Settled. -/
private theorem topPortInteriorRowLiveSettledTailSettled
    {c : Compiled} (r j : Nat) (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
      topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  have hdist : r - j = r - (j + 1) + 1 := by omega
  have hnonzero : j ≠ 0 := by omega
  have hnew : topPortInteriorAfter r j x y resolvedX resolvedY = r - (j + 1) := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortInteriorAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi, hnonzero] <;> omega

/-- One literal border QI/QC row: old source OFF,
source Front, responder Empty. -/
private theorem topPortBorderRowOffFrontEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source Front, responder Settled. -/
private theorem topPortBorderRowOffFrontSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source PendingNonTail, responder Empty. -/
private theorem topPortBorderRowOffPendingNonTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r + 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte] <;> omega
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source PendingNonTail, responder Settled. -/
private theorem topPortBorderRowOffPendingNonTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r + 2 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source PendingTail, responder Empty. -/
private theorem topPortBorderRowOffPendingTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r + 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte] <;> omega
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source PendingTail, responder Settled. -/
private theorem topPortBorderRowOffPendingTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r + 2 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source SettledNonTail, responder Empty. -/
private theorem topPortBorderRowOffSettledNonTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source SettledNonTail, responder Settled. -/
private theorem topPortBorderRowOffSettledNonTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r + 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source SettledTail, responder Empty. -/
private theorem topPortBorderRowOffSettledTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source OFF,
source SettledTail, responder Settled. -/
private theorem topPortBorderRowOffSettledTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r + 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source Empty, responder Empty. -/
private theorem topPortBorderRowLiveEmptyEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .E)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source Empty, responder Settled. -/
private theorem topPortBorderRowLiveEmptySettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .E)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source Front, responder Empty. -/
private theorem topPortBorderRowLiveFrontEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source Front, responder Settled. -/
private theorem topPortBorderRowLiveFrontSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .X)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source PendingNonTail, responder Empty. -/
private theorem topPortBorderRowLivePendingNonTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source PendingNonTail, responder Settled. -/
private theorem topPortBorderRowLivePendingNonTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source PendingTail, responder Empty. -/
private theorem topPortBorderRowLivePendingTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source PendingTail, responder Settled. -/
private theorem topPortBorderRowLivePendingTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source SettledNonTail, responder Empty. -/
private theorem topPortBorderRowLiveSettledNonTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source SettledNonTail, responder Settled. -/
private theorem topPortBorderRowLiveSettledNonTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v false)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source SettledTail, responder Empty. -/
private theorem topPortBorderRowLiveSettledTailEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = 0 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal border QI/QC row: old source live carry,
source SettledTail, responder Settled. -/
private theorem topPortBorderRowLiveSettledTailSettled
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (bit err : Bool) (v : Fin c.topA) (w : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v true)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .S w false) :
    topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
      topPortSiteWeight r 1 y.qIn y.qCarry := by
  have hdist : r - 1 + 1 = r := by omega
  have hnew : topPortBorderAfter r x y resolvedX resolvedY = r - 1 := by
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortBorderAfter,
        liveTopPair,
      topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
      topTerminal, topInternal, topBorder,
      QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
      InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
      hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hyc, hyi] <;> omega

/-- One literal terminal QI/QC row: old source OFF,
source Front, responder arbitrary terminal. -/
private theorem topPortTerminalRowOffFront
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .X) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry <;>
      cases hyi : y.qIn <;>
      cases hqo : x.qOut <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
          liveTopPair,
        topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
        topTerminal, topInternal, topBorder,
        QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
        InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
        hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
        hnonzero, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source OFF,
source PendingNonTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowOffPendingNonTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v false) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 1 := by
    cases hyc : y.qCarry <;>
      cases hyi : y.qIn <;>
      cases hqo : x.qOut <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
          liveTopPair,
        topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
        topTerminal, topInternal, topBorder,
        QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
        InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
        hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
        hnonzero, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source OFF,
source PendingTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowOffPendingTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .P v true) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry <;>
      cases hyi : y.qIn <;>
      cases hqo : x.qOut <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
          liveTopPair,
        topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
        topTerminal, topInternal, topBorder,
        QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
        InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
        hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
        hnonzero, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source OFF,
source SettledTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowOffSettledTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (v : Fin c.topA)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v true) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 1 := by
    cases hyc : y.qCarry <;>
      cases hyi : y.qIn <;>
      cases hqo : x.qOut <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
          liveTopPair,
        topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
        topTerminal, topInternal, topBorder,
        QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
        InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
        hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
        hnonzero, hdist, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source live carry,
source Empty, responder arbitrary terminal. -/
private theorem topPortTerminalRowLiveEmpty
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (bit err : Bool)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .E) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry <;>
      cases hyi : y.qIn <;>
      cases hqo : x.qOut <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
          liveTopPair,
        topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
        topTerminal, topInternal, topBorder,
        QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
        InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
        hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
        hnonzero, ↓reduceIte]
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source live carry,
source Front, responder arbitrary terminal. -/
private theorem topPortTerminalRowLiveFront
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (bit err : Bool)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .X) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry with
    | OFF =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
    | L responderBit responderErr =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source live carry,
source PendingNonTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowLivePendingNonTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v false) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry with
    | OFF =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
    | L responderBit responderErr =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source live carry,
source PendingTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowLivePendingTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .P v true) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry with
    | OFF =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
    | L responderBit responderErr =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source live carry,
source SettledNonTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowLiveSettledNonTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v false) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry with
    | OFF =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
    | L responderBit responderErr =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

/-- One literal terminal QI/QC row: old source live carry,
source SettledTail, responder arbitrary terminal. -/
private theorem topPortTerminalRowLiveSettledTail
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (bit err : Bool) (v : Fin c.topA)
    (hxc : x.qCarry = .L bit err)
    (hxi : x.qIn = .S v true) :
    topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  have hdist : r - (r - 1) = 1 := by omega
  have hnonzero : r - 1 ≠ 0 := by omega
  have hnew : topPortTerminalAfter r x y resolvedX resolvedY = 0 := by
    cases hyc : y.qCarry with
    | OFF =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
    | L responderBit responderErr =>
        cases hyi : y.qIn with
        | E =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | X =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | P responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
        | S responderValue responderTail =>
            cases hqo : x.qOut <;>
              simp only [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
                  ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut,
                  ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry,
                  ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut, liveTopWC,
                  liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, topPortTerminalAfter,
                  liveTopPair,
                topPortSiteWeight, topPortInputWeight, topPortCarryWeight,
                topTerminal, topInternal, topBorder,
                QCarry.isOff, QCarry.isL, InTok.isE, InTok.isP,
                InTok.isS, InTok.isX, OutTok.isD, inT, inV, QC,
                hxl, hyl, hxb, hyb, hxc, hxi, hyc, hyi, hqo,
                ↓reduceIte] <;> rfl
  rw [hnew]
  simp [topPortSiteWeight, topPortInputWeight,
    topPortCarryWeight, hxc, hxi, hnonzero] <;> omega

private theorem topPortOwnerInteriorDrop
    {c : Compiled} (r j : Nat)
    (hj : 0 < j) (hnext : j + 1 < r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (hm : topPortMobile x.qIn x.qCarry = true)
    (hp : topPortMobile y.qIn y.qCarry = false) :
    topPortSiteWeight r j
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry +
      topPortSiteWeight r (j + 1)
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry + 1 ≤
      topPortSiteWeight r j x.qIn x.qCarry +
        topPortSiteWeight r (j + 1) y.qIn y.qCarry := by
  change topPortInteriorAfter r j x y resolvedX resolvedY + 1 ≤
    topPortSiteWeight r j x.qIn x.qCarry +
    topPortSiteWeight r (j + 1) y.qIn y.qCarry
  rcases topPortMobileFalse y.qIn y.qCarry hp with ⟨hyc, hy⟩
  rcases hy with hyi | ⟨w, hyi⟩
  · cases hxc : x.qCarry with
    | OFF =>
        cases hxi : x.qIn with
        | E => simp [topPortMobile, hxc, hxi] at hm
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffFrontEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffPendingNonTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffPendingTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simp [topPortMobile, hxc, hxi] at hm
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffSettledTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
    | L bit err =>
        cases hxi : x.qIn with
        | E =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveEmptyEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err hxc hxi hyc hyi)
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveFrontEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLivePendingNonTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLivePendingTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveSettledNonTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveSettledTailEmpty r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
  · cases hxc : x.qCarry with
    | OFF =>
        cases hxi : x.qIn with
        | E => simp [topPortMobile, hxc, hxi] at hm
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffFrontSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb w hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffPendingNonTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffPendingTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simp [topPortMobile, hxc, hxi] at hm
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowOffSettledTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
    | L bit err =>
        cases hxi : x.qIn with
        | E =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveEmptySettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err w hxc hxi hyc hyi)
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveFrontSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err w hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLivePendingNonTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLivePendingTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveSettledNonTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortInteriorRowLiveSettledTailSettled r j hj hnext x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)

private theorem topPortOwnerBorderDrop
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hyb : y.beta = false)
    (hb : ¬ (x.qIn = .E ∧ x.qCarry = .OFF))
    (hp : topPortMobile y.qIn y.qCarry = false) :
    topPortSiteWeight r 0
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry +
      topPortSiteWeight r 1
        (liveTopPair c x y resolvedX resolvedY).y.qIn
        (liveTopPair c x y resolvedX resolvedY).y.qCarry + 1 ≤
      topPortSiteWeight r 0 x.qIn x.qCarry +
        topPortSiteWeight r 1 y.qIn y.qCarry := by
  change topPortBorderAfter r x y resolvedX resolvedY + 1 ≤
    topPortSiteWeight r 0 x.qIn x.qCarry +
    topPortSiteWeight r 1 y.qIn y.qCarry
  rcases topPortMobileFalse y.qIn y.qCarry hp with ⟨hyc, hy⟩
  rcases hy with hyi | ⟨w, hyi⟩
  · cases hxc : x.qCarry with
    | OFF =>
        cases hxi : x.qIn with
        | E => exact False.elim (hb ⟨hxi, hxc⟩)
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffFrontEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffPendingNonTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffPendingTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffSettledNonTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffSettledTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi hyc hyi)
    | L bit err =>
        cases hxi : x.qIn with
        | E =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveEmptyEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err hxc hxi hyc hyi)
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveFrontEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLivePendingNonTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLivePendingTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveSettledNonTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveSettledTailEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi hyc hyi)
  · cases hxc : x.qCarry with
    | OFF =>
        cases hxi : x.qIn with
        | E => exact False.elim (hb ⟨hxi, hxc⟩)
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffFrontSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb w hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffPendingNonTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffPendingTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffSettledNonTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowOffSettledTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb v w hxc hxi hyc hyi)
    | L bit err =>
        cases hxi : x.qIn with
        | E =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveEmptySettled r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err w hxc hxi hyc hyi)
        | X =>
            simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveFrontSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err w hxc hxi hyc hyi)
        | P v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLivePendingNonTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLivePendingTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)
        | S v tail =>
            cases tail with
            | false =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveSettledNonTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)
            | true =>
                simpa only [hxc, hxi, hyc, hyi] using (topPortBorderRowLiveSettledTailSettled r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v w hxc hxi hyc hyi)

/-- The third beta marker terminates pending inputs at the last
target offset. Neither the responder's old input nor its carry
is assumed clean; only the OLD source is charged here. -/
private theorem topPortOwnerTerminalDrop
    {c : Compiled} (r : Nat) (hr : 2 ≤ r)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = true)
    (hm : topPortMobile x.qIn x.qCarry = true) :
    topPortSiteWeight r (r - 1)
        (liveTopPair c x y resolvedX resolvedY).x.qIn
        (liveTopPair c x y resolvedX resolvedY).x.qCarry + 1 ≤
      topPortSiteWeight r (r - 1) x.qIn x.qCarry := by
  change topPortTerminalAfter r x y resolvedX resolvedY + 1 ≤
    topPortSiteWeight r (r - 1) x.qIn x.qCarry
  cases hxc : x.qCarry with
  | OFF =>
      cases hxi : x.qIn with
      | E => simp [topPortMobile, hxc, hxi] at hm
      | X =>
          simpa only [hxc, hxi] using (topPortTerminalRowOffFront r hr x y resolvedX resolvedY hxl hyl hxb hyb hxc hxi)
      | P v tail =>
          cases tail with
          | false =>
              simpa only [hxc, hxi] using (topPortTerminalRowOffPendingNonTail r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi)
          | true =>
              simpa only [hxc, hxi] using (topPortTerminalRowOffPendingTail r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi)
      | S v tail =>
          cases tail with
          | false =>
              simp [topPortMobile, hxc, hxi] at hm
          | true =>
              simpa only [hxc, hxi] using (topPortTerminalRowOffSettledTail r hr x y resolvedX resolvedY hxl hyl hxb hyb v hxc hxi)
  | L bit err =>
      cases hxi : x.qIn with
      | E =>
          simpa only [hxc, hxi] using (topPortTerminalRowLiveEmpty r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err hxc hxi)
      | X =>
          simpa only [hxc, hxi] using (topPortTerminalRowLiveFront r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err hxc hxi)
      | P v tail =>
          cases tail with
          | false =>
              simpa only [hxc, hxi] using (topPortTerminalRowLivePendingNonTail r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi)
          | true =>
              simpa only [hxc, hxi] using (topPortTerminalRowLivePendingTail r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi)
      | S v tail =>
          cases tail with
          | false =>
              simpa only [hxc, hxi] using (topPortTerminalRowLiveSettledNonTail r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi)
          | true =>
              simpa only [hxc, hxi] using (topPortTerminalRowLiveSettledTail r hr x y resolvedX resolvedY hxl hyl hxb hyb bit err v hxc hxi)

/-- Strict counterpart of the two-index W-swap: the
same OLD first-match table is used, but with one extra unit
on the NEW side of the touched-pair inequality. -/
private theorem topPortStrictLift {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hloc :
      (if topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e) then
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) + 1 ≤
          topPortWeightAt s Z (topPortIndexAtSite s e)
      else
        topPortOldPairAfterWeight ring s Z e
            (topPortIndexAtSite s e) +
          topPortOldPairAfterWeight ring s Z e
            (topPortIndexAtSite s (ring.rightNeighbor e)) + 1 ≤
          topPortWeightAt s Z (topPortIndexAtSite s e) +
          topPortWeightAt s Z
            (topPortIndexAtSite s (ring.rightNeighbor e)))) :
    topPortPotential s (topFixedTraceNext ring C Z e) + 1 ≤
      topPortPotential s Z := by
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hn : 2 ≤ n := by omega
  have hframe : ∀ j : Fin (topClockSpan n),
      j ≠ topPortIndexAtSite s e →
      j ≠ topPortIndexAtSite s (ring.rightNeighbor e) →
      topPortWeightAt s (topFixedTraceNext ring C Z e) j =
        topPortWeightAt s Z j := by
    intro j hji hjk
    have hx : certSite s (topClockSpan n + j.val) ≠ e := by
      intro he
      rcases topPortSelectedEdgeCover ring C s hbad e
          j (Or.inl he) with hfirst | hsecond
      · exact hji hfirst
      · exact hjk hsecond
    have hy : certSite s (topClockSpan n + j.val) ≠
        ring.rightNeighbor e := by
      intro he
      rcases topPortSelectedEdgeCover ring C s hbad e
          j (Or.inr he) with hfirst | hsecond
      · exact hji hfirst
      · exact hjk hsecond
    exact topPortWeightAtAway ring C s Z e j hx hy
  have hloc' :
      (if topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e) then
        topPortWeightAt s (topFixedTraceNext ring C Z e)
          (topPortIndexAtSite s e)
      else
        topPortWeightAt s (topFixedTraceNext ring C Z e)
            (topPortIndexAtSite s e) +
          topPortWeightAt s (topFixedTraceNext ring C Z e)
            (topPortIndexAtSite s (ring.rightNeighbor e))) + 1 ≤
      (if topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e) then
        topPortWeightAt s Z (topPortIndexAtSite s e)
      else
        topPortWeightAt s Z (topPortIndexAtSite s e) +
          topPortWeightAt s Z
            (topPortIndexAtSite s (ring.rightNeighbor e))) := by
    by_cases heq : topPortIndexAtSite s e =
        topPortIndexAtSite s (ring.rightNeighbor e)
    · simp only [if_pos heq] at hloc ⊢
      rw [topPortOldPairAfterWeight_eq ring hn C s Z e
        (topPortIndexAtSite s e)]
      exact hloc
    · simp only [if_neg heq] at hloc ⊢
      rw [topPortOldPairAfterWeight_eq ring hn C s Z e
          (topPortIndexAtSite s e),
        topPortOldPairAfterWeight_eq ring hn C s Z e
          (topPortIndexAtSite s (ring.rightNeighbor e))]
      exact hloc
  have hbalance := topPortSumTwoSwap
    (topPortWeightAt s Z)
    (topPortWeightAt s (topFixedTraceNext ring C Z e))
    (topPortIndexAtSite s e)
    (topPortIndexAtSite s (ring.rightNeighbor e))
    hframe
  have hsum :
      (List.ofFn (topPortWeightAt s
        (topFixedTraceNext ring C Z e))).sum + 1 ≤
      (List.ofFn (topPortWeightAt s Z)).sum := by
    omega
  change
    (List.ofFn (topPortWeightAt s
      (topFixedTraceNext ring C Z e))).sum + 1 ≤
    (List.ofFn (topPortWeightAt s Z)).sum
  exact hsum

/-- A frontier at offset j<r-1 has a passive OLD responder,
so the corresponding two-site literal checker row drops W. -/
private theorem topPortInternalFrontierDrop {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (hnext : j.val + 1 < topClockSpan n)
    (hsource : e = certSite s (topClockSpan n + j.val))
    (htarget : ring.rightNeighbor e =
      certSite s (topClockSpan n + (j.val + 1)))
    (hblocked : ¬
      ((Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
       (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF))
    (hmobile : 0 < j.val →
      topPortMobileAt s Z j.val = true)
    (hpassive : topPortMobileAt s Z (j.val + 1) = false) :
    topPortPotential s (topFixedTraceNext ring C Z e) + 1 ≤
      topPortPotential s Z := by
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hn : 2 ≤ n := by omega
  have hxsite : certSite s (topClockSpan n + j.val) = e :=
    hsource.symm
  have hysite : certSite s (topClockSpan n + (j.val + 1)) =
      ring.rightNeighbor e := htarget.symm
  have hix : topPortIndexAtSite s e = j :=
    topPortMemberIndex s hle j e hxsite
  have hiy : topPortIndexAtSite s (ring.rightNeighbor e) =
      (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) :=
    topPortMemberIndex s hle ⟨j.val + 1, hnext⟩
      (ring.rightNeighbor e) hysite
  have hne : j ≠ (⟨j.val + 1, hnext⟩ :
      Fin (topClockSpan n)) := by
    intro heq
    have hv := congrArg Fin.val heq
    change j.val = j.val + 1 at hv
    omega
  have hxl : (Z.1.1 e).l = false := by
    rw [hsource]
    exact topPortReachedTargetFollower ring C s hbad Z hreach j
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [htarget]
    exact topPortReachedTargetFollower ring C s hbad Z hreach
      ⟨j.val + 1, hnext⟩
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    rw [htarget]
    exact topPortReachedTargetInteriorMarker ring C s hbad
      Z hreach ⟨j.val + 1, hnext⟩ (Nat.zero_lt_succ j.val)
  have hp : topPortMobile
      (Z.1.1 (ring.rightNeighbor e)).qIn
      (Z.1.1 (ring.rightNeighbor e)).qCarry = false := by
    unfold topPortMobileAt at hpassive
    rw [← htarget] at hpassive
    exact hpassive
  have hraw :
      topPortSiteWeight (topClockSpan n) j.val
          (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
          (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry +
        topPortSiteWeight (topClockSpan n) (j.val + 1)
          (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
          (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry + 1 ≤
      topPortSiteWeight (topClockSpan n) j.val
          (Z.1.1 e).qIn (Z.1.1 e).qCarry +
        topPortSiteWeight (topClockSpan n) (j.val + 1)
          (Z.1.1 (ring.rightNeighbor e)).qIn
          (Z.1.1 (ring.rightNeighbor e)).qCarry := by
    by_cases hz : j.val = 0
    · have hxb : (Z.1.1 e).beta = true := by
        rw [hsource, hz]
        simpa only [Nat.add_zero] using
          (topPortReachedBorderMarker ring C s hbad Z hreach)
      have hb : ¬ ((Z.1.1 e).qIn = .E ∧
          (Z.1.1 e).qCarry = .OFF) := by
        rw [hsource, hz, Nat.add_zero]
        exact hblocked
      simpa only [hz, Nat.zero_add, topPortLiteralTopOwner] using
        (topPortOwnerBorderDrop (topClockSpan n)
          (by omega) (Z.1.1 e)
          (Z.1.1 (ring.rightNeighbor e)) _ _
          hxl hyl hxb hyb hb hp)
    · have hjpos : 0 < j.val := by omega
      have hxb : (Z.1.1 e).beta = false := by
        rw [hsource]
        exact topPortReachedTargetInteriorMarker ring C s
          hbad Z hreach j hjpos
      have hm : topPortMobile (Z.1.1 e).qIn
          (Z.1.1 e).qCarry = true := by
        unfold topPortMobileAt at hmobile
        rw [← hsource] at hmobile
        exact hmobile hjpos
      simpa only [topPortLiteralTopOwner] using
        (topPortOwnerInteriorDrop (topClockSpan n) j.val
          hjpos hnext (Z.1.1 e)
          (Z.1.1 (ring.rightNeighbor e)) _ _
          hxl hyl hxb hyb hm hp)
  have hpair :
      topPortOldPairAfterWeight ring s Z e j +
        topPortOldPairAfterWeight ring s Z e
          (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) + 1 ≤
      topPortWeightAt s Z j +
        topPortWeightAt s Z
          (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) := by
    calc
      topPortOldPairAfterWeight ring s Z e j +
          topPortOldPairAfterWeight ring s Z e
            (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) + 1 =
        topPortSiteWeight (topClockSpan n) j.val
            (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry +
          topPortSiteWeight (topClockSpan n) (j.val + 1)
            (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry + 1 := by
              rw [topPortAfterAtSource ring s Z e j hxsite,
                topPortAfterAtResponder ring hn s Z e
                  ⟨j.val + 1, hnext⟩ hysite]
      _ ≤ topPortSiteWeight (topClockSpan n) j.val
              (Z.1.1 e).qIn (Z.1.1 e).qCarry +
            topPortSiteWeight (topClockSpan n) (j.val + 1)
              (Z.1.1 (ring.rightNeighbor e)).qIn
              (Z.1.1 (ring.rightNeighbor e)).qCarry := hraw
      _ = topPortWeightAt s Z j +
            topPortWeightAt s Z
              (⟨j.val + 1, hnext⟩ :
                Fin (topClockSpan n)) := by
              rw [topPortBeforeAtSource s Z e j hxsite,
                topPortBeforeAtResponder ring s Z e
                  ⟨j.val + 1, hnext⟩ hysite]
  have hlocal :
      (if topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e) then
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) + 1 ≤
          topPortWeightAt s Z (topPortIndexAtSite s e)
      else
        topPortOldPairAfterWeight ring s Z e
            (topPortIndexAtSite s e) +
          topPortOldPairAfterWeight ring s Z e
            (topPortIndexAtSite s (ring.rightNeighbor e)) + 1 ≤
          topPortWeightAt s Z (topPortIndexAtSite s e) +
          topPortWeightAt s Z
            (topPortIndexAtSite s (ring.rightNeighbor e))) := by
    rw [hix, hiy]
    simp only [if_neg hne]
    exact hpair
  exact topPortStrictLift ring C s hbad Z e hlocal

/-- At offset r-1 the successor is the third marker. The
source clears or settles strictly. The target-border coordinate
is either untouched or nonincreasing under the blocked offer
guard, including the cyclic self-pair. -/
private theorem topPortTerminalFrontierDrop {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hlast : e =
      certSite s (topClockSpan n + (topClockSpan n - 1)))
    (hblocked : ¬
      ((Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
       (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF))
    (hmobile : topPortMobileAt s Z (topClockSpan n - 1) = true) :
    topPortPotential s (topFixedTraceNext ring C Z e) + 1 ≤
      topPortPotential s Z := by
  have hspan := topPortSpanThreeAll n
  have hle := topPortSpanLeOfBad C s hbad
  have hn : 2 ≤ n := by omega
  have hlastsite :
      certSite s (topClockSpan n + (topPortLastIndex n).val) =
        e := by
    change certSite s (topClockSpan n + (topClockSpan n - 1)) = e
    exact hlast.symm
  have hix : topPortIndexAtSite s e = topPortLastIndex n :=
    topPortMemberIndex s hle (topPortLastIndex n) e hlastsite
  have htarget :
      ring.rightNeighbor e = certSite s (2 * topClockSpan n) := by
    rw [hlast, topPortNeighborCertSite]
    congr 1
    omega
  have hxl : (Z.1.1 e).l = false := by
    rw [hlast]
    exact topPortReachedTargetFollower ring C s hbad Z hreach
      (topPortLastIndex n)
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [htarget]
    calc
      (Z.1.1 (certSite s (2 * topClockSpan n))).l =
        (C (certSite s (2 * topClockSpan n))).l :=
          (topPortReachedPublicMask ring C Z hreach _).1
      _ = false :=
        topPortEligibleFollower C s hbad
          (2 * topClockSpan n) (by omega)
  have hxb : (Z.1.1 e).beta = false := by
    rw [hlast]
    exact topPortReachedTargetInteriorMarker ring C s hbad
      Z hreach (topPortLastIndex n) (by
        change 0 < topClockSpan n - 1
        omega)
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [htarget]
    calc
      (Z.1.1 (certSite s (2 * topClockSpan n))).beta =
        (C (certSite s (2 * topClockSpan n))).beta :=
          (topPortReachedPublicMask ring C Z hreach _).2
      _ = true := hbad.1.2.2.1
  have hm : topPortMobile (Z.1.1 e).qIn
      (Z.1.1 e).qCarry = true := by
    unfold topPortMobileAt at hmobile
    rw [← hlast] at hmobile
    exact hmobile
  have hstrict :
      topPortOldPairAfterWeight ring s Z e
          (topPortLastIndex n) + 1 ≤
        topPortWeightAt s Z (topPortLastIndex n) := by
    calc
      topPortOldPairAfterWeight ring s Z e
          (topPortLastIndex n) + 1 =
        topPortSiteWeight (topClockSpan n) (topClockSpan n - 1)
            (topPortLiteralTopOwner ring Z.1.1 e).x.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).x.qCarry + 1 := by
              rw [topPortAfterAtSource ring s Z e
                (topPortLastIndex n) hlastsite] <;>
              simp only [topPortLastIndex]
      _ ≤ topPortSiteWeight (topClockSpan n) (topClockSpan n - 1)
            (Z.1.1 e).qIn (Z.1.1 e).qCarry := by
              simpa only [topPortLiteralTopOwner] using
                (topPortOwnerTerminalDrop (topClockSpan n)
                  (by omega) (Z.1.1 e)
                  (Z.1.1 (ring.rightNeighbor e)) _ _
                  hxl hyl hxb hyb hm)
      _ = topPortWeightAt s Z (topPortLastIndex n) :=
        (topPortBeforeAtSource s Z e
          (topPortLastIndex n) hlastsite).symm
  have hnotSourceZero :
      certSite s (topClockSpan n + (topPortZeroIndex n).val) ≠
        e := by
    intro hzeroSource
    have hidx : topPortZeroIndex n = topPortLastIndex n := by
      apply topPortTargetSiteInj s hle
      exact hzeroSource.trans hlastsite.symm
    exact (topPortZeroLastNe n) hidx.symm
  have hiy :
      topPortIndexAtSite s (ring.rightNeighbor e) =
        topPortZeroIndex n := by
    by_cases hb : ring.rightNeighbor e =
        certSite s (topClockSpan n)
    · have hysite :
          certSite s (topClockSpan n + (topPortZeroIndex n).val) =
            ring.rightNeighbor e := by
        change certSite s (topClockSpan n + 0) =
          ring.rightNeighbor e
        rw [Nat.add_zero]
        exact hb.symm
      exact topPortMemberIndex s hle (topPortZeroIndex n)
        (ring.rightNeighbor e) hysite
    · have hout :
          ∀ j : Fin (topClockSpan n),
            certSite s (topClockSpan n + j.val) ≠
              ring.rightNeighbor e := by
        intro j hj
        have hjzero := topPortAfterLastMemberBorder
          ring s hle e hlast j hj
        apply hb
        calc
          ring.rightNeighbor e =
              certSite s (topClockSpan n + j.val) := hj.symm
          _ = certSite s (topClockSpan n) := by
            rw [hjzero, Nat.add_zero]
      exact topPortOutsideIndexZero s (ring.rightNeighbor e) hout
  have hzero :
      topPortOldPairAfterWeight ring s Z e
          (topPortZeroIndex n) ≤
        topPortWeightAt s Z (topPortZeroIndex n) := by
    by_cases hb : ring.rightNeighbor e =
        certSite s (topClockSpan n)
    · have hysite :
          certSite s (topClockSpan n + (topPortZeroIndex n).val) =
            ring.rightNeighbor e := by
        change certSite s (topClockSpan n + 0) =
          ring.rightNeighbor e
        rw [Nat.add_zero]
        exact hb.symm
      have hblockedY :
          ¬ ((Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
             (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) := by
        rw [hb]
        exact hblocked
      have hdestRaw := topPortLiteralBorderBlockedBound
        ring Z e (topClockSpan n) hyb hblockedY
      calc
        topPortOldPairAfterWeight ring s Z e
            (topPortZeroIndex n) =
          topPortSiteWeight (topClockSpan n) 0
            (topPortLiteralTopOwner ring Z.1.1 e).y.qIn
            (topPortLiteralTopOwner ring Z.1.1 e).y.qCarry :=
              topPortAfterAtResponder ring hn s Z e
                (topPortZeroIndex n) hysite
        _ ≤ topPortSiteWeight (topClockSpan n) 0
              (Z.1.1 (ring.rightNeighbor e)).qIn
              (Z.1.1 (ring.rightNeighbor e)).qCarry := hdestRaw
        _ = topPortWeightAt s Z (topPortZeroIndex n) :=
          (topPortBeforeAtResponder ring s Z e
            (topPortZeroIndex n) hysite).symm
    · have hout :
          ∀ j : Fin (topClockSpan n),
            certSite s (topClockSpan n + j.val) ≠
              ring.rightNeighbor e := by
        intro j hj
        have hjzero := topPortAfterLastMemberBorder
          ring s hle e hlast j hj
        apply hb
        calc
          ring.rightNeighbor e =
              certSite s (topClockSpan n + j.val) := hj.symm
          _ = certSite s (topClockSpan n) := by
            rw [hjzero, Nat.add_zero]
      exact Nat.le_of_eq
        (topPortAfterAway ring s Z e (topPortZeroIndex n)
          hnotSourceZero (hout (topPortZeroIndex n)))
  have hpair :
      topPortOldPairAfterWeight ring s Z e
          (topPortLastIndex n) +
        topPortOldPairAfterWeight ring s Z e
          (topPortZeroIndex n) + 1 ≤
      topPortWeightAt s Z (topPortLastIndex n) +
        topPortWeightAt s Z (topPortZeroIndex n) := by
    omega
  have hlocal :
      (if topPortIndexAtSite s e =
          topPortIndexAtSite s (ring.rightNeighbor e) then
        topPortOldPairAfterWeight ring s Z e
          (topPortIndexAtSite s e) + 1 ≤
          topPortWeightAt s Z (topPortIndexAtSite s e)
      else
        topPortOldPairAfterWeight ring s Z e
            (topPortIndexAtSite s e) +
          topPortOldPairAfterWeight ring s Z e
            (topPortIndexAtSite s (ring.rightNeighbor e)) + 1 ≤
          topPortWeightAt s Z (topPortIndexAtSite s e) +
          topPortWeightAt s Z
            (topPortIndexAtSite s (ring.rightNeighbor e))) := by
    rw [hix, hiy]
    simp only [if_neg (topPortZeroLastNe n)]
    exact hpair
  exact topPortStrictLift ring C s hbad Z e hlocal

/-- A history-measurable OLD-state frontier choice:
offer if the border is free, otherwise service the rightmost
mobile obstruction (falling back to a blocked S(false) border). -/
def topPortFrontierEdge {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Fin n :=
  if (Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
      (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF then
    certSite s (topClockSpan n - 1)
  else
    certSite s
      (topClockSpan n +
        topPortRightmost s Z (topClockSpan n))

/-- Candidate LOCAL P.2 progress, with no new geometric, mobile,
or future-trace premise beyond the existing BadCompletePair
and the ready/reached/nonstopped hypotheses. -/
theorem topPortFrontierProgress {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s) :
    ∀ Z : TopFixedTraceState n,
      topClockReached ring C Z →
      topClockPortReady s atom Z →
      ¬ topClockStopOr ring C s (topClockPortAccepted s atom) Z →
      topClockStopOr ring C s (topClockPortAccepted s atom)
        (topFixedTraceNext ring C Z (topPortFrontierEdge s Z)) ∨
      topPortPotential s
          (topFixedTraceNext ring C Z (topPortFrontierEdge s Z)) + 1 ≤
        topPortPotential s Z := by
  intro Z hreach hready hnot
  have hr : 3 ≤ topClockSpan n := topPortSpanThreeAll n
  by_cases hfree :
      (Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
      (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF
  · apply Or.inl
    simp only [topPortFrontierEdge, if_pos hfree]
    apply topPortReadyOfferFirstMatchStops ring C s atom hbad Z
      (certSite s (topClockSpan n - 1)) hreach hready
    refine ⟨rfl, topPortFrameBorderGeometry ring s, ?_, ?_⟩
    · rw [topPortFrameBorderGeometry ring s]
      exact hfree.1
    · rw [topPortFrameBorderGeometry ring s]
      exact hfree.2
  · apply Or.inr
    simp only [topPortFrontierEdge, if_neg hfree]
    have hj :
        topPortRightmost s Z (topClockSpan n) <
          topClockSpan n :=
      topPortRightmostLt s Z (topClockSpan n) (by omega)
    have hactive : 0 < topPortRightmost s Z (topClockSpan n) →
        topPortMobileAt s Z
          (topPortRightmost s Z (topClockSpan n)) = true := by
      intro hpositive
      rcases topPortRightmostActiveOrZero s Z (topClockSpan n) with
        hz | hm
      · omega
      · exact hm
    by_cases hnext :
        topPortRightmost s Z (topClockSpan n) + 1 <
          topClockSpan n
    · have hpassive :=
        topPortRightmostNextPassive s Z (topClockSpan n) hnext
      apply topPortInternalFrontierDrop ring C s hbad Z hreach
        (certSite s
          (topClockSpan n + topPortRightmost s Z (topClockSpan n)))
        (⟨topPortRightmost s Z (topClockSpan n), hj⟩ :
          Fin (topClockSpan n))
        hnext rfl
      · rw [topPortNeighborCertSite]
        congr 1 <;> omega
      · exact hfree
      · intro hpositive
        exact hactive hpositive
      · exact hpassive
    · have hlast :
        topPortRightmost s Z (topClockSpan n) =
          topClockSpan n - 1 := by omega
      apply topPortTerminalFrontierDrop ring C s hbad Z hreach
        (certSite s
          (topClockSpan n + topPortRightmost s Z (topClockSpan n)))
      · rw [hlast]
      · exact hfree
      · rw [← hlast]
        exact hactive (by omega)

/-- The stop-aware nonincrease field is already established:
topPortFourCoordinateProductStop_holds supplies it.  The
new field here is solely the explicit OLD-frontier progress. -/
def topPortPhysicalFrontierRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (atom : Option (DigitAtom n))
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopPortPhysicalRowsStop ring C s atom :=
  topPortPhysicalRowsStopOfProgress ring C s atom hbad
    (topPortFrontierEdge s)
    (topPortFrontierProgress ring C s atom hbad)

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Receipt/physical Appendix-P cut classes. -/

/-- P, lines 55--59: physical target input. -/
def topClockConcreteInputAt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (j : Fin (topClockSpan n)) :=
  (Z.1.1 (certSite s (topClockSpan n + j.val))).qIn

/-- P, lines 55--59: independent target carry. -/
def topClockConcreteCarryAt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (j : Fin (topClockSpan n)) :=
  (Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry

/-- Actual audit ancestry on a target input. -/
def topClockConcreteInputAtom {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (j : Fin (topClockSpan n)) : Option (DigitAtom n) :=
  (Z.1.2.current
    (certSite s (topClockSpan n + j.val))).comparison.input

/-- P, lines 373--382, 429--436: chronological comparison
exports after the nominated genuine accepted tail. -/
noncomputable def topClockConcreteExportsAfter {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (anchorTime : Nat) :
    List (DigitExport (compileAdvice (ceilLogTwo n)) n) :=
  ((Z.1.2.frames.reverse.filterMap
    (fun frame =>
      (digitReceiptLane .comparison frame.receipt).exported)).filter
    (fun exported =>
      if anchorTime < exported.time ∧
          exported.source = certSite s (topClockSpan n - 1) ∧
          exported.destination = certSite s (topClockSpan n)
      then true else false))

/-- The chronological serial lookup uses a bounded Fin index. -/
noncomputable def topClockConcreteExportAt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (anchorTime : Nat)
    (i : Fin (topClockConcreteExportsAfter s Z anchorTime).length) :
    DigitExport (compileAdvice (ceilLogTwo n)) n :=
  (topClockConcreteExportsAfter s Z anchorTime)[i.val]'i.isLt

/-- P, lines 62--69 and 373--382: an actual sampled
origin-zero tail, exported through the correct source port. -/
def topClockConcreteTailAnchor {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  DigitRecordedExport Z.1.2 anchor ∧
  anchor.lane = .comparison ∧
  anchor.source = certSite s (topClockSpan n - 1) ∧
  anchor.destination = certSite s (topClockSpan n) ∧
  anchor.tail = true ∧
  ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
    DigitRecordedSample Z.1.2 sample ∧
    sample.id.lane = .comparison ∧
    sample.id.site = certSite s 0 ∧
    sample.tail = true ∧
    sample.id.time < anchor.time ∧
    anchor.operand = some (.sampled sample.id) ∧
    anchor.value = sample.value

/-- P, lines 62--69, 429--436: serial i has sampled
origin r-1-(i mod r), with only each final member a tail.
Receipts, values and atoms must agree. -/
noncomputable def topClockConcretePureStream {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ i : Fin (topClockConcreteExportsAfter s Z anchor.time).length,
    ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample Z.1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site =
        certSite s
          (topClockSpan n - 1 - (i.val % topClockSpan n)) ∧
      sample.tail =
        (if i.val % topClockSpan n = topClockSpan n - 1
         then true else false) ∧
      (topClockConcreteExportAt s Z anchor.time i).operand =
        some (.sampled sample.id) ∧
      (topClockConcreteExportAt s Z anchor.time i).value =
        sample.value ∧
      (topClockConcreteExportAt s Z anchor.time i).tail =
        sample.tail

/-- Source purity is an anchored, genuine-receipt invariant;
it is not a True predicate on arbitrary inherited scratch. -/
noncomputable def topClockConcretePureCohorts {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
    topClockConcreteTailAnchor s Z anchor ∧
    topClockConcretePureStream s Z anchor

/-- P, lines 438--450: moving pending strictly left of
settled material, erasure fronts, and live carries. -/
def topClockConcreteMovingBarrier {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∀ i j : Fin (topClockSpan n),
    (topClockConcreteInputAt s Z i).isP = true →
    ((topClockConcreteInputAt s Z j).isS = true ∨
      topClockConcreteInputAt s Z j = .X ∨
      (topClockConcreteCarryAt s Z j).isL = true) →
    i.val < j.val

/-- P, lines 452--471: every generated carry has an empty
host, no settled input/front on its left, and no competing
live carry. Its actual ghost ledger is not inherited. -/
def topClockConcreteGeneratedCarryGap {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∀ j : Fin (topClockSpan n),
    (topClockConcreteCarryAt s Z j).isL = true →
      topClockConcreteInputAt s Z j = .E ∧
      (∀ i : Fin (topClockSpan n), i.val < j.val →
        (topClockConcreteInputAt s Z i).isE = true ∨
        (topClockConcreteInputAt s Z i).isP = true) ∧
      (∀ k : Fin (topClockSpan n),
        (topClockConcreteCarryAt s Z k).isL = true → k = j) ∧
      ∃ ledger : DigitCarryGhost
          (compileAdvice (ceilLogTwo n)) n,
        (Z.1.2.current
          (certSite s (topClockSpan n + j.val))).comparison.carry =
            some ledger ∧
        ledger.inherited = none

/-- P, lines 473--503: analytical active/doomed colouring.
Every doomed settled member has a contiguous protected run
whose immediate left predecessor is X. An X followed by
settled material marks that first settled member doomed. -/
def topClockConcreteFrontProtection {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∃ doomed : Fin (topClockSpan n) → Prop,
    (∀ j, doomed j →
      (topClockConcreteInputAt s Z j).isS = true) ∧
    (∀ j, doomed j →
      ∃ left : Fin (topClockSpan n),
        left.val < j.val ∧
        topClockConcreteInputAt s Z left = .X ∧
        (∀ k : Fin (topClockSpan n),
          left.val < k.val → k.val ≤ j.val →
          (topClockConcreteInputAt s Z k).isS = true ∧
          doomed k)) ∧
    (∀ left j : Fin (topClockSpan n),
      topClockConcreteInputAt s Z left = .X →
      j.val = left.val + 1 →
      (topClockConcreteInputAt s Z j).isS = true →
      doomed j)

/-- P, lines 505--513: old settled material prevents
NEW terminal settlement on each actual scheduler edge.
The invariant is a local, history-readable safety condition. -/
def topClockConcreteNoTerminalReseed {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∀ e : Fin n,
    (∃ j : Fin (topClockSpan n),
      (topClockConcreteInputAt s Z j).isS = true) →
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (topClockSpan n + (topClockSpan n - 1)))).qIn.isS =
        true →
    (Z.1.1
      (certSite s (topClockSpan n + (topClockSpan n - 1)))).qIn.isS =
        true

/-- P, lines 427--450 and 822--847: physical pending records
are precisely a suffix of the accepted pure-source serials,
with gaps allowed and with matching audit input atoms. -/
noncomputable def topClockConcreteConsecutivePendingSuffix {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
    topClockConcreteTailAnchor s Z anchor ∧
    topClockConcretePureStream s Z anchor ∧
    ∃ k : Nat,
      k ≤ (topClockConcreteExportsAfter s Z anchor.time).length ∧
      (∀ j : Fin (topClockSpan n),
        (topClockConcreteInputAt s Z j).isP = true →
          ∃ i : Fin (topClockConcreteExportsAfter s Z anchor.time).length,
            k ≤ i.val ∧
            topClockConcreteInputAtom s Z j =
              (topClockConcreteExportAt s Z anchor.time i).operand ∧
            ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA)
              (tail : Bool),
              topClockConcreteInputAt s Z j = .P v tail ∧
              (topClockConcreteExportAt s Z anchor.time i).value = v ∧
              (topClockConcreteExportAt s Z anchor.time i).tail = tail) ∧
      (∀ i : Fin (topClockConcreteExportsAfter s Z anchor.time).length,
        k ≤ i.val →
          ∃ j : Fin (topClockSpan n),
            (topClockConcreteInputAt s Z j).isP = true ∧
            topClockConcreteInputAtom s Z j =
              (topClockConcreteExportAt s Z anchor.time i).operand) ∧
      (∀ i j : Fin (topClockSpan n),
        (topClockConcreteInputAt s Z i).isP = true →
        (topClockConcreteInputAt s Z j).isP = true →
        topClockConcreteInputAtom s Z i =
          topClockConcreteInputAtom s Z j →
        i = j)

/-- P.3, lines 373--382: genuine tail and future pure cohorts. -/
noncomputable def topClockConcreteFirstTail {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  topClockGenuineTailAccepted C s Z ∧
  topClockConcretePureCohorts s Z

/-- The five-colour restart conjunction, P.4--P.10,
lines 410--427 and 438--513. -/
noncomputable def topClockConcreteColoured {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  topClockConcretePureCohorts s Z ∧
  topClockConcreteMovingBarrier s Z ∧
  topClockConcreteGeneratedCarryGap s Z ∧
  topClockConcreteFrontProtection s Z ∧
  topClockConcreteNoTerminalReseed ring C s Z

/-- T_(S=0), P lines 797--835. -/
noncomputable def topClockConcreteSettledEmpty {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  topClockConcretePureCohorts s Z ∧
  topClockTargetSettledEmpty s Z

/-- The pure pending-only pi restart, P lines 822--847. -/
noncomputable def topClockConcretePendingOnly {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  topClockConcretePureCohorts s Z ∧
  topClockConcreteConsecutivePendingSuffix s Z ∧
  topClockTargetPendingOnly s Z

/-- P lines 919--977: the genuine origin-zero S(true) tail
is at a nonborder h, older non-tail S(false) operands occupy
the whole right suffix, younger inputs are E/P, and carries OFF. -/
def topClockConcreteMisplacedAt {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n)
    (h : Fin (topClockSpan n)) : Prop :=
  1 ≤ h.val ∧ h.val + 1 < topClockSpan n ∧
  (∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
    DigitRecordedSample Z.1.2 sample ∧
    sample.id.lane = .comparison ∧
    sample.id.site = certSite s 0 ∧
    sample.tail = true ∧
    topClockConcreteInputAt s Z h = .S sample.value true ∧
    topClockConcreteInputAtom s Z h =
      some (.sampled sample.id)) ∧
  (∀ j : Fin (topClockSpan n), h.val < j.val →
    ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample Z.1.2 sample ∧
      sample.id.lane = .comparison ∧
      sample.id.site = certSite s (j.val - h.val) ∧
      sample.tail = false ∧
      topClockConcreteInputAt s Z j = .S sample.value false ∧
      topClockConcreteInputAtom s Z j =
        some (.sampled sample.id)) ∧
  (∀ j : Fin (topClockSpan n), j.val < h.val →
    (topClockConcreteInputAt s Z j).isE = true ∨
    (topClockConcreteInputAt s Z j).isP = true) ∧
  (∀ j : Fin (topClockSpan n),
    topClockConcreteCarryAt s Z j = .OFF)

/-- P lines 930--948: actual reached misaligned tail-race cut. -/
noncomputable def topClockConcreteMisplacedTail {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  topClockConcretePureCohorts s Z ∧
  topClockConcreteConsecutivePendingSuffix s Z ∧
  ∃ h : Fin (topClockSpan n), topClockConcreteMisplacedAt s Z h

/-- P lines 950--955, 999--1033: the OWN f_h outgoing edge
wins and the OLD settled tail becomes an erasure front. -/
noncomputable def topClockConcreteFavourable {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  ∃ (pre : List (Fin n)) (h : Fin (topClockSpan n)),
    topClockConcreteMisplacedTail ring C s
      (topFixedTraceRun ring C pre) ∧
    topClockConcreteMisplacedAt s (topFixedTraceRun ring C pre) h ∧
    Z.2 = pre ++ [certSite s (topClockSpan n + h.val)] ∧
    (Z.1.1 (certSite s (topClockSpan n + h.val))).qIn = .X

/-- P lines 1035--1055: the actual f_(h-1) incoming
edge wins; the analytical attempt is abandoned at its
entire coloured successor, even if it merely framed. -/
noncomputable def topClockConcreteUnfavourable {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  topClockConcreteColoured ring C s Z ∧
  ∃ (pre : List (Fin n)) (h : Fin (topClockSpan n)),
    topClockConcreteMisplacedTail ring C s
      (topFixedTraceRun ring C pre) ∧
    topClockConcreteMisplacedAt s (topFixedTraceRun ring C pre) h ∧
    Z.2 = pre ++ [certSite s (topClockSpan n + h.val - 1)]

/-- Concrete predicates populate every field of the P.1
interface. Seven spec projections are immediate constructors.
No class is literally False or a generic stand-in True. -/
noncomputable def topClockConcreteCutClasses {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) : TopClockCutClasses ring C s :=
  { pureCohorts := topClockConcretePureCohorts s
    movingBarrier := topClockConcreteMovingBarrier s
    generatedCarryGap := topClockConcreteGeneratedCarryGap s
    frontProtection := topClockConcreteFrontProtection s
    noTerminalReseed := topClockConcreteNoTerminalReseed ring C s
    consecutivePendingSuffix := topClockConcreteConsecutivePendingSuffix s
    firstTail := topClockConcreteFirstTail ring C s
    coloured := topClockConcreteColoured ring C s
    settledEmpty := topClockConcreteSettledEmpty ring C s
    pendingOnly := topClockConcretePendingOnly ring C s
    misplacedTail := topClockConcreteMisplacedTail ring C s
    favourable := topClockConcreteFavourable ring C s
    unfavourable := topClockConcreteUnfavourable ring C s
    firstTailSpec := by
      intro Z h
      exact h
    colouredSpec := by
      intro Z h
      exact h
    settledSpec := by
      intro Z h
      exact h
    pendingSpec := by
      intro Z h
      exact h
    misplacedSpec := by
      intro Z h
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    favourableSpec := by
      intro Z h
      exact h.1
    unfavourableSpec := by
      intro Z h
      exact h.1 }

/-- The class ring exists as a type-level witness for every
public pair; this does NOT assert each phase is reached. -/
theorem topClockConcreteClassesExist {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) :
    Nonempty (TopClockCutClasses ring C s) :=
  ⟨topClockConcreteCutClasses ring C s⟩

/-- A real reached reference cut: the original zero-letter cut. -/
theorem topClockConcreteInitialReached {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    topClockReached ring C (topFixedTraceRun ring C []) := by
  rfl

/-- P.2 for complete pairs, from the stop-aware frontier,
frame and all-four-coordinate nonincrease. -/
theorem topClockConcretePortPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockPortPhase ring C s := by
  have hn : 0 < n :=
    Nat.lt_of_le_of_lt (Nat.zero_le s.val) s.isLt
  exact topClockPortPhaseOfStopRows ring C s hn
    (fun atom => topPortPhysicalFrontierRows ring C s atom hbad)

end L3
