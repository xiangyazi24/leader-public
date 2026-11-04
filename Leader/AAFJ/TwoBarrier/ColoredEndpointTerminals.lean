import Leader.AAFJ.TwoBarrier.EndpointRace
import Leader.Core.PayloadFiniteStoppingTree

/-!
# Direction-colored two-endpoint service terminals

The scalar two-endpoint clock forgets which endpoint completed service.  This
module retains the literal post-configuration and partitions the first stopped
child into rear advance, front advance, or charged contact.  It supplies the
exact observable needed by a transported-gap Bellman argument; no directional
drift claim is made here.
-/

set_option autoImplicit false

namespace AAFJPK.TwoEndpointColoredClock

open BarrierAlgebra
open PersistentBarrierService
open TwoEndpointServiceClock
open PayloadFiniteStoppingTree
open FiniteUniformStoppingTree

inductive TerminalKind where
  | rearAdvance
  | frontAdvance
  | contact
deriving DecidableEq

def ContactAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (D : Fin n → State k) (b : Fin n) : Prop :=
  BarrierAt hk ring (labelsOf D) b ∧
    (BarrierAt hk ring (labelsOf D) (ring.rightNeighbor b) ∨
      ∃ a, ring.rightNeighbor a = b ∧ BarrierAt hk ring (labelsOf D) a)

def TerminalKind.Holds {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C D : Fin n → State k) (rear front e : Fin n) : TerminalKind → Prop
  | .rearAdvance =>
      (e = rear ∧ AdvanceReady hk ring C rear) ∧
        ¬ ContactAt hk ring D rear ∧ ¬ ContactAt hk ring D front
  | .frontAdvance =>
      (e = front ∧ AdvanceReady hk ring C front) ∧
        ¬ ContactAt hk ring D rear ∧ ¬ ContactAt hk ring D front
  | .contact => ContactAt hk ring D rear ∨ ContactAt hk ring D front

private theorem preContact_not_contact
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (D : Fin n → State k) (b : Fin n) (h : PreContact hk ring D b) :
    ¬ ContactAt hk ring D b := by
  rintro ⟨_, hright | ⟨a, ha, hleft⟩⟩
  · exact h.2.1 hright
  · exact h.2.2 a ha hleft

/-- A colored terminal retains the actual child configuration and a proof of
the advertised physical event. -/
structure TerminalPayload {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) where
  origin : ActivePair hk ring
  config : Fin n → State k
  edge : Fin n
  kind : TerminalKind
  holds : kind.Holds hk ring origin.config config origin.rear origin.front edge

private theorem one_terminal_contact_or_advance
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C D : Fin n → State k) (b e : Fin n)
    (h : PersistentBarrierClock.ServiceTerminal hk ring C D b e) :
    (e = b ∧ AdvanceReady hk ring C b) ∨ ContactAt hk ring D b := by
  exact h

/-- The literal scheduler child with its first endpoint event retained. -/
noncomputable def coloredStep
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) (e : Fin n) :
    PayloadNode (ActivePair hk ring)
      (TerminalPayload hk ring) Empty := by
  classical
  let D := (protocol k hk).step ring st.config e
  if hr : PreContact hk ring D st.rear then
    if hf : PreContact hk ring D st.front then
      exact .active
        { config := D
          rear := st.rear
          front := st.front
          ne := st.ne
          rearPre := hr
          frontPre := hf }
    else
      have ht := PersistentBarrierClock.not_preContact_child_terminal
        hk ring hn3 st.config st.front e st.frontPre (by simpa [D] using hf)
      by_cases hcontact : ContactAt hk ring D st.front
      · exact .success
          { origin := st, config := D, edge := e, kind := .contact,
            holds := Or.inr hcontact }
      · have hadv : e = st.front ∧ AdvanceReady hk ring st.config st.front :=
          (one_terminal_contact_or_advance hk ring st.config D st.front e ht).resolve_right hcontact
        exact .success
          { origin := st, config := D, edge := e, kind := .frontAdvance,
            holds := ⟨hadv, preContact_not_contact hk ring D st.rear hr,
              hcontact⟩ }
  else
    have ht := PersistentBarrierClock.not_preContact_child_terminal
      hk ring hn3 st.config st.rear e st.rearPre (by simpa [D] using hr)
    by_cases hcontact : ContactAt hk ring D st.rear
    · exact .success
        { origin := st, config := D, edge := e, kind := .contact,
          holds := Or.inl hcontact }
    · have hadv : e = st.rear ∧ AdvanceReady hk ring st.config st.rear :=
        (one_terminal_contact_or_advance hk ring st.config D st.rear e ht).resolve_right hcontact
      by_cases hfrontContact : ContactAt hk ring D st.front
      · exact .success
          { origin := st, config := D, edge := e, kind := .contact,
            holds := Or.inr hfrontContact }
      · exact .success
          { origin := st, config := D, edge := e, kind := .rearAdvance,
            holds := ⟨hadv, hcontact, hfrontContact⟩ }

/-- Forgetting the color gives exactly the accepted scalar two-endpoint step. -/
theorem erase_coloredStep
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) (e : Fin n) :
    (coloredStep hn3 st e).erase = TwoEndpointServiceClock.step st e := by
  classical
  let D := (protocol k hk).step ring st.config e
  by_cases hr : PreContact hk ring D st.rear
  · by_cases hf : PreContact hk ring D st.front
    · let next : ActivePair hk ring :=
        { config := D
          rear := st.rear
          front := st.front
          ne := st.ne
          rearPre := hr
          frontPre := hf }
      have hc : coloredStep hn3 st e = .active next := by
        simp [coloredStep, D, hr, hf, next]
      have hs : TwoEndpointServiceClock.step st e = .active next := by
        simp [TwoEndpointServiceClock.step, D, hr, hf, next]
      rw [hc, hs]
      rfl
    · by_cases hcontact : ContactAt hk ring D st.front <;>
        simp [coloredStep, TwoEndpointServiceClock.step, D, hr, hf, hcontact,
          PayloadNode.erase]
  · by_cases hrearContact : ContactAt hk ring D st.rear
    · simp [coloredStep, TwoEndpointServiceClock.step, D, hr, hrearContact,
        PayloadNode.erase]
    · by_cases hfrontContact : ContactAt hk ring D st.front <;>
        simp [coloredStep, TwoEndpointServiceClock.step, D, hr, hrearContact,
          hfrontContact, PayloadNode.erase]

/-- Exact finite-tree mass of one terminal color. -/
noncomputable def colorMass
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (color : TerminalKind) :
    (x : PayloadNode (ActivePair hk ring) (TerminalPayload hk ring) Empty) →
      Nat → Nat
  | .active _, 0 => 0
  | .success p, 0 => if p.kind = color then 1 else 0
  | .failure _, 0 => 0
  | .active st, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        let child := coloredStep hn3 st e
        match child with
        | .active next => colorMass hn3 color (.active next) T
        | .success p => colorMass hn3 color (.success p) T
        | .failure f => nomatch f)).sum
  | .success p, T + 1 => n * colorMass hn3 color (.success p) T
  | .failure f, _ + 1 => nomatch f

/-- The three colors form an exact partition of scalar terminal mass. -/
theorem colorMass_partition
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n) :
    ∀ (x : PayloadNode (ActivePair hk ring) (TerminalPayload hk ring) Empty)
      (T : Nat),
      colorMass hn3 .rearAdvance x T + colorMass hn3 .frontAdvance x T +
          colorMass hn3 .contact x T =
        successMass (coloredStep hn3) x T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x with
      | active st => rfl
      | success p => cases h : p.kind <;> simp [colorMass, successMass, h]
      | failure f => exact f.elim
  | succ T ih =>
      cases x with
      | active st =>
          simp only [colorMass, successMass, PayloadFiniteStoppingTree.stepNode]
          rw [← ofFn_sum_add, ← ofFn_sum_add]
          apply ofFn_sum_eq
          intro e
          cases hchild : coloredStep hn3 st e with
          | active next => simpa [hchild] using ih (.active next)
          | success p => simpa [hchild] using ih (.success p)
          | failure f => exact f.elim
      | success p =>
          simp only [colorMass]
          rw [successMass_success]
          have h := ih (.success p)
          rw [successMass_success] at h
          calc
            n * colorMass hn3 .rearAdvance (.success p) T +
                  n * colorMass hn3 .frontAdvance (.success p) T +
                n * colorMass hn3 .contact (.success p) T =
                n * (colorMass hn3 .rearAdvance (.success p) T +
                  colorMass hn3 .frontAdvance (.success p) T +
                  colorMass hn3 .contact (.success p) T) := by
                    rw [Nat.mul_add, Nat.mul_add]
            _ = n * n ^ T := by rw [h]
            _ = n ^ (T + 1) := by rw [Nat.pow_succ]; ac_rfl
      | failure f => exact f.elim

/-- The colored tree retains the scalar half-mass bound at horizon `10*n`. -/
theorem colored_success_half_by_ten_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) :
    n ^ (10 * n) ≤
      2 * successMass (coloredStep hn3) (.active st) (10 * n) := by
  let cstep : ActivePair hk ring → Fin n →
      PayloadNode (ActivePair hk ring) (TerminalPayload hk ring) Empty :=
    coloredStep hn3
  let pstep : ActivePair hk ring → Fin n → StopNode (ActivePair hk ring) :=
    TwoEndpointServiceClock.step
  have herase : eraseStep cstep = pstep := by
    funext s e
    exact erase_coloredStep hn3 s e
  have hm := TwoEndpointServiceClock.success_half_by_ten_mul hn3 st
  change n ^ (10 * n) ≤ 2 * successMass cstep (.active st) (10 * n)
  rw [successMass_eq_successCount, herase]
  exact hm

/-- Rear advance, front advance, and contact exactly partition the terminal
half-mass guarantee. -/
theorem three_color_half_by_ten_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) :
    n ^ (10 * n) ≤ 2 *
      (colorMass hn3 .rearAdvance (.active st) (10 * n) +
        colorMass hn3 .frontAdvance (.active st) (10 * n) +
        colorMass hn3 .contact (.active st) (10 * n)) := by
  rw [colorMass_partition]
  exact colored_success_half_by_ten_mul hn3 st

#print axioms erase_coloredStep
#print axioms colorMass_partition
#print axioms three_color_half_by_ten_mul

end AAFJPK.TwoEndpointColoredClock
