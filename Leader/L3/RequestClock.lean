import Leader.L3.Headline.Digit
import Leader.L3.RequestCoefficient

/-!
Static request failure selector and complete quiet physical frame.

Do not import HeadlineAssembly or Headline via reverse dependencies.
The tap table is primitive at every width (`tapTablePrimitive`), so the rootless
exclusion covers all compiled widths.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-! ## B: all-width static RAW-or-TOP selector -/

/-- The fourth static relation is a complete bad TOP pair,
not a fourth RAW test. This selector covers every compiled t. -/
theorem requestRawOrTopFailure {n : Nat}
    (C : HeadlineConfiguration n) (hn : 5 ≤ n)
    (hl : ∀ i : Fin n, (C i).l = false) :
    (∃ s : Fin n, HeadlineRequest.RequestRawFailure C s) ∨
      (∃ s : Fin n, HeadlineDigit.BadCompletePair C s) := by
  obtain ⟨s, hs⟩ :=
    HeadlineRequest.rootlessFailedSiteSupported C hn hl
  rcases hs with hnonzero | hrec | hmarker | hincrement
  · exact Or.inl ⟨s, Or.inl hnonzero⟩
  · exact Or.inl ⟨s, Or.inr (Or.inl hrec)⟩
  · exact Or.inl ⟨s, Or.inr (Or.inr hmarker)⟩
  · exact Or.inr
      ⟨s, HeadlineDigit.badCompletePair_of_incrementFailure
        C s hincrement⟩

/-! ## A: the entire public quiet-step frame -/

/-- The old request and DCC event are checked at the actual
selected source and responder, never a frozen shadow edge. -/
private theorem requestClockAtSource {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e e =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).1 := by
  have h :
      (protocol (ceilLogTwo n)).step ring C e e =
        (transition (compileAdvice (ceilLogTwo n))
          (C e) (C (ring.rightNeighbor e))).1 := by
    simp [PopulationProtocol.step, protocol]
  exact h

private theorem requestClockAtTarget {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2 := by
  have hne : ring.rightNeighbor e ≠ e :=
    Ne.symm (ring_neighbor_distinct ring hn e)
  have h :
      (protocol (ceilLogTwo n)).step ring C e
          (ring.rightNeighbor e) =
        (transition (compileAdvice (ceilLogTwo n))
          (C e) (C (ring.rightNeighbor e))).2 := by
    simp [PopulationProtocol.step, protocol, hne]
  exact h

private theorem requestClockAway {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e i : Fin n)
    (he : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    headlinePhysicalNext ring C e i = C i := by
  have h : (protocol (ceilLogTwo n)).step ring C e i = C i := by
    simp [PopulationProtocol.step, he, hy]
  exact h

/-- The DCC demand checks all committed writes, not just the
SI u/beta fields: topReject, ddX and ddY are also urgent. -/
private theorem requestClockDccQuietTopDigit {c : Compiled}
    (x y : Agent c) (ev : CertEvent)
    (hq : (dccStep x y ev).request = false) :
    ev.topReject = false ∧
      ev.ddX = false ∧ ev.ddY = false := by
  have htop : ev.topReject = false := by
    cases hv : ev.topReject with
    | false => rfl
    | true =>
        have hh : (dccStep x y ev).request = true := by
          simp [dccStep, hv]
        rw [hq] at hh
        cases hh
  have hdx : ev.ddX = false := by
    cases hv : ev.ddX with
    | false => rfl
    | true =>
        have hh : (dccStep x y ev).request = true := by
          simp [dccStep, hv]
          split <;> rfl
        rw [hq] at hh
        cases hh
  have hdy : ev.ddY = false := by
    cases hv : ev.ddY with
    | false => rfl
    | true =>
        have hh : (dccStep x y ev).request = true := by
          simp [dccStep, hv]
          split <;> rfl
        rw [hq] at hh
        cases hh
  exact ⟨htop, hdx, hdy⟩

/-- Certificate dd events are exactly the final committed
digit changes, because Protocol.assemble retains TOP d fields. -/
private theorem requestClockPairDigitEvents
    (c : Compiled) (x y : Agent c) :
    (certificateStep c x y).2.2.ddX =
      ((transition c x y).1.d != x.d) ∧
    (certificateStep c x y).2.2.ddY =
      ((transition c x y).2.d != y.d) := by
  rcases HeadlineDigit.transitionCheckerFields c x y with
    ⟨_, _, _, _, _, _, hx, hy, _, _⟩
  constructor
  · rw [hx]
    rfl
  · rw [hy]
    rfl

private theorem requestClockFinBneQuiet {m : Nat}
    (a b : Fin m) (h : (a != b) = false) :
    a = b := by
  by_cases he : a = b
  · exact he
  · have hh : (a != b) = true := by simp [he]
    rw [hh] at h
    cases h

/-- Step A: if a leaderless, requestless OLD cut stays
requestless, every public u, beta, d coordinate is frozen.
Neither a RAW report nor a TOP report fired on that edge.
This concerns final committed d, not suppressed proposals. -/
theorem requestQuietPhysicalAll {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hafter : ∀ i : Fin n,
      (headlinePhysicalNext ring C e i).req = false) :
    (∀ i : Fin n,
      (headlinePhysicalNext ring C e i).u = (C i).u ∧
      (headlinePhysicalNext ring C e i).beta = (C i).beta ∧
      (headlinePhysicalNext ring C e i).d = (C i).d) ∧
    (FreshReference.rawResult ring C e).reject = false ∧
    (certificateStep (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e))).2.2.topReject = false := by
  have hold :=
    HeadlineRequest.requestQuietPhysical ring hn C e hl hr hafter
  have htarget := requestClockAtTarget ring hn C e
  have hnew :
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2.req = false :=
    (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.req)
      htarget).symm.trans
        (hafter (ring.rightNeighbor e))
  have hpair := HeadlineRequest.requestPairNoOldRequest
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hl e) (hl (ring.rightNeighbor e))
    (hr e) (hr (ring.rightNeighbor e))
  have hdemand :
      (dccStep (C e) (C (ring.rightNeighbor e))
        (certificateStep (compileAdvice (ceilLogTwo n))
          (C e) (C (ring.rightNeighbor e))).2.2).request =
          false := hpair.1.symm.trans hnew
  have hquiet := requestClockDccQuietTopDigit
    (C e) (C (ring.rightNeighbor e))
    (certificateStep (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e))).2.2 hdemand
  have hfields := requestClockPairDigitEvents
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
  have hdx :
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).1.d = (C e).d :=
    requestClockFinBneQuiet _ _
      (hfields.1.symm.trans hquiet.2.1)
  have hdy :
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2.d =
          (C (ring.rightNeighbor e)).d :=
    requestClockFinBneQuiet _ _
      (hfields.2.symm.trans hquiet.2.2)
  refine ⟨?_, hold.2, hquiet.1⟩
  intro i
  have hu := (hold.1 i).1
  have hb := (hold.1 i).2
  refine ⟨hu, hb, ?_⟩
  by_cases hs : i = e
  · subst i
    exact (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.d)
      (requestClockAtSource ring C e)).trans hdx
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      exact (congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.d)
        (requestClockAtTarget ring hn C e)).trans hdy
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.d)
        (requestClockAway ring C e i hs ht)

end L3

/-!
Arithmetic soundness of a fresh checker carry and
the OLD-input bridge interface.

Only completed proofs are declared. In particular,
the reverse half of the full list iff, and the strict terminal
ledger-to-owner report theorem, are not postulated here.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-! Plain digit-pair lists, independent of physical packet scratch. -/

/-- Ordinary low-first source integer carried by paired digits. -/
private def requestClockSourceList (c : Compiled) :
    List (Fin c.topA × Fin c.topA) → Nat
  | [] => 0
  | p :: ps => p.1.val + c.topA * requestClockSourceList c ps

/-- Ordinary low-first target integer carried by paired digits. -/
private def requestClockTargetList (c : Compiled) :
    List (Fin c.topA × Fin c.topA) → Nat
  | [] => 0
  | p :: ps => p.2.val + c.topA * requestClockTargetList c ps

/-- Actual checked carry recurrence, starting with an arbitrary
carry/error pair; a genuinely fresh run starts at (true,false). -/
private def requestClockCarryList (c : Compiled) :
    List (Fin c.topA × Fin c.topA) →
      Bool × Bool → Bool × Bool
  | [], state => state
  | p :: ps, state =>
      requestClockCarryList c ps
        (checkerCarryNext c state p.1 p.2)

/-- A zero error after one physical arithmetic update implies
zero incoming error and correct arithmetic for the low digit.
The carry-out is valued as either zero or one whole radix. -/
private theorem requestClockCarryDigitSound
    (c : Compiled) (old : Bool × Bool)
    (source target : Fin c.topA)
    (hzero : (checkerCarryNext c old source target).2 = false) :
    old.2 = false ∧
    target.val +
      (if (checkerCarryNext c old source target).1
        then c.topA else 0) =
      source.val + (if old.1 then 1 else 0) := by
  rcases old with ⟨carry, error⟩
  cases carry with
  | false =>
      cases error with
      | true =>
          simp [checkerCarryNext] at hzero
      | false =>
          have htarget : target.val = source.val := by
            by_cases he : target.val = source.val
            · exact he
            · have hf := hzero
              simp [checkerCarryNext,
                Nat.mod_eq_of_lt source.isLt, he] at hf
          constructor
          · rfl
          · simp [checkerCarryNext,
              Nat.mod_eq_of_lt source.isLt, htarget]
  | true =>
      cases error with
      | true =>
          simp [checkerCarryNext] at hzero
      | false =>
          by_cases htop : source.val + 1 = c.topA
          · have htarget : target.val = 0 := by
              by_cases he : target.val = 0
              · exact he
              · have hf := hzero
                simp [checkerCarryNext, htop, he] at hf
            have hcarry :
                (checkerCarryNext c (true, false)
                  source target).1 = true := by
              simp [checkerCarryNext, htop]
            constructor
            · rfl
            · rw [hcarry]
              simp only [if_pos]
              omega
          · have hbelow : source.val + 1 < c.topA := by
              have hs := source.isLt
              omega
            have htarget :
                target.val = source.val + 1 := by
              by_cases he : target.val = source.val + 1
              · exact he
              · have hf := hzero
                simp [checkerCarryNext, htop,
                  Nat.mod_eq_of_lt hbelow, he] at hf
            have hcarry :
                (checkerCarryNext c (true, false)
                  source target).1 = false := by
              simp [checkerCarryNext, htop]
            constructor
            · rfl
            · rw [hcarry]
              simp only [Bool.false_eq_true, ↓reduceIte]
              omega

/-- The sticky error cannot spontaneously clear while a list
of checked source/target digits is consumed. -/
private theorem requestClockCarryListSticky
    (c : Compiled) :
    ∀ (ps : List (Fin c.topA × Fin c.topA))
      (state : Bool × Bool),
      (requestClockCarryList c ps state).2 = false →
      state.2 = false := by
  intro ps
  induction ps with
  | nil =>
      intro state h
      exact h
  | cons p ps ih =>
      intro state h
      have hnext := ih
        (checkerCarryNext c state p.1 p.2) h
      rcases state with ⟨carry, error⟩
      cases error with
      | false => rfl
      | true =>
          have hbad :
              (checkerCarryNext c (carry, true)
                p.1 p.2).2 = true := by
            simp [checkerCarryNext]
          rw [hbad] at hnext
          cases hnext

/-- The arithmetic direction needed for A.3: zero sticky
error implies exact addition of incoming carry, including the
single outgoing carry above the final base-a digit.
This is a structural induction on a plain list, without
using any packet or scheduler theorem. -/
theorem requestClockCarryListSound (c : Compiled) :
    ∀ (ps : List (Fin c.topA × Fin c.topA))
      (state : Bool × Bool),
    (requestClockCarryList c ps state).2 = false →
      state.2 = false ∧
      requestClockTargetList c ps +
        (if (requestClockCarryList c ps state).1
          then c.topA ^ ps.length else 0) =
      requestClockSourceList c ps +
        (if state.1 then 1 else 0) := by
  intro ps
  induction ps with
  | nil =>
      intro state h
      constructor
      · exact h
      · cases hc : state.1 <;>
          simp [requestClockCarryList,
            requestClockSourceList, requestClockTargetList, hc]
  | cons p ps ih =>
      intro state h
      have ht := ih
        (checkerCarryNext c state p.1 p.2) h
      have hd := requestClockCarryDigitSound
        c state p.1 p.2 ht.1
      refine ⟨hd.1, ?_⟩
      change
        p.2.val + c.topA * requestClockTargetList c ps +
          (if (requestClockCarryList c ps
              (checkerCarryNext c state p.1 p.2)).1
            then c.topA ^ (ps.length + 1) else 0) =
        p.1.val + c.topA * requestClockSourceList c ps +
          (if state.1 then 1 else 0)
      calc
        _ = p.2.val + c.topA *
              (requestClockTargetList c ps +
                (if (requestClockCarryList c ps
                    (checkerCarryNext c state p.1 p.2)).1
                  then c.topA ^ ps.length else 0)) := by
            cases hcarry :
                (requestClockCarryList c ps
                  (checkerCarryNext c state p.1 p.2)).1 <;>
              simp [hcarry, Nat.pow_succ,
                Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] <;>
              exact Nat.mul_comm _ _
        _ = p.2.val + c.topA *
              (requestClockSourceList c ps +
                (if (checkerCarryNext c state p.1 p.2).1
                  then 1 else 0)) := by
            rw [ht.2]
        _ = (p.2.val +
              (if (checkerCarryNext c state p.1 p.2).1
                then c.topA else 0)) +
              c.topA * requestClockSourceList c ps := by
            cases hcarry :
                (checkerCarryNext c state p.1 p.2).1 <;>
              simp [hcarry, Nat.mul_add, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]
        _ = (p.1.val + (if state.1 then 1 else 0)) +
              c.topA * requestClockSourceList c ps := by
            rw [hd.2]
        _ = p.1.val + c.topA * requestClockSourceList c ps +
              (if state.1 then 1 else 0) := by omega

/-! Indexed specializations of the same carry invariant.
They are used solely to connect the arithmetic to the
existing certBlockValue / checkerTruePartial definitions. -/

/-- A low-first base-a value of the first k digits in an
unrestricted (possibly cyclic) index stream. -/
private def requestClockDigitPrefix (a : Nat)
    (f : Nat → Fin a) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      requestClockDigitPrefix a f k + (f k).val * a ^ k

private theorem requestClockDigitPrefixBound
    (a : Nat) (ha : 0 < a)
    (f : Nat → Fin a) :
    ∀ k : Nat,
      requestClockDigitPrefix a f k < a ^ k := by
  intro k
  induction k with
  | zero =>
      simp [requestClockDigitPrefix]
  | succ k ih =>
      change
        requestClockDigitPrefix a f k +
          (f k).val * a ^ k < a ^ (k + 1)
      have hdigit : (f k).val + 1 ≤ a := by
        have hh := (f k).isLt
        omega
      have hm := Nat.mul_le_mul_right (a ^ k) hdigit
      have hadd :
          a ^ k + (f k).val * a ^ k =
            ((f k).val + 1) * a ^ k := by
        rw [Nat.add_mul]
        simp only [Nat.one_mul]
        omega
      have hp : a ^ (k + 1) = a * a ^ k := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hp]
      omega

/-- Fin.foldl uses exactly the low-first positional value.
The last-coordinate recursion is a core Fin lemma. -/
private theorem requestClockDigitPrefixFold
    (a : Nat) (f : Nat → Fin a) (k : Nat) :
    requestClockDigitPrefix a f k =
      Fin.foldl k
        (fun z j => z + (f j.val).val * a ^ j.val) 0 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [Fin.foldl_succ_last]
      change
        requestClockDigitPrefix a f k + (f k).val * a ^ k =
          Fin.foldl k
            (fun z j => z + (f j.val).val * a ^ j.val) 0 +
            (f k).val * a ^ k
      rw [ih]

/-- The checker recurrence on the actual cyclic public digit
streams has the same conservation law as plain paired lists. -/
private theorem requestClockCheckerPartialSound
    {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) :
    ∀ k : Nat,
      (checkerTruePartial W s k).2 = false →
      requestClockDigitPrefix c.topA
          (fun j => certDigit W
            (certSite s (c.rho + j))) k +
        (if (checkerTruePartial W s k).1
          then c.topA ^ k else 0) =
      requestClockDigitPrefix c.topA
          (fun j => certDigit W (certSite s j)) k + 1 := by
  intro k
  induction k with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro hzero
      have hstep :
          (checkerCarryNext c
            (checkerTruePartial W s k)
            (certDigit W (certSite s k))
            (certDigit W (certSite s (c.rho + k)))).2 =
              false := by
        rw [← checkerTruePartial_succ W s k]
        exact hzero
      have hd := requestClockCarryDigitSound c
        (checkerTruePartial W s k)
        (certDigit W (certSite s k))
        (certDigit W (certSite s (c.rho + k)))
        hstep
      have hp := ih hd.1
      change
        (requestClockDigitPrefix c.topA
          (fun j => certDigit W
            (certSite s (c.rho + j))) k +
          (certDigit W (certSite s (c.rho + k))).val *
            c.topA ^ k) +
          (if (checkerCarryNext c
              (checkerTruePartial W s k)
              (certDigit W (certSite s k))
              (certDigit W (certSite s (c.rho + k)))).1
            then c.topA ^ (k + 1) else 0) =
        (requestClockDigitPrefix c.topA
          (fun j => certDigit W (certSite s j)) k +
          (certDigit W (certSite s k)).val * c.topA ^ k) + 1
      calc
        _ =
          requestClockDigitPrefix c.topA
            (fun j => certDigit W
              (certSite s (c.rho + j))) k +
          ((certDigit W
              (certSite s (c.rho + k))).val +
            (if (checkerCarryNext c
                (checkerTruePartial W s k)
                (certDigit W (certSite s k))
                (certDigit W
                  (certSite s (c.rho + k)))).1
              then c.topA else 0)) * c.topA ^ k := by
          cases hc :
              (checkerCarryNext c
                (checkerTruePartial W s k)
                (certDigit W (certSite s k))
                (certDigit W (certSite s (c.rho + k)))).1 <;>
            simp [hc, Nat.pow_succ, Nat.add_mul,
              Nat.mul_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] <;>
            exact Nat.mul_comm _ _
        _ =
          requestClockDigitPrefix c.topA
            (fun j => certDigit W
              (certSite s (c.rho + j))) k +
          ((certDigit W (certSite s k)).val +
            (if (checkerTruePartial W s k).1
              then 1 else 0)) * c.topA ^ k := by
          rw [hd.2]
        _ =
          (requestClockDigitPrefix c.topA
            (fun j => certDigit W
              (certSite s (c.rho + j))) k +
            (if (checkerTruePartial W s k).1
              then c.topA ^ k else 0)) +
          (certDigit W (certSite s k)).val * c.topA ^ k := by
          cases hc : (checkerTruePartial W s k).1 <;>
            simp [hc, Nat.add_mul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
        _ =
          (requestClockDigitPrefix c.topA
            (fun j => certDigit W (certSite s j)) k + 1) +
          (certDigit W (certSite s k)).val * c.topA ^ k := by
          rw [hp]
        _ =
          (requestClockDigitPrefix c.topA
            (fun j => certDigit W (certSite s j)) k +
            (certDigit W (certSite s k)).val * c.topA ^ k) + 1 := by
          omega

/-- A false complete increment forces the genuine *fresh*
comparison arithmetic to set its sticky error. This theorem
does not assert that an inherited physical QCarry is fresh. -/
theorem checkerTruePartialBad {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : BadCompletePair C s) :
    (checkerTruePartial (publicWord C) s
      (compileAdvice (ceilLogTwo n)).rho).2 = true := by
  cases hzero :
      (checkerTruePartial (publicWord C) s
        (compileAdvice (ceilLogTwo n)).rho).2 with
  | true =>
      rfl
  | false =>
      have hs := requestClockCheckerPartialSound
        (publicWord C) s
        (compileAdvice (ceilLogTwo n)).rho hzero
      have hsource :
          requestClockDigitPrefix
            (compileAdvice (ceilLogTwo n)).topA
            (fun j => certDigit (publicWord C)
              (certSite s j))
            (compileAdvice (ceilLogTwo n)).rho =
          certBlockValue (publicWord C) s := by
        rw [requestClockDigitPrefixFold]
        rfl
      have htarget :
          requestClockDigitPrefix
            (compileAdvice (ceilLogTwo n)).topA
            (fun j => certDigit (publicWord C)
              (certSite s
                ((compileAdvice (ceilLogTwo n)).rho + j)))
            (compileAdvice (ceilLogTwo n)).rho =
          certBlockValue (publicWord C)
            (certSite s (compileAdvice (ceilLogTwo n)).rho) := by
        rw [requestClockDigitPrefixFold]
        unfold certBlockValue
        congr 1
        funext z j
        rw [certSite_add]
      have hboundSource :=
        requestClockDigitPrefixBound
          (compileAdvice (ceilLogTwo n)).topA
          (compileAdvice (ceilLogTwo n)).topA_pos
          (fun j => certDigit (publicWord C)
            (certSite s j))
          (compileAdvice (ceilLogTwo n)).rho
      have hboundTarget :=
        requestClockDigitPrefixBound
          (compileAdvice (ceilLogTwo n)).topA
          (compileAdvice (ceilLogTwo n)).topA_pos
          (fun j => certDigit (publicWord C)
            (certSite s
              ((compileAdvice (ceilLogTwo n)).rho + j)))
          (compileAdvice (ceilLogTwo n)).rho
      rw [hsource] at hboundSource
      rw [htarget] at hboundTarget
      rw [hsource, htarget] at hs
      have hcorrect :
          certBlockId (publicWord C)
            (certSite s (compileAdvice (ceilLogTwo n)).rho) =
          (certBlockId (publicWord C) s + 1) %
            ((compileAdvice (ceilLogTwo n)).topA ^
              (compileAdvice (ceilLogTwo n)).rho) := by
        unfold certBlockId
        rw [Nat.mod_eq_of_lt hboundTarget,
          Nat.mod_eq_of_lt hboundSource]
        cases hcarry :
            (checkerTruePartial (publicWord C) s
              (compileAdvice (ceilLogTwo n)).rho).1 with
        | false =>
            have heq :
                certBlockValue (publicWord C)
                    (certSite s (compileAdvice (ceilLogTwo n)).rho) =
                  certBlockValue (publicWord C) s + 1 := by
              simpa only [hcarry, Bool.false_eq_true, ↓reduceIte,
                Nat.add_zero] using hs
            rw [← heq, Nat.mod_eq_of_lt hboundTarget]
        | true =>
            have heq :
                certBlockValue (publicWord C)
                    (certSite s (compileAdvice (ceilLogTwo n)).rho) +
                  (compileAdvice (ceilLogTwo n)).topA ^
                    (compileAdvice (ceilLogTwo n)).rho =
                certBlockValue (publicWord C) s + 1 := by
              simpa only [hcarry, if_true] using hs
            rw [← heq, Nat.add_mod_right,
              Nat.mod_eq_of_lt hboundTarget]
      exact False.elim (hbad.2 hcorrect)

/-! The correctly stopped OLD-terminal interface. -/

/-- Unlike StrictReportBridge, this freezes only the OLD prefix.
The terminal service may itself change visible public fields. -/
def StrictReportBridgeOld {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n) (s : Fin n)
      (pfx : List (Fin n)) (e : Fin n),
    BadCompletePair C s →
    FrozenOnWord ring C pfx →
    StrictCompletesAt ring C s pfx e →
    TopRejectAt ring
      (HeadlineRequest.realRequestRun ring C pfx) e

/-- A verified OLD-input bridge, if established, directly
discharges the existing stronger-final-freeze interface. -/
theorem requestClockOldBridgeImpliesStrict {n : Nat}
    (ring : DirectedRing n)
    (hbridge : StrictReportBridgeOld ring) :
    StrictReportBridge ring := by
  intro C s pfx e hbad hfrozen hstrict
  have hprefix : FrozenOnWord ring C pfx := by
    intro before after heq
    apply hfrozen before (after ++ [e])
    rw [heq, List.append_assoc]
  exact hbridge C s pfx e hbad hprefix hstrict

/-- The OLD-input report, once proved, is a physical responder
request at the same terminal edge. Grant transport and separate
first-hit accounting remain independent. -/
theorem requestClockStrictOldBridgeRequests {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (pfx : List (Fin n)) (e : Fin n)
    (hbridge : StrictReportBridgeOld ring)
    (hbad : BadCompletePair C s)
    (hfrozen : FrozenOnWord ring C pfx)
    (hstrict : StrictCompletesAt ring C s pfx e)
    (hl : ∀ i : Fin n,
      ((HeadlineRequest.realRequestRun ring C pfx) i).l = false)
    (hr : ∀ i : Fin n,
      ((HeadlineRequest.realRequestRun ring C pfx) i).req = false) :
    ((headlinePhysicalNext ring
      (HeadlineRequest.realRequestRun ring C pfx) e)
      (ring.rightNeighbor e)).req = true := by
  exact topRejectMakesPhysicalRequest ring hn
    (HeadlineRequest.realRequestRun ring C pfx)
    e hl hr (hbridge C s pfx e hbad hfrozen hstrict)

end HeadlineDigit
end L3

/-!
Strict-terminal OLD snapshot.

It proves the
final receipt-to-OLD-carry identity; the independent carry-use
arithmetic invariant is not asserted.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-- A live carry at the inherited cut has an inherited
ghost origin, whatever its physical carry and error bits. -/
theorem requestClockInitialCarryInherited
    {c : Compiled} {n : Nat}
    (lane : DigitLane) (site : Fin n)
    (view : DigitLaneView c)
    (ledger : DigitCarryGhost c n)
    (hcarry :
      (DigitLaneGhost.initial lane site view).carry =
        some ledger) :
    ledger.inherited =
      some (.inherited lane site .carry) := by
  change
    (if view.carryLive then
      some
        ({ inherited := some (.inherited lane site .carry)
           uses := [] } : DigitCarryGhost c n)
     else none) = some ledger at hcarry
  split at hcarry
  · cases hcarry
    rfl
  · cases hcarry

/-- Actual replay terminal metadata is copied from the OLD
source carry and ghost ledger. -/
theorem requestClockReplayTerminalOldFields
    {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (terminal : DigitTerminal c n)
    (hterminal :
      (digitLaneReplay lane time source destination
        x y gx gy).terminal = some terminal) :
    terminal.time = time ∧
    terminal.lane = lane ∧
    terminal.source = source ∧
    terminal.destination = destination ∧
    terminal.ledger = gx.carry ∧
    terminal.errorBit = x.carryError := by
  change
    (if !(x.leader || y.leader) && x.carryLive &&
        (y.leader || y.marker) then
      some
        ({ time := time
           lane := lane
           source := source
           destination := destination
           ledger := gx.carry
           carryBit := x.carryBit
           errorBit := x.carryError } : DigitTerminal c n)
     else none) = some terminal at hterminal
  split at hterminal
  · cases hterminal
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases hterminal

/-- No historical frame has a timestamp beyond the current
audit clock. -/
def RequestClockAuditFrameBound {n : Nat}
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ f : DigitFrame (compileAdvice (ceilLogTwo n)) n,
    f ∈ A.frames → f.time ≤ A.clock

private theorem requestClockAuditFrameBoundInitial {n : Nat}
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n))) :
    RequestClockAuditFrameBound (digitAuditInitial S) := by
  intro f hf
  change f ∈ ([] : List
    (DigitFrame (compileAdvice (ceilLogTwo n)) n)) at hf
  cases hf

private theorem requestClockAuditFrameBoundStep {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hbound : RequestClockAuditFrameBound A) :
    RequestClockAuditFrameBound (digitAuditStep ring S A e) := by
  intro f hf
  rw [checkerAuditFramesAfter ring S A e] at hf
  rcases List.mem_cons.mp hf with hhead | hold
  · rw [hhead]
    change A.clock + 1 ≤ A.clock + 1
    exact Nat.le_refl _
  · have hh := hbound f hold
    change f.time ≤ A.clock + 1
    omega

/-- The audit clock counts real physical scheduler letters. -/
theorem requestClockAuditClockOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    (auditedRealRun ring C word).2.clock = word.length := by
  have key : ∀ rev : List (Fin n),
      (auditedRealRun ring C rev.reverse).2.clock =
        rev.reverse.length := by
    intro rev
    induction rev with
    | nil =>
        rfl
    | cons e rev ih =>
        rw [List.reverse_cons]
        rw [checkerAuditedRunAppendOne ring C rev.reverse e]
        change
          (auditedRealRun ring C rev.reverse).2.clock + 1 =
            (rev.reverse ++ [e]).length
        rw [ih, List.length_append, List.length_singleton]
  have hh := key word.reverse
  simpa only [List.reverse_reverse] using hh

/-- Every chronological real word preserves the frame bound,
including arbitrary inherited private scratch. -/
theorem requestClockAuditFrameBoundOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    RequestClockAuditFrameBound
      (auditedRealRun ring C word).2 := by
  have key : ∀ rev : List (Fin n),
      RequestClockAuditFrameBound
        (auditedRealRun ring C rev.reverse).2 := by
    intro rev
    induction rev with
    | nil =>
        exact requestClockAuditFrameBoundInitial (piD C)
    | cons e rev ih =>
        rw [List.reverse_cons]
        rw [checkerAuditedRunAppendOne ring C rev.reverse e]
        exact requestClockAuditFrameBoundStep ring
          (piD (auditedRealRun ring C rev.reverse).1)
          (auditedRealRun ring C rev.reverse).2 e ih
  have hh := key word.reverse
  simpa only [List.reverse_reverse] using hh

/-- A recorded terminal stamped at the new time must belong
to the final newly inserted frame, not an earlier frame. -/
private theorem requestClockLatestTerminalReceipt {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (terminal : DigitTerminal
      (compileAdvice (ceilLogTwo n)) n)
    (hbound : RequestClockAuditFrameBound A)
    (hrecord :
      DigitRecordedTerminal (digitAuditStep ring S A e) terminal)
    (htime : terminal.time = A.clock + 1)
    (hlane : terminal.lane = .comparison) :
    (digitService (A.clock + 1) e (ring.rightNeighbor e)
      (S e) (S (ring.rightNeighbor e))
      (A.current e) (A.current (ring.rightNeighbor e))).comparison.terminal = some terminal := by
  obtain ⟨f, hmember, hfTime, hfEdge, hfReceipt⟩ := hrecord
  rw [checkerAuditFramesAfter ring S A e] at hmember
  rcases List.mem_cons.mp hmember with hnew | hold
  · rw [hnew] at hfReceipt
    rw [hlane] at hfReceipt
    change
      (digitService (A.clock + 1) e (ring.rightNeighbor e)
        (S e) (S (ring.rightNeighbor e))
        (A.current e) (A.current (ring.rightNeighbor e))).comparison.terminal = some terminal at hfReceipt
    exact hfReceipt
  · have hh := hbound f hold
    omega

/-- A strictly authenticated terminal refers to the actual
OLD qCarry error and to a live ghost ledger whose inherited
origin is NONE and whose complete use count is rho.
No arithmetic fold of those uses is assumed here. -/
theorem requestClockStrictTerminalOldSnapshot {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (s : Fin n)
    (pfx : List (Fin n)) (e : Fin n)
    (hstrict : StrictCompletesAt ring C s pfx e) :
    ∃ (terminal : DigitTerminal
        (compileAdvice (ceilLogTwo n)) n)
      (ledger : DigitCarryGhost
        (compileAdvice (ceilLogTwo n)) n),
      terminal.ledger = some ledger ∧
      ledger.inherited = none ∧
      ledger.uses.length = (compileAdvice (ceilLogTwo n)).rho ∧
      ((auditedRealRun ring C pfx).2.current e).comparison.carry =
        some ledger ∧
      terminal.errorBit =
        qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry := by
  obtain ⟨terminal, hfirst, htime, hsource, hdestination⟩ := hstrict
  have hrecord :
      DigitRecordedTerminal
        (auditedRealRun ring C (pfx ++ [e])).2 terminal :=
    hfirst.1.2.2.1
  have hlane : terminal.lane = .comparison :=
    hfirst.1.2.2.2.1
  obtain ⟨positive, ledger, samples, exports, uses,
      hledger, hinherited, hsize, hremaining⟩ :=
    hfirst.1.2.2.2.2.2.2
  have hrecordNext :
      DigitRecordedTerminal
        (digitAuditStep ring
          (piD (auditedRealRun ring C pfx).1)
          (auditedRealRun ring C pfx).2 e) terminal := by
    rw [checkerAuditedRunAppendOne ring C pfx e] at hrecord
    exact hrecord
  have hclock := requestClockAuditClockOnWord ring C pfx
  have htimeNew :
      terminal.time = (auditedRealRun ring C pfx).2.clock + 1 := by
    rw [hclock]
    exact htime
  have hlast := requestClockLatestTerminalReceipt
    ring (piD (auditedRealRun ring C pfx).1)
    (auditedRealRun ring C pfx).2 e terminal
    (requestClockAuditFrameBoundOnWord ring C pfx)
    hrecordNext htimeNew hlane
  have hfields := requestClockReplayTerminalOldFields
    .comparison
    ((auditedRealRun ring C pfx).2.clock + 1)
    e (ring.rightNeighbor e)
    (digitLaneView .comparison
      ((piD (auditedRealRun ring C pfx).1) e)
      ((piD (auditedRealRun ring C pfx).1) e).word.beta)
    (digitLaneView .comparison
      ((piD (auditedRealRun ring C pfx).1)
        (ring.rightNeighbor e))
      ((piD (auditedRealRun ring C pfx).1)
        (ring.rightNeighbor e)).word.beta)
    ((auditedRealRun ring C pfx).2.current e).comparison
    ((auditedRealRun ring C pfx).2.current
      (ring.rightNeighbor e)).comparison
    terminal hlast
  obtain ⟨_, _, _, _, hcurrent, herror⟩ := hfields
  have hfresh :
      ((auditedRealRun ring C pfx).2.current e).comparison.carry =
        some ledger := by
    rw [← hcurrent]
    exact hledger
  have hphysical :
      terminal.errorBit =
        qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry := by
    change terminal.errorBit =
      qcE ((auditedRealRun ring C pfx).1 e).qCarry at herror
    rw [checkerAuditedRunPhysical ring C pfx] at herror
    exact herror
  exact ⟨terminal, ledger, hledger, hinherited,
    hsize, hfresh, hphysical⟩

end HeadlineDigit
end L3

/-!
QC3/old-physical-carry audit.

The requested unqualified
carryIn = OLD qcC invariant is false on a genuinely new QC3 ledger:
the launch uses the virtual increment seed true, while OLD QCarry
is OFF and its qcC is false. The lemmas below isolate the exact
birth/advance split and a legal Cartesian real-run witness.
No strictly authenticated terminal implication is asserted.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-- The literal first DigitUse of a newly launched QC3 carry.
The incoming carry is the *virtual arithmetic seed*, not the
physical OLD source carry, which must be OFF at QC3. -/
def requestClockQC3FirstUse {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (v : DigitLaneView c) (g : DigitLaneGhost c n) :
    DigitUse c n :=
  { time := time
    target := site
    operand := g.input
    value := inV c v.input
    tail := inT v.input
    targetDigit := v.digit
    carryIn := true
    errorIn := false }

/-- An ordinary QC2 service consumes the OLD physical live
carry/error bits at its source. -/
def requestClockQC2NextUse {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (v : DigitLaneView c) (g : DigitLaneGhost c n)
    (carry error : Bool) : DigitUse c n :=
  { time := time
    target := site
    operand := g.input
    value := inV c v.input
    tail := inT v.input
    targetDigit := v.digit
    carryIn := carry
    errorIn := error }

/-- The real receipt constructor's QC3 case starts a ledger with
no inherited carry and exactly the seed use (true,false).
Nothing is asserted about an independent/fabricated scheduler. -/
theorem requestClockQC3ReplayBirth {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false)
    (hyl : y.leader = false)
    (hmarker : x.marker = true)
    (hfree : x.carryLive = false)
    (hsettled : x.input.isS = true) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.carry =
      some
        ({ inherited := none
           uses := [requestClockQC3FirstUse time source x gx] } :
          DigitCarryGhost c n) := by
  simp [digitLaneReplay, requestClockQC3FirstUse,
    hxl, hyl, hmarker, hfree, hsettled]

/-- The corresponding QC2 replay adds one use whose incoming bits
are exactly the OLD comparison view at the selected source.
The inherited-or-fresh status of the old ledger is irrelevant. -/
theorem requestClockQC2ReplayAppend {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (ledger : DigitCarryGhost c n)
    (hxl : x.leader = false)
    (hyl : y.leader = false)
    (hlive : x.carryLive = true)
    (hmarker : y.marker = false)
    (hfree : y.carryLive = false)
    (hsettled : y.input.isS = true)
    (hledger : gx.carry = some ledger) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).y.carry =
      some
        { ledger with
          uses := ledger.uses ++
            [requestClockQC2NextUse time destination y gy
              x.carryBit x.carryError] } := by
  simp [digitLaneReplay, requestClockQC2NextUse,
    hxl, hyl, hlive, hmarker, hfree, hsettled, hledger]

/-- The comparison lane's view of an OLD physical state is exactly
qcC/qcE, independently of writer-lane resolved beta. -/
theorem requestClockQC2OldViewBits {c : Compiled}
    (x : ProjD c) :
    (digitLaneView .comparison x x.word.beta).carryBit =
        qcC x.top.qCarry ∧
      (digitLaneView .comparison x x.word.beta).carryError =
        qcE x.top.qCarry := by
  exact ⟨rfl, rfl⟩

/-- The first QC3 use cannot have carryIn equal to the OLD
physical QC carry: an OFF record has qcC=false, whereas the
new carry has virtual input true. -/
theorem requestClockQC3OldOffMismatch {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (x : ProjD c) (gx : DigitLaneGhost c n)
    (hoff : x.top.qCarry = .OFF) :
    (requestClockQC3FirstUse time site
      (digitLaneView .comparison x x.word.beta) gx).carryIn ≠
      qcC x.top.qCarry := by
  rw [hoff]
  change true ≠ false
  intro h
  cases h

end HeadlineDigit
end L3

/-!
Corrected QC3-seed / QC2-OLD carry accounting.

The invariant is a PROOF-SIDE property of the actual audit and
actual physical configuration. Its seed-and-frame fragments and
the pure A.3 fold are proved below. An unconditional two-endpoint
physical/ghost preservation theorem is not silently postulated.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-- Fold recorded LOW-FIRST checker uses. Unlike the first QC3
DigitUse's carryIn, the fold's initial true is not read from
the OLD physical qCarry, which is OFF at launch. -/
private def requestClockFoldDigitUses {c : Compiled} {n : Nat} :
    List (DigitUse c n) → Bool × Bool → Bool × Bool
  | [], state => state
  | use :: rest, state =>
      requestClockFoldDigitUses rest
        (checkerCarryNext c state use.value use.targetDigit)

/-- Each appended use must consume precisely the result of all
preceding uses. For the first use this result is (true,false);
later uses have the old physical carry pair at QC2. -/
inductive RequestClockFreshUseChain
    (c : Compiled) (n : Nat) :
    List (DigitUse c n) → Prop where
  | empty : RequestClockFreshUseChain c n []
  | snoc
      (uses : List (DigitUse c n)) (use : DigitUse c n)
      (hchain : RequestClockFreshUseChain c n uses)
      (hinput :
        (use.carryIn, use.errorIn) =
          requestClockFoldDigitUses uses (true, false)) :
      RequestClockFreshUseChain c n (uses ++ [use])

/-- The required QC3 seed is exactly the empty-chain extension. -/
theorem requestClockQC3FreshUseChain {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (view : DigitLaneView c) (ghost : DigitLaneGhost c n) :
    RequestClockFreshUseChain c n
      [requestClockQC3FirstUse time site view ghost] := by
  change RequestClockFreshUseChain c n
    ([] ++ [requestClockQC3FirstUse time site view ghost])
  exact RequestClockFreshUseChain.snoc []
    (requestClockQC3FirstUse time site view ghost)
    RequestClockFreshUseChain.empty rfl

/-- The new QC2 use's incoming pair is its explicitly supplied
OLD live-carry bits, not the successor's bits. -/
theorem requestClockQC2NextUseBits {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (view : DigitLaneView c) (ghost : DigitLaneGhost c n)
    (carry error : Bool) :
    ((requestClockQC2NextUse time site view ghost carry error).carryIn,
     (requestClockQC2NextUse time site view ghost carry error).errorIn) =
      (carry, error) := by
  rfl

/-- The QC3 first use has the virtual seed, irrespective of any
inherited OLD physical carry field. -/
theorem requestClockQC3FirstUseBits {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (view : DigitLaneView c) (ghost : DigitLaneGhost c n) :
    ((requestClockQC3FirstUse time site view ghost).carryIn,
     (requestClockQC3FirstUse time site view ghost).errorIn) =
      (true, false) := by
  rfl

/-- A single fresh QC3 use evaluates to the same arithmetic
checkerCarryNext that the physical launch row computes. -/
theorem requestClockQC3FirstUseFold {c : Compiled} {n : Nat}
    (time : Nat) (site : Fin n)
    (view : DigitLaneView c) (ghost : DigitLaneGhost c n) :
    requestClockFoldDigitUses
      [requestClockQC3FirstUse time site view ghost] (true, false) =
    checkerCarryNext c (true, false)
      (inV c view.input) view.digit := by
  rfl

/-- The list fold commutes with adding the next recorded use.
The checker only reads use.value and use.targetDigit. -/
private theorem requestClockFoldDigitUsesSnoc {c : Compiled} {n : Nat} :
    ∀ (uses : List (DigitUse c n)) (state : Bool × Bool)
      (use : DigitUse c n),
      requestClockFoldDigitUses (uses ++ [use]) state =
        checkerCarryNext c (requestClockFoldDigitUses uses state)
          use.value use.targetDigit := by
  intro uses
  induction uses with
  | nil =>
      intro state use
      rfl
  | cons hd rest ih =>
      intro state use
      change
        requestClockFoldDigitUses (rest ++ [use])
          (checkerCarryNext c state hd.value hd.targetDigit) =
        checkerCarryNext c
          (requestClockFoldDigitUses rest
            (checkerCarryNext c state hd.value hd.targetDigit))
          use.value use.targetDigit
      exact ih _ _

/-- A QC2 append extends a valid chain if its OLD physical
input pair was the previously folded live-carry pair. -/
theorem requestClockQC2FreshUseChainAppend {c : Compiled} {n : Nat}
    (uses : List (DigitUse c n))
    (time : Nat) (site : Fin n)
    (view : DigitLaneView c) (ghost : DigitLaneGhost c n)
    (carry error : Bool)
    (hchain : RequestClockFreshUseChain c n uses)
    (hbits :
      requestClockFoldDigitUses uses (true, false) = (carry, error)) :
    RequestClockFreshUseChain c n
      (uses ++ [requestClockQC2NextUse time site view ghost carry error]) := by
  apply RequestClockFreshUseChain.snoc uses
    (requestClockQC2NextUse time site view ghost carry error)
    hchain
  rw [requestClockQC2NextUseBits, hbits]

/-- The append arithmetic is the actual checkerCarryNext
of the OLD pair, not a second synthetic virtual seed. -/
theorem requestClockQC2FreshUseFoldAppend {c : Compiled} {n : Nat}
    (uses : List (DigitUse c n))
    (time : Nat) (site : Fin n)
    (view : DigitLaneView c) (ghost : DigitLaneGhost c n)
    (carry error : Bool)
    (hbits :
      requestClockFoldDigitUses uses (true, false) = (carry, error)) :
    requestClockFoldDigitUses
      (uses ++ [requestClockQC2NextUse time site view ghost carry error])
      (true, false) =
    checkerCarryNext c (carry, error)
      (inV c view.input) view.digit := by
  rw [requestClockFoldDigitUsesSnoc, hbits]
  rfl

/-- An individual use has a real OLD audit frame:
at QC3 birth the source's physical carry was OFF and the
recorded input is virtual; at QC2 the OLD source was live
with the recorded incoming carry/error. -/
def RequestClockOldUseFrame {n : Nat}
    (ring : DirectedRing n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (use : DigitUse (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ frame : DigitFrame (compileAdvice (ceilLogTwo n)) n,
    frame ∈ A.frames ∧ frame.time = use.time ∧
    ((frame.edge = use.target ∧
        (frame.old frame.edge).top.qCarry = .OFF ∧
        use.carryIn = true ∧ use.errorIn = false ∧
        use.value = inV (compileAdvice (ceilLogTwo n))
          (frame.old frame.edge).top.qIn ∧
        use.targetDigit = (frame.old frame.edge).top.d) ∨
     (ring.rightNeighbor frame.edge = use.target ∧
        (frame.old frame.edge).top.qCarry =
          .L use.carryIn use.errorIn ∧
        use.value = inV (compileAdvice (ceilLogTwo n))
          (frame.old (ring.rightNeighbor frame.edge)).top.qIn ∧
        use.targetDigit =
          (frame.old (ring.rightNeighbor frame.edge)).top.d))

/-- Already recorded OLD-frame witnesses remain available after
every selected edge, including irrelevant edges and terminal. -/
theorem requestClockOldUseFrameStep {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (use : DigitUse (compileAdvice (ceilLogTwo n)) n)
    (h : RequestClockOldUseFrame ring A use) :
    RequestClockOldUseFrame ring (digitAuditStep ring S A e) use := by
  obtain ⟨frame, hm, ht, hrow⟩ := h
  refine ⟨frame, ?_, ht, hrow⟩
  rw [checkerAuditFramesAfter ring S A e]
  exact List.mem_cons.mpr (Or.inr hm)

/-- Each fresh QC3 birth use is certified by the exact NEW
frame with the OLD source qCarry OFF. -/
theorem requestClockOldUseFrameBirth {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hoff : (S e).top.qCarry = .OFF) :
    RequestClockOldUseFrame ring (digitAuditStep ring S A e)
      (requestClockQC3FirstUse (A.clock + 1) e
        (digitLaneView .comparison (S e) (S e).word.beta)
        (A.current e).comparison) := by
  refine ⟨checkerNewAuditFrame ring S A e, ?_, rfl, ?_⟩
  · rw [checkerAuditFramesAfter ring S A e]
    exact List.mem_cons.mpr (Or.inl rfl)
  · exact Or.inl ⟨rfl, hoff, rfl, rfl, rfl, rfl⟩

/-- Each QC2 use records the OLD actual source carry from its
own NEW frame, before the physical move and ledger append. -/
theorem requestClockOldUseFrameAdvance {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (carry error : Bool)
    (hold : (S e).top.qCarry = .L carry error) :
    RequestClockOldUseFrame ring (digitAuditStep ring S A e)
      (requestClockQC2NextUse (A.clock + 1)
        (ring.rightNeighbor e)
        (digitLaneView .comparison
          (S (ring.rightNeighbor e))
          (S (ring.rightNeighbor e)).word.beta)
        (A.current (ring.rightNeighbor e)).comparison
        carry error) := by
  refine ⟨checkerNewAuditFrame ring S A e, ?_, rfl, ?_⟩
  · rw [checkerAuditFramesAfter ring S A e]
    exact List.mem_cons.mpr (Or.inl rfl)
  · exact Or.inr ⟨rfl, hold, rfl, rfl⟩

/-- The corrected global invariant at one REAL current cut:
for every live ghost carry born here (inherited = none),
every use is a correctly linked arithmetic use and has a real
OLD frame; the current physical QCarry is the resulting fold.
Inherited arbitrary scratch is intentionally not certified. -/
def RequestClockFreshCarryInvariant {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ i : Fin n,
    ∀ ledger : DigitCarryGhost
      (compileAdvice (ceilLogTwo n)) n,
    ((A.current i).comparison.carry = some ledger) →
    ledger.inherited = none →
    RequestClockFreshUseChain
      (compileAdvice (ceilLogTwo n)) n ledger.uses ∧
    (∀ use : DigitUse (compileAdvice (ceilLogTwo n)) n,
      use ∈ ledger.uses → RequestClockOldUseFrame ring A use) ∧
    (D i).qCarry =
      .L (requestClockFoldDigitUses ledger.uses (true, false)).1
         (requestClockFoldDigitUses ledger.uses (true, false)).2

/-- Initial arbitrary physical carries have inherited ghost
origins. Thus no inherited Cartesian scratch is incorrectly
certified as a freshly launched comparison. -/
theorem requestClockFreshCarryInvariantInitial {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n) :
    RequestClockFreshCarryInvariant ring D
      (digitAuditInitial (piD D)) := by
  intro i ledger hledger hfresh
  have hinit :
      (DigitLaneGhost.initial .comparison i
        (digitLaneView .comparison
          ((piD D) i) ((piD D) i).word.beta)).carry =
        some ledger := by
    exact hledger
  have hnot := requestClockInitialCarryInherited
    .comparison i
    (digitLaneView .comparison
      ((piD D) i) ((piD D) i).word.beta)
    ledger hinit
  rw [hfresh] at hnot
  cases hnot

/-- Physical and ghost state both frame at a truly unrelated
edge. No assumption on the ledger's phase or numeral is needed;
its OLD recorded frames remain in the audit after the service. -/
theorem requestClockFreshCarryInvariantAway {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e i : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (he : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    ∀ ledger : DigitCarryGhost
        (compileAdvice (ceilLogTwo n)) n,
      ((digitAuditStep ring (piD D) A e).current i).comparison.carry =
        some ledger →
      ledger.inherited = none →
      RequestClockFreshUseChain
        (compileAdvice (ceilLogTwo n)) n ledger.uses ∧
      (∀ use : DigitUse (compileAdvice (ceilLogTwo n)) n,
        use ∈ ledger.uses →
          RequestClockOldUseFrame ring
            (digitAuditStep ring (piD D) A e) use) ∧
      ((headlinePhysicalNext ring D e) i).qCarry =
        .L (requestClockFoldDigitUses ledger.uses (true, false)).1
           (requestClockFoldDigitUses ledger.uses (true, false)).2 := by
  intro ledger hnew hfresh
  have hghost :
      ((digitAuditStep ring (piD D) A e).current i).comparison.carry =
        (A.current i).comparison.carry := by
    simp [digitAuditStep, digitGhostStep, he, hy]
  have hold : (A.current i).comparison.carry = some ledger := by
    rw [← hghost]
    exact hnew
  obtain ⟨hchain, hframes, hphysical⟩ := h i ledger hold hfresh
  refine ⟨hchain, ?_, ?_⟩
  · intro use hu
    exact requestClockOldUseFrameStep ring (piD D) A e use
      (hframes use hu)
  · have hp := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
      (headlineRendezvousStepAway ring D e i he hy)
    exact hp.trans hphysical

/-- Recorded DigitUse values fold to A.3's *same* arithmetic
list recursion, with no active private QCarry assumption. -/
private theorem requestClockFoldDigitUsesMap {c : Compiled} {n : Nat} :
    ∀ (uses : List (DigitUse c n)) (state : Bool × Bool),
      requestClockFoldDigitUses uses state =
        requestClockCarryList c
          (uses.map (fun use => (use.value, use.targetDigit))) state := by
  intro uses
  induction uses with
  | nil =>
      intro state
      rfl
  | cons use rest ih =>
      intro state
      change
        requestClockFoldDigitUses rest
          (checkerCarryNext c state use.value use.targetDigit) =
        requestClockCarryList c
          (rest.map (fun u => (u.value, u.targetDigit)))
          (checkerCarryNext c state use.value use.targetDigit)
      exact ih _

/-- A.3 applies directly to the list of *recorded* DigitUse
source/target operands. In the fresh case it starts at (true,false)
and exact addition follows whenever sticky error is false. -/
theorem requestClockFreshUseFoldArithmetic {c : Compiled} {n : Nat}
    (uses : List (DigitUse c n))
    (hzero : (requestClockFoldDigitUses uses (true, false)).2 = false) :
    requestClockTargetList c
        (uses.map (fun use => (use.value, use.targetDigit))) +
      (if (requestClockFoldDigitUses uses (true, false)).1
        then c.topA ^ uses.length else 0) =
    requestClockSourceList c
        (uses.map (fun use => (use.value, use.targetDigit))) + 1 := by
  have heq := requestClockFoldDigitUsesMap uses (true, false)
  have hz :
      (requestClockCarryList c
        (uses.map (fun use => (use.value, use.targetDigit)))
        (true, false)).2 = false := by
    rw [← heq]
    exact hzero
  have hs := (requestClockCarryListSound c
    (uses.map (fun use => (use.value, use.targetDigit)))
    (true, false) hz).2
  rw [← heq] at hs
  simpa only [List.length_map, if_true, ↓reduceIte] using hs


/-- The intended source/target pairs of a genuinely fresh
little-endian comparison, in the exact order in which QC3/QC2
use the source and destination digits. -/
private def requestClockExpectedDigitPairs {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (source : Fin n) :
    Nat → List (Fin c.topA × Fin c.topA)
  | 0 => []
  | k + 1 =>
      requestClockExpectedDigitPairs W source k ++
        [(certDigit W (certSite source k),
          certDigit W (certSite source (c.rho + k)))]

/-- A.3's plain pair-list recursion on a list with a last
source/target pair appended. -/
private theorem requestClockCarryListSnoc (c : Compiled) :
    ∀ (pairs : List (Fin c.topA × Fin c.topA))
      (state : Bool × Bool)
      (pair : Fin c.topA × Fin c.topA),
      requestClockCarryList c (pairs ++ [pair]) state =
        checkerCarryNext c (requestClockCarryList c pairs state)
          pair.1 pair.2 := by
  intro pairs
  induction pairs with
  | nil =>
      intro state pair
      rfl
  | cons first rest ih =>
      intro state pair
      change
        requestClockCarryList c (rest ++ [pair])
          (checkerCarryNext c state first.1 first.2) =
        checkerCarryNext c
          (requestClockCarryList c rest
            (checkerCarryNext c state first.1 first.2))
          pair.1 pair.2
      exact ih _ _

/-- Every intended digit prefix has the exact same carry fold
as checkerTruePartial, without assuming a physical packet has
yet established those digit values. -/
theorem requestClockExpectedDigitPairsFold {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (source : Fin n) :
    ∀ k : Nat,
      requestClockCarryList c
        (requestClockExpectedDigitPairs W source k)
        (true, false) =
      checkerTruePartial W source k := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change
        requestClockCarryList c
          (requestClockExpectedDigitPairs W source k ++
            [(certDigit W (certSite source k),
              certDigit W (certSite source (c.rho + k)))])
          (true, false) =
        checkerTruePartial W source (k + 1)
      rw [requestClockCarryListSnoc, ih]
      exact (checkerTruePartial_succ W source k).symm

/-- The precise missing frozen-digit correspondence needed at
strict completion: equality of the *recorded* use pairs and
the intended source/target digit-prefix list. If this witness
is provided, the raw ledger fold is the genuine checker. -/
theorem requestClockMatchedUseFoldIsChecker {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (source : Fin n)
    (uses : List (DigitUse c n)) (k : Nat)
    (hpairs :
      uses.map (fun use => (use.value, use.targetDigit)) =
        requestClockExpectedDigitPairs W source k) :
    requestClockFoldDigitUses uses (true, false) =
      checkerTruePartial W source k := by
  calc
    requestClockFoldDigitUses uses (true, false) =
      requestClockCarryList c
        (uses.map (fun use => (use.value, use.targetDigit)))
        (true, false) := requestClockFoldDigitUsesMap uses (true, false)
    _ = requestClockCarryList c
        (requestClockExpectedDigitPairs W source k)
        (true, false) := by rw [hpairs]
    _ = checkerTruePartial W source k :=
      requestClockExpectedDigitPairsFold W source k

/-- The checker arithmetic conclusion at a bad OLD public pair.
This is a conditional TERMINAL ledger-to-static-checker fact:
the missing input is not arithmetic but the use-by-use frozen
digit map plus the real terminal physical/fold correspondence. -/
theorem requestClockBadPairOldErrorOfMatchedUses {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (source e : Fin n)
    (pfx : List (Fin n))
    (ledger : DigitCarryGhost
      (compileAdvice (ceilLogTwo n)) n)
    (hbad : BadCompletePair C source)
    (hpairs :
      ledger.uses.map (fun use => (use.value, use.targetDigit)) =
        requestClockExpectedDigitPairs (publicWord C) source
          (compileAdvice (ceilLogTwo n)).rho)
    (hphysical :
      qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
        (requestClockFoldDigitUses ledger.uses (true, false)).2) :
    qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
      true := by
  have hfold := requestClockMatchedUseFoldIsChecker
    (publicWord C) source ledger.uses
    (compileAdvice (ceilLogTwo n)).rho hpairs
  calc
    qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
        (requestClockFoldDigitUses ledger.uses (true, false)).2 :=
          hphysical
    _ = (checkerTruePartial (publicWord C) source
        (compileAdvice (ceilLogTwo n)).rho).2 :=
          congrArg Prod.snd hfold
    _ = true := checkerTruePartialBad C source hbad

/-- An actual strictly completed OLD terminal gives the same
error conclusion as soon as the two *specific* missing physical
per-use facts are supplied for its live ghost ledger.
The terminal-to-OLD snapshot is the existing theorem. -/
theorem requestClockStrictOldErrorOfMatchedTrace {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (source : Fin n) (pfx : List (Fin n)) (e : Fin n)
    (hbad : BadCompletePair C source)
    (hstrict : StrictCompletesAt ring C source pfx e)
    (htrace :
      ∀ ledger : DigitCarryGhost
          (compileAdvice (ceilLogTwo n)) n,
        ((auditedRealRun ring C pfx).2.current e).comparison.carry =
            some ledger →
        ledger.inherited = none →
        ledger.uses.length = (compileAdvice (ceilLogTwo n)).rho →
        ledger.uses.map
          (fun use => (use.value, use.targetDigit)) =
            requestClockExpectedDigitPairs (publicWord C) source
              (compileAdvice (ceilLogTwo n)).rho ∧
        qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
          (requestClockFoldDigitUses ledger.uses (true, false)).2) :
    qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
      true := by
  obtain ⟨terminal, ledger, hledger, hfresh,
    hsize, hcurrent, herror⟩ :=
    requestClockStrictTerminalOldSnapshot ring C source pfx e hstrict
  obtain ⟨hpairs, hphysical⟩ :=
    htrace ledger hcurrent hfresh hsize
  exact requestClockBadPairOldErrorOfMatchedUses ring C
    source e pfx ledger hbad hpairs hphysical


/-- The per-site component of RequestClockFreshCarryInvariant.
It is stated separately so that the global physical step needs
only two touched-edge proofs; all remote sites are already framed. -/
def RequestClockFreshCarryAt {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i : Fin n) : Prop :=
  ∀ ledger : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
    ((A.current i).comparison.carry = some ledger) →
    ledger.inherited = none →
    RequestClockFreshUseChain
      (compileAdvice (ceilLogTwo n)) n ledger.uses ∧
    (∀ use : DigitUse (compileAdvice (ceilLogTwo n)) n,
      use ∈ ledger.uses → RequestClockOldUseFrame ring A use) ∧
    (D i).qCarry =
      .L (requestClockFoldDigitUses ledger.uses (true, false)).1
         (requestClockFoldDigitUses ledger.uses (true, false)).2

/-- The whole invariant is exactly the conjunction over sites. -/
theorem requestClockFreshCarryAtIff {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    RequestClockFreshCarryInvariant ring D A ↔
      ∀ i : Fin n, RequestClockFreshCarryAt ring D A i := by
  rfl

/-- Pure geometry reduces full physical-step preservation to the
source and responder. The nonincident edges are *unconditional*
physical/ghost frames, already proved above. -/
theorem requestClockFreshCarryStepOfEndpoints {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hx :
      RequestClockFreshCarryAt ring
        (headlinePhysicalNext ring D e)
        (digitAuditStep ring (piD D) A e) e)
    (hy :
      RequestClockFreshCarryAt ring
        (headlinePhysicalNext ring D e)
        (digitAuditStep ring (piD D) A e)
        (ring.rightNeighbor e)) :
    RequestClockFreshCarryInvariant ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) := by
  intro i ledger hlive hfresh
  by_cases he : i = e
  · subst i
    exact hx ledger hlive hfresh
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      exact hy ledger hlive hfresh
    · exact requestClockFreshCarryInvariantAway ring
        D A e i h he hj ledger hlive hfresh

/-- The remaining named source-level obligation: under an
authenticated OLD cut, the two endpoints of the selected
physical/ghost service satisfy the corrected carry invariant.
It includes arbitrary inherited scratch and ALL pair outcomes. -/
def RequestClockFreshEndpointRows {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n),
      RequestClockFreshCarryInvariant ring D A →
      RequestClockFreshCarryAt ring
        (headlinePhysicalNext ring D e)
        (digitAuditStep ring (piD D) A e) e ∧
      RequestClockFreshCarryAt ring
        (headlinePhysicalNext ring D e)
        (digitAuditStep ring (piD D) A e)
        (ring.rightNeighbor e)

/-- The actual auditedRealRun induction is now entirely formal
from the two physical endpoint rows. This is a CONDITIONAL
consumer, not a claim that those rows are already discharged. -/
theorem requestClockFreshCarryInvariantOnRealWordOfEndpointRows
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hrows : RequestClockFreshEndpointRows ring)
    (word : List (Fin n)) :
    RequestClockFreshCarryInvariant ring
      (auditedRealRun ring C word).1
      (auditedRealRun ring C word).2 := by
  have key : ∀ rev : List (Fin n),
      RequestClockFreshCarryInvariant ring
        (auditedRealRun ring C rev.reverse).1
        (auditedRealRun ring C rev.reverse).2 := by
    intro rev
    induction rev with
    | nil =>
        exact requestClockFreshCarryInvariantInitial ring C
    | cons e rev ih =>
        rw [List.reverse_cons]
        have hh := hrows
          (auditedRealRun ring C rev.reverse).1
          (auditedRealRun ring C rev.reverse).2 e ih
        have hstep := requestClockFreshCarryStepOfEndpoints ring
          (auditedRealRun ring C rev.reverse).1
          (auditedRealRun ring C rev.reverse).2 e
          ih hh.1 hh.2
        rw [checkerAuditedRunAppendOne ring C rev.reverse e]
        exact hstep
  have hh := key word.reverse
  simpa only [List.reverse_reverse] using hh


/-- Productive QC3 on one literal Agent pair simultaneously:
the replay ledger starts at (true,false), and the assembled
physical source QCarry holds exactly the one-use fold.
The selected-edge lift still needs the existing source frame. -/
theorem requestClockQC3PairedPhysicalGhost {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : Agent c)
    (gx gy : DigitLaneGhost c n)
    (value : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hmarker : x.beta = true)
    (hfree : x.qCarry = .OFF)
    (hinput : x.qIn = .S value tail) :
    (digitLaneReplay .comparison time source destination
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta)
      gx gy).x.carry =
        some
          ({ inherited := none
             uses :=
               [requestClockQC3FirstUse time source
                 (digitLaneView .comparison
                   (ProjD.ofAgent x) x.beta) gx] } :
            DigitCarryGhost c n) ∧
    RequestClockFreshUseChain c n
      [requestClockQC3FirstUse time source
        (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx] ∧
    (transition c x y).1.qCarry =
      .L (requestClockFoldDigitUses
        [requestClockQC3FirstUse time source
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx]
        (true, false)).1
         (requestClockFoldDigitUses
        [requestClockQC3FirstUse time source
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx]
        (true, false)).2 := by
  have hx :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).leader =
        false := by
    change x.l = false
    exact hxl
  have hy :
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta).leader =
        false := by
    change y.l = false
    exact hyl
  have hmark :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).marker =
        true := by
    change x.beta = true
    exact hmarker
  have hoff :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).carryLive =
        false := by
    change x.qCarry.isL = false
    rw [hfree]
    rfl
  have hsettled :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).input.isS =
        true := by
    change x.qIn.isS = true
    rw [hinput]
    rfl
  have hghost := requestClockQC3ReplayBirth time source destination
    (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
    (digitLaneView .comparison (ProjD.ofAgent y) y.beta)
    gx gy hx hy hmark hoff hsettled
  have hphysical := checkerTransitionCarryLaunch c x y tail value
    hxl hyl hfree hinput hmarker
  have hfold :
      requestClockFoldDigitUses
        [requestClockQC3FirstUse time source
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx]
        (true, false) =
        checkerCarryNext c (true, false) value x.d := by
    have hh := requestClockQC3FirstUseFold time source
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx
    change
      requestClockFoldDigitUses
        [requestClockQC3FirstUse time source
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx]
        (true, false) =
        checkerCarryNext c (true, false) (inV c x.qIn) x.d at hh
    rw [hinput] at hh
    exact hh
  refine ⟨hghost, requestClockQC3FreshUseChain time source
    (digitLaneView .comparison (ProjD.ofAgent x) x.beta) gx, ?_⟩
  rw [hfold]
  exact hphysical

/-- Productive QC2 on one literal Agent pair simultaneously:
the replay ghost appends the OLD physical carry/error, preserves
the fresh chain, and the real responder's POST carry is the
arithmetic fold of all old uses plus the new one. -/
theorem requestClockQC2PairedPhysicalGhost {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : Agent c)
    (gx gy : DigitLaneGhost c n)
    (ledger : DigitCarryGhost c n)
    (value : Fin c.topA) (tail carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcarry : x.qCarry = .L carry error)
    (hfree : y.qCarry = .OFF)
    (hinput : y.qIn = .S value tail)
    (hmarker : y.beta = false)
    (hledger : gx.carry = some ledger)
    (hchain : RequestClockFreshUseChain c n ledger.uses)
    (hfold :
      requestClockFoldDigitUses ledger.uses (true, false) =
        (carry, error)) :
    (digitLaneReplay .comparison time source destination
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta)
      gx gy).y.carry =
        some
          { ledger with uses := ledger.uses ++
            [requestClockQC2NextUse time destination
              (digitLaneView .comparison
                (ProjD.ofAgent y) y.beta) gy carry error] } ∧
    RequestClockFreshUseChain c n
      (ledger.uses ++
        [requestClockQC2NextUse time destination
          (digitLaneView .comparison
            (ProjD.ofAgent y) y.beta) gy carry error]) ∧
    (transition c x y).2.qCarry =
      .L (requestClockFoldDigitUses
        (ledger.uses ++
          [requestClockQC2NextUse time destination
            (digitLaneView .comparison
              (ProjD.ofAgent y) y.beta) gy carry error])
        (true, false)).1
         (requestClockFoldDigitUses
        (ledger.uses ++
          [requestClockQC2NextUse time destination
            (digitLaneView .comparison
              (ProjD.ofAgent y) y.beta) gy carry error])
        (true, false)).2 := by
  have hx :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).leader =
        false := by
    change x.l = false
    exact hxl
  have hy :
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta).leader =
        false := by
    change y.l = false
    exact hyl
  have hlive :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).carryLive =
        true := by
    change x.qCarry.isL = true
    rw [hcarry]
    rfl
  have hoff :
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta).carryLive =
        false := by
    change y.qCarry.isL = false
    rw [hfree]
    rfl
  have hmark :
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta).marker =
        false := by
    change y.beta = false
    exact hmarker
  have hsettled :
      (digitLaneView .comparison (ProjD.ofAgent y) y.beta).input.isS =
        true := by
    change y.qIn.isS = true
    rw [hinput]
    rfl
  have hghost := requestClockQC2ReplayAppend time source destination
    (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
    (digitLaneView .comparison (ProjD.ofAgent y) y.beta)
    gx gy ledger hx hy hlive hmark hoff hsettled hledger
  have hcb :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).carryBit =
        carry := by
    change qcC x.qCarry = carry
    rw [hcarry]
    rfl
  have hce :
      (digitLaneView .comparison (ProjD.ofAgent x) x.beta).carryError =
        error := by
    change qcE x.qCarry = error
    rw [hcarry]
    rfl
  rw [hcb, hce] at hghost
  have hphysical := checkerTransitionCarryAdvance c x y
    carry error tail value hxl hyl hcarry hfree hinput hmarker
  have hnext := requestClockQC2FreshUseFoldAppend ledger.uses
    time destination
    (digitLaneView .comparison (ProjD.ofAgent y) y.beta)
    gy carry error hfold
  change
    requestClockFoldDigitUses
      (ledger.uses ++
        [requestClockQC2NextUse time destination
          (digitLaneView .comparison
            (ProjD.ofAgent y) y.beta) gy carry error])
      (true, false) =
    checkerCarryNext c (carry, error) (inV c y.qIn) y.d at hnext
  rw [hinput] at hnext
  have hnewChain := requestClockQC2FreshUseChainAppend ledger.uses
    time destination
    (digitLaneView .comparison (ProjD.ofAgent y) y.beta)
    gy carry error hchain hfold
  refine ⟨hghost, hnewChain, ?_⟩
  rw [hnext]
  exact hphysical


/-- The true comparison terminal consumes NO new DigitUse: it
copies the OLD source ghost ledger/error to the terminal receipt
and deletes that source's live carry. The resident responder
ghost is unchanged. -/
theorem requestClockQCTerminalReplay {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hlive : x.carryLive = true)
    (hmarker : y.marker = true) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.carry = none ∧
    (digitLaneReplay .comparison time source destination
      x y gx gy).y.carry = gy.carry ∧
    (digitLaneReplay .comparison time source destination
      x y gx gy).terminal =
      some
        ({ time := time
           lane := .comparison
           source := source
           destination := destination
           ledger := gx.carry
           carryBit := x.carryBit
           errorBit := x.carryError } : DigitTerminal c n) := by
  simp [digitLaneReplay, hxl, hyl, hlive, hmarker]

/-- When a selected endpoint is an OLD root, a live source
comparison carry is killed, and no fresh ledger is created.
The ghost response is distinct from a valid terminal receipt. -/
theorem requestClockQCSourceRootKill {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hroot : x.leader = true ∨ y.leader = true)
    (hlive : x.carryLive = true) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.carry = none := by
  rcases hroot with hx | hy
  · simp [digitLaneReplay, hx, hlive]
  · simp [digitLaneReplay, hy, hlive]

end HeadlineDigit
end L3

/-!
Endpoint rows of the corrected QC3/QC2 carry invariant.
No imported dependencies.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-- Source-first projection of the real audit's new comparison
ghost onto the OLD physical pair's literal replay. -/
private theorem requestClockQCSourceGhostFrame {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    ((digitAuditStep ring (piD D) A e).current e).comparison.carry =
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison
          ((piD D) e) ((piD D) e).word.beta)
        (digitLaneView .comparison
          ((piD D) (ring.rightNeighbor e))
          ((piD D) (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).x.carry := by
  simp [digitAuditStep, digitGhostStep, digitService]

/-- The invariant forces every genuinely fresh live ledger to
have an actual physical QCarry, not an arbitrary OFF record. -/
theorem requestClockFreshLedgerPhysicalLive {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (ledger : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hlive : ((A.current i).comparison.carry = some ledger))
    (hfresh : ledger.inherited = none) :
    (D i).qCarry.isL = true := by
  have hp := (h i ledger hlive hfresh).2.2
  rw [hp]
  rfl

/-- A physical OLD OFF carry cannot have a fresh associated
ghost ledger at a cut satisfying the invariant. -/
theorem requestClockFreshLedgerNotAtOff {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hoff : (D i).qCarry = .OFF)
    (ledger : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hlive : (A.current i).comparison.carry = some ledger) :
    ledger.inherited ≠ none := by
  intro hfresh
  have hh := requestClockFreshLedgerPhysicalLive ring D A i
    h ledger hlive hfresh
  rw [hoff] at hh
  cases hh

/-- Any live OLD comparison carry leaves the selected SOURCE
ghost slot on this edge, whether it succeeds, aborts, reaches
a terminal, or encounters a native root. -/
theorem requestClockQCSourceLiveDropsGhost {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hlive : x.carryLive = true) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.carry = none := by
  simp [digitLaneReplay, hlive]

/-- A site whose new ghost carry is absent satisfies the fresh
invariant unconditionally, independently of its physical fields. -/
theorem requestClockFreshCarryAtAbsent {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i : Fin n)
    (habsent : (A.current i).comparison.carry = none) :
    RequestClockFreshCarryAt ring D A i := by
  intro ledger hledger _
  rw [habsent] at hledger
  cases hledger

/-- Both physical QCarry and the ghost ledger are unchanged at
a held/resident carry. Previously recorded OLD-frame witnesses
persist when one new real frame is prepended. -/
theorem requestClockFreshCarryAtHeld {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e i : Fin n)
    (h : RequestClockFreshCarryAt ring D A i)
    (hghost :
      ((digitAuditStep ring (piD D) A e).current i).comparison.carry =
        (A.current i).comparison.carry)
    (hphysical :
      ((headlinePhysicalNext ring D e) i).qCarry = (D i).qCarry) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) i := by
  intro ledger hnew hfresh
  have hold :
      (A.current i).comparison.carry = some ledger :=
    hghost.symm.trans hnew
  obtain ⟨hchain, hframes, hcarry⟩ := h ledger hold hfresh
  refine ⟨hchain, ?_, ?_⟩
  · intro use hu
    exact requestClockOldUseFrameStep ring (piD D) A e use
      (hframes use hu)
  · exact hphysical.trans hcarry

/-- A source carrying any live OLD QCarry contributes no new
fresh ghost ledger at the selected initiator, even if its
comparison is immediately terminated or aborted. -/
theorem requestClockFreshCarryAtSourceLive {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hlive : (D e).qCarry.isL = true) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) e := by
  have hview :
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).carryLive = true := by
    change (D e).qCarry.isL = true
    exact hlive
  have hdropped :=
    requestClockQCSourceLiveDropsGhost
      (A.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta)
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta)
      (A.current e).comparison
      (A.current (ring.rightNeighbor e)).comparison hview
  have hnone :
      ((digitAuditStep ring (piD D) A e).current e).comparison.carry =
        none := by
    exact (requestClockQCSourceGhostFrame ring D A e).trans hdropped
  exact requestClockFreshCarryAtAbsent ring
    (headlinePhysicalNext ring D e)
    (digitAuditStep ring (piD D) A e) e hnone

/-- The actual freshly launched QC3 source row is valid,
including the first virtual carry seed and historical OLD
frame witness. This is not a hypothetical pair receipt: it
is attached to the selected physical OLD source edge. -/
theorem requestClockFreshCarryAtSourceBirth {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hmarker : (D e).beta = true)
    (hfree : (D e).qCarry = .OFF)
    (hinput : (D e).qIn = .S v tail) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) e := by
  have hpaired := requestClockQC3PairedPhysicalGhost
    (A.clock + 1) e (ring.rightNeighbor e)
    (D e) (D (ring.rightNeighbor e))
    (A.current e).comparison
    (A.current (ring.rightNeighbor e)).comparison
    v tail hxl hyl hmarker hfree hinput
  intro ledger hnew hfresh
  have hnew' :
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (D e))
          (D e).beta)
        (digitLaneView .comparison
          (ProjD.ofAgent (D (ring.rightNeighbor e)))
          (D (ring.rightNeighbor e)).beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).x.carry =
        some ledger := by
    have hs := (requestClockQCSourceGhostFrame ring D A e).symm.trans hnew
    exact hs
  rw [hpaired.1] at hnew'
  cases hnew'
  refine ⟨hpaired.2.1, ?_, ?_⟩
  · intro use hu
    have heq :
        use = requestClockQC3FirstUse (A.clock + 1) e
          (digitLaneView .comparison (ProjD.ofAgent (D e))
            (D e).beta)
          (A.current e).comparison := by
      simpa only [List.mem_singleton] using hu
    subst use
    exact requestClockOldUseFrameBirth ring (piD D) A e hfree
  · have hphysical := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
      (headlineRendezvousStepAtSource ring D e)
    exact hphysical.trans hpaired.2.2


/-- With no OLD source comparison carry, a nonproductive
selected source cannot create a fresh ledger: root incidence,
a non-marker source, or a non-settled source input frames the
old source ghost carry. -/
private theorem requestClockQCSourceNoLaunchGhost {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hfree : x.carryLive = false)
    (hstop : x.leader = true ∨ y.leader = true ∨
      x.marker = false ∨ x.input.isS = false) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.carry = gx.carry := by
  rcases hstop with hx | hy | hm | hi
  · simp [digitLaneReplay, hx, hfree]
  · simp [digitLaneReplay, hy, hfree]
  · simp [digitLaneReplay, hm, hfree]
  · simp [digitLaneReplay, hi, hfree]

/-- A nonproductive OFF source preserves its old ghost carry,
which must be inherited if occupied: the global invariant
rules out any fresh ledger at an OLD OFF physical source. -/
theorem requestClockFreshCarryAtSourceNoLaunch {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hoff : (D e).qCarry = .OFF)
    (hstop : (D e).l = true ∨
      (D (ring.rightNeighbor e)).l = true ∨
      (D e).beta = false ∨ (D e).qIn.isS = false) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) e := by
  have hfree :
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).carryLive = false := by
    change (D e).qCarry.isL = false
    rw [hoff]
    rfl
  have hguard :
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).leader = true ∨
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).leader = true ∨
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).marker = false ∨
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).input.isS = false := by
    exact hstop
  have hframe := requestClockQCSourceNoLaunchGhost
    (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison ((piD D) e)
      ((piD D) e).word.beta)
    (digitLaneView .comparison
      ((piD D) (ring.rightNeighbor e))
      ((piD D) (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison
    (A.current (ring.rightNeighbor e)).comparison
    hfree hguard
  have hghost :
      ((digitAuditStep ring (piD D) A e).current e).comparison.carry =
        (A.current e).comparison.carry :=
    (requestClockQCSourceGhostFrame ring D A e).trans hframe
  intro ledger hnew hfresh
  have hold := hghost.symm.trans hnew
  have hbad := requestClockFreshLedgerNotAtOff
    ring D A e h hoff ledger hold
  exact False.elim (hbad hfresh)

/-- The selected source endpoint is now completely discharged:
every OLD source either holds a live carry (which leaves), is
an OFF source taking QC3, or is an OFF source framing its
non-fresh ghost ledger. -/
theorem requestClockFreshCarryAtSourceEveryEdge {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) e := by
  cases hcarry : (D e).qCarry with
  | L carry error =>
      apply requestClockFreshCarryAtSourceLive ring D A e
      rw [hcarry]
      rfl
  | OFF =>
      by_cases hxroot : (D e).l = true
      · exact requestClockFreshCarryAtSourceNoLaunch
          ring D A e h hcarry (Or.inl hxroot)
      · by_cases hyroot :
          (D (ring.rightNeighbor e)).l = true
        · exact requestClockFreshCarryAtSourceNoLaunch
            ring D A e h hcarry (Or.inr (Or.inl hyroot))
        · have hxl : (D e).l = false := by
            cases hb : (D e).l with
            | false => rfl
            | true => exact False.elim (hxroot hb)
          have hyl : (D (ring.rightNeighbor e)).l = false := by
            cases hb : (D (ring.rightNeighbor e)).l with
            | false => rfl
            | true => exact False.elim (hyroot hb)
          by_cases hmarker : (D e).beta = true
          · cases hinput : (D e).qIn with
            | E =>
                exact requestClockFreshCarryAtSourceNoLaunch
                  ring D A e h hcarry
                  (Or.inr (Or.inr (Or.inr (by rw [hinput]; rfl))))
            | X =>
                exact requestClockFreshCarryAtSourceNoLaunch
                  ring D A e h hcarry
                  (Or.inr (Or.inr (Or.inr (by rw [hinput]; rfl))))
            | P value tail =>
                exact requestClockFreshCarryAtSourceNoLaunch
                  ring D A e h hcarry
                  (Or.inr (Or.inr (Or.inr (by rw [hinput]; rfl))))
            | S value tail =>
                exact requestClockFreshCarryAtSourceBirth
                  ring D A e value tail
                  hxl hyl hmarker hcarry hinput
          · have hm : (D e).beta = false := by
              cases hb : (D e).beta with
              | false => rfl
              | true => exact False.elim (hmarker hb)
            exact requestClockFreshCarryAtSourceNoLaunch
              ring D A e h hcarry (Or.inr (Or.inr (Or.inl hm)))


/-- A distinct right neighbor forces at least two sites, even
without an externally stated population-size hypothesis. -/
private theorem requestClockDistinctNeighborTwo {n : Nat}
    (ring : DirectedRing n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) : 2 ≤ n := by
  by_cases hn : 2 ≤ n
  · exact hn
  · have he : e.val < n := e.isLt
    have hj : (ring.rightNeighbor e).val < n :=
      (ring.rightNeighbor e).isLt
    have heq : (ring.rightNeighbor e).val = e.val := by omega
    exact False.elim (hne (Fin.ext heq))

/-- On a genuinely distinct responder, the new audit ghost is
the Y component of this exact comparison-lane replay. -/
private theorem requestClockResponderGhostFrame {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    ((digitAuditStep ring (piD D) A e).current
      (ring.rightNeighbor e)).comparison.carry =
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison
          ((piD D) e) ((piD D) e).word.beta)
        (digitLaneView .comparison
          ((piD D) (ring.rightNeighbor e))
          ((piD D) (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).y.carry := by
  simp [digitAuditStep, digitGhostStep, digitService,
    hne]

/-- A free OLD responder's ghost carry is unchanged except for
a productive QC2 incoming advance. These disjoint cases block
QC2: root, no source live carry, terminal marker or no settled
responder input. -/
private theorem requestClockQCResponderNoAdvanceGhost
    {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hfree : y.carryLive = false)
    (hstop : x.leader = true ∨ y.leader = true ∨
      x.carryLive = false ∨ y.marker = true ∨
      y.input.isS = false) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).y.carry = gy.carry := by
  rcases hstop with hx | hy | hsrc | hm | hi
  · simp [digitLaneReplay, hx, hfree]
  · simp [digitLaneReplay, hy, hfree]
  · simp [digitLaneReplay, hsrc, hfree]
  · simp [digitLaneReplay, hm, hfree]
  · simp [digitLaneReplay, hi, hfree]

/-- An OFF responder with no productive incoming QC2 cannot
develop a fresh carry. This handles inherited old ghost scratch
without assuming it accurately represents a live carry. -/
theorem requestClockFreshCarryAtResponderNoAdvance {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hne : ring.rightNeighbor e ≠ e)
    (hoff : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hstop : (D e).l = true ∨
      (D (ring.rightNeighbor e)).l = true ∨
      (D e).qCarry.isL = false ∨
      (D (ring.rightNeighbor e)).beta = true ∨
      (D (ring.rightNeighbor e)).qIn.isS = false) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e)
      (ring.rightNeighbor e) := by
  have hfree :
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).carryLive =
          false := by
    change (D (ring.rightNeighbor e)).qCarry.isL = false
    rw [hoff]
    rfl
  have hguard :
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).leader = true ∨
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).leader = true ∨
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).carryLive = false ∨
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).marker = true ∨
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).input.isS =
          false := by
    exact hstop
  have hframe := requestClockQCResponderNoAdvanceGhost
    (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison ((piD D) e)
      ((piD D) e).word.beta)
    (digitLaneView .comparison
      ((piD D) (ring.rightNeighbor e))
      ((piD D) (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison
    (A.current (ring.rightNeighbor e)).comparison hfree hguard
  have hresp := requestClockResponderGhostFrame ring D A e hne
  have hghost :
      ((digitAuditStep ring (piD D) A e).current
        (ring.rightNeighbor e)).comparison.carry =
          (A.current (ring.rightNeighbor e)).comparison.carry :=
    hresp.trans hframe
  intro ledger hnew hfresh
  have hold := hghost.symm.trans hnew
  have hbad := requestClockFreshLedgerNotAtOff ring D A
    (ring.rightNeighbor e) h hoff ledger hold
  exact False.elim (hbad hfresh)

/-- The ghost half of the resident comparison-carry row:
an OLD live responder retains its old ledger on a rootless
selected edge, whether the initiator launches/aborts or not. -/
private theorem requestClockQCResidentGhostFrame {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hlive : y.carryLive = true) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).y.carry = gy.carry := by
  simp [digitLaneReplay, hxl, hyl, hlive]

/-- The physical half: an OLD live responder cannot receive a
second carry. Its physical qCarry remains the same, even if the
initiator aborts a competing live carry. -/
private theorem requestClockQCResidentPhysicalFrame (c : Compiled)
    (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false)
    (hlive : y.qCarry.isL = true) :
    (transition c x y).2.qCarry = y.qCarry := by
  have howner := (checkerTransitionCarryOwner c x y).2
  rw [howner]
  cases hcx : x.qCarry <;>
    cases hcy : y.qCarry
  · rw [hcy] at hlive
    cases hlive
  · simp [liveTopPair, hxl, hyl, hcx, hcy,
      QCarry.isL, QCarry.isOff, topTerminal]
  · rw [hcy] at hlive
    cases hlive
  · simp [liveTopPair, hxl, hyl, hcx, hcy,
      QCarry.isL, QCarry.isOff, topTerminal]

/-- The responder root branch erases an OLD live comparison
carry and therefore cannot leave a fresh ghost ledger. -/
private theorem requestClockQCResponderRootGhostDrop {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hroot : x.leader = true ∨ y.leader = true)
    (hlive : y.carryLive = true) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).y.carry = none := by
  rcases hroot with hx | hy
  · simp [digitLaneReplay, hx, hlive]
  · simp [digitLaneReplay, hy, hlive]

/-- The full OLD live responder branch is either a root-induced
ghost erasure, or an unchanged physical and ghost resident carry.
It is independent of the source's inherited packet scratch. -/
theorem requestClockFreshCarryAtResponderResident {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hne : ring.rightNeighbor e ≠ e)
    (hlive : (D (ring.rightNeighbor e)).qCarry.isL = true) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e)
      (ring.rightNeighbor e) := by
  by_cases hxroot : (D e).l = true
  · have hdrop := requestClockQCResponderRootGhostDrop
      (A.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta)
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta)
      (A.current e).comparison
      (A.current (ring.rightNeighbor e)).comparison
      (Or.inl hxroot) hlive
    have hresp := requestClockResponderGhostFrame ring D A e hne
    exact requestClockFreshCarryAtAbsent ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e)
      (ring.rightNeighbor e) (hresp.trans hdrop)
  · by_cases hyroot : (D (ring.rightNeighbor e)).l = true
    · have hdrop := requestClockQCResponderRootGhostDrop
        (A.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison ((piD D) e)
          ((piD D) e).word.beta)
        (digitLaneView .comparison
          ((piD D) (ring.rightNeighbor e))
          ((piD D) (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison
        (Or.inr hyroot) hlive
      have hresp := requestClockResponderGhostFrame ring D A e hne
      exact requestClockFreshCarryAtAbsent ring
        (headlinePhysicalNext ring D e)
        (digitAuditStep ring (piD D) A e)
        (ring.rightNeighbor e) (hresp.trans hdrop)
    · have hxl : (D e).l = false := by
        cases hbool : (D e).l with
        | false => rfl
        | true => exact False.elim (hxroot hbool)
      have hyl : (D (ring.rightNeighbor e)).l = false := by
        cases hbool : (D (ring.rightNeighbor e)).l with
        | false => rfl
        | true => exact False.elim (hyroot hbool)
      have hghostRow := requestClockQCResidentGhostFrame
        (A.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison ((piD D) e)
          ((piD D) e).word.beta)
        (digitLaneView .comparison
          ((piD D) (ring.rightNeighbor e))
          ((piD D) (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison
        hxl hyl hlive
      have hresp := requestClockResponderGhostFrame ring D A e hne
      have hghost :
          ((digitAuditStep ring (piD D) A e).current
            (ring.rightNeighbor e)).comparison.carry =
            (A.current (ring.rightNeighbor e)).comparison.carry :=
        hresp.trans hghostRow
      have hp := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
        (headlineRendezvousStepAtResponder ring
          (requestClockDistinctNeighborTwo ring e hne) D e)
      have hrow := requestClockQCResidentPhysicalFrame
        (compileAdvice (ceilLogTwo n))
        (D e) (D (ring.rightNeighbor e)) hxl hyl hlive
      exact requestClockFreshCarryAtHeld ring D A e
        (ring.rightNeighbor e) (h (ring.rightNeighbor e))
        hghost (hp.trans hrow)


/-- Productive QC2 with an OLD fresh source ledger satisfies
the full NEW responder invariant: the historical receipt list
is extended by the actual source carry, the fresh chain grows,
and the POST physical responder qCarry is the same fold. -/
theorem requestClockFreshCarryAtResponderAdvanceFresh {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hne : ring.rightNeighbor e ≠ e)
    (carry error tail : Bool)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hcarry : (D e).qCarry = .L carry error)
    (hfree : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hinput : (D (ring.rightNeighbor e)).qIn = .S value tail)
    (hmarker : (D (ring.rightNeighbor e)).beta = false)
    (old : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hledger : (A.current e).comparison.carry = some old)
    (hfresh : old.inherited = none) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e)
      (ring.rightNeighbor e) := by
  obtain ⟨hchain, hframes, holdPhysical⟩ :=
    h e old hledger hfresh
  have hcarryBit := congrArg qcC holdPhysical
  rw [hcarry] at hcarryBit
  change carry =
    (requestClockFoldDigitUses old.uses (true, false)).1
      at hcarryBit
  have herrorBit := congrArg qcE holdPhysical
  rw [hcarry] at herrorBit
  change error =
    (requestClockFoldDigitUses old.uses (true, false)).2
      at herrorBit
  have hfold :
      requestClockFoldDigitUses old.uses (true, false) =
        (carry, error) :=
    Prod.ext hcarryBit.symm herrorBit.symm
  have hpaired := requestClockQC2PairedPhysicalGhost
    (A.clock + 1) e (ring.rightNeighbor e)
    (D e) (D (ring.rightNeighbor e))
    (A.current e).comparison
    (A.current (ring.rightNeighbor e)).comparison
    old value tail carry error
    hxl hyl hcarry hfree hinput hmarker
    hledger hchain hfold
  intro ledger hnew _
  have hresp := requestClockResponderGhostFrame ring D A e hne
  have hnew' :
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison ((piD D) e)
          ((piD D) e).word.beta)
        (digitLaneView .comparison
          ((piD D) (ring.rightNeighbor e))
          ((piD D) (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).y.carry =
          some ledger :=
    hresp.symm.trans hnew
  have hnew2 := hpaired.1.symm.trans hnew'
  cases hnew2
  refine ⟨hpaired.2.1, ?_, ?_⟩
  · intro use hu
    rcases List.mem_append.mp hu with hprevious | hlast
    · exact requestClockOldUseFrameStep ring (piD D) A e
        use (hframes use hprevious)
    · have heq :
          use = requestClockQC2NextUse (A.clock + 1)
            (ring.rightNeighbor e)
            (digitLaneView .comparison
              ((piD D) (ring.rightNeighbor e))
              ((piD D) (ring.rightNeighbor e)).word.beta)
            (A.current (ring.rightNeighbor e)).comparison
            carry error := by
        have hl := List.mem_singleton.mp hlast
        exact hl
      subst use
      exact requestClockOldUseFrameAdvance ring
        (piD D) A e carry error hcarry
  · have hphysical := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
      (headlineRendezvousStepAtResponder ring
        (requestClockDistinctNeighborTwo ring e hne) D e)
    exact hphysical.trans hpaired.2.2


/-- A productive QC2 receiver cannot manufacture a fresh
ledger from missing or inherited source ghost scratch.
If the resulting ledger is fresh, a fresh OLD source ledger
must exist. This checks the getD missing-stamp fallback. -/
private theorem requestClockQC2FreshOrigin {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hlive : x.carryLive = true)
    (hmarker : y.marker = false)
    (hfree : y.carryLive = false)
    (hinput : y.input.isS = true)
    (newLedger : DigitCarryGhost c n)
    (hnew :
      (digitLaneReplay .comparison time source destination
        x y gx gy).y.carry = some newLedger)
    (hfresh : newLedger.inherited = none) :
    ∃ old : DigitCarryGhost c n,
      gx.carry = some old ∧ old.inherited = none := by
  cases hg : gx.carry with
  | none =>
      have hformula :
          (digitLaneReplay .comparison time source destination
            x y gx gy).y.carry =
          some
            ({ inherited :=
                 some (.missing
                   { time := time, site := source, lane := .comparison }
                   .carry)
               uses := [requestClockQC2NextUse time destination
                 y gy x.carryBit x.carryError] } :
              DigitCarryGhost c n) := by
        simp [digitLaneReplay, requestClockQC2NextUse,
          hxl, hyl, hlive, hmarker, hfree, hinput, hg]
      rw [hformula] at hnew
      cases hnew
      cases hfresh
  | some old =>
      have hrow := requestClockQC2ReplayAppend
        time source destination x y gx gy old
        hxl hyl hlive hmarker hfree hinput hg
      rw [hrow] at hnew
      cases hnew
      refine ⟨old, rfl, ?_⟩
      exact hfresh

/-- The entire productive QC2 responder case, with arbitrary
inherited scratch: a NEW fresh ledger can only come from an
OLD fresh source, already paid by the paired advance theorem. -/
theorem requestClockFreshCarryAtResponderAdvance {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A)
    (hne : ring.rightNeighbor e ≠ e)
    (carry error tail : Bool)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hcarry : (D e).qCarry = .L carry error)
    (hfree : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hinput : (D (ring.rightNeighbor e)).qIn = .S value tail)
    (hmarker : (D (ring.rightNeighbor e)).beta = false) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e)
      (ring.rightNeighbor e) := by
  intro newLedger hnew hfresh
  have hresp := requestClockResponderGhostFrame ring D A e hne
  have hnew' :
      (digitLaneReplay .comparison (A.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison ((piD D) e)
          ((piD D) e).word.beta)
        (digitLaneView .comparison
          ((piD D) (ring.rightNeighbor e))
          ((piD D) (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison
        (A.current (ring.rightNeighbor e)).comparison).y.carry =
          some newLedger :=
    hresp.symm.trans hnew
  have hx :
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).leader = false := by
    change (D e).l = false
    exact hxl
  have hy :
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).leader =
          false := by
    change (D (ring.rightNeighbor e)).l = false
    exact hyl
  have hlive :
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta).carryLive = true := by
    change (D e).qCarry.isL = true
    rw [hcarry]
    rfl
  have hoff :
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).carryLive =
          false := by
    change (D (ring.rightNeighbor e)).qCarry.isL = false
    rw [hfree]
    rfl
  have hmark :
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).marker =
          false := by
    change (D (ring.rightNeighbor e)).beta = false
    exact hmarker
  have hsettled :
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta).input.isS =
          true := by
    change (D (ring.rightNeighbor e)).qIn.isS = true
    rw [hinput]
    rfl
  obtain ⟨old, hsource, holdFresh⟩ :=
    requestClockQC2FreshOrigin
      (A.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison ((piD D) e)
        ((piD D) e).word.beta)
      (digitLaneView .comparison
        ((piD D) (ring.rightNeighbor e))
        ((piD D) (ring.rightNeighbor e)).word.beta)
      (A.current e).comparison
      (A.current (ring.rightNeighbor e)).comparison
      hx hy hlive hmark hoff hsettled
      newLedger hnew' hfresh
  exact requestClockFreshCarryAtResponderAdvanceFresh
    ring D A e h hne carry error tail value
    hxl hyl hcarry hfree hinput hmarker
    old hsource holdFresh newLedger hnew hfresh


/-- Exhaustive OLD comparison-lane responder dispatcher.
A self-edge is the source case, since the physical and audit
definitions both prioritize the source when sites coincide.
Otherwise distinguish resident carry, nonproductive OFF and
productive QC2, with OLD roots and marker/input guards first. -/
theorem requestClockFreshCarryAtResponderEveryEdge {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : RequestClockFreshCarryInvariant ring D A) :
    RequestClockFreshCarryAt ring
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e)
      (ring.rightNeighbor e) := by
  by_cases hself : ring.rightNeighbor e = e
  · rw [hself]
    exact requestClockFreshCarryAtSourceEveryEdge ring D A e h
  · cases hcarryY : (D (ring.rightNeighbor e)).qCarry with
    | L carry error =>
        apply requestClockFreshCarryAtResponderResident
          ring D A e h hself
        rw [hcarryY]
        rfl
    | OFF =>
        by_cases hxroot : (D e).l = true
        · exact requestClockFreshCarryAtResponderNoAdvance
            ring D A e h hself hcarryY (Or.inl hxroot)
        · by_cases hyroot :
            (D (ring.rightNeighbor e)).l = true
          · exact requestClockFreshCarryAtResponderNoAdvance
              ring D A e h hself hcarryY
              (Or.inr (Or.inl hyroot))
          · have hxl : (D e).l = false := by
              cases hb : (D e).l with
              | false => rfl
              | true => exact False.elim (hxroot hb)
            have hyl :
                (D (ring.rightNeighbor e)).l = false := by
              cases hb : (D (ring.rightNeighbor e)).l with
              | false => rfl
              | true => exact False.elim (hyroot hb)
            cases hcarryX : (D e).qCarry with
            | OFF =>
                exact requestClockFreshCarryAtResponderNoAdvance
                  ring D A e h hself hcarryY
                  (Or.inr (Or.inr (Or.inl (by rw [hcarryX]; rfl))))
            | L carry error =>
                by_cases hmarker :
                    (D (ring.rightNeighbor e)).beta = true
                · exact requestClockFreshCarryAtResponderNoAdvance
                    ring D A e h hself hcarryY
                    (Or.inr (Or.inr (Or.inr (Or.inl hmarker))))
                · have hmarkerFalse :
                    (D (ring.rightNeighbor e)).beta = false := by
                    cases hb : (D (ring.rightNeighbor e)).beta with
                    | false => rfl
                    | true => exact False.elim (hmarker hb)
                  cases hinput :
                    (D (ring.rightNeighbor e)).qIn with
                  | E =>
                      exact requestClockFreshCarryAtResponderNoAdvance
                        ring D A e h hself hcarryY
                        (Or.inr (Or.inr (Or.inr (Or.inr
                          (by rw [hinput]; rfl)))))
                  | X =>
                      exact requestClockFreshCarryAtResponderNoAdvance
                        ring D A e h hself hcarryY
                        (Or.inr (Or.inr (Or.inr (Or.inr
                          (by rw [hinput]; rfl)))))
                  | P value tail =>
                      exact requestClockFreshCarryAtResponderNoAdvance
                        ring D A e h hself hcarryY
                        (Or.inr (Or.inr (Or.inr (Or.inr
                          (by rw [hinput]; rfl)))))
                  | S value tail =>
                      exact requestClockFreshCarryAtResponderAdvance
                        ring D A e h hself
                        carry error tail value
                        hxl hyl hcarryX hcarryY hinput hmarkerFalse

/-- All selected-edge endpoint rows are now discharged for the
actual physical protocol and exact ghost audit, on arbitrary
Cartesian configurations and arbitrary audit contents
satisfying the corrected fresh-carry invariant. -/
theorem requestClockFreshEndpointRows_proved {n : Nat}
    (ring : DirectedRing n) :
    RequestClockFreshEndpointRows ring := by
  intro D A e h
  exact
    ⟨requestClockFreshCarryAtSourceEveryEdge ring D A e h,
     requestClockFreshCarryAtResponderEveryEdge ring D A e h⟩

/-- Corrected QC3/QC2 carry-value and historical-use invariant
on the ENTIRE REAL audited word, without a conditional endpoint
premise; includes stutter, resident, terminal, abort and root-kill
steps and all inherited Cartesian scratch at time zero. -/
theorem requestClockFreshCarryInvariantOnRealWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    RequestClockFreshCarryInvariant ring
      (auditedRealRun ring C word).1
      (auditedRealRun ring C word).2 := by
  exact requestClockFreshCarryInvariantOnRealWordOfEndpointRows
    ring C (requestClockFreshEndpointRows_proved ring) word

end HeadlineDigit
end L3


/-!
OLD frozen-digit comparison and strict physical report bridge.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-- A successful optional list lookup names an actual list member. -/
private theorem requestClockUseMemOfGetElem {α : Type}
    (xs : List α) :
    ∀ (j : Nat) (x : α), xs[j]? = some x → x ∈ xs := by
  induction xs with
  | nil =>
      intro j x h
      cases j <;> cases h
  | cons a rest ih =>
      intro j x h
      cases j with
      | zero =>
          change some a = some x at h
          cases h
          exact List.mem_cons.mpr (Or.inl rfl)
      | succ j =>
          change rest[j]? = some x at h
          exact List.mem_cons.mpr (Or.inr (ih j x h))

/-- Optional indexing commutes with a list map. -/
private theorem requestClockMapGetElem {α β : Type}
    (f : α → β) :
    ∀ (xs : List α) (j : Nat),
      (xs.map f)[j]? = Option.map f (xs[j]?) := by
  intro xs
  induction xs with
  | nil =>
      intro j
      cases j <;> rfl
  | cons a rest ih =>
      intro j
      cases j with
      | zero => rfl
      | succ j => exact ih j

/-- Equality of lengths and all optional indexed entries determines
a list, without using Finset or a classical choice principle. -/
private theorem requestClockListExtGetElem {α : Type} :
    ∀ (xs ys : List α),
      xs.length = ys.length →
      (∀ j : Nat, j < xs.length → xs[j]? = ys[j]?) →
      xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlength _
      cases ys with
      | nil => rfl
      | cons a rest => cases hlength
  | cons a rest ih =>
      intro ys hlength hentry
      cases ys with
      | nil => cases hlength
      | cons b tail =>
          have hhead : a = b := by
            have h := hentry 0 (by simp)
            change some a = some b at h
            cases h
            rfl
          have htail : rest = tail := by
            apply ih tail
            · exact Nat.succ.inj hlength
            · intro j hj
              have h := hentry (j + 1) (by simp; omega)
              change rest[j]? = tail[j]? at h
              exact h
          rw [hhead, htail]

/-- Snoc does not disturb any earlier optional list entry. -/
private theorem requestClockSnocGetElemLeft {α : Type} :
    ∀ (xs : List α) (last : α) (j : Nat),
      j < xs.length →
      (xs ++ [last])[j]? = xs[j]? := by
  intro xs
  induction xs with
  | nil =>
      intro last j hj
      change j < 0 at hj
      omega
  | cons a rest ih =>
      intro last j hj
      cases j with
      | zero => rfl
      | succ j =>
          change (rest ++ [last])[j]? = rest[j]?
          exact ih last j (by simp at hj; omega)

/-- The newly appended entry is at the old list length. -/
private theorem requestClockSnocGetElemLast {α : Type} :
    ∀ (xs : List α) (last : α),
      (xs ++ [last])[xs.length]? = some last := by
  intro xs
  induction xs with
  | nil =>
      intro last
      rfl
  | cons a rest ih =>
      intro last
      change (rest ++ [last])[rest.length]? = some last
      exact ih last

/-- The static intended low-first digit-pair list has length k. -/
private theorem requestClockExpectedPairsLength {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) :
    ∀ k : Nat,
      (requestClockExpectedDigitPairs W s k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change
        (requestClockExpectedDigitPairs W s k ++
          [(certDigit W (certSite s k),
            certDigit W (certSite s (c.rho + k)))]).length = k + 1
      rw [List.length_append, ih]
      rfl

/-- The exact optional indexed entry of the intended digit pairs. -/
private theorem requestClockExpectedPairsGet {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) :
    ∀ (k j : Nat), j < k →
      (requestClockExpectedDigitPairs W s k)[j]? =
        some (certDigit W (certSite s j),
          certDigit W (certSite s (c.rho + j))) := by
  intro k
  induction k with
  | zero =>
      intro j hj
      omega
  | succ k ih =>
      intro j hj
      change
        (requestClockExpectedDigitPairs W s k ++
          [(certDigit W (certSite s k),
            certDigit W (certSite s (c.rho + k)))])[j]? =
        some (certDigit W (certSite s j),
          certDigit W (certSite s (c.rho + j)))
      by_cases hlt : j < k
      · have hleft := requestClockSnocGetElemLeft
          (requestClockExpectedDigitPairs W s k)
          (certDigit W (certSite s k),
            certDigit W (certSite s (c.rho + k))) j
          (by rw [requestClockExpectedPairsLength W s k]; exact hlt)
        rw [hleft]
        exact ih j hlt
      · have heq : j = k := by omega
        subst j
        have hlast := requestClockSnocGetElemLast
          (requestClockExpectedDigitPairs W s k)
          (certDigit W (certSite s k),
            certDigit W (certSite s (c.rho + k)))
        rw [requestClockExpectedPairsLength W s k] at hlast
        exact hlast

/-- An OLD-frame use records the same target digit as the frozen
entrance public word, in both QC3 birth and QC2 advance cases. -/
private theorem requestClockOldUseTargetDigitFrozen {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (use : DigitUse (compileAdvice (ceilLogTwo n)) n)
    (hfrozen : CheckerFrameDigitFrozen C A)
    (hold : RequestClockOldUseFrame ring A use) :
    use.targetDigit = certDigit (publicWord C) use.target := by
  obtain ⟨frame, hmember, _, hrow⟩ := hold
  rcases hrow with hbirth | hadvance
  · obtain ⟨htarget, _, _, _, _, hdigit⟩ := hbirth
    have hstatic := hfrozen frame hmember frame.edge
    rw [hstatic] at hdigit
    rw [htarget] at hdigit
    exact hdigit
  · obtain ⟨htarget, _, _, hdigit⟩ := hadvance
    have hstatic :=
      hfrozen frame hmember (ring.rightNeighbor frame.edge)
    rw [hstatic] at hdigit
    rw [htarget] at hdigit
    exact hdigit

/-- The terminal's NEW receipt frame is frozen from its OLD
configuration. No final-POST public freeze is needed. -/
private theorem requestClockFrozenFramesAfterTerminalEdge {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (pfx : List (Fin n)) (e : Fin n)
    (hfrozen : FrozenOnWord ring C pfx) :
    CheckerFrameDigitFrozen C
      (auditedRealRun ring C (pfx ++ [e])).2 := by
  have hprevious :=
    checkerFrameDigitFrozenOnWord ring C pfx hfrozen
  have hcurrent : ∀ i : Fin n,
      ((auditedRealRun ring C pfx).1 i).d = (C i).d := by
    intro i
    have hp := checkerAuditedRunPhysical ring C pfx
    have heq := congrArg
      (fun D : HeadlineConfiguration n => (D i).d) hp
    have hs := hfrozen pfx [] (by simp)
    exact heq.trans (hs i).2.2.2
  rw [checkerAuditedRunAppendOne ring C pfx e]
  exact checkerFrameDigitFrozenStep ring C
    (auditedRealRun ring C pfx).1
    (auditedRealRun ring C pfx).2 e hprevious hcurrent

/-- Per-use OLD frozen pairing for the actual strictly authenticated
terminal. It uses only the authentic sample receipts, the strict
ledger's ordered use slots, and the real-run OLD-use-frame invariant.
It also returns the terminal's actual final-edge receipt. -/
theorem requestClockStrictOldMatchedFrozenPairs {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (s : Fin n) (pfx : List (Fin n)) (e : Fin n)
    (hfrozen : FrozenOnWord ring C pfx)
    (hstrict : StrictCompletesAt ring C s pfx e) :
    ∃ (terminal : DigitTerminal
          (compileAdvice (ceilLogTwo n)) n)
      (ledger : DigitCarryGhost
          (compileAdvice (ceilLogTwo n)) n),
      (digitService ( (auditedRealRun ring C pfx).2.clock + 1)
        e (ring.rightNeighbor e)
        (piD (auditedRealRun ring C pfx).1 e)
        (piD (auditedRealRun ring C pfx).1
          (ring.rightNeighbor e))
        ((auditedRealRun ring C pfx).2.current e)
        ((auditedRealRun ring C pfx).2.current
          (ring.rightNeighbor e))).comparison.terminal =
            some terminal ∧
      ((auditedRealRun ring C pfx).2.current e).comparison.carry =
        some ledger ∧
      ledger.inherited = none ∧
      ledger.uses.map
        (fun use => (use.value, use.targetDigit)) =
          requestClockExpectedDigitPairs (publicWord C) s
            (compileAdvice (ceilLogTwo n)).rho := by
  obtain ⟨terminal, hfirst, htime, _, _⟩ := hstrict
  have hrecord :
      DigitRecordedTerminal
        (auditedRealRun ring C (pfx ++ [e])).2 terminal :=
    hfirst.1.2.2.1
  have hlane : terminal.lane = .comparison :=
    hfirst.1.2.2.2.1
  obtain ⟨positive, ledger, samples, exports, uses,
    hledger, hinherited, hsize, hremaining⟩ :=
    hfirst.1.2.2.2.2.2.2
  have hrecordNext :
      DigitRecordedTerminal
        (digitAuditStep ring
          (piD (auditedRealRun ring C pfx).1)
          (auditedRealRun ring C pfx).2 e) terminal := by
    rw [checkerAuditedRunAppendOne ring C pfx e] at hrecord
    exact hrecord
  have hclock := requestClockAuditClockOnWord ring C pfx
  have htimeNew :
      terminal.time = (auditedRealRun ring C pfx).2.clock + 1 := by
    rw [hclock]
    exact htime
  have hlast := requestClockLatestTerminalReceipt
    ring (piD (auditedRealRun ring C pfx).1)
    (auditedRealRun ring C pfx).2 e terminal
    (requestClockAuditFrameBoundOnWord ring C pfx)
    hrecordNext htimeNew hlane
  have hfields := requestClockReplayTerminalOldFields
    .comparison
    ((auditedRealRun ring C pfx).2.clock + 1)
    e (ring.rightNeighbor e)
    (digitLaneView .comparison
      ((piD (auditedRealRun ring C pfx).1) e)
      ((piD (auditedRealRun ring C pfx).1) e).word.beta)
    (digitLaneView .comparison
      ((piD (auditedRealRun ring C pfx).1)
        (ring.rightNeighbor e))
      ((piD (auditedRealRun ring C pfx).1)
        (ring.rightNeighbor e)).word.beta)
    ((auditedRealRun ring C pfx).2.current e).comparison
    ((auditedRealRun ring C pfx).2.current
      (ring.rightNeighbor e)).comparison
    terminal hlast
  obtain ⟨_, _, _, _, hcarry, _⟩ := hfields
  have hcurrent :
      ((auditedRealRun ring C pfx).2.current e).comparison.carry =
        some ledger := hcarry.symm.trans hledger
  have hframesOld :=
    checkerFrameDigitFrozenOnWord ring C pfx hfrozen
  have hframesFinal :=
    requestClockFrozenFramesAfterTerminalEdge
      ring C pfx e hfrozen
  obtain ⟨_, husesFrames, _⟩ :=
    requestClockFreshCarryInvariantOnRealWord ring C pfx
      e ledger hcurrent hinherited
  have hmatched :
      ledger.uses.map
        (fun use => (use.value, use.targetDigit)) =
          requestClockExpectedDigitPairs (publicWord C) s
            (compileAdvice (ceilLogTwo n)).rho := by
    apply requestClockListExtGetElem
    · rw [List.length_map, hsize]
      exact (requestClockExpectedPairsLength
        (publicWord C) s
        (compileAdvice (ceilLogTwo n)).rho).symm
    · intro j hj
      have hjlt : j < (compileAdvice (ceilLogTwo n)).rho := by
        rw [List.length_map, hsize] at hj
        exact hj
      let hjfin : Fin (compileAdvice (ceilLogTwo n)).rho :=
        ⟨j, hjlt⟩
      have hindex : (hjfin : Nat) = j := rfl
      rcases hremaining.1 hjfin with
        ⟨hsampleRecord, _, hsampleSite, _, _, _, _, _, _, _,
         _, _, huseSlot, huseTarget, _, huseValue, _, _, _, _⟩
      rw [hindex] at hsampleSite
      rw [hindex] at huseSlot
      rw [hindex] at huseTarget
      have hsourceDigit :
          (uses hjfin).value =
            certDigit (publicWord C) (certSite s j) := by
        have hsampleValue :=
          (checkerFreshSampleAtOfFrames C
            (auditedRealRun ring C (pfx ++ [e])).2
            (certSite s j) hframesFinal)
            (samples hjfin) hsampleRecord hsampleSite
        exact huseValue.trans hsampleValue
      have htargetDigit :
          (uses hjfin).targetDigit =
            certDigit (publicWord C)
              (certSite s
                ((compileAdvice (ceilLogTwo n)).rho + j)) := by
        have hmember :=
          requestClockUseMemOfGetElem ledger.uses j
            (uses hjfin) huseSlot
        have hold := husesFrames (uses hjfin) hmember
        have hvalue := requestClockOldUseTargetDigitFrozen
          ring C (auditedRealRun ring C pfx).2
          (uses hjfin) hframesOld hold
        rw [huseTarget] at hvalue
        exact hvalue
      have hmap :
          (ledger.uses.map
            (fun use => (use.value, use.targetDigit)))[j]? =
              some ((uses hjfin).value, (uses hjfin).targetDigit) := by
        calc
          (ledger.uses.map
            (fun use => (use.value, use.targetDigit)))[j]? =
              Option.map
                (fun use => (use.value, use.targetDigit))
                (ledger.uses[j]?) :=
              requestClockMapGetElem
                (fun use : DigitUse
                  (compileAdvice (ceilLogTwo n)) n =>
                  (use.value, use.targetDigit)) ledger.uses j
          _ = some ((uses hjfin).value,
                (uses hjfin).targetDigit) := by
                rw [huseSlot]
                rfl
      rw [hsourceDigit, htargetDigit] at hmap
      exact hmap.trans
        (requestClockExpectedPairsGet
          (publicWord C) s
          (compileAdvice (ceilLogTwo n)).rho j hjlt).symm
  exact ⟨terminal, ledger, hlast, hcurrent,
    hinherited, hmatched⟩

/-- A real comparison terminal receipt is impossible unless the
OLD physical source and responder are rootless, the OLD source
carry is live, and the OLD responder is a terminal. -/
private theorem requestClockReplayTerminalGuard {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (terminal : DigitTerminal c n)
    (hterminal :
      (digitLaneReplay lane time source destination
        x y gx gy).terminal = some terminal) :
    x.leader = false ∧ y.leader = false ∧
      x.carryLive = true ∧ (y.leader || y.marker) = true := by
  change
    (if !(x.leader || y.leader) && x.carryLive &&
        (y.leader || y.marker) then
      some
        ({ time := time, lane := lane, source := source,
           destination := destination, ledger := gx.carry,
           carryBit := x.carryBit, errorBit := x.carryError } :
          DigitTerminal c n)
     else none) = some terminal at hterminal
  cases hx : x.leader with
  | true =>
      simp [hx] at hterminal
  | false =>
      cases hy : y.leader with
      | true =>
          simp [hx, hy] at hterminal
      | false =>
          cases hc : x.carryLive with
          | false =>
              simp [hx, hy, hc] at hterminal
          | true =>
              cases hm : y.marker with
              | false =>
                  simp [hx, hy, hc, hm] at hterminal
              | true =>
                  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A true OLD terminal error makes the real certificateStep
TOP report true. Both OLD dirty-bit emission-first branches are
allowed; the SI-resolved writer betas do not enter qTerminal. -/
private theorem requestClockTopRejectOnTerminal (c : Compiled)
    (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hlive : x.qCarry.isL = true)
    (hterminal : (y.l || y.beta) = true)
    (herror : qcE x.qCarry = true) :
    (certificateStep c x y).2.2.topReject = true := by
  have htop : ∀ betaX betaY : Bool,
      (liveTopStep c x y betaX betaY).topReject = true := by
    intro betaX betaY
    have hmarker : y.beta = true := by
      cases hm : y.beta with
      | false =>
          simp [hy, hm] at hterminal
      | true =>
          rfl
    cases hdirtyX : x.topDirty <;>
      cases hdirtyY : y.topDirty <;>
        simp [liveTopStep, liveTopPair, topTerminal,
          hx, hy, hlive, hmarker, herror, hdirtyX, hdirtyY]
  change
    (liveTopStep c x y
      (siStep c x y (postEInfo x y)
        (serializerStep c x y (postEInfo x y)).hard).betaX
      (siStep c x y (postEInfo x y)
        (serializerStep c x y (postEInfo x y)).hard).betaY).topReject =
          true
  exact htop _ _

/-- The real OLD-prefix strict bridge, without imposing freeze
after the terminal edge. The recorded comparison is genuine, its
frozen digit pairs are the static pair, and the real TOP event
reports the arithmetic mismatch on that very OLD edge. -/
theorem strictReportBridgeOld_proved {n : Nat}
    (ring : DirectedRing n) :
    StrictReportBridgeOld ring := by
  intro C s pfx e hbad hfrozen hstrict
  obtain ⟨terminal, ledger, hlast, hcurrent, hinherited,
    hmatched⟩ :=
    requestClockStrictOldMatchedFrozenPairs
      ring C s pfx e hfrozen hstrict
  obtain ⟨_, _, hphysical⟩ :=
    requestClockFreshCarryInvariantOnRealWord ring C pfx
      e ledger hcurrent hinherited
  have hphysicalBit :
      qcE ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
        (requestClockFoldDigitUses ledger.uses (true, false)).2 := by
    have hb := congrArg qcE hphysical
    change
      qcE ((auditedRealRun ring C pfx).1 e).qCarry =
        (requestClockFoldDigitUses ledger.uses (true, false)).2 at hb
    rw [checkerAuditedRunPhysical ring C pfx] at hb
    exact hb
  have herror :=
    requestClockBadPairOldErrorOfMatchedUses ring C
      s e pfx ledger hbad hmatched hphysicalBit
  have herrorOld :
      qcE ((auditedRealRun ring C pfx).1 e).qCarry = true := by
    rw [checkerAuditedRunPhysical ring C pfx]
    exact herror
  have hguard := requestClockReplayTerminalGuard
    .comparison
    ((auditedRealRun ring C pfx).2.clock + 1)
    e (ring.rightNeighbor e)
    (digitLaneView .comparison
      ((piD (auditedRealRun ring C pfx).1) e)
      ((piD (auditedRealRun ring C pfx).1) e).word.beta)
    (digitLaneView .comparison
      ((piD (auditedRealRun ring C pfx).1)
        (ring.rightNeighbor e))
      ((piD (auditedRealRun ring C pfx).1)
        (ring.rightNeighbor e)).word.beta)
    ((auditedRealRun ring C pfx).2.current e).comparison
    ((auditedRealRun ring C pfx).2.current
      (ring.rightNeighbor e)).comparison
    terminal hlast
  have hx :
      ((auditedRealRun ring C pfx).1 e).l = false :=
    hguard.1
  have hy :
      ((auditedRealRun ring C pfx).1
        (ring.rightNeighbor e)).l = false :=
    hguard.2.1
  have hlive :
      ((auditedRealRun ring C pfx).1 e).qCarry.isL = true :=
    hguard.2.2.1
  have hterminal :
      (((auditedRealRun ring C pfx).1
        (ring.rightNeighbor e)).l ||
       ((auditedRealRun ring C pfx).1
        (ring.rightNeighbor e)).beta) = true :=
    hguard.2.2.2
  have hreport := requestClockTopRejectOnTerminal
    (compileAdvice (ceilLogTwo n))
    ((auditedRealRun ring C pfx).1 e)
    ((auditedRealRun ring C pfx).1
      (ring.rightNeighbor e))
    hx hy hlive hterminal herrorOld
  rw [checkerAuditedRunPhysical ring C pfx] at hreport
  exact hreport

end HeadlineDigit
end L3
