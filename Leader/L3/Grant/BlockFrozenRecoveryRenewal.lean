import Leader.L3.Grant.BlockFrozenRenewal
import Leader.L3.Grant.BlockFrozenRenewalCost
import Leader.L3.Bank.TrialRecovery

/-!
# G16: C.2 recovery on the frozen chain

The frozen kernel is the clamped local reference; from an unlatched RESET
reference its stopped cost to a latched or Clean reference is bounded by
the local recovery occupation potential of `BankTrialRecovery.lean`
(applied at the state `<S, recovery>`), after the root lease of a RESET
root, which the dynamics never reads, is normalised to zero.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open GrantBankReference

set_option autoImplicit false
set_option Elab.async false

/-- The root BANK row from a RESET root: the lease of the RESET root is
overwritten, so it does not enter the output.

Consumer: `grantBlockFrozenRecoveryPairNorm`. -/
theorem grantBlockFrozenRecoveryPairReset (x y : BankCell) (p b : Nat) (theta : Nat → Bool)
    (hp : p = 1) (hx : x.role = 0) (hm : x.mode = .RESET) (hg : x.grant = false)
    (hy : y.role = 1) :
    bankPair x y p b theta =
      ({ x with tok := .E, mode := .RWAIT, lease := 13 * (b + 2) },
       { y with mode := .RESET, lease := 0, bit := false, tok := .RR }) := by
  subst hp
  simp [bankPair, hx, hm, hg, hy]

/-- Normal form of a reference whose root is RESET: the root lease is
zeroed (a RESET root's lease is irrelevant to the dynamics).

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
noncomputable def grantBlockFrozenRecoveryNorm {q : Nat}
    (S : BankLocalReference (compileAdvice q).b) :
    BankLocalReference (compileAdvice q).b where
  fields := fun i =>
    if i.val = 0 ∧ (S.fields i).1 = .RESET then
      ((S.fields i).1, (S.fields i).2.1, (S.fields i).2.2.1, 0)
    else S.fields i
  success := S.success

/-- Cells of the normal form.

Consumer: `grantBlockFrozenRecoveryPairNorm`. -/
theorem grantBlockFrozenRecoveryCellNorm {q : Nat} (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET) (j : Fin ((compileAdvice q).b + 1)) :
    bankLocalReferenceCell (grantBlockFrozenRecoveryNorm S) j =
      if j.val = 0 then { bankLocalReferenceCell S j with lease := 0 }
      else bankLocalReferenceCell S j := by
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := Fin.ext hj
    subst hj0
    simp [grantBlockFrozenRecoveryNorm, bankLocalReferenceCell, hm]
  · have hne : j ≠ 0 := fun h => hj (by rw [h]; rfl)
    simp [grantBlockFrozenRecoveryNorm, bankLocalReferenceCell, hj, hne]

/-- Internal BANK rows do not see the root lease of a RESET root.

Consumer: `grantBlockFrozenRecoveryFieldStep`. -/
theorem grantBlockFrozenRecoveryPairNorm {q : Nat} (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET)
    (j : Fin (compileAdvice q).b) :
    bankLocalReferenceInternalPair q (grantBlockFrozenRecoveryNorm S) j =
      bankLocalReferenceInternalPair q S j := by
  have hb : 11 ≤ (compileAdvice q).b := by
    change 11 ≤ (compileAdvice q).s + 11
    omega
  unfold bankLocalReferenceInternalPair
  have h1 := grantBlockFrozenRecoveryCellNorm S hm ⟨j.val, by omega⟩
  have h2 := grantBlockFrozenRecoveryCellNorm S hm ⟨j.val + 1, by omega⟩
  by_cases hj : j.val = 0
  · have hz : (⟨j.val, by omega⟩ : Fin ((compileAdvice q).b + 1)) = 0 :=
      Fin.ext hj
    have hone : (⟨j.val + 1, by omega⟩ : Fin ((compileAdvice q).b + 1)).val
        ≠ 0 := by simp
    rw [if_neg hone] at h2
    rw [if_pos hj] at h1
    rw [h1, h2]
    have hx : (bankLocalReferenceCell S ⟨j.val, by omega⟩).role = 0 := by
      simp [bankLocalReferenceCell, hj]
    have hmode : (bankLocalReferenceCell S ⟨j.val, by omega⟩).mode = .RESET := by
      simp only [bankLocalReferenceCell]
      rw [hz]; exact hm
    have hy : (bankLocalReferenceCell S ⟨j.val + 1, by omega⟩).role = 1 := by
      simp [bankLocalReferenceCell, hj]
    have hpost : j.val + 1 = 1 := by omega
    rw [grantBlockFrozenRecoveryPairReset _ _ _ _ _ hpost hx hmode
      (by simp [bankLocalReferenceCell]) hy]
    rw [grantBlockFrozenRecoveryPairReset { bankLocalReferenceCell S ⟨j.val, by omega⟩ with lease := 0 } _ _ _ _ hpost
      (by simpa using hx) (by simpa using hmode) (by simp [bankLocalReferenceCell]) hy]
  · have hne : (⟨j.val, by omega⟩ : Fin ((compileAdvice q).b + 1)).val ≠ 0 := hj
    have hone : (⟨j.val + 1, by omega⟩ : Fin ((compileAdvice q).b + 1)).val
        ≠ 0 := by simp
    rw [if_neg hne] at h1
    rw [if_neg hone] at h2
    rw [h1, h2]


/-- A RESET root serviced by its outgoing row becomes RWAIT.

Consumer: `grantBlockFrozenRecoveryFieldStep`. -/
theorem grantBlockFrozenRecoveryPairRootMode {q : Nat} (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET)
    (j : Fin (compileAdvice q).b) (hj : j.val = 0) :
    (bankLocalReferenceClampedQuad q
      (bankLocalReferenceInternalPair q S j).1).1 = .RWAIT := by
  have hb : 11 ≤ (compileAdvice q).b := by
    change 11 ≤ (compileAdvice q).s + 11
    omega
  unfold bankLocalReferenceInternalPair
  have hz : (⟨j.val, by omega⟩ : Fin ((compileAdvice q).b + 1)) = 0 :=
    Fin.ext hj
  have hx : (bankLocalReferenceCell S ⟨j.val, by omega⟩).role = 0 := by
    simp [bankLocalReferenceCell, hj]
  have hmode : (bankLocalReferenceCell S ⟨j.val, by omega⟩).mode = .RESET := by
    simp only [bankLocalReferenceCell]
    rw [hz]; exact hm
  have hy : (bankLocalReferenceCell S ⟨j.val + 1, by omega⟩).role = 1 := by
    simp [bankLocalReferenceCell, hj]
  have hpost : j.val + 1 = 1 := by omega
  rw [grantBlockFrozenRecoveryPairReset _ _ _ _ _ hpost hx hmode
    (by simp [bankLocalReferenceCell]) hy]
  simp [bankLocalReferenceClampedQuad, bankAgentLeaseQuad, copyBank]

/-- The clamped field step commutes with the normal form on a RESET
root.

Consumer: `grantBlockFrozenRecoveryStepNorm`. -/
theorem grantBlockFrozenRecoveryFieldStep {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET)
    (i : Fin ((compileAdvice q).b + 1)) :
    bankLocalReferenceFieldStepClamped ring root e (grantBlockFrozenRecoveryNorm S) i =
      if i.val = 0 ∧
          (bankLocalReferenceFieldStepClamped ring root e S i).1 = .RESET
      then ((bankLocalReferenceFieldStepClamped ring root e S i).1,
        (bankLocalReferenceFieldStepClamped ring root e S i).2.1,
        (bankLocalReferenceFieldStepClamped ring root e S i).2.2.1, 0)
      else bankLocalReferenceFieldStepClamped ring root e S i := by
  have hb : 11 ≤ (compileAdvice q).b := by
    change 11 ≤ (compileAdvice q).s + 11
    omega
  by_cases c1 : i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val
  · have hP := grantBlockFrozenRecoveryPairNorm S hm ⟨i.val, c1.1⟩
    unfold bankLocalReferenceFieldStepClamped
    rw [dif_pos c1, dif_pos c1, hP]
    by_cases hi : i.val = 0
    · have hmr := grantBlockFrozenRecoveryPairRootMode S hm ⟨i.val, c1.1⟩ hi
      rw [if_neg (by simp [hmr])]
    · rw [if_neg (by simp [hi])]
  · by_cases c2 : 0 < i.val ∧ e = Counter.site ring root (i.val - 1)
    · have hP := grantBlockFrozenRecoveryPairNorm S hm ⟨i.val - 1, by omega⟩
      unfold bankLocalReferenceFieldStepClamped
      rw [dif_neg c1, dif_neg c1, dif_pos c2, dif_pos c2, hP]
      rw [if_neg (fun h => by have h1 := h.1; have := c2.1; omega)]
    · by_cases c3 : i.val = (compileAdvice q).b ∧
          e = Counter.site ring root (compileAdvice q).b
      · have hcell := grantBlockFrozenRecoveryCellNorm S hm i
        rw [if_neg (by omega)] at hcell
        unfold bankLocalReferenceFieldStepClamped
        rw [dif_neg c1, dif_neg c1, dif_neg c2, dif_neg c2,
          dif_pos c3, dif_pos c3, hcell]
        rw [if_neg (fun h => by have h1 := h.1; have := c3.1; omega)]
      · by_cases c4 : i.val = 0 ∧ ring.rightNeighbor e = root
        · have hcell := grantBlockFrozenRecoveryCellNorm S hm i
          rw [if_pos c4.1] at hcell
          have hi0 : i = 0 := Fin.ext c4.1
          unfold bankLocalReferenceFieldStepClamped
          rw [dif_neg c1, dif_neg c1, dif_neg c2, dif_neg c2,
            dif_neg c3, dif_neg c3, dif_pos c4, dif_pos c4, hcell]
          have hmode : (bankLocalReferenceCell S i).mode = .RESET := by
            simp only [bankLocalReferenceCell]
            rw [hi0]; exact hm
          rw [if_pos (by
            simp [incomingRootBankMap, isWaitMode, hmode,
              bankLocalReferenceClampedQuad, bankAgentLeaseQuad, copyBank,
              c4.1])]
          simp [incomingRootBankMap, isWaitMode, hmode,
            bankLocalReferenceClampedQuad, bankAgentLeaseQuad, copyBank]
        · unfold bankLocalReferenceFieldStepClamped
          rw [dif_neg c1, dif_neg c1, dif_neg c2, dif_neg c2,
            dif_neg c3, dif_neg c3, dif_neg c4, dif_neg c4]
          by_cases hi : i.val = 0
          · have hi0 : i = 0 := Fin.ext hi
            subst hi0
            simp [grantBlockFrozenRecoveryNorm, hm]
          · have hne : i ≠ 0 := fun h => hi (by rw [h]; rfl)
            simp [grantBlockFrozenRecoveryNorm, hi, hne]



/-- A RESET root cannot fire the BANK success event.

Consumer: `grantBlockFrozenRecoveryStepNorm`. -/
theorem grantBlockFrozenRecoveryEventReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET) :
    bankLocalReferenceSuccessEvent ring root S e = false := by
  have hb : 11 ≤ (compileAdvice q).b := by
    change 11 ≤ (compileAdvice q).s + 11
    omega
  have hmz : (S.fields ⟨0, by omega⟩).1 = .RESET := hm
  unfold bankLocalReferenceSuccessEvent
  split
  · change bankSuccess (bankLocalReferenceCell S ⟨0, by omega⟩)
      (bankLocalReferenceCell S ⟨1, by omega⟩) 1 (compileAdvice q).b = false
    simp [bankSuccess, bankLocalReferenceCell]
    intro h
    exact absurd (hm.symm.trans h) (by decide)
  · rfl

/-- The normal form keeps a RESET root.

Consumer: `grantBlockFrozenRecoveryStepNorm`. -/
theorem grantBlockFrozenRecoveryNormMode {q : Nat}
    (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET) :
    ((grantBlockFrozenRecoveryNorm S).fields 0).1 = .RESET := by
  simp [grantBlockFrozenRecoveryNorm, hm]

/-- The clamped step commutes with the normal form on a RESET root.

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
theorem grantBlockFrozenRecoveryStepNorm {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET) :
    bankLocalReferenceStepClamped ring root
        (grantBlockFrozenRecoveryNorm S) e =
      grantBlockFrozenRecoveryNorm
        (bankLocalReferenceStepClamped ring root S e) := by
  have hm' := grantBlockFrozenRecoveryNormMode S hm
  by_cases hs : Counter.Support q ring root e
  · by_cases hsucc : S.success = true
    · have hsn : (grantBlockFrozenRecoveryNorm S).success = true := hsucc
      simp [bankLocalReferenceStepClamped, hs, hsucc, hsn]
    · have hsn : (grantBlockFrozenRecoveryNorm S).success = false := by
        have : S.success = false := by simpa using hsucc
        simpa [grantBlockFrozenRecoveryNorm] using this
      have hsf : S.success = false := by simpa using hsucc
      have e1 := grantBlockFrozenRecoveryEventReset ring root e S hm
      have e2 := grantBlockFrozenRecoveryEventReset ring root e
        (grantBlockFrozenRecoveryNorm S) hm'
      unfold bankLocalReferenceStepClamped
      rw [dif_pos hs, dif_pos hs, if_neg (by simp [hsn]),
        if_neg (by simp [hsucc])]
      rw [e2, e1]
      simp only [grantBlockFrozenRecoveryNorm]
      congr 1
      funext i
      have h := grantBlockFrozenRecoveryFieldStep ring root e S hm i
      simpa [grantBlockFrozenRecoveryNorm] using h
  · simp [bankLocalReferenceStepClamped, hs]

/-- A RESET unlatched reference stays unlatched.

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
theorem grantBlockFrozenRecoveryStepUnlatched {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : BankLocalReference (compileAdvice q).b)
    (hm : (S.fields 0).1 = .RESET) (hs : S.success = false) :
    (bankLocalReferenceStepClamped ring root S e).success = false := by
  have e1 := grantBlockFrozenRecoveryEventReset ring root e S hm
  unfold bankLocalReferenceStepClamped
  by_cases h : Counter.Support q ring root e
  · rw [dif_pos h, if_neg (by simp [hs])]
    simp [hs, e1]
  · rw [dif_neg h]; exact hs


/-- The normal form does nothing off a RESET root.

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
theorem grantBlockFrozenRecoveryNormId {q : Nat}
    (S : BankLocalReference (compileAdvice q).b)
    (hm : ¬ (S.fields 0).1 = .RESET) :
    grantBlockFrozenRecoveryNorm S = S := by
  obtain ⟨f, s⟩ := S
  simp only [grantBlockFrozenRecoveryNorm]
  congr 1
  funext i
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this
    simp [hm]
  · have hne : i ≠ 0 := fun h => hi (by rw [h]; rfl)
    simp [hi, hne]

/-- The frozen chain as a plain step function on references.

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
noncomputable def grantBlockFrozenRecoveryNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBlockFrozenRef n) (e : Fin n) : GrantBlockFrozenRef n :=
  bankLocalReferenceStepClamped ring root S e

/-- Terminal references: latched or Clean.

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
def grantBlockFrozenRecoveryTerm {n : Nat}
    (S : GrantBlockFrozenRef n) : Prop :=
  S.success = true ∨ BankTrialLocalClean (ceilLogTwo n) S

/-- An unlatched RESET reference is not terminal.

Consumer: `grantBlockFrozenRecoveryCostEqNorm`. -/
theorem grantBlockFrozenRecoveryResetLive {n : Nat}
    (S : GrantBlockFrozenRef n)
    (hs : S.success = false) (hm : (S.fields 0).1 = .RESET) :
    ¬ grantBlockFrozenRecoveryTerm S := by
  rintro (h | h)
  · rw [hs] at h; cases h
  · have hc : (S.fields ⟨0, by omega⟩).1 = .ARMED := h.2.1
    have : (S.fields ⟨0, by omega⟩).1 = .RESET := hm
    rw [this] at hc; cases hc

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
/-- The stopped cost of an unlatched RESET reference equals that of its
normal form.

Consumer: `grantBlockFrozenRecoveryCostOfWindow`. -/
theorem grantBlockFrozenRecoveryCostEqNorm {n : Nat} (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (T : Nat) (S : GrantBlockFrozenRef n), S.success = false →
      (S.fields 0).1 = .RESET →
      costNumerator (grantBlockFrozenRecoveryNext ring root)
          grantBlockFrozenRecoveryTerm S T =
        costNumerator (grantBlockFrozenRecoveryNext ring root)
          grantBlockFrozenRecoveryTerm
          (grantBlockFrozenRecoveryNorm S) T := by
  intro T
  induction T with
  | zero => intro S _ _; simp only [costNumerator_zero]
  | succ T ih =>
      intro S hs hm
      have hm' := grantBlockFrozenRecoveryNormMode S hm
      have hs' : (grantBlockFrozenRecoveryNorm S).success = false := hs
      rw [costNumerator_succ _ _ S
          (grantBlockFrozenRecoveryResetLive S hs hm) T,
        costNumerator_succ _ _ (grantBlockFrozenRecoveryNorm S)
          (grantBlockFrozenRecoveryResetLive _ hs' hm') T]
      congr 1
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext e
      have hstep := grantBlockFrozenRecoveryStepNorm ring root e S hm
      have hun := grantBlockFrozenRecoveryStepUnlatched ring root e S hm hs
      change costNumerator (grantBlockFrozenRecoveryNext ring root)
          grantBlockFrozenRecoveryTerm
          (bankLocalReferenceStepClamped ring root S e) T =
        costNumerator (grantBlockFrozenRecoveryNext ring root)
          grantBlockFrozenRecoveryTerm
          (bankLocalReferenceStepClamped ring root
            (grantBlockFrozenRecoveryNorm S) e) T
      rw [hstep]
      by_cases hr : ((bankLocalReferenceStepClamped ring root S e).fields
          0).1 = .RESET
      · exact ih _ hun hr
      · rw [grantBlockFrozenRecoveryNormId _ hr]


/-- One local trial step from the recovery phase, in terms of the frozen
step: the bank moves by the clamped step and the phase is won, lost
(Clean) or still recovering.

Consumer: `grantBlockFrozenRecoveryDrift`. -/
theorem grantBlockFrozenRecoveryLocalNext {n : Nat} (ring : DirectedRing n)
    (root e : Fin n) (S : GrantBlockFrozenRef n) :
    bankTrialLocalNext ring root
        (⟨S, .recovery⟩ : BankTrialLocalState (ceilLogTwo n)) e =
      if (grantBlockFrozenRecoveryNext ring root S e).success = true then
        ⟨grantBlockFrozenRecoveryNext ring root S e, .won⟩
      else if BankTrialLocalClean (ceilLogTwo n)
          (grantBlockFrozenRecoveryNext ring root S e) then
        ⟨grantBlockFrozenRecoveryNext ring root S e, .lost⟩
      else ⟨grantBlockFrozenRecoveryNext ring root S e, .recovery⟩ := by
  unfold bankTrialLocalNext grantBlockFrozenRecoveryNext
  simp

/-- The local trial machine stops exactly at terminal frozen references.

Consumer: `grantBlockFrozenRecoveryDrift`. -/
theorem grantBlockFrozenRecoveryLocalTerminal {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (S : GrantBlockFrozenRef n) :
    bankTrialLocalTerminal (bankTrialLocalNext ring root
        (⟨S, .recovery⟩ : BankTrialLocalState (ceilLogTwo n)) e) ↔
      grantBlockFrozenRecoveryTerm (grantBlockFrozenRecoveryNext ring root S e) := by
  rw [grantBlockFrozenRecoveryLocalNext]
  unfold grantBlockFrozenRecoveryTerm bankTrialLocalTerminal
  by_cases h1 : (grantBlockFrozenRecoveryNext ring root S e).success = true
  · simp [h1]
  · by_cases h2 : BankTrialLocalClean (ceilLogTwo n)
        (grantBlockFrozenRecoveryNext ring root S e)
    · simp [h1, h2]
    · simp [h1, h2]

/-- A nonterminal frozen step is a recovering local step.

Consumer: `grantBlockFrozenRecoveryDrift`. -/
theorem grantBlockFrozenRecoveryLocalLive {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (S : GrantBlockFrozenRef n)
    (h : ¬ grantBlockFrozenRecoveryTerm
      (grantBlockFrozenRecoveryNext ring root S e)) :
    bankTrialLocalNext ring root
        (⟨S, .recovery⟩ : BankTrialLocalState (ceilLogTwo n)) e =
      ⟨grantBlockFrozenRecoveryNext ring root S e, .recovery⟩ := by
  rw [grantBlockFrozenRecoveryLocalNext]
  unfold grantBlockFrozenRecoveryTerm at h
  have h1 : ¬ (grantBlockFrozenRecoveryNext ring root S e).success = true :=
    fun hh => h (Or.inl hh)
  have h2 : ¬ BankTrialLocalClean (ceilLogTwo n)
      (grantBlockFrozenRecoveryNext ring root S e) :=
    fun hh => h (Or.inr hh)
  simp [h1, h2]

/-- The local recovery state of a reference.

Consumer: `grantBlockFrozenRecoveryDrift`. -/
abbrev grantBlockFrozenRecoveryState {n : Nat} (S : GrantBlockFrozenRef n) :
    BankTrialLocalState (ceilLogTwo n) := ⟨S, .recovery⟩

/-- Potential of the frozen recovery: the local occupation potential at
the recovery state of the reference, zero on terminal references. -/
noncomputable def grantBlockFrozenRecoveryPotential {n : Nat}
    (S : GrantBlockFrozenRef n) : Nat :=
  if grantBlockFrozenRecoveryTerm S then 0
  else bankTrialDurationRecoveryTwinOccupation n
    (⟨S, .recovery⟩ : BankTrialLocalState (ceilLogTwo n))

/-- Recovery fronts, plus terminal references.

Consumer: `grantBlockFrozenRecoveryTwiceCost`. -/
def grantBlockFrozenRecoveryInv {n : Nat} (S : GrantBlockFrozenRef n) :
    Prop :=
  grantBlockFrozenRecoveryTerm S ∨
    BankTrialDurationRecoveryFront (ceilLogTwo n)
      (⟨S, .recovery⟩ : BankTrialLocalState (ceilLogTwo n))

/-- The reachable-recovery Bellman inequality on the frozen chain, from
the front rows, the port sum and the clock Bellman inequality, none of
which needs a Clean seed.

Consumer: `grantBlockFrozenRecoveryTwiceCost`. -/
theorem grantBlockFrozenRecoveryDrift {n : Nat} (ring : DirectedRing n)
    (root : Fin n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (S : GrantBlockFrozenRef n)
    (hf : BankTrialDurationRecoveryFront (ceilLogTwo n)
      (⟨S, .recovery⟩ : BankTrialLocalState (ceilLogTwo n)))
    (hnot : ¬ grantBlockFrozenRecoveryTerm S) :
    (grantBlockFrozenRecoveryInv S ∧ True) ∧
    (∀ e : Fin n, grantBlockFrozenRecoveryInv
      (grantBlockFrozenRecoveryNext ring root S e)) ∧
    2 * n + (List.ofFn (fun e : Fin n =>
        grantBlockFrozenRecoveryPotential
          (grantBlockFrozenRecoveryNext ring root S e))).sum ≤
      n * grantBlockFrozenRecoveryPotential S := by
  classical
  have hrows := bankTrialDurationRecoveryAllRowsNonalias ring root hsmall hw
  have hzn : ¬ bankTrialLocalTerminal (grantBlockFrozenRecoveryState S) := by
    intro h
    rcases h with h | h <;> cases h
  refine ⟨⟨Or.inr hf, trivial⟩, ?_, ?_⟩
  · intro e
    by_cases ht : grantBlockFrozenRecoveryTerm
        (grantBlockFrozenRecoveryNext ring root S e)
    · exact Or.inl ht
    · right
      have hlive := grantBlockFrozenRecoveryLocalLive ring root e S ht
      rcases (hrows (grantBlockFrozenRecoveryState S) e hf).1 with htl | hfn
      · exact absurd ((grantBlockFrozenRecoveryLocalTerminal ring root e S).mp htl) ht
      · rw [hlive] at hfn
        exact hfn
  · have hchild (e : Fin n) :
        grantBlockFrozenRecoveryPotential
            (grantBlockFrozenRecoveryNext ring root S e) =
          bankTrialDurationRecoveryTwinPotential
            (compileAdvice (ceilLogTwo n)).b n
            (bankTrialDurationRecoveryClockNext
              (compileAdvice (ceilLogTwo n)).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root (grantBlockFrozenRecoveryState S))
              e (bankTrialDurationRecoveryClockOf (grantBlockFrozenRecoveryState S))) := by
      have hrow := hrows (grantBlockFrozenRecoveryState S) e hf
      by_cases ht : grantBlockFrozenRecoveryTerm
          (grantBlockFrozenRecoveryNext ring root S e)
      · have htl := (grantBlockFrozenRecoveryLocalTerminal ring root e S).mpr ht
        have hocc : bankTrialDurationRecoveryTwinOccupation n
            (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e) =
            bankTrialDurationRecoveryTwinPotential (compileAdvice (ceilLogTwo n)).b n
              (bankTrialDurationRecoveryClockOf
                (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e)) := by
          unfold bankTrialDurationRecoveryTwinOccupation
          have hc : bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e) = .done := by
            unfold bankTrialDurationRecoveryClockOf
            simp only [if_pos htl]
          rw [hc]
          simp only [if_pos htl, bankTrialDurationRecoveryTwinPotential]
        have hpot : grantBlockFrozenRecoveryPotential
            (grantBlockFrozenRecoveryNext ring root S e) = 0 := by
          simp [grantBlockFrozenRecoveryPotential, ht]
        have hz0 : bankTrialDurationRecoveryTwinOccupation n
            (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e) = 0 := by
          unfold bankTrialDurationRecoveryTwinOccupation
          simp only [if_pos htl]
        rw [hpot, ← congrArg
          (bankTrialDurationRecoveryTwinPotential
            (compileAdvice (ceilLogTwo n)).b n) hrow.2, ← hocc, hz0]
      · have hlive := grantBlockFrozenRecoveryLocalLive ring root e S ht
        have hfn : BankTrialDurationRecoveryFront (ceilLogTwo n)
            (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e) := by
          rcases hrow.1 with htl | hfn
          · exact absurd ((grantBlockFrozenRecoveryLocalTerminal ring root e S).mp htl) ht
          · exact hfn
        have hocc := bankTrialDurationRecoveryTwinOccupationFront
          (n := n) (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e) hfn
        have hpot : grantBlockFrozenRecoveryPotential
            (grantBlockFrozenRecoveryNext ring root S e) =
            bankTrialDurationRecoveryTwinOccupation n
              (bankTrialLocalNext ring root (grantBlockFrozenRecoveryState S) e) := by
          rw [hlive]
          simp [grantBlockFrozenRecoveryPotential, ht]
        rw [hpot, hocc]
        exact congrArg
          (bankTrialDurationRecoveryTwinPotential
            (compileAdvice (ceilLogTwo n)).b n) hrow.2
    have hsum := FiniteUniformStoppingTree.ofFn_sum_eq
      (fun e : Fin n => grantBlockFrozenRecoveryPotential
        (grantBlockFrozenRecoveryNext ring root S e))
      (fun e : Fin n =>
        bankTrialDurationRecoveryTwinPotential
          (compileAdvice (ceilLogTwo n)).b n
          (bankTrialDurationRecoveryClockNext
            (compileAdvice (ceilLogTwo n)).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root (grantBlockFrozenRecoveryState S))
            e (bankTrialDurationRecoveryClockOf (grantBlockFrozenRecoveryState S)))) hchild
    have hports := bankTrialDurationRecoveryTwinPortSumHolds ring root hw (grantBlockFrozenRecoveryState S) hf
    have hbellman := bankTrialDurationRecoveryTwinFrontBellman ring root hw (grantBlockFrozenRecoveryState S) hf
    have hpotS : grantBlockFrozenRecoveryPotential S =
        bankTrialDurationRecoveryTwinPotential
          (compileAdvice (ceilLogTwo n)).b n
          (bankTrialDurationRecoveryClockOf (grantBlockFrozenRecoveryState S)) := by
      simp only [grantBlockFrozenRecoveryPotential, if_neg hnot]
      exact bankTrialDurationRecoveryTwinOccupationFront (grantBlockFrozenRecoveryState S) hf
    rw [hsum, hpotS]
    exact Nat.le_trans (Nat.add_le_add_left hports _) hbellman


/-- Bellman induction with doubled cost: a potential with the drift
`2 n + sum <= n * potential` on a closed class bounds twice the stopped
cost.

Consumer: `grantBlockFrozenRecoveryFrontCost`. -/
theorem grantBlockFrozenRecoveryTwiceCost {X : Type} {n : Nat}
    (next : X → Fin n → X) (Term I : X → Prop) (Φ : X → Nat)
    (hclosed : ∀ x, I x → ¬ Term x → ∀ e : Fin n, I (next x e))
    (hdrift : ∀ x, I x → ¬ Term x →
      2 * n + (List.ofFn (fun e : Fin n => Φ (next x e))).sum ≤
        n * Φ x) :
    ∀ (T : Nat) (x : X), I x →
      2 * costNumerator next Term x T ≤ n ^ T * Φ x := by
  intro T
  induction T with
  | zero => intro x _; simp only [costNumerator_zero, Nat.mul_zero]; exact Nat.zero_le _
  | succ T ih =>
      intro x hx
      by_cases ht : Term x
      · rw [costNumerator_terminal next Term x ht (T + 1)]
        simp
      · rw [costNumerator_succ next Term x ht T]
        have hs := ofFn_sum_le
          (fun e : Fin n => 2 * costNumerator next Term (next x e) T)
          (fun e : Fin n => n ^ T * Φ (next x e))
          (fun e => ih (next x e) (hclosed x hx ht e))
        rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hs
        calc
          2 * (n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
              costNumerator next Term (next x e) T)).sum) =
              2 * n ^ (T + 1) + 2 * (List.ofFn (fun e : Fin n =>
                costNumerator next Term (next x e) T)).sum := by
            rw [Nat.mul_add]
          _ ≤ 2 * n ^ (T + 1) + n ^ T * (List.ofFn (fun e : Fin n =>
              Φ (next x e))).sum := Nat.add_le_add_left hs _
          _ = n ^ T * (2 * n + (List.ofFn (fun e : Fin n =>
              Φ (next x e))).sum) := by
            rw [Nat.mul_add, Nat.pow_succ]
            ac_rfl
          _ ≤ n ^ T * (n * Φ x) := Nat.mul_le_mul_left _ (hdrift x hx ht)
          _ = n ^ (T + 1) * Φ x := by
            rw [Nat.pow_succ]; ac_rfl

/-- The stopped cost of the frozen chain from a RESET recovery front is
at most `(4 b + 6) n`: the local recovery budget of `BankTrialRecovery`
on the frozen chain itself.

Consumer: `grantBlockFrozenRecoveryCostOfWindow`. -/
theorem grantBlockFrozenRecoveryFrontCost {n : Nat} (ring : DirectedRing n)
    (root : Fin n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (S : GrantBlockFrozenRef n)
    (hf : BankTrialDurationRecoveryFront (ceilLogTwo n)
      (grantBlockFrozenRecoveryState S))
    (hm : (S.fields 0).1 = .RESET) (T : Nat) :
    costNumerator (grantBlockFrozenRecoveryNext ring root)
        grantBlockFrozenRecoveryTerm S T ≤
      n ^ T * (((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n)) := by
  have hmain := grantBlockFrozenRecoveryTwiceCost
    (grantBlockFrozenRecoveryNext ring root) grantBlockFrozenRecoveryTerm
    grantBlockFrozenRecoveryInv grantBlockFrozenRecoveryPotential
    (by
      intro x hx hnt e
      have hf' : BankTrialDurationRecoveryFront (ceilLogTwo n)
          (grantBlockFrozenRecoveryState x) :=
        hx.resolve_left hnt
      exact (grantBlockFrozenRecoveryDrift ring root hsmall hw x hf' hnt).2.1 e)
    (by
      intro x hx hnt
      have hf' : BankTrialDurationRecoveryFront (ceilLogTwo n)
          (grantBlockFrozenRecoveryState x) :=
        hx.resolve_left hnt
      exact (grantBlockFrozenRecoveryDrift ring root hsmall hw x hf' hnt).2.2)
    T S (Or.inr hf)
  have hnt : ¬ grantBlockFrozenRecoveryTerm S := by
    refine grantBlockFrozenRecoveryResetLive S ?_ hm
    exact hf.2.2.1
  have hpot : grantBlockFrozenRecoveryPotential S =
      n * (8 * (compileAdvice (ceilLogTwo n)).b) := by
    simp only [grantBlockFrozenRecoveryPotential, if_neg hnt]
    rw [bankTrialDurationRecoveryTwinOccupationFront _ hf,
      bankTrialDurationRecoveryClockResetOfFront _ hf hm]
    rfl
  rw [hpot] at hmain
  have h8 : n ^ T * (n * (8 * (compileAdvice (ceilLogTwo n)).b)) =
      2 * (n ^ T * (((4 * (compileAdvice (ceilLogTwo n)).b) * n))) := by
    have : 8 * (compileAdvice (ceilLogTwo n)).b =
        2 * (4 * (compileAdvice (ceilLogTwo n)).b) := by omega
    rw [this]; ac_rfl
  rw [h8] at hmain
  have hle := Nat.le_of_mul_le_mul_left hmain (by decide : 0 < 2)
  exact Nat.le_trans hle (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right n (by omega)))


/-- Every reference reached from the member's start has leases within
the compiled cap.

Consumer: `grantBlockFrozenRecoveryCostOfWindow`. -/
theorem grantBlockFrozenReachedLeaseCap {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (S : GrantBlockFrozenRef n)
    (hS : GrantBlockFrozenReached ring member S) :
    BankTrialLocalLeaseCap (ceilLogTwo n) S := by
  obtain ⟨w, hw⟩ := hS
  have hb : GrantBlockFrozenColdLeaseBound (ceilLogTwo n) S := by
    rw [hw]
    exact grantBlockFrozenColdLeaseBoundWord ring member.1 w _
      (grantBlockFrozenColdLeaseBoundStart ring member.2.val member.1)
  intro j hj
  have := hb ⟨j, Nat.lt_succ_of_le hj⟩
  omega

/-- The C.2 recovery cost of the frozen chain, for every family member:
from every reached unlatched RESET reference the stopped cost to a latched
or Clean reference is at most `n ^ T * ((4 b + 6) n)`.  The reference
need not be a seed-reachable recovery front: a RESET root lease is
normalised away and the digit scratch is arbitrary.

Consumer: `grantBlockFrozenLocalColdClockOfBuffered`. -/
theorem grantBlockFrozenRecoveryCostOfWindow {n : Nat}
    (ring : DirectedRing n) (member : GrantBlockFamilyMember ring)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n)) :
    GrantBlockFrozenRecoveryCost ring member := by
  intro S hS hs hm T
  have hterm : (grantBlockFrozenKernel ring member).Terminal =
      grantBlockFrozenRecoveryTerm := by
    funext R
    apply propext
    unfold GrantBlockFrozenKernel.Terminal grantBlockFrozenKernel
      grantBlockFrozenRecoveryTerm
    by_cases h1 : R.success = true
    · simp [h1]
    · by_cases h2 : BankTrialLocalClean (ceilLogTwo n) R <;> simp [h1, h2]
  rw [hterm]
  change costNumerator (grantBlockFrozenRecoveryNext ring member.1)
      grantBlockFrozenRecoveryTerm S T ≤ _
  rw [grantBlockFrozenRecoveryCostEqNorm ring member.1 T S hs hm]
  have hcap := grantBlockFrozenReachedLeaseCap ring member S hS
  have hm' := grantBlockFrozenRecoveryNormMode S hm
  apply grantBlockFrozenRecoveryFrontCost ring member.1 hsmall hw _ _ hm'
  refine ⟨rfl, ?_, ?_, Or.inl ⟨hm', ?_⟩⟩
  · intro j hj
    by_cases h0 : j = 0
    · subst h0
      simp [grantBlockFrozenRecoveryNorm, hm]
    · have hne : (⟨j, Nat.lt_succ_of_le hj⟩ :
          Fin ((compileAdvice (ceilLogTwo n)).b + 1)) ≠ 0 := by
        intro h
        exact h0 (congrArg Fin.val h)
      have := hcap j hj
      simp [grantBlockFrozenRecoveryNorm, hne, this]
  · exact hs
  · simp [grantBlockFrozenRecoveryNorm, hm]


/-- The frozen local cold clock for a buffered member, with the C.2
recovery cost proved: C.3 from the canonical frozen Bellman inequality,
C.2 from the local recovery occupation potential on the frozen chain, the
renewal window from the G13 chain run on the frozen kernel.

Consumer: `grantBlockFrozenDirectMarginalOfLocalClock`. -/
theorem grantBlockFrozenLocalColdClockOfBuffered
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (radius : Nat)
    (hbuffered : HeadlineGrantBufferedCounter ring member.2.val radius
      member.1)
    (R L T W : Nat) :
    GrantBlockFrozenLocalColdClock ring member R L T W := by
  intro hn hsp hw hlarge hradius hW hL hWT hbudget
  exact (grantBlockFrozenLocalColdClockOfRecovery ring member radius
    hbuffered (grantBlockFrozenRecoveryCostOfWindow ring member hsp hw)
    R L T W) hn hsp hw hlarge hradius hW hL hWT hbudget

end L3
#print axioms L3.grantBlockFrozenRecoveryStepNorm
#print axioms L3.grantBlockFrozenRecoveryCostEqNorm
#print axioms L3.grantBlockFrozenRecoveryDrift
#print axioms L3.grantBlockFrozenRecoveryFrontCost
#print axioms L3.grantBlockFrozenRecoveryCostOfWindow
#print axioms L3.grantBlockFrozenLocalColdClockOfBuffered
