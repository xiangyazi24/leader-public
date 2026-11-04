import Leader.L3.Bank.TrialCompare
import Leader.L3.Bank.TrialDuration
import Leader.L3.Bank.CounterTrialLower

/-!
G11c, paper Appendix C (spatial-counter.tex on main), C.5: the completed-head
soundness of the K-head comparison. The seven-field invariant
`BankTrialC5CompletedHeadInvariant` (BankTrialCompare.lean) was checked
inductive by exhaustive enumeration on the b = 3, K = 3 and b = 4, K = 6
projections: 0 breaking (state, edge) pairs over all states satisfying it.
What remains is the one-edge row table `BankTrialC5RemainingLiveRows`
(exact carry, strict ARMED bound, CR0 and CL0 negative provenance).
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A fixed original-clock service of the four OPEN C.5 fields. -/
def BankTrialC5RemainingRowAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (heads : Nat) (e : Fin n) : Prop :=
  BankTrialC5CompletedHeadInvariant q z heads →
  ∀ nextBegun : Bool,
    (bankTrialLocalNext ring root z e).phase = .live nextBegun →
    (bankTrialLiveCarryValue
        (bankTrialLocalNext ring root z e).bank =
      heads +
        (if BankTrialProbabilityArmedGate z ∧ e = root then 1 else 0)) ∧
    (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .ARMED →
      heads +
        (if BankTrialProbabilityArmedGate z ∧ e = root then 1 else 0) <
        (compileAdvice q).K) ∧
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root z e).bank j = .CR0 →
      ∃ i : Fin (compileAdvice q).b,
        i.val ≤ j.val ∧
        bankTrialLiveWaveBit
          (bankTrialLocalNext ring root z e).bank i ≠
          (compileAdvice q).theta i.val) ∧
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root z e).bank j = .CL0 →
      bankTrialLiveBinaryValue
        (bankTrialLocalNext ring root z e).bank ≠
        bankTrialLiveThetaBinary q)

/-- If an edge frames every protected bit/token and root mode, all
four difficult C.5 fields are inherited, including CR0/CL0
negative provenance.  This is a *proved* transport rule, not
the as-yet-missing proof that every selected edge frames. -/
theorem bankTrialC5RemainingFramedRows {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q) (heads : Nat)
    (hzero : ¬ (BankTrialProbabilityArmedGate z ∧ e = root))
    (hbits : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit (bankTrialLocalNext ring root z e).bank i =
        bankTrialLiveWaveBit z.bank i)
    (htokens : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken (bankTrialLocalNext ring root z e).bank i =
        bankTrialLiveWaveToken z.bank i)
    (hmode : bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank =
      bankTrialLiveWaveRootMode z.bank) :
    BankTrialC5RemainingRowAt ring root z heads e := by
  intro hInv nextBegun hnext
  obtain ⟨oldBegun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root e z nextBegun hnext
  have hcarry :
      bankTrialLiveCarryValue (bankTrialLocalNext ring root z e).bank =
        bankTrialLiveCarryValue z.bank := by
    unfold bankTrialLiveCarryValue
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro i
    change bankTrialLiveSlotPotential i.val
      (bankTrialLiveWaveBit (bankTrialLocalNext ring root z e).bank i)
      (bankTrialLiveWaveToken (bankTrialLocalNext ring root z e).bank i) =
      bankTrialLiveSlotPotential i.val
        (bankTrialLiveWaveBit z.bank i)
        (bankTrialLiveWaveToken z.bank i)
    rw [hbits i, htokens i]
  have hbinary :=
    bankTrialCmpBinaryCongr
      (bankTrialLocalNext ring root z e).bank z.bank hbits
  simp only [if_neg hzero, Nat.add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hcarry.trans (hInv.liveCarry oldBegun hlive)
  · intro armed
    rw [hmode] at armed
    exact hInv.armedStrict oldBegun hlive armed
  · intro j htok
    rw [htokens j] at htok
    obtain ⟨i, hi, hbad⟩ :=
      hInv.crZeroWitness oldBegun hlive j htok
    refine ⟨i, hi, ?_⟩
    rw [hbits i]
    exact hbad
  · intro j htok
    rw [htokens j] at htok
    have hbad := hInv.clZeroWitness oldBegun hlive j htok
    rw [hbinary]
    exact hbad

/-- Outside-support case: all four fields hold, not just carry.
Uses hlarge to obtain nonalias; hwidth is not needed. -/
theorem bankTrialC5RemainingOutsideRows {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (z : BankTrialLocalState q) (heads : Nat)
    (hout : ¬ Counter.Support q ring root e) :
    BankTrialC5RemainingRowAt ring root z heads e := by
  intro hInv nextBegun hnext
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have h := bankTrialC5CompletedHeadOutsideNext
    ring root e hw z heads hInv hout
  exact ⟨h.liveCarry nextBegun hnext,
    h.armedStrict nextBegun hnext,
    h.crZeroWitness nextBegun hnext,
    h.clZeroWitness nextBegun hnext⟩

/-- Terminal predecessor classes: a LIVE successor is impossible.
No quantitative width or nonalias assumption is used here. -/
theorem bankTrialC5RemainingTerminalRows {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q) (heads : Nat)
    (ht : bankTrialLocalTerminal z) :
    BankTrialC5RemainingRowAt ring root z heads e := by
  intro hInv nextBegun hnext
  obtain ⟨oldBegun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root e z nextBegun hnext
  rcases ht with hw | hl
  · rw [hw] at hlive
    cases hlive
  · rw [hl] at hlive
    cases hlive

/-- Actual outgoing-root LIVE successor: exact all-digit carry.
Uses hlarge (nonalias), but does not use hwidth.
The strict ARMED and mismatch rows are separate obligations. -/
theorem bankTrialC5RemainingRootCarry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z root).phase =
      .live nextBegun) :
    bankTrialLiveCarryValue
        (bankTrialLocalNext ring root z root).bank =
      heads +
        (if BankTrialProbabilityArmedGate z ∧ root = root
         then 1 else 0) := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root root z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) root).phase =
        .live nextBegun := by
    rw [hz] at hnext
    exact hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root z.bank begun nextBegun hcanonical
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hroot := bankTrialC5RootCarryExact ring root hw z.bank
    hf (hInv.locked.1 begun hlive)
    (hInv.locked.2 begun hlive)
    (hInv.noRWAIT begun hlive)
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hz]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  have hindicator :
      (if bankTrialLiveWaveRootMode z.bank = .ARMED then 1 else 0) =
        (if BankTrialProbabilityArmedGate z ∧ root = root
         then 1 else 0) := by
    by_cases hm : bankTrialLiveWaveRootMode z.bank = .ARMED
    · have hg : BankTrialProbabilityArmedGate z :=
        ⟨⟨begun, hlive⟩, hm⟩
      rw [if_pos hm, if_pos (show
        BankTrialProbabilityArmedGate z ∧ root = root from ⟨hg, rfl⟩)]
    · have hng : ¬ (BankTrialProbabilityArmedGate z ∧ root = root) := by
        intro h
        exact hm h.1.2
      rw [if_neg hm, if_neg hng]
  rw [hbank, hroot, hInv.liveCarry begun hlive, hindicator]

/-- The TOP-erasure hazard is impossible in every LIVE predecessor
of a LIVE top successor, because its IR credit is at least 2^b.
Uses hwidth; hlarge is not used in this source exclusion. -/
theorem bankTrialC5RemainingTopNoIR {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z e).phase =
      .live nextBegun) :
    bankTrialLiveWaveToken z.bank
      ⟨(compileAdvice q).b - 1,
        by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root e z nextBegun hnext
  exact bankTrialC5NoTopIRInLive z heads hwidth hInv begun hlive

/-- A genuine selected interior CR0/E step moves CR0 one slot
right and carries its failed-prefix ancestor with it.
This is for the *clamped* BANK reference, not just raw bankPair.
Only nonalias (hlarge -> hw) is needed, not hwidth. -/
theorem bankTrialC5RemainingInteriorCRZeroWitness {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 =
      .CR0)
    (hdst : (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 =
      .E)
    (hWitness : ∃ i : Fin (compileAdvice q).b,
      i.val ≤ j.val - 1 ∧
      bankTrialLiveWaveBit B i ≠ (compileAdvice q).theta i.val) :
    bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) j = .CR0 ∧
      (∃ i : Fin (compileAdvice q).b, i.val ≤ j.val ∧
        bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) i ≠
          (compileAdvice q).theta i.val) := by
  have hcmp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  have hp := bankTrialInteriorCRZeroForward
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hsrc hdst
  have hsourceBit :
      (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit =
        (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.1 :=
    hp.2.1
  have hnewToken :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) j = .CR0 := by
    calc
      bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) j =
        (GrantBankReference.bankLocalReferenceInternalPair q B
          j).2.tok := ((hcmp.2.2 j).2.1 rfl).2
      _ = .CR0 := hp.2.2.1
  have hprefix :
      ∀ i : Fin (compileAdvice q).b,
        i.val ≤ j.val - 1 →
        bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) i =
          bankTrialLiveWaveBit B i := by
    intro i hi
    by_cases hs : i.val + 1 = j.val
    · have hindex :
          (⟨i.val + 1, by have hh := i.isLt; omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val, by have hh := j.isLt; omega⟩ :=
        Fin.ext hs
      calc
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) i =
          (GrantBankReference.bankLocalReferenceInternalPair q B
            j).1.bit := ((hcmp.2.2 i).1 hs).1
        _ = (B.fields
            ⟨j.val, by have hh := j.isLt; omega⟩).2.1 :=
          hsourceBit
        _ = bankTrialLiveWaveBit B i := by
          change (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.1 =
            (B.fields ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.1
          rw [hindex]
    · have ht : i.val ≠ j.val := by omega
      exact ((hcmp.2.2 i).2.2 hs ht).1
  refine ⟨hnewToken, ?_⟩
  exact bankTrialC5CRZeroWitnessPrefixFrame
    B
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    ⟨j.val - 1, by have hh := j.isLt; omega⟩ j
    (by change j.val - 1 ≤ j.val; omega) hWitness hprefix

/-- The selected interior E/CL0 return takes CL0 one slot
left and preserves every protected digit bit. Hence the
full-binary mismatch cannot disappear when the worker moves. -/
theorem bankTrialC5RemainingInteriorCLZeroWitness {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 =
      .E)
    (hdst : (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 =
      .CL0)
    (hMismatch :
      bankTrialLiveBinaryValue B ≠ bankTrialLiveThetaBinary q) :
    bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val))
      ⟨j.val - 1, by have hh := j.isLt; omega⟩ = .CL0 ∧
    bankTrialLiveBinaryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) ≠
        bankTrialLiveThetaBinary q := by
  have hcmp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  have hp := bankTrialInteriorCLZeroReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hsrc hdst
  have hsourceBit :
      (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit =
        (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.1 :=
    hp.2.1
  have htargetBit :
      (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit =
        (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.1 :=
    hp.2.2.2
  have hnewToken :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val))
        ⟨j.val - 1, by have hh := j.isLt; omega⟩ = .CL0 := by
    have hi : j.val - 1 + 1 = j.val := by omega
    calc
      bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val))
          ⟨j.val - 1, by have hh := j.isLt; omega⟩ =
        (GrantBankReference.bankLocalReferenceInternalPair q B
          j).1.tok :=
        ((hcmp.2.2 ⟨j.val - 1, by have hh := j.isLt; omega⟩).1 hi).2
      _ = .CL0 := hp.1
  have hbits :
      ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) i =
          bankTrialLiveWaveBit B i := by
    intro i
    by_cases hs : i.val + 1 = j.val
    · have hindex :
          (⟨i.val + 1, by have hh := i.isLt; omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val, by have hh := j.isLt; omega⟩ :=
        Fin.ext hs
      calc
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) i =
          (GrantBankReference.bankLocalReferenceInternalPair q B
            j).1.bit := ((hcmp.2.2 i).1 hs).1
        _ = (B.fields
            ⟨j.val, by have hh := j.isLt; omega⟩).2.1 :=
          hsourceBit
        _ = bankTrialLiveWaveBit B i := by
          change (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.1 =
            (B.fields ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.1
          rw [hindex]
    · by_cases ht : i.val = j.val
      · have hindex :
            (⟨i.val + 1, by have hh := i.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨j.val + 1, by have hh := j.isLt; omega⟩ :=
          Fin.ext (show i.val + 1 = j.val + 1 by omega)
        calc
          bankTrialLiveWaveBit
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B (Counter.site ring root j.val)) i =
            (GrantBankReference.bankLocalReferenceInternalPair q B
              j).2.bit := ((hcmp.2.2 i).2.1 ht).1
          _ = (B.fields
              ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.1 :=
            htargetBit
          _ = bankTrialLiveWaveBit B i := by
            change (B.fields
              ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.1 =
              (B.fields
                ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.1
            rw [hindex]
      · exact ((hcmp.2.2 i).2.2 hs ht).1
  refine ⟨hnewToken, ?_⟩
  exact bankTrialC5CLZeroWitnessBitFrame
    B
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    hbits hMismatch


end L3



namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The available public C.5 theorem covers q >= 3;
the remaining closed advice indices have only thirteen digits. -/
theorem bankTrialC5ThetaOfWidth (q : Nat)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    bankTrialLiveThetaBinary q = (compileAdvice q).K := by
  by_cases hq : 3 ≤ q
  · exact bankTrialProbabilityThetaBinaryEqualsK q hq
  · have hsmall : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hsmall with hz | ho | ht
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide

/-- Every non-IR token has zero carry credit.
Comparison workers CR/CL and increment ACK AL are allowed. -/
theorem bankTrialC5CarryBinaryWithoutIR {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hnoIR : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j ≠ .IR) :
    bankTrialLiveCarryValue B = bankTrialLiveBinaryValue B := by
  unfold bankTrialLiveCarryValue bankTrialLiveBinaryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  change bankTrialLiveSlotPotential j.val
      (bankTrialLiveWaveBit B j) (bankTrialLiveWaveToken B j) =
    (if bankTrialLiveWaveBit B j then 2 ^ j.val else 0)
  simp [bankTrialLiveSlotPotential, hnoIR j]

/-- The missing root CL0-to-ARMED strictness has a pure
invariant proof once the OLD root is CWAIT and CL0 exists.
CWAIT forbids IR credit; the CL0 witness makes binary != K. -/
theorem bankTrialC5CWaitCLZeroStrict {q : Nat}
    (z : BankTrialLocalState q) (heads : Nat)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (begun : Bool) (hlive : z.phase = .live begun)
    (hcwait : bankTrialLiveWaveRootMode z.bank = .CWAIT)
    (hCL : ∃ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .CL0) :
    heads < (compileAdvice q).K := by
  have hcert : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  have hnoIR : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j ≠ .IR := by
    intro j
    exact (bankTrialLiveWaveCWaitNoWriters
      z.bank hcert hcwait j).1
  have hcarry := bankTrialC5CarryBinaryWithoutIR z.bank hnoIR
  have hheads := hInv.liveCarry begun hlive
  have hbound := hInv.liveBound begun hlive
  obtain ⟨j, hj⟩ := hCL
  have hMismatch := hInv.clZeroWitness begun hlive j hj
  have htheta := bankTrialC5ThetaOfWidth q hwidth
  omega

/-- On a nonaliased incoming-root letter no digit slot is
selected, even when nonroot Mode/lease scratch is arbitrary.
This directly uses the original clamped BANK reference. -/
theorem bankTrialC5IncomingDigitFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hin : ring.rightNeighbor e = root)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveBit
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) j = bankTrialLiveWaveBit B j ∧
    bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) j = bankTrialLiveWaveToken B j := by
  have hj := j.isLt
  have hsource :
      ¬ (j.val + 1 < (compileAdvice q).b ∧
        e = Counter.site ring root (j.val + 1)) := by
    intro h
    have hsite : Counter.site ring root (j.val + 2) =
        Counter.site ring root 0 := by
      have hh := hin
      rw [h.2] at hh
      exact hh
    have hd := bankTrialWindowSitesDistinct
      ring root hw (j.val + 2) 0 (by omega) (by omega) hsite
    omega
  have htarget :
      ¬ (0 < j.val + 1 ∧
        e = Counter.site ring root (j.val + 1 - 1)) := by
    intro h
    have hpred : j.val + 1 - 1 = j.val := by omega
    have hsite : Counter.site ring root (j.val + 1) =
        Counter.site ring root 0 := by
      have hh := hin
      rw [h.2, hpred] at hh
      exact hh
    have hd := bankTrialWindowSitesDistinct
      ring root hw (j.val + 1) 0 (by omega) (by omega) hsite
    omega
  have htop :
      ¬ (j.val + 1 = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hsite : Counter.site ring root ((compileAdvice q).b + 1) =
        Counter.site ring root 0 := by
      have hh := hin
      rw [h.2] at hh
      exact hh
    have hd := bankTrialWindowSitesDistinct
      ring root hw ((compileAdvice q).b + 1) 0
      (by omega) (by omega) hsite
    omega
  have hnoIncoming :
      ¬ (j.val + 1 = 0 ∧ ring.rightNeighbor e = root) := by
    intro h
    omega
  have hfield := bankTrialLiveCarryUnselectedField
    ring root e B (Or.inl hin) hf
    (⟨j.val + 1, show j.val + 1 < (compileAdvice q).b + 1 by omega⟩)
    hsource htarget htop hnoIncoming
  exact ⟨congrArg (fun v : Mode × Bool × BTok × Nat => v.2.1)
    hfield,
    congrArg (fun v : Mode × Bool × BTok × Nat => v.2.2.1)
    hfield⟩

/-- A root-incoming scheduler letter cannot also be root
outgoing under the nonalias hypothesis. -/
theorem bankTrialC5IncomingNotRoot {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root) :
    e ≠ root := by
  intro he
  have hsite : Counter.site ring root 1 =
      Counter.site ring root 0 := by
    have hh := hin
    rw [he] at hh
    exact hh
  have hd := bankTrialWindowSitesDistinct
    ring root hw 1 0 (by omega) (by omega) hsite
  omega

/-- Reproduce the public part of the incoming unary raw
case table: the root mode is retained or changes to RESET. -/
theorem bankTrialC5IncomingRawModeCases (x : BankCell) :
    (GrantBankReference.incomingRootBankMap x).mode = x.mode ∨
    (GrantBankReference.incomingRootBankMap x).mode = .RESET := by
  cases hm : x.mode <;>
    simp [GrantBankReference.incomingRootBankMap,
      hm, isWaitMode] <;>
    (repeat' split) <;> simp

/-- For an incoming-root LIVE-to-LIVE step, the absorbing
RESET alternative cannot occur. The remaining root mode frames. -/
theorem bankTrialC5IncomingRootModeFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hlock : BankTrialLiveNoResetLocked
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hin : ring.rightNeighbor e = root)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
    bankTrialLiveWaveRootMode B := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root e B begun nextBegun hnext
  have hnroot := bankTrialC5IncomingNotRoot ring root e hw hin
  have hnextlock := bankTrialWindowIncomingRows ring root
    e hin hw B begun hlock nextBegun hnext
  have hnreset :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ≠ .RESET := by
    have hh := hnextlock.2 nextBegun hnext
    rw [bankTrialLocalNextLiveBank ring root e B begun] at hh
    exact hh
  have hsource :
      ¬ (0 < (compileAdvice q).b ∧
        e = Counter.site ring root 0) := by
    intro h
    exact hnroot (by simpa only [Counter.site] using h.2)
  have htarget :
      ¬ (0 < (0 : Nat) ∧
        e = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have htop :
      ¬ ((0 : Nat) = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hb := bankTrialCmpWidth q
    omega
  have hroot :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) =
        (GrantBankReference.incomingRootBankMap
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by omega⟩)).mode := by
    have hs : Counter.Support q ring root e := Or.inl hin
    have hr := (bankTrialLocalStepField ring root e B hs hf
      ⟨0, by omega⟩).trans
      (bankTrialLocalSelectedIncoming ring root e B
        ⟨0, by omega⟩ hsource htarget htop ⟨rfl, hin⟩)
    exact congrArg
      (fun v : Mode × Bool × BTok × Nat => v.1) hr
  have hcases := bankTrialC5IncomingRawModeCases
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
  rw [bankTrialLocalNextLiveBank ring root e B begun]
  rcases hcases with hkeep | hreset
  · exact hroot.trans hkeep
  · exact False.elim (hnreset (hroot.trans hreset))

/-- Incoming-root closes all four rows of the pinned
specification: it frames every digit and preserves root mode
on LIVE continuations. Uses hlarge, not hwidth. -/
theorem bankTrialC5RemainingIncomingRows {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (z : BankTrialLocalState q) (heads : Nat)
    (hin : ring.rightNeighbor e = root) :
    BankTrialC5RemainingRowAt ring root z heads e := by
  intro hInv nextBegun hnext
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root e z nextBegun hnext
  cases z with
  | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      have hw : BankTrialLiveWindowNonalias n q :=
        bankTrialProbabilityUpperWindow hlarge
      have hf := bankTrialWindowLiveOldNotLatched
        ring root e B begun nextBegun hnext
      have hbank := bankTrialLocalNextLiveBank
        ring root e B begun
      have hnroot := bankTrialC5IncomingNotRoot ring root e hw hin
      have hzero :
          ¬ (BankTrialProbabilityArmedGate
            (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
            e = root) := by
        intro h
        exact hnroot h.2
      have hbits :
          ∀ i : Fin (compileAdvice q).b,
            bankTrialLiveWaveBit
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank i =
              bankTrialLiveWaveBit B i := by
        intro i
        rw [hbank]
        exact (bankTrialC5IncomingDigitFrame
          ring root e hw B hf hin i).1
      have htokens :
          ∀ i : Fin (compileAdvice q).b,
            bankTrialLiveWaveToken
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank i =
              bankTrialLiveWaveToken B i := by
        intro i
        rw [hbank]
        exact (bankTrialC5IncomingDigitFrame
          ring root e hw B hf hin i).2
      have hmode := bankTrialC5IncomingRootModeFrame ring root e
        hw B begun nextBegun hInv.locked hin hnext
      exact (bankTrialC5RemainingFramedRows ring root e
        (⟨B, .live begun⟩ : BankTrialLocalState q) heads
        hzero hbits htokens hmode) hInv nextBegun hnext

/-- Strict ARMED inequality for every proper interior
LIVE-to-LIVE service: root Mode frames, and no head is paid.
Uses nonalias, not hwidth. -/
theorem bankTrialC5RemainingInteriorArmedStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z
      (Counter.site ring root j.val)).phase = .live nextBegun) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)).bank = .ARMED →
    heads +
      (if BankTrialProbabilityArmedGate z ∧
          Counter.site ring root j.val = root then 1 else 0) <
        (compileAdvice q).K := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root
      (Counter.site ring root j.val) z nextBegun hnext
  cases z with
  | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      have hnotroot :=
        bankTrialWindowInteriorNotRoot ring root hw j hj
      have hzero :
          ¬ (BankTrialProbabilityArmedGate
             (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
             Counter.site ring root j.val = root) := by
        intro h
        exact hnotroot h.2
      have hf := bankTrialWindowLiveOldNotLatched ring root
        (Counter.site ring root j.val) B begun nextBegun hnext
      have hbank := bankTrialLocalNextLiveBank
        ring root (Counter.site ring root j.val) B begun
      have hm := bankTrialWindowInteriorRootModeFrame
        ring root hw B hf j hj
      intro hnewArmed
      rw [if_neg hzero, Nat.add_zero]
      rw [hbank, hm] at hnewArmed
      exact hInv.armedStrict begun rfl hnewArmed


/-- The top unary service is a full protected digit frame when the
old highest worker is not IR. This is the physical clamped selector,
not merely the raw topBoundaryBankMap projection. -/
theorem bankTrialC5TopWholeBitTokenModeFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hnoIR : bankTrialLiveWaveToken B
      ⟨(compileAdvice q).b - 1,
        by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR) :
    (∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (compileAdvice q).b)) i =
        bankTrialLiveWaveBit B i ∧
      bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (compileAdvice q).b)) i =
        bankTrialLiveWaveToken B i) ∧
    bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root (compileAdvice q).b)) =
      bankTrialLiveWaveRootMode B := by
  have hb := bankTrialCmpWidth q
  have hs : Counter.Support q ring root
      (Counter.site ring root (compileAdvice q).b) :=
    Or.inr ⟨(compileAdvice q).b, Nat.le_refl _, rfl⟩
  constructor
  · intro i
    by_cases ht : i.val + 1 = (compileAdvice q).b
    · have hsource :
          ¬ (i.val + 1 < (compileAdvice q).b ∧
            Counter.site ring root (compileAdvice q).b =
              Counter.site ring root (i.val + 1)) := by
        intro h
        omega
      have htarget :
          ¬ (0 < i.val + 1 ∧
            Counter.site ring root (compileAdvice q).b =
              Counter.site ring root (i.val + 1 - 1)) := by
        intro h
        have hd := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b (i.val + 1 - 1)
          (by omega) (by omega) h.2
        omega
      have hslot :
          (⟨i.val + 1, by have hh := i.isLt; omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨(compileAdvice q).b - 1 + 1,
            by have hb := bankTrialCmpWidth q; omega⟩ := by
          apply Fin.ext
          have hlast : (compileAdvice q).b - 1 + 1 =
              (compileAdvice q).b := by omega
          exact ht.trans hlast.symm
      have hcellIR :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨i.val + 1, by have hh := i.isLt; omega⟩).tok ≠ .IR := by
        change (B.fields
          ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.2.1 ≠ .IR
        rw [hslot]
        exact hnoIR
      have hselected := bankTrialLiveCarryTopSelected ring root
        (Counter.site ring root (compileAdvice q).b)
        B hs hf
        ⟨i.val + 1, by have hh := i.isLt; omega⟩
        hsource htarget ⟨ht, rfl⟩
      have hmap := bankTrialC5TopBitTokenFrame q
        (GrantBankReference.bankLocalReferenceCell B
          ⟨i.val + 1, by have hh := i.isLt; omega⟩)
        hcellIR
      constructor
      · change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (compileAdvice q).b)).fields
              ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.1 =
          (B.fields ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.1
        rw [hselected]
        exact hmap.1
      · change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (compileAdvice q).b)).fields
              ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.2.1 =
          (B.fields ⟨i.val + 1, by have hh := i.isLt; omega⟩).2.2.1
        rw [hselected]
        exact hmap.2
    · have hsource :
          ¬ (i.val + 1 < (compileAdvice q).b ∧
            Counter.site ring root (compileAdvice q).b =
              Counter.site ring root (i.val + 1)) := by
        intro h
        have hd := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b (i.val + 1)
          (by omega) (by omega) h.2
        exact ht hd.symm
      have htarget :
          ¬ (0 < i.val + 1 ∧
            Counter.site ring root (compileAdvice q).b =
              Counter.site ring root (i.val + 1 - 1)) := by
        intro h
        have hd := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b (i.val + 1 - 1)
          (by omega) (by omega) h.2
        have hi := i.isLt
        omega
      have htop :
          ¬ (i.val + 1 = (compileAdvice q).b ∧
            Counter.site ring root (compileAdvice q).b =
              Counter.site ring root (compileAdvice q).b) := by
        intro h
        exact ht h.1
      have hin :
          ¬ (i.val + 1 = 0 ∧
            ring.rightNeighbor
              (Counter.site ring root (compileAdvice q).b) = root) := by
        intro h
        omega
      have hfield := bankTrialLiveCarryUnselectedField ring root
        (Counter.site ring root (compileAdvice q).b)
        B hs hf
        ⟨i.val + 1, by have hh := i.isLt; omega⟩
        hsource htarget htop hin
      exact ⟨congrArg (fun v : Mode × Bool × BTok × Nat => v.2.1)
        hfield,
        congrArg (fun v : Mode × Bool × BTok × Nat => v.2.2.1)
        hfield⟩
  · have hsource :
        ¬ ((0 : Nat) < (compileAdvice q).b ∧
          Counter.site ring root (compileAdvice q).b =
            Counter.site ring root 0) := by
      intro h
      have hd := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b 0 (by omega) (by omega) h.2
      omega
    have htarget :
        ¬ (0 < (0 : Nat) ∧
          Counter.site ring root (compileAdvice q).b =
            Counter.site ring root (0 - 1)) := by
      intro h
      omega
    have htop :
        ¬ ((0 : Nat) = (compileAdvice q).b ∧
          Counter.site ring root (compileAdvice q).b =
            Counter.site ring root (compileAdvice q).b) := by
      intro h
      omega
    have hin :
        ¬ ((0 : Nat) = 0 ∧
          ring.rightNeighbor
            (Counter.site ring root (compileAdvice q).b) = root) := by
      intro h
      have he : Counter.site ring root ((compileAdvice q).b + 1) =
          Counter.site ring root 0 := h.2
      have hd := bankTrialWindowSitesDistinct ring root hw
        ((compileAdvice q).b + 1) 0
        (by omega) (by omega) he
      omega
    have hfield := bankTrialLiveCarryUnselectedField ring root
      (Counter.site ring root (compileAdvice q).b)
      B hs hf ⟨0, by omega⟩
      hsource htarget htop hin
    exact congrArg (fun v : Mode × Bool × BTok × Nat => v.1)
      hfield

/-- The entire top edge-class row follows from the bounded
top-IR exclusion and the all-digit physical frame. -/
theorem bankTrialC5RemainingTopFramedRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (z : BankTrialLocalState q) (heads : Nat) :
    BankTrialC5RemainingRowAt ring root z heads
      (Counter.site ring root (compileAdvice q).b) := by
  intro hInv nextBegun hnext
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root
      (Counter.site ring root (compileAdvice q).b) z nextBegun hnext
  cases z with
  | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      have hw : BankTrialLiveWindowNonalias n q :=
        bankTrialProbabilityUpperWindow hlarge
      have hnotroot :
          Counter.site ring root (compileAdvice q).b ≠ root := by
        intro he
        have hd := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b 0 (by omega) (by omega) he
        have hb := bankTrialCmpWidth q
        omega
      have hzero :
          ¬ (BankTrialProbabilityArmedGate
            (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
            Counter.site ring root (compileAdvice q).b = root) := by
        intro h
        exact hnotroot h.2
      have hf := bankTrialWindowLiveOldNotLatched ring root
        (Counter.site ring root (compileAdvice q).b)
        B begun nextBegun hnext
      have hnoIR := bankTrialC5NoTopIRInLive
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        heads hwidth hInv begun rfl
      have hframe := bankTrialC5TopWholeBitTokenModeFrame
        ring root hw B hf hnoIR
      have hbank := bankTrialLocalNextLiveBank ring root
        (Counter.site ring root (compileAdvice q).b) B begun
      have hbits :
          ∀ i : Fin (compileAdvice q).b,
            bankTrialLiveWaveBit
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q)
                (Counter.site ring root (compileAdvice q).b)).bank i =
              bankTrialLiveWaveBit B i := by
        intro i
        rw [hbank]
        exact (hframe.1 i).1
      have htokens :
          ∀ i : Fin (compileAdvice q).b,
            bankTrialLiveWaveToken
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q)
                (Counter.site ring root (compileAdvice q).b)).bank i =
              bankTrialLiveWaveToken B i := by
        intro i
        rw [hbank]
        exact (hframe.1 i).2
      have hmode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q)
              (Counter.site ring root (compileAdvice q).b)).bank =
          bankTrialLiveWaveRootMode B := by
        rw [hbank]
        exact hframe.2
      exact (bankTrialC5RemainingFramedRows ring root
        (Counter.site ring root (compileAdvice q).b)
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        heads hzero hbits htokens hmode) hInv nextBegun hnext



/-- On a grant-free root owner with the LIVE head-clear palette,
a newly ARMED output can only be the CWAIT/CL0 return.
The forbidden RWAIT/RL reset-completion origin is excluded. -/
theorem bankTrialC5RawRootNewArmedOnlyCLZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) →
      y.tok = .E)
    (hnew : (bankPair x y 1 b theta).1.mode = .ARMED) :
    x.mode = .CWAIT ∧ y.tok = .CL0 := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET =>
      exact False.elim (hnr hm)
  | RWAIT =>
      exact False.elim (hnw hm)
  | ARMED =>
      have ht := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CSTART =>
      have ht := hhead (Or.inr hm)
      simp [bankPair, hx, hy, hg, hm, ht,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew
  | IWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
          simp [bankPair, hx, hy, hg, hm, ht, hl,
            hbpos, hbne, isRetTok, isWaitMode,
            Id.run_pure, Id.run_bind] at hnew
  | CWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
          simp [bankPair, hx, hy, hg, hm, ht, hl,
            hbpos, hbne, isRetTok, isWaitMode,
            Id.run_pure, Id.run_bind] at hnew ⊢

/-- The selected root's newly-ARMED strict inequality:
a fresh ARMED here is necessarily an unpaid CL0 return.
This discharges the strictness row, not the CR0/CL0 witness rows. -/
theorem bankTrialC5RemainingRootArmedStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z root).phase =
      .live nextBegun) :
    bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z root).bank = .ARMED →
      heads +
        (if BankTrialProbabilityArmedGate z ∧ root = root
         then 1 else 0) < (compileAdvice q).K := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive
      ring root root z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) root).phase =
        .live nextBegun := by
    rw [hz] at hnext
    exact hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root z.bank begun nextBegun hcanonical
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hz]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  have hhead :
      ((GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .ARMED ∨
       (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .CSTART) →
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .E := by
    intro hm
    exact hc.headClear ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hm
  intro hnew
  rw [hbank] at hnew
  have hproj := bankTrialCmpRoot ring root hw z.bank hf
  have hrawnew :
      (GrantBankReference.bankLocalReferenceInternalPair q z.bank
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).1.mode = .ARMED :=
    hproj.1.symm.trans hnew
  have hraw := bankTrialC5RawRootNewArmedOnlyCLZero
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
    (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
    (by have hb := bankTrialCmpWidth q; omega)
    rfl rfl rfl
    (hInv.locked.2 begun hlive)
    (hInv.noRWAIT begun hlive)
    hhead hrawnew
  have hcwait :
      bankTrialLiveWaveRootMode z.bank = .CWAIT := hraw.1
  have hCL :
      ∃ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j = .CL0 :=
    ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩, hraw.2⟩
  have hstrict :=
    bankTrialC5CWaitCLZeroStrict
      z heads hwidth hInv begun hlive hcwait hCL
  have hnotgate :
      ¬ (BankTrialProbabilityArmedGate z ∧ root = root) := by
    intro h
    have hArmed := h.1.2
    change bankTrialLiveWaveRootMode z.bank = .ARMED at hArmed
    rw [hcwait] at hArmed
    cases hArmed
  rw [if_neg hnotgate, Nat.add_zero]
  exact hstrict



/-- Exact edge-class reduction of the pinned theorem. The caller
must still prove *both* selected families: root and proper interior.
Top, incoming, outside and terminal classes are now independent
proved candidates, with no new history assumption. -/
theorem bankTrialC5RemainingLiveRowsOfSelected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hroot : ∀ (z : BankTrialLocalState q) (heads : Nat),
      BankTrialC5RemainingRowAt ring root z heads root)
    (hinterior : ∀ (j : Fin (compileAdvice q).b),
      0 < j.val →
      ∀ (z : BankTrialLocalState q) (heads : Nat),
      BankTrialC5RemainingRowAt ring root z heads
        (Counter.site ring root j.val)) :
    BankTrialC5RemainingLiveRows (q := q) ring root := by
  intro z heads e hInv nextBegun hnext
  by_cases hterminal : bankTrialLocalTerminal z
  · exact (bankTrialC5RemainingTerminalRows
      ring root e z heads hterminal) hInv nextBegun hnext
  · by_cases houtside : ¬ Counter.Support q ring root e
    · exact (bankTrialC5RemainingOutsideRows
        ring root e hlarge z heads houtside)
        hInv nextBegun hnext
    · by_cases heRoot : e = root
      · subst e
        exact (hroot z heads) hInv nextBegun hnext
      · by_cases hincoming : ring.rightNeighbor e = root
        · exact (bankTrialC5RemainingIncomingRows
            ring root e hlarge z heads hincoming)
            hInv nextBegun hnext
        · have hsupport : Counter.Support q ring root e :=
            Classical.not_not.mp houtside
          rcases hsupport with hi | ⟨j, hjb, he⟩
          · exact False.elim (hincoming hi)
          · subst e
            by_cases htop : j = (compileAdvice q).b
            · subst j
              exact (bankTrialC5RemainingTopFramedRows
                ring root hlarge hwidth z heads)
                hInv nextBegun hnext
            · have hjzero : j ≠ 0 := by
                intro hz
                subst j
                exact heRoot rfl
              have hjpos : 0 < j := by omega
              have hjlt : j < (compileAdvice q).b := by omega
              exact (hinterior ⟨j, hjlt⟩ hjpos z heads)
                hInv nextBegun hnext


theorem bankTrialC5SumSwapSinglePublic :
    ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
      (∀ j : Fin m, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i =
        (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero =>
      intro f g i h
      exact Fin.elim0 i
  | succ m ih =>
      intro f g i h
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi : i = 0
      · subst i
        have ht :
            (List.ofFn (fun j : Fin m => f j.succ)).sum =
            (List.ofFn (fun j : Fin m => g j.succ)).sum := by
          apply FiniteUniformStoppingTree.ofFn_sum_eq
          intro j
          apply h
          intro hz
          have hv := congrArg Fin.val hz
          change j.val + 1 = 0 at hv
          omega
        rw [ht]
        omega
      · have hiv : i.val ≠ 0 := by
          intro hz
          exact hi (Fin.ext hz)
        obtain ⟨j, hj⟩ :
            ∃ j : Fin m, j.succ = i := by
          refine ⟨⟨i.val - 1, by have hh := i.isLt; omega⟩, ?_⟩
          apply Fin.ext
          change i.val - 1 + 1 = i.val
          omega
        have hmatch : ∀ k : Fin m, k ≠ j →
            f k.succ = g k.succ := by
          intro k hk
          apply h
          intro heq
          apply hk
          apply Fin.ext
          have hv := congrArg Fin.val heq
          have hjv := congrArg Fin.val hj
          change k.val + 1 = i.val at hv
          change j.val + 1 = i.val at hjv
          omega
        have htail := ih
          (fun k : Fin m => f k.succ)
          (fun k : Fin m => g k.succ) j hmatch
        have hhead := h 0 (Ne.symm hi)
        simp only [hj] at htail
        omega



/-- A two-coordinate exact replacement in List.ofFn Nat sums. -/
theorem bankTrialC5SumSwapTwoExact {m : Nat}
    (f g : Fin m → Nat) (i j : Fin m)
    (hij : i ≠ j)
    (hframe : ∀ k : Fin m, k ≠ i → k ≠ j → f k = g k)
    (hlocal : f i + f j = g i + g j) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  have hleft : ∀ k : Fin m, k ≠ i →
      f k = (if k = i then g i else f k) := by
    intro k hk
    rw [if_neg hk]
  have hright : ∀ k : Fin m, k ≠ j →
      (if k = i then g i else f k) = g k := by
    intro k hk
    by_cases hi : k = i
    · rw [if_pos hi, hi]
    · rw [if_neg hi]
      exact hframe k hi hk
  have hs1 := bankTrialC5SumSwapSinglePublic f
    (fun k => if k = i then g i else f k) i hleft
  have hs2 := bankTrialC5SumSwapSinglePublic
    (fun k => if k = i then g i else f k) g j hright
  have hmid : (if i = i then g i else f i) = g i :=
    if_pos rfl
  have hother : (if j = i then g i else f j) = f j :=
    if_neg (Ne.symm hij)
  rw [hmid] at hs1
  rw [hother] at hs2
  omega



/-- Lift an exact raw adjacent-pair potential identity to the
original physical clamped interior edge. This proves *all-slot*
carry equality without treating unrelated endpoint modes as frames.
The remaining obligation is the raw pair equality for the certified
old worker's concrete token row. -/
theorem bankTrialC5InteriorCarryOfRawPairExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b)
    (hj : 0 < j.val)
    (hraw :
      bankTrialLiveSlotPotential (j.val - 1)
          (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit
          (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok +
        bankTrialLiveSlotPotential j.val
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
      bankTrialLiveSlotPotential (j.val - 1)
          (bankTrialLiveWaveBit B
            ⟨j.val - 1, by have hh := j.isLt; omega⟩)
          (bankTrialLiveWaveToken B
            ⟨j.val - 1, by have hh := j.isLt; omega⟩) +
        bankTrialLiveSlotPotential j.val
          (bankTrialLiveWaveBit B j)
          (bankTrialLiveWaveToken B j)) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  have hp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  have hindex : j.val - 1 + 1 = j.val := by omega
  have hleftNe :
      (⟨j.val - 1, by have hh := j.isLt; omega⟩ :
        Fin (compileAdvice q).b) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change j.val - 1 = j.val at hv
    omega
  have hlocal :
      bankTrialLiveSlotPotential (j.val - 1)
          (bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val))
            ⟨j.val - 1, by have hh := j.isLt; omega⟩)
          (bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val))
            ⟨j.val - 1, by have hh := j.isLt; omega⟩) +
        bankTrialLiveSlotPotential j.val
          (bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) j)
          (bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) j) =
      bankTrialLiveSlotPotential (j.val - 1)
          (bankTrialLiveWaveBit B
            ⟨j.val - 1, by have hh := j.isLt; omega⟩)
          (bankTrialLiveWaveToken B
            ⟨j.val - 1, by have hh := j.isLt; omega⟩) +
        bankTrialLiveSlotPotential j.val
          (bankTrialLiveWaveBit B j)
          (bankTrialLiveWaveToken B j) := by
    have hs := ((hp.2.2
      (⟨j.val - 1, by have hh := j.isLt; omega⟩ :
        Fin (compileAdvice q).b)).1 hindex)
    have ht := ((hp.2.2 j).2.1 rfl)
    rw [hs.1, hs.2, ht.1, ht.2]
    exact hraw
  have hframe :
      ∀ k : Fin (compileAdvice q).b,
        k ≠ ⟨j.val - 1, by have hh := j.isLt; omega⟩ →
        k ≠ j →
        bankTrialLiveSlotPotential k.val
          (bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) k)
          (bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) k) =
        bankTrialLiveSlotPotential k.val
          (bankTrialLiveWaveBit B k)
          (bankTrialLiveWaveToken B k) := by
    intro k hneleft hneright
    have hs : k.val + 1 ≠ j.val := by
      intro he
      apply hneleft
      apply Fin.ext
      change k.val = j.val - 1
      omega
    have ht : k.val ≠ j.val := by
      intro he
      exact hneright (Fin.ext he)
    have h := ((hp.2.2 k).2.2 hs ht)
    rw [h.1, h.2]
  change
    (List.ofFn (fun k : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential k.val
        (bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k))).sum =
    (List.ofFn (fun k : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential k.val
        (bankTrialLiveWaveBit B k)
        (bankTrialLiveWaveToken B k))).sum
  exact bankTrialC5SumSwapTwoExact
    (fun k : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential k.val
        (bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k))
    (fun k : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential k.val
        (bankTrialLiveWaveBit B k)
        (bankTrialLiveWaveToken B k))
    ⟨j.val - 1, by have hh := j.isLt; omega⟩
    j hleftNe hframe hlocal



/-- The same two-slot physical carry lifting rule with old source
and destination fields, convenient for the five literal rows. -/
theorem bankTrialC5InteriorCarryOfRawFieldsExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hraw :
      bankTrialLiveSlotPotential (j.val - 1)
          (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit
          (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok +
        bankTrialLiveSlotPotential j.val
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
      bankTrialLiveSlotPotential (j.val - 1)
          (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.1
          (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 +
        bankTrialLiveSlotPotential j.val
          (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.1
          (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  apply bankTrialC5InteriorCarryOfRawPairExact
    ring root hw B hf j hj
  have hindex :
      (⟨j.val - 1 + 1, by have hh := j.isLt; omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨j.val, by have hh := j.isLt; omega⟩ :=
    Fin.ext (show j.val - 1 + 1 = j.val by omega)
  change
    bankTrialLiveSlotPotential (j.val - 1)
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok +
      bankTrialLiveSlotPotential j.val
        (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit
        (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
    bankTrialLiveSlotPotential (j.val - 1)
        (B.fields
          ⟨j.val - 1 + 1, by have hh := j.isLt; omega⟩).2.1
        (B.fields
          ⟨j.val - 1 + 1, by have hh := j.isLt; omega⟩).2.2.1 +
      bankTrialLiveSlotPotential j.val
        (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.1
        (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1
  rw [hindex]
  exact hraw

/-- Exact physical interior carry for the IR literal pair row. -/
theorem bankTrialC5InteriorIRCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields
        ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .IR)
    (hdst : (B.fields
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .E) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  apply bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj
  have hp := bankTrialC5InteriorIRPairExact
    (j.val - 1) (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change j.val = j.val - 1 + 1; omega) j.isLt rfl
    hsrc hdst
  have hindex : j.val - 1 + 1 = j.val := by omega
  simpa only [GrantBankReference.bankLocalReferenceInternalPair,
    GrantBankReference.bankLocalReferenceCell, hindex] using hp

/-- Exact physical interior carry for the AL literal pair row. -/
theorem bankTrialC5InteriorALCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields
        ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .E)
    (hdst : (B.fields
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .AL) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  apply bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj
  have hp := bankTrialC5InteriorALPairExact
    (j.val - 1) (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change j.val = j.val - 1 + 1; omega) j.isLt rfl
    hsrc hdst
  have hindex : j.val - 1 + 1 = j.val := by omega
  simpa only [GrantBankReference.bankLocalReferenceInternalPair,
    GrantBankReference.bankLocalReferenceCell, hindex] using hp

/-- Exact physical interior carry for the CRZero literal pair row. -/
theorem bankTrialC5InteriorCRZeroCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields
        ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .CR0)
    (hdst : (B.fields
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .E) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  apply bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj
  have hp := bankTrialC5InteriorCRZeroPairExact
    (j.val - 1) (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change j.val = j.val - 1 + 1; omega) j.isLt rfl
    hsrc hdst
  have hindex : j.val - 1 + 1 = j.val := by omega
  simpa only [GrantBankReference.bankLocalReferenceInternalPair,
    GrantBankReference.bankLocalReferenceCell, hindex] using hp

/-- Exact physical interior carry for the CLZero literal pair row. -/
theorem bankTrialC5InteriorCLZeroCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields
        ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .E)
    (hdst : (B.fields
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .CL0) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  apply bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj
  have hp := bankTrialC5InteriorCLZeroPairExact
    (j.val - 1) (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change j.val = j.val - 1 + 1; omega) j.isLt rfl
    hsrc hdst
  have hindex : j.val - 1 + 1 = j.val := by omega
  simpa only [GrantBankReference.bankLocalReferenceInternalPair,
    GrantBankReference.bankLocalReferenceCell, hindex] using hp

/-- Exact physical interior carry for the TopCRZero literal pair row. -/
theorem bankTrialC5InteriorTopCRZeroCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields
        ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .E)
    (hdst : (B.fields
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .CR0) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  apply bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj
  have hp := bankTrialC5InteriorTopCRZeroExact
    (j.val - 1) (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change j.val = j.val - 1 + 1; omega) j.isLt rfl (by change j.val + 1 = (compileAdvice q).b; omega)
    hsrc hdst
  have hindex : j.val - 1 + 1 = j.val := by omega
  simpa only [GrantBankReference.bankLocalReferenceInternalPair,
    GrantBankReference.bankLocalReferenceCell, hindex] using hp



/-- In a locked LIVE non-reset, non-RWAIT word, any old CL0
comparison worker authenticates the CWAIT root stage. -/
theorem bankTrialC5CLZeroRequiresCWait {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT)
    (j : Fin (compileAdvice q).b)
    (hCL : bankTrialLiveWaveToken B j = .CL0) :
    bankTrialLiveWaveRootMode B = .CWAIT := by
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have he := hc.headClear j (Or.inl hm)
      rw [he] at hCL
      cases hCL
  | CSTART =>
      have he := hc.headClear j (Or.inr hm)
      rw [he] at hCL
      cases hCL
  | IWAIT =>
      rcases hc.iwaitTokens j hm with ht | ht | ht
      · rw [ht] at hCL
        cases hCL
      · rw [ht] at hCL
        cases hCL
      · rw [ht] at hCL
        cases hCL
  | CWAIT => rfl

/-- The outgoing root cannot produce a fresh CL0 on its own
digit-one responder; CL0 is consumed, never created there. -/
theorem bankTrialC5RawRootNeverProducesCLZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) :
    (bankPair x y 1 b theta).2.tok ≠ .CL0 := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode <;> cases ht : y.tok <;>
    simp [bankPair, hx, hy, hg, hm, ht,
      hbpos, hbne, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
    (repeat' split) <;> simp

/-- A CWAIT outgoing root frames all protected bit values.
This uses the literal raw owner for digit one and the physical
clamped selector for every other digit. -/
theorem bankTrialC5CWaitRootWholeBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hcwait : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) i =
        bankTrialLiveWaveBit B i := by
  have hcmp := bankTrialCmpRoot ring root hw B hf
  have hraw := bankTrialLiveRawCWaitBitFrame
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
    (by have hb := bankTrialCmpWidth q; omega)
    rfl rfl rfl hcwait
  intro i
  by_cases hi : i.val = 0
  · have heq :
        i = ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :=
      Fin.ext hi
    rw [heq]
    calc
      bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root)
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ =
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).2.bit :=
          ((hcmp.2 (⟨0, by have hb := bankTrialCmpWidth q; omega⟩)).1
            rfl).1
      _ = bankTrialLiveWaveBit B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := hraw
  · exact ((hcmp.2 i).2 hi).1



/-- Every new CL0 on a selected outgoing-root step must be an
old higher-slot CL0. Its CWAIT origin and unchanged bit word
preserve the negative full-comparison witness. -/
theorem bankTrialC5RemainingRootCLZeroWitness {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z root).phase =
      .live nextBegun)
    (j : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root z root).bank j = .CL0) :
    bankTrialLiveBinaryValue
        (bankTrialLocalNext ring root z root).bank ≠
      bankTrialLiveThetaBinary q := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root root
      z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) root).phase =
          .live nextBegun := by
    rw [hz] at hnext
    exact hnext
  have hf := bankTrialWindowLiveOldNotLatched ring root root
    z.bank begun nextBegun hcanonical
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hz]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  have hcmp := bankTrialCmpRoot ring root hw z.bank hf
  rw [hbank] at hnew ⊢
  have hnever : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank root)
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ ≠ .CL0 := by
    have hp := ((hcmp.2
      (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
        Fin (compileAdvice q).b)).1 rfl).2
    rw [hp]
    exact bankTrialC5RawRootNeverProducesCLZero
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      (by have hb := bankTrialCmpWidth q; omega)
      rfl rfl rfl
  have hj0 : j.val ≠ 0 := by
    intro hzj
    have hj : j = ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :=
      Fin.ext hzj
    rw [hj] at hnew
    exact hnever hnew
  have hold : bankTrialLiveWaveToken z.bank j = .CL0 := by
    have hp := (hcmp.2 j).2 hj0
    rw [hp.2] at hnew
    exact hnew
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  have hcwait : bankTrialLiveWaveRootMode z.bank = .CWAIT :=
    bankTrialC5CLZeroRequiresCWait z.bank hc
      (hInv.locked.2 begun hlive)
      (hInv.noRWAIT begun hlive) j hold
  exact bankTrialC5CLZeroWitnessBitFrame z.bank
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root z.bank root)
    (bankTrialC5CWaitRootWholeBitFrame
      ring root hw z.bank hf hcwait)
    (hInv.clZeroWitness begun hlive j hold)



/-- A CR0 produced at digit one by the literal outgoing root
comes either from a newly failed CSTART comparison or from an
old CWAIT/CR0 worker. This uses the locked stage palettes. -/
theorem bankTrialC5RawRootCRZeroOrigins
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) →
      y.tok = .E)
    (hiwait : x.mode = .IWAIT →
      y.tok = .E ∨ y.tok = .IR ∨ y.tok = .AL)
    (hcwait : x.mode = .CWAIT →
      y.tok = .E ∨ y.tok = .CR0 ∨ y.tok = .CR1 ∨
        y.tok = .CL0 ∨ y.tok = .CL1)
    (hnew : (bankPair x y 1 b theta).2.tok = .CR0) :
    (x.mode = .CSTART ∧ y.tok = .E ∧
      y.bit ≠ theta 0) ∨
    (x.mode = .CWAIT ∧ y.tok = .CR0) := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET =>
      exact False.elim (hnr hm)
  | RWAIT =>
      exact False.elim (hnw hm)
  | ARMED =>
      have ht := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CSTART =>
      have ht := hhead (Or.inr hm)
      cases hbit : y.bit <;> cases htheta : theta 0 <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit, htheta,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew ⊢
  | IWAIT =>
      rcases hiwait hm with ht | ht | ht <;>
        by_cases hlease : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hlease,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CWAIT =>
      rcases hcwait hm with ht | ht | ht | ht | ht <;>
        by_cases hlease : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hlease,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew ⊢

/-- An existing CR0 worker in a locked LIVE word forces CWAIT.
The RWAIT and RESET origins are excluded by the seven-field invariant. -/
theorem bankTrialC5CRZeroRequiresCWait {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT)
    (j : Fin (compileAdvice q).b)
    (hCR : bankTrialLiveWaveToken B j = .CR0) :
    bankTrialLiveWaveRootMode B = .CWAIT := by
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have he := hc.headClear j (Or.inl hm)
      rw [he] at hCR
      cases hCR
  | CSTART =>
      have he := hc.headClear j (Or.inr hm)
      rw [he] at hCR
      cases hCR
  | IWAIT =>
      rcases hc.iwaitTokens j hm with ht | ht | ht
      · rw [ht] at hCR
        cases hCR
      · rw [ht] at hCR
        cases hCR
      · rw [ht] at hCR
        cases hCR
  | CWAIT => rfl



/-- A selected outgoing-root CR0 either inherits its prior
CWAIT-prefix mismatch, or is freshly launched by CSTART at an
already mismatching first bit. Both are authentic prefix witnesses. -/
theorem bankTrialC5RemainingRootCRZeroWitness {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z root).phase =
      .live nextBegun)
    (j : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root z root).bank j = .CR0) :
    ∃ i : Fin (compileAdvice q).b,
      i.val ≤ j.val ∧
      bankTrialLiveWaveBit
        (bankTrialLocalNext ring root z root).bank i ≠
        (compileAdvice q).theta i.val := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root root
      z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) root).phase =
          .live nextBegun := by
    rw [hz] at hnext
    exact hnext
  have hf := bankTrialWindowLiveOldNotLatched ring root root
    z.bank begun nextBegun hcanonical
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hz]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  have hcmp := bankTrialCmpRoot ring root hw z.bank hf
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  rw [hbank] at hnew ⊢
  by_cases hjzero : j.val = 0
  · have hj : j =
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :=
      Fin.ext hjzero
    have hfirst := ((hcmp.2
      (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
        Fin (compileAdvice q).b)).1 rfl)
    have hrawNew :
        (GrantBankReference.bankLocalReferenceInternalPair q z.bank
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).2.tok =
          .CR0 := by
      rw [hj] at hnew
      rw [hfirst.2] at hnew
      exact hnew
    have hhead :
        ((GrantBankReference.bankLocalReferenceCell z.bank
          ⟨0, by omega⟩).mode = .ARMED ∨
         (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨0, by omega⟩).mode = .CSTART) →
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .E := by
      intro hm
      exact hc.headClear ⟨0, by omega⟩ hm
    have hiwait :
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨0, by omega⟩).mode = .IWAIT →
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .E ∨
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .IR ∨
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .AL := by
      intro hm
      exact hc.iwaitTokens ⟨0, by omega⟩ hm
    have hcwait :
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨0, by omega⟩).mode = .CWAIT →
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .E ∨
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .CR0 ∨
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .CR1 ∨
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .CL0 ∨
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩).tok = .CL1 := by
      intro hm
      rcases hc.cwaitTokens ⟨0, by omega⟩ hm with ht | ht
      · exact Or.inl ht
      · rcases ht with ht | ht | ht | ht
        · exact Or.inr (Or.inl ht)
        · exact Or.inr (Or.inr (Or.inl ht))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ht)))
    have horigin := bankTrialC5RawRootCRZeroOrigins
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by omega⟩)
      (by have hb := bankTrialCmpWidth q; omega)
      rfl rfl rfl
      (hInv.locked.2 begun hlive)
      (hInv.noRWAIT begun hlive)
      hhead hiwait hcwait hrawNew
    rcases horigin with hlaunch | hold
    · have hlaunchRaw := bankTrialCmpRawLaunch
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨1, by omega⟩)
        (by have hb := bankTrialCmpWidth q; omega)
        rfl rfl rfl hlaunch.1 hlaunch.2.1
      have hfirstBit :
          bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank root)
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ =
          bankTrialLiveWaveBit z.bank
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :=
        hfirst.1.trans hlaunchRaw.2.2
      refine ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩,
        (by change 0 ≤ j.val; omega), ?_⟩
      rw [hfirstBit]
      exact hlaunch.2.2
    · have holdToken :
          bankTrialLiveWaveToken z.bank j = .CR0 := by
        rw [hj]
        exact hold.2
      obtain ⟨i, hi, hbad⟩ :=
        hInv.crZeroWitness begun hlive j holdToken
      have hbits := bankTrialC5CWaitRootWholeBitFrame
        ring root hw z.bank hf hold.1
      refine ⟨i, hi, ?_⟩
      rw [hbits i]
      exact hbad
  · have hframe := (hcmp.2 j).2 hjzero
    have holdToken :
        bankTrialLiveWaveToken z.bank j = .CR0 := by
      rw [hframe.2] at hnew
      exact hnew
    obtain ⟨i, hi, hbad⟩ :=
      hInv.crZeroWitness begun hlive j holdToken
    have hcwait := bankTrialC5CRZeroRequiresCWait
      z.bank hc (hInv.locked.2 begun hlive)
      (hInv.noRWAIT begun hlive) j holdToken
    have hbits := bankTrialC5CWaitRootWholeBitFrame
      ring root hw z.bank hf hcwait
    refine ⟨i, hi, ?_⟩
    rw [hbits i]
    exact hbad



/-- All four formerly OPEN C.5 rows for the selected outgoing
root, assembled from exact carry, the new-ARMED source
characterization, and the two negative-comparison witnesses. -/
theorem bankTrialC5RemainingRootSelectedRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (z : BankTrialLocalState q) (heads : Nat) :
    BankTrialC5RemainingRowAt ring root z heads root := by
  intro hInv nextBegun hnext
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bankTrialC5RemainingRootCarry
      ring root hlarge z heads hInv nextBegun hnext
  · exact bankTrialC5RemainingRootArmedStrict
      ring root hw hwidth z heads hInv nextBegun hnext
  · intro j htok
    exact bankTrialC5RemainingRootCRZeroWitness
      ring root hw z heads hInv nextBegun hnext j htok
  · intro j htok
    exact bankTrialC5RemainingRootCLZeroWitness
      ring root hw z heads hInv nextBegun hnext j htok

/-- With terminal/outside/incoming/top/root discharged by the
preceding local lemmas, the target now reduces to genuine
proper-interior (nonroot, nontop) selected pair rows only. -/
theorem bankTrialC5RemainingLiveRowsOfInterior {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hinterior : ∀ (j : Fin (compileAdvice q).b),
      0 < j.val →
      ∀ (z : BankTrialLocalState q) (heads : Nat),
      BankTrialC5RemainingRowAt ring root z heads
        (Counter.site ring root j.val)) :
    BankTrialC5RemainingLiveRows (q := q) ring root :=
  bankTrialC5RemainingLiveRowsOfSelected
    ring root hlarge hwidth
    (bankTrialC5RemainingRootSelectedRows
      ring root hlarge hwidth)
    hinterior



/-- If the protected bits are framed and no old or new slot has
an IR credit, the entire carry sum is framed. This eliminates
token-case accounting for comparison-only stages. -/
theorem bankTrialC5CarryOfNoIRBitFrame {q : Nat}
    (oldB newB : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbits : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit newB i = bankTrialLiveWaveBit oldB i)
    (hOld : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken oldB i ≠ .IR)
    (hNew : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken newB i ≠ .IR) :
    bankTrialLiveCarryValue newB =
      bankTrialLiveCarryValue oldB := by
  unfold bankTrialLiveCarryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  change bankTrialLiveSlotPotential i.val
      (bankTrialLiveWaveBit newB i)
      (bankTrialLiveWaveToken newB i) =
    bankTrialLiveSlotPotential i.val
      (bankTrialLiveWaveBit oldB i)
      (bankTrialLiveWaveToken oldB i)
  rw [hbits i]
  simp [bankTrialLiveSlotPotential, hOld i, hNew i]

/-- The locked CWAIT palette has no IR worker at any digit. -/
theorem bankTrialC5CWaitNoIR {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B k ≠ .IR := by
  intro k
  exact (bankTrialLiveWaveCWaitNoWriters B hc hm k).1

/-- The CWAIT locked comparison palette contains only E and
CR/CL tokens, at any protected digit. -/
theorem bankTrialC5CWaitTokenCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (k : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken B k = .E ∨
    bankTrialLiveWaveToken B k = .CR0 ∨
    bankTrialLiveWaveToken B k = .CR1 ∨
    bankTrialLiveWaveToken B k = .CL0 ∨
    bankTrialLiveWaveToken B k = .CL1 := by
  rcases hc.cwaitTokens k hm with h | h
  · exact Or.inl h
  · rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))



/-- Every proper selected interior edge in the CWAIT stage
preserves *all* protected bits, including the two touched
positions. The proof uses the old unique-worker certificate,
the raw comparison-bit row, and physical nonalias. -/
theorem bankTrialC5InteriorCWaitWholeBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) k =
        bankTrialLiveWaveBit B k := by
  have hleft :
      j.val - 1 < (compileAdvice q).b := by
    have hb := j.isLt
    omega
  have hleftIdx :
      (⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨j.val, by have hb := j.isLt; omega⟩ :=
    Fin.ext (show j.val - 1 + 1 = j.val by omega)
  have hxs :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CR0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CR1 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CL0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CL1 := by
    have h := bankTrialC5CWaitTokenCases B hc hm
      ⟨j.val - 1, hleft⟩
    change
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CR1 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CL0 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CL1 at h
    rw [hleftIdx] at h
    exact h
  have hys :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .CR0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .CR1 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .CL0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .CL1 :=
    bankTrialC5CWaitTokenCases B hc hm j
  have hsolo :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .E := by
    by_cases hs : bankTrialLiveWaveToken B
        ⟨j.val - 1, hleft⟩ = .E
    · left
      change (B.fields ⟨j.val, by omega⟩).2.2.1 = .E
      change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E at hs
      rw [hleftIdx] at hs
      exact hs
    · by_cases ht : bankTrialLiveWaveToken B j = .E
      · exact Or.inr ht
      · have heq := hc.uniqueWorker
          ⟨j.val - 1, hleft⟩ j hs ht
        have heqv := congrArg Fin.val heq
        change j.val - 1 = j.val at heqv
        omega
  have hraw := bankTrialInteriorRawComparisonBits
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hb := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hb := j.isLt; omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl
    hxs hys hsolo
  have hcmp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  intro k
  by_cases hs : k.val + 1 = j.val
  · calc
      bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k =
        (GrantBankReference.bankLocalReferenceInternalPair q B
          j).1.bit := ((hcmp.2.2 k).1 hs).1
      _ = (B.fields
          ⟨j.val, by have hb := j.isLt; omega⟩).2.1 := hraw.1
      _ = bankTrialLiveWaveBit B k := by
        change (B.fields
          ⟨j.val, by have hb := j.isLt; omega⟩).2.1 =
          (B.fields
            ⟨k.val + 1, by have hb := k.isLt; omega⟩).2.1
        have hindex :
            (⟨j.val, by have hb := j.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨k.val + 1, by have hb := k.isLt; omega⟩ :=
          Fin.ext (show j.val = k.val + 1 by omega)
        rw [hindex]
  · by_cases ht : k.val = j.val
    · calc
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B
            j).2.bit := ((hcmp.2.2 k).2.1 ht).1
        _ = (B.fields
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).2.1 :=
          hraw.2
        _ = bankTrialLiveWaveBit B k := by
          change (B.fields
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).2.1 =
            (B.fields
              ⟨k.val + 1, by have hb := k.isLt; omega⟩).2.1
          have hindex :
              (⟨j.val + 1, by have hb := j.isLt; omega⟩ :
                Fin ((compileAdvice q).b + 1)) =
              ⟨k.val + 1, by have hb := k.isLt; omega⟩ :=
            Fin.ext (show j.val + 1 = k.val + 1 by omega)
          rw [hindex]
    · exact ((hcmp.2.2 k).2.2 hs ht).1



/-- On a proper selected interior CWAIT edge, all-token CR/CL
comparison service conserves the exact carry. Old and new
CWAIT palettes exclude IR and the raw owner frames every bit. -/
theorem bankTrialC5InteriorCWaitCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (heads : Nat) (begun nextBegun : Bool)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hInv : BankTrialC5CompletedHeadInvariant q
      (⟨B, .live begun⟩ : BankTrialLocalState q) heads)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank =
      bankTrialLiveCarryValue B := by
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) B begun nextBegun hnext
  have hc : BankTrialLiveWaveCertificate q B :=
    hInv.locked.1 begun rfl
  have hbit := bankTrialC5InteriorCWaitWholeBitFrame
    ring root hw B hf j hj hc hm
  have hlock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) := by
    change BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root [Counter.site ring root j.val]
        (⟨B, .live begun⟩ : BankTrialLocalState q))
    exact bankTrialC5LockedArbitraryWord ring root hw
      [Counter.site ring root j.val]
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      hInv.locked
  have hnewCert : BankTrialLiveWaveCertificate q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank :=
    hlock.1 nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank
    ring root (Counter.site ring root j.val) B begun
  have hnewMode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root j.val)).bank = .CWAIT := by
    rw [hbank]
    rw [(bankTrialCmpInterior ring root hw B hf
      j.val hj j.isLt).2.1]
    exact hm
  have hbits :
      ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (bankTrialLocalNext ring root
            (⟨B, .live begun⟩ : BankTrialLocalState q)
            (Counter.site ring root j.val)).bank i =
          bankTrialLiveWaveBit B i := by
    intro i
    rw [hbank]
    exact hbit i
  exact bankTrialC5CarryOfNoIRBitFrame
    B
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).bank
    hbits (bankTrialC5CWaitNoIR B hc hm)
    (bankTrialC5CWaitNoIR _ hnewCert hnewMode)



/-- Exact two-slot potential for the five admissible IWAIT
single-worker local cases. Top IR is excluded in the last
case, because the top unary erasure would otherwise lose credit. -/
theorem bankTrialC5InteriorIWaitPairExact
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = j + 1) (hlim : j + 2 ≤ b)
    (hy : y.role = j + 2)
    (hcase :
      (x.tok = .E ∧ y.tok = .E) ∨
      (x.tok = .IR ∧ y.tok = .E) ∨
      (x.tok = .E ∧ y.tok = .AL) ∨
      (x.tok = .AL ∧ y.tok = .E) ∨
      (x.tok = .E ∧ y.tok = .IR ∧ y.role ≠ b)) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok =
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hlt : x.role < b := by omega
  have hsucc : y.role = x.role + 1 := by omega
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  rcases hcase with ⟨htx, hty⟩ | ⟨htx, hty⟩ |
      ⟨htx, hty⟩ | ⟨htx, hty⟩ | ⟨htx, hty, hnTop⟩
  · simp [bankPair, hx, hy, hpos, hlt, hsucc,
      hxn, hxTop, hyn, hyPos, hyLe, hxLe,
      htx, hty, Id.run_pure, Id.run_bind]
  · exact bankTrialC5InteriorIRPairExact
      j b theta x y hx hlt hsucc htx hty
  · exact bankTrialC5InteriorALPairExact
      j b theta x y hx hlt hsucc htx hty
  · have hnot : ¬ b < j + 1 := by omega
    simp [bankPair, hx, hy, hpos, hlt, hsucc,
      hxn, hxTop, hyn, hyPos, hyLe, hxLe,
      htx, hty, hnot, bankTrialLiveSlotPotential,
      Id.run_pure, Id.run_bind]
  · have hnot : ¬ b < j + 2 := by omega
    have hnotTop : j + 2 ≠ b := by omega
    simp [bankPair, hx, hy, hpos, hlt, hsucc,
      hxn, hxTop, hyn, hyPos, hyLe, hxLe,
      htx, hty, hnTop, hnot, hnotTop,
      bankTrialLiveSlotPotential, Id.run_pure, Id.run_bind]



/-- The locked IWAIT palette and uniqueness reduce a proper
interior pair to five exhaustive noncollision cases. The top-IR
exception is excluded using the bounded LIVE credit. -/
theorem bankTrialC5InteriorIWaitCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (hnoTop : bankTrialLiveWaveToken B
      ⟨(compileAdvice q).b - 1,
        by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    ((GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E ∧
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E) ∨
    ((GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .IR ∧
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E) ∨
    ((GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E ∧
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .AL) ∨
    ((GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .AL ∧
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E) ∨
    ((GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E ∧
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .IR ∧
      j.val + 1 ≠ (compileAdvice q).b) := by
  have hleft : j.val - 1 < (compileAdvice q).b := by
    have hjb := j.isLt
    omega
  have hidx :
      (⟨j.val - 1 + 1, by have hh := j.isLt; omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨j.val, by have hh := j.isLt; omega⟩ :=
    Fin.ext (show j.val - 1 + 1 = j.val by omega)
  have hxs :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .IR ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .AL := by
    have h := hc.iwaitTokens ⟨j.val - 1, hleft⟩ hm
    change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .IR ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .AL at h
    rw [hidx] at h
    exact h
  have hys :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .IR ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .AL :=
    hc.iwaitTokens j hm
  by_cases hxE :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E
  · rcases hys with hyE | hyIR | hyAL
    · exact Or.inl ⟨hxE, hyE⟩
    · have hnTop : j.val + 1 ≠ (compileAdvice q).b := by
        intro htop
        have hv : j.val = (compileAdvice q).b - 1 := by omega
        have hi : j =
          ⟨(compileAdvice q).b - 1,
            by have hb := bankTrialCmpWidth q; omega⟩ :=
          Fin.ext hv
        have ht : bankTrialLiveWaveToken B j = .IR := hyIR
        rw [hi] at ht
        exact hnoTop ht
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hxE, hyIR, hnTop⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hxE, hyAL⟩))
  · have hyE :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E := by
      by_cases hyKnown : (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E
      · exact hyKnown
      · have hnot := hyKnown
        have hs :
            bankTrialLiveWaveToken B
              ⟨j.val - 1, hleft⟩ ≠ .E := by
          intro h
          apply hxE
          change (B.fields ⟨j.val, by omega⟩).2.2.1 = .E
          change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E at h
          rw [hidx] at h
          exact h
        have ht : bankTrialLiveWaveToken B j ≠ .E := hnot
        have heq := hc.uniqueWorker
          ⟨j.val - 1, hleft⟩ j hs ht
        have hv := congrArg Fin.val heq
        change j.val - 1 = j.val at hv
        omega
    rcases hxs with hxe | hxi | hxa
    · exact False.elim (hxE hxe)
    · exact Or.inr (Or.inl ⟨hxi, hyE⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hxa, hyE⟩)))



/-- Exact physical carry for all proper interior IWAIT selected
edges. The locked palette and worker uniqueness select exactly
one of the five raw conservative pair rows. -/
theorem bankTrialC5InteriorIWaitCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (heads : Nat) (begun nextBegun : Bool)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hInv : BankTrialC5CompletedHeadInvariant q
      (⟨B, .live begun⟩ : BankTrialLocalState q) heads)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank =
      bankTrialLiveCarryValue B := by
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) B begun nextBegun hnext
  have hnoTop := bankTrialC5NoTopIRInLive
    (⟨B, .live begun⟩ : BankTrialLocalState q)
    heads hwidth hInv begun rfl
  have hcases := bankTrialC5InteriorIWaitCases B
    (hInv.locked.1 begun rfl) hm hnoTop j hj
  have hraw := bankTrialC5InteriorIWaitPairExact
    (j.val - 1) (compileAdvice q).b
    (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change j.val = j.val - 1 + 1; omega)
    (by have hh := j.isLt; omega)
    (by change j.val + 1 = j.val - 1 + 2; omega)
    hcases
  have hindex : j.val - 1 + 1 = j.val := by omega
  have hraw' := by
    simpa only [GrantBankReference.bankLocalReferenceInternalPair,
      GrantBankReference.bankLocalReferenceCell, hindex] using hraw
  have hcarry := bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj hraw'
  rw [bankTrialLocalNextLiveBank ring root
    (Counter.site ring root j.val) B begun]
  exact hcarry



/-- ARMED/CSTART interior services have empty worker tokens on
both endpoints and conserve carry by the empty-pair row. -/
theorem bankTrialC5InteriorHeadClearCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .ARMED ∨
      bankTrialLiveWaveRootMode B = .CSTART) :
    bankTrialLiveCarryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) =
      bankTrialLiveCarryValue B := by
  have hsrc :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E := by
    have h := hc.headClear
      ⟨j.val - 1, by have hh := j.isLt; omega⟩ hm
    change
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E at h
    have hi :
        (⟨j.val - 1 + 1, by have hh := j.isLt; omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by have hh := j.isLt; omega⟩ :=
      Fin.ext (show j.val - 1 + 1 = j.val by omega)
    rw [hi] at h
    exact h
  have hdst :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E :=
    hc.headClear j hm
  have hp := bankTrialInteriorRawEmptyPair
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hsrc hdst
  apply bankTrialC5InteriorCarryOfRawFieldsExact
    ring root hw B hf j hj
  have hindex : j.val - 1 + 1 = j.val := by omega
  simp only [GrantBankReference.bankLocalReferenceInternalPair,
    GrantBankReference.bankLocalReferenceCell] at hp ⊢
  rw [hp.2.2.1, hp.1, hp.2.2.2, hp.2.1]
  have hsrcField :
      (B.fields ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .E := hsrc
  have hdstField :
      (B.fields ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .E := hdst
  rw [hsrcField, hdstField]

/-- The exact proper-interior carry rule for ALL old LIVE modes
allowed by the seven-field invariant: ARMED/CSTART have no worker;
IWAIT conserves IR credit, CWAIT frames comparison bits; RESET
and RWAIT are excluded by locked/noRWAIT. -/
theorem bankTrialC5InteriorCarryExactAllModes {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (heads : Nat) (begun nextBegun : Bool)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hInv : BankTrialC5CompletedHeadInvariant q
      (⟨B, .live begun⟩ : BankTrialLocalState q) heads)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank =
      bankTrialLiveCarryValue B := by
  have hc : BankTrialLiveWaveCertificate q B :=
    hInv.locked.1 begun rfl
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET =>
      exact False.elim ((hInv.locked.2 begun rfl) hm)
  | RWAIT =>
      exact False.elim ((hInv.noRWAIT begun rfl) hm)
  | ARMED =>
      have hf := bankTrialWindowLiveOldNotLatched ring root
        (Counter.site ring root j.val) B begun nextBegun hnext
      have hraw := bankTrialC5InteriorHeadClearCarryExact
        ring root hw B hf j hj hc (Or.inl hm)
      rw [bankTrialLocalNextLiveBank ring root
        (Counter.site ring root j.val) B begun]
      exact hraw
  | CSTART =>
      have hf := bankTrialWindowLiveOldNotLatched ring root
        (Counter.site ring root j.val) B begun nextBegun hnext
      have hraw := bankTrialC5InteriorHeadClearCarryExact
        ring root hw B hf j hj hc (Or.inr hm)
      rw [bankTrialLocalNextLiveBank ring root
        (Counter.site ring root j.val) B begun]
      exact hraw
  | IWAIT =>
      exact bankTrialC5InteriorIWaitCarryExact ring root
        hw hwidth B heads begun nextBegun j hj hInv hnext hm
  | CWAIT =>
      exact bankTrialC5InteriorCWaitCarryExact ring root
        hw B heads begun nextBegun j hj hInv hnext hm



/-- A certified failed comparison prefix already implies
inequality of the complete binary word; injectivity of binary
expansion makes no assumption about where the witness lies. -/
theorem bankTrialC5CRZeroWitnessImpliesBinaryMismatch {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (hWitness : ∃ i : Fin (compileAdvice q).b,
      i.val ≤ j.val ∧
      bankTrialLiveWaveBit B i ≠ (compileAdvice q).theta i.val) :
    bankTrialLiveBinaryValue B ≠ bankTrialLiveThetaBinary q := by
  intro heq
  obtain ⟨i, hi, hbad⟩ := hWitness
  have hbits := (bankTrialCmpBinaryIff B).mp heq
  have hbit := hbits i.val i.isLt
  rw [bankTrialCmpBitEq B i.val i.isLt] at hbit
  exact hbad hbit



/-- A failed top CR0 turns into leftward CL0 while the entire
comparison word remains unchanged. The old CR0 prefix mismatch
thus authenticates the new CL0 negative full-word witness. -/
theorem bankTrialC5InteriorTopCRZeroWitness {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT)
    (hsrc : (B.fields
      ⟨j.val, by have hh := j.isLt; omega⟩).2.2.1 = .E)
    (hdst : (B.fields
      ⟨j.val + 1, by have hh := j.isLt; omega⟩).2.2.1 = .CR0)
    (hWitness : ∃ i : Fin (compileAdvice q).b,
      i.val ≤ j.val ∧
      bankTrialLiveWaveBit B i ≠
        (compileAdvice q).theta i.val) :
    bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val))
      ⟨j.val - 1, by have hh := j.isLt; omega⟩ = .CL0 ∧
    bankTrialLiveBinaryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) ≠
      bankTrialLiveThetaBinary q := by
  have hm := bankTrialC5CRZeroRequiresCWait
    B hc hnr hnw j hdst
  have hraw := bankTrialInteriorCRZeroTop
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl
    (by change j.val + 1 = (compileAdvice q).b; omega)
    hsrc hdst
  have hcmp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  have htoken :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val))
        ⟨j.val - 1, by have hh := j.isLt; omega⟩ = .CL0 := by
    calc
      bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val))
          ⟨j.val - 1, by have hh := j.isLt; omega⟩ =
        (GrantBankReference.bankLocalReferenceInternalPair q B
          j).1.tok :=
        ((hcmp.2.2
          (⟨j.val - 1, by have hh := j.isLt; omega⟩ :
            Fin (compileAdvice q).b)).1
          (show j.val - 1 + 1 = j.val by omega)).2
      _ = .CL0 := hraw.1
  refine ⟨htoken, ?_⟩
  exact bankTrialC5CLZeroWitnessBitFrame B
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    (bankTrialC5InteriorCWaitWholeBitFrame
      ring root hw B hf j hj hc hm)
    (bankTrialC5CRZeroWitnessImpliesBinaryMismatch B j hWitness)



/-- Precise final interface: after the unconditional root/top/
incoming/outside rows and exact proper-interior carry, the
ONLY remaining proper-interior obligations are preservation of
the two negative comparison witnesses. This theorem does not
assume the conclusion of the pinned theorem. -/
theorem bankTrialC5RemainingLiveRowsOfInteriorWitnesses {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hCR : ∀ (j : Fin (compileAdvice q).b),
      0 < j.val →
      ∀ (z : BankTrialLocalState q) (heads : Nat),
      BankTrialC5CompletedHeadInvariant q z heads →
      ∀ nextBegun : Bool,
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)).phase = .live nextBegun →
        ∀ k : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z
              (Counter.site ring root j.val)).bank k = .CR0 →
          ∃ i : Fin (compileAdvice q).b,
            i.val ≤ k.val ∧
            bankTrialLiveWaveBit
              (bankTrialLocalNext ring root z
                (Counter.site ring root j.val)).bank i ≠
              (compileAdvice q).theta i.val)
    (hCL : ∀ (j : Fin (compileAdvice q).b),
      0 < j.val →
      ∀ (z : BankTrialLocalState q) (heads : Nat),
      BankTrialC5CompletedHeadInvariant q z heads →
      ∀ nextBegun : Bool,
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)).phase = .live nextBegun →
        ∀ k : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z
              (Counter.site ring root j.val)).bank k = .CL0 →
          bankTrialLiveBinaryValue
            (bankTrialLocalNext ring root z
              (Counter.site ring root j.val)).bank ≠
          bankTrialLiveThetaBinary q) :
    BankTrialC5RemainingLiveRows (q := q) ring root := by
  apply bankTrialC5RemainingLiveRowsOfInterior
    ring root hlarge hwidth
  intro j hj z heads hInv nextBegun hnext
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hnotRoot := bankTrialWindowInteriorNotRoot
    ring root hw j hj
  have hzero :
      ¬ (BankTrialProbabilityArmedGate z ∧
        Counter.site ring root j.val = root) := by
    intro h
    exact hnotRoot h.2
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root
      (Counter.site ring root j.val) z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hInvCanon : BankTrialC5CompletedHeadInvariant q
      (⟨z.bank, .live begun⟩ : BankTrialLocalState q)
      heads := by
    have h := hInv
    rw [hz] at h
    exact h
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).phase = .live nextBegun := by
    have h := hnext
    rw [hz] at h
    exact h
  have hcarry :
      bankTrialLiveCarryValue
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)).bank =
        bankTrialLiveCarryValue z.bank := by
    rw [hz]
    exact bankTrialC5InteriorCarryExactAllModes ring root
      hw hwidth z.bank heads begun nextBegun j hj
      hInvCanon hcanonical
  have hstrict := bankTrialC5RemainingInteriorArmedStrict
    ring root hw z heads hInv j hj nextBegun hnext
  rw [if_neg hzero, Nat.add_zero] at hstrict
  rw [if_neg hzero, Nat.add_zero]
  refine ⟨hcarry.trans (hInv.liveCarry begun hlive),
    hstrict, ?_, ?_⟩
  · intro k ht
    exact hCR j hj z heads hInv nextBegun hnext k ht
  · intro k ht
    exact hCL j hj z heads hInv nextBegun hnext k ht



/-- A locked pair cannot contain two distinct nonempty digit workers. -/
theorem bankTrialC5InteriorOldPairSolo {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hh := j.isLt; omega⟩).tok = .E ∨
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hh := j.isLt; omega⟩).tok = .E := by
  have hleft : j.val - 1 < (compileAdvice q).b := by
    have hb := j.isLt
    omega
  have hidx :
      (⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨j.val, by have hb := j.isLt; omega⟩ :=
    Fin.ext (show j.val - 1 + 1 = j.val by omega)
  by_cases hx : bankTrialLiveWaveToken B ⟨j.val - 1, hleft⟩ = .E
  · left
    change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E at hx
    rw [hidx] at hx
    exact hx
  · by_cases hy : bankTrialLiveWaveToken B j = .E
    · exact Or.inr hy
    · have h := hc.uniqueWorker ⟨j.val - 1, hleft⟩ j hx hy
      have hv := congrArg Fin.val h
      change j.val - 1 = j.val at hv
      omega

/-- The interior raw comparison owner cannot output CR0 at its
left endpoint when at most one old worker is present. -/
theorem bankTrialC5RawInteriorLeftNoCRZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).1.tok ≠ .CR0 := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  -- Nonroot source: only the token rows of `bankPair` run (BankPairNonroot.lean).
  rw [bankPair_nonroot x y y.role b theta hxn]
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp [he, ht]
  · cases ht : x.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp [he, ht]

/-- The interior raw comparison owner cannot output CL0 at its
right endpoint when at most one old worker is present. -/
theorem bankTrialC5RawInteriorRightNoCLZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).2.tok ≠ .CL0 := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  -- Nonroot source: only the token rows of `bankPair` run (BankPairNonroot.lean).
  rw [bankPair_nonroot x y y.role b theta hxn]
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp [he, ht]
  · cases ht : x.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp [he, ht]

/-- A right CR0 is inherited from a right CR0, forwarded from
left CR0, or created when left CR1 fails the next comparison. -/
theorem bankTrialC5RawInteriorRightCRZeroAncestors
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnew : (bankPair x y y.role b theta).2.tok = .CR0) :
    x.tok = .CR0 ∨ y.tok = .CR0 ∨ x.tok = .CR1 := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  -- Nonroot source: only the token rows of `bankPair` run (BankPairNonroot.lean).
  rw [bankPair_nonroot x y y.role b theta hxn] at hnew
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢
  · cases ht : x.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢

/-- A left CL0 is inherited on the left, returned from the
right, or turned from the right CR0 at the top rank. -/
theorem bankTrialC5RawInteriorLeftCLZeroAncestors
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnew : (bankPair x y y.role b theta).1.tok = .CL0) :
    x.tok = .CL0 ∨ y.tok = .CL0 ∨
      (y.tok = .CR0 ∧ y.role = b) := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  -- Nonroot source: only the token rows of `bankPair` run (BankPairNonroot.lean).
  rw [bankPair_nonroot x y y.role b theta hxn] at hnew
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢
  · cases ht : x.tok <;>
      simp [bankPairNR, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢

/-- Proper interior CR0 provenance. An inherited failed comparison
keeps its witness; a CR1 that first becomes CR0 witnesses the current
right-hand digit. hlarge is represented here by physical nonalias. -/
theorem bankTrialC5RemainingInteriorCRZeroSelected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (k : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)).bank k = .CR0) :
    ∃ i : Fin (compileAdvice q).b,
      i.val ≤ k.val ∧
      bankTrialLiveWaveBit
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)).bank i ≠
        (compileAdvice q).theta i.val := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root
      (Counter.site ring root j.val) z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).phase = .live nextBegun := by
    rw [hz] at hnext
    exact hnext
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) z.bank begun nextBegun hcanonical
  have hbank :
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)).bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank (Counter.site ring root j.val) := by
    rw [hz]
    exact bankTrialLocalNextLiveBank ring root
      (Counter.site ring root j.val) z.bank begun
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  have hcmp := bankTrialCmpInterior ring root hw z.bank hf
    j.val hj j.isLt
  have hsolo := bankTrialC5InteriorOldPairSolo z.bank hc j hj
  have htransport :
      bankTrialLiveWaveRootMode z.bank = .CWAIT →
      ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank (Counter.site ring root j.val)) i =
        bankTrialLiveWaveBit z.bank i := by
    intro hm
    exact bankTrialC5InteriorCWaitWholeBitFrame
      ring root hw z.bank hf j hj hc hm
  rw [hbank] at hnew ⊢
  by_cases hs : k.val + 1 = j.val
  · have hraw :
        (GrantBankReference.bankLocalReferenceInternalPair
          q z.bank j).1.tok = .CR0 := by
      rw [((hcmp.2.2 k).1 hs).2] at hnew
      exact hnew
    exact False.elim (bankTrialC5RawInteriorLeftNoCRZero
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨j.val, by have h := j.isLt; omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨j.val + 1, by have h := j.isLt; omega⟩)
      (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw)
  · by_cases ht : k.val = j.val
    · have hraw :
          (GrantBankReference.bankLocalReferenceInternalPair
            q z.bank j).2.tok = .CR0 := by
        rw [((hcmp.2.2 k).2.1 ht).2] at hnew
        exact hnew
      have horigin := bankTrialC5RawInteriorRightCRZeroAncestors
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨j.val, by have h := j.isLt; omega⟩)
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨j.val + 1, by have h := j.isLt; omega⟩)
        (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw
      rcases horigin with hleft | hright | hleftGood
      · have hleftIdx :
            (⟨k.val + 1, by have h := k.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨j.val + 1, by have h := j.isLt; omega⟩ :=
          Fin.ext (show k.val + 1 = j.val + 1 by omega)
        have hsourceIdx :
            (⟨j.val - 1 + 1, by have h := j.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨j.val, by have h := j.isLt; omega⟩ :=
          Fin.ext (show j.val - 1 + 1 = j.val by omega)
        have hsource :
            bankTrialLiveWaveToken z.bank
              ⟨j.val - 1, by have h := j.isLt; omega⟩ = .CR0 := by
          change (z.bank.fields
            ⟨j.val - 1 + 1, by have h := j.isLt; omega⟩).2.2.1 = .CR0
          rw [hsourceIdx]
          exact hleft
        have hm := bankTrialC5CRZeroRequiresCWait z.bank hc
          (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
          ⟨j.val - 1, by have h := j.isLt; omega⟩ hsource
        obtain ⟨i, hi, hbad⟩ :=
          hInv.crZeroWitness begun hlive
            ⟨j.val - 1, by have h := j.isLt; omega⟩ hsource
        change i.val ≤ j.val - 1 at hi
        refine ⟨i, (by omega), ?_⟩
        rw [htransport hm i]
        exact hbad
      · have hsource : bankTrialLiveWaveToken z.bank j = .CR0 :=
          hright
        have hm := bankTrialC5CRZeroRequiresCWait z.bank hc
          (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
          j hsource
        obtain ⟨i, hi, hbad⟩ :=
          hInv.crZeroWitness begun hlive j hsource
        refine ⟨i, (by omega), ?_⟩
        rw [htransport hm i]
        exact hbad
      · have hsourceIdx :
            (⟨j.val - 1 + 1, by have h := j.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨j.val, by have h := j.isLt; omega⟩ :=
          Fin.ext (show j.val - 1 + 1 = j.val by omega)
        have hsource :
            bankTrialLiveWaveToken z.bank
              ⟨j.val - 1, by have h := j.isLt; omega⟩ = .CR1 := by
          change (z.bank.fields
            ⟨j.val - 1 + 1, by have h := j.isLt; omega⟩).2.2.1 = .CR1
          rw [hsourceIdx]
          exact hleftGood
        have hm : bankTrialLiveWaveRootMode z.bank = .CWAIT :=
          hc.comparisonMode
            ⟨j.val - 1, by have h := j.isLt; omega⟩
            (Or.inl hsource)
        have hrightE :
            (GrantBankReference.bankLocalReferenceCell z.bank
              ⟨j.val + 1, by have h := j.isLt; omega⟩).tok = .E := by
          rcases hsolo with hxE | hyE
          · rw [hxE] at hleftGood
            cases hleftGood
          · exact hyE
        have hforward := bankTrialCmpRawCRForward
          (compileAdvice q).b (compileAdvice q).theta
          (GrantBankReference.bankLocalReferenceCell z.bank
            ⟨j.val, by have h := j.isLt; omega⟩)
          (GrantBankReference.bankLocalReferenceCell z.bank
            ⟨j.val + 1, by have h := j.isLt; omega⟩)
          (by change 1 ≤ j.val; omega) j.isLt rfl true
          (by simpa using hleftGood) hrightE
        have hbad :
            (GrantBankReference.bankLocalReferenceCell z.bank
              ⟨j.val + 1, by have h := j.isLt; omega⟩).bit ≠
            (compileAdvice q).theta
              ((GrantBankReference.bankLocalReferenceCell z.bank
                ⟨j.val + 1, by have h := j.isLt; omega⟩).role - 1) := by
          intro heq
          have hbool :
              (true && ((GrantBankReference.bankLocalReferenceCell
                z.bank ⟨j.val + 1, by have h := j.isLt; omega⟩).bit ==
                (compileAdvice q).theta
                  ((GrantBankReference.bankLocalReferenceCell z.bank
                    ⟨j.val + 1, by have h := j.isLt; omega⟩).role - 1))) =
                true := by simp [heq]
          have htest := hforward.2.2.1
          rw [hbool] at htest
          have hcontr : (BTok.CR1 : BTok) = .CR0 :=
            htest.symm.trans hraw
          cases hcontr
        refine ⟨j, (by omega), ?_⟩
        rw [htransport hm j]
        have hnum : j.val + 1 - 1 = j.val := by omega
        change (z.bank.fields
          ⟨j.val + 1, by have h := j.isLt; omega⟩).2.1 ≠
          (compileAdvice q).theta (j.val + 1 - 1) at hbad
        rw [hnum] at hbad
        exact hbad
    · have hframe := ((hcmp.2.2 k).2.2 hs ht)
      have hold : bankTrialLiveWaveToken z.bank k = .CR0 := by
        rw [hframe.2] at hnew
        exact hnew
      have hm := bankTrialC5CRZeroRequiresCWait z.bank hc
        (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
        k hold
      obtain ⟨i, hi, hbad⟩ :=
        hInv.crZeroWitness begun hlive k hold
      refine ⟨i, hi, ?_⟩
      rw [htransport hm i]
      exact hbad

/-- Proper interior CL0 provenance. The top CR0 turn is the only
source of a new CL0 not already a CL0; its failed prefix certifies
the negative full binary comparison. -/
theorem bankTrialC5RemainingInteriorCLZeroSelected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (k : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)).bank k = .CL0) :
    bankTrialLiveBinaryValue
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)).bank ≠
      bankTrialLiveThetaBinary q := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root
      (Counter.site ring root j.val) z nextBegun hnext
  have hz := bankTrialCmpStateEta z begun hlive
  have hcanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).phase = .live nextBegun := by
    rw [hz] at hnext
    exact hnext
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) z.bank begun nextBegun hcanonical
  have hbank :
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)).bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank (Counter.site ring root j.val) := by
    rw [hz]
    exact bankTrialLocalNextLiveBank ring root
      (Counter.site ring root j.val) z.bank begun
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  have hcmp := bankTrialCmpInterior ring root hw z.bank hf
    j.val hj j.isLt
  have hsolo := bankTrialC5InteriorOldPairSolo z.bank hc j hj
  have htransport :
      bankTrialLiveWaveRootMode z.bank = .CWAIT →
      bankTrialLiveBinaryValue z.bank ≠ bankTrialLiveThetaBinary q →
      bankTrialLiveBinaryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank (Counter.site ring root j.val)) ≠
      bankTrialLiveThetaBinary q := by
    intro hm hbad
    exact bankTrialC5CLZeroWitnessBitFrame z.bank
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank (Counter.site ring root j.val))
      (bankTrialC5InteriorCWaitWholeBitFrame
        ring root hw z.bank hf j hj hc hm) hbad
  rw [hbank] at hnew ⊢
  by_cases hs : k.val + 1 = j.val
  · have hraw :
        (GrantBankReference.bankLocalReferenceInternalPair
          q z.bank j).1.tok = .CL0 := by
      rw [((hcmp.2.2 k).1 hs).2] at hnew
      exact hnew
    have horigin := bankTrialC5RawInteriorLeftCLZeroAncestors
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨j.val, by have h := j.isLt; omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨j.val + 1, by have h := j.isLt; omega⟩)
      (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw
    rcases horigin with hleft | hright | ⟨htopCR, htop⟩
    · have hsourceIdx :
          (⟨k.val + 1, by have h := k.isLt; omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val, by have h := j.isLt; omega⟩ :=
        Fin.ext hs
      have hold : bankTrialLiveWaveToken z.bank k = .CL0 := by
        change (z.bank.fields
          ⟨k.val + 1, by have h := k.isLt; omega⟩).2.2.1 = .CL0
        rw [hsourceIdx]
        exact hleft
      have hm := bankTrialC5CLZeroRequiresCWait z.bank hc
        (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
        k hold
      exact htransport hm (hInv.clZeroWitness begun hlive k hold)
    · have hold : bankTrialLiveWaveToken z.bank j = .CL0 :=
        hright
      have hm := bankTrialC5CLZeroRequiresCWait z.bank hc
        (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
        j hold
      exact htransport hm (hInv.clZeroWitness begun hlive j hold)
    · have hold : bankTrialLiveWaveToken z.bank j = .CR0 :=
        htopCR
      have hm := bankTrialC5CRZeroRequiresCWait z.bank hc
        (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
        j hold
      have hprefix := hInv.crZeroWitness begun hlive j hold
      exact htransport hm
        (bankTrialC5CRZeroWitnessImpliesBinaryMismatch z.bank j hprefix)
  · by_cases ht : k.val = j.val
    · have hraw :
          (GrantBankReference.bankLocalReferenceInternalPair
            q z.bank j).2.tok = .CL0 := by
        rw [((hcmp.2.2 k).2.1 ht).2] at hnew
        exact hnew
      exact False.elim (bankTrialC5RawInteriorRightNoCLZero
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨j.val, by have h := j.isLt; omega⟩)
        (GrantBankReference.bankLocalReferenceCell z.bank
          ⟨j.val + 1, by have h := j.isLt; omega⟩)
        (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw)
    · have hframe := ((hcmp.2.2 k).2.2 hs ht)
      have hold : bankTrialLiveWaveToken z.bank k = .CL0 := by
        rw [hframe.2] at hnew
        exact hnew
      have hm := bankTrialC5CLZeroRequiresCWait z.bank hc
        (hInv.locked.2 begun hlive) (hInv.noRWAIT begun hlive)
        k hold
      exact htransport hm (hInv.clZeroWitness begun hlive k hold)


/-- G11c: the remaining one-edge LIVE rows of the C.5 invariant. -/
theorem bankTrialC5RemainingLiveRowsHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialC5RemainingLiveRows (q := q) ring root := by
  apply bankTrialC5RemainingLiveRowsOfInteriorWitnesses
    ring root hlarge hwidth
  · intro j hj z heads hInv nextBegun hnext k htok
    exact bankTrialC5RemainingInteriorCRZeroSelected
      ring root (bankTrialProbabilityUpperWindow hlarge)
      z heads hInv j hj nextBegun hnext k htok
  · intro j hj z heads hInv nextBegun hnext k htok
    exact bankTrialC5RemainingInteriorCLZeroSelected
      ring root (bankTrialProbabilityUpperWindow hlarge)
      z heads hInv j hj nextBegun hnext k htok


/-- G11c, soundness half of C.5: every completed-head word from a
CLEAN start ends in `won`, for every start bank `S`. -/
theorem bankTrialProbabilityC5CompletedHeadSoundHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    BankTrialProbabilityC5CompletedHeadSound ring root S := by
  intro hsp hlarge hwidth hclean
  exact bankTrialProbabilityC5CompletedHeadSoundOfRemainingRows
    ring root S
    (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
    hsp hlarge hwidth hclean

/-- G11c: the C.4/C.5 lower target now needs only the mass bound
`BankTrialProbabilityC5CompletedHeadMassLower`. -/
theorem bankTrialProbabilityThetaLowerOfCompletedHeadMass
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hmass : BankTrialProbabilityC5CompletedHeadMassLower
      ring root S) :
    BankTrialProbabilityThetaLowerTarget ring root S :=
  bankTrialProbabilityThetaLowerOfCompletedHead ring root S
    (bankTrialProbabilityC5CompletedHeadSoundHolds ring root S)
    hmass

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An original-n-edge numerator for a shadow all-head cylinder.
Unlike the actual gated head event, the shadow can include words
whose worker aborted before all K head decisions were observed. -/
noncomputable def bankTrialProbabilityC5ShadowHeadMass {n : Nat}
    (shadow : List (Fin n) → Prop) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w => if shadow w then 1 else 0)

/-- The mass in the shadow cylinder not accounted for by an actual
completed K-head word. The subtraction is sound when the completed
event is included in the shadow, as required below. -/
noncomputable def bankTrialProbabilityC5ShadowDefectMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop) (T : Nat) : Nat :=
  bankTrialProbabilityC5ShadowHeadMass shadow T -
    bankTrialProbabilityC5CompletedHeadMass ring root S T

/-- Inclusion of actual completed heads in an enclosing shadow
cylinder implies inclusion of their original-clock masses. -/
theorem bankTrialProbabilityC5CompletedMassLeShadow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop)
    (hshadow : ∀ w : List (Fin n),
      bankTrialProbabilityC5CompletedHeadWord ring root S w →
        shadow w)
    (T : Nat) :
    bankTrialProbabilityC5CompletedHeadMass ring root S T ≤
      bankTrialProbabilityC5ShadowHeadMass shadow T := by
  unfold bankTrialProbabilityC5CompletedHeadMass
    bankTrialProbabilityC5ShadowHeadMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro w
  by_cases hc :
      bankTrialProbabilityC5CompletedHeadWord ring root S w
  · have hs : shadow w := hshadow w hc
    simp only [if_pos hc, if_pos hs]
    exact Nat.le_refl _
  · simp only [if_neg hc]
    exact Nat.zero_le _

/-- Exact partition at one common physical scheduler horizon;
no independence or tail probability is inferred here. -/
theorem bankTrialProbabilityC5ShadowHeadMassSplit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop)
    (hshadow : ∀ w : List (Fin n),
      bankTrialProbabilityC5CompletedHeadWord ring root S w →
        shadow w)
    (T : Nat) :
    bankTrialProbabilityC5ShadowHeadMass shadow T =
      bankTrialProbabilityC5CompletedHeadMass ring root S T +
        bankTrialProbabilityC5ShadowDefectMass
          ring root S shadow T := by
  have hsub := bankTrialProbabilityC5CompletedMassLeShadow
    ring root S shadow hshadow T
  unfold bankTrialProbabilityC5ShadowDefectMass
  calc
    bankTrialProbabilityC5ShadowHeadMass shadow T =
        (bankTrialProbabilityC5ShadowHeadMass shadow T -
          bankTrialProbabilityC5CompletedHeadMass ring root S T) +
          bankTrialProbabilityC5CompletedHeadMass ring root S T :=
      (Nat.sub_add_cancel hsub).symm
    _ = bankTrialProbabilityC5CompletedHeadMass ring root S T +
          (bankTrialProbabilityC5ShadowHeadMass shadow T -
            bankTrialProbabilityC5CompletedHeadMass ring root S T) :=
      Nat.add_comm _ _

/-- All powers have been replaced by opaque Nat variables.
A coverage defect of at most 1/(1024 D), combined with a
head-conditioned worker defect of at most L N / D, gives the
required 1023/1024 lower fraction when 1024 L N < D. -/
theorem bankTrialProbabilityC5ShadowArithmetic
    {D N L P H E B X : Nat}
    (hD : 0 < D)
    (hbudget : 1024 * L * N < D)
    (hsplit : H = E + B)
    (hcover : 1024 * D * X ≤ 1024 * D * P * H + X)
    (hbad : D * P * B ≤ L * N * X) :
    1023 * X ≤ 1024 * P * E := by
  have hcost : 1024 * L * N + 1 ≤ D := by omega
  have hcostX :
      (1024 * L * N + 1) * X ≤ D * X :=
    Nat.mul_le_mul_right X hcost
  have hbadScaled :
      1024 * (D * P * B) ≤ 1024 * (L * N * X) :=
    Nat.mul_le_mul_left 1024 hbad
  have hmass :
      1024 * D * X ≤ 1024 * D * P * E + D * X := by
    calc
      1024 * D * X ≤ 1024 * D * P * H + X := hcover
      _ = 1024 * D * P * (E + B) + X := by rw [hsplit]
      _ = 1024 * D * P * E +
            (1024 * (D * P * B) + X) := by
          simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      _ ≤ 1024 * D * P * E +
            (1024 * (L * N * X) + X) :=
          Nat.add_le_add_left
            (Nat.add_le_add_right hbadScaled X) _
      _ = 1024 * D * P * E +
            ((1024 * L * N + 1) * X) := by
          simp only [Nat.add_mul, Nat.one_mul,
            Nat.mul_assoc]
      _ ≤ 1024 * D * P * E + D * X :=
          Nat.add_le_add_left hcostX _
  have hfactor :
      D * (1023 * X) + D * X = 1024 * D * X := by
    calc
      D * (1023 * X) + D * X =
          1023 * (D * X) + D * X := by
        simp only [Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc]
      _ = (1023 + 1) * (D * X) := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = 1024 * D * X := by
        change 1024 * (D * X) = (1024 * D) * X
        exact (Nat.mul_assoc 1024 D X).symm
  have hcancel :
      D * (1023 * X) + D * X ≤
        D * (1024 * P * E) + D * X := by
    calc
      _ = 1024 * D * X := hfactor
      _ ≤ 1024 * D * P * E + D * X := hmass
      _ = D * (1024 * P * E) + D * X := by
        simp only [Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc]
  have hmul :
      D * (1023 * X) ≤ D * (1024 * P * E) := by
    omega
  exact Nat.le_of_mul_le_mul_left hmul hD

/-- FIRST MISSING FACT (not a theorem).

At a single finite physical-n-edge horizon T there must be a
shadow fair-all-K-head cylinder enclosing actual completed heads.
The first inequality quantifies a sufficiently small finite-time
defect of the shadow's fair 2^(-K) mass. The second quantifies
the watchdog defect *conditioned on that head cylinder*.

The ordinary designated schedule, armed-cut fairness equality,
all-word start cap, and unconditional OriginRarity estimate do
not currently prove this coupled stopping-time assertion. -/
def BankTrialProbabilityC5ShadowHeadWatchdog {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∃ shadow : List (Fin n) → Prop,
    (∀ w : List (Fin n),
      bankTrialProbabilityC5CompletedHeadWord ring root S w →
        shadow w) ∧
    ∃ T : Nat,
      (1024 * bankTrialProbabilityC5WorkerDenominator q *
          n ^ T ≤
        1024 * bankTrialProbabilityC5WorkerDenominator q *
          2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5ShadowHeadMass shadow T +
          n ^ T) ∧
      (bankTrialProbabilityC5WorkerDenominator q *
          2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5ShadowDefectMass
            ring root S shadow T ≤
        (2 * (compileAdvice q).K + 1) *
          bankTrialProbabilityC5WorkerNumerator q * n ^ T)

/-- The conditional mass theorem, rigorously separating the
one missing finite-horizon/conditional-watchdog assertion from
the already proved numerical WorkerBudget inequality. -/
theorem bankTrialProbabilityC5CompletedHeadMassLowerOfShadowHeadWatchdog
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbridge : BankTrialProbabilityC5ShadowHeadWatchdog
      ring root S) :
    BankTrialProbabilityC5CompletedHeadMassLower
      ring root S := by
  intro hsp hlarge hwidth hclean
  obtain ⟨shadow, hshadow, T, hcover, hbad⟩ :=
    hbridge hsp hlarge hwidth hclean
  refine ⟨T, ?_⟩
  have hD : 0 < bankTrialProbabilityC5WorkerDenominator q := by
    unfold bankTrialProbabilityC5WorkerDenominator
    exact Nat.pow_pos (by omega)
  have hbudget := bankTrialProbabilityC5WorkerBudget
    q hsp hwidth
  have hsplit := bankTrialProbabilityC5ShadowHeadMassSplit
    ring root S shadow hshadow T
  exact bankTrialProbabilityC5ShadowArithmetic
    hD hbudget hsplit hcover hbad

/-- Conditional transfer to the original theta target, using
the existing unconditional completed-head soundness theorem. -/
theorem bankTrialProbabilityThetaLowerOfShadowHeadWatchdog
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbridge : BankTrialProbabilityC5ShadowHeadWatchdog
      ring root S) :
    BankTrialProbabilityThetaLowerTarget ring root S :=
  bankTrialProbabilityThetaLowerOfCompletedHeadMass
    ring root S
    (bankTrialProbabilityC5CompletedHeadMassLowerOfShadowHeadWatchdog
      ring root S hbridge)

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Every actual CLEAN-reachable ARMED cut has an exactly fair
next root-port orientation at every finite scheduler horizon.
This does not claim that another ARMED cut is reached. -/
theorem bankTrialProbabilityC5ReachableArmedCutFair {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hgate : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)))
    (T : Nat) :
    bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T =
      bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) false T := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hlocked : BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) :=
    bankTrialC5LockedArbitraryWord ring root hw pre
      (bankTrialLocalStart S)
      (bankTrialLiveNoResetLockedStart S hclean)
  exact bankTrialProbabilityC5ArmedCutFair
    ring root hlarge
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    hlocked hgate T

/-- Pure Nat finite-horizon arithmetic. The large quantities are
opaque variables; no exponential is sent to omega or decide. -/
theorem bankTrialProbabilityC5HeadCoverageOpaque
    {C P H R X : Nat}
    (hpartition : P * H + R = X)
    (hremainder : C * R ≤ X) :
    C * X ≤ C * P * H + X := by
  calc
    C * X = C * (P * H + R) := by rw [hpartition]
    _ = C * P * H + C * R := by
      simp only [Nat.mul_add, Nat.mul_assoc]
    _ ≤ C * P * H + X :=
      Nat.add_le_add_left hremainder _

/-- FIRST MISSING FACT: a genuine adapted, possibly ghost-continued
shadow process must exhaust its K fair head labels. Its finite
truncations have a nonnegative unobserved mass R, with R/n^T
arbitrarily small. In particular, this is NOT a claim about the
first K raw root-port incidents: services while a worker is busy
are not authenticated head decisions.

The proved ArmedCutFair equality does not imply this statement
without return/progress at every adapted cut and a specified
continuation after a terminal worker failure. -/
def BankTrialProbabilityC5AdaptedShadowHeadExhaustion {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∀ C : Nat, 0 < C →
    ∃ T R : Nat,
      2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5ShadowHeadMass shadow T + R =
        n ^ T ∧
      C * R ≤ n ^ T

/-- Head half (A), conditional on the precise missing adapted
stopping-time exhaustion statement, at the required C=1024*D.
No worker rarity or head/timeout independence is assumed. -/
theorem bankTrialProbabilityC5HeadHalfOfExhaustion {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop)
    (hexhaust : BankTrialProbabilityC5AdaptedShadowHeadExhaustion
      ring root S shadow)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∃ T : Nat,
      1024 * bankTrialProbabilityC5WorkerDenominator q *
          n ^ T ≤
        1024 * bankTrialProbabilityC5WorkerDenominator q *
          2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5ShadowHeadMass shadow T +
          n ^ T := by
  have hden : 0 < bankTrialProbabilityC5WorkerDenominator q := by
    unfold bankTrialProbabilityC5WorkerDenominator
    exact Nat.pow_pos (by omega)
  have hC :
      0 < 1024 * bankTrialProbabilityC5WorkerDenominator q :=
    Nat.mul_pos (by omega) hden
  obtain ⟨T, R, hpartition, hremainder⟩ :=
    hexhaust hsp hlarge hwidth hclean
      (1024 * bankTrialProbabilityC5WorkerDenominator q) hC
  refine ⟨T, ?_⟩
  exact bankTrialProbabilityC5HeadCoverageOpaque
    hpartition hremainder

/-- A concrete BANK-observer adapter, not an assumed theorem
about the physically different Counter.ResetColdLatchedPrivateState.
In addition to actual BANK worker rarity and the all-word start cap,
this requires the head-weighted defect to be covered by the original
unconditional tagged timeout numerator at the SAME T.

The factor 2^K is essential. A pointwise inclusion of defect
words in timeout words alone does not imply this inequality. -/
def BankTrialProbabilityC5ShadowOriginAdapter {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∃ O : Type,
    ∃ starts : BankTrialLocalState q → Fin n → List O,
      ∃ timeout : O → List (Fin n) → Bool,
        BankTrialProbabilityC5WorkerRarity
          ring root starts timeout ∧
        BankTrialProbabilityC5WorkerStartCap
          ring root S starts ∧
        ∀ T : Nat,
          2 ^ (compileAdvice q).K *
              bankTrialProbabilityC5ShadowDefectMass
                ring root S shadow T ≤
            bankTrialProbabilityC5WorkerTimeoutMass
              ring root S starts timeout T

/-- Keep the original sharp D * timeout ≤ N * n^T * M bound.
The existing WorkerTimeoutTiny theorem loses this precision by
rounding directly to 1024 * timeout ≤ n^T. -/
theorem bankTrialProbabilityC5WorkerOriginUnionRaw {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    (starts : BankTrialLocalState q → Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (hrare : BankTrialProbabilityC5WorkerRarity
      ring root starts timeout)
    (hcap : BankTrialProbabilityC5WorkerStartCap
      ring root S starts)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
        bankTrialProbabilityC5WorkerTimeoutMass
          ring root S starts timeout T ≤
      bankTrialProbabilityC5WorkerNumerator q *
        (n ^ T * (2 * (compileAdvice q).K + 1)) := by
  have hfirst := Prob.origin_counting_le
    (bankTrialLocalNext ring root) bankTrialLocalTerminal
    starts timeout
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityC5WorkerDenominator q)
    hrare (bankTrialLocalStart S) T
  have hcount :
      Prob.originsNumerator
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          starts (bankTrialLocalStart S) T ≤
        n ^ T * (2 * (compileAdvice q).K + 1) := by
    change Prob.scheduleSum n T
        (Prob.originsWord
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          starts (bankTrialLocalStart S)) ≤
        n ^ T * (2 * (compileAdvice q).K + 1)
    calc
      _ ≤ Prob.scheduleSum n T
          (fun _ => 2 * (compileAdvice q).K + 1) := by
        apply bankTrialProbabilityScheduleSumMono
        intro w
        exact hcap w
      _ = n ^ T * (2 * (compileAdvice q).K + 1) :=
        bankTrialProbabilityScheduleSumConst
          n T (2 * (compileAdvice q).K + 1)
  unfold bankTrialProbabilityC5WorkerTimeoutMass
  exact Nat.le_trans hfirst
    (Nat.mul_le_mul_left
      (bankTrialProbabilityC5WorkerNumerator q) hcount)

/-- Defect half (B), conditional on the one explicit BANK
head-weighted origin adapter. This is an original-clock result,
with no independence assertion and no large-power arithmetic. -/
theorem bankTrialProbabilityC5DefectHalfOfOriginAdapter {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop)
    (hadapter : BankTrialProbabilityC5ShadowOriginAdapter
      ring root S shadow)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
        2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5ShadowDefectMass
          ring root S shadow T ≤
      (2 * (compileAdvice q).K + 1) *
        bankTrialProbabilityC5WorkerNumerator q * n ^ T := by
  obtain ⟨O, starts, timeout, hrare, hcap, hcover⟩ :=
    hadapter hsp hlarge hwidth hclean
  have hunion := bankTrialProbabilityC5WorkerOriginUnionRaw
    ring root S starts timeout hrare hcap T
  calc
    bankTrialProbabilityC5WorkerDenominator q *
        2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5ShadowDefectMass
          ring root S shadow T =
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5ShadowDefectMass
            ring root S shadow T) :=
      Nat.mul_assoc _ _ _
    _ ≤ bankTrialProbabilityC5WorkerDenominator q *
        bankTrialProbabilityC5WorkerTimeoutMass
          ring root S starts timeout T :=
      Nat.mul_le_mul_left _ (hcover T)
    _ ≤ bankTrialProbabilityC5WorkerNumerator q *
        (n ^ T * (2 * (compileAdvice q).K + 1)) := hunion
    _ = (2 * (compileAdvice q).K + 1) *
        bankTrialProbabilityC5WorkerNumerator q * n ^ T := by
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Assembly uses the SAME shadow in the head and defect halves.
In particular, it does not choose an arbitrary unrelated
raw-port cylinder and silently identify it with adapted heads. -/
theorem bankTrialProbabilityC5ShadowHeadWatchdogOfHeadAndOrigin
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (shadow : List (Fin n) → Prop)
    (hcontains : ∀ w : List (Fin n),
      bankTrialProbabilityC5CompletedHeadWord ring root S w →
        shadow w)
    (hexhaust : BankTrialProbabilityC5AdaptedShadowHeadExhaustion
      ring root S shadow)
    (hadapter : BankTrialProbabilityC5ShadowOriginAdapter
      ring root S shadow) :
    BankTrialProbabilityC5ShadowHeadWatchdog ring root S := by
  intro hsp hlarge hwidth hclean
  obtain ⟨T, hcover⟩ := bankTrialProbabilityC5HeadHalfOfExhaustion
    ring root S shadow hexhaust hsp hlarge hwidth hclean
  refine ⟨shadow, hcontains, T, hcover, ?_⟩
  exact bankTrialProbabilityC5DefectHalfOfOriginAdapter
    ring root S shadow hadapter hsp hlarge hwidth hclean T

end L3

namespace L3


open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting


set_option autoImplicit false
set_option Elab.async false


/-!
G11c forward chronological route.
No new transition row or protocol Prop.


The implicit O/starts/post/returned/badExit/timeout/increment/heads
are semantic observer data, not stored BANK coordinates. In particular
they must be supplied by a literal postservice worker-origin census.
This four-field structure is only the LOCAL kernel specification.
-/


structure BankTrialC5WorkerExcursionKernel {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    {starts : BankTrialLocalState q → Fin n → List O}
    {post : O → BankTrialLocalState q}
    {returned : O → BankTrialLocalState q → Prop}
    {badExit : O → BankTrialLocalState q → Prop}
    {timeout : O → List (Fin n) → Bool}
    {increment : O → Bool}
    {heads : O → Nat} : Prop where
  boundedMean :
    ∀ x : BankTrialLocalState q, ∀ e : Fin n, ∀ o : O,
      o ∈ starts x e →
        post o = bankTrialLocalNext ring root x e ∧
        ∀ T : Nat,
          costNumerator (bankTrialLocalNext ring root)
              (fun z => returned o z ∨ badExit o z)
              (post o) T ≤
            n ^ T * ((2 * (compileAdvice q).b + 2 + 1) * n)
  /-- An exit at u is the FIRST exit of this worker: no strict
  chronological prefix of u was already returned or badExit. -/
  nonreturnBad :
    ∀ x : BankTrialLocalState q, ∀ e : Fin n, ∀ o : O,
      o ∈ starts x e →
        ∀ u v : List (Fin n),
          (∀ pre tail : List (Fin n), ∀ f : Fin n,
            u = pre ++ (f :: tail) →
              ¬ (returned o
                   (bankTrialLocalRun ring root pre (post o)) ∨
                 badExit o
                   (bankTrialLocalRun ring root pre (post o)))) →
          (returned o
              (bankTrialLocalRun ring root u (post o)) ∨
            badExit o
              (bankTrialLocalRun ring root u (post o))) →
          ¬ returned o
              (bankTrialLocalRun ring root u (post o)) →
            timeout o (u ++ v) = true
  goodReturn :
    BankTrialProbabilityC5WorkerStartCap ring root S starts ∧
      ∀ x : BankTrialLocalState q, ∀ e : Fin n, ∀ o : O,
        o ∈ starts x e →
          ∀ w : List (Fin n),
            returned o
                (bankTrialLocalRun ring root w (post o)) →
              (if increment o then
                bankTrialLiveWaveRootMode
                    (bankTrialLocalRun ring root w (post o)).bank =
                  .CSTART
               else
                (heads o < (compileAdvice q).K ∧
                  BankTrialC5ArmedAt q
                    (bankTrialLocalRun ring root w (post o))
                    (heads o)) ∨
                (heads o = (compileAdvice q).K ∧
                  (bankTrialLocalRun ring root w
                    (post o)).phase = .won))
  conditionalRarity :
    BankTrialProbabilityC5WorkerRarity
      ring root starts timeout

  /-- Exactly the actual CLEAN-prefix root launches. A launch changes
  ARMED to IWAIT or CSTART to CWAIT and creates a fresh first token.
  The reverse clause excludes unrelated and forged origin records;
  the last clause excludes multiple copies of one origin. -/
  coverage :
    ∀ (hclean : BankTrialLocalClean q S)
      (pre : List (Fin n)) (z : BankTrialLocalState q),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      ∀ e : Fin n,
        ((e = root ∧
          ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
           (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .CWAIT)) ∧
          bankTrialLiveWaveToken z.bank
            ⟨0, bankTrialWindowWidthPos q⟩ = .E ∧
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z e).bank
            ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E) →
         ∃ o : O,
           o ∈ starts z e ∧
           post o = bankTrialLocalNext ring root z e ∧
           increment o =
             decide (bankTrialLiveWaveRootMode z.bank = .ARMED) ∧
           heads o =
             bankTrialLiveHeadCount ring root (pre ++ [e])
               (bankTrialLocalStart S)) ∧
        (∀ o : O, o ∈ starts z e →
          e = root ∧
          ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
           (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .CWAIT)) ∧
          bankTrialLiveWaveToken z.bank
            ⟨0, bankTrialWindowWidthPos q⟩ = .E ∧
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z e).bank
            ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E ∧
          post o = bankTrialLocalNext ring root z e ∧
          increment o =
            decide (bankTrialLiveWaveRootMode z.bank = .ARMED) ∧
          heads o =
            bankTrialLiveHeadCount ring root (pre ++ [e])
              (bankTrialLocalStart S)) ∧
        (starts z e).length ≤ 1

/-- The precise unconditional consequence of the rarity and
2K+1 origin-cap fields. This is NOT a head-conditioned estimate:
Prob.origin_counting_le has no factor 2^(-K). -/
theorem bankTrialC5WorkerExcursionOriginUnion
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    {starts : BankTrialLocalState q → Fin n → List O}
    {post : O → BankTrialLocalState q}
    {returned : O → BankTrialLocalState q → Prop}
    {badExit : O → BankTrialLocalState q → Prop}
    {timeout : O → List (Fin n) → Bool}
    {increment : O → Bool}
    {heads : O → Nat}
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := O) (starts := starts) (post := post)
      (returned := returned) (badExit := badExit)
      (timeout := timeout) (increment := increment)
      (heads := heads) ring root S)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
        bankTrialProbabilityC5WorkerTimeoutMass
          ring root S starts timeout T ≤
      bankTrialProbabilityC5WorkerNumerator q *
        (n ^ T * (2 * (compileAdvice q).K + 1)) := by
  exact bankTrialProbabilityC5WorkerOriginUnionRaw
    ring root S starts timeout
    hkernel.conditionalRarity hkernel.goodReturn.1 T


/-- Lemma 11, cancellation over OPAQUE naturals.
The input hstage is the finite-horizon forward chronological
Lemma 10; it must NOT be replaced by the unconditional union bound.
No exponent is evaluated by omega or decide. -/
theorem bankTrialC5ForwardOpaqueArithmetic
    {D N M P B T X E : Nat}
    (hD : 0 < D)
    (hT : 0 < T)
    (hbudget : 1024 * M * N < D)
    (hclock : 1024 * P * D * B ≤
      T * (D - 1024 * M * N))
    (hstage : D * T * X ≤
      D * T * (P * E) +
        (M * N * T + P * D * B) * X) :
    1023 * X ≤ 1024 * P * E := by
  have hcost :
      (D - 1024 * M * N) + 1024 * M * N = D :=
    Nat.sub_add_cancel (Nat.le_of_lt hbudget)
  have hfee :
      1024 * (M * N * T + P * D * B) ≤ D * T := by
    calc
      1024 * (M * N * T + P * D * B) =
          1024 * M * N * T + 1024 * P * D * B := by
        simp only [Nat.mul_add, Nat.mul_assoc]
      _ ≤ 1024 * M * N * T +
          T * (D - 1024 * M * N) :=
        Nat.add_le_add_left hclock _
      _ = ((D - 1024 * M * N) +
          1024 * M * N) * T := by
        rw [Nat.add_mul, Nat.add_comm (1024 * M * N * T),
          Nat.mul_comm T (D - 1024 * M * N)]
      _ = D * T := by rw [hcost]
  have hfeeX :
      1024 * (M * N * T + P * D * B) * X ≤
        (D * T) * X :=
    Nat.mul_le_mul_right X hfee
  have hscaled :
      1024 * (D * T) * X ≤
        1024 * (D * T) * (P * E) +
          1024 * (M * N * T + P * D * B) * X := by
    simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_le_mul_left 1024 hstage)
  have hmass :
      1024 * (D * T) * X ≤
        1024 * (D * T) * (P * E) + (D * T) * X :=
    Nat.le_trans hscaled (Nat.add_le_add_left hfeeX _)
  have hfactor :
      (D * T) * (1023 * X) + (D * T) * X =
        1024 * (D * T) * X := by
    calc
      (D * T) * (1023 * X) + (D * T) * X =
          (D * T) * ((1023 + 1) * X) := by
        simp only [Nat.add_mul, Nat.one_mul,
          Nat.mul_add, Nat.mul_assoc]
      _ = 1024 * (D * T) * X := by
        simp only [Nat.reduceAdd, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc]
  have hcancel :
      (D * T) * (1023 * X) + (D * T) * X ≤
        (D * T) * (1024 * (P * E)) +
          (D * T) * X := by
    calc
      (D * T) * (1023 * X) + (D * T) * X =
          1024 * (D * T) * X := hfactor
      _ ≤ 1024 * (D * T) * (P * E) +
          (D * T) * X := hmass
      _ = (D * T) * (1024 * (P * E)) +
          (D * T) * X := by
        simp only [Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc]
  have hmul :
      (D * T) * (1023 * X) ≤
        (D * T) * (1024 * (P * E)) := by
    omega
  have hpositive : 0 < D * T :=
    Nat.mul_pos hD hT
  have hfinal := Nat.le_of_mul_le_mul_left hmul hpositive
  simpa only [Nat.mul_assoc] using hfinal


/-- Construct a single *finite* horizon from the strict budget.
Here B is the complete success-or-abort staged-clock mean bound,
not the unbounded physical recovery clock. -/
theorem bankTrialC5ForwardOpaqueHorizon
    {D N M P B n : Nat}
    (hD : 0 < D)
    (hbudget : 1024 * M * N < D)
    (mass : Nat → Nat)
    (hstage : ∀ T : Nat, 0 < T →
      D * T * n ^ T ≤
        D * T * (P * mass T) +
          (M * N * T + P * D * B) * n ^ T) :
    ∃ T : Nat, 1023 * n ^ T ≤ 1024 * P * mass T := by
  have hgap : 1 ≤ D - 1024 * M * N := by
    omega
  have hTpos : 0 < 1024 * P * D * B + 1 := by
    omega
  have hclock : 1024 * P * D * B ≤
      (1024 * P * D * B + 1) *
        (D - 1024 * M * N) := by
    calc
      1024 * P * D * B ≤ 1024 * P * D * B + 1 := by
        omega
      _ = (1024 * P * D * B + 1) * 1 := by
        simp
      _ ≤ (1024 * P * D * B + 1) *
          (D - 1024 * M * N) :=
        Nat.mul_le_mul_left _ hgap
  refine ⟨1024 * P * D * B + 1, ?_⟩
  exact bankTrialC5ForwardOpaqueArithmetic
    hD hTpos hbudget hclock
    (hstage (1024 * P * D * B + 1) hTpos)


/-- Conditional final-horizon adapter. The hforward parameter
is precisely the still-unformalized Lemmas 7--10 stopped-tree
estimate; it is NOT a consequence of origin_counting_le alone. -/
theorem bankTrialProbabilityC5CompletedHeadMassLowerOfForwardEstimate
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hforward :
      (compileAdvice q).useSmall = false →
      2 * (compileAdvice q).bankLeaseCap ≤ n →
      (compileAdvice q).K < 2 ^ (compileAdvice q).b →
      BankTrialLocalClean q S →
      ∀ T : Nat, 0 < T →
        bankTrialProbabilityC5WorkerDenominator q *
          T * n ^ T ≤
          bankTrialProbabilityC5WorkerDenominator q *
            T * (2 ^ (compileAdvice q).K *
              bankTrialProbabilityC5CompletedHeadMass
                ring root S T) +
            ((2 * (compileAdvice q).K + 1) *
                bankTrialProbabilityC5WorkerNumerator q * T +
              2 ^ (compileAdvice q).K *
                bankTrialProbabilityC5WorkerDenominator q *
                (((compileAdvice q).K +
                  (2 * (compileAdvice q).K + 1) *
                    (2 * (compileAdvice q).b + 3)) * n)) *
                n ^ T) :
    BankTrialProbabilityC5CompletedHeadMassLower
      ring root S := by
  intro hsp hlarge hwidth hclean
  have hden : 0 < bankTrialProbabilityC5WorkerDenominator q := by
    unfold bankTrialProbabilityC5WorkerDenominator
    exact Nat.pow_pos (by omega)
  have hbudget := bankTrialProbabilityC5WorkerBudget
    q hsp hwidth
  exact bankTrialC5ForwardOpaqueHorizon
    (D := bankTrialProbabilityC5WorkerDenominator q)
    (N := bankTrialProbabilityC5WorkerNumerator q)
    (M := 2 * (compileAdvice q).K + 1)
    (P := 2 ^ (compileAdvice q).K)
    (B := (((compileAdvice q).K +
      (2 * (compileAdvice q).K + 1) *
        (2 * (compileAdvice q).b + 3)) * n))
    (n := n) hden hbudget
    (bankTrialProbabilityC5CompletedHeadMass ring root S)
    (hforward hsp hlarge hwidth hclean)


/-- The designated completion establishes a real attainable
CLEAN-origin winning word, not the universally quantified
worker mean, nonreturn classification, or rarity fields. -/
theorem bankTrialC5WorkerExcursionDesignatedWitness
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    (bankTrialC5CleanRun ring root S
      (bankTrialC5Rounds ring root
        (compileAdvice q).b bankTrialC5Trailing
        (compileAdvice q).K)).phase = .won := by
  exact (bankTrialProbabilityC5DesignatedCompletion
    ring root S hsp hlarge hclean).2


/-!
NOT PROVED HERE: bankTrialProbabilityC5CompletedHeadMassLowerOfKernel
and bankTrialProbabilityThetaLowerOfKernel. To add these without an
extra assumption, first prove the hforward stopped-tree estimate above
*from* the four kernel fields and full actual-origin coverage. The
unconditional origin-union inequality has no required 2^(-K) factor.
There is deliberately no sorry, axiom, or theorem claiming this gap
has been closed.
-/


end L3

namespace L3


open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting


set_option autoImplicit false
set_option Elab.async false


/-!
Postservice worker-origin data and phase-local rank arithmetic.
The C5 kernel itself is not asserted: its boundedMean, cap and
conditionalRarity fields still need a CLEAN-reachable excursion
certificate. No extra protocol row or axiom is introduced.
-/


/-- An actual physical-edge worker origin, including its postservice
state, local kind, and the postservice carried head count. -/
structure BankTrialC5ActualOrigin (n q : Nat) where
  before : BankTrialLocalState q
  edge : Fin n
  after : BankTrialLocalState q
  increment : Bool
  heads : Nat


/-- One origin is emitted exactly on a CLEAN-reachable outgoing root
service changing LIVE ARMED to LIVE IWAIT, or LIVE CSTART to LIVE CWAIT.
There is no origin on a mere ARMED-to-CSTART first-zero head. -/
noncomputable def bankTrialC5ActualStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n) :
    List (BankTrialC5ActualOrigin n q) :=
  if
    BankTrialLocalClean q S ∧
    (∃ w : List (Fin n),
      bankTrialLocalRun ring root w (bankTrialLocalStart S) = x) ∧
    e = root ∧
    (∃ begun nextBegun : Bool,
      x.phase = .live begun ∧
      (bankTrialLocalNext ring root x e).phase = .live nextBegun) ∧
    ((bankTrialLiveWaveRootMode x.bank = .ARMED ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x e).bank = .IWAIT) ∨
     (bankTrialLiveWaveRootMode x.bank = .CSTART ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x e).bank = .CWAIT))
  then
    [{ before := x,
       edge := e,
       after := bankTrialLocalNext ring root x e,
       increment :=
         (bankTrialLiveWaveRootMode
           (bankTrialLocalNext ring root x e).bank == .IWAIT),
       heads :=
         bankTrialLiveCarryValue
           (bankTrialLocalNext ring root x e).bank }]
  else []


/-- The recorded origin is the true selected postservice state. -/
theorem bankTrialC5ActualStartPost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (h : o ∈ bankTrialC5ActualStarts ring root S x e) :
    o.after = bankTrialLocalNext ring root x e := by
  unfold bankTrialC5ActualStarts at h
  split at h
  · simp only [List.mem_singleton] at h
    subst o
    rfl
  · simp at h


/-- The origin census never emits more than one tagged worker
for a single physical service. -/
theorem bankTrialC5ActualStartsLength {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n) :
    (bankTrialC5ActualStarts ring root S x e).length ≤ 1 := by
  unfold bankTrialC5ActualStarts
  split <;> simp


/-- Neither an interior service nor an incoming root edge can
fabricate one of the specified worker launch origins. -/
theorem bankTrialC5ActualStartAtRoot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (h : o ∈ bankTrialC5ActualStarts ring root S x e) :
    e = root := by
  unfold bankTrialC5ActualStarts at h
  split at h
  · rename_i hgood
    exact hgood.2.2.1
  · simp at h


/-- A matching increment return is LIVE CSTART.
A matching comparator return is an authorized ARMED cut before K,
or WON at the K-th completed head. -/
def bankTrialC5ActualReturned {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q) : Prop :=
  if o.increment then
    ∃ begun : Bool,
      z.phase = .live begun ∧
      bankTrialLiveWaveRootMode z.bank = .CSTART
  else
    (o.heads < (compileAdvice q).K ∧
      BankTrialC5ArmedAt q z o.heads) ∨
    (o.heads = (compileAdvice q).K ∧ z.phase = .won)


/-- This is the actual live IWAIT/CWAIT interval being resolved. -/
def bankTrialC5ActualWorkerActive {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, z.phase = .live begun) ∧
  bankTrialLiveWaveRootMode z.bank =
    (if o.increment then .IWAIT else .CWAIT)


/-- A nonmatching LIVE departure is an abort; the explicit
RECOVERY/LOST outcomes are bad exits. A wrong-head WON is a
classified invalid outcome, not an authorized comparator return. -/
def bankTrialC5ActualBadExit {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q) : Prop :=
  z.phase = .recovery ∨ z.phase = .lost ∨
  ((∃ begun : Bool, z.phase = .live begun) ∧
    ¬ bankTrialC5ActualWorkerActive o z ∧
    ¬ bankTrialC5ActualReturned o z) ∨
  (z.phase = .won ∧ ¬ bankTrialC5ActualReturned o z)


noncomputable def bankTrialC5ActualTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (word : List (Fin n)) : Bool :=
  decide (∃ pre tail : List (Fin n), ∃ e : Fin n,
    word = pre ++ (e :: tail) ∧
    (∀ before middle : List (Fin n), ∀ f : Fin n,
      pre = before ++ (f :: middle) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root before o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root before o.after))) ∧
    (∃ begun : Bool,
      (bankTrialLocalRun ring root pre o.after).phase =
        .live begun) ∧
    (bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre o.after).bank = .IWAIT ∨
     bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre o.after).bank = .CWAIT) ∧
    ((bankTrialLocalRun ring root pre o.after).bank.fields
      ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
    (e = root ∨ ring.rightNeighbor e = root) ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre o.after) e).bank = .RESET ∧
    (bankTrialLocalNext ring root
      (bankTrialLocalRun ring root pre o.after) e).phase ≠ .won ∧
    ¬ (bankTrialC5ActualReturned o
         (bankTrialLocalRun ring root pre o.after) ∨
       bankTrialC5ActualBadExit o
         (bankTrialLocalRun ring root pre o.after)))


/-- Phase-local rank: an IR no longer reserves the separate
comparison after the authorized increment return. -/
def bankTrialC5PhaseTokenRank (b j : Nat) : BTok → Nat
  | .E => 0
  | .RR => 0
  | .RL => 0
  | .IR => 2 * b + 3 - j
  | .AL => 1 + j
  | .CR0 => 2 * b + 2 - j
  | .CR1 => 2 * b + 2 - j
  | .CL0 => j
  | .CL1 => j


/-- Each authenticated digit-worker rank is <= 2b+2. -/
theorem bankTrialC5PhaseTokenRankCap
    (b j : Nat) (tok : BTok)
    (hlo : 1 ≤ j) (hhi : j ≤ b) :
    bankTrialC5PhaseTokenRank b j tok ≤ 2 * b + 2 := by
  cases tok <;> simp [bankTrialC5PhaseTokenRank] <;> omega


/-- IR either advances or turns to AL, decreasing local rank. -/
theorem bankTrialC5PhaseIncrementForwardRank
    (b j : Nat) (hlo : 1 ≤ j) (hhi : j + 1 ≤ b) :
    bankTrialC5PhaseTokenRank b (j + 1) .IR + 1 ≤
        bankTrialC5PhaseTokenRank b j .IR ∧
    bankTrialC5PhaseTokenRank b (j + 1) .AL + 1 ≤
        bankTrialC5PhaseTokenRank b j .IR := by
  simp [bankTrialC5PhaseTokenRank]
  omega


/-- The AL return consumes one nominated service. -/
theorem bankTrialC5PhaseIncrementReturnRank
    (b j : Nat) (hlo : 1 < j) (hhi : j ≤ b) :
    bankTrialC5PhaseTokenRank b (j - 1) .AL + 1 ≤
      bankTrialC5PhaseTokenRank b j .AL := by
  simp [bankTrialC5PhaseTokenRank]
  omega


/-- Both forward comparison token types pay exactly one step. -/
theorem bankTrialC5PhaseComparisonForwardRank
    (b j : Nat) (hlo : 1 ≤ j) (hhi : j + 1 ≤ b)
    (tok : BTok) (ht : tok = .CR0 ∨ tok = .CR1) :
    bankTrialC5PhaseTokenRank b (j + 1) tok + 1 ≤
      bankTrialC5PhaseTokenRank b j tok := by
  rcases ht with ht | ht <;>
    simp [ht, bankTrialC5PhaseTokenRank] <;> omega


/-- The top comparison turn and the CL backward edge pay. -/
theorem bankTrialC5PhaseComparisonReturnRank
    (b j : Nat) (hlo : 1 < j) (hhi : j ≤ b) :
    bankTrialC5PhaseTokenRank b (j - 1) .CL0 + 1 ≤
        bankTrialC5PhaseTokenRank b j .CL0 ∧
    bankTrialC5PhaseTokenRank b (j - 1) .CL1 + 1 ≤
        bankTrialC5PhaseTokenRank b j .CL1 ∧
    bankTrialC5PhaseTokenRank b (b - 1) .CL1 + 1 ≤
        bankTrialC5PhaseTokenRank b b .CR1 := by
  simp [bankTrialC5PhaseTokenRank]
  omega


/-- Precise remaining mathematical bridge to boundedMean:
original-edge nominated strict drift plus a start rank cap.
The hypotheses here are NOT claimed to follow from C.6's
aggregate CLEAN-start occupation bound alone. -/
theorem bankTrialC5ActualMeanOfNominatedRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (P : BankTrialLocalState q → Prop)
    (rank : BankTrialLocalState q → Nat)
    (chosen : BankTrialLocalState q → Fin n)
    (hdrop : ∀ z : BankTrialLocalState q, ¬ P z →
      rank (bankTrialLocalNext ring root z (chosen z)) + 1 ≤ rank z)
    (hnoninc : ∀ z : BankTrialLocalState q, ¬ P z →
      ∀ e : Fin n,
      rank (bankTrialLocalNext ring root z e) ≤ rank z)
    (hstart : rank o.after ≤ 2 * (compileAdvice q).b + 3)
    (T : Nat) :
    costNumerator (bankTrialLocalNext ring root)
        P o.after T ≤
      n ^ T * ((2 * (compileAdvice q).b + 3) * n) := by
  have hcost := Prob.costNumerator_le_of_nominated_edge
    (bankTrialLocalNext ring root) P rank chosen
    hdrop hnoninc o.after T
  calc
    costNumerator (bankTrialLocalNext ring root) P o.after T ≤
        n ^ T * (n * rank o.after) := hcost
    _ ≤ n ^ T * (n * (2 * (compileAdvice q).b + 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left n hstart)
    _ = n ^ T * ((2 * (compileAdvice q).b + 3) * n) := by
      rw [Nat.mul_comm n (2 * (compileAdvice q).b + 3)]


/-- Deterministic good-return shape, without reversing the
existing C.5 completed-head soundness theorem. -/
theorem bankTrialC5ActualReturnShape {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (h : bankTrialC5ActualReturned o z) :
    if o.increment then
      bankTrialLiveWaveRootMode z.bank = .CSTART
    else
      (o.heads < (compileAdvice q).K ∧
        BankTrialC5ArmedAt q z o.heads) ∨
      (o.heads = (compileAdvice q).K ∧ z.phase = .won) := by
  cases hi : o.increment with
  | false =>
      simpa [bankTrialC5ActualReturned, hi] using h
  | true =>
      have h' : ∃ begun : Bool,
          z.phase = .live begun ∧
          bankTrialLiveWaveRootMode z.bank = .CSTART := by
        unfold bankTrialC5ActualReturned at h
        rw [if_pos hi] at h
        exact h
      obtain ⟨_, _, hmode⟩ := h'
      rw [if_pos rfl]
      exact hmode


end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/--
A genuinely completed all-head word is included in the existing
C.5 numerator. The final WON fact is essential: K authenticated
outgoing heads alone can end while a comparator is not yet launched.
-/
theorem bankTrialC5FinishedAllGoodIncluded
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n))
    (hno : BankTrialNoArmedIncoming
      ring root w (bankTrialLocalStart S))
    (hheads : (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root w (bankTrialLocalStart S))
    (hwon : (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialProbabilityC5CompletedHeadWord ring root S w := by
  constructor
  · exact bankTrialHeadEventOfCount
      ring root w (compileAdvice q).K
      (bankTrialLocalStart S) hno hheads
  · exact Or.inl hwon

/--
The coverage field transfers a real root-launched worker into
the existing BANK-local truncated mean. This does not yet bound
workerless CSTART intervals or sum costs over stopped origins.
-/
theorem bankTrialC5KernelActualLaunchMean
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    {starts : BankTrialLocalState q → Fin n → List O}
    {post : O → BankTrialLocalState q}
    {returned : O → BankTrialLocalState q → Prop}
    {badExit : O → BankTrialLocalState q → Prop}
    {timeout : O → List (Fin n) → Bool}
    {increment : O → Bool}
    {heads : O → Nat}
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := O) (starts := starts) (post := post)
      (returned := returned) (badExit := badExit)
      (timeout := timeout) (increment := increment)
      (heads := heads) ring root S)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n)
    (hlaunch :
      e = root ∧
      ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
       (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root z e).bank = .CWAIT)) ∧
      bankTrialLiveWaveToken z.bank
        ⟨0, bankTrialWindowWidthPos q⟩ = .E ∧
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root z e).bank
        ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E)
    (T : Nat) :
    ∃ o : O,
      o ∈ starts z e ∧
      post o = bankTrialLocalNext ring root z e ∧
      increment o =
        decide (bankTrialLiveWaveRootMode z.bank = .ARMED) ∧
      heads o = bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S) ∧
      costNumerator (bankTrialLocalNext ring root)
          (fun zz => returned o zz ∨ badExit o zz)
          (post o) T ≤
        n ^ T * ((2 * (compileAdvice q).b + 2 + 1) * n) := by
  obtain ⟨o, ho, hp, hi, hh⟩ :=
    (hkernel.coverage hclean pre z hz e).1 hlaunch
  have hm := (hkernel.boundedMean z e o ho).2 T
  exact ⟨o, ho, hp, hi, hh, hm⟩

/-- No origin can be attached to an unserved or unrelated edge
on an actual CLEAN-origin prefix. -/
theorem bankTrialC5KernelNoSpuriousOrigin
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    {starts : BankTrialLocalState q → Fin n → List O}
    {post : O → BankTrialLocalState q}
    {returned : O → BankTrialLocalState q → Prop}
    {badExit : O → BankTrialLocalState q → Prop}
    {timeout : O → List (Fin n) → Bool}
    {increment : O → Bool}
    {heads : O → Nat}
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := O) (starts := starts) (post := post)
      (returned := returned) (badExit := badExit)
      (timeout := timeout) (increment := increment)
      (heads := heads) ring root S)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : O) (ho : o ∈ starts z e) :
    e = root ∧
    post o = bankTrialLocalNext ring root z e ∧
    increment o =
      decide (bankTrialLiveWaveRootMode z.bank = .ARMED) ∧
    heads o = bankTrialLiveHeadCount ring root (pre ++ [e])
      (bankTrialLocalStart S) := by
  obtain ⟨he, _, _, _, hp, hi, hh⟩ :=
    (hkernel.coverage hclean pre z hz e).2.1 o ho
  exact ⟨he, hp, hi, hh⟩

/--
COUNTEREXAMPLE to the unqualified Lemma 7 implication:
truncate the C3 designated schedule immediately after the
Kth outgoing root head, with even pre-head value K-1.
Every earlier designated round ended ARMED with no live worker,
but the last root service enters LIVE/CSTART with no token.
The final comparison has not even been launched.

In particular, "all launched workers returned" is insufficient
without a final comparator-completion/terminal condition.
-/
theorem bankTrialC5LastZeroHeadIsPending
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hKone : 1 ≤ (compileAdvice q).K)
    (hzero : bankTrialC5Trailing
      ((compileAdvice q).K - 1) = 0) :
    ∃ w : List (Fin n),
      bankTrialLiveHeadCount ring root w
          (bankTrialLocalStart S) = (compileAdvice q).K ∧
      (∃ begun : Bool,
        (bankTrialC5CleanRun ring root S w).phase =
          .live begun ∧
        bankTrialLiveWaveRootMode
          (bankTrialC5CleanRun ring root S w).bank = .CSTART ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialC5CleanRun ring root S w).bank j = .E)) ∧
      ¬ bankTrialProbabilityC5CompletedHeadWord
        ring root S w := by
  have hstrict :
      (compileAdvice q).K - 1 < (compileAdvice q).K := by
    omega
  have hbefore : BankTrialC5ArmedAt q
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1)))
      ((compileAdvice q).K - 1) :=
    (bankTrialProbabilityC5DesignatedCompletion
      ring root S hsp hlarge hclean).1
      ((compileAdvice q).K - 1) hstrict
  obtain ⟨begun, hphase, hmode, htoks,
    hvalue, hsuccess, hlock⟩ := hbefore
  have hbound :
      ((compileAdvice q).K - 1) + 1 <
        2 ^ (compileAdvice q).b := by
    rw [Nat.sub_add_cancel hKone]
    exact hwidth
  have htrail := bankTrialC5TrailingFromBinary
    (bankTrialC5CleanRun ring root S
      (bankTrialC5Rounds ring root
        (compileAdvice q).b bankTrialC5Trailing
        ((compileAdvice q).K - 1))).bank
    ((compileAdvice q).K - 1) hvalue hbound
  rw [hzero] at htrail
  have hbit : bankTrialLiveWaveBit
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1))).bank
      ⟨0, bankTrialWindowWidthPos q⟩ = false :=
    htrail.2.2
      (⟨0, bankTrialWindowWidthPos q⟩ :
        Fin (compileAdvice q).b) rfl
  have hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1))) :=
    ⟨bankTrialProbabilityUpperWindow hlarge, hlock,
      ⟨begun, hphase⟩, hsuccess, hmode, htoks⟩
  have hlast := bankTrialC5ArmedHeadZeroCStart ring root
    (bankTrialC5CleanRun ring root S
      (bankTrialC5Rounds ring root
        (compileAdvice q).b bankTrialC5Trailing
        ((compileAdvice q).K - 1))) hstart hbit
  obtain ⟨nextBegun, hnextLive⟩ := hlast.live
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart
      S (by omega) hclean)
    (bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S
      (bankTrialC5RemainingLiveRowsHolds
        ring root hlarge hwidth))
    (bankTrialC5Rounds ring root
      (compileAdvice q).b bankTrialC5Trailing
      ((compileAdvice q).K - 1))
  have hpreCount :
      bankTrialLiveHeadCount ring root
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1))
          (bankTrialLocalStart S) =
        (compileAdvice q).K - 1 := by
    have hcarry := hInv.liveCarry begun hphase
    have hb := bankTrialC5NoWorkerCarryBinary
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1))).bank htoks
    simp only [bankTrialC5CleanRun] at hb hvalue hcarry ⊢
    rw [hb, hvalue] at hcarry
    exact hcarry.symm
  have hgate : BankTrialProbabilityArmedGate
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1))) :=
    ⟨⟨begun, hphase⟩, hmode⟩
  have honeCount :
      bankTrialLiveHeadCount ring root [root]
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1))) = 1 := by
    change
      (if BankTrialProbabilityArmedGate
          (bankTrialC5CleanRun ring root S
            (bankTrialC5Rounds ring root
              (compileAdvice q).b bankTrialC5Trailing
              ((compileAdvice q).K - 1))) ∧ root = root
       then 1 else 0) + 0 = 1
    rw [if_pos ⟨hgate, rfl⟩]
  have hcount :
      bankTrialLiveHeadCount ring root
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1) ++ [root])
        (bankTrialLocalStart S) = (compileAdvice q).K := by
    rw [bankTrialLiveHeadCountAppend]
    change
      bankTrialLiveHeadCount ring root
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1))
          (bankTrialLocalStart S) +
        bankTrialLiveHeadCount ring root [root]
          (bankTrialC5CleanRun ring root S
            (bankTrialC5Rounds ring root
              (compileAdvice q).b bankTrialC5Trailing
              ((compileAdvice q).K - 1))) = (compileAdvice q).K
    rw [hpreCount, honeCount]
    exact Nat.sub_add_cancel hKone
  have hpostLive :
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing
          ((compileAdvice q).K - 1) ++ [root])).phase =
          .live nextBegun := by
    rw [bankTrialC5CleanRunAppend]
    change
      (bankTrialLocalNext ring root
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1))) root).phase =
        .live nextBegun
    exact hnextLive
  have hpostMode :
      bankTrialLiveWaveRootMode
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1) ++ [root])).bank =
        .CSTART := by
    rw [bankTrialC5CleanRunAppend]
    change bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1))) root).bank = .CSTART
    exact hlast.cstart
  have hpostEmpty :
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialC5CleanRun ring root S
            (bankTrialC5Rounds ring root
              (compileAdvice q).b bankTrialC5Trailing
              ((compileAdvice q).K - 1) ++ [root])).bank j = .E := by
    intro j
    rw [bankTrialC5CleanRunAppend]
    change bankTrialLiveWaveToken
      (bankTrialLocalNext ring root
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing
            ((compileAdvice q).K - 1))) root).bank j = .E
    exact hlast.empty j
  refine ⟨bankTrialC5Rounds ring root
    (compileAdvice q).b bankTrialC5Trailing
    ((compileAdvice q).K - 1) ++ [root],
    hcount, ⟨nextBegun, hpostLive, hpostMode, hpostEmpty⟩, ?_⟩
  intro hc
  have hw := bankTrialProbabilityC5CompletedHeadSoundHolds
    ring root S hsp hlarge hwidth hclean
    (bankTrialC5Rounds ring root
      (compileAdvice q).b bankTrialC5Trailing
      ((compileAdvice q).K - 1) ++ [root]) hc
  change
    (bankTrialC5CleanRun ring root S
      (bankTrialC5Rounds ring root
        (compileAdvice q).b bankTrialC5Trailing
        ((compileAdvice q).K - 1) ++ [root])).phase = .won at hw
  rw [hpostLive] at hw
  cases hw

/-- Small closed advice check: K(80)=2*80+17=177, which is odd. -/
theorem bankTrialC5ThresholdAtEighty :
    (compileAdvice 80).K = 177 := by
  decide

theorem bankTrialC5TrailingAtEighty :
    bankTrialC5Trailing ((compileAdvice 80).K - 1) = 0 := by
  rw [bankTrialC5ThresholdAtEighty, bankTrialC5Trailing]
  simp

/-- A fully explicit compiled large-band instance of the pending
K-head prefix; its designated earlier rounds really return ARMED. -/
theorem bankTrialC5EightyPendingCounterexample
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice 80).b)
    (hlarge : 2 * (compileAdvice 80).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean 80 S) :
    ∃ w : List (Fin n),
      bankTrialLiveHeadCount ring root w
          (bankTrialLocalStart S) = (compileAdvice 80).K ∧
      (∃ begun : Bool,
        (bankTrialC5CleanRun ring root S w).phase =
          .live begun ∧
        bankTrialLiveWaveRootMode
          (bankTrialC5CleanRun ring root S w).bank = .CSTART ∧
        (∀ j : Fin (compileAdvice 80).b,
          bankTrialLiveWaveToken
            (bankTrialC5CleanRun ring root S w).bank j = .E)) ∧
      ¬ bankTrialProbabilityC5CompletedHeadWord
        ring root S w := by
  have hsp : (compileAdvice 80).useSmall = false := by
    decide
  have hKone : 1 ≤ (compileAdvice 80).K := by
    rw [bankTrialC5ThresholdAtEighty]
    omega
  exact bankTrialC5LastZeroHeadIsPending
    ring root S hsp hlarge
    (by have := compileAdvice_K_lt_two_pow_b 80 (by omega); omega)
    hclean hKone bankTrialC5TrailingAtEighty

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/--
At every actual CLEAN-reachable LIVE/CSTART cut, the selected
outgoing root edge launches the comparator and reaches LIVE/CWAIT.
This works from an arbitrary reachable prefix, not only C3's
designated word.
-/
theorem bankTrialC5CStartRootLaunchAtReachable
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (z : BankTrialLocalState q) (begun : Bool)
    (hreach : z =
      bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode z.bank = .CSTART) :
    BankTrialCmpCRStage z.bank 0
      (bankTrialLocalNext ring root z root) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hlivePre :
      (bankTrialC5CleanRun ring root S pre).phase =
        .live begun := by
    change (bankTrialLocalRun ring root pre
      (bankTrialLocalStart S)).phase = .live begun
    rw [← hreach]
    exact hlive
  have hmodePre :
      bankTrialLiveWaveRootMode
        (bankTrialC5CleanRun ring root S pre).bank =
        .CSTART := by
    change bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank = .CSTART
    rw [← hreach]
    exact hmode
  have htoken :
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j = .E := by
    intro j
    have hj := bankTrialC5CleanCStartTokensEmpty
      ring root hw S hclean pre begun
      hlivePre hmodePre j
    change bankTrialLiveWaveToken
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank j = .E at hj
    rw [← hreach] at hj
    exact hj
  have hzeta :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    cases z with
    | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      rfl
  have hactual :
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    rw [← hreach]
    exact hzeta
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean pre z.bank begun hactual
  exact bankTrialCmpLaunch
    ring root hw z ⟨begun, hlive⟩ hf hmode htoken

/--
Original-clock truncated mean for the workerless CSTART interval.
The stop is EXIT from the actual CLEAN-reachable LIVE/CSTART class,
including an early non-CSTART/terminal exit. Its rank is one and
the nominated physical root edge strictly reduces it.
-/
theorem bankTrialC5CStartInterstageMean
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hstart :
      ∃ pre : List (Fin n), ∃ begun : Bool,
        z = bankTrialLocalRun ring root pre
          (bankTrialLocalStart S) ∧
        z.phase = .live begun ∧
        bankTrialLiveWaveRootMode z.bank = .CSTART)
    (T : Nat) :
    costNumerator (bankTrialLocalNext ring root)
      (fun x : BankTrialLocalState q =>
        ¬ ∃ pre : List (Fin n), ∃ begun : Bool,
          x = bankTrialLocalRun ring root pre
            (bankTrialLocalStart S) ∧
          x.phase = .live begun ∧
          bankTrialLiveWaveRootMode x.bank = .CSTART)
      z T ≤ n ^ T * n := by
  classical
  have hdrop :
      ∀ x : BankTrialLocalState q,
        ¬ (¬ ∃ pre : List (Fin n), ∃ begun : Bool,
          x = bankTrialLocalRun ring root pre
            (bankTrialLocalStart S) ∧
          x.phase = .live begun ∧
          bankTrialLiveWaveRootMode x.bank = .CSTART) →
        (if bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root x root).bank = .CSTART
         then 1 else 0) + 1 ≤
          (if bankTrialLiveWaveRootMode x.bank = .CSTART
           then 1 else 0) := by
    intro x hx
    by_cases ha :
        ∃ pre : List (Fin n), ∃ begun : Bool,
          x = bankTrialLocalRun ring root pre
            (bankTrialLocalStart S) ∧
          x.phase = .live begun ∧
          bankTrialLiveWaveRootMode x.bank = .CSTART
    · obtain ⟨pre, begun, hreach, hlive, hmode⟩ := ha
      have hlaunch := bankTrialC5CStartRootLaunchAtReachable
        ring root S hlarge hclean pre x begun
        hreach hlive hmode
      have hwait :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root x root).bank =
            .CWAIT := hlaunch.2.2.1
      have hne :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root x root).bank ≠
            .CSTART := by
        intro h
        rw [hwait] at h
        cases h
      rw [if_neg hne, if_pos hmode]
      omega
    · exact False.elim (hx ha)
  have hnoninc :
      ∀ x : BankTrialLocalState q,
        ¬ (¬ ∃ pre : List (Fin n), ∃ begun : Bool,
          x = bankTrialLocalRun ring root pre
            (bankTrialLocalStart S) ∧
          x.phase = .live begun ∧
          bankTrialLiveWaveRootMode x.bank = .CSTART) →
        ∀ e : Fin n,
          (if bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root x e).bank = .CSTART
           then 1 else 0) ≤
            (if bankTrialLiveWaveRootMode x.bank = .CSTART
             then 1 else 0) := by
    intro x hx e
    by_cases ha :
        ∃ pre : List (Fin n), ∃ begun : Bool,
          x = bankTrialLocalRun ring root pre
            (bankTrialLocalStart S) ∧
          x.phase = .live begun ∧
          bankTrialLiveWaveRootMode x.bank = .CSTART
    · obtain ⟨pre, begun, hreach, hlive, hmode⟩ := ha
      rw [if_pos hmode]
      split <;> omega
    · exact False.elim (hx ha)
  have hcost := Prob.costNumerator_le_of_nominated_edge
    (bankTrialLocalNext ring root)
    (fun x : BankTrialLocalState q =>
      ¬ ∃ pre : List (Fin n), ∃ begun : Bool,
        x = bankTrialLocalRun ring root pre
          (bankTrialLocalStart S) ∧
        x.phase = .live begun ∧
        bankTrialLiveWaveRootMode x.bank = .CSTART)
    (fun x : BankTrialLocalState q =>
      if bankTrialLiveWaveRootMode x.bank = .CSTART
      then 1 else 0)
    (fun _ : BankTrialLocalState q => root)
    hdrop hnoninc z T
  obtain ⟨pre, begun, hreach, hlive, hmode⟩ := hstart
  simpa only [if_pos hmode, Nat.mul_one] using hcost

/--
Pure opaque-Nat accounting for ONE finite head-cut stage.
H and F are the first HEAD and TAIL masses; Q is pending
before any decision. G, Bad, R split the HEAD mass into
good completion, classified bad exit and unresolved work.
This arithmetic does NOT construct that stopped-prefix partition.
-/
theorem bankTrialC5OneStageFairRarityArithmetic
    {D N X H F Q G Bad R : Nat}
    (hfair : H = F)
    (hpartition : X = H + F + Q)
    (hgood : H ≤ G + Bad + R)
    (hbad : D * Bad ≤ N * X) :
    D * X ≤
      (2 * D * G + 2 * N * X) + (D * Q + 2 * D * R) := by
  have hcover : X ≤ 2 * (G + Bad + R) + Q := by
    omega
  have hscaled :
      D * X ≤ D * (2 * (G + Bad + R) + Q) :=
    Nat.mul_le_mul_left D hcover
  have hbadtwice : 2 * D * Bad ≤ 2 * N * X := by
    simpa only [Nat.mul_assoc] using
      (Nat.mul_le_mul_left 2 hbad)
  calc
    D * X ≤ D * (2 * (G + Bad + R) + Q) := hscaled
    _ = (2 * D * G + 2 * D * Bad) +
          (D * Q + 2 * D * R) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ (2 * D * G + 2 * N * X) +
          (D * Q + 2 * D * R) :=
      Nat.add_le_add_right
        (Nat.add_le_add_left hbadtwice (2 * D * G))
        (D * Q + 2 * D * R)

/--
Exact starting state/edge where a head is not a worker launch:
the first CLEAN outgoing root service goes to LIVE/CSTART,
with all private worker tokens empty. A further root service
is needed to launch the comparator.
-/
theorem bankTrialC5CleanFirstHeadInterstage
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    (bankTrialLocalNext ring root
        (bankTrialLocalStart S) root).phase = .live true ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (bankTrialLocalStart S) root).bank = .CSTART ∧
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root
          (bankTrialLocalStart S) root).bank j = .E) := by
  have hhead := bankTrialProbabilityCleanHeadCStart
    ring root S hclean
  have hphase :
      (bankTrialC5CleanRun ring root S [root]).phase =
        .live true := by
    change (bankTrialLocalNext ring root
      (bankTrialLocalStart S) root).phase = .live true
    rw [hhead.2.2]
  have hmode :
      bankTrialLiveWaveRootMode
        (bankTrialC5CleanRun ring root S [root]).bank =
        .CSTART := by
    change bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (bankTrialLocalStart S) root).bank = .CSTART
    rw [hhead.2.2]
    exact hhead.2.1
  have htoks := bankTrialC5CleanCStartTokensEmpty
    ring root (bankTrialProbabilityUpperWindow hlarge)
    S hclean [root] true hphase hmode
  refine ⟨?_, ?_, ?_⟩
  · change (bankTrialC5CleanRun ring root S [root]).phase =
      .live true
    exact hphase
  · change bankTrialLiveWaveRootMode
      (bankTrialC5CleanRun ring root S [root]).bank =
        .CSTART
    exact hmode
  · intro j
    change bankTrialLiveWaveToken
      (bankTrialC5CleanRun ring root S [root]).bank j = .E
    exact htoks j

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Four exclusive outcomes of the first incident root decision,
followed by the FIRST actual worker origin on a HEAD branch. -/
inductive BankTrialC5StageCase where
  | tail | good | bad | pending
  deriving DecidableEq

/-- First matching return, first classified bad exit, or no
resolution yet for one selected postservice origin. -/
noncomputable def bankTrialC5WorkerFirstExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    List (Fin n) → BankTrialLocalState q → Option Bool
  | [], z =>
      if bankTrialC5ActualReturned o z then some true
      else if bankTrialC5ActualBadExit o z then some false
      else none
  | e :: w, z =>
      if bankTrialC5ActualReturned o z then some true
      else if bankTrialC5ActualBadExit o z then some false
      else bankTrialC5WorkerFirstExit ring root o w
        (bankTrialLocalNext ring root z e)

/-- Scan for the first launched worker on the HEAD branch.
A workerless CSTART cut is charged to this waiting scan. -/
noncomputable def bankTrialC5PostHeadFirstExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    List (Fin n) → BankTrialLocalState q → Option Bool
  | [], _ => none
  | e :: w, z =>
      match bankTrialC5ActualStarts ring root S z e with
      | [] =>
          bankTrialC5PostHeadFirstExit ring root S w
            (bankTrialLocalNext ring root z e)
      | o :: _ =>
          bankTrialC5WorkerFirstExit ring root o w
            (bankTrialLocalNext ring root z e)

/-- Consume unrelated letters until the first physical incident.
A first incoming letter makes this a TAIL, not a bad worker. -/
noncomputable def bankTrialC5PreHeadFirstExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    List (Fin n) → BankTrialLocalState q → Option Bool
  | [], _ => none
  | e :: w, z =>
      if e = root then
        match bankTrialC5ActualStarts ring root S z e with
        | [] =>
            bankTrialC5PostHeadFirstExit ring root S w
              (bankTrialLocalNext ring root z e)
        | o :: _ =>
            bankTrialC5WorkerFirstExit ring root o w
              (bankTrialLocalNext ring root z e)
      else if e = ring.leftNeighbor root then none
      else bankTrialC5PreHeadFirstExit ring root S w
        (bankTrialLocalNext ring root z e)

/-- Canonical four-way classification of the length-T original
scheduler word. Pending includes no first incident, CSTART waiting,
and a launched worker still unresolved at time T. -/
noncomputable def bankTrialC5StageClass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) :
    BankTrialC5StageCase :=
  if bankTrialProbabilityFirstIncidentOrientation
      root (ring.leftNeighbor root) w = some false then .tail
  else if bankTrialC5PreHeadFirstExit ring root S w x = some true
    then .good
  else if bankTrialC5PreHeadFirstExit ring root S w x = some false
    then .bad
  else .pending

/-- The four required Boolean predicates share one classifier. -/
noncomputable def bankTrialC5StageClassBool {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q)
    (w : List (Fin n)) (c : BankTrialC5StageCase) : Bool :=
  if bankTrialC5StageClass ring root S x w = c then true
  else false

def bankTrialC5StageIndicator
    (c d : BankTrialC5StageCase) : Nat :=
  if c = d then 1 else 0

/-- The four ORIGINAL-clock class numerators. -/
noncomputable def bankTrialC5StageMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat)
    (c : BankTrialC5StageCase) : Nat :=
  Prob.scheduleSum n T (fun w =>
    bankTrialC5StageIndicator
      (bankTrialC5StageClass ring root S x w) c)

theorem bankTrialC5StageIndicatorPartition
    (c : BankTrialC5StageCase) :
    bankTrialC5StageIndicator c .tail +
      bankTrialC5StageIndicator c .good +
      bankTrialC5StageIndicator c .bad +
      bankTrialC5StageIndicator c .pending = 1 := by
  cases c <;> rfl

/-- Original-scheduler additive word counting. -/
theorem bankTrialC5ScheduleSumAdd {n : Nat}
    (T : Nat) (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => f w + g w) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  induction T generalizing f g with
  | zero =>
      rw [bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero]
  | succ T ih =>
      rw [bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      rw [← ofFn_sum_add]
      apply ofFn_sum_eq
      intro e
      exact ih (fun w => f (e :: w))
        (fun w => g (e :: w))

/-- An arbitrary four-class map partitions every length-T tape. -/
theorem bankTrialC5FourClassMass {n : Nat} (T : Nat)
    (classify : List (Fin n) → BankTrialC5StageCase) :
    Prob.scheduleSum n T (fun w =>
        bankTrialC5StageIndicator (classify w) .tail) +
      Prob.scheduleSum n T (fun w =>
        bankTrialC5StageIndicator (classify w) .good) +
      Prob.scheduleSum n T (fun w =>
        bankTrialC5StageIndicator (classify w) .bad) +
      Prob.scheduleSum n T (fun w =>
        bankTrialC5StageIndicator (classify w) .pending) =
      n ^ T := by
  calc
    _ = Prob.scheduleSum n T (fun w =>
        ((bankTrialC5StageIndicator (classify w) .tail +
          bankTrialC5StageIndicator (classify w) .good) +
          bankTrialC5StageIndicator (classify w) .bad) +
          bankTrialC5StageIndicator (classify w) .pending) := by
      rw [bankTrialC5ScheduleSumAdd,
        bankTrialC5ScheduleSumAdd,
        bankTrialC5ScheduleSumAdd]
    _ = Prob.scheduleSum n T (fun _ => 1) := by
      have heq :
          (fun w : List (Fin n) =>
            ((bankTrialC5StageIndicator (classify w) .tail +
              bankTrialC5StageIndicator (classify w) .good) +
              bankTrialC5StageIndicator (classify w) .bad) +
              bankTrialC5StageIndicator (classify w) .pending) =
            (fun _ => 1) := by
        funext w
        exact bankTrialC5StageIndicatorPartition (classify w)
      rw [heq]
    _ = n ^ T := by
      simpa only [Nat.mul_one] using
        (bankTrialProbabilityScheduleSumConst n T 1)

/-- The requested four masses sum to n^T, without any independence
or kernel-field premise. -/
theorem bankTrialC5FourStageMassPartition
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialC5StageMass ring root S x T .tail +
      bankTrialC5StageMass ring root S x T .good +
      bankTrialC5StageMass ring root S x T .bad +
      bankTrialC5StageMass ring root S x T .pending =
        n ^ T := by
  unfold bankTrialC5StageMass
  exact bankTrialC5FourClassMass T
    (bankTrialC5StageClass ring root S x)

/-- Class TAIL is exactly the first physical incoming incident. -/
theorem bankTrialC5StageTailEqFirstIncident
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialC5StageMass ring root S x T .tail =
      bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) false T := by
  unfold bankTrialC5StageMass
    bankTrialProbabilityFirstIncidentMass
  have heq :
      (fun w : List (Fin n) =>
        bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S x w) .tail) =
      (fun w : List (Fin n) =>
        if bankTrialProbabilityFirstIncidentOrientation
            root (ring.leftNeighbor root) w = some false
        then 1 else 0) := by
    funext w
    unfold bankTrialC5StageIndicator bankTrialC5StageClass
    split
    · simp
    · split <;> split <;> (try simp) <;> (rename_i h; cases h)
  rw [heq]

/-- At an actual CLEAN-reachable ARMED gate the first-TAIL class
and the entire first-HEAD branch have equal finite-horizon mass. -/
theorem bankTrialC5StageTailHeadFair
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate x)
    (T : Nat) :
    bankTrialC5StageMass ring root S x T .tail =
      bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T := by
  have hlocked : BankTrialLiveNoResetLocked x := by
    rw [hreach]
    exact bankTrialWindowLockedCleanWords
      ring root (bankTrialProbabilityUpperWindow hlarge)
      S hclean pre
  calc
    bankTrialC5StageMass ring root S x T .tail =
      bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) false T :=
      bankTrialC5StageTailEqFirstIncident ring root S x T
    _ = bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T :=
      (bankTrialProbabilityLockedArmedFirstIncidentFair
        ring root hlarge x hlocked hgate T).symm

theorem bankTrialC5WorkerBadHasPrefix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialC5WorkerFirstExit ring root o w z = some false →
      ∃ u v : List (Fin n),
        w = u ++ v ∧
        bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root u z) ∧
        ¬ bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root u z) ∧
        (∀ pre tail : List (Fin n), ∀ f : Fin n,
          u = pre ++ (f :: tail) →
            ¬ (bankTrialC5ActualReturned o
                 (bankTrialLocalRun ring root pre z) ∨
               bankTrialC5ActualBadExit o
                 (bankTrialLocalRun ring root pre z))) := by
  intro w
  induction w with
  | nil =>
    intro z h
    have hr : ¬ bankTrialC5ActualReturned o z := by
      intro hret
      simp [bankTrialC5WorkerFirstExit, hret] at h
    have hb : bankTrialC5ActualBadExit o z := by
      by_cases hbad : bankTrialC5ActualBadExit o z
      · exact hbad
      · simp [bankTrialC5WorkerFirstExit, hr, hbad] at h
    refine ⟨[], [], rfl, hb, hr, ?_⟩
    intro pre tail f hpre
    cases pre with
    | nil => cases hpre
    | cons a pre => cases hpre
  | cons e w ih =>
    intro z h
    by_cases hr : bankTrialC5ActualReturned o z
    · simp [bankTrialC5WorkerFirstExit, hr] at h
    · by_cases hb : bankTrialC5ActualBadExit o z
      · refine ⟨[], e :: w, rfl, hb, hr, ?_⟩
        intro pre tail f hpre
        cases pre with
        | nil => cases hpre
        | cons a pre => cases hpre
      · have htail :
            bankTrialC5WorkerFirstExit ring root o w
              (bankTrialLocalNext ring root z e) = some false := by
          simpa only [bankTrialC5WorkerFirstExit,
            if_neg hr, if_neg hb] using h
        obtain ⟨u, v, hu, hbad, hnot, hprior⟩ :=
          ih (bankTrialLocalNext ring root z e) htail
        refine ⟨e :: u, v, ?_, ?_, ?_, ?_⟩
        · simpa only [List.cons_append] using
            congrArg (List.cons e) hu
        · change bankTrialC5ActualBadExit o
            (bankTrialLocalRun ring root u
              (bankTrialLocalNext ring root z e))
          exact hbad
        · change ¬ bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root u
              (bankTrialLocalNext ring root z e))
          exact hnot
        · intro pre tail f hpre
          cases pre with
          | nil =>
            intro hcase
            rcases hcase with hreturn | hbad
            · exact hr hreturn
            · exact hb hbad
          | cons d pre =>
            simp only [List.cons_append, List.cons.injEq] at hpre
            have hed : e = d := hpre.1
            have hu : u = pre ++ (f :: tail) := hpre.2
            cases hed
            change ¬ (bankTrialC5ActualReturned o
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalNext ring root z e)) ∨
              bankTrialC5ActualBadExit o
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalNext ring root z e)))
            exact hprior pre tail f hu

theorem bankTrialC5FirstBadImpliesTimeout
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (z : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S z e)
    (w : List (Fin n))
    (hb : bankTrialC5WorkerFirstExit ring root o w o.after =
      some false) :
    bankTrialC5ActualTimeout ring root o w = true := by
  obtain ⟨u, v, hu, hbad, hnot, hfirst⟩ :=
    bankTrialC5WorkerBadHasPrefix ring root o w o.after hb
  subst w
  exact hkernel.nonreturnBad z e o ho u v
    hfirst (Or.inr hbad) hnot

/-- An actual origin is launched from a LIVE nonterminal state. -/
theorem bankTrialC5ActualOriginNonterminal
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S z e) :
    ¬ bankTrialLocalTerminal z := by
  unfold bankTrialC5ActualStarts at ho
  split at ho
  · rename_i hguard
    obtain ⟨begun, nextBegun, hphase, _⟩ :=
      hguard.2.2.2.1
    intro hterm
    rcases hterm with hw | hl
    · rw [hphase] at hw
      cases hw
    · rw [hphase] at hl
      cases hl
  · simp at ho

/-- Conditional N/D for the FIRST worker, with no union charge
for any hypothetical future launches. -/
theorem bankTrialC5FirstWorkerBadRarity
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (z : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S z e)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      Prob.scheduleSum n T (fun w =>
        if bankTrialC5WorkerFirstExit ring root o w o.after =
          some false then 1 else 0) ≤
      bankTrialProbabilityC5WorkerNumerator q * n ^ T := by
  have hmono :
      Prob.scheduleSum n T (fun w =>
        if bankTrialC5WorkerFirstExit ring root o w o.after =
          some false then 1 else 0) ≤
      Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5ActualTimeout ring root o w)) := by
    apply bankTrialProbabilityScheduleSumMono n T
    intro w
    by_cases hb :
        bankTrialC5WorkerFirstExit ring root o w o.after =
          some false
    · have ht := bankTrialC5FirstBadImpliesTimeout
        ring root S hkernel z e o ho w hb
      simp [hb, Prob.indicator, ht]
    · simp [hb]
  have hr := hkernel.conditionalRarity
    z (bankTrialC5ActualOriginNonterminal ring root S z e o ho)
    e o ho T
  exact Nat.le_trans
    (Nat.mul_le_mul_left
      (bankTrialProbabilityC5WorkerDenominator q) hmono) hr

end L3

/- No structure replacement is necessary. -/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/--
One-origin first-BAD bound on the original n-edge scheduler.
The local induction statements are stronger than the displayed
CLEAN-reachable ARMED-gate conclusion: they hold for every local
state. This class is closed under every no-origin successor.

The first outgoing HEAD need not launch a worker: an ARMED-to-CSTART
service switches from the pre-HEAD scanner to the post-HEAD scanner.
Consequently the proof does not assert the false equation that the
whole four-way stage classifier simply shifts to its successor.
-/
theorem bankTrialC5StageBadRarity
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate x)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialC5StageMass ring root S x T .bad ≤
    bankTrialProbabilityC5WorkerNumerator q * n ^ T := by
  have hsumBound (t : Nat)
      (f : Fin n → List (Fin n) → Nat)
      (hf : ∀ e : Fin n,
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (f e) ≤
        bankTrialProbabilityC5WorkerNumerator q * n ^ t) :
      bankTrialProbabilityC5WorkerDenominator q *
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n t (f e))).sum ≤
      bankTrialProbabilityC5WorkerNumerator q * n ^ (t + 1) := by
    have hs := ofFn_sum_le
      (fun e : Fin n =>
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (f e))
      (fun _ : Fin n =>
        bankTrialProbabilityC5WorkerNumerator q * n ^ t)
      hf
    rw [ofFn_sum_mul_left, ofFn_sum_const] at hs
    simpa only [Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using hs
  have hpost :
      ∀ t : Nat, ∀ z : BankTrialLocalState q,
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (fun w =>
            if bankTrialC5PostHeadFirstExit ring root S w z =
              some false then 1 else 0) ≤
        bankTrialProbabilityC5WorkerNumerator q * n ^ t := by
    intro t
    induction t with
    | zero =>
        intro z
        rw [bankTrialProbabilityScheduleSumZero]
        simp [bankTrialC5PostHeadFirstExit]
    | succ t ih =>
        intro z
        rw [bankTrialProbabilityScheduleSumFirst]
        have hrow (e : Fin n) :
            bankTrialProbabilityC5WorkerDenominator q *
              Prob.scheduleSum n t (fun w =>
                if bankTrialC5PostHeadFirstExit ring root S
                  (e :: w) z = some false then 1 else 0) ≤
            bankTrialProbabilityC5WorkerNumerator q * n ^ t := by
          cases hstarts :
              bankTrialC5ActualStarts ring root S z e with
          | nil =>
              simpa only [bankTrialC5PostHeadFirstExit,
                hstarts] using
                (ih (bankTrialLocalNext ring root z e))
          | cons o os =>
              have ho :
                  o ∈ bankTrialC5ActualStarts ring root S z e := by
                rw [hstarts]
                simp
              have hp :
                  o.after = bankTrialLocalNext ring root z e :=
                bankTrialC5ActualStartPost ring root S z e o ho
              have hr := bankTrialC5FirstWorkerBadRarity
                ring root S hkernel z e o ho t
              simpa only [bankTrialC5PostHeadFirstExit,
                hstarts, ← hp] using hr
        exact hsumBound t (fun e w =>
          if bankTrialC5PostHeadFirstExit ring root S
            (e :: w) z = some false then 1 else 0) hrow
  have hpre :
      ∀ t : Nat, ∀ z : BankTrialLocalState q,
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (fun w =>
            if bankTrialC5PreHeadFirstExit ring root S w z =
              some false then 1 else 0) ≤
        bankTrialProbabilityC5WorkerNumerator q * n ^ t := by
    intro t
    induction t with
    | zero =>
        intro z
        rw [bankTrialProbabilityScheduleSumZero]
        simp [bankTrialC5PreHeadFirstExit]
    | succ t ih =>
        intro z
        rw [bankTrialProbabilityScheduleSumFirst]
        have hrow (e : Fin n) :
            bankTrialProbabilityC5WorkerDenominator q *
              Prob.scheduleSum n t (fun w =>
                if bankTrialC5PreHeadFirstExit ring root S
                  (e :: w) z = some false then 1 else 0) ≤
            bankTrialProbabilityC5WorkerNumerator q * n ^ t := by
          by_cases he : e = root
          · cases hstarts :
                bankTrialC5ActualStarts ring root S z e with
            | nil =>
                simpa only [bankTrialC5PreHeadFirstExit,
                  if_pos he, hstarts] using
                  (hpost t (bankTrialLocalNext ring root z e))
            | cons o os =>
                have ho :
                    o ∈ bankTrialC5ActualStarts ring root S z e := by
                  rw [hstarts]
                  simp
                have hp :
                    o.after = bankTrialLocalNext ring root z e :=
                  bankTrialC5ActualStartPost ring root S z e o ho
                have hr := bankTrialC5FirstWorkerBadRarity
                  ring root S hkernel z e o ho t
                simpa only [bankTrialC5PreHeadFirstExit,
                  if_pos he, hstarts, ← hp] using hr
          · by_cases hi : e = ring.leftNeighbor root
            · have hzero :
                  (fun w : List (Fin n) =>
                    if bankTrialC5PreHeadFirstExit ring root S
                      (e :: w) z = some false then 1 else 0) =
                    (fun _ => 0) := by
                funext w
                simp [bankTrialC5PreHeadFirstExit, he, hi]
                intro hlr
                exact absurd (hi.trans hlr) he
              rw [hzero, bankTrialProbabilityScheduleSumConst]
              simp
            · simpa only [bankTrialC5PreHeadFirstExit,
                if_neg he, if_neg hi] using
                (ih (bankTrialLocalNext ring root z e))
        exact hsumBound t (fun e w =>
          if bankTrialC5PreHeadFirstExit ring root S
            (e :: w) z = some false then 1 else 0) hrow
  have hmono :
      Prob.scheduleSum n T (fun w =>
        bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S x w) .bad) ≤
      Prob.scheduleSum n T (fun w =>
        if bankTrialC5PreHeadFirstExit ring root S w x =
          some false then 1 else 0) := by
    apply bankTrialProbabilityScheduleSumMono n T
    intro w
    by_cases ht :
        bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) w = some false
    · simp [bankTrialC5StageClass,
        bankTrialC5StageIndicator, ht]
    · by_cases hg :
          bankTrialC5PreHeadFirstExit ring root S w x =
            some true
      · simp [bankTrialC5StageClass,
          bankTrialC5StageIndicator, ht, hg]
      · by_cases hb :
            bankTrialC5PreHeadFirstExit ring root S w x =
              some false
        · simp [bankTrialC5StageClass,
            bankTrialC5StageIndicator, ht, hg, hb]
        · simp [bankTrialC5StageClass,
            bankTrialC5StageIndicator, ht, hg, hb]
  unfold bankTrialC5StageMass
  exact Nat.le_trans
    (Nat.mul_le_mul_left
      (bankTrialProbabilityC5WorkerDenominator q) hmono)
    (hpre T x)

end L3

/- No structure replacement. -/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Pending with no first physical root-incident service yet. -/
noncomputable def bankTrialC5PendingBeforeBool {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) : Bool :=
  if bankTrialProbabilityFirstIncidentOrientation
      root (ring.leftNeighbor root) w = none then
    bankTrialC5StageClassBool ring root S x w .pending
  else false

/-- Pending after the first physical HEAD, including CSTART waiting. -/
noncomputable def bankTrialC5PendingAfterBool {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) : Bool :=
  if bankTrialProbabilityFirstIncidentOrientation
      root (ring.leftNeighbor root) w = some true then
    bankTrialC5StageClassBool ring root S x w .pending
  else false

/-- Both pending masses use the same original n-edge word clock. -/
noncomputable def bankTrialC5PendingBeforeMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    Prob.indicator (bankTrialC5PendingBeforeBool ring root S x w))

noncomputable def bankTrialC5PendingAfterMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    Prob.indicator (bankTrialC5PendingAfterBool ring root S x w))

/-- The pre-HEAD scanner cannot report a worker exit before the
first physical root-incident letter. This holds for every state. -/
theorem bankTrialC5PreHeadNoneBeforeIncident {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) w = none →
      bankTrialC5PreHeadFirstExit ring root S w z = none := by
  intro w
  induction w with
  | nil =>
      intro z hnone
      rfl
  | cons e w ih =>
      intro z hnone
      by_cases he : e = root
      · have hh :
          bankTrialProbabilityFirstIncidentOrientation
            root (ring.leftNeighbor root) (e :: w) = some true := by
          simp [bankTrialProbabilityFirstIncidentOrientation, he]
        rw [hh] at hnone
        cases hnone
      · by_cases hi : e = ring.leftNeighbor root
        · have hh :
            bankTrialProbabilityFirstIncidentOrientation
              root (ring.leftNeighbor root) (e :: w) =
              some false := by
            simp [bankTrialProbabilityFirstIncidentOrientation,
              he, hi]
            intro hlr
            exact he (hi.trans hlr)
          rw [hh] at hnone
          cases hnone
        · have ht :
            bankTrialProbabilityFirstIncidentOrientation
              root (ring.leftNeighbor root) w = none := by
            simpa only [bankTrialProbabilityFirstIncidentOrientation,
              if_neg he, if_neg hi] using hnone
          simpa only [bankTrialC5PreHeadFirstExit,
            if_neg he, if_neg hi] using
            (ih (bankTrialLocalNext ring root z e) ht)

/-- Pointwise disjoint pending split and exact first-HEAD split.
The classifier's precedence for TAIL is respected. -/
theorem bankTrialC5PendingAndHeadIndicators {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) :
    bankTrialC5StageIndicator
        (bankTrialC5StageClass ring root S x w) .pending =
      Prob.indicator (bankTrialC5PendingBeforeBool ring root S x w) +
        Prob.indicator (bankTrialC5PendingAfterBool ring root S x w) ∧
    (if bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) w = some true then 1 else 0) =
      (bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S x w) .good +
        bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S x w) .bad) +
        Prob.indicator
          (bankTrialC5PendingAfterBool ring root S x w) := by
  cases hfirst :
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) w with
  | none =>
      have hpre := bankTrialC5PreHeadNoneBeforeIncident
        ring root S w x hfirst
      have hc :
          bankTrialC5StageClass ring root S x w = .pending := by
        simp [bankTrialC5StageClass, hfirst, hpre]
      constructor <;>
        simp [bankTrialC5StageIndicator,
          bankTrialC5PendingBeforeBool, bankTrialC5PendingAfterBool,
          bankTrialC5StageClassBool, Prob.indicator, hfirst, hc]
  | some b =>
      cases b with
      | false =>
          have hc :
              bankTrialC5StageClass ring root S x w = .tail := by
            simp [bankTrialC5StageClass, hfirst]
          constructor <;>
            simp [bankTrialC5StageIndicator,
              bankTrialC5PendingBeforeBool, bankTrialC5PendingAfterBool,
              bankTrialC5StageClassBool, Prob.indicator, hfirst, hc]
      | true =>
          by_cases hg :
              bankTrialC5PreHeadFirstExit ring root S w x = some true
          · have hc :
                bankTrialC5StageClass ring root S x w = .good := by
              simp [bankTrialC5StageClass, hfirst, hg]
            constructor <;>
              simp [bankTrialC5StageIndicator,
                bankTrialC5PendingBeforeBool,
                bankTrialC5PendingAfterBool,
                bankTrialC5StageClassBool, Prob.indicator, hfirst, hc]
          · by_cases hb :
                bankTrialC5PreHeadFirstExit ring root S w x =
                  some false
            · have hc :
                  bankTrialC5StageClass ring root S x w = .bad := by
                simp [bankTrialC5StageClass, hfirst, hg, hb]
              constructor <;>
                simp [bankTrialC5StageIndicator,
                  bankTrialC5PendingBeforeBool,
                  bankTrialC5PendingAfterBool,
                  bankTrialC5StageClassBool, Prob.indicator, hfirst, hc]
            · have hc :
                  bankTrialC5StageClass ring root S x w =
                    .pending := by
                simp [bankTrialC5StageClass, hfirst, hg, hb]
              constructor <;>
                simp [bankTrialC5StageIndicator,
                  bankTrialC5PendingBeforeBool,
                  bankTrialC5PendingAfterBool,
                  bankTrialC5StageClassBool, Prob.indicator, hfirst, hc]

/-- Q + R is exactly the existing pending class, word by word. -/
theorem bankTrialC5PendingMassSplit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialC5StageMass ring root S x T .pending =
      bankTrialC5PendingBeforeMass ring root S x T +
        bankTrialC5PendingAfterMass ring root S x T := by
  unfold bankTrialC5StageMass bankTrialC5PendingBeforeMass
    bankTrialC5PendingAfterMass
  calc
    Prob.scheduleSum n T (fun w =>
        bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S x w) .pending) =
      Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5PendingBeforeBool ring root S x w) +
          Prob.indicator
            (bankTrialC5PendingAfterBool ring root S x w)) := by
        apply congrArg (Prob.scheduleSum n T)
        funext w
        exact (bankTrialC5PendingAndHeadIndicators ring root S x w).1
    _ = _ := bankTrialC5ScheduleSumAdd T _ _

/-- The full first-HEAD cylinder is G + Bad + R, with no
identification of a CSTART cut as a completed worker. -/
theorem bankTrialC5HeadMassSplit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T =
      (bankTrialC5StageMass ring root S x T .good +
        bankTrialC5StageMass ring root S x T .bad) +
        bankTrialC5PendingAfterMass ring root S x T := by
  unfold bankTrialProbabilityFirstIncidentMass
    bankTrialC5StageMass bankTrialC5PendingAfterMass
  calc
    Prob.scheduleSum n T (fun w =>
        if bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) w = some true
        then 1 else 0) =
      Prob.scheduleSum n T (fun w =>
        (bankTrialC5StageIndicator
            (bankTrialC5StageClass ring root S x w) .good +
          bankTrialC5StageIndicator
            (bankTrialC5StageClass ring root S x w) .bad) +
          Prob.indicator
            (bankTrialC5PendingAfterBool ring root S x w)) := by
        apply congrArg (Prob.scheduleSum n T)
        funext w
        exact (bankTrialC5PendingAndHeadIndicators ring root S x w).2
    _ = _ := by
      rw [bankTrialC5ScheduleSumAdd, bankTrialC5ScheduleSumAdd]

/-- One literal first-ARMED stage, with all terms evaluated at the
same original physical scheduler horizon and the same observer x.
No independence or fresh-scheduler assumption is used. -/
theorem bankTrialC5OneArmedStage
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate x)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ T ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialC5StageMass ring root S x T .good +
        2 * bankTrialProbabilityC5WorkerNumerator q * n ^ T) +
        (bankTrialProbabilityC5WorkerDenominator q *
            bankTrialC5PendingBeforeMass ring root S x T +
          2 * bankTrialProbabilityC5WorkerDenominator q *
            bankTrialC5PendingAfterMass ring root S x T) := by
  have hfour :=
    bankTrialC5FourStageMassPartition ring root S x T
  have hpending :=
    bankTrialC5PendingMassSplit ring root S x T
  have hhead :=
    bankTrialC5HeadMassSplit ring root S x T
  have hfair :=
    (bankTrialC5StageTailHeadFair
      ring root S x hlarge hclean pre hreach hgate T).symm
  have hbad :=
    bankTrialC5StageBadRarity ring root S hkernel
      hclean pre x hreach hgate T
  have harith :
      ∀ X F G Bad Pending Q R H : Nat,
        F + G + Bad + Pending = X →
        Pending = Q + R →
        H = G + Bad + R →
        X = H + F + Q := by
    intro X F G Bad Pending Q R H hpart hsplit hhsplit
    omega
  have hpartition :
      n ^ T =
        bankTrialProbabilityFirstIncidentMass
          root (ring.leftNeighbor root) true T +
          bankTrialC5StageMass ring root S x T .tail +
          bankTrialC5PendingBeforeMass ring root S x T :=
    harith
      (n ^ T)
      (bankTrialC5StageMass ring root S x T .tail)
      (bankTrialC5StageMass ring root S x T .good)
      (bankTrialC5StageMass ring root S x T .bad)
      (bankTrialC5StageMass ring root S x T .pending)
      (bankTrialC5PendingBeforeMass ring root S x T)
      (bankTrialC5PendingAfterMass ring root S x T)
      (bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T)
      hfour hpending hhead
  exact bankTrialC5OneStageFairRarityArithmetic
    (D := bankTrialProbabilityC5WorkerDenominator q)
    (N := bankTrialProbabilityC5WorkerNumerator q)
    (X := n ^ T)
    (H := bankTrialProbabilityFirstIncidentMass
      root (ring.leftNeighbor root) true T)
    (F := bankTrialC5StageMass ring root S x T .tail)
    (Q := bankTrialC5PendingBeforeMass ring root S x T)
    (G := bankTrialC5StageMass ring root S x T .good)
    (Bad := bankTrialC5StageMass ring root S x T .bad)
    (R := bankTrialC5PendingAfterMass ring root S x T)
    hfair hpartition (Nat.le_of_eq hhead) hbad

end L3

/- No structure replacement. -/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- An actually emitted postservice origin remains on the very same
physical scheduler tape. This requires no kernel hypothesis. -/
theorem bankTrialC5GoodReturnReachable
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (w : List (Fin n)) :
    bankTrialLocalRun ring root w o.after =
      bankTrialLocalRun ring root (pre ++ (e :: w))
        (bankTrialLocalStart S) := by
  calc
    bankTrialLocalRun ring root w o.after =
        bankTrialLocalRun ring root w
          (bankTrialLocalNext ring root x e) := by
            rw [bankTrialC5ActualStartPost ring root S x e o ho]
    _ = bankTrialLocalRun ring root (e :: w) x := rfl
    _ = bankTrialLocalRun ring root (e :: w)
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) := by
              rw [← hreach]
    _ = bankTrialLocalRun ring root (pre ++ (e :: w))
          (bankTrialLocalStart S) :=
        (bankTrialLocalRunAppend ring root pre (e :: w)
          (bankTrialLocalStart S)).symm

/-- Three mutually exclusive actual return classes.

Increment: reachable LIVE/CSTART, all digit tokens E, with a real
root comparator launch. Comparator before K: authenticated ARMED at
the ALREADY RECORDED postservice count o.heads. Comparator at K:
WON. The two comparator alternatives are exclusive because
o.heads < K and o.heads = K cannot both hold; either is disjoint
from the increment alternative because of the Boolean tag.

The count is deliberately NOT o.heads + 1: see the refutation
theorem below. -/
theorem bankTrialC5GoodReturnClassification
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (w : List (Fin n)) (y : BankTrialLocalState q)
    (hy : y = bankTrialLocalRun ring root w o.after)
    (hgood : bankTrialC5ActualReturned o y) :
    (∃ full : List (Fin n),
      y = bankTrialLocalRun ring root full
        (bankTrialLocalStart S) ∧
      ((o.increment = true ∧
          ∃ begun : Bool,
            y.phase = .live begun ∧
            bankTrialLiveWaveRootMode y.bank = .CSTART ∧
            (∀ j : Fin (compileAdvice q).b,
              bankTrialLiveWaveToken y.bank j = .E) ∧
            BankTrialCmpCRStage y.bank 0
              (bankTrialLocalNext ring root y root)) ∨
       (o.increment = false ∧
          o.heads < (compileAdvice q).K ∧
          BankTrialC5ArmedAt q y o.heads ∧
          BankTrialProbabilityArmedGate y) ∨
       (o.increment = false ∧
          o.heads = (compileAdvice q).K ∧
          y.phase = .won))) ∧
    ¬ (o.increment = true ∧ o.increment = false) ∧
    ¬ (o.heads < (compileAdvice q).K ∧
       o.heads = (compileAdvice q).K) := by
  have hreachFinal :
      y = bankTrialLocalRun ring root (pre ++ (e :: w))
        (bankTrialLocalStart S) := by
    calc
      y = bankTrialLocalRun ring root w o.after := hy
      _ = bankTrialLocalRun ring root (pre ++ (e :: w))
            (bankTrialLocalStart S) :=
        bankTrialC5GoodReturnReachable
          ring root S pre x hreach e o ho w
  refine ⟨⟨pre ++ (e :: w), hreachFinal, ?_⟩, ?_, ?_⟩
  · unfold bankTrialC5ActualReturned at hgood
    cases hinc : o.increment with
    | false =>
        simp only [hinc, ↓reduceIte] at hgood
        rcases hgood with hbefore | hfinal
        · right
          left
          have hgate : BankTrialProbabilityArmedGate y := by
            obtain ⟨begun, hphase, hmode, _, _, _, _⟩ :=
              hbefore.2
            exact ⟨⟨begun, hphase⟩, hmode⟩
          exact ⟨rfl, hbefore.1, hbefore.2, hgate⟩
        · right
          right
          exact ⟨rfl, hfinal.1, hfinal.2⟩
    | true =>
        simp only [hinc, ↓reduceIte] at hgood
        obtain ⟨begun, hphase, hmode⟩ := hgood
        have hphasePre :
            (bankTrialC5CleanRun ring root S
              (pre ++ (e :: w))).phase = .live begun := by
          change (bankTrialLocalRun ring root (pre ++ (e :: w))
            (bankTrialLocalStart S)).phase = .live begun
          rw [← hreachFinal]
          exact hphase
        have hmodePre :
            bankTrialLiveWaveRootMode
              (bankTrialC5CleanRun ring root S
                (pre ++ (e :: w))).bank = .CSTART := by
          change bankTrialLiveWaveRootMode
            (bankTrialLocalRun ring root (pre ++ (e :: w))
              (bankTrialLocalStart S)).bank = .CSTART
          rw [← hreachFinal]
          exact hmode
        have htokens :
            ∀ j : Fin (compileAdvice q).b,
              bankTrialLiveWaveToken y.bank j = .E := by
          intro j
          have ht := bankTrialC5CleanCStartTokensEmpty
            ring root (bankTrialProbabilityUpperWindow hlarge)
            S hclean (pre ++ (e :: w)) begun
            hphasePre hmodePre j
          change bankTrialLiveWaveToken
            (bankTrialLocalRun ring root (pre ++ (e :: w))
              (bankTrialLocalStart S)).bank j = .E at ht
          rw [← hreachFinal] at ht
          exact ht
        have hlaunch : BankTrialCmpCRStage y.bank 0
            (bankTrialLocalNext ring root y root) :=
          bankTrialC5CStartRootLaunchAtReachable
            ring root S hlarge hclean
            (pre ++ (e :: w)) y begun hreachFinal
            hphase hmode
        left
        exact ⟨rfl, begun, hphase, hmode, htokens, hlaunch⟩
  · rintro ⟨htrue, hfalse⟩
    have hc : true = false := htrue.symm.trans hfalse
    cases hc
  · rintro ⟨hbelow, hequal⟩
    omega

/-- The launch itself consumes one actual HEAD at an ARMED gate.
The stored o.heads is the POSTservice count, not the old count.
This uses only the existing actual-origin kernel coverage. -/
theorem bankTrialC5ArmedLaunchHeadAlreadyAdvanced
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate x)
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    e = root ∧ o.increment = true ∧
      o.heads =
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) + 1 := by
  obtain ⟨he, _, hinc, hheads⟩ :=
    bankTrialC5KernelNoSpuriousOrigin
      ring root S hkernel hclean pre x hreach e o ho
  have hmode :
      bankTrialLiveWaveRootMode x.bank = .ARMED := hgate.2
  have htag : o.increment = true := by
    rw [hinc, hmode]
    rfl
  have hcount :
      bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S) =
      bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) + 1 := by
    calc
      bankTrialLiveHeadCount ring root (pre ++ [e])
          (bankTrialLocalStart S) =
        bankTrialLiveHeadCount ring root pre
            (bankTrialLocalStart S) +
          bankTrialLiveHeadCount ring root [e]
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) :=
        bankTrialLiveHeadCountAppend ring root pre [e]
          (bankTrialLocalStart S)
      _ = bankTrialLiveHeadCount ring root pre
            (bankTrialLocalStart S) + 1 := by
        rw [← hreach]
        simp only [bankTrialLiveHeadCount,
          if_pos (show BankTrialProbabilityArmedGate x ∧
            e = root from ⟨hgate, he⟩),
          Nat.add_zero]
  exact ⟨he, htag, hheads.trans hcount⟩

/-- At a CSTART-to-CWAIT comparator launch there is NO extra
ARMED-head decision. The recorded postservice count is unchanged. -/
theorem bankTrialC5ComparatorLaunchHeadUnchanged
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hcstart : bankTrialLiveWaveRootMode x.bank = .CSTART)
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    e = root ∧ o.increment = false ∧
      o.heads =
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) := by
  obtain ⟨he, _, hinc, hheads⟩ :=
    bankTrialC5KernelNoSpuriousOrigin
      ring root S hkernel hclean pre x hreach e o ho
  have hnotarmed :
      ¬ bankTrialLiveWaveRootMode x.bank = .ARMED := by
    intro ha
    rw [hcstart] at ha
    cases ha
  have hnotgate :
      ¬ BankTrialProbabilityArmedGate x := by
    intro hg
    exact hnotarmed hg.2
  have htag : o.increment = false := by
    rw [hinc]
    simp only [decide_eq_false hnotarmed]
  have hcount :
      bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S) =
      bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) := by
    calc
      bankTrialLiveHeadCount ring root (pre ++ [e])
          (bankTrialLocalStart S) =
        bankTrialLiveHeadCount ring root pre
            (bankTrialLocalStart S) +
          bankTrialLiveHeadCount ring root [e]
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) :=
        bankTrialLiveHeadCountAppend ring root pre [e]
          (bankTrialLocalStart S)
      _ = bankTrialLiveHeadCount ring root pre
            (bankTrialLocalStart S) := by
        rw [← hreach]
        simp only [bankTrialLiveHeadCount,
          if_neg (show ¬ (BankTrialProbabilityArmedGate x ∧
            e = root) by
              intro hg
              exact hnotgate hg.1),
          Nat.zero_add, Nat.add_zero]
  exact ⟨he, htag, hheads.trans hcount⟩

/-- The requested +1 comparator-return ARMED claim is not merely
unproved; it contradicts the actual good-return definition.
A good comparator either certifies ARMED at o.heads, or ends WON.
Neither case can certify ARMED at o.heads + 1. -/
theorem bankTrialC5ComparatorReturnNotIncrementedAgain
    {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (y : BankTrialLocalState q)
    (hcomp : o.increment = false)
    (hgood : bankTrialC5ActualReturned o y) :
    ¬ BankTrialC5ArmedAt q y (o.heads + 1) := by
  unfold bankTrialC5ActualReturned at hgood
  simp only [hcomp, ↓reduceIte] at hgood
  intro hplus
  rcases hgood with hbefore | hfinal
  · obtain ⟨_, _, _, _, hval, _, _⟩ := hbefore.2
    obtain ⟨_, _, _, _, hplusval, _, _⟩ := hplus
    rw [hval] at hplusval
    omega
  · obtain ⟨_, hphase, _, _, _, _, _⟩ := hplus
    rw [hfinal.2] at hphase
    cases hphase

/-- A good comparator return below K is an actual reachable ARMED
cut, so the EXISTING one-stage bound can be applied with the
returned state as its new starting state. -/
theorem bankTrialC5GoodComparatorNextArmedStage
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (w : List (Fin n)) (y : BankTrialLocalState q)
    (hy : y = bankTrialLocalRun ring root w o.after)
    (hgood : bankTrialC5ActualReturned o y)
    (hcomp : o.increment = false)
    (hbelow : o.heads < (compileAdvice q).K)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ T ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialC5StageMass ring root S y T .good +
        2 * bankTrialProbabilityC5WorkerNumerator q * n ^ T) +
        (bankTrialProbabilityC5WorkerDenominator q *
            bankTrialC5PendingBeforeMass ring root S y T +
          2 * bankTrialProbabilityC5WorkerDenominator q *
            bankTrialC5PendingAfterMass ring root S y T) := by
  obtain ⟨⟨full, hreachFinal, hcases⟩, _, _⟩ :=
    bankTrialC5GoodReturnClassification
      ring root S hlarge hclean pre x hreach e o ho
      w y hy hgood
  rcases hcases with hincrement | harm | hwon
  · have hc : true = false := hincrement.1.symm.trans hcomp
    cases hc
  · exact bankTrialC5OneArmedStage
      ring root S hkernel hlarge hclean full y hreachFinal
      harm.2.2.2 T
  · have heq : o.heads = (compileAdvice q).K := hwon.2.1
    omega

end L3

/- No structure replacement is needed. -/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- GOOD is a matching return from the first actual worker origin
encountered by the post-head scanner on the original edge tape. -/
noncomputable def bankTrialC5CStartGoodBool {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) : Bool :=
  if bankTrialC5PostHeadFirstExit ring root S w x = some true
  then true else false

/-- BAD is the first actual worker origin's classified bad exit. -/
noncomputable def bankTrialC5CStartBadBool {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) : Bool :=
  if bankTrialC5PostHeadFirstExit ring root S w x = some false
  then true else false

/-- PENDING means the first-origin scanner has no recorded exit
at the given horizon. This includes no origin yet and an active
origin without an exit. The existing scanner also leaves any
unclassified early prelaunch exit pending; no unsupported
no-early-exit invariant is silently asserted here. -/
noncomputable def bankTrialC5CStartPendingBool {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) : Bool :=
  if bankTrialC5PostHeadFirstExit ring root S w x = none
  then true else false

/-- Original-clock numerator of exactly one of the three Bool
classes. The Option Bool index is merely a convenient finite tag. -/
noncomputable def bankTrialC5CStartMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat)
    (tag : Option Bool) : Nat :=
  Prob.scheduleSum n T (fun w =>
    Prob.indicator
      (match tag with
       | some true => bankTrialC5CStartGoodBool ring root S x w
       | some false => bankTrialC5CStartBadBool ring root S x w
       | none => bankTrialC5CStartPendingBool ring root S x w))

/-- Exactly one of GOOD, BAD, PENDING holds for each actual word. -/
theorem bankTrialC5CStartThreeIndicators {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (w : List (Fin n)) :
    Prob.indicator (bankTrialC5CStartGoodBool ring root S x w) +
      (Prob.indicator (bankTrialC5CStartBadBool ring root S x w) +
        Prob.indicator
          (bankTrialC5CStartPendingBool ring root S x w)) = 1 := by
  unfold bankTrialC5CStartGoodBool
    bankTrialC5CStartBadBool bankTrialC5CStartPendingBool
    Prob.indicator
  cases he :
      bankTrialC5PostHeadFirstExit ring root S w x with
  | none =>
      simp [he]
  | some b =>
      cases b <;> simp [he]

/-- Complete three-way mass partition, at one physical horizon. -/
theorem bankTrialC5CStartMassPartition {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialC5CStartMass ring root S x T (some true) +
      bankTrialC5CStartMass ring root S x T (some false) +
      bankTrialC5CStartMass ring root S x T none = n ^ T := by
  unfold bankTrialC5CStartMass
  calc
    Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5CStartGoodBool ring root S x w)) +
      Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5CStartBadBool ring root S x w)) +
      Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5CStartPendingBool ring root S x w)) =
      Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5CStartGoodBool ring root S x w) +
          (Prob.indicator (bankTrialC5CStartBadBool ring root S x w) +
            Prob.indicator
              (bankTrialC5CStartPendingBool ring root S x w))) := by
                rw [bankTrialC5ScheduleSumAdd,
                  bankTrialC5ScheduleSumAdd]
                simp only [Nat.add_assoc]
    _ = Prob.scheduleSum n T (fun _ => 1) := by
      apply congrArg (Prob.scheduleSum n T)
      funext w
      exact bankTrialC5CStartThreeIndicators ring root S x w
    _ = n ^ T := by
      simpa only [Nat.mul_one] using
        (bankTrialProbabilityScheduleSumConst n T 1)

/-- The single first-origin conditional watchdog, not the all-origin
union estimate: there is no factor 2K+1 in this bound. It actually
holds for every local state, a class closed under no-origin edges. -/
theorem bankTrialC5CStartBadRarity
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialC5CStartMass ring root S x T (some false) ≤
    bankTrialProbabilityC5WorkerNumerator q * n ^ T := by
  have hsumBound (t : Nat)
      (f : Fin n → List (Fin n) → Nat)
      (hf : ∀ e : Fin n,
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (f e) ≤
        bankTrialProbabilityC5WorkerNumerator q * n ^ t) :
      bankTrialProbabilityC5WorkerDenominator q *
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n t (f e))).sum ≤
      bankTrialProbabilityC5WorkerNumerator q * n ^ (t + 1) := by
    have hs := ofFn_sum_le
      (fun e : Fin n =>
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (f e))
      (fun _ : Fin n =>
        bankTrialProbabilityC5WorkerNumerator q * n ^ t)
      hf
    rw [ofFn_sum_mul_left, ofFn_sum_const] at hs
    simpa only [Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using hs
  have hpost :
      ∀ t : Nat, ∀ z : BankTrialLocalState q,
        bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (fun w =>
            if bankTrialC5PostHeadFirstExit ring root S w z =
              some false then 1 else 0) ≤
        bankTrialProbabilityC5WorkerNumerator q * n ^ t := by
    intro t
    induction t with
    | zero =>
        intro z
        rw [bankTrialProbabilityScheduleSumZero]
        simp [bankTrialC5PostHeadFirstExit]
    | succ t ih =>
        intro z
        rw [bankTrialProbabilityScheduleSumFirst]
        have hrow (e : Fin n) :
            bankTrialProbabilityC5WorkerDenominator q *
              Prob.scheduleSum n t (fun w =>
                if bankTrialC5PostHeadFirstExit ring root S
                  (e :: w) z = some false then 1 else 0) ≤
            bankTrialProbabilityC5WorkerNumerator q * n ^ t := by
          cases hstarts :
              bankTrialC5ActualStarts ring root S z e with
          | nil =>
              simpa only [bankTrialC5PostHeadFirstExit,
                hstarts] using
                (ih (bankTrialLocalNext ring root z e))
          | cons o os =>
              have ho :
                  o ∈ bankTrialC5ActualStarts ring root S z e := by
                rw [hstarts]
                simp
              have hp :
                  o.after = bankTrialLocalNext ring root z e :=
                bankTrialC5ActualStartPost ring root S z e o ho
              have hr := bankTrialC5FirstWorkerBadRarity
                ring root S hkernel z e o ho t
              simpa only [bankTrialC5PostHeadFirstExit,
                hstarts, ← hp] using hr
        exact hsumBound t (fun e w =>
          if bankTrialC5PostHeadFirstExit ring root S
            (e :: w) z = some false then 1 else 0) hrow
  have heq :
      (fun w : List (Fin n) =>
        Prob.indicator (bankTrialC5CStartBadBool ring root S x w)) =
      (fun w : List (Fin n) =>
        if bankTrialC5PostHeadFirstExit ring root S w x =
          some false then 1 else 0) := by
    funext w
    by_cases hb :
        bankTrialC5PostHeadFirstExit ring root S w x = some false
    · simp [bankTrialC5CStartBadBool, Prob.indicator, hb]
    · simp [bankTrialC5CStartBadBool, Prob.indicator, hb]
  unfold bankTrialC5CStartMass
  rw [heq]
  exact hpost T x

/-- CSTART's nominated root service is a genuine comparator origin
on every CLEAN-reachable LIVE/CSTART state; it is not a new HEAD.
The other physical edges cannot emit an origin by
bankTrialC5ActualStartAtRoot. -/
theorem bankTrialC5CStartRootActualOrigin
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (x : BankTrialLocalState q) (begun : Bool)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : x.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode x.bank = .CSTART) :
    ∃ o : BankTrialC5ActualOrigin n q,
      o ∈ bankTrialC5ActualStarts ring root S x root ∧
      o.after = bankTrialLocalNext ring root x root ∧
      o.increment = false := by
  have hlaunch := bankTrialC5CStartRootLaunchAtReachable
    ring root S hlarge hclean pre x begun hreach hlive hmode
  obtain ⟨nextBegun, hnextLive⟩ := hlaunch.1
  have hnextMode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x root).bank = .CWAIT :=
    hlaunch.2.2.1
  have hguard :
      BankTrialLocalClean q S ∧
      (∃ w : List (Fin n),
        bankTrialLocalRun ring root w (bankTrialLocalStart S) = x) ∧
      root = root ∧
      (∃ begun nextBegun : Bool,
        x.phase = .live begun ∧
        (bankTrialLocalNext ring root x root).phase = .live nextBegun) ∧
      ((bankTrialLiveWaveRootMode x.bank = .ARMED ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root x root).bank = .IWAIT) ∨
       (bankTrialLiveWaveRootMode x.bank = .CSTART ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root x root).bank = .CWAIT)) := by
    exact ⟨hclean, ⟨pre, hreach.symm⟩, rfl,
      ⟨begun, nextBegun, hlive, hnextLive⟩,
      Or.inr ⟨hmode, hnextMode⟩⟩
  have hstarts :
      bankTrialC5ActualStarts ring root S x root =
        [{ before := x,
           edge := root,
           after := bankTrialLocalNext ring root x root,
           increment :=
             (bankTrialLiveWaveRootMode
               (bankTrialLocalNext ring root x root).bank == .IWAIT),
           heads :=
             bankTrialLiveCarryValue
               (bankTrialLocalNext ring root x root).bank }] := by
    unfold bankTrialC5ActualStarts
    rw [if_pos hguard]
  refine ⟨BankTrialC5ActualOrigin.mk x root
      (bankTrialLocalNext ring root x root)
      (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x root).bank == .IWAIT)
      (bankTrialLiveCarryValue
        (bankTrialLocalNext ring root x root).bank),
    ?_, rfl, ?_⟩
  · rw [hstarts]
    simp
  · rw [hnextMode]
    rfl

/-- Opaque-Nat arithmetic; no expensive compiled-advice powers enter
the arithmetic elaborator. -/
theorem bankTrialC5CStartStageArithmetic
    {D N X G Bad P : Nat}
    (hpartition : G + Bad + P = X)
    (hbad : D * Bad ≤ N * X) :
    D * X ≤ D * G + N * X + D * P := by
  calc
    D * X = D * (G + Bad + P) := by rw [hpartition]
    _ = D * G + D * Bad + D * P := by
      simp only [Nat.mul_add]
    _ ≤ D * G + N * X + D * P :=
      Nat.add_le_add_right
        (Nat.add_le_add_left hbad (D * G)) (D * P)

/-- ONE CSTART comparator stage on the same n-edge scheduler.
Unlike an ARMED stage there is no 1/2 fair-race factor.
The completion P is the precise nonclassified remainder of the
first-origin scanner, not an assertion of continued LIVE mode. -/
theorem bankTrialC5OneCStartStage
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (x : BankTrialLocalState q) (begun : Bool)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : x.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode x.bank = .CSTART)
    (htokens : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken x.bank j = .E)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5CStartMass ring root S x T (some true) +
      bankTrialProbabilityC5WorkerNumerator q * n ^ T +
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5CStartMass ring root S x T none := by
  have hlaunch :=
    bankTrialC5CStartRootActualOrigin
      ring root S hlarge hclean pre x begun hreach hlive hmode
  have hpartition :=
    bankTrialC5CStartMassPartition ring root S x T
  have hbad :=
    bankTrialC5CStartBadRarity ring root S hkernel x T
  exact bankTrialC5CStartStageArithmetic hpartition hbad

end L3

-- No replacement of the installed structure is claimed here.
-- Its nonreturnBad field must be restricted to first exit
-- before a complete five-field instance can be constructed.

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- An emitted actual origin carries exactly the stored postservice
fields. This lemma does not assume a kernel instance. -/
theorem bankTrialC5ActualStartRecordFields {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    o.before = x ∧ o.edge = e ∧
      o.after = bankTrialLocalNext ring root x e ∧
      o.increment =
        (bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root x e).bank == .IWAIT) ∧
      o.heads =
        bankTrialLiveCarryValue
          (bankTrialLocalNext ring root x e).bank := by
  unfold bankTrialC5ActualStarts at ho
  split at ho
  · simp only [List.mem_singleton] at ho
    subst o
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp at ho

/-- Any emitted origin has the exact CLEAN-reachable launch guard.
In particular a launch has a LIVE predecessor and LIVE successor. -/
theorem bankTrialC5ActualStartGuardFacts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    BankTrialLocalClean q S ∧
    (∃ w : List (Fin n),
      bankTrialLocalRun ring root w (bankTrialLocalStart S) = x) ∧
    e = root ∧
    (∃ begun nextBegun : Bool,
      x.phase = .live begun ∧
      (bankTrialLocalNext ring root x e).phase = .live nextBegun) ∧
    ((bankTrialLiveWaveRootMode x.bank = .ARMED ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x e).bank = .IWAIT) ∨
     (bankTrialLiveWaveRootMode x.bank = .CSTART ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x e).bank = .CWAIT)) := by
  unfold bankTrialC5ActualStarts at ho
  split at ho
  · rename_i hguard
    exact hguard
  · simp at ho

/-- The return-classification component of goodReturn is already
available independently of coverage or the origin count cap. -/
theorem bankTrialC5ActualGoodReturnShapeOnWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (w : List (Fin n))
    (hret : bankTrialC5ActualReturned o
      (bankTrialLocalRun ring root w o.after)) :
    if o.increment then
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root w o.after).bank = .CSTART
    else
      (o.heads < (compileAdvice q).K ∧
        BankTrialC5ArmedAt q
          (bankTrialLocalRun ring root w o.after) o.heads) ∨
      (o.heads = (compileAdvice q).K ∧
        (bankTrialLocalRun ring root w o.after).phase = .won) := by
  exact bankTrialC5ActualReturnShape o
    (bankTrialLocalRun ring root w o.after) hret

/-- Assemble exactly the kernel's goodReturn field from its
unresolved all-word origin cap and the proved return shape. -/
theorem bankTrialC5ActualGoodReturnOfStartCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hcap : BankTrialProbabilityC5WorkerStartCap
      ring root S (bankTrialC5ActualStarts ring root S)) :
    BankTrialProbabilityC5WorkerStartCap
      ring root S (bankTrialC5ActualStarts ring root S) ∧
      ∀ (x : BankTrialLocalState q) (e : Fin n)
        (o : BankTrialC5ActualOrigin n q),
        o ∈ bankTrialC5ActualStarts ring root S x e →
        ∀ w : List (Fin n),
          bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root w o.after) →
          (if o.increment then
             bankTrialLiveWaveRootMode
               (bankTrialLocalRun ring root w o.after).bank = .CSTART
           else
             (o.heads < (compileAdvice q).K ∧
               BankTrialC5ArmedAt q
                 (bankTrialLocalRun ring root w o.after)
                 o.heads) ∨
             (o.heads = (compileAdvice q).K ∧
               (bankTrialLocalRun ring root w o.after).phase = .won)) := by
  refine ⟨hcap, ?_⟩
  intro x e o ho w hret
  exact bankTrialC5ActualGoodReturnShapeOnWord
    ring root o w hret

/-- The phase-local nominated-edge drift interface is enough for
the exact boundedMean field. The physical drop/nonincrease rows
remain hypotheses here, not claimed from aggregate C.6. -/
theorem bankTrialC5ActualBoundedMeanOfNominatedRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (rank : BankTrialC5ActualOrigin n q →
      BankTrialLocalState q → Nat)
    (chosen : BankTrialC5ActualOrigin n q →
      BankTrialLocalState q → Fin n)
    (hdrop : ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      ∀ z : BankTrialLocalState q,
      ¬ (bankTrialC5ActualReturned o z ∨
         bankTrialC5ActualBadExit o z) →
      rank o (bankTrialLocalNext ring root z (chosen o z)) + 1 ≤
        rank o z)
    (hnoninc : ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      ∀ z : BankTrialLocalState q,
      ¬ (bankTrialC5ActualReturned o z ∨
         bankTrialC5ActualBadExit o z) →
      ∀ f : Fin n,
      rank o (bankTrialLocalNext ring root z f) ≤ rank o z)
    (hstart : ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
        rank o o.after ≤ 2 * (compileAdvice q).b + 3) :
    ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      o.after = bankTrialLocalNext ring root x e ∧
      ∀ T : Nat,
        costNumerator (bankTrialLocalNext ring root)
          (fun z => bankTrialC5ActualReturned o z ∨
            bankTrialC5ActualBadExit o z)
          o.after T ≤
        n ^ T * ((2 * (compileAdvice q).b + 2 + 1) * n) := by
  intro x e o ho
  refine ⟨bankTrialC5ActualStartPost ring root S x e o ho, ?_⟩
  intro T
  exact bankTrialC5ActualMeanOfNominatedRank
    ring root o
    (fun z => bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)
    (rank o) (chosen o)
    (hdrop x e o ho) (hnoninc x e o ho)
    (hstart x e o ho) T

theorem bankTrialC5ActualNonreturnBadObstruction {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (u : List (Fin n))
    (hbad : bankTrialC5ActualBadExit o
      (bankTrialLocalRun ring root u o.after))
    (hnot : ¬ bankTrialC5ActualReturned o
      (bankTrialLocalRun ring root u o.after))
    (hfirst : ∀ pre tail : List (Fin n), ∀ f : Fin n,
      u = pre ++ (f :: tail) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root pre o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root pre o.after)))
    (htimeout : bankTrialC5ActualTimeout ring root o u = false) :
    ¬ BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S := by
  intro hkernel
  have hfalse : false = true := by
    simpa only [List.append_nil, htimeout] using
      (hkernel.nonreturnBad x e o ho u []
        hfirst (Or.inr hbad) hnot)
  cases hfalse

def bankTrialC5NonreturnBadTraceSeed :
    GrantBankReference.BankLocalReference (compileAdvice 80).b :=
  { fields := fun i =>
      if i.val = 0 then (.ARMED, false, .E, 0)
      else (.RESET, false, .E, 0),
    success := false }

def bankTrialC5NonreturnBadTraceRoot : Fin 520 :=
  ⟨0, show 0 < 520 by omega⟩

def bankTrialC5NonreturnBadTracePrefix
    (ring : DirectedRing 520) : List (Fin 520) :=
  [bankTrialC5NonreturnBadTraceRoot] ++
    bankTrialC5ComparisonWord ring
      bankTrialC5NonreturnBadTraceRoot (compileAdvice 80).b

noncomputable def bankTrialC5NonreturnBadTraceBefore
    (ring : DirectedRing 520) : BankTrialLocalState 80 :=
  bankTrialLocalRun ring bankTrialC5NonreturnBadTraceRoot
    (bankTrialC5NonreturnBadTracePrefix ring)
    (bankTrialLocalStart bankTrialC5NonreturnBadTraceSeed)

noncomputable def bankTrialC5NonreturnBadTraceOrigin
    (ring : DirectedRing 520) :
    BankTrialC5ActualOrigin 520 80 :=
  { before := bankTrialC5NonreturnBadTraceBefore ring,
    edge := bankTrialC5NonreturnBadTraceRoot,
    after := bankTrialLocalNext ring bankTrialC5NonreturnBadTraceRoot
      (bankTrialC5NonreturnBadTraceBefore ring)
      bankTrialC5NonreturnBadTraceRoot,
    increment := true,
    heads := bankTrialLiveCarryValue
      (bankTrialLocalNext ring bankTrialC5NonreturnBadTraceRoot
        (bankTrialC5NonreturnBadTraceBefore ring)
        bankTrialC5NonreturnBadTraceRoot).bank }

def bankTrialC5NonreturnBadTraceSuffix
    (ring : DirectedRing 520) : List (Fin 520) :=
  [Counter.site ring bankTrialC5NonreturnBadTraceRoot 1,
    Counter.site ring bankTrialC5NonreturnBadTraceRoot 1,
    bankTrialC5NonreturnBadTraceRoot,
    bankTrialC5NonreturnBadTraceRoot]

end L3

/- No existing structure is replaced. -/

namespace L3.Prob

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The actual chronological state after a finite scheduler prefix. -/
def stoppedTapeRun {X : Type} {n : Nat}
    (next : X → Fin n → X) :
    List (Fin n) → X → X
  | [], x => x
  | e :: w, x => stoppedTapeRun next w (next x e)

/-- A stop test may depend on both the consumed prefix and its state.
This says that any one complete word has at most one stopping prefix. -/
def StoppedPrefixFree {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) (x : X) : Prop :=
  ∀ u v : List (Fin n),
    stop u (stoppedTapeRun next u x) = true →
    stop (u ++ v) (stoppedTapeRun next (u ++ v) x) = true →
    v = []

/-- Test the suffix at the first stop, with remaining horizon t.
Unlike a fresh random experiment, every step consumes the actual
successive letter of the same Fin n scheduler word. -/
def firstStoppedSuffixWord {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : X → Nat → List (Fin n) → Bool) :
    Nat → List (Fin n) → X → List (Fin n) → Bool
  | t, pre, x, [] =>
      if stop pre x then A x t [] else false
  | t, pre, x, e :: w =>
      if stop pre x then A x t (e :: w)
      else firstStoppedSuffixWord next stop A (t - 1)
        (pre ++ [e]) (next x e) w

/-- Exact finite list of FIRST stopping prefixes, relative to pre.
Every listed u has length at most t. Under StoppedPrefixFree it is
also the list of ALL stopping prefixes of length at most t.
The algorithm never inserts an overlapping later stop. -/
def firstStoppedPrefixes {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    Nat → List (Fin n) → X → List (List (Fin n))
  | 0, pre, x =>
      if stop pre x then [[]] else []
  | t + 1, pre, x =>
      if stop pre x then [[]]
      else (List.ofFn (fun e : Fin n => e)).flatMap (fun e =>
        (firstStoppedPrefixes next stop t
          (pre ++ [e]) (next x e)).map (List.cons e))

/-- Sum of suffix weights at each first-stopping prefix; the
recursive form makes the original scheduler's first-letter
decomposition explicit. -/
def firstStoppedPrefixSum {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (weight : X → Nat → Nat) :
    Nat → List (Fin n) → X → Nat
  | 0, pre, x =>
      if stop pre x then weight x 0 else 0
  | t + 1, pre, x =>
      if stop pre x then weight x (t + 1)
      else (List.ofFn (fun e : Fin n =>
        firstStoppedPrefixSum next stop weight t
          (pre ++ [e]) (next x e))).sum

/-- First-letter induction: the accepted full-word numerator is the
recursive sum of the correct residual-horizon suffix numerators. -/
private theorem firstStoppedPrefixSumFactor {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : X → Nat → List (Fin n) → Bool) :
    ∀ t pre x,
      scheduleSum n t (fun w =>
        indicator (firstStoppedSuffixWord next stop A t pre x w)) =
      firstStoppedPrefixSum next stop
        (fun y k => scheduleSum n k (fun v => indicator (A y k v)))
        t pre x := by
  intro t
  induction t with
  | zero =>
      intro pre x
      cases hs : stop pre x with
      | false =>
          simp [bankTrialProbabilityScheduleSumZero,
            firstStoppedSuffixWord, firstStoppedPrefixSum, hs,
            indicator]
      | true =>
          simp [bankTrialProbabilityScheduleSumZero,
            firstStoppedSuffixWord, firstStoppedPrefixSum, hs]
  | succ t ih =>
      intro pre x
      cases hs : stop pre x with
      | true =>
          have heq :
              (fun w : List (Fin n) =>
                indicator (firstStoppedSuffixWord next stop A
                  (t + 1) pre x w)) =
              (fun w : List (Fin n) =>
                indicator (A x (t + 1) w)) := by
            funext w
            cases w with
            | nil => simp [firstStoppedSuffixWord, hs]
            | cons e tail =>
                simp [firstStoppedSuffixWord, hs]
          rw [heq]
          simp [firstStoppedPrefixSum, hs]
      | false =>
          rw [bankTrialProbabilityScheduleSumFirst]
          simp only [firstStoppedPrefixSum, hs, Bool.false_eq_true,
            if_false]
          apply ofFn_sum_eq
          intro e
          have heq :
              (fun w : List (Fin n) =>
                indicator (firstStoppedSuffixWord next stop A
                  (t + 1) pre x (e :: w))) =
              (fun w : List (Fin n) =>
                indicator (firstStoppedSuffixWord next stop A
                  t (pre ++ [e]) (next x e) w)) := by
            funext w
            simp [firstStoppedSuffixWord, hs]
          rw [heq]
          exact ih (pre ++ [e]) (next x e)

/-- List-flatMap and summation over a finite collection. -/
private theorem firstStoppedSumFlatMap {U V : Type}
    (xs : List U) (ys : U → List V) (f : V → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Only opaque lengths occur in this arithmetic lemma. -/
private theorem firstStoppedSuccSub (t k : Nat) :
    (t + 1) - (k + 1) = t - k := by
  omega

/-- Prefixing e shifts exactly one letter from the residual
scheduler horizon to the consumed stopping prefix. -/
private theorem firstStoppedStepSum {X : Type} {n : Nat}
    (next : X → Fin n → X) (weight : X → Nat → Nat)
    (x : X) (t : Nat)
    (prefixes : Fin n → List (List (Fin n))) :
    (List.ofFn (fun e : Fin n =>
      ((prefixes e).map (fun u =>
        weight (stoppedTapeRun next u (next x e))
          (t - u.length))).sum)).sum =
    (((List.ofFn (fun e : Fin n => e)).flatMap (fun e =>
      (prefixes e).map (List.cons e))).map (fun u =>
        weight (stoppedTapeRun next u x)
          ((t + 1) - u.length))).sum := by
  rw [firstStoppedSumFlatMap]
  simp only [List.map_ofFn]
  apply ofFn_sum_eq
  intro e
  simp only [List.map_map, Function.comp_def,
    List.length_cons, Nat.succ_eq_add_one, firstStoppedSuccSub]
  rfl

/-- Expands the recursive prefix sum into a literal finite sum over
the stopping prefix list. The state of prefix u is its actual run. -/
private theorem firstStoppedPrefixSumIsList {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (weight : X → Nat → Nat) :
    ∀ t pre x,
      firstStoppedPrefixSum next stop weight t pre x =
      ((firstStoppedPrefixes next stop t pre x).map (fun u =>
        weight (stoppedTapeRun next u x) (t - u.length))).sum := by
  intro t
  induction t with
  | zero =>
      intro pre x
      cases hs : stop pre x with
      | false =>
          simp [firstStoppedPrefixSum, firstStoppedPrefixes, hs]
      | true =>
          simp [firstStoppedPrefixSum, firstStoppedPrefixes,
            stoppedTapeRun, hs]
  | succ t ih =>
      intro pre x
      cases hs : stop pre x with
      | true =>
          simp [firstStoppedPrefixSum, firstStoppedPrefixes,
            stoppedTapeRun, hs]
      | false =>
          calc
            firstStoppedPrefixSum next stop weight (t + 1) pre x =
                (List.ofFn (fun e : Fin n =>
                  firstStoppedPrefixSum next stop weight t
                    (pre ++ [e]) (next x e))).sum := by
                      simp [firstStoppedPrefixSum, hs]
            _ = (List.ofFn (fun e : Fin n =>
                  ((firstStoppedPrefixes next stop t
                    (pre ++ [e]) (next x e)).map (fun u =>
                      weight (stoppedTapeRun next u (next x e))
                        (t - u.length))).sum)).sum := by
                      apply ofFn_sum_eq
                      intro e
                      exact ih (pre ++ [e]) (next x e)
            _ = (((List.ofFn (fun e : Fin n => e)).flatMap
                  (fun e =>
                    (firstStoppedPrefixes next stop t
                      (pre ++ [e]) (next x e)).map
                        (List.cons e))).map (fun u =>
                      weight (stoppedTapeRun next u x)
                        ((t + 1) - u.length))).sum :=
              firstStoppedStepSum next weight x t (fun e =>
                firstStoppedPrefixes next stop t
                  (pre ++ [e]) (next x e))
            _ = ((firstStoppedPrefixes next stop
                  (t + 1) pre x).map (fun u =>
                    weight (stoppedTapeRun next u x)
                      ((t + 1) - u.length))).sum := by
                        simp [firstStoppedPrefixes, hs]

/-- FINITE STOPPED-PREFIX FACTORIZATION.
For a prefix-free stop, firstStoppedPrefixes enumerates precisely
the stopping prefixes u with |u| <= T. Each contribution is the
original-scheduler mass of the residual event A(run u x,T-|u|)
on length-(T-|u|) suffixes, with no independence assumption. -/
theorem stoppedPrefixFactorization {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : X → Nat → List (Fin n) → Bool)
    (x : X) (T : Nat)
    (hfree : StoppedPrefixFree next stop x) :
    scheduleSum n T (fun w =>
      indicator (firstStoppedSuffixWord next stop A T [] x w)) =
    ((firstStoppedPrefixes next stop T [] x).map (fun u =>
      scheduleSum n (T - u.length) (fun v =>
        indicator (A (stoppedTapeRun next u x)
          (T - u.length) v)))).sum := by
  calc
    scheduleSum n T (fun w =>
        indicator (firstStoppedSuffixWord next stop A T [] x w)) =
      firstStoppedPrefixSum next stop
        (fun y k => scheduleSum n k (fun v => indicator (A y k v)))
        T [] x :=
      firstStoppedPrefixSumFactor next stop A T [] x
    _ = _ := firstStoppedPrefixSumIsList next stop
      (fun y k => scheduleSum n k (fun v => indicator (A y k v)))
      T [] x

/-- Antitone means a bound at the shorter remaining horizon t
is at least as strong as the one requested at full horizon T. -/
theorem stoppedPrefixLowerBound {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : X → Nat → List (Fin n) → Bool)
    (x : X) (T D : Nat) (c : Nat → Nat)
    (hanti : ∀ a b, a ≤ b → c b ≤ c a)
    (hlocal : ∀ pre y t,
      stop pre y = true →
      c t * n ^ t ≤
        D * scheduleSum n t (fun v => indicator (A y t v))) :
    c T * scheduleSum n T (fun w =>
        indicator (firstStoppedSuffixWord next stop
          (fun _ _ _ => true) T [] x w)) ≤
      D * scheduleSum n T (fun w =>
        indicator (firstStoppedSuffixWord next stop A T [] x w)) := by
  have htree :
      ∀ t pre y,
        c t * firstStoppedPrefixSum next stop
          (fun (_ : X) k =>
            scheduleSum n k (fun _ : List (Fin n) =>
              indicator true)) t pre y ≤
        D * firstStoppedPrefixSum next stop
          (fun z k => scheduleSum n k
            (fun v => indicator (A z k v))) t pre y := by
    intro t
    induction t with
    | zero =>
        intro pre y
        cases hs : stop pre y with
        | false =>
            simp [firstStoppedPrefixSum, hs]
        | true =>
            have h := hlocal pre y 0 hs
            simpa [firstStoppedPrefixSum, hs,
              indicator, bankTrialProbabilityScheduleSumConst] using h
    | succ t ih =>
        intro pre y
        cases hs : stop pre y with
        | true =>
            have h := hlocal pre y (t + 1) hs
            simpa [firstStoppedPrefixSum, hs,
              indicator, bankTrialProbabilityScheduleSumConst] using h
        | false =>
            have hrow (e : Fin n) :
                c (t + 1) *
                    firstStoppedPrefixSum next stop
                      (fun (_ : X) k =>
                        scheduleSum n k (fun _ : List (Fin n) =>
                          indicator true))
                      t (pre ++ [e]) (next y e) ≤
                D *
                    firstStoppedPrefixSum next stop
                      (fun z k => scheduleSum n k
                        (fun v => indicator (A z k v)))
                      t (pre ++ [e]) (next y e) := by
              calc
                _ ≤ c t *
                    firstStoppedPrefixSum next stop
                      (fun (_ : X) k =>
                        scheduleSum n k (fun _ : List (Fin n) =>
                          indicator true))
                      t (pre ++ [e]) (next y e) :=
                  Nat.mul_le_mul_right _ (hanti t (t + 1)
                    (Nat.le_succ t))
                _ ≤ _ := ih (pre ++ [e]) (next y e)
            have hsum := ofFn_sum_le
              (fun e : Fin n =>
                c (t + 1) * firstStoppedPrefixSum next stop
                  (fun (_ : X) k =>
                    scheduleSum n k (fun _ : List (Fin n) =>
                      indicator true))
                  t (pre ++ [e]) (next y e))
              (fun e : Fin n =>
                D * firstStoppedPrefixSum next stop
                  (fun z k => scheduleSum n k
                    (fun v => indicator (A z k v)))
                  t (pre ++ [e]) (next y e))
              hrow
            rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
            simpa only [firstStoppedPrefixSum, hs,
              Bool.false_eq_true, if_false] using hsum
  have hstop := firstStoppedPrefixSumFactor next stop
    (fun (_ : X) (_ : Nat) (_ : List (Fin n)) => true)
    T [] x
  have hA := firstStoppedPrefixSumFactor next stop A T [] x
  rw [hstop, hA]
  exact htree T [] x

end L3.Prob

/- No structure replacement. -/

namespace L3.Prob

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A finite-list integer tower inequality. No probabilistic or
protocol hypothesis is present. -/
private theorem stoppedPrefixScaledListBound
    {U : Type} (c D : Nat) (f g : U → Nat) :
    ∀ us : List U,
      (∀ u, u ∈ us → c * f u ≤ D * g u) →
      c * ((us.map f).sum) ≤ D * ((us.map g).sum) := by
  intro us
  induction us with
  | nil =>
      intro _
      simp
  | cons a us ih =>
      intro h
      have ha : c * f a ≤ D * g a :=
        h a (by simp)
      have ht : c * ((us.map f).sum) ≤
          D * ((us.map g).sum) := by
        apply ih
        intro u hu
        exact h u (by simp [hu])
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
        (Nat.add_le_add ha ht)

/-- Finite-horizon stopped-prefix lower bound with a FIXED
coefficient c. Unlike stoppedPrefixLowerBound, no antitone
coefficient is needed, and no estimate is demanded at an
unreachable residual horizon. This is the correct interface for
a continuation bound valid only after a nonzero time reserve. -/
theorem stoppedPrefixLowerBoundOnActualCuts
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : X → Nat → List (Fin n) → Bool)
    (x : X) (T c D : Nat)
    (hfree : StoppedPrefixFree next stop x)
    (hlocal :
      ∀ u,
        u ∈ firstStoppedPrefixes next stop T [] x →
        c * n ^ (T - u.length) ≤
          D * scheduleSum n (T - u.length)
            (fun v => indicator
              (A (stoppedTapeRun next u x)
                (T - u.length) v))) :
    c * scheduleSum n T (fun w =>
        indicator
          (firstStoppedSuffixWord next stop
            (fun _ _ _ => true) T [] x w)) ≤
      D * scheduleSum n T (fun w =>
        indicator (firstStoppedSuffixWord next stop A T [] x w)) := by
  have hlocal' :
      ∀ u,
        u ∈ firstStoppedPrefixes next stop T [] x →
        c * scheduleSum n (T - u.length)
            (fun _ : List (Fin n) => indicator true) ≤
          D * scheduleSum n (T - u.length)
            (fun v => indicator
              (A (stoppedTapeRun next u x)
                (T - u.length) v)) := by
    intro u hu
    have h := hlocal u hu
    simpa only [indicator, if_true,
      bankTrialProbabilityScheduleSumConst, Nat.mul_one] using h
  have hsum := stoppedPrefixScaledListBound
    c D
    (fun u : List (Fin n) =>
      scheduleSum n (T - u.length)
        (fun _ : List (Fin n) => indicator true))
    (fun u : List (Fin n) =>
      scheduleSum n (T - u.length)
        (fun v => indicator
          (A (stoppedTapeRun next u x)
            (T - u.length) v)))
    (firstStoppedPrefixes next stop T [] x)
    hlocal'
  rw [stoppedPrefixFactorization next stop
    (fun _ _ _ => true) x T hfree,
    stoppedPrefixFactorization next stop A x T hfree]
  exact hsum

end L3.Prob

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The ONE-ROUND arithmetic, with the required future-continuation
charge made explicit. The latter is not implied by the stage
inequality: it needs an authenticated first-return stopped-prefix
coupling on the SAME scheduler tape.

All variables, including future success mass E, are opaque Naturals.
No compiled advice powers are reduced. -/
theorem bankTrialC5OneRoundOpaqueContinuation
    {D N C X G E Q R : Nat}
    (hstage :
      D * X ≤
        (2 * D * G + 2 * N * X) + (D * Q + 2 * D * R))
    (hsplice : C * G ≤ D * E) :
    C * D * X ≤
      (2 * D * D * E + 2 * C * N * X) +
        (C * D * Q + 2 * C * D * R) := by
  have hcharged :
      (2 * D) * (C * G) ≤ (2 * D) * (D * E) :=
    Nat.mul_le_mul_left (2 * D) hsplice
  calc
    C * D * X = C * (D * X) := by rw [Nat.mul_assoc]
    _ ≤ C * ((2 * D * G + 2 * N * X) +
          (D * Q + 2 * D * R)) :=
      Nat.mul_le_mul_left C hstage
    _ = ((2 * D) * (C * G) + 2 * C * N * X) +
          (C * D * Q + 2 * C * D * R) := by
            simp only [Nat.mul_add, Nat.mul_comm,
              Nat.mul_left_comm, Nat.mul_assoc]
    _ ≤ ((2 * D) * (D * E) + 2 * C * N * X) +
          (C * D * Q + 2 * C * D * R) :=
      Nat.add_le_add_right
        (Nat.add_le_add_right hcharged (2 * C * N * X))
        (C * D * Q + 2 * C * D * R)
    _ = (2 * D * D * E + 2 * C * N * X) +
          (C * D * Q + 2 * C * D * R) := by
            simp only [Nat.mul_assoc]

/-- A conditional one-round inequality for an ACTUAL reachable
ARMED-k seed. Its hsplice is deliberately a separate hypothesis,
not an assertion derived from mere StageClass.good.
The quantity E is the true WON numerator from x, not a ghost mass.
-/
theorem bankTrialC5OneRoundFromCertifiedContinuation
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hreach : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (k : Nat) (harmed : BankTrialC5ArmedAt q x k)
    (T C : Nat)
    (hsplice :
      C * bankTrialC5StageMass ring root S x T .good ≤
      bankTrialProbabilityC5WorkerDenominator q *
        Prob.scheduleSum n T (fun w =>
          if (bankTrialLocalRun ring root w x).phase = .won
          then 1 else 0)) :
    C * bankTrialProbabilityC5WorkerDenominator q * n ^ T ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n T (fun w =>
            if (bankTrialLocalRun ring root w x).phase = .won
            then 1 else 0) +
        2 * C * bankTrialProbabilityC5WorkerNumerator q * n ^ T) +
      (C * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialC5PendingBeforeMass ring root S x T +
        2 * C * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialC5PendingAfterMass ring root S x T) := by
  obtain ⟨begun, hlive, hmode, _, _, _, _⟩ := harmed
  have hgate : BankTrialProbabilityArmedGate x :=
    ⟨⟨begun, hlive⟩, hmode⟩
  have hstage := bankTrialC5OneArmedStage
    ring root S hkernel hlarge hclean pre x hreach hgate T
  exact bankTrialC5OneRoundOpaqueContinuation
    (D := bankTrialProbabilityC5WorkerDenominator q)
    (N := bankTrialProbabilityC5WorkerNumerator q)
    (C := C) (X := n ^ T)
    (G := bankTrialC5StageMass ring root S x T .good)
    (E := Prob.scheduleSum n T (fun w =>
      if (bankTrialLocalRun ring root w x).phase = .won
      then 1 else 0))
    (Q := bankTrialC5PendingBeforeMass ring root S x T)
    (R := bankTrialC5PendingAfterMass ring root S x T)
    hstage hsplice

/-- Zero remaining letters cannot turn an unwon observer into WON.
Consequently NO positive antitone Nat lower coefficient on WON mass
can satisfy the all-horizon premise of stoppedPrefixLowerBound.
This is the exact issue with using that lemma directly for m_k. -/
theorem bankTrialC5AntitoneWonContinuationDegenerates
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : BankTrialLocalState q) (hx : x.phase ≠ .won)
    (D : Nat) (c : Nat → Nat)
    (hanti : ∀ a b, a ≤ b → c b ≤ c a)
    (hbound : ∀ t : Nat,
      c t * n ^ t ≤
        D * Prob.scheduleSum n t (fun w =>
          if (bankTrialLocalRun ring root w x).phase = .won
          then 1 else 0))
    (T : Nat) : c T = 0 := by
  have hzero := hbound 0
  rw [bankTrialProbabilityScheduleSumZero] at hzero
  have hc : c 0 = 0 := by
    simp only [bankTrialLocalRun,
      Nat.pow_zero, Nat.mul_one] at hzero
    simp only [hx, if_false, Nat.mul_zero] at hzero
    omega
  have ht := hanti 0 T (Nat.zero_le T)
  omega

/-- Literal reachable counter-witness for a positive continuation
bound at t=0: state bankTrialLocalStart S, scheduler word [].
It is ARMED with zero heads, but that zero-length word is not WON. -/
theorem bankTrialC5CleanArmedEmptyWordWitness
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5ArmedAt q (bankTrialLocalStart S) 0 ∧
      Prob.scheduleSum n 0 (fun w =>
        if (bankTrialLocalRun ring root w
          (bankTrialLocalStart S)).phase = .won
        then 1 else 0) = 0 := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have ha : BankTrialC5ArmedAt q (bankTrialLocalStart S) 0 := by
    change BankTrialC5ArmedAt q
      (bankTrialC5CleanRun ring root S []) 0
    exact bankTrialC5SeedArmed ring root S hw hclean
  refine ⟨ha, ?_⟩
  rw [bankTrialProbabilityScheduleSumZero]
  simp [bankTrialLocalRun, bankTrialLocalStart]

/-- A second literal phase cut: the real single HEAD word [root]
from CLEAN is LIVE/CSTART, so its empty suffix [] cannot have
completed a comparator. In particular, the comparator stage has
pending mass one at horizon zero, and no immediate good return. -/
theorem bankTrialC5LiteralFirstHeadInterstagePending
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    (bankTrialLocalRun ring root [root]
      (bankTrialLocalStart S)).phase = .live true ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root [root]
        (bankTrialLocalStart S)).bank = .CSTART ∧
    bankTrialC5CStartMass ring root S
      (bankTrialLocalRun ring root [root]
        (bankTrialLocalStart S)) 0 none = 1 := by
  have h := bankTrialC5CleanFirstHeadInterstage
    ring root S hlarge hclean
  refine ⟨?_, ?_, ?_⟩
  · change (bankTrialLocalNext ring root
      (bankTrialLocalStart S) root).phase = .live true
    exact h.1
  · change bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (bankTrialLocalStart S) root).bank = .CSTART
    exact h.2.1
  · unfold bankTrialC5CStartMass bankTrialC5CStartPendingBool
    rw [bankTrialProbabilityScheduleSumZero]
    simp [bankTrialC5PostHeadFirstExit, Prob.indicator]

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- An emitted actual origin initially has the matching LIVE wait mode. -/
theorem bankTrialC5ActualOriginInitiallyActive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    bankTrialC5ActualWorkerActive o o.after := by
  obtain ⟨_, _, hafter, htag, _⟩ :=
    bankTrialC5ActualStartRecordFields ring root S x e o ho
  obtain ⟨_, _, _, ⟨begun, nextBegun, _, hnext⟩, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  refine ⟨⟨nextBegun, ?_⟩, ?_⟩
  · rw [hafter]
    exact hnext
  · rcases hmodes with hinc | hcomp
    · simp [hafter, htag, hinc.2]
    · simp [hafter, htag, hcomp.2]

/-- No matching active worker is simultaneously an authorized return. -/
theorem bankTrialC5ActualActiveNotReturned {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (ha : bankTrialC5ActualWorkerActive o z) :
    ¬ bankTrialC5ActualReturned o z := by
  intro hret
  obtain ⟨⟨begun, hphase⟩, hmode⟩ := ha
  have hshape := bankTrialC5ActualReturnShape o z hret
  cases hinc : o.increment with
  | true =>
    have hi : bankTrialLiveWaveRootMode z.bank = .IWAIT := by
      simpa only [hinc, ↓reduceIte] using hmode
    simp only [hinc, ↓reduceIte] at hshape
    rw [hi] at hshape
    cases hshape
  | false =>
    have hc : bankTrialLiveWaveRootMode z.bank = .CWAIT := by
      simpa only [hinc, Bool.false_eq_true, ↓reduceIte] using hmode
    simp only [hinc, Bool.false_eq_true, ↓reduceIte] at hshape
    rcases hshape with ⟨_, harmed⟩ | ⟨_, hwon⟩
    · obtain ⟨_, _, harm, _, _, _, _⟩ := harmed
      rw [hc] at harm
      cases harm
    · rw [hwon] at hphase
      cases hphase

/-- Nor is the matching LIVE wait mode classified as badExit. -/
theorem bankTrialC5ActualActiveNotBadExit {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (ha : bankTrialC5ActualWorkerActive o z) :
    ¬ bankTrialC5ActualBadExit o z := by
  intro hbad
  obtain ⟨⟨begun, hphase⟩, hmode⟩ := ha
  rcases hbad with hrec | hlost | hwrong | hwon
  · rw [hphase] at hrec
    cases hrec
  · rw [hphase] at hlost
    cases hlost
  · exact hwrong.2.1 ⟨⟨begun, hphase⟩, hmode⟩
  · have hw1 := hwon.1
    rw [hphase] at hw1
    cases hw1

/-- The empty suffix of an emitted origin has not yet exited. -/
theorem bankTrialC5ActualOriginInitiallyUnresolved {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    ¬ (bankTrialC5ActualReturned o o.after ∨
      bankTrialC5ActualBadExit o o.after) := by
  intro hexit
  have ha := bankTrialC5ActualOriginInitiallyActive
    ring root S x e o ho
  rcases hexit with hret | hbad
  · exact bankTrialC5ActualActiveNotReturned o o.after ha hret
  · exact bankTrialC5ActualActiveNotBadExit o o.after ha hbad

/-- Core List decomposition of a nonempty chronological tape. -/
private theorem bankTrialC5NonemptyHasLastEdge {α : Type} :
    ∀ w : List α, w ≠ [] →
      ∃ pre : List α, ∃ e : α, w = pre ++ [e] := by
  intro w
  induction w with
  | nil =>
    intro hn
    exact False.elim (hn rfl)
  | cons e rest ih =>
    intro _
    cases rest with
    | nil =>
      exact ⟨[], e, rfl⟩
    | cons f more =>
      obtain ⟨pre, last, hl⟩ :=
        ih (by intro he; cases he)
      refine ⟨e :: pre, last, ?_⟩
      simpa only [List.cons_append] using
        congrArg (List.cons e) hl

def BankTrialC5ActualFirstBadTimeoutRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  ∀ (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q),
    o ∈ bankTrialC5ActualStarts ring root S x e →
    ∀ (pre : List (Fin n)) (f : Fin n),
      (∀ (u v : List (Fin n)) (g : Fin n),
        pre = u ++ (g :: v) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root u o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root u o.after))) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after)) →
      bankTrialC5ActualBadExit o
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f) →
      ¬ bankTrialC5ActualReturned o
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f) →
      (∃ begun : Bool,
        (bankTrialLocalRun ring root pre o.after).phase =
          .live begun) ∧
      (bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root pre o.after).bank = .IWAIT ∨
       bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root pre o.after).bank = .CWAIT) ∧
      ((bankTrialLocalRun ring root pre o.after).bank.fields
          ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
      (f = root ∨ ring.rightNeighbor f = root) ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f).bank =
          .RESET ∧
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre o.after) f).phase ≠ .won

/-- A witnessed first-exit watchdog persists after appending any suffix. -/
theorem bankTrialC5ActualTimeoutAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (word suffix : List (Fin n))
    (h : bankTrialC5ActualTimeout ring root o word = true) :
    bankTrialC5ActualTimeout ring root o (word ++ suffix) =
      true := by
  unfold bankTrialC5ActualTimeout at h ⊢
  obtain ⟨pre, tail, f, hword, hstrict, hlive, hm, hlease, hf,
    hreset, hnotwon⟩ := of_decide_eq_true h
  apply decide_eq_true
  refine ⟨pre, tail ++ suffix, f, ?_, hstrict, hlive, hm,
    hlease, hf, hreset, hnotwon⟩
  rw [hword]
  simp only [List.append_assoc, List.cons_append]

theorem bankTrialC5ActualNonreturnBadOfOwnerRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hrow : BankTrialC5ActualFirstBadTimeoutRow ring root S) :
    ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      ∀ u v : List (Fin n),
        (∀ pre tail : List (Fin n), ∀ f : Fin n,
          u = pre ++ (f :: tail) →
          ¬ (bankTrialC5ActualReturned o
               (bankTrialLocalRun ring root pre o.after) ∨
             bankTrialC5ActualBadExit o
               (bankTrialLocalRun ring root pre o.after))) →
        (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root u o.after)) →
        ¬ bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root u o.after) →
        bankTrialC5ActualTimeout ring root o (u ++ v) = true := by
  intro x e o ho u v hfirst hexit hnot
  by_cases hnil : u = []
  · rw [hnil] at hexit
    change bankTrialC5ActualReturned o o.after ∨
      bankTrialC5ActualBadExit o o.after at hexit
    exact False.elim
      ((bankTrialC5ActualOriginInitiallyUnresolved
        ring root S x e o ho) hexit)
  · obtain ⟨pre, f, hu⟩ := bankTrialC5NonemptyHasLastEdge u hnil
    have hbefore :
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root pre o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root pre o.after)) :=
      hfirst pre [] f hu
    have hstrict :
        ∀ (a b : List (Fin n)) (g : Fin n),
          pre = a ++ (g :: b) →
          ¬ (bankTrialC5ActualReturned o
               (bankTrialLocalRun ring root a o.after) ∨
             bankTrialC5ActualBadExit o
               (bankTrialLocalRun ring root a o.after)) := by
      intro a b g hab
      apply hfirst a (b ++ [f]) g
      calc
        u = pre ++ [f] := hu
        _ = (a ++ (g :: b)) ++ [f] := by rw [hab]
        _ = a ++ (g :: (b ++ [f])) := by
          simp only [List.append_assoc, List.cons_append]
    have hrun :
        bankTrialLocalRun ring root u o.after =
          bankTrialLocalNext ring root
            (bankTrialLocalRun ring root pre o.after) f := by
      rw [hu, bankTrialLocalRunAppend]
      rfl
    have hnret :
        ¬ bankTrialC5ActualReturned o
          (bankTrialLocalNext ring root
            (bankTrialLocalRun ring root pre o.after) f) := by
      rw [hrun] at hnot
      exact hnot
    have hbad :
        bankTrialC5ActualBadExit o
          (bankTrialLocalNext ring root
            (bankTrialLocalRun ring root pre o.after) f) := by
      rcases hexit with hret | hfail
      · exact False.elim (hnot hret)
      · rw [hrun] at hfail
        exact hfail
    obtain ⟨hlive, hmode, hlease, hincident, hreset, hnotwon⟩ :=
      hrow hsp hlarge hwidth x e o ho pre f
        hstrict hbefore hbad hnret
    unfold bankTrialC5ActualTimeout
    apply decide_eq_true
    refine ⟨pre, v, f, ?_, hstrict, hlive, hmode, hlease,
      hincident, hreset, hnotwon, hbefore⟩
    rw [hu]
    simp only [List.append_assoc, List.singleton_append]

/-- The carry ledger gives the one-sided coverage inequality.
Exact coverage additionally needs the reverse comparison. -/
theorem bankTrialC5ActualOriginHeadCreditLeCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z =
      bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S z e) :
    o.heads ≤ bankTrialLiveHeadCount ring root (pre ++ [e])
      (bankTrialLocalStart S) := by
  obtain ⟨_, _, _, _, hheads⟩ :=
    bankTrialC5ActualStartRecordFields ring root S z e o ho
  obtain ⟨_, _, _, ⟨_, nextBegun, _, hnext⟩, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S z e o ho
  have hstate :
      bankTrialLocalRun ring root (pre ++ [e])
          (bankTrialLocalStart S) =
        bankTrialLocalNext ring root z e := by
    rw [bankTrialLocalRunAppend, ← hz]
    rfl
  have hlive :
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S)).phase = .live nextBegun := by
    rw [hstate]
    exact hnext
  have hledger := bankTrialProbabilityLockedCarryCleanWords
    ring root hw S hclean (pre ++ [e])
  have hbound := hledger nextBegun hlive
  rw [hstate] at hbound
  rw [hheads]
  exact hbound

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- If neither first-exit class holds, the worker is LIVE in its
own IWAIT or CWAIT mode. No reachability premise is needed. -/
theorem bankTrialC5ActualUnresolvedIsActive {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (h : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    bankTrialC5ActualWorkerActive o z := by
  have hret : ¬ bankTrialC5ActualReturned o z := by
    intro hr
    exact h (Or.inl hr)
  have hbad : ¬ bankTrialC5ActualBadExit o z := by
    intro hb
    exact h (Or.inr hb)
  cases hp : z.phase with
  | live begun =>
    by_cases ha : bankTrialC5ActualWorkerActive o z
    · exact ha
    · have hb : bankTrialC5ActualBadExit o z :=
        Or.inr (Or.inr (Or.inl
          ⟨⟨begun, hp⟩, ha, hret⟩))
      exact False.elim (hbad hb)
  | recovery =>
    exact False.elim (hbad (Or.inl hp))
  | lost =>
    exact False.elim (hbad (Or.inr (Or.inl hp)))
  | won =>
    exact False.elim (hbad (Or.inr (Or.inr
      (Or.inr ⟨hp, hret⟩))))

/-- On a nonincident edge the root quad is framed, success is not
set, and an old LIVE matching wait remains LIVE with the same mode. -/
theorem bankTrialC5ActualNonincidentActiveNext {n q : Nat}
    (ring : DirectedRing n) (root f : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (o : BankTrialC5ActualOrigin n q)
    (hf : B.success = false)
    (ha : bankTrialC5ActualWorkerActive o
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hne : f ≠ root)
    (hni : ring.rightNeighbor f ≠ root) :
    bankTrialC5ActualWorkerActive o
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) f) := by
  have hframe := bankTrialLocalRootNonincidentFrame
    ring root f B hf hne hni
  have hm :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B f) =
      bankTrialLiveWaveRootMode B := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B f).fields ⟨0, by omega⟩).1 =
      (B.fields ⟨0, by omega⟩).1
    exact congrArg (fun p => p.1) hframe
  have hnotArmed : bankTrialLiveWaveRootMode B ≠ .ARMED := by
    intro hc
    rw [ha.2] at hc
    split at hc <;> cases hc
  have hnotReset : bankTrialLiveWaveRootMode B ≠ .RESET := by
    intro hc
    rw [ha.2] at hc
    split at hc <;> cases hc
  have hs :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B f).success = false :=
    bankTrialLocalUnlatchedNonrootNoWin
      ring root f B hf hne
  have hnotClean :
      ¬ BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B f) := by
    intro hc
    exact hnotArmed (hm.symm.trans hc.2.1)
  have hnotResetStep :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B f).fields ⟨0, by omega⟩).1 ≠ .RESET := by
    intro hc
    exact hnotReset (hm.symm.trans hc)
  have hnext :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) f).phase =
        .live (begun ||
          decide (f = root ∨ ring.rightNeighbor f = root)) := by
    simp [bankTrialLocalNext, hs, hnotClean]
    split
    · rename_i hr
      exact absurd hr hnotResetStep
    · rfl
  have hnextMode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
        (if o.increment then .IWAIT else .CWAIT) := by
    rw [bankTrialLocalNextLiveBank ring root f B begun, hm]
    exact ha.2
  exact ⟨⟨_, hnext⟩, hnextMode⟩

/-- Every first bad successor of an actual origin must use the
outgoing root edge or the incoming root edge. -/
theorem bankTrialC5ActualFirstBadRootIncident {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre o.after)
    (hbefore : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (f : Fin n)
    (hbad : bankTrialC5ActualBadExit o
      (bankTrialLocalNext ring root z f)) :
    f = root ∨ ring.rightNeighbor f = root := by
  by_cases he : f = root
  · exact Or.inl he
  · by_cases hin : ring.rightNeighbor f = root
    · exact Or.inr hin
    · have ha := bankTrialC5ActualUnresolvedIsActive o z hbefore
      obtain ⟨⟨begun, hp⟩, _⟩ := id ha
      have hzeta :
          z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
        cases z with
        | mk B phase =>
          change phase = .live begun at hp
          cases hp
          rfl
      obtain ⟨hclean, ⟨word, hword⟩, _, _, _⟩ :=
        bankTrialC5ActualStartGuardFacts ring root S x e o ho
      have hfull := bankTrialC5GoodReturnReachable
        ring root S word x hword.symm e o ho pre
      have hreach :
          bankTrialLocalRun ring root (word ++ (e :: pre))
            (bankTrialLocalStart S) =
          (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
        exact (hz.trans hfull).symm.trans hzeta
      have hf : z.bank.success = false :=
        bankTrialProbabilityCleanLiveUnlatched
          ring root S hclean (word ++ (e :: pre))
          z.bank begun hreach
      have hac :
          bankTrialC5ActualWorkerActive o
            (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
        rw [← hzeta]
        exact ha
      have hnext :
          bankTrialC5ActualWorkerActive o
            (bankTrialLocalNext ring root z f) := by
        rw [hzeta]
        exact bankTrialC5ActualNonincidentActiveNext
          ring root f z.bank begun o hf hac he hin
      exact False.elim
        ((bankTrialC5ActualActiveNotBadExit o
          (bankTrialLocalNext ring root z f) hnext) hbad)

/-- The actual census records the true Boolean launch kind. -/
theorem bankTrialC5ActualIncrementTagExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    o.increment =
      decide (bankTrialLiveWaveRootMode x.bank = .ARMED) := by
  obtain ⟨_, _, _, htag, _⟩ :=
    bankTrialC5ActualStartRecordFields ring root S x e o ho
  obtain ⟨_, _, _, _, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  rcases hmodes with hinc | hcomp
  · calc
      o.increment =
          (bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root x e).bank == .IWAIT) := htag
      _ = true := by rw [hinc.2]; rfl
      _ = decide (bankTrialLiveWaveRootMode x.bank = .ARMED) := by
        rw [hinc.1]
        rfl
  · have hnot :
        ¬ bankTrialLiveWaveRootMode x.bank = .ARMED := by
      intro h
      rw [hcomp.1] at h
      cases h
    calc
      o.increment =
          (bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root x e).bank == .IWAIT) := htag
      _ = false := by rw [hcomp.2]; rfl
      _ = decide (bankTrialLiveWaveRootMode x.bank = .ARMED) :=
        (decide_eq_false hnot).symm

/-- The completed-head invariant, not merely the one-sided
carry ledger, yields exact head-count equality at launch. -/
theorem bankTrialC5ActualOriginHeadCountExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    o.heads = bankTrialLiveHeadCount ring root (pre ++ [e])
      (bankTrialLocalStart S) := by
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    rw [hs] at hsp
    have hn : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hn
    omega
  have hK : 0 < (compileAdvice q).K := by
    change 0 < 2 * q + productionKappa q
    omega
  have hstep : BankTrialC5CompletedHeadEdgePreservation ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep (pre ++ [e])
  obtain ⟨_, _, _, _, hheads⟩ :=
    bankTrialC5ActualStartRecordFields ring root S x e o ho
  obtain ⟨_, _, _, ⟨_, nextBegun, _, hnext⟩, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have hstate :
      bankTrialLocalRun ring root (pre ++ [e])
          (bankTrialLocalStart S) =
        bankTrialLocalNext ring root x e := by
    rw [bankTrialLocalRunAppend, ← hx]
    rfl
  have hlive :
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S)).phase = .live nextBegun := by
    rw [hstate]
    exact hnext
  have hcarry := hInv.liveCarry nextBegun hlive
  rw [hstate] at hcarry
  exact hheads.trans hcarry

def BankTrialC5ActualIncidentBadFinishRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  ∀ (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q),
    o ∈ bankTrialC5ActualStarts ring root S x e →
    ∀ (pre : List (Fin n)) (f : Fin n),
      (f = root ∨ ring.rightNeighbor f = root) →
      (∀ (u v : List (Fin n)) (g : Fin n),
        pre = u ++ (g :: v) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root u o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root u o.after))) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after)) →
      bankTrialC5ActualBadExit o
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f) →
      ¬ bankTrialC5ActualReturned o
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f) →
      ((bankTrialLocalRun ring root pre o.after).bank.fields
        ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f).bank =
          .RESET ∧
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre o.after) f).phase ≠ .won

theorem bankTrialC5ActualFirstBadTimeoutRowOfIncidentRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hincident : BankTrialC5ActualIncidentBadFinishRow
      ring root S) :
    BankTrialC5ActualFirstBadTimeoutRow ring root S := by
  intro hsp hlarge hwidth x e o ho pre f hstrict hbefore hbad hnot
  have ha := bankTrialC5ActualUnresolvedIsActive o
    (bankTrialLocalRun ring root pre o.after) hbefore
  have he := bankTrialC5ActualFirstBadRootIncident
    ring root S x e o ho pre
    (bankTrialLocalRun ring root pre o.after)
    rfl hbefore f hbad
  have hmode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre o.after).bank = .IWAIT ∨
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre o.after).bank = .CWAIT := by
    cases hi : o.increment with
    | true =>
      apply Or.inl
      simpa only [hi, ↓reduceIte] using ha.2
    | false =>
      apply Or.inr
      simpa only [hi, Bool.false_eq_true, ↓reduceIte] using ha.2
  obtain ⟨hlease, hreset, hnotwon⟩ :=
    hincident hsp hlarge hwidth x e o ho pre f he
      hstrict hbefore hbad hnot
  exact ⟨ha.1, hmode, hlease, he, hreset, hnotwon⟩

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Clamping the numeric lease cannot change the BANK mode. -/
theorem bankTrialC5ClampedMode
    (q : Nat) (z : BankCell) :
    (GrantBankReference.bankLocalReferenceClampedQuad q z).1 =
      z.mode := by
  simp [GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank]

/-- Literal incoming owner: an old IWAIT or CWAIT is unchanged
with lease > 1, or resets when the lease is at most one. -/
theorem bankTrialC5IncomingWaitRawClassification
    (q : Nat) (z : BankCell)
    (hwait : z.mode = .IWAIT ∨ z.mode = .CWAIT) :
    (((GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap z)).1 = z.mode) ∧
        1 < z.lease) ∨
    (((GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap z)).1 = .RESET) ∧
        z.lease ≤ 1) := by
  simp only [bankTrialC5ClampedMode]
  rcases hwait with hm | hm
  · by_cases hl : 1 < z.lease
    · exact Or.inl ⟨by simp [GrantBankReference.incomingRootBankMap,
        hm, hl, isWaitMode], hl⟩
    · exact Or.inr ⟨by simp [GrantBankReference.incomingRootBankMap,
        hm, hl, isWaitMode], by omega⟩
  · by_cases hl : 1 < z.lease
    · exact Or.inl ⟨by simp [GrantBankReference.incomingRootBankMap,
        hm, hl, isWaitMode], hl⟩
    · exact Or.inr ⟨by simp [GrantBankReference.incomingRootBankMap,
        hm, hl, isWaitMode], by omega⟩

/-- Exhaustive literal BANK pair root-owner classification in a
waiting mode. The only non-waiting branches are AL return,
CL0 return, CL1 acceptance, and watchdog expiration.
No reachability or independent scheduler is assumed. -/
theorem bankTrialC5OutgoingWaitRawClassification
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hwait : x.mode = .IWAIT ∨ x.mode = .CWAIT) :
    ((bankPair x y 1 b theta).1.mode = x.mode ∧
      1 < x.lease) ∨
    ((bankPair x y 1 b theta).1.mode = .RESET ∧
      x.lease ≤ 1) ∨
    (x.mode = .IWAIT ∧ y.tok = .AL ∧
      (bankPair x y 1 b theta).1.mode = .CSTART) ∨
    (x.mode = .CWAIT ∧ y.tok = .CL0 ∧
      (bankPair x y 1 b theta).1.mode = .ARMED) ∨
    (x.mode = .CWAIT ∧ y.tok = .CL1 ∧
      (bankPair x y 1 b theta).1.mode = .RESET) := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hwait with hm | hm
  · cases ht : y.tok <;>
      by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, ht, hl, hbpos,
        hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] <;> omega
  · cases ht : y.tok <;>
      by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, ht, hl, hbpos,
        hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] <;> omega

/-- Public clamped incoming-root lift of the exact unary mode
split. Physical nonalias rules out the simultaneous root-outgoing
owner; other protected-digit updates are irrelevant. -/
theorem bankTrialC5IncomingWaitPhysicalClassification {n q : Nat}
    (ring : DirectedRing n) (root f : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hwait : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hin : ring.rightNeighbor f = root) :
    (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
        bankTrialLiveWaveRootMode B ∧
      1 < (B.fields ⟨0, by omega⟩).2.2.2) ∨
    (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
        .RESET ∧
      (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1) := by
  have hne := bankTrialC5IncomingNotRoot ring root f hw hin
  have hsource :
      ¬ (0 < (compileAdvice q).b ∧
        f = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa only [Counter.site] using h.2)
  have htarget :
      ¬ (0 < (0 : Nat) ∧
        f = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have htop :
      ¬ ((0 : Nat) = (compileAdvice q).b ∧
        f = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hb := bankTrialCmpWidth q
    omega
  have hs : Counter.Support q ring root f := Or.inl hin
  have hfield :=
    (bankTrialLocalStepField ring root f B hs hf
      ⟨0, by omega⟩).trans
      (bankTrialLocalSelectedIncoming ring root f B
        ⟨0, by omega⟩ hsource htarget htop ⟨rfl, hin⟩)
  have hmodeEq :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by omega⟩))).1 := by
    rw [bankTrialLocalNextLiveBank ring root f B begun]
    exact congrArg (fun v : Mode × Bool × BTok × Nat => v.1)
      hfield
  have hraw := bankTrialC5IncomingWaitRawClassification q
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩) hwait
  rcases hraw with ⟨hmode, hlease⟩ | ⟨hreset, hlease⟩
  · exact Or.inl ⟨hmodeEq.trans hmode, hlease⟩
  · exact Or.inr ⟨hmodeEq.trans hreset, hlease⟩

/-- A LIVE worker's incoming-root bad exit can occur only when
the old lease expires. This case needs neither a rank nor the
completed-head ledger. -/
theorem bankTrialC5IncomingWaitBadFinish {n q : Nat}
    (ring : DirectedRing n) (root f : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (o : BankTrialC5ActualOrigin n q)
    (hf : B.success = false)
    (ha : bankTrialC5ActualWorkerActive o
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hin : ring.rightNeighbor f = root)
    (hbad : bankTrialC5ActualBadExit o
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) f)) :
    (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
        .RESET ∧
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) f).phase ≠ .won := by
  have hwait :
      bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT := by
    cases hi : o.increment with
    | true =>
      exact Or.inl (by simpa only [hi, ↓reduceIte] using ha.2)
    | false =>
      exact Or.inr (by simpa only [hi, Bool.false_eq_true,
        ↓reduceIte] using ha.2)
  have hne := bankTrialC5IncomingNotRoot ring root f hw hin
  have hnotwon :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) f).phase ≠
        .won := by
    intro hwinner
    have hguard := bankTrialProbabilityLiveWonRequiresOldGuard
      ring root f B begun hf hwinner
    exact hne hguard.1
  rcases bankTrialC5IncomingWaitPhysicalClassification
      ring root f hw B begun hf hwait hin with
      ⟨hmode, hlease⟩ | ⟨hreset, hlease⟩
  · have hnotArmed : bankTrialLiveWaveRootMode B ≠ .ARMED := by
      intro har
      rw [ha.2] at har
      split at har <;> cases har
    have hnotReset : bankTrialLiveWaveRootMode B ≠ .RESET := by
      intro hr
      rw [ha.2] at hr
      split at hr <;> cases hr
    have hsuccess :
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B f).success = false :=
      bankTrialLocalUnlatchedNonrootNoWin ring root f B hf hne
    have hnotClean :
        ¬ BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B f) := by
      intro hc
      have hnew :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
            .ARMED := by
        rw [bankTrialLocalNextLiveBank ring root f B begun]
        exact hc.2.1
      exact hnotArmed (hmode.symm.trans hnew)
    have hnotResetStep :
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B f).fields ⟨0, by omega⟩).1 ≠ .RESET := by
      intro hr
      have hnew :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
            .RESET := by
        rw [bankTrialLocalNextLiveBank ring root f B begun]
        exact hr
      exact hnotReset (hmode.symm.trans hnew)
    have hphase :
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f).phase =
        .live (begun ||
          decide (f = root ∨ ring.rightNeighbor f = root)) := by
      simp [bankTrialLocalNext, hsuccess, hnotClean]
      split
      · rename_i hr
        exact absurd hr hnotResetStep
      · rfl
    have hnewActive : bankTrialC5ActualWorkerActive o
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f) :=
      ⟨⟨_, hphase⟩, hmode.trans ha.2⟩
    exact False.elim ((bankTrialC5ActualActiveNotBadExit o
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) f)
      hnewActive) hbad)
  · exact ⟨hlease, hreset, hnotwon⟩

/-- Exact old CLEAN-run suffix still has an unlatched root
whenever it is LIVE. This avoids assuming an arbitrary local
IWAIT/CWAIT snapshot is authenticated. -/
theorem bankTrialC5ActualPrefixLiveUnlatched {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n)) (begun : Bool)
    (hlive :
      (bankTrialLocalRun ring root pre o.after).phase = .live begun) :
    (bankTrialLocalRun ring root pre o.after).bank.success =
      false := by
  obtain ⟨_, ⟨w, hw⟩, _, _, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have hreachable := bankTrialC5GoodReturnReachable
    ring root S w x hw.symm e o ho pre
  have hzeta :
      bankTrialLocalRun ring root pre o.after =
        (⟨(bankTrialLocalRun ring root pre o.after).bank,
          .live begun⟩ : BankTrialLocalState q) := by
    generalize bankTrialLocalRun ring root pre o.after = z at hlive ⊢
    cases z with
    | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      rfl
  have hfull :
      bankTrialLocalRun ring root (w ++ (e :: pre))
        (bankTrialLocalStart S) =
      (⟨(bankTrialLocalRun ring root pre o.after).bank,
        .live begun⟩ : BankTrialLocalState q) :=
    hreachable.symm.trans hzeta
  exact bankTrialProbabilityCleanLiveUnlatched
    ring root S hclean (w ++ (e :: pre))
    (bankTrialLocalRun ring root pre o.after).bank begun hfull

def BankTrialC5ActualOutgoingBadFinishRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  ∀ (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q),
    o ∈ bankTrialC5ActualStarts ring root S x e →
    ∀ pre : List (Fin n),
      (∀ (u v : List (Fin n)) (g : Fin n),
        pre = u ++ (g :: v) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root u o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root u o.after))) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after)) →
      bankTrialC5ActualBadExit o
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) root) →
      ¬ bankTrialC5ActualReturned o
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) root) →
      ((bankTrialLocalRun ring root pre o.after).bank.fields
        ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) root).bank =
          .RESET ∧
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre o.after) root).phase ≠ .won

theorem bankTrialC5ActualIncidentBadFinishOfOutgoing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (hout : BankTrialC5ActualOutgoingBadFinishRow ring root S) :
    BankTrialC5ActualIncidentBadFinishRow ring root S := by
  intro hsp hlarge hwidth x e o ho pre f hincident
    hstrict hbefore hbad hnot
  rcases hincident with hroot | hin
  · subst f
    exact hout hsp hlarge hwidth x e o ho pre
      hstrict hbefore hbad hnot
  · have ha := bankTrialC5ActualUnresolvedIsActive o
      (bankTrialLocalRun ring root pre o.after) hbefore
    obtain ⟨⟨begun, hlive⟩, hmode⟩ := id ha
    have hzeta :
        bankTrialLocalRun ring root pre o.after =
        (⟨(bankTrialLocalRun ring root pre o.after).bank,
          .live begun⟩ : BankTrialLocalState q) := by
      generalize bankTrialLocalRun ring root pre o.after = z at hlive ⊢
      cases z with
      | mk B phase =>
        change phase = .live begun at hlive
        cases hlive
        rfl
    have hf := bankTrialC5ActualPrefixLiveUnlatched
      ring root S hclean x e o ho pre begun hlive
    have hac :
        bankTrialC5ActualWorkerActive o
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) := by
      rw [← hzeta]
      exact ha
    have hbad' : bankTrialC5ActualBadExit o
        (bankTrialLocalNext ring root
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) f) := by
      rw [← hzeta]
      exact hbad
    rw [hzeta]
    exact bankTrialC5IncomingWaitBadFinish ring root f hw
      (bankTrialLocalRun ring root pre o.after).bank
      begun o hf hac hin hbad'

theorem bankTrialC5ActualFirstBadTimeoutRowOfOutgoing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (hout : BankTrialC5ActualOutgoingBadFinishRow ring root S) :
    BankTrialC5ActualFirstBadTimeoutRow ring root S := by
  exact bankTrialC5ActualFirstBadTimeoutRowOfIncidentRows
    ring root S
    (bankTrialC5ActualIncidentBadFinishOfOutgoing
      ring root S hw hclean hout)

theorem bankTrialC5ActualNonreturnBadOfOutgoing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (hout : BankTrialC5ActualOutgoingBadFinishRow ring root S) :
    ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      ∀ u v : List (Fin n),
        (∀ pre tail : List (Fin n), ∀ f : Fin n,
          u = pre ++ (f :: tail) →
          ¬ (bankTrialC5ActualReturned o
              (bankTrialLocalRun ring root pre o.after) ∨
            bankTrialC5ActualBadExit o
              (bankTrialLocalRun ring root pre o.after))) →
        (bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root u o.after) ∨
          bankTrialC5ActualBadExit o
            (bankTrialLocalRun ring root u o.after)) →
        ¬ bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root u o.after) →
        bankTrialC5ActualTimeout ring root o (u ++ v) = true := by
  exact bankTrialC5ActualNonreturnBadOfOwnerRows ring root S
    hsp hlarge hwidth
    (bankTrialC5ActualFirstBadTimeoutRowOfOutgoing
      ring root S hw hclean hout)

end L3


namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An unresolved actual worker cannot be an ARMED head gate. -/
private theorem bankTrialC5ActualUnresolvedNoHeadGate {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (h : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    ¬ BankTrialProbabilityArmedGate z := by
  intro hg
  have ha := bankTrialC5ActualUnresolvedIsActive o z h
  have hm : bankTrialLiveWaveRootMode z.bank = .ARMED := hg.2
  rw [ha.2] at hm
  split at hm <;> cases hm

/-- On a suffix with no earlier return or bad exit, no additional
chronological head is paid. This is valid even if the state at the
end of the suffix is itself the first exit. -/
theorem bankTrialC5ActualHeadCountZeroBeforeFirstExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (word : List (Fin n))
    (hbefore : ∀ (pre tail : List (Fin n)) (f : Fin n),
      word = pre ++ (f :: tail) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after))) :
    bankTrialLiveHeadCount ring root word o.after = 0 := by
  have hrev : ∀ rev : List (Fin n),
      (∀ (pre tail : List (Fin n)) (f : Fin n),
        rev.reverse = pre ++ (f :: tail) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root pre o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root pre o.after))) →
      bankTrialLiveHeadCount ring root rev.reverse o.after = 0 := by
    intro rev
    induction rev with
    | nil =>
        intro _
        rfl
    | cons f rest ih =>
        intro hp
        have hshort :
            ∀ (pre tail : List (Fin n)) (g : Fin n),
              rest.reverse = pre ++ (g :: tail) →
              ¬ (bankTrialC5ActualReturned o
                   (bankTrialLocalRun ring root pre o.after) ∨
                 bankTrialC5ActualBadExit o
                   (bankTrialLocalRun ring root pre o.after)) := by
          intro pre tail g heq
          apply hp pre (tail ++ [f]) g
          rw [List.reverse_cons, heq]
          simp only [List.append_assoc, List.cons_append]
        have hcurrent :
            ¬ (bankTrialC5ActualReturned o
                 (bankTrialLocalRun ring root rest.reverse o.after) ∨
               bankTrialC5ActualBadExit o
                 (bankTrialLocalRun ring root rest.reverse o.after)) :=
          hp rest.reverse [] f (by simp only [List.reverse_cons])
        have hnogate : ¬ BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root rest.reverse o.after) :=
          bankTrialC5ActualUnresolvedNoHeadGate o
            (bankTrialLocalRun ring root rest.reverse o.after)
            hcurrent
        rw [List.reverse_cons, bankTrialC5StrengthenedSnocHeads,
          ih hshort]
        simp [hnogate]
  have h := hrev word.reverse (by
    intro pre tail f heq
    apply hbefore pre tail f
    simpa only [List.reverse_reverse] using heq)
  simpa only [List.reverse_reverse] using h

/-- The origin's recorded heads remain the absolute chronological
head count through its first exit, for the very same original tape. -/
theorem bankTrialC5ActualOriginChronologicalHeadLedger {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root u o.after))) :
    ∃ launch : List (Fin n),
      bankTrialLocalRun ring root launch (bankTrialLocalStart S) = x ∧
      bankTrialLiveHeadCount ring root (launch ++ (e :: pre))
        (bankTrialLocalStart S) = o.heads := by
  obtain ⟨_, ⟨launch, hlaunch⟩, _, _, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have hlaunchHeads := bankTrialC5ActualOriginHeadCountExact
    ring root S hsp hlarge hwidth hclean
    launch x hlaunch.symm e o ho
  have hpost :
      bankTrialLocalRun ring root (launch ++ [e])
        (bankTrialLocalStart S) = o.after := by
    rw [bankTrialC5StrengthenedSnocRun, hlaunch]
    exact (bankTrialC5ActualStartPost ring root S x e o ho).symm
  have hzero := bankTrialC5ActualHeadCountZeroBeforeFirstExit
    ring root o pre hbefore
  refine ⟨launch, hlaunch, ?_⟩
  have hsplit :
      launch ++ (e :: pre) = (launch ++ [e]) ++ pre := by
    simp only [List.append_assoc, List.singleton_append]
  rw [hsplit, bankTrialLiveHeadCountAppend, hpost,
    hzero, Nat.add_zero]
  exact hlaunchHeads.symm

/-- The numeric carry equals the origin's fixed head count at any
LIVE state through the first exit. In particular, it also applies
to a LIVE matching-return state, not just unresolved waits. -/
theorem bankTrialC5ActualOriginLiveCarryBeforeFirstExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root u o.after)))
    (begun : Bool)
    (hlive : (bankTrialLocalRun ring root pre o.after).phase =
      .live begun) :
    bankTrialLiveCarryValue
      (bankTrialLocalRun ring root pre o.after).bank = o.heads := by
  obtain ⟨launch, hlaunch, hcount⟩ :=
    bankTrialC5ActualOriginChronologicalHeadLedger
      ring root S hsp hlarge hwidth hclean
      x e o ho pre hbefore
  have hstate :
      bankTrialLocalRun ring root (launch ++ (e :: pre))
        (bankTrialLocalStart S) =
      bankTrialLocalRun ring root pre o.after :=
    (bankTrialC5GoodReturnReachable
      ring root S launch x hlaunch.symm e o ho pre).symm
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
        decide (q ≤ qStar) := rfl
    have hn : ¬ q ≤ qStar :=
      of_decide_eq_false (hs.symm.trans hsp)
    change ¬ q ≤ 79 at hn
    omega
  have hK : 0 < (compileAdvice q).K := by
    change 0 < 2 * q + productionKappa q
    omega
  have hstep : BankTrialC5CompletedHeadEdgePreservation ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep (launch ++ (e :: pre))
  have hfullLive :
      (bankTrialLocalRun ring root (launch ++ (e :: pre))
        (bankTrialLocalStart S)).phase = .live begun := by
    rw [hstate]
    exact hlive
  have hcarry := hInv.liveCarry begun hfullLive
  rw [hstate, hcount] at hcarry
  exact hcarry

/-- The actual run invariant: until (but not including) its first
exit, the origin remains LIVE in its recorded wait kind and its
numeric carry equals its recorded head count. -/
theorem bankTrialC5ActualOriginRunLedger {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root u o.after)))
    (hcurrent :
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after))) :
    (∃ begun : Bool,
      (bankTrialLocalRun ring root pre o.after).phase =
        .live begun) ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre o.after).bank =
        (if o.increment then .IWAIT else .CWAIT) ∧
    bankTrialLiveCarryValue
      (bankTrialLocalRun ring root pre o.after).bank =
        o.heads := by
  obtain ⟨⟨begun, hlive⟩, hmode⟩ :=
    bankTrialC5ActualUnresolvedIsActive o
      (bankTrialLocalRun ring root pre o.after) hcurrent
  have hcarry :=
    bankTrialC5ActualOriginLiveCarryBeforeFirstExit
      ring root S hsp hlarge hwidth hclean
      x e o ho pre hbefore begun hlive
  exact ⟨⟨begun, hlive⟩, hmode, hcarry⟩

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The raw five-way waiting-mode classification lifted to the
physical outgoing root edge. No origin-history claim is made. -/
theorem bankTrialC5OutgoingWaitPhysicalCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hwait : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) :
    (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        bankTrialLiveWaveRootMode B ∧
      1 < (B.fields ⟨0, by omega⟩).2.2.2) ∨
    (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        .RESET ∧
      (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1) ∨
    (bankTrialLiveWaveRootMode B = .IWAIT ∧
      bankTrialLiveWaveToken B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .AL ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        .CSTART) ∨
    (bankTrialLiveWaveRootMode B = .CWAIT ∧
      bankTrialLiveWaveToken B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL0 ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        .ARMED) ∨
    (bankTrialLiveWaveRootMode B = .CWAIT ∧
      bankTrialLiveWaveToken B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL1 ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        .RESET) := by
  have hb : 1 < (compileAdvice q).b := by
    have hwidth := bankTrialCmpWidth q
    omega
  have hraw := bankTrialC5OutgoingWaitRawClassification
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by omega⟩)
    hb rfl rfl rfl hwait
  have hprojection :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
      (bankPair
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by omega⟩)
        1 (compileAdvice q).b (compileAdvice q).theta).1.mode := by
    rw [bankTrialLocalNextLiveBank ring root root B begun]
    exact (bankTrialCmpRoot ring root hw B hf).1
  rcases hraw with hstay | htimeout | hal | hclzero | hclone
  · exact Or.inl ⟨hprojection.trans hstay.1, hstay.2⟩
  · exact Or.inr (Or.inl
      ⟨hprojection.trans htimeout.1, htimeout.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨hal.1, hal.2.1, hprojection.trans hal.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hclzero.1, hclzero.2.1,
        hprojection.trans hclzero.2.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hclone.1, hclone.2.1,
        hprojection.trans hclone.2.2⟩)))

/-- Two ARMED certificates of the same observer have the same count. -/
theorem bankTrialC5ArmedCountUnique {q : Nat}
    (z : BankTrialLocalState q) (a b : Nat)
    (ha : BankTrialC5ArmedAt q z a)
    (hb : BankTrialC5ArmedAt q z b) :
    a = b := by
  obtain ⟨_, _, _, _, hvalueA, _, _⟩ := ha
  obtain ⟨_, _, _, _, hvalueB, _, _⟩ := hb
  exact hvalueA.symm.trans hvalueB

/-- An ARMED return with a different head count is a nonreturning
bad exit for the *old* comparator origin, even though it is a
perfectly legitimate return for a later comparator origin. -/
theorem bankTrialC5ActualLaterArmedBad {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q) (k : Nat)
    (hinc : o.increment = false)
    (hne : k ≠ o.heads)
    (harmed : BankTrialC5ArmedAt q z k) :
    bankTrialC5ActualBadExit o z ∧
    ¬ bankTrialC5ActualReturned o z ∧
    bankTrialLiveWaveRootMode z.bank ≠ .RESET := by
  obtain ⟨begun, hphase, hmode, _, _, _, _⟩ := id harmed
  have hnot : ¬ bankTrialC5ActualReturned o z := by
    intro hr
    unfold bankTrialC5ActualReturned at hr
    simp only [hinc, Bool.false_eq_true, ↓reduceIte] at hr
    rcases hr with hlow | hwon
    · have hcount := bankTrialC5ArmedCountUnique z
        o.heads k hlow.2 harmed
      exact hne hcount.symm
    · rw [hphase] at hwon
      cases hwon.2
  have hnotActive : ¬ bankTrialC5ActualWorkerActive o z := by
    intro ha
    have hc : bankTrialLiveWaveRootMode z.bank = .CWAIT := by
      simpa only [hinc, Bool.false_eq_true, ↓reduceIte] using ha.2
    rw [hmode] at hc
    cases hc
  refine ⟨Or.inr (Or.inr (Or.inl
    ⟨⟨begun, hphase⟩, hnotActive, hnot⟩)), hnot, ?_⟩
  rw [hmode]
  intro hreset
  cases hreset

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- CL1 at a locked CWAIT root authenticates the full compiled K
comparison. This uses no origin census or guessed successor phase. -/
theorem bankTrialC5CWaitCLoneCountExact {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (heads : Nat) (hq : 3 ≤ q)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL1)
    (hcarry : bankTrialLiveCarryValue B = heads) :
    heads = (compileAdvice q).K := by
  have hnoIR :
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken B j ≠ .IR := by
    intro j
    exact (bankTrialLiveWaveCWaitNoWriters B hc hm j).1
  have hbinary := bankTrialC5CarryBinaryWithoutIR B hnoIR
  have hbits :
      ∀ l : Nat, l < (compileAdvice q).b →
        bankTrialCmpBit B l = (compileAdvice q).theta l := by
    intro l hl
    rw [bankTrialCmpBitEq B l hl]
    exact hc.clAll
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩
      ht ⟨l, hl⟩
  have htheta := (bankTrialCmpBinaryIff B).2 hbits
  calc
    heads = bankTrialLiveCarryValue B := hcarry.symm
    _ = bankTrialLiveBinaryValue B := hbinary
    _ = bankTrialLiveThetaBinary q := htheta
    _ = (compileAdvice q).K :=
      bankTrialProbabilityThetaBinaryEqualsK q hq

/-- The IWAIT/AL branch is an authorized increment return,
without requiring any global HEAD provenance beyond the origin tag. -/
theorem bankTrialC5OutgoingALReturnExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (o : BankTrialC5ActualOrigin n q)
    (hinc : o.increment = true)
    (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (hnext : bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
      .CSTART) :
    bankTrialC5ActualReturned o
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) := by
  have hnotCWait :
      (B.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
    change bankTrialLiveWaveRootMode B ≠ .CWAIT
    rw [hm]
    intro h
    cases h
  have hs := bankTrialLocalUnlatchedNonCWaitNoWin
    ring root root B hf hnotCWait
  have hmodeStep :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .CSTART := by
    rw [← bankTrialLocalNextLiveBank ring root root B begun]
    exact hnext
  have hstep := bankTrialProbabilityLiveCStartNext
    ring root root B begun hs hmodeStep (Or.inl rfl)
  unfold bankTrialC5ActualReturned
  simp only [hinc, ↓reduceIte]
  refine ⟨true, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
    exact hmodeStep

/-- CL0 before the first exit forces the recorded actual-origin
counter below K. This is the old globally proved strictness
invariant instantiated on the original chronological word. -/
theorem bankTrialC5ActualCLZeroBeforeK {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root u o.after)))
    (hcurrent :
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after)))
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre o.after).bank = .CWAIT)
    (htok : bankTrialLiveWaveToken
      (bankTrialLocalRun ring root pre o.after).bank
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL0) :
    o.heads < (compileAdvice q).K := by
  obtain ⟨launch, hlaunch, hcount⟩ :=
    bankTrialC5ActualOriginChronologicalHeadLedger
      ring root S hsp hlarge hwidth hclean
      x e o ho pre hbefore
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    have hn : ¬ q ≤ qStar :=
      of_decide_eq_false (hs.symm.trans hsp)
    change ¬ q ≤ 79 at hn
    omega
  have hK : 0 < (compileAdvice q).K := by
    change 0 < 2 * q + productionKappa q
    omega
  have hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep (launch ++ (e :: pre))
  have hstate :
      bankTrialLocalRun ring root (launch ++ (e :: pre))
        (bankTrialLocalStart S) =
      bankTrialLocalRun ring root pre o.after :=
    (bankTrialC5GoodReturnReachable
      ring root S launch x hlaunch.symm e o ho pre).symm
  rw [hstate, hcount] at hInv
  obtain ⟨⟨begun, hlive⟩, _, _⟩ :=
    bankTrialC5ActualOriginRunLedger
      ring root S hsp hlarge hwidth hclean
      x e o ho pre hbefore hcurrent
  exact bankTrialC5CWaitCLZeroStrict
    (bankTrialLocalRun ring root pre o.after)
    o.heads hwidth hInv begun hlive hmode
    ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩, htok⟩

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- On a CLEAN original-clock word, a zero chronological head count
cannot coexist with a LIVE root outside ARMED. The proof uses the
real incoming-ARMED RESET row, not a synthetic mode machine. -/
theorem bankTrialC5ZeroHeadLiveArmed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) (begun : Bool)
    (hlive : (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .live begun)
    (hzero : bankTrialLiveHeadCount ring root word
      (bankTrialLocalStart S) = 0) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).bank = .ARMED := by
  have hreverse : ∀ rev : List (Fin n), ∀ nb : Bool,
      (bankTrialLocalRun ring root rev.reverse
        (bankTrialLocalStart S)).phase = .live nb →
      bankTrialLiveHeadCount ring root rev.reverse
        (bankTrialLocalStart S) = 0 →
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root rev.reverse
          (bankTrialLocalStart S)).bank = .ARMED := by
    intro rev
    induction rev with
    | nil =>
        intro nb _ _
        change bankTrialLiveWaveRootMode S = .ARMED
        exact hclean.2.1
    | cons f rest ih =>
        intro nextBegun hnext hcount
        have hnextStep :
            (bankTrialLocalNext ring root
              (bankTrialLocalRun ring root rest.reverse
                (bankTrialLocalStart S)) f).phase =
              .live nextBegun := by
          simpa only [List.reverse_cons,
            bankTrialC5StrengthenedSnocRun] using hnext
        have hcountStep :
            bankTrialLiveHeadCount ring root rest.reverse
              (bankTrialLocalStart S) +
              (if BankTrialProbabilityArmedGate
                  (bankTrialLocalRun ring root rest.reverse
                    (bankTrialLocalStart S)) ∧ f = root
                then 1 else 0) = 0 := by
          simpa only [List.reverse_cons,
            bankTrialC5StrengthenedSnocHeads] using hcount
        have hcountOld :
            bankTrialLiveHeadCount ring root rest.reverse
              (bankTrialLocalStart S) = 0 := by
          omega
        obtain ⟨oldBegun, holdLive⟩ :=
          bankTrialC5StrengthenedOldLive ring root f
            (bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S)) nextBegun hnextStep
        have holdArmed := ih oldBegun holdLive hcountOld
        have hgate : BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S)) :=
          ⟨⟨oldBegun, holdLive⟩, holdArmed⟩
        have hne : f ≠ root := by
          intro he
          rw [if_pos ⟨hgate, he⟩] at hcountStep
          omega
        have hcanon :
            bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S) =
              (⟨(bankTrialLocalRun ring root rest.reverse
                (bankTrialLocalStart S)).bank,
                .live oldBegun⟩ : BankTrialLocalState q) :=
          bankTrialCmpStateEta _ oldBegun holdLive
        have hf :
            (bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S)).bank.success = false :=
          bankTrialProbabilityCleanLiveUnlatched
            ring root S hclean rest.reverse
            (bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S)).bank oldBegun hcanon
        have hnextArmed :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (bankTrialLocalRun ring root rest.reverse
                  (bankTrialLocalStart S)) f).bank = .ARMED := by
          by_cases hin : ring.rightNeighbor f = root
          · have hreset :=
              bankTrialProbabilityIncomingArmedRootReset
                ring root f
                (bankTrialLocalRun ring root rest.reverse
                  (bankTrialLocalStart S)).bank
                hf holdArmed hne hin
            have hresetNext :
                bankTrialLiveWaveRootMode
                  (bankTrialLocalNext ring root
                    (bankTrialLocalRun ring root rest.reverse
                      (bankTrialLocalStart S)) f).bank = .RESET := by
              rw [hcanon, bankTrialLocalNextLiveBank]
              exact hreset
            have hlocked := bankTrialWindowLockedCleanWords
              ring root hw S hclean (rest.reverse ++ [f])
            have hnotReset :
                bankTrialLiveWaveRootMode
                  (bankTrialLocalNext ring root
                    (bankTrialLocalRun ring root rest.reverse
                      (bankTrialLocalStart S)) f).bank ≠ .RESET := by
              have hnextFull :
                  (bankTrialLocalRun ring root (rest.reverse ++ [f])
                    (bankTrialLocalStart S)).phase =
                    .live nextBegun := by
                simpa only [List.reverse_cons] using hnext
              have hn := hlocked.2 nextBegun hnextFull
              rw [bankTrialC5StrengthenedSnocRun] at hn
              exact hn
            exact False.elim (hnotReset hresetNext)
          · have hframe := bankTrialLocalRootNonincidentFrame
              ring root f
              (bankTrialLocalRun ring root rest.reverse
                (bankTrialLocalStart S)).bank hf hne hin
            rw [hcanon, bankTrialLocalNextLiveBank]
            change
              ((GrantBankReference.bankLocalReferenceStepClamped
                ring root
                (bankTrialLocalRun ring root rest.reverse
                  (bankTrialLocalStart S)).bank f).fields
                  ⟨0, by omega⟩).1 = .ARMED
            rw [hframe]
            exact holdArmed
        rw [List.reverse_cons, bankTrialC5StrengthenedSnocRun]
        exact hnextArmed
  have h := hreverse word.reverse begun
  simpa only [List.reverse_reverse] using
    h (by simpa only [List.reverse_reverse] using hlive)
      (by simpa only [List.reverse_reverse] using hzero)

/-- Every CLEAN-reachable LIVE CSTART state has seen an actual
ARMED outgoing decision: its chronological HEAD count is positive. -/
theorem bankTrialC5CStartHasPositiveHeads {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) (begun : Bool)
    (hlive : (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).bank = .CSTART) :
    0 < bankTrialLiveHeadCount ring root word
      (bankTrialLocalStart S) := by
  by_cases hz : bankTrialLiveHeadCount ring root word
      (bankTrialLocalStart S) = 0
  · have ha := bankTrialC5ZeroHeadLiveArmed
      ring root S hw hclean word begun hlive hz
    rw [hmode] at ha
    cases ha
  · omega

/-- Comparator origins (CSTART-to-CWAIT) record at least one
chronological head, even when their launching CSTART was reached
by an arbitrary, rather than designated, physical word. -/
theorem bankTrialC5ActualComparatorOriginPositive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (hinc : o.increment = false) :
    0 < o.heads := by
  obtain ⟨hclean, ⟨launch, hlaunch⟩, _,
    ⟨begun, _, hlive, _⟩, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have hcstart : bankTrialLiveWaveRootMode x.bank = .CSTART := by
    rcases hmodes with hi | hc
    · have htag := bankTrialC5ActualIncrementTagExact
        ring root S x e o ho
      rw [hi.1] at htag
      have htrue : o.increment = true := by
        simpa using htag
      rw [hinc] at htrue
      cases htrue
    · exact hc.1
  have hPrevLive :
      (bankTrialLocalRun ring root launch
        (bankTrialLocalStart S)).phase = .live begun := by
    rw [hlaunch]
    exact hlive
  have hPrevMode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root launch
          (bankTrialLocalStart S)).bank = .CSTART := by
    rw [hlaunch]
    exact hcstart
  have hpositive := bankTrialC5CStartHasPositiveHeads
    ring root S (bankTrialProbabilityUpperWindow hlarge)
    hclean launch begun hPrevLive hPrevMode
  have hcount := bankTrialC5ActualOriginHeadCountExact
    ring root S hsp hlarge hwidth hclean
    launch x hlaunch.symm e o ho
  rw [bankTrialC5StrengthenedSnocHeads] at hcount
  omega

/-- A genuine origin suffix is a CLEAN-reachable physical word.
The full locked certificate, not just its root-mode restriction,
therefore remains available at any pre-exit or post-exit prefix. -/
theorem bankTrialC5ActualPrefixLocked {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n)) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root pre o.after) := by
  obtain ⟨_, ⟨launch, hlaunch⟩, _, _, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  rw [bankTrialC5GoodReturnReachable
    ring root S launch x hlaunch.symm e o ho pre]
  exact bankTrialWindowLockedCleanWords
    ring root hw S hclean (launch ++ (e :: pre))

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A genuine physical CWAIT/CL0 outgoing service with positive
carry returns a LIVE ARMED certificate at exactly that carry.
The proof checks the first-token consumption, frames all other
tokens and bits, and excludes the zero-valued CLEAN/lost branch. -/
theorem bankTrialC5OutgoingCLZeroArmedOfPositive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hf : B.success = false)
    (hlock : BankTrialLiveNoResetLocked
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL0)
    (hpos : 0 < bankTrialLiveCarryValue B) :
    BankTrialC5ArmedAt q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root)
      (bankTrialLiveCarryValue B) := by
  have hc : BankTrialLiveWaveCertificate q B :=
    hlock.1 begun rfl
  have hfirstNE :
      bankTrialLiveWaveToken B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ ≠ .E := by
    rw [ht]
    intro he
    cases he
  have htail :
      ∀ j : Fin (compileAdvice q).b, j.val ≠ 0 →
        bankTrialLiveWaveToken B j = .E := by
    intro j hj
    by_cases he : bankTrialLiveWaveToken B j = .E
    · exact he
    · have heq := hc.uniqueWorker
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩
        j hfirstNE he
      have hv := congrArg Fin.val heq
      exact False.elim (hj hv.symm)
  have hraw := bankTrialCmpRawCLZeroRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
    (by have hb := bankTrialCmpWidth q; omega)
    rfl rfl rfl hm ht
  have hproj := bankTrialCmpRoot ring root hw B hf
  have hmodeStep :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .ARMED :=
    hproj.1.trans hraw.1
  have htokStep :
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) j = .E := by
    intro j
    by_cases hj : j.val = 0
    · exact ((hproj.2 j).1 hj).2.trans hraw.2.1
    · exact ((hproj.2 j).2 hj).2.trans (htail j hj)
  have hbits := bankTrialC5CWaitRootWholeBitFrame
    ring root hw B hf hm
  have hOldNoIR := bankTrialC5CWaitNoIR B hc hm
  have hBinary :
      bankTrialLiveBinaryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) =
      bankTrialLiveCarryValue B := by
    calc
      bankTrialLiveBinaryValue
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) =
        bankTrialLiveBinaryValue B :=
          bankTrialCmpBinaryCongr _ _ hbits
      _ = bankTrialLiveCarryValue B :=
        (bankTrialC5CarryBinaryWithoutIR B hOldNoIR).symm
  have hCarryStep :
      bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) =
      bankTrialLiveCarryValue B := by
    exact (bankTrialC5NoWorkerCarryBinary
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) htokStep).trans hBinary
  have hsupport : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hevent :
      GrantBankReference.bankLocalReferenceSuccessEvent
        ring root B root = false := by
    unfold GrantBankReference.bankLocalReferenceSuccessEvent
    rw [if_pos rfl]
    change bankSuccess
      (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      1 (compileAdvice q).b = false
    simp [bankSuccess, GrantBankReference.bankLocalReferenceCell,
      ht]
    intro _ h
    have h2 : bankTrialLiveWaveToken B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL1 := h
    rw [ht] at h2
    cases h2
  have hsuccess :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).success = false := by
    simp [GrantBankReference.bankLocalReferenceStepClamped,
      hsupport, hf, hevent]
  have hnotClean :
      ¬ BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) := by
    intro hclean
    have hzero := bankTrialLiveBinaryClean _ hclean
    rw [hBinary] at hzero
    omega
  have hnotReset :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) ≠ .RESET := by
    rw [hmodeStep]
    intro he
    cases he
  obtain ⟨nextBegun, hnext⟩ :=
    bankTrialCmpLiveNext ring root root B begun
      hsuccess hnotClean hnotReset
  have hlockedNext : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) := by
    change BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root [root]
        (⟨B, .live begun⟩ : BankTrialLocalState q))
    exact bankTrialC5LockedArbitraryWord
      ring root hw [root]
      (⟨B, .live begun⟩ : BankTrialLocalState q) hlock
  refine ⟨nextBegun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext]
  · rw [hnext]
    exact hmodeStep
  · intro j
    rw [hnext]
    exact htokStep j
  · rw [hnext]
    exact hBinary
  · rw [hnext]
    exact hsuccess
  · exact hlockedNext

/-- Authenticated comparator CL0 return on a strict first-exit
prefix. The post-state carries precisely the *origin's* HEAD count. -/
theorem bankTrialC5ActualCLZeroArmedAtOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root u o.after)))
    (hcurrent :
      ¬ (bankTrialC5ActualReturned o
           (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
           (bankTrialLocalRun ring root pre o.after)))
    (hinc : o.increment = false)
    (hm : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre o.after).bank = .CWAIT)
    (ht : bankTrialLiveWaveToken
      (bankTrialLocalRun ring root pre o.after).bank
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL0) :
    BankTrialC5ArmedAt q
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre o.after) root) o.heads := by
  have hclean := (bankTrialC5ActualStartGuardFacts
    ring root S x e o ho).1
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  obtain ⟨⟨begun, hlive⟩, _, hcarry⟩ :=
    bankTrialC5ActualOriginRunLedger
      ring root S hsp hlarge hwidth hclean
      x e o ho pre hbefore hcurrent
  have hpos := bankTrialC5ActualComparatorOriginPositive
    ring root S hsp hlarge hwidth x e o ho hinc
  have hf := bankTrialC5ActualPrefixLiveUnlatched
    ring root S hclean x e o ho pre begun hlive
  have hcanonical :
      bankTrialLocalRun ring root pre o.after =
      (⟨(bankTrialLocalRun ring root pre o.after).bank,
        .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta _ begun hlive
  have hlocked := bankTrialC5ActualPrefixLocked
    ring root S hw hclean x e o ho pre
  rw [hcanonical] at hlocked
  have hcarryPos :
      0 < bankTrialLiveCarryValue
        (bankTrialLocalRun ring root pre o.after).bank := by
    rw [hcarry]
    exact hpos
  have harm := bankTrialC5OutgoingCLZeroArmedOfPositive
    ring root hw
    (bankTrialLocalRun ring root pre o.after).bank begun
    hf hlocked hm ht hcarryPos
  rw [hcarry] at harm
  rw [hcanonical]
  exact harm

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- On an unlatched outgoing-root service, success can be set
only by the old CWAIT/CL1 acceptance guard. -/
theorem bankTrialC5OutgoingWithoutCLoneUnlatched {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hno : ¬ (bankTrialLiveWaveRootMode B = .CWAIT ∧
      bankTrialLiveWaveToken B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL1)) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).success = false := by
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hevent :
      GrantBankReference.bankLocalReferenceSuccessEvent
        ring root B root = false := by
    unfold GrantBankReference.bankLocalReferenceSuccessEvent
    rw [if_pos rfl]
    change bankSuccess
      (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      1 (compileAdvice q).b = false
    by_cases hm : bankTrialLiveWaveRootMode B = .CWAIT
    · have ht : bankTrialLiveWaveToken B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ ≠ .CL1 := by
        intro h
        exact hno ⟨hm, h⟩
      simp [bankSuccess, GrantBankReference.bankLocalReferenceCell,
        hm, ht]
      exact fun _ h => ht h
    · simp [bankSuccess, GrantBankReference.bankLocalReferenceCell,
        hm]
      exact fun h _ => hm h
  simp [GrantBankReference.bankLocalReferenceStepClamped,
    hs, hf, hevent]

/-- The repaired outgoing-root first-exit row. Returns AL and CL0
are authenticated against the original origin. CL1 is WON at the
original K count. The remaining bad non-return case is watchdog
expiration. -/
theorem bankTrialC5ActualOutgoingBadFinishRowHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    BankTrialC5ActualOutgoingBadFinishRow ring root S := by
  intro hsp hlarge hwidth x e o ho pre hbefore hcurrent hbad hnot
  have hclean := (bankTrialC5ActualStartGuardFacts
    ring root S x e o ho).1
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  obtain ⟨⟨begun, hlive⟩, hmode, hcarry⟩ :=
    bankTrialC5ActualOriginRunLedger
      ring root S hsp hlarge hwidth hclean
      x e o ho pre hbefore hcurrent
  have hf := bankTrialC5ActualPrefixLiveUnlatched
    ring root S hclean x e o ho pre begun hlive
  have hcanonical :
      bankTrialLocalRun ring root pre o.after =
      (⟨(bankTrialLocalRun ring root pre o.after).bank,
        .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta _ begun hlive
  have hbadCanonical :
      bankTrialC5ActualBadExit o
        (bankTrialLocalNext ring root
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) root) := by
    rw [← hcanonical]
    exact hbad
  have hnotCanonical :
      ¬ bankTrialC5ActualReturned o
        (bankTrialLocalNext ring root
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) root) := by
    rw [← hcanonical]
    exact hnot
  have hwait :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre o.after).bank = .IWAIT ∨
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre o.after).bank = .CWAIT := by
    cases hi : o.increment with
    | true =>
        exact Or.inl (by
          simpa only [hi, ↓reduceIte] using hmode)
    | false =>
        exact Or.inr (by
          simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hmode)
  have hlocked := bankTrialC5ActualPrefixLocked
    ring root S hw hclean x e o ho pre
  rw [hcanonical] at hlocked
  have hcert : BankTrialLiveWaveCertificate q
      (bankTrialLocalRun ring root pre o.after).bank :=
    hlocked.1 begun rfl
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    have hn : ¬ q ≤ qStar :=
      of_decide_eq_false (hs.symm.trans hsp)
    change ¬ q ≤ 79 at hn
    omega
  have hnoCLone :
      ¬ (bankTrialLiveWaveRootMode
           (bankTrialLocalRun ring root pre o.after).bank = .CWAIT ∧
         bankTrialLiveWaveToken
           (bankTrialLocalRun ring root pre o.after).bank
           ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ = .CL1) := by
    intro h
    have hinc : o.increment = false := by
      cases hi : o.increment with
      | false => rfl
      | true =>
          have hiwait : bankTrialLiveWaveRootMode
              (bankTrialLocalRun ring root pre o.after).bank =
              .IWAIT := by
            simpa only [hi, ↓reduceIte] using hmode
          rw [h.1] at hiwait
          cases hiwait
    have hK := bankTrialC5CWaitCLoneCountExact
      (bankTrialLocalRun ring root pre o.after).bank
      o.heads hq hcert h.1 h.2 hcarry
    have hwon := bankTrialProbabilityLiveReturnWon
      ring root
      (bankTrialLocalRun ring root pre o.after).bank
      begun hf h.1 h.2
    have hreturned : bankTrialC5ActualReturned o
        (bankTrialLocalNext ring root
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) root) := by
      unfold bankTrialC5ActualReturned
      simp only [hinc, Bool.false_eq_true, ↓reduceIte]
      exact Or.inr ⟨hK, hwon⟩
    exact hnotCanonical hreturned
  have hsuccess := bankTrialC5OutgoingWithoutCLoneUnlatched
    ring root (bankTrialLocalRun ring root pre o.after).bank
    hf hnoCLone
  have hnotWon :
      (bankTrialLocalNext ring root
        (⟨(bankTrialLocalRun ring root pre o.after).bank,
          .live begun⟩ : BankTrialLocalState q) root).phase ≠ .won := by
    intro hwon
    have hguard := bankTrialProbabilityLiveWonRequiresOldGuard
      ring root root
      (bankTrialLocalRun ring root pre o.after).bank
      begun hf hwon
    exact hnoCLone ⟨hguard.2.1, hguard.2.2⟩
  have hcases := bankTrialC5OutgoingWaitPhysicalCases
    ring root hw (bankTrialLocalRun ring root pre o.after).bank
      begun hf hwait
  have hresult :
      ((bankTrialLocalRun ring root pre o.after).bank.fields
        ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) root).bank = .RESET ∧
      (bankTrialLocalNext ring root
        (⟨(bankTrialLocalRun ring root pre o.after).bank,
          .live begun⟩ : BankTrialLocalState q) root).phase ≠ .won := by
    rcases hcases with hstay | htimeout | hal | hclzero | hclone
    · have hstepMode :
          bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root
              (bankTrialLocalRun ring root pre o.after).bank root) =
          bankTrialLiveWaveRootMode
            (bankTrialLocalRun ring root pre o.after).bank := by
        rw [← bankTrialLocalNextLiveBank ring root root
          (bankTrialLocalRun ring root pre o.after).bank begun]
        exact hstay.1
      have hnotClean :
          ¬ BankTrialLocalClean q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root
              (bankTrialLocalRun ring root pre o.after).bank root) := by
        intro hc
        have har : bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root
              (bankTrialLocalRun ring root pre o.after).bank root) =
            .ARMED := hc.2.1
        rw [hstepMode] at har
        rcases hwait with hi | hcwait
        · rw [hi] at har
          cases har
        · rw [hcwait] at har
          cases har
      have hnotReset :
          bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root
              (bankTrialLocalRun ring root pre o.after).bank root) ≠
              .RESET := by
        intro hr
        rw [hstepMode] at hr
        rcases hwait with hi | hcwait
        · rw [hi] at hr
          cases hr
        · rw [hcwait] at hr
          cases hr
      obtain ⟨nextBegun, hnext⟩ :=
        bankTrialCmpLiveNext ring root root
          (bankTrialLocalRun ring root pre o.after).bank begun
          hsuccess hnotClean hnotReset
      have ha : bankTrialC5ActualWorkerActive o
          (bankTrialLocalNext ring root
            (⟨(bankTrialLocalRun ring root pre o.after).bank,
              .live begun⟩ : BankTrialLocalState q) root) := by
        refine ⟨⟨nextBegun, ?_⟩, ?_⟩
        · rw [hnext]
        · rw [hnext]
          exact hstepMode.trans hmode
      exact False.elim
        ((bankTrialC5ActualActiveNotBadExit o _ ha)
          hbadCanonical)
    · exact ⟨htimeout.2, htimeout.1, hnotWon⟩
    · have hinc : o.increment = true := by
        cases hi : o.increment with
        | true => rfl
        | false =>
            have hcwait : bankTrialLiveWaveRootMode
                (bankTrialLocalRun ring root pre o.after).bank =
                .CWAIT := by
              simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hmode
            rw [hal.1] at hcwait
            cases hcwait
      have hret := bankTrialC5OutgoingALReturnExact
        ring root (bankTrialLocalRun ring root pre o.after).bank
        begun o hinc hf hal.1 hal.2.2
      exact False.elim (hnotCanonical hret)
    · have hinc : o.increment = false := by
        cases hi : o.increment with
        | false => rfl
        | true =>
            have hiwait : bankTrialLiveWaveRootMode
                (bankTrialLocalRun ring root pre o.after).bank =
                .IWAIT := by
              simpa only [hi, ↓reduceIte] using hmode
            rw [hclzero.1] at hiwait
            cases hiwait
      have harmed := bankTrialC5ActualCLZeroArmedAtOrigin
        ring root S hsp hlarge hwidth
        x e o ho pre hbefore hcurrent hinc
        hclzero.1 hclzero.2.1
      have hbelow := bankTrialC5ActualCLZeroBeforeK
        ring root S hsp hlarge hwidth hclean
        x e o ho pre hbefore hcurrent
        hclzero.1 hclzero.2.1
      have hreturn : bankTrialC5ActualReturned o
          (bankTrialLocalNext ring root
            (bankTrialLocalRun ring root pre o.after) root) := by
        unfold bankTrialC5ActualReturned
        simp only [hinc, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨hbelow, harmed⟩
      have hreturnCanon : bankTrialC5ActualReturned o
          (bankTrialLocalNext ring root
            (⟨(bankTrialLocalRun ring root pre o.after).bank,
              .live begun⟩ : BankTrialLocalState q) root) := by
        rw [← hcanonical]
        exact hreturn
      exact False.elim (hnotCanonical hreturnCanon)
    · exact False.elim (hnoCLone ⟨hclone.1, hclone.2.1⟩)
  rw [hcanonical]
  exact hresult

/-- Exact nonreturnBad field of the repaired actual-worker kernel,
now obtained directly from the proved physical outgoing-owner row. -/
theorem bankTrialC5ActualNonreturnBadHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      ∀ u v : List (Fin n),
        (∀ pre tail : List (Fin n), ∀ f : Fin n,
          u = pre ++ (f :: tail) →
          ¬ (bankTrialC5ActualReturned o
               (bankTrialLocalRun ring root pre o.after) ∨
             bankTrialC5ActualBadExit o
               (bankTrialLocalRun ring root pre o.after))) →
        (bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root u o.after) ∨
          bankTrialC5ActualBadExit o
            (bankTrialLocalRun ring root u o.after)) →
        ¬ bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root u o.after) →
        bankTrialC5ActualTimeout ring root o (u ++ v) = true := by
  exact bankTrialC5ActualNonreturnBadOfOutgoing
    ring root S hsp hlarge hwidth
    (bankTrialProbabilityUpperWindow hlarge) hclean
    (bankTrialC5ActualOutgoingBadFinishRowHolds ring root S)

end L3

/- No structure replacement. -/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The sole outgoing ARMED-to-IWAIT raw transition issues IR
at digit one. This is a two-cell theorem, independent of words. -/
theorem bankTrialC5RawArmedToIWaitFirstIR
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (ht : y.tok = .E)
    (hnew : (bankPair x y 1 b theta).1.mode = .IWAIT) :
    (bankPair x y 1 b theta).2.tok = .IR := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hbit : y.bit with
  | false =>
      have hc :
          (bankPair x y 1 b theta).1.mode = .CSTART := by
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind]
      rw [hc] at hnew
      cases hnew
  | true =>
      simp [bankPair, hx, hy, hg, hm, ht, hbit,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind]

theorem bankTrialC5CoverageLaunchPhases {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hmodes :
      (bankTrialLiveWaveRootMode z.bank = .ARMED ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
      (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root z e).bank = .CWAIT)) :
    ∃ begun nextBegun : Bool,
      z.phase = .live begun ∧
      (bankTrialLocalNext ring root z e).phase = .live nextBegun := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    have hb := bankTrialCmpWidth q
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hsafeSeed : BankTrialLocalObserverSafe
      (bankTrialLocalStart S) := by
    refine ⟨bankTrialLocalCleanLeaseCap S hclean, ?_⟩
    intro hr
    cases hr
  have hsafe : BankTrialLocalObserverSafe z := by
    rw [hz]
    exact bankTrialLocalObserverSafeRun ring root
      (bankTrialLocalRecoveryCertStepPremise ring root hn)
      pre (bankTrialLocalStart S) hsafeSeed
  cases hp : z.phase with
  | live begun =>
      have hzeta :
          z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
        bankTrialCmpStateEta z begun hp
      have hactual :
          bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
            (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
        hz.symm.trans hzeta
      have hf : z.bank.success = false :=
        bankTrialProbabilityCleanLiveUnlatched
          ring root S hclean pre z.bank begun hactual
      have hnotCWait : bankTrialLiveWaveRootMode z.bank ≠
          .CWAIT := by
        intro h
        rcases hmodes with ha | hc
        · rw [ha.1] at h
          cases h
        · rw [hc.1] at h
          cases h
      have hs := bankTrialLocalUnlatchedNonCWaitNoWin
        ring root e z.bank hf hnotCWait
      have hb :
          (bankTrialLocalNext ring root z e).bank =
            GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank e := by
        rw [hzeta]
        exact bankTrialLocalNextLiveBank ring root e z.bank begun
      have hstepMode :
          bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank e) = .IWAIT ∨
          bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank e) = .CWAIT := by
        rcases hmodes with ha | hc
        · apply Or.inl
          rw [← hb]
          exact ha.2
        · apply Or.inr
          rw [← hb]
          exact hc.2
      have hnotClean : ¬ BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e) := by
        intro hc
        have harm :
            bankTrialLiveWaveRootMode
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root z.bank e) = .ARMED := hc.2.1
        rcases hstepMode with hi | hcwait
        · rw [hi] at harm
          cases harm
        · rw [hcwait] at harm
          cases harm
      have hnotReset :
          bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank e) ≠ .RESET := by
        intro hr
        rcases hstepMode with hi | hcwait
        · rw [hi] at hr
          cases hr
        · rw [hcwait] at hr
          cases hr
      obtain ⟨nextBegun, hnext⟩ := bankTrialCmpLiveNext
        ring root e z.bank begun hs hnotClean hnotReset
      refine ⟨begun, nextBegun, ?_, ?_⟩
      · rfl
      · rw [hzeta, hnext]
  | recovery =>
      have hcert : BankTrialLocalRecoveryCert q z.bank :=
        hsafe.2 hp
      have hroot :
          bankTrialLiveWaveRootMode z.bank = .RESET ∨
          bankTrialLiveWaveRootMode z.bank = .RWAIT := by
        rcases hcert.2.2 with hreset | hwait
        · exact Or.inl hreset
        · exact Or.inr hwait.1
      rcases hroot with hreset | hwait
      · rcases hmodes with ha | hc
        · rw [ha.1] at hreset
          cases hreset
        · rw [hc.1] at hreset
          cases hreset
      · rcases hmodes with ha | hc
        · rw [ha.1] at hwait
          cases hwait
        · rw [hc.1] at hwait
          cases hwait
  | won =>
      have hterm : bankTrialLocalTerminal z := Or.inl hp
      have hfixed := bankTrialLocalTerminalAbsorbs ring root e z hterm
      rcases hmodes with ha | hc
      · rw [hfixed, ha.1] at ha
        cases ha.2
      · rw [hfixed, hc.1] at hc
        cases hc.2
  | lost =>
      have hterm : bankTrialLocalTerminal z := Or.inr hp
      have hfixed := bankTrialLocalTerminalAbsorbs ring root e z hterm
      rcases hmodes with ha | hc
      · rw [hfixed, ha.1] at ha
        cases ha.2
      · rw [hfixed, hc.1] at hc
        cases hc.2

/-- Every emitted launch has the specified first-digit token
transition. The old token-clear fact comes from the CLEAN lock;
the new nonempty token comes from the literal outgoing bankPair. -/
theorem bankTrialC5ActualLaunchTokenFacts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S z e) :
    bankTrialLiveWaveToken z.bank
      ⟨0, bankTrialWindowWidthPos q⟩ = .E ∧
    bankTrialLiveWaveToken
      (bankTrialLocalNext ring root z e).bank
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
  obtain ⟨_, _, he, ⟨begun, _, hlive, _⟩, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S z e o ho
  subst e
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hcanon :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  have hactual :
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    hz.symm.trans hcanon
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean pre z.bank begun hactual
  have hlocked : BankTrialLiveNoResetLocked z := by
    rw [hz]
    exact bankTrialWindowLockedCleanWords ring root hw S hclean pre
  have hcert : BankTrialLiveWaveCertificate q z.bank :=
    hlocked.1 begun hlive
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hcanon]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  have hprojection := bankTrialCmpRoot ring root hw z.bank hf
  have hfirst := (hprojection.2
    ⟨0, bankTrialWindowWidthPos q⟩).1 rfl
  rcases hmodes with ha | hc
  · have htokOld := hcert.headClear
      ⟨0, bankTrialWindowWidthPos q⟩ (Or.inl ha.1)
    have hrawMode :
        (GrantBankReference.bankLocalReferenceInternalPair q z.bank
          ⟨0, bankTrialWindowWidthPos q⟩).1.mode = .IWAIT :=
      hprojection.1.symm.trans (by rw [← hbank]; exact ha.2)
    have hraw := bankTrialC5RawArmedToIWaitFirstIR
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      (by have hb := bankTrialCmpWidth q; omega)
      rfl rfl rfl ha.1 htokOld hrawMode
    have hnew :
        bankTrialLiveWaveToken
          (bankTrialLocalNext ring root z root).bank
          ⟨0, bankTrialWindowWidthPos q⟩ = .IR := by
      rw [hbank]
      exact hfirst.2.trans hraw
    refine ⟨htokOld, ?_⟩
    rw [hnew]
    intro h
    cases h
  · have htokOld := hcert.headClear
      ⟨0, bankTrialWindowWidthPos q⟩ (Or.inr hc.1)
    have hraw := bankTrialCmpRawLaunch
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      (by have hb := bankTrialCmpWidth q; omega)
      rfl rfl rfl hc.1 htokOld
    have hnew :
        bankTrialLiveWaveToken
          (bankTrialLocalNext ring root z root).bank
          ⟨0, bankTrialWindowWidthPos q⟩ =
        (if (GrantBankReference.bankLocalReferenceCell z.bank
             ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).bit ==
               (compileAdvice q).theta 0
         then .CR1 else .CR0) := by
      rw [hbank]
      exact hfirst.2.trans hraw.2.1
    refine ⟨htokOld, ?_⟩
    rw [hnew]
    split <;> intro h <;> cases h

/-- Kernel.coverage for actual origin records and the original
chronological scheduler. This includes both directions and the
one-origin-per-edge bound. -/
theorem bankTrialC5ActualCoverageHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    ∀ (hclean : BankTrialLocalClean q S)
      (pre : List (Fin n)) (z : BankTrialLocalState q),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      ∀ e : Fin n,
        ((e = root ∧
          ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
           (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .CWAIT)) ∧
          bankTrialLiveWaveToken z.bank
            ⟨0, bankTrialWindowWidthPos q⟩ = .E ∧
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z e).bank
            ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E) →
         ∃ o : BankTrialC5ActualOrigin n q,
           o ∈ bankTrialC5ActualStarts ring root S z e ∧
           o.after = bankTrialLocalNext ring root z e ∧
           o.increment =
             decide (bankTrialLiveWaveRootMode z.bank = .ARMED) ∧
           o.heads =
             bankTrialLiveHeadCount ring root (pre ++ [e])
               (bankTrialLocalStart S)) ∧
        (∀ o : BankTrialC5ActualOrigin n q,
          o ∈ bankTrialC5ActualStarts ring root S z e →
          e = root ∧
          ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
           (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .CWAIT)) ∧
          bankTrialLiveWaveToken z.bank
            ⟨0, bankTrialWindowWidthPos q⟩ = .E ∧
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z e).bank
            ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E ∧
          o.after = bankTrialLocalNext ring root z e ∧
          o.increment =
            decide (bankTrialLiveWaveRootMode z.bank = .ARMED) ∧
          o.heads =
            bankTrialLiveHeadCount ring root (pre ++ [e])
              (bankTrialLocalStart S)) ∧
        (bankTrialC5ActualStarts ring root S z e).length ≤ 1 := by
  intro hclean pre z hz e
  refine ⟨?_, ?_, bankTrialC5ActualStartsLength ring root S z e⟩
  · intro hcriterion
    obtain ⟨he, hmodes, _, _⟩ := hcriterion
    have hphases := bankTrialC5CoverageLaunchPhases
      ring root e S hlarge hclean pre z hz hmodes
    have hguard :
        BankTrialLocalClean q S ∧
        (∃ w : List (Fin n),
          bankTrialLocalRun ring root w
            (bankTrialLocalStart S) = z) ∧
        e = root ∧
        (∃ begun nextBegun : Bool,
          z.phase = .live begun ∧
          (bankTrialLocalNext ring root z e).phase = .live nextBegun) ∧
        ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
          (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z e).bank = .CWAIT)) :=
      ⟨hclean, ⟨pre, hz.symm⟩, he, hphases, hmodes⟩
    have hstarts :
        bankTrialC5ActualStarts ring root S z e =
        [{ before := z, edge := e,
           after := bankTrialLocalNext ring root z e,
           increment :=
             (bankTrialLiveWaveRootMode
                (bankTrialLocalNext ring root z e).bank == .IWAIT),
           heads := bankTrialLiveCarryValue
             (bankTrialLocalNext ring root z e).bank }] := by
      unfold bankTrialC5ActualStarts
      rw [if_pos hguard]
    have hmem :
        (BankTrialC5ActualOrigin.mk z e
           (bankTrialLocalNext ring root z e)
           (bankTrialLiveWaveRootMode
             (bankTrialLocalNext ring root z e).bank == .IWAIT)
           (bankTrialLiveCarryValue
             (bankTrialLocalNext ring root z e).bank)) ∈
          bankTrialC5ActualStarts ring root S z e := by
      rw [hstarts]
      simp
    refine ⟨_, hmem, rfl, ?_, ?_⟩
    · exact bankTrialC5ActualIncrementTagExact
        ring root S z e _ hmem
    · exact bankTrialC5ActualOriginHeadCountExact
        ring root S hsp hlarge hwidth hclean
        pre z hz e _ hmem
  · intro o ho
    obtain ⟨_, _, he, _, hmodes⟩ :=
      bankTrialC5ActualStartGuardFacts ring root S z e o ho
    obtain ⟨htokOld, htokNew⟩ :=
      bankTrialC5ActualLaunchTokenFacts
        ring root S hlarge hclean pre z hz e o ho
    have hpost := bankTrialC5ActualStartPost
      ring root S z e o ho
    have hinc := bankTrialC5ActualIncrementTagExact
      ring root S z e o ho
    have hheads := bankTrialC5ActualOriginHeadCountExact
      ring root S hsp hlarge hwidth hclean
      pre z hz e o ho
    exact ⟨he, hmodes, htokOld, htokNew,
      hpost, hinc, hheads⟩

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- All chronological CLEAN-run words, including terminal words,
have at most K paid ARMED outgoing heads. The successor need not be
LIVE: an old ARMED head is already strictly below K. -/
theorem bankTrialC5ActualAllWordsHeadCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) :
    bankTrialLiveHeadCount ring root word
      (bankTrialLocalStart S) ≤ (compileAdvice q).K := by
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    have hn : ¬ q ≤ qStar :=
      of_decide_eq_false (hs.symm.trans hsp)
    change ¬ q ≤ 79 at hn
    omega
  have hK : 0 < (compileAdvice q).K := by
    change 0 < 2 * q + productionKappa q
    omega
  have hstep : BankTrialC5CompletedHeadEdgePreservation ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hreverse : ∀ rev : List (Fin n),
      bankTrialLiveHeadCount ring root rev.reverse
        (bankTrialLocalStart S) ≤ (compileAdvice q).K := by
    intro rev
    induction rev with
    | nil =>
        change 0 ≤ (compileAdvice q).K
        omega
    | cons e rest ih =>
        rw [List.reverse_cons, bankTrialC5StrengthenedSnocHeads]
        have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
          ring root S hlarge hwidth hclean
          (bankTrialC5CompletedHeadInvariantStart S hK hclean)
          hstep rest.reverse
        by_cases hg : BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S))
        · by_cases he : e = root
          · have hstrict :=
              hInv.armedStrict hg.1.choose
                hg.1.choose_spec hg.2
            rw [if_pos ⟨hg, he⟩]
            omega
          · have hnot :
                ¬ (BankTrialProbabilityArmedGate
                    (bankTrialLocalRun ring root rest.reverse
                      (bankTrialLocalStart S)) ∧ e = root) := by
              intro h
              exact he h.2
            rw [if_neg hnot, Nat.add_zero]
            exact ih
        · have hnot :
              ¬ (BankTrialProbabilityArmedGate
                  (bankTrialLocalRun ring root rest.reverse
                    (bankTrialLocalStart S)) ∧ e = root) := by
            intro h
            exact hg h.1
          rw [if_neg hnot, Nat.add_zero]
          exact ih
  have h := hreverse word.reverse
  simpa only [List.reverse_reverse] using h

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every materialized actual origin records a paid-head index at
most K, even when the full scheduler word later becomes terminal. -/
theorem bankTrialC5ActualOriginRecordedHeadBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    o.heads ≤ (compileAdvice q).K := by
  rw [bankTrialC5ActualOriginHeadCountExact
    ring root S hsp hlarge hwidth hclean pre x hx e o ho]
  exact bankTrialC5ActualAllWordsHeadCap
    ring root S hsp hlarge hwidth hclean (pre ++ [e])

theorem bankTrialC5ActualOriginLaunchHeadIndex {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    (o.increment = true ∧
      o.heads =
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) + 1) ∨
    (o.increment = false ∧
      o.heads =
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S)) := by
  obtain ⟨_, _, he, ⟨begun, _, hlive, _⟩, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have htag := bankTrialC5ActualIncrementTagExact
    ring root S x e o ho
  have hcount := bankTrialC5ActualOriginHeadCountExact
    ring root S hsp hlarge hwidth hclean pre x hx e o ho
  have hsnoc :
      o.heads =
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) +
        (if BankTrialProbabilityArmedGate x ∧ e = root
         then 1 else 0) := by
    rw [bankTrialC5StrengthenedSnocHeads] at hcount
    rw [← hx] at hcount
    exact hcount
  rcases hmodes with ha | hc
  · have hinc : o.increment = true := by
      rw [htag, ha.1]
      rfl
    have hgate : BankTrialProbabilityArmedGate x :=
      ⟨⟨begun, hlive⟩, ha.1⟩
    rw [if_pos ⟨hgate, he⟩] at hsnoc
    exact Or.inl ⟨hinc, hsnoc⟩
  · have hinc : o.increment = false := by
      rw [htag, hc.1]
      rfl
    have hnot : ¬ (BankTrialProbabilityArmedGate x ∧
        e = root) := by
      intro h
      have hr : bankTrialLiveWaveRootMode x.bank = .ARMED :=
        h.1.2
      rw [hc.1] at hr
      cases hr
    rw [if_neg hnot, Nat.add_zero] at hsnoc
    exact Or.inr ⟨hinc, hsnoc⟩

end L3



namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The exact stopped origin census of the actual observer, on a
chronological prefix of the original scheduler tape. -/
noncomputable def bankTrialC5ActualPrefixOrigins {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) : Nat :=
  Prob.originsWord (bankTrialLocalNext ring root)
    bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
    (bankTrialLocalStart S) pre

/-- An appended service creates its origin unless the preceding
state is terminal. This uses the actual Stop guard, and the
absorbing nature of WON and LOST. -/
theorem bankTrialC5ActualPrefixOriginsSnoc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) (e : Fin n) :
    bankTrialC5ActualPrefixOrigins ring root S (pre ++ [e]) =
      bankTrialC5ActualPrefixOrigins ring root S pre +
        (if bankTrialLocalTerminal
              (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
         then 0
         else (bankTrialC5ActualStarts ring root S
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) e).length) := by
  have haux :
      ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
        Prob.originsWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
            z (w ++ [e]) =
          Prob.originsWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
              z w +
            (if bankTrialLocalTerminal
                  (bankTrialLocalRun ring root w z)
             then 0
             else (bankTrialC5ActualStarts ring root S
                    (bankTrialLocalRun ring root w z) e).length) := by
    intro w
    induction w with
    | nil =>
        intro z
        by_cases ht : bankTrialLocalTerminal z
        · simp [Prob.originsWord, bankTrialLocalRun, ht]
        · simp [Prob.originsWord, bankTrialLocalRun, ht]
    | cons f tail ih =>
        intro z
        by_cases ht : bankTrialLocalTerminal z
        · have hz : bankTrialLocalRun ring root (f :: tail) z = z :=
            bankTrialLocalRunTerminalAbsorbs ring root
              (f :: tail) z ht
          simp only [List.cons_append, Prob.originsWord,
            if_pos ht, hz, Nat.zero_add]
        · simp only [List.cons_append, Prob.originsWord,
            if_neg ht, bankTrialLocalRun]
          rw [ih (bankTrialLocalNext ring root z f), Nat.add_assoc]
          congr 2
  exact haux pre (bankTrialLocalStart S)

/-- No LIVE predecessor means the actual-origin guard is false,
independently of the bank's physical root mode. -/
theorem bankTrialC5ActualStartsZeroOfNotLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hn : ¬ ∃ begun : Bool, z.phase = .live begun) :
    (bankTrialC5ActualStarts ring root S z e).length = 0 := by
  unfold bankTrialC5ActualStarts
  split
  · rename_i hg
    obtain ⟨begun, _, hlive, _⟩ := hg.2.2.2.1
    exact False.elim (hn ⟨begun, hlive⟩)
  · rfl

/-- Outside the two exact launch-mode changes, the actual census
cannot emit an origin. -/
theorem bankTrialC5ActualStartsZeroOfModes {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hn :
      ¬ ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
           bankTrialLiveWaveRootMode
             (bankTrialLocalNext ring root z e).bank = .IWAIT) ∨
         (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
           bankTrialLiveWaveRootMode
             (bankTrialLocalNext ring root z e).bank = .CWAIT))) :
    (bankTrialC5ActualStarts ring root S z e).length = 0 := by
  unfold bankTrialC5ActualStarts
  split
  · rename_i hg
    exact False.elim (hn hg.2.2.2.2)
  · rfl

/-- If the service does not pay an ARMED head and the old mode
is not CSTART, no actual origin can be created. -/
theorem bankTrialC5ActualStartsZeroOfNoCredit {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hpay : ¬ (BankTrialProbabilityArmedGate z ∧ e = root))
    (hc : bankTrialLiveWaveRootMode z.bank ≠ .CSTART) :
    (bankTrialC5ActualStarts ring root S z e).length = 0 := by
  unfold bankTrialC5ActualStarts
  split
  · rename_i hg
    rcases hg.2.2.2.2 with ha | hh
    · obtain ⟨begun, _, hlive, _⟩ := hg.2.2.2.1
      exact False.elim (hpay
        ⟨⟨⟨begun, hlive⟩, ha.1⟩, hg.2.2.1⟩)
    · exact False.elim (hc hh.1)
  · rfl

/-- A service whose old AND new root modes are in the interstage
IWAIT/CSTART palette cannot itself be a new launch. -/
theorem bankTrialC5ActualStartsZeroOfInterstage {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hold : bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
      bankTrialLiveWaveRootMode z.bank = .CSTART)
    (hnew :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .IWAIT ∨
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .CSTART) :
    (bankTrialC5ActualStarts ring root S z e).length = 0 := by
  apply bankTrialC5ActualStartsZeroOfModes ring root e S z
  intro hm
  rcases hm with ha | hc
  · rcases hold with hi | hs
    · rw [ha.1] at hi
      cases hi
    · rw [ha.1] at hs
      cases hs
  · rcases hnew with hi | hs
    · rw [hc.2] at hi
      cases hi
    · rw [hc.2] at hs
      cases hs

/-- The remaining PHYSICAL one-step obligation needed for the
two-credit-per-head accounting. An IWAIT or CSTART LIVE successor
must have been an interstage successor already, or result from
a newly paid outgoing ARMED head. This is not proved here. -/
def BankTrialC5ActualLiveModeEntry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ (pre : List (Fin n)) (e : Fin n) (nextBegun : Bool),
    (bankTrialLocalNext ring root
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      e).phase = .live nextBegun →
    (bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          e).bank = .IWAIT ∨
     bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          e).bank = .CSTART) →
    (bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S)).bank =
          .IWAIT ∨
     bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S)).bank =
          .CSTART) ∨
      (BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) ∧
        e = root)

/-- The all-prefix amortized accounting invariant. The second
inequality retains one unused origin slot at LIVE IWAIT/CSTART;
this slot pays for the next possible CSTART-to-CWAIT launch. -/
def BankTrialC5ActualPrefixCharge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) : Prop :=
  bankTrialC5ActualPrefixOrigins ring root S pre ≤
    2 * bankTrialLiveHeadCount ring root pre (bankTrialLocalStart S) + 1 ∧
  ∀ begun : Bool,
    (bankTrialLocalRun ring root pre
      (bankTrialLocalStart S)).phase = .live begun →
    (bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank = .IWAIT ∨
     bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank = .CSTART) →
    bankTrialC5ActualPrefixOrigins ring root S pre ≤
      2 * bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S)

/-- Pure chronological accounting conditional on the unique
physical LIVE mode-entry row. The origin count is the real
Stop-guarded Prob.originsWord, not a surrogate count. -/
theorem bankTrialC5ActualPrefixChargeOfModeEntry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hentry : BankTrialC5ActualLiveModeEntry ring root S)
    (word : List (Fin n)) :
    BankTrialC5ActualPrefixCharge ring root S word := by
  have hrev : ∀ rev : List (Fin n),
      BankTrialC5ActualPrefixCharge ring root S rev.reverse := by
    intro rev
    induction rev with
    | nil =>
        unfold BankTrialC5ActualPrefixCharge
        constructor
        · change 0 ≤ 2 * 0 + 1
          omega
        · intro begun hlive hm
          have har : bankTrialLiveWaveRootMode S = .ARMED :=
            hclean.2.1
          change bankTrialLiveWaveRootMode S = .IWAIT ∨
            bankTrialLiveWaveRootMode S = .CSTART at hm
          rcases hm with hi | hc
          · rw [har] at hi
            cases hi
          · rw [har] at hc
            cases hc
    | cons e rest ih =>
        rw [List.reverse_cons]
        unfold BankTrialC5ActualPrefixCharge at ih ⊢
        have hheads := bankTrialC5StrengthenedSnocHeads
          ring root (bankTrialLocalStart S) rest.reverse e
        have horigins := bankTrialC5ActualPrefixOriginsSnoc
          ring root S rest.reverse e
        have hbirth := bankTrialC5ActualStartsLength
          ring root S
          (bankTrialLocalRun ring root rest.reverse
            (bankTrialLocalStart S)) e
        by_cases hlive :
            ∃ begun : Bool,
              (bankTrialLocalRun ring root rest.reverse
                (bankTrialLocalStart S)).phase = .live begun
        · obtain ⟨begun, holdlive⟩ := hlive
          have hnotstop : ¬ bankTrialLocalTerminal
              (bankTrialLocalRun ring root rest.reverse
                (bankTrialLocalStart S)) := by
            intro ht
            rcases ht with hw | hl
            · rw [holdlive] at hw
              cases hw
            · rw [holdlive] at hl
              cases hl
          rw [if_neg hnotstop] at horigins
          by_cases hpay :
              BankTrialProbabilityArmedGate
                (bankTrialLocalRun ring root rest.reverse
                  (bankTrialLocalStart S)) ∧ e = root
          · rw [if_pos hpay] at hheads
            constructor
            · omega
            · intro nextBegun hnext hm
              omega
          · rw [if_neg hpay, Nat.add_zero] at hheads
            constructor
            · by_cases hcstart :
                bankTrialLiveWaveRootMode
                  (bankTrialLocalRun ring root rest.reverse
                    (bankTrialLocalStart S)).bank = .CSTART
              · have hstrict := ih.2 begun holdlive
                  (Or.inr hcstart)
                omega
              · have hzero := bankTrialC5ActualStartsZeroOfNoCredit
                  ring root e S
                  (bankTrialLocalRun ring root rest.reverse
                    (bankTrialLocalStart S)) hpay hcstart
                omega
            · intro nextBegun hnext hm
              have hnext' :
                  (bankTrialLocalNext ring root
                    (bankTrialLocalRun ring root rest.reverse
                      (bankTrialLocalStart S)) e).phase =
                        .live nextBegun := by
                rw [← bankTrialC5StrengthenedSnocRun ring root
                  (bankTrialLocalStart S) rest.reverse e]
                exact hnext
              have hm' :
                  bankTrialLiveWaveRootMode
                    (bankTrialLocalNext ring root
                      (bankTrialLocalRun ring root rest.reverse
                        (bankTrialLocalStart S)) e).bank = .IWAIT ∨
                  bankTrialLiveWaveRootMode
                    (bankTrialLocalNext ring root
                      (bankTrialLocalRun ring root rest.reverse
                        (bankTrialLocalStart S)) e).bank = .CSTART := by
                rw [← bankTrialC5StrengthenedSnocRun ring root
                  (bankTrialLocalStart S) rest.reverse e]
                exact hm
              rcases hentry rest.reverse e nextBegun hnext' hm' with
                hstay | hpaid
              · have hstrict := ih.2 begun holdlive hstay
                have hzero := bankTrialC5ActualStartsZeroOfInterstage
                  ring root e S
                  (bankTrialLocalRun ring root rest.reverse
                    (bankTrialLocalStart S)) hstay hm'
                omega
              · exact False.elim (hpay hpaid)
        · have hnotpay :
              ¬ (BankTrialProbabilityArmedGate
                (bankTrialLocalRun ring root rest.reverse
                  (bankTrialLocalStart S)) ∧ e = root) := by
            intro h
            exact hlive h.1.1
          have hzero := bankTrialC5ActualStartsZeroOfNotLive
            ring root e S
            (bankTrialLocalRun ring root rest.reverse
              (bankTrialLocalStart S)) hlive
          rw [if_neg hnotpay, Nat.add_zero] at hheads
          simp only [hzero, ite_self, Nat.add_zero] at horigins
          constructor
          · omega
          · intro nextBegun hnext hm
            have hnext' :
                (bankTrialLocalNext ring root
                  (bankTrialLocalRun ring root rest.reverse
                    (bankTrialLocalStart S)) e).phase =
                    .live nextBegun := by
              rw [← bankTrialC5StrengthenedSnocRun ring root
                (bankTrialLocalStart S) rest.reverse e]
              exact hnext
            obtain ⟨oldBegun, holdlive⟩ :=
              bankTrialC5StrengthenedOldLive ring root e
                (bankTrialLocalRun ring root rest.reverse
                  (bankTrialLocalStart S)) nextBegun hnext'
            exact False.elim (hlive ⟨oldBegun, holdlive⟩)
  have h := hrev word.reverse
  simpa only [List.reverse_reverse] using h

/-- The full numerical 2K+1 cap follows from the mode-entry row,
the actual all-word head bound, and no additional probability
assumption. The mode-entry row itself remains open. -/
theorem bankTrialC5ActualStartCapOfModeEntry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hentry : BankTrialC5ActualLiveModeEntry ring root S) :
    BankTrialProbabilityC5WorkerStartCap
      ring root S (bankTrialC5ActualStarts ring root S) := by
  change ∀ w : List (Fin n),
    bankTrialC5ActualPrefixOrigins ring root S w ≤
      2 * (compileAdvice q).K + 1
  intro w
  have hcharge := (bankTrialC5ActualPrefixChargeOfModeEntry
    ring root S hclean hentry w).1
  have hheads := bankTrialC5ActualAllWordsHeadCap
    ring root S hsp hlarge hwidth hclean w
  omega

/-- Exact goodReturn field, conditional only on discharge of the
single physical mode-entry row; no start cap is assumed here. -/
theorem bankTrialC5ActualGoodReturnOfModeEntry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hentry : BankTrialC5ActualLiveModeEntry ring root S) :
    BankTrialProbabilityC5WorkerStartCap
      ring root S (bankTrialC5ActualStarts ring root S) ∧
      ∀ (x : BankTrialLocalState q) (e : Fin n)
        (o : BankTrialC5ActualOrigin n q),
        o ∈ bankTrialC5ActualStarts ring root S x e →
        ∀ w : List (Fin n),
          bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root w o.after) →
          (if o.increment then
             bankTrialLiveWaveRootMode
               (bankTrialLocalRun ring root w o.after).bank = .CSTART
           else
             (o.heads < (compileAdvice q).K ∧
               BankTrialC5ArmedAt q
                 (bankTrialLocalRun ring root w o.after)
                 o.heads) ∨
             (o.heads = (compileAdvice q).K ∧
               (bankTrialLocalRun ring root w o.after).phase = .won)) := by
  exact bankTrialC5ActualGoodReturnOfStartCap ring root S
    (bankTrialC5ActualStartCapOfModeEntry
      ring root S hsp hlarge hwidth hclean hentry)

end L3


namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Literal source-owner inversion. Neither a RESET/RWAIT recovery
service nor any CWAIT service can create IWAIT or CSTART.
The only additional possible predecessor is ARMED. -/
theorem bankTrialC5RawRootLiveModePredecessor
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnew :
      (bankPair x y 1 b theta).1.mode = .IWAIT ∨
      (bankPair x y 1 b theta).1.mode = .CSTART) :
    x.mode = .IWAIT ∨ x.mode = .CSTART ∨ x.mode = .ARMED := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode with
  | ARMED =>
      exact Or.inr (Or.inr rfl)
  | IWAIT =>
      exact Or.inl rfl
  | CSTART =>
      exact Or.inr (Or.inl rfl)
  | RESET =>
      have hr := (bankTrialLocalRawRootLaunch
        b theta x y hbpos hx hy hg hm).1
      rcases hnew with hi | hc
      · rw [hr] at hi
        cases hi
      · rw [hr] at hc
        cases hc
  | RWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
          simp [bankPair, hx, hy, hg, hm, ht, hl,
            hbpos, hbne, isRetTok, isWaitMode,
            Id.run_pure, Id.run_bind] at hnew
  | CWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
          simp [bankPair, hx, hy, hg, hm, ht, hl,
            hbpos, hbne, isRetTok, isWaitMode,
            Id.run_pure, Id.run_bind] at hnew

/-- Exact single-step inversion. The public incoming-root LIVE
frame handles the incoming edge. Every nonincident edge frames
the root field, including top, interior and outside services.
Only the root-outgoing owner needs the literal bankPair inversion. -/
theorem bankTrialC5LiveModeEntryStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveNoResetLocked z)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z e).phase =
      .live nextBegun)
    (hmodes :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .IWAIT ∨
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .CSTART) :
    (bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
      bankTrialLiveWaveRootMode z.bank = .CSTART) ∨
      (BankTrialProbabilityArmedGate z ∧ e = root) := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive
      ring root e z nextBegun hnext
  have hzeta :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  have hnextCanonical :
      (bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) e).phase =
          .live nextBegun := by
    rw [← hzeta]
    exact hnext
  by_cases he : e = root
  · subst e
    have hf : z.bank.success = false :=
      bankTrialWindowLiveOldNotLatched
        ring root root z.bank begun nextBegun hnextCanonical
    have hbank :
        (bankTrialLocalNext ring root z root).bank =
          GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank root := by
      rw [hzeta]
      exact bankTrialLocalNextLiveBank
        ring root root z.bank begun
    have hstepMode :
        bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank root) = .IWAIT ∨
        bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank root) = .CSTART := by
      simpa only [hbank] using hmodes
    have hproject := (bankTrialCmpRoot
      ring root hw z.bank hf).1
    have hraw :
        (GrantBankReference.bankLocalReferenceInternalPair
          q z.bank ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).1.mode = .IWAIT ∨
        (GrantBankReference.bankLocalReferenceInternalPair
          q z.bank ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).1.mode = .CSTART := by
      simpa only [hproject] using hstepMode
    have hpair :
        (bankPair
          (GrantBankReference.bankLocalReferenceCell
            z.bank ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
          (GrantBankReference.bankLocalReferenceCell
            z.bank ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
          1 (compileAdvice q).b (compileAdvice q).theta).1.mode =
            .IWAIT ∨
        (bankPair
          (GrantBankReference.bankLocalReferenceCell
            z.bank ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
          (GrantBankReference.bankLocalReferenceCell
            z.bank ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
          1 (compileAdvice q).b (compileAdvice q).theta).1.mode =
            .CSTART := hraw
    have hb : 1 < (compileAdvice q).b := by
      have hh := bankTrialCmpWidth q
      omega
    have hpred := bankTrialC5RawRootLiveModePredecessor
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell
        z.bank ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
      (GrantBankReference.bankLocalReferenceCell
        z.bank ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      hb rfl rfl rfl hpair
    change
      bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
      bankTrialLiveWaveRootMode z.bank = .CSTART ∨
      bankTrialLiveWaveRootMode z.bank = .ARMED at hpred
    rcases hpred with hi | hc | ha
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hc)
    · exact Or.inr ⟨⟨⟨begun, hlive⟩, ha⟩, rfl⟩
  · by_cases hin : ring.rightNeighbor e = root
    · have hlockCanonical :
          BankTrialLiveNoResetLocked
            (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
        rw [← hzeta]
        exact hlock
      have hframe :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root z e).bank =
          bankTrialLiveWaveRootMode z.bank := by
        rw [hzeta]
        exact bankTrialC5IncomingRootModeFrame
          ring root e hw z.bank begun nextBegun
          hlockCanonical hin hnextCanonical
      rw [hframe] at hmodes
      exact Or.inl hmodes
    · have hf : z.bank.success = false :=
        bankTrialWindowLiveOldNotLatched
          ring root e z.bank begun nextBegun hnextCanonical
      have hfield := bankTrialLocalRootNonincidentFrame
        ring root e z.bank hf he hin
      have hbank :
          (bankTrialLocalNext ring root z e).bank =
            GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank e := by
        rw [hzeta]
        exact bankTrialLocalNextLiveBank
          ring root e z.bank begun
      have hframe :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root z e).bank =
          bankTrialLiveWaveRootMode z.bank := by
        rw [hbank]
        exact congrArg
          (fun v : Mode × Bool × BTok × Nat => v.1) hfield
      rw [hframe] at hmodes
      exact Or.inl hmodes

/-- The open LIVE mode-entry row follows on all reachable
CLEAN prefixes. The prefix lock is proved for arbitrary words. -/
theorem bankTrialC5ActualLiveModeEntryHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5ActualLiveModeEntry ring root S := by
  intro pre e nextBegun hnext hmodes
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hlocked : BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)) :=
    bankTrialC5LockedArbitraryWord ring root hw pre
      (bankTrialLocalStart S)
      (bankTrialLiveNoResetLockedStart S hclean)
  exact bankTrialC5LiveModeEntryStep ring root e hw
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    hlocked nextBegun hnext hmodes

/-- Unconditional actual 2K+1 tagged-worker cap. -/
theorem bankTrialC5ActualStartCapHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialProbabilityC5WorkerStartCap
      ring root S (bankTrialC5ActualStarts ring root S) := by
  exact bankTrialC5ActualStartCapOfModeEntry
    ring root S hsp hlarge hwidth hclean
    (bankTrialC5ActualLiveModeEntryHolds ring root S hlarge hclean)

/-- The kernel's exact goodReturn field with no start-cap
premise or further unproved transition condition. -/
theorem bankTrialC5ActualGoodReturnHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialProbabilityC5WorkerStartCap
      ring root S (bankTrialC5ActualStarts ring root S) ∧
      ∀ (x : BankTrialLocalState q) (e : Fin n)
        (o : BankTrialC5ActualOrigin n q),
        o ∈ bankTrialC5ActualStarts ring root S x e →
        ∀ w : List (Fin n),
          bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root w o.after) →
          (if o.increment then
             bankTrialLiveWaveRootMode
               (bankTrialLocalRun ring root w o.after).bank = .CSTART
           else
             (o.heads < (compileAdvice q).K ∧
               BankTrialC5ArmedAt q
                 (bankTrialLocalRun ring root w o.after)
                 o.heads) ∨
             (o.heads = (compileAdvice q).K ∧
               (bankTrialLocalRun ring root w o.after).phase = .won)) := by
  exact bankTrialC5ActualGoodReturnOfModeEntry
    ring root S hsp hlarge hwidth hclean
    (bankTrialC5ActualLiveModeEntryHolds ring root S hlarge hclean)

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A phase-local maximum over the actual digit token array.
This uses the already-proved single-token rank, rather than
the larger lease-aware C.6 rank. -/
def bankTrialC5ActualWaveRank {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  (List.ofFn (fun i : Fin (compileAdvice q).b =>
    bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
      (bankTrialLiveWaveToken B i))).foldl Nat.max 0

private theorem bankTrialC5ActualFoldMaxBound
    (xs : List Nat) :
    ∀ (seed bound : Nat), seed ≤ bound →
      (∀ item : Nat, item ∈ xs → item ≤ bound) →
      xs.foldl Nat.max seed ≤ bound := by
  induction xs with
  | nil =>
      intro seed bound hseed _
      exact hseed
  | cons head tail ih =>
      intro seed bound hseed hall
      change tail.foldl Nat.max (Nat.max seed head) ≤ bound
      apply ih (Nat.max seed head) bound
      · exact Nat.max_le_of_le_of_le hseed
          (hall head (by simp))
      · intro item hitem
        exact hall item (by simp [hitem])

/-- The physical maximum token rank is at most 2b+2 on EVERY
bank array; no certificate or uniqueness assumption is used
for this numerical cap. -/
theorem bankTrialC5ActualWaveRankCap {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialC5ActualWaveRank B ≤ 2 * (compileAdvice q).b + 2 := by
  unfold bankTrialC5ActualWaveRank
  apply bankTrialC5ActualFoldMaxBound
    (List.ofFn (fun i : Fin (compileAdvice q).b =>
      bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
        (bankTrialLiveWaveToken B i)))
    0 (2 * (compileAdvice q).b + 2) (Nat.zero_le _)
  intro item hmem
  obtain ⟨i, hi⟩ := (List.mem_ofFn).1 hmem
  rw [← hi]
  exact bankTrialC5PhaseTokenRankCap
    (compileAdvice q).b (i.val + 1)
    (bankTrialLiveWaveToken B i)
    (by omega) (Nat.succ_le_of_lt i.isLt)

/-- This class includes exactly states produced before an exit and
their first exit successors. In particular, it does NOT include
arbitrary states occurring after an earlier return/badExit. -/
inductive BankTrialC5ActualFirstExitReachable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    BankTrialLocalState q → Prop where
  | start :
      BankTrialC5ActualFirstExitReachable ring root o o.after
  | advance (z : BankTrialLocalState q)
      (hz : BankTrialC5ActualFirstExitReachable ring root o z)
      (hnot : ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z))
      (e : Fin n) :
      BankTrialC5ActualFirstExitReachable ring root o
        (bankTrialLocalNext ring root z e)

/-- A target extended by the complement of a class closed
BEFORE the original target has exactly the same finite-horizon
first-hit cost from an in-class start. Closure is not required
once the target has already been hit. -/
private theorem bankTrialC5CostPreExitClosedTarget
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (A P : X → Prop)
    (hclosed : ∀ z, A z → ¬ P z →
      ∀ e : Fin n, A (next z e)) :
    ∀ z, A z → ∀ T,
      costNumerator next P z T =
        costNumerator next (fun y => ¬ A y ∨ P y) z T := by
  classical
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero]
  | succ T ih =>
      by_cases hp : P z
      · rw [costNumerator_terminal next P z hp (T + 1),
          costNumerator_terminal next (fun y => ¬ A y ∨ P y)
            z (Or.inr hp) (T + 1)]
      · have hu : ¬ (¬ A z ∨ P z) := by
          intro h
          rcases h with hna | hp'
          · exact hna hz
          · exact hp hp'
        rw [costNumerator_succ next P z hp T,
          costNumerator_succ next (fun y => ¬ A y ∨ P y)
            z hu T]
        have hsum := ofFn_sum_eq
          (fun e : Fin n => costNumerator next P (next z e) T)
          (fun e : Fin n =>
            costNumerator next (fun y => ¬ A y ∨ P y)
              (next z e) T)
          (fun e => ih (next z e) (hclosed z hz hp e))
        rw [hsum]

/-- The nominated-edge mean theorem restricted to first-exit
reachable states. This is a genuine reduction of the ALL-STATES
premises in bankTrialC5ActualBoundedMeanOfNominatedRows. -/
theorem bankTrialC5ActualMeanOfFirstExitNominatedRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (rank : BankTrialLocalState q → Nat)
    (chosen : BankTrialLocalState q → Fin n)
    (hdrop : ∀ z : BankTrialLocalState q,
      BankTrialC5ActualFirstExitReachable ring root o z →
      ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z) →
      rank (bankTrialLocalNext ring root z (chosen z)) + 1 ≤
        rank z)
    (hnoninc : ∀ z : BankTrialLocalState q,
      BankTrialC5ActualFirstExitReachable ring root o z →
      ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z) →
      ∀ e : Fin n,
        rank (bankTrialLocalNext ring root z e) ≤ rank z)
    (hstart : rank o.after ≤ 2 * (compileAdvice q).b + 3)
    (T : Nat) :
    costNumerator (bankTrialLocalNext ring root)
      (fun z => bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z)
      o.after T ≤
      n ^ T * ((2 * (compileAdvice q).b + 3) * n) := by
  classical
  have hseed :
      BankTrialC5ActualFirstExitReachable ring root o o.after :=
    BankTrialC5ActualFirstExitReachable.start
  have hclosed : ∀ z : BankTrialLocalState q,
      BankTrialC5ActualFirstExitReachable ring root o z →
      ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z) →
      ∀ e : Fin n,
        BankTrialC5ActualFirstExitReachable ring root o
          (bankTrialLocalNext ring root z e) := by
    intro z hz hn e
    exact BankTrialC5ActualFirstExitReachable.advance z hz hn e
  have hdropGlobal : ∀ z : BankTrialLocalState q,
      ¬ (¬ BankTrialC5ActualFirstExitReachable ring root o z ∨
        (bankTrialC5ActualReturned o z ∨
         bankTrialC5ActualBadExit o z)) →
      (if BankTrialC5ActualFirstExitReachable ring root o
              (bankTrialLocalNext ring root z (chosen z))
       then rank (bankTrialLocalNext ring root z (chosen z))
       else 0) + 1 ≤
      (if BankTrialC5ActualFirstExitReachable ring root o z
       then rank z else 0) := by
    intro z hn
    by_cases hz : BankTrialC5ActualFirstExitReachable ring root o z
    · have hp : ¬ (bankTrialC5ActualReturned o z ∨
          bankTrialC5ActualBadExit o z) := by
        intro h
        exact hn (Or.inr h)
      have hnext := hclosed z hz hp (chosen z)
      simpa only [if_pos hz, if_pos hnext] using
        (hdrop z hz hp)
    · exact False.elim (hn (Or.inl hz))
  have hnonincGlobal : ∀ z : BankTrialLocalState q,
      ¬ (¬ BankTrialC5ActualFirstExitReachable ring root o z ∨
        (bankTrialC5ActualReturned o z ∨
         bankTrialC5ActualBadExit o z)) →
      ∀ e : Fin n,
      (if BankTrialC5ActualFirstExitReachable ring root o
              (bankTrialLocalNext ring root z e)
       then rank (bankTrialLocalNext ring root z e)
       else 0) ≤
      (if BankTrialC5ActualFirstExitReachable ring root o z
       then rank z else 0) := by
    intro z hn e
    by_cases hz : BankTrialC5ActualFirstExitReachable ring root o z
    · have hp : ¬ (bankTrialC5ActualReturned o z ∨
          bankTrialC5ActualBadExit o z) := by
        intro h
        exact hn (Or.inr h)
      have hnext := hclosed z hz hp e
      simpa only [if_pos hz, if_pos hnext] using
        (hnoninc z hz hp e)
    · exact False.elim (hn (Or.inl hz))
  have hcost := Prob.costNumerator_le_of_nominated_edge
    (bankTrialLocalNext ring root)
    (fun z : BankTrialLocalState q =>
      ¬ BankTrialC5ActualFirstExitReachable ring root o z ∨
        (bankTrialC5ActualReturned o z ∨
         bankTrialC5ActualBadExit o z))
    (fun z => if BankTrialC5ActualFirstExitReachable ring root o z
      then rank z else 0)
    chosen hdropGlobal hnonincGlobal o.after T
  have hcostEq :=
    bankTrialC5CostPreExitClosedTarget
      (bankTrialLocalNext ring root)
      (BankTrialC5ActualFirstExitReachable ring root o)
      (fun z : BankTrialLocalState q =>
        bankTrialC5ActualReturned o z ∨
          bankTrialC5ActualBadExit o z)
      hclosed o.after hseed T
  calc
    costNumerator (bankTrialLocalNext ring root)
        (fun z => bankTrialC5ActualReturned o z ∨
          bankTrialC5ActualBadExit o z)
        o.after T =
      costNumerator (bankTrialLocalNext ring root)
        (fun z => ¬ BankTrialC5ActualFirstExitReachable
          ring root o z ∨
          (bankTrialC5ActualReturned o z ∨
            bankTrialC5ActualBadExit o z))
        o.after T := hcostEq
    _ ≤ n ^ T * (n * rank o.after) := by
      simpa only [if_pos hseed] using hcost
    _ ≤ n ^ T * (n * (2 * (compileAdvice q).b + 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left n hstart)
    _ = n ^ T * ((2 * (compileAdvice q).b + 3) * n) := by
      rw [Nat.mul_comm n (2 * (compileAdvice q).b + 3)]

/-- The remaining physical source-row obligation, scoped only
to first-exit prefixes of actual emitted workers. The concrete
rank is the maximum of the source's phase-local token ranks;
no global transition claim is hidden in this definition. -/
def BankTrialC5ActualFirstExitWaveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q),
    o ∈ bankTrialC5ActualStarts ring root S x e →
    ∀ z : BankTrialLocalState q,
      BankTrialC5ActualFirstExitReachable ring root o z →
      ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z) →
      (∀ f : Fin n,
        bankTrialC5ActualWaveRank
          (bankTrialLocalNext ring root z f).bank ≤
          bankTrialC5ActualWaveRank z.bank) ∧
      (∃ f : Fin n,
        bankTrialC5ActualWaveRank
          (bankTrialLocalNext ring root z f).bank + 1 ≤
          bankTrialC5ActualWaveRank z.bank)

/-- First-exit wave rows, if physically discharged, give the
EXACT boundedMean kernel field with the required numerical
constant and without all-state nominated assumptions. -/
theorem bankTrialC5ActualBoundedMeanOfFirstExitWaveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrows : BankTrialC5ActualFirstExitWaveRows ring root S) :
    ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      o.after = bankTrialLocalNext ring root x e ∧
      ∀ T : Nat,
        costNumerator (bankTrialLocalNext ring root)
          (fun z => bankTrialC5ActualReturned o z ∨
            bankTrialC5ActualBadExit o z)
          o.after T ≤
          n ^ T * ((2 * (compileAdvice q).b + 2 + 1) * n) := by
  classical
  intro x e o ho
  refine ⟨bankTrialC5ActualStartPost ring root S x e o ho, ?_⟩
  have hpick : ∀ z : BankTrialLocalState q,
      ∃ f : Fin n,
        BankTrialC5ActualFirstExitReachable ring root o z →
        ¬ (bankTrialC5ActualReturned o z ∨
          bankTrialC5ActualBadExit o z) →
        bankTrialC5ActualWaveRank
          (bankTrialLocalNext ring root z f).bank + 1 ≤
          bankTrialC5ActualWaveRank z.bank := by
    intro z
    by_cases hz :
        BankTrialC5ActualFirstExitReachable ring root o z ∧
        ¬ (bankTrialC5ActualReturned o z ∨
          bankTrialC5ActualBadExit o z)
    · obtain ⟨f, hd⟩ := (hrows x e o ho z hz.1 hz.2).2
      exact ⟨f, fun _ _ => hd⟩
    · exact ⟨root, fun hr hn => False.elim (hz ⟨hr, hn⟩)⟩
  let chosen : BankTrialLocalState q → Fin n :=
    fun z => Classical.choose (hpick z)
  have hdrop : ∀ z : BankTrialLocalState q,
      BankTrialC5ActualFirstExitReachable ring root o z →
      ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z) →
      bankTrialC5ActualWaveRank
          (bankTrialLocalNext ring root z (chosen z)).bank + 1 ≤
        bankTrialC5ActualWaveRank z.bank := by
    intro z hr hn
    exact (Classical.choose_spec (hpick z)) hr hn
  have hnoninc : ∀ z : BankTrialLocalState q,
      BankTrialC5ActualFirstExitReachable ring root o z →
      ¬ (bankTrialC5ActualReturned o z ∨
        bankTrialC5ActualBadExit o z) →
      ∀ f : Fin n,
        bankTrialC5ActualWaveRank
          (bankTrialLocalNext ring root z f).bank ≤
          bankTrialC5ActualWaveRank z.bank := by
    intro z hr hn f
    exact (hrows x e o ho z hr hn).1 f
  have hstart :
      bankTrialC5ActualWaveRank o.after.bank ≤
        2 * (compileAdvice q).b + 3 := by
    have hc := bankTrialC5ActualWaveRankCap o.after.bank
    omega
  intro T
  exact bankTrialC5ActualMeanOfFirstExitNominatedRank
    ring root o
    (fun z => bankTrialC5ActualWaveRank z.bank)
    chosen hdrop hnoninc hstart T

/-- Strict progress forces a nonempty rank on every unresolved
first-exit state; this isolates the no-orphan requirement. -/
theorem bankTrialC5ActualFirstExitNoZeroRankOfRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrows : BankTrialC5ActualFirstExitWaveRows ring root S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hr : BankTrialC5ActualFirstExitReachable ring root o z)
    (hn : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    0 < bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨f, hd⟩ := (hrows x e o ho z hr hn).2
  omega

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Every first-exit descendant of a genuine actual origin still
has a chronological CLEAN-run witness. This includes the first exit
state itself, but not arbitrary states after that exit. -/
theorem bankTrialC5ActualFirstExitCleanReachable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z) :
    ∃ w : List (Fin n),
      bankTrialLocalRun ring root w (bankTrialLocalStart S) = z := by
  obtain ⟨_, ⟨launch, hlaunch⟩, _, _, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  induction hz with
  | start =>
      refine ⟨launch ++ [e], ?_⟩
      rw [bankTrialC5StrengthenedSnocRun, hlaunch]
      exact (bankTrialC5ActualStartPost ring root S x e o ho).symm
  | advance y hy hnot f ih =>
      obtain ⟨word, hword⟩ := ih
      refine ⟨word ++ [f], ?_⟩
      rw [bankTrialC5StrengthenedSnocRun, hword]

/-- The full source-level LIVE worker certificate and no-RESET
lock are inherited by every first-exit descendant. -/
theorem bankTrialC5ActualFirstExitLocked {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z) :
    BankTrialLiveNoResetLocked z := by
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hlocked := bankTrialWindowLockedCleanWords
    ring root hw S hclean word
  rw [hword] at hlocked
  exact hlocked

/-- The installed unique-worker certificate applies
to the original worker's complete unresolved first-exit class. -/
theorem bankTrialC5ActualFirstExitUniqueToken {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (i j : Fin (compileAdvice q).b)
    (hi : bankTrialLiveWaveToken z.bank i ≠ .E)
    (hj : bankTrialLiveWaveToken z.bank j ≠ .E) :
    i = j := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hlocked := bankTrialC5ActualFirstExitLocked
    ring root S hlarge hclean x e o ho z hz
  exact (hlocked.1 begun hlive).uniqueWorker i j hi hj

/-- The known K < 2^b threshold excludes the only top-site IR
erasure scenario on every first-exit-reachable non-exited cut.
No chosen completion word is assumed. -/
theorem bankTrialC5ActualFirstExitNoTopIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    bankTrialLiveWaveToken z.bank
      ⟨(compileAdvice q).b - 1,
        by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR := by
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    have hn : ¬ q ≤ qStar :=
      of_decide_eq_false (hs.symm.trans hsp)
    change ¬ q ≤ 79 at hn
    omega
  have hK : 0 < (compileAdvice q).K := by
    change 0 < 2 * q + productionKappa q
    omega
  have hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep word
  rw [hword] at hInv
  exact bankTrialC5NoTopIRInLive z
    (bankTrialLiveHeadCount ring root word (bankTrialLocalStart S))
    hwidth hInv begun hlive

/-- The actual origin begins with an occupied first digit, not
merely a matching LIVE root wait mode. -/
theorem bankTrialC5ActualOriginFirstTokenNonempty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    bankTrialLiveWaveToken o.after.bank
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
  obtain ⟨_, ⟨pre, hpre⟩, _, _, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have hfirst := (bankTrialC5ActualLaunchTokenFacts
    ring root S hlarge hclean pre x hpre.symm e o ho).2
  rw [bankTrialC5ActualStartPost ring root S x e o ho]
  exact hfirst

/-- General fold-max monotonicity, with no Finset or Batteries. -/
private theorem bankTrialC5ActualFoldMaxMono :
    ∀ (m : Nat) (f g : Fin m → Nat)
      (seedF seedG : Nat),
      (∀ i : Fin m, f i ≤ g i) →
      seedF ≤ seedG →
      (List.ofFn f).foldl Nat.max seedF ≤
        (List.ofFn g).foldl Nat.max seedG := by
  intro m
  induction m with
  | zero =>
      intro f g seedF seedG _ hseed
      simpa only [List.ofFn_zero, List.foldl_nil] using hseed
  | succ k ih =>
      intro f g seedF seedG hpoint hseed
      rw [List.ofFn_succ, List.ofFn_succ,
        List.foldl_cons, List.foldl_cons]
      apply ih (fun i : Fin k => f i.succ)
        (fun i : Fin k => g i.succ)
        (Nat.max seedF (f 0)) (Nat.max seedG (g 0))
      · intro i
        exact hpoint i.succ
      · exact Nat.max_le_of_le_of_le
          (Nat.le_trans hseed (Nat.le_max_left _ _))
          (Nat.le_trans (hpoint 0) (Nat.le_max_right _ _))

/-- Incoming-root services frame the entire wave rank, even
when the root lease is decremented or resets. -/
theorem bankTrialC5ActualIncomingWaveRankFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hin : ring.rightNeighbor e = root) :
    bankTrialC5ActualWaveRank
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = bankTrialC5ActualWaveRank B := by
  unfold bankTrialC5ActualWaveRank
  have hfun :
      (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B e) i)) =
      (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken B i)) := by
    funext i
    rw [(bankTrialC5IncomingDigitFrame ring root e hw B hf hin i).2]
  rw [hfun]

/-- Unsupported scheduler letters frame the complete wave
rank, without a reachability or CLEAN hypothesis. -/
theorem bankTrialC5ActualOutsideWaveRankFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hout : ¬ Counter.Support q ring root e) :
    bankTrialC5ActualWaveRank
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = bankTrialC5ActualWaveRank B := by
  rw [bankTrialLocalStepOutside ring root e B hout]

/-- The nonalias top-site physical row frames every token when
top IR is absent, and hence frames the exact wave rank. -/
theorem bankTrialC5ActualTopWaveRankFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hnoIR : bankTrialLiveWaveToken B
      ⟨(compileAdvice q).b - 1,
        by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR) :
    bankTrialC5ActualWaveRank
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b)) =
      bankTrialC5ActualWaveRank B := by
  have hframe := (bankTrialC5TopWholeBitTokenModeFrame
    ring root hw B hf hnoIR).1
  unfold bankTrialC5ActualWaveRank
  have hfun :
      (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root (compileAdvice q).b))
            i)) =
      (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken B i)) := by
    funext i
    rw [(hframe i).2]
  rw [hfun]

/-- Direct raw-root owner statement: while the OLD root is
IWAIT or CWAIT, the root outgoing service never increases the
first digit's phase token rank. It may consume a returning AL/CL
or merely decrement its wait lease. -/
theorem bankTrialC5ActualRawRootWaitTokenRankNonincrease
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT) :
    bankTrialC5PhaseTokenRank b 1
      (bankPair x y 1 b theta).2.tok ≤
    bankTrialC5PhaseTokenRank b 1 y.tok := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hm with hi | hc
  · cases ht : y.tok <;>
      by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hi, ht, hl,
          hbpos, hbne, bankTrialC5PhaseTokenRank,
          isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
        omega
  · cases ht : y.tok <;>
      by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hc, ht, hl,
          hbpos, hbne, bankTrialC5PhaseTokenRank,
          isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
        omega

/-- Lift that raw-root rank inequality through the actual
clamped root pair. Every digit except digit one is framed. -/
theorem bankTrialC5ActualOutgoingWaveRankNonincrease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) :
    bankTrialC5ActualWaveRank
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) ≤ bankTrialC5ActualWaveRank B := by
  have hb : 1 < (compileAdvice q).b := by
    have hwidth := bankTrialCmpWidth q
    omega
  have hroot := bankTrialCmpRoot ring root hw B hf
  have hpair := bankTrialC5ActualRawRootWaitTokenRankNonincrease
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by have hwidth := bankTrialCmpWidth q; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by have hwidth := bankTrialCmpWidth q; omega⟩)
    hb rfl rfl rfl hm
  unfold bankTrialC5ActualWaveRank
  apply bankTrialC5ActualFoldMaxMono
    (compileAdvice q).b
    (fun i : Fin (compileAdvice q).b =>
      bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) i))
    (fun i : Fin (compileAdvice q).b =>
      bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
        (bankTrialLiveWaveToken B i))
    0 0 ?_ (Nat.le_refl 0)
  intro i
  by_cases hi : i.val = 0
  · have hiz : i = ⟨0, bankTrialWindowWidthPos q⟩ :=
      Fin.ext hi
    rw [hiz]
    have hfirst := ((hroot.2
      ⟨0, bankTrialWindowWidthPos q⟩).1 rfl).2
    rw [hfirst]
    change bankTrialC5PhaseTokenRank (compileAdvice q).b 1
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, bankTrialWindowWidthPos q⟩).2.tok ≤
      bankTrialC5PhaseTokenRank (compileAdvice q).b 1
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hwidth := bankTrialCmpWidth q; omega⟩).tok
    exact hpair
  · rw [((hroot.2 i).2 hi).2]
    exact Nat.le_refl _

/-- The exact root-outgoing nonincrease row, scoped to a
non-exited actual origin's first-exit-reachable state. -/
theorem bankTrialC5ActualFirstExitRootRankNonincrease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    bankTrialC5ActualWaveRank
      (bankTrialLocalNext ring root z root).bank ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  obtain ⟨⟨begun, hlive⟩, hmode⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  have hactual :
      bankTrialLocalRun ring root word (bankTrialLocalStart S) =
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    hword.trans hcanonical
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun hactual
  have hwait :
      bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
      bankTrialLiveWaveRootMode z.bank = .CWAIT := by
    cases hi : o.increment with
    | true =>
        apply Or.inl
        simpa only [hi, ↓reduceIte] using hmode
    | false =>
        apply Or.inr
        simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hmode
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hcanonical]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  rw [hbank]
  exact bankTrialC5ActualOutgoingWaveRankNonincrease
    ring root (bankTrialProbabilityUpperWindow hlarge)
    z.bank hf hwait

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

theorem bankTrialC5ActualProductionKPositive
    (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    0 < (compileAdvice q).K := by
  have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
  have hq : 3 ≤ q := by
    have hn : ¬ q ≤ qStar :=
      of_decide_eq_false (hs.symm.trans hsp)
    change ¬ q ≤ 79 at hn
    omega
  change 0 < 2 * q + productionKappa q
  omega

/-- Every first-exit reachable state inherits the
C.6 no-orphan invariant, including its positive worker witness. -/
theorem bankTrialC5ActualFirstExitOrphanInvariant {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z) :
    BankTrialDurationOrphanInv q z := by
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  exact bankTrialDurationReachableOrphanInv
    ring root (bankTrialProbabilityUpperWindow hlarge)
    (bankTrialC5ActualProductionKPositive q hsp)
    hwidth S hclean z ⟨word, hword⟩

/-- This is the requested worker persistence: no first-exit
reachable unresolved actual origin is workerless. -/
theorem bankTrialC5ActualFirstExitWorkerPersists {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    ∃ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j ≠ .E := by
  obtain ⟨⟨begun, hlive⟩, hmode⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hwait :
      bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
      bankTrialLiveWaveRootMode z.bank = .CWAIT := by
    cases hi : o.increment with
    | true =>
        apply Or.inl
        simpa only [hi, ↓reduceIte] using hmode
    | false =>
        apply Or.inr
        simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hmode
  have hinv := bankTrialC5ActualFirstExitOrphanInvariant
    ring root S hsp hlarge hwidth hclean x e o ho z hz
  exact hinv.workerPresent begun hlive hwait

private theorem bankTrialC5ActualFoldMaxSeedLower
    (xs : List Nat) :
    ∀ seed : Nat, seed ≤ xs.foldl Nat.max seed := by
  induction xs with
  | nil =>
      intro seed
      exact Nat.le_refl seed
  | cons head tail ih =>
      intro seed
      change seed ≤ tail.foldl Nat.max (Nat.max seed head)
      exact Nat.le_trans (Nat.le_max_left seed head)
        (ih (Nat.max seed head))

private theorem bankTrialC5ActualFoldMaxMember
    (xs : List Nat) :
    ∀ (seed item : Nat), item ∈ xs →
      item ≤ xs.foldl Nat.max seed := by
  induction xs with
  | nil =>
      intro seed item h
      cases h
  | cons head tail ih =>
      intro seed item h
      change item ≤ tail.foldl Nat.max (Nat.max seed head)
      have hc : item = head ∨ item ∈ tail := by
        simpa only [List.mem_cons] using h
      rcases hc with he | ht
      · rw [he]
        exact Nat.le_trans (Nat.le_max_right seed head)
          (bankTrialC5ActualFoldMaxSeedLower tail _)
      · exact ih (Nat.max seed head) item ht

/-- If all other tokens are E, the phase-local fold maximum is
exactly the one occupied token's rank. -/
theorem bankTrialC5ActualWaveRankSingleToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : Fin (compileAdvice q).b)
    (hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ w → bankTrialLiveWaveToken B i = .E) :
    bankTrialC5ActualWaveRank B =
      bankTrialC5PhaseTokenRank (compileAdvice q).b
        (w.val + 1) (bankTrialLiveWaveToken B w) := by
  unfold bankTrialC5ActualWaveRank
  have hupper :
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken B i))).foldl Nat.max 0 ≤
      bankTrialC5PhaseTokenRank (compileAdvice q).b
        (w.val + 1) (bankTrialLiveWaveToken B w) := by
    apply bankTrialC5ActualFoldMaxBound
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken B i)))
      0
      (bankTrialC5PhaseTokenRank (compileAdvice q).b
        (w.val + 1) (bankTrialLiveWaveToken B w))
      (Nat.zero_le _)
    intro item hmem
    obtain ⟨i, hi⟩ := (List.mem_ofFn).1 hmem
    rw [← hi]
    by_cases he : i = w
    · rw [he]
      exact Nat.le_refl _
    · rw [hother i he]
      change 0 ≤
        bankTrialC5PhaseTokenRank (compileAdvice q).b
          (w.val + 1) (bankTrialLiveWaveToken B w)
      exact Nat.zero_le _
  have hlower :
      bankTrialC5PhaseTokenRank (compileAdvice q).b
        (w.val + 1) (bankTrialLiveWaveToken B w) ≤
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken B i))).foldl Nat.max 0 :=
    bankTrialC5ActualFoldMaxMember
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b (i.val + 1)
          (bankTrialLiveWaveToken B i)))
      0 _ ((List.mem_ofFn).2 ⟨w, rfl⟩)
  exact Nat.le_antisymm hupper hlower

/-- On an occupied LIVE wait, the older C.6 token maximum
is the C.5 maximum, with one constant offset in IWAIT and no
offset in CWAIT. All token positions and token kinds are covered. -/
theorem bankTrialC5ActualWaitMaximumOffset {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hworker : ∃ w : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B w ≠ .E) :
    bankTrialDurationWorkerTokenMaximum B =
      bankTrialC5ActualWaveRank B +
        (if bankTrialLiveWaveRootMode B = .IWAIT
         then 2 * (compileAdvice q).b + 2 else 0) := by
  obtain ⟨w, hw⟩ := hworker
  have hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ w → bankTrialLiveWaveToken B i = .E := by
    intro i hi
    exact bankTrialInteriorOldWorkerOthersEmpty B hc w i hw hi
  rw [bankTrialDurationMaximumOfSingleToken B w hother,
    bankTrialC5ActualWaveRankSingleToken B w hother]
  rcases hm with hi | hcomp
  · rw [if_pos hi]
    rcases hc.iwaitTokens w hi with he | hir | hal
    · exact False.elim (hw he)
    · rw [hir]
      change 4 * (compileAdvice q).b + 5 - (w.val + 1) =
        (2 * (compileAdvice q).b + 3 - (w.val + 1)) +
          (2 * (compileAdvice q).b + 2)
      have hb := w.isLt
      omega
    · rw [hal]
      change 2 * (compileAdvice q).b + 3 + (w.val + 1) =
        (1 + (w.val + 1)) + (2 * (compileAdvice q).b + 2)
      omega
  · have hnot : ¬ bankTrialLiveWaveRootMode B = .IWAIT := by
      intro hi
      rw [hcomp] at hi
      cases hi
    rw [if_neg hnot, Nat.add_zero]
    rcases hc.cwaitTokens w hcomp with he | ht
    · exact False.elim (hw he)
    · rcases ht with ht | ht | ht | ht
      · rw [ht]
        rfl
      · rw [ht]
        rfl
      · rw [ht]
        rfl
      · rw [ht]
        rfl

/-- The numerical offset is fixed by the actual origin kind,
and holds on every unresolved first-exit descendant. -/
theorem bankTrialC5ActualFirstExitMaximumOffset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    bankTrialDurationWorkerTokenMaximum z.bank =
      bankTrialC5ActualWaveRank z.bank +
        (if o.increment then 2 * (compileAdvice q).b + 2 else 0) := by
  obtain ⟨⟨begun, hlive⟩, hmode⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hlocked := bankTrialC5ActualFirstExitLocked
    ring root S hlarge hclean x e o ho z hz
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hlocked.1 begun hlive
  have hworker := bankTrialC5ActualFirstExitWorkerPersists
    ring root S hsp hlarge hwidth hclean
    x e o ho z hz hnot
  cases hi : o.increment with
  | true =>
      have hm : bankTrialLiveWaveRootMode z.bank = .IWAIT := by
        simpa only [hi, ↓reduceIte] using hmode
      have h := bankTrialC5ActualWaitMaximumOffset
        z.bank hc (Or.inl hm) hworker
      rw [if_pos hm] at h
      simpa only [hi, ↓reduceIte] using h
  | false =>
      have hm : bankTrialLiveWaveRootMode z.bank = .CWAIT := by
        simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hmode
      have hnotI : ¬ bankTrialLiveWaveRootMode z.bank = .IWAIT := by
        intro h
        rw [hm] at h
        cases h
      have h := bankTrialC5ActualWaitMaximumOffset
        z.bank hc (Or.inr hm) hworker
      rw [if_neg hnotI, Nat.add_zero] at h
      simpa only [hi, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] using h

/-- The phase type of a genuinely active worker is IWAIT or CWAIT. -/
theorem bankTrialC5ActualActiveWaitMode {n q : Nat}
    (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (ha : bankTrialC5ActualWorkerActive o z) :
    bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
    bankTrialLiveWaveRootMode z.bank = .CWAIT := by
  cases hi : o.increment with
  | true =>
      apply Or.inl
      simpa only [hi, ↓reduceIte] using ha.2
  | false =>
      apply Or.inr
      simpa only [hi, Bool.false_eq_true, ↓reduceIte] using ha.2

theorem bankTrialC5ActualFirstExitWaitRankTransfer {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (f : Fin n) (d : Nat)
    (haNext : bankTrialC5ActualWorkerActive o
      (bankTrialLocalNext ring root z f))
    (hcost :
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root z f) + d ≤
      bankTrialDurationLeaseAwareWorkerRemaining z) :
    bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z f).bank + d ≤
      bankTrialC5ActualWaveRank z.bank := by
  have hzNext :
      BankTrialC5ActualFirstExitReachable ring root o
        (bankTrialLocalNext ring root z f) :=
    BankTrialC5ActualFirstExitReachable.advance z hz hnot f
  have hnotNext :
      ¬ (bankTrialC5ActualReturned o
            (bankTrialLocalNext ring root z f) ∨
         bankTrialC5ActualBadExit o
            (bankTrialLocalNext ring root z f)) := by
    intro h
    rcases h with hr | hb
    · exact (bankTrialC5ActualActiveNotReturned
        o _ haNext) hr
    · exact (bankTrialC5ActualActiveNotBadExit
        o _ haNext) hb
  have hmaxOld := bankTrialC5ActualFirstExitMaximumOffset
    ring root S hsp hlarge hwidth hclean x e o ho z hz hnot
  have hmaxNew := bankTrialC5ActualFirstExitMaximumOffset
    ring root S hsp hlarge hwidth hclean
    x e o ho (bankTrialLocalNext ring root z f) hzNext hnotNext
  have hinvOld := bankTrialC5ActualFirstExitOrphanInvariant
    ring root S hsp hlarge hwidth hclean x e o ho z hz
  have hinvNew := bankTrialC5ActualFirstExitOrphanInvariant
    ring root S hsp hlarge hwidth hclean
    x e o ho (bankTrialLocalNext ring root z f) hzNext
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hmodeOld := bankTrialC5ActualActiveWaitMode
    o z (bankTrialC5ActualUnresolvedIsActive o z hnot)
  have hpositiveOld :=
    bankTrialDurationNoOrphanOfInv z hinvOld begun hlive hmodeOld
  have hcanonicalOld :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  have hremOld :
      bankTrialDurationLeaseAwareWorkerRemaining z =
      bankTrialDurationWorkerTokenMaximum z.bank := by
    rw [hcanonicalOld]
    exact bankTrialDurationLeaseAwareWaitWorkerExact
      z.bank begun hmodeOld hpositiveOld
  have hmodeNew := bankTrialC5ActualActiveWaitMode
    o (bankTrialLocalNext ring root z f) haNext
  obtain ⟨⟨nextBegun, hliveNext⟩, _⟩ := haNext
  have hpositiveNew :=
    bankTrialDurationNoOrphanOfInv
      (bankTrialLocalNext ring root z f)
      hinvNew nextBegun hliveNext hmodeNew
  have hcanonicalNew :
      bankTrialLocalNext ring root z f =
        (⟨(bankTrialLocalNext ring root z f).bank,
          .live nextBegun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta
      (bankTrialLocalNext ring root z f) nextBegun hliveNext
  have hremNew :
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root z f) =
      bankTrialDurationWorkerTokenMaximum
        (bankTrialLocalNext ring root z f).bank := by
    rw [hcanonicalNew]
    exact bankTrialDurationLeaseAwareWaitWorkerExact
      (bankTrialLocalNext ring root z f).bank
      nextBegun hmodeNew hpositiveNew
  rw [hremNew, hremOld, hmaxNew, hmaxOld] at hcost
  omega

/-- Proper interior edges are neither the outgoing nor the
incoming root edge in the nonaliased window. -/
theorem bankTrialC5ActualInteriorNonincident {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    Counter.site ring root j.val ≠ root ∧
    ring.rightNeighbor (Counter.site ring root j.val) ≠ root := by
  constructor
  · exact bankTrialWindowInteriorNotRoot ring root hw j hj
  · intro h
    have hsite : Counter.site ring root (j.val + 1) =
        Counter.site ring root 0 := by
      change Counter.site ring root (j.val + 1) =
        Counter.site ring root 0 at h
      exact h
    have hdistinct := bankTrialWindowSitesDistinct
      ring root hw (j.val + 1) 0 (by omega) (by omega) hsite
    omega

/-- Proper interior services preserve the actual origin's ACTIVE
status, even if they update the unique worker. -/
theorem bankTrialC5ActualFirstExitInteriorActiveNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialC5ActualWorkerActive o
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)) := by
  obtain ⟨⟨begun, hlive⟩, hmode⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun
      (hword.trans hcanonical)
  have hactive :
      bankTrialC5ActualWorkerActive o
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    rw [← hcanonical]
    exact ⟨⟨begun, hlive⟩, hmode⟩
  have hnonincident := bankTrialC5ActualInteriorNonincident
    ring root (bankTrialProbabilityUpperWindow hlarge) j hj
  have hnext := bankTrialC5ActualNonincidentActiveNext
    ring root (Counter.site ring root j.val)
    z.bank begun o hf hactive hnonincident.1 hnonincident.2
  rw [← hcanonical] at hnext
  exact hnext

theorem bankTrialC5ActualFirstExitInteriorRankNonincrease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)).bank ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun
      (hword.trans hcanonical)
  have hinv := bankTrialC5ActualFirstExitOrphanInvariant
    ring root S hsp hlarge hwidth hclean x e o ho z hz
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hinv.locked.1 begun hlive
  have hwait := bankTrialC5ActualActiveWaitMode
    o z (bankTrialC5ActualUnresolvedIsActive o z hnot)
  have hpositive :=
    bankTrialDurationNoOrphanOfInv z hinv begun hlive hwait
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hweakCanonical :=
    Nat.le_trans
      (bankTrialDurationLeaseAwareNextLeLiveReference
        ring root (Counter.site ring root j.val) z.bank begun)
      (bankTrialDurationReferenceInteriorWaitWeak
        ring root hw z.bank begun hf hc hwait hpositive j hj)
  have hweak :
      bankTrialDurationLeaseAwareWorkerRemaining
          (bankTrialLocalNext ring root z
            (Counter.site ring root j.val)) ≤
        bankTrialDurationLeaseAwareWorkerRemaining z := by
    rw [← hcanonical] at hweakCanonical
    exact hweakCanonical
  have hactiveNew :=
    bankTrialC5ActualFirstExitInteriorActiveNext
      ring root S hlarge hclean x e o ho z hz hnot j hj
  exact bankTrialC5ActualFirstExitWaitRankTransfer
    ring root S hsp hlarge hwidth hclean
    x e o ho z hz hnot
    (Counter.site ring root j.val) 0 hactiveNew
    (by simpa only [Nat.add_zero] using hweak)

/-- The existing four selected IR/AL/CR/CL interior physical
owner rows give a strict nominated edge for the small C.5 rank. -/
theorem bankTrialC5ActualFirstExitInteriorSelectedStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hselected : BankTrialDurationSelectedInteriorCondition z.bank j) :
    bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)).bank + 1 ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun
      (hword.trans hcanonical)
  have hinv := bankTrialC5ActualFirstExitOrphanInvariant
    ring root S hsp hlarge hwidth hclean x e o ho z hz
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hinv.locked.1 begun hlive
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hstrictCanonical :
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root
          (⟨z.bank, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    unfold BankTrialDurationSelectedInteriorCondition at hselected
    rcases hselected with hi | hcomp
    · obtain ⟨hm, hcase⟩ := hi
      rcases hcase with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
      · exact bankTrialDurationSelectedIRLeaseAwareDrop
          ring root hw z.bank begun hf hc hm j hj hsrc hdst
      · exact bankTrialDurationSelectedALLeaseAwareDrop
          ring root hw z.bank begun hf hc hm j hj hsrc hdst
    · obtain ⟨hm, hcase⟩ := hcomp
      rcases hcase with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
      · exact bankTrialDurationSelectedCRLeaseAwareDrop
          ring root hw z.bank begun hf hc hm j hj hsrc hdst
      · exact bankTrialDurationSelectedCLLeaseAwareDrop
          ring root hw z.bank begun hf hc hm j hj hsrc hdst
  have hstrict :
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining z := by
    rw [← hcanonical] at hstrictCanonical
    exact hstrictCanonical
  have hactiveNew :=
    bankTrialC5ActualFirstExitInteriorActiveNext
      ring root S hlarge hclean x e o ho z hz hnot j hj
  exact bankTrialC5ActualFirstExitWaitRankTransfer
    ring root S hsp hlarge hwidth hclean
    x e o ho z hz hnot
    (Counter.site ring root j.val) 1 hactiveNew hstrict
/-- Every scheduler letter has weak C.5 wave-rank monotonicity
before the first exit: root from an earlier theorem, proper interior from
the C.6 transfer, and top/incoming/outside from their frames. -/
theorem bankTrialC5ActualFirstExitAllEdgesRankNonincrease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    ∀ f : Fin n,
      bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z f).bank ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun
      (hword.trans hcanonical)
  have hbank : ∀ f : Fin n,
      (bankTrialLocalNext ring root z f).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank f := by
    intro f
    rw [hcanonical]
    exact bankTrialLocalNextLiveBank ring root f z.bank begun
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  intro f
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root f with hsite | hin | hout
  · obtain ⟨j, hj, he⟩ := hsite
    by_cases htop : j = (compileAdvice q).b
    · subst j
      rw [he, hbank]
      have hnoIR := bankTrialC5ActualFirstExitNoTopIR
        ring root S hsp hlarge hwidth hclean
        x e o ho z hz hnot
      rw [bankTrialC5ActualTopWaveRankFrame
        ring root hw z.bank hf hnoIR]
      exact Nat.le_refl _
    · by_cases hroot : j = 0
      · subst j
        change f = root at he
        rw [he]
        exact bankTrialC5ActualFirstExitRootRankNonincrease
          ring root S hlarge hclean x e o ho z hz hnot
      · have hjlt : j < (compileAdvice q).b := by omega
        have hjpos : 0 < j := Nat.pos_of_ne_zero hroot
        rw [he]
        exact bankTrialC5ActualFirstExitInteriorRankNonincrease
          ring root S hsp hlarge hwidth hclean
          x e o ho z hz hnot ⟨j, hjlt⟩ hjpos
  · rw [hbank]
    rw [bankTrialC5ActualIncomingWaveRankFrame
      ring root f hw z.bank hf hin]
    exact Nat.le_refl _
  · have houtside : ¬ Counter.Support q ring root f := by
      intro hs
      rcases hs with hinc | ⟨j, hj, he⟩
      · have hp := (hout 0 (by omega)).2
        change ring.rightNeighbor f ≠ root at hp
        exact hp hinc
      · exact (hout j hj).1 he
    rw [hbank]
    rw [bankTrialC5ActualOutsideWaveRankFrame
      ring root f z.bank houtside]
    exact Nat.le_refl _
theorem bankTrialC5ActualWaveRankEmptyTokens {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hempty : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B i = .E) :
    bankTrialC5ActualWaveRank B = 0 := by
  have hupper : bankTrialC5ActualWaveRank B ≤ 0 := by
    unfold bankTrialC5ActualWaveRank
    apply bankTrialC5ActualFoldMaxBound
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        bankTrialC5PhaseTokenRank (compileAdvice q).b
          (i.val + 1) (bankTrialLiveWaveToken B i)))
      0 0 (Nat.le_refl 0)
    intro item hmem
    obtain ⟨i, hi⟩ := (List.mem_ofFn).1 hmem
    rw [← hi, hempty i]
    exact Nat.le_refl _
  omega

/-- A returning AL, CL0 or CL1 digit-one token is consumed by
the literal wait-mode root outgoing owner; root lease expiry
does not affect this token clearing. -/
theorem bankTrialC5ActualRawWaitReturnClearsFirst
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0)
    (hy : y.role = 1) (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (ht : y.tok = .AL ∨ y.tok = .CL0 ∨ y.tok = .CL1) :
    (bankPair x y 1 b theta).2.tok = .E := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hm with hm | hm
  · rcases ht with ht | ht | ht
    all_goals by_cases hl : 1 < x.lease
    all_goals simp [bankPair, hx, hy, hg, hm, ht, hl,
      hbpos, hbne, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  · rcases ht with ht | ht | ht
    all_goals by_cases hl : 1 < x.lease
    all_goals simp [bankPair, hx, hy, hg, hm, ht, hl,
      hbpos, hbne, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]

theorem bankTrialC5ActualFirstExitRootReturnStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (ht : bankTrialLiveWaveToken z.bank
        ⟨0, bankTrialWindowWidthPos q⟩ = .AL ∨
      bankTrialLiveWaveToken z.bank
        ⟨0, bankTrialWindowWidthPos q⟩ = .CL0 ∨
      bankTrialLiveWaveToken z.bank
        ⟨0, bankTrialWindowWidthPos q⟩ = .CL1) :
    bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z root).bank + 1 ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun
      (hword.trans hcanonical)
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hlocked := bankTrialC5ActualFirstExitLocked
    ring root S hlarge hclean x e o ho z hz
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hlocked.1 begun hlive
  have hwait := bankTrialC5ActualActiveWaitMode
    o z (bankTrialC5ActualUnresolvedIsActive o z hnot)
  have hnotEmpty :
      bankTrialLiveWaveToken z.bank
        ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
    rcases ht with h | h | h <;>
      rw [h] <;> intro he <;> cases he
  have hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken z.bank i = .E := by
    intro i hi
    exact bankTrialInteriorOldWorkerOthersEmpty z.bank hc
      ⟨0, bankTrialWindowWidthPos q⟩ i hnotEmpty hi
  have hbank :
      (bankTrialLocalNext ring root z root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root := by
    rw [hcanonical]
    exact bankTrialLocalNextLiveBank ring root root z.bank begun
  have hproj := (bankTrialCmpRoot ring root hw z.bank hf).2
  have hb : 1 < (compileAdvice q).b := by
    have hwidth := bankTrialCmpWidth q
    omega
  have hraw :
      (GrantBankReference.bankLocalReferenceInternalPair q
        z.bank ⟨0, bankTrialWindowWidthPos q⟩).2.tok = .E := by
    change (bankPair
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, show 0 < (compileAdvice q).b + 1 by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by have hwidth := bankTrialCmpWidth q; omega⟩)
      1 (compileAdvice q).b (compileAdvice q).theta).2.tok = .E
    exact bankTrialC5ActualRawWaitReturnClearsFirst
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨0, show 0 < (compileAdvice q).b + 1 by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨1, by have hwidth := bankTrialCmpWidth q; omega⟩)
      hb rfl rfl rfl hwait ht
  have hempty : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root z root).bank i = .E := by
    intro i
    rw [hbank]
    by_cases hi : i = ⟨0, bankTrialWindowWidthPos q⟩
    · rw [hi]
      exact ((hproj ⟨0, bankTrialWindowWidthPos q⟩).1 rfl).2.trans
        hraw
    · have hiv : i.val ≠ 0 := by
        intro hzero
        exact hi (Fin.ext hzero)
      exact ((hproj i).2 hiv).2.trans (hother i hi)
  have hzero : bankTrialC5ActualWaveRank
      (bankTrialLocalNext ring root z root).bank = 0 :=
    bankTrialC5ActualWaveRankEmptyTokens _ hempty
  have hold : 0 < bankTrialC5ActualWaveRank z.bank := by
    rw [bankTrialC5ActualWaveRankSingleToken z.bank
      ⟨0, bankTrialWindowWidthPos q⟩ hother]
    rcases ht with ht | ht | ht
    · rw [ht]
      simp [bankTrialC5PhaseTokenRank]
    · rw [ht]
      simp [bankTrialC5PhaseTokenRank]
    · rw [ht]
      simp [bankTrialC5PhaseTokenRank]
  rw [hzero]
  omega

theorem bankTrialC5ActualFirstExitTopComparisonStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z))
    (hmode : bankTrialLiveWaveRootMode z.bank = .CWAIT)
    (hsrc : (z.bank.fields
      ⟨(compileAdvice q).b - 1, by have hb := bankTrialCmpWidth q; omega⟩).2.2.1 =
        .E)
    (hdst :
      (z.bank.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR0 ∨
      (z.bank.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR1) :
    bankTrialC5ActualWaveRank
      (bankTrialLocalNext ring root z
        (Counter.site ring root ((compileAdvice q).b - 1))).bank + 1 ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hcanonical :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta z begun hlive
  obtain ⟨word, hword⟩ :=
    bankTrialC5ActualFirstExitCleanReachable
      ring root S x e o ho z hz
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word z.bank begun
      (hword.trans hcanonical)
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    (bankTrialC5ActualFirstExitLocked
      ring root S hlarge hclean x e o ho z hz).1 begun hlive
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hb : 2 ≤ (compileAdvice q).b := by
    have hh := bankTrialCmpWidth q
    omega
  have hdst' :
      (z.bank.fields
        ⟨(compileAdvice q).b - 1 + 1, by omega⟩).2.2.1 = .CR0 ∨
      (z.bank.fields
        ⟨(compileAdvice q).b - 1 + 1, by omega⟩).2.2.1 = .CR1 := by
    have heq : (⟨(compileAdvice q).b - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨(compileAdvice q).b, by omega⟩ :=
      Fin.ext (show (compileAdvice q).b - 1 + 1 =
        (compileAdvice q).b by omega)
    rw [heq]
    exact hdst
  have hstrictCanonical :=
    bankTrialDurationCWaitTopTurnStrict
      ring root hw z.bank begun hf hc hmode
      ⟨(compileAdvice q).b - 1,
        show (compileAdvice q).b - 1 < (compileAdvice q).b by omega⟩
      (show 0 < (compileAdvice q).b - 1 by omega)
      (show (compileAdvice q).b - 1 + 1 = (compileAdvice q).b by omega)
      hsrc hdst'
  have hstrict :
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root z
          (Counter.site ring root ((compileAdvice q).b - 1))) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining z := by
    rw [← hcanonical] at hstrictCanonical
    exact hstrictCanonical
  have hactiveNew :=
    bankTrialC5ActualFirstExitInteriorActiveNext
      ring root S hlarge hclean x e o ho z hz hnot
      ⟨(compileAdvice q).b - 1,
        show (compileAdvice q).b - 1 < (compileAdvice q).b by omega⟩
      (show 0 < (compileAdvice q).b - 1 by omega)
  exact bankTrialC5ActualFirstExitWaitRankTransfer
    ring root S hsp hlarge hwidth hclean
    x e o ho z hz hnot
    (Counter.site ring root ((compileAdvice q).b - 1))
    1 hactiveNew hstrict
theorem bankTrialC5ActualFirstExitNominatedStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    ∃ f : Fin n,
      bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z f).bank + 1 ≤
      bankTrialC5ActualWaveRank z.bank := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o z hnot
  have hinv := bankTrialC5ActualFirstExitOrphanInvariant
    ring root S hsp hlarge hwidth hclean x e o ho z hz
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hinv.locked.1 begun hlive
  have hmode := bankTrialC5ActualActiveWaitMode
    o z (bankTrialC5ActualUnresolvedIsActive o z hnot)
  obtain ⟨w, hworker⟩ := hinv.workerPresent begun hlive hmode
  rcases hmode with hi | hcomp
  · rcases hc.iwaitTokens w hi with hE | hIR | hAL
    · exact False.elim (hworker hE)
    · by_cases htop : w.val + 1 = (compileAdvice q).b
      · have heq : w =
            ⟨(compileAdvice q).b - 1,
              by have hb := bankTrialCmpWidth q; omega⟩ :=
          Fin.ext (show w.val = (compileAdvice q).b - 1 by omega)
        have hbad : bankTrialLiveWaveToken z.bank
          ⟨(compileAdvice q).b - 1,
            by have hb := bankTrialCmpWidth q; omega⟩ = .IR := by
          rw [← heq]
          exact hIR
        have hnoTop := bankTrialC5ActualFirstExitNoTopIR
          ring root S hsp hlarge hwidth hclean
          x e o ho z hz hnot
        exact False.elim (hnoTop hbad)
      · have hspace : w.val + 1 < (compileAdvice q).b := by
          have hw := w.isLt
          omega
        obtain ⟨j, hj, hsel⟩ :=
          bankTrialDurationForwardWorkerCovered
            z.bank hc w hworker hspace (Or.inl ⟨hi, hIR⟩)
        refine ⟨Counter.site ring root j.val, ?_⟩
        exact bankTrialC5ActualFirstExitInteriorSelectedStrict
          ring root S hsp hlarge hwidth hclean
          x e o ho z hz hnot j hj hsel
    · by_cases hfirst : w.val = 0
      · have heq : w = ⟨0, bankTrialWindowWidthPos q⟩ :=
          Fin.ext hfirst
        have hfirstTok : bankTrialLiveWaveToken z.bank
            ⟨0, bankTrialWindowWidthPos q⟩ = .AL := by
          rw [← heq]
          exact hAL
        refine ⟨root, ?_⟩
        exact bankTrialC5ActualFirstExitRootReturnStrict
          ring root S hlarge hclean x e o ho z hz hnot
          (Or.inl hfirstTok)
      · have hwpos : 0 < w.val := Nat.pos_of_ne_zero hfirst
        obtain ⟨j, hj, hsel⟩ :=
          bankTrialDurationReturnWorkerCovered
            z.bank hc w hworker hwpos (Or.inl ⟨hi, hAL⟩)
        refine ⟨Counter.site ring root j.val, ?_⟩
        exact bankTrialC5ActualFirstExitInteriorSelectedStrict
          ring root S hsp hlarge hwidth hclean
          x e o ho z hz hnot j hj hsel
  · rcases hc.cwaitTokens w hcomp with hE | hkind
    · exact False.elim (hworker hE)
    · have hsplit :
          (bankTrialLiveWaveToken z.bank w = .CR0 ∨
           bankTrialLiveWaveToken z.bank w = .CR1) ∨
          (bankTrialLiveWaveToken z.bank w = .CL0 ∨
           bankTrialLiveWaveToken z.bank w = .CL1) := by
        unfold BankTrialLiveComparisonToken at hkind
        rcases hkind with hzero | hone | hbackZero | hbackOne
        · exact Or.inl (Or.inl hzero)
        · exact Or.inl (Or.inr hone)
        · exact Or.inr (Or.inl hbackZero)
        · exact Or.inr (Or.inr hbackOne)
      rcases hsplit with hCR | hCL
      · by_cases htop : w.val + 1 = (compileAdvice q).b
        · have hb : 2 ≤ (compileAdvice q).b := by
            have hh := bankTrialCmpWidth q
            omega
          have hwpos : 0 < w.val := by omega
          have hprevEmpty :=
            bankTrialDurationInteriorLeftEmptyOfRight
              z.bank hc w hwpos hworker
          have hsrc :
              (z.bank.fields
                ⟨(compileAdvice q).b - 1, by omega⟩).2.2.1 = .E := by
            have hindex :
                w.val - 1 + 1 = (compileAdvice q).b - 1 := by
              omega
            simpa only [bankTrialLiveWaveToken, Fin.val_mk, hindex]
              using hprevEmpty
          have hdst :
              (z.bank.fields
                ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR0 ∨
              (z.bank.fields
                ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR1 := by
            simpa only [bankTrialLiveWaveToken, htop] using hCR
          refine ⟨Counter.site ring root
            ((compileAdvice q).b - 1), ?_⟩
          exact bankTrialC5ActualFirstExitTopComparisonStrict
            ring root S hsp hlarge hwidth hclean
            x e o ho z hz hnot hcomp hsrc hdst
        · have hspace : w.val + 1 < (compileAdvice q).b := by
            have hw := w.isLt
            omega
          obtain ⟨j, hj, hsel⟩ :=
            bankTrialDurationForwardWorkerCovered
              z.bank hc w hworker hspace
              (Or.inr ⟨hcomp, hCR⟩)
          refine ⟨Counter.site ring root j.val, ?_⟩
          exact bankTrialC5ActualFirstExitInteriorSelectedStrict
            ring root S hsp hlarge hwidth hclean
            x e o ho z hz hnot j hj hsel
      · by_cases hfirst : w.val = 0
        · have heq : w = ⟨0, bankTrialWindowWidthPos q⟩ :=
            Fin.ext hfirst
          have hfirstTok :
              bankTrialLiveWaveToken z.bank
                ⟨0, bankTrialWindowWidthPos q⟩ = .CL0 ∨
              bankTrialLiveWaveToken z.bank
                ⟨0, bankTrialWindowWidthPos q⟩ = .CL1 := by
            rw [← heq]
            exact hCL
          refine ⟨root, ?_⟩
          apply bankTrialC5ActualFirstExitRootReturnStrict
            ring root S hlarge hclean x e o ho z hz hnot
          rcases hfirstTok with hzero | hone
          · exact Or.inr (Or.inl hzero)
          · exact Or.inr (Or.inr hone)
        · have hwpos : 0 < w.val := Nat.pos_of_ne_zero hfirst
          obtain ⟨j, hj, hsel⟩ :=
            bankTrialDurationReturnWorkerCovered
              z.bank hc w hworker hwpos
              (Or.inr ⟨hcomp, hCL⟩)
          refine ⟨Counter.site ring root j.val, ?_⟩
          exact bankTrialC5ActualFirstExitInteriorSelectedStrict
            ring root S hsp hlarge hwidth hclean
            x e o ho z hz hnot j hj hsel

/-- Full two-field physical wave row, with all-edge weak rank
and one strictly decreasing selected ORIGINAL scheduler edge. -/
theorem bankTrialC5ActualFirstExitWaveRowsHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5ActualFirstExitWaveRows ring root S := by
  intro x e o ho z hz hnot
  exact ⟨
    bankTrialC5ActualFirstExitAllEdgesRankNonincrease
      ring root S hsp hlarge hwidth hclean
      x e o ho z hz hnot,
    bankTrialC5ActualFirstExitNominatedStrict
      ring root S hsp hlarge hwidth hclean
      x e o ho z hz hnot⟩

/-- Exact boundedMean field of BankTrialC5WorkerExcursionKernel,
with only production hypotheses and actual postservice origins. -/
theorem bankTrialC5ActualBoundedMeanHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (x : BankTrialLocalState q) (e : Fin n)
      (o : BankTrialC5ActualOrigin n q),
      o ∈ bankTrialC5ActualStarts ring root S x e →
      o.after = bankTrialLocalNext ring root x e ∧
      ∀ T : Nat,
        costNumerator (bankTrialLocalNext ring root)
          (fun z => bankTrialC5ActualReturned o z ∨
            bankTrialC5ActualBadExit o z)
          o.after T ≤
          n ^ T * ((2 * (compileAdvice q).b + 2 + 1) * n) := by
  exact bankTrialC5ActualBoundedMeanOfFirstExitWaveRows
    ring root S
    (bankTrialC5ActualFirstExitWaveRowsHolds
      ring root S hsp hlarge hwidth hclean)
end L3



namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The physical C.1 ratio and the C.5 worker ratio
are definitionally identical; there is no constant mismatch. -/
theorem bankTrialC5ActualRarityConstantsAgree (q : Nat) :
    bankTrialProbabilityC5WorkerNumerator q =
      CounterTrialLower.workerTimeoutNumerator (compileAdvice q).b ∧
    bankTrialProbabilityC5WorkerDenominator q =
      CounterTrialLower.workerTimeoutDenominator (compileAdvice q).b := by
  exact ⟨rfl, rfl⟩

/-- Equality of the postservice state, worker kind, and head index
is sufficient for timeout equality. The strict-prefix guard now
inspects the latter two fields through Returned and BadExit. -/
theorem bankTrialC5ActualTimeoutDependsOnlyOnAfter {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o p : BankTrialC5ActualOrigin n q)
    (hpost : o.after = p.after)
    (hinc : o.increment = p.increment)
    (hheads : o.heads = p.heads)
    (word : List (Fin n)) :
    bankTrialC5ActualTimeout ring root o word =
      bankTrialC5ActualTimeout ring root p word := by
  obtain ⟨b1, e1, a1, i1, h1⟩ := o
  obtain ⟨b2, e2, a2, i2, h2⟩ := p
  dsimp only at hpost hinc hheads
  subst hpost hinc hheads
  rfl

/-- Explicit missing bridge to the two physical C.1
theorems. A physical witness must carry the full authenticated,
isolated launch data. More importantly, the WHOLE-SUFFIX
actual timeout mass must be dominated by the corresponding
FIRST-EXIT physical timeout mass at every finite horizon.

This uses the same Fin n scheduler and makes no claim that the
bridge follows from CLEAN BANK reachability. The bridge is
strictly a comparison of two finite-word sums, not an axiom. -/
def BankTrialC5ActualPhysicalWatchdogMassBridge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q),
    o ∈ bankTrialC5ActualStarts ring root S x e →
      (∃ p : CounterTrialLower.PrivateIncrementBoundedOrigin
          (q := q) ring root,
        ∀ T : Nat,
          Prob.scheduleSum n T
            (fun w => Prob.indicator
              (bankTrialC5ActualTimeout ring root o w)) ≤
          Prob.scheduleSum n T
            (fun w => Prob.indicator
              (CounterTrialLower.privateIncrementBoundedTimeout
                ring root p w))) ∨
      (∃ p : CounterTrialLower.PrivateComparatorBoundedOrigin
          (q := q) ring root,
        ∀ T : Nat,
          Prob.scheduleSum n T
            (fun w => Prob.indicator
              (bankTrialC5ActualTimeout ring root o w)) ≤
          Prob.scheduleSum n T
            (fun w => Prob.indicator
              (CounterTrialLower.privateComparatorBoundedTimeout
                ring root p w)))

/-- The exact missing rarity field follows from the mass adapter
and the already-proved physical IWAIT/CWAIT C.1 bounds. Neither
the event numerator nor its denominator is weakened or changed. -/
theorem bankTrialC5ActualConditionalRarityOfPhysicalMassBridge
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hbridge : BankTrialC5ActualPhysicalWatchdogMassBridge
      ring root S) :
    BankTrialProbabilityC5WorkerRarity
      ring root
      (bankTrialC5ActualStarts ring root S)
      (bankTrialC5ActualTimeout ring root) := by
  unfold BankTrialProbabilityC5WorkerRarity Prob.OriginRarity
  intro x hnonterminal e o ho T
  have hconstants := bankTrialC5ActualRarityConstantsAgree q
  rcases hbridge x e o ho with ⟨p, hdom⟩ | ⟨p, hdom⟩
  · have hphysical :=
      (CounterTrialLower.privateIncrementBoundedRarityPhysical
        ring root hsp hwidth) hlarge p T
    rw [hconstants.1, hconstants.2]
    exact Nat.le_trans
      (Nat.mul_le_mul_left
        (CounterTrialLower.workerTimeoutDenominator
          (compileAdvice q).b) (hdom T))
      hphysical
  · have hphysical :=
      (CounterTrialLower.privateComparatorBoundedRarityPhysical
        ring root hsp hwidth) hlarge p T
    rw [hconstants.1, hconstants.2]
    exact Nat.le_trans
      (Nat.mul_le_mul_left
        (CounterTrialLower.workerTimeoutDenominator
          (compileAdvice q).b) (hdom T))
      hphysical

/-- The other four kernel fields are proved at the actual
origin data. Once the ONE exact OriginRarity field is supplied,
the complete five-field kernel is constructor assembly. -/
theorem bankTrialC5ActualWorkerExcursionKernelOfRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hrare : BankTrialProbabilityC5WorkerRarity
      ring root
      (bankTrialC5ActualStarts ring root S)
      (bankTrialC5ActualTimeout ring root)) :
    BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o : BankTrialC5ActualOrigin n q => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o : BankTrialC5ActualOrigin n q =>
        o.increment)
      (heads := fun o : BankTrialC5ActualOrigin n q => o.heads)
      ring root S := by
  refine {
    boundedMean := ?_,
    nonreturnBad := ?_,
    goodReturn := ?_,
    conditionalRarity := ?_,
    coverage := ?_
  }
  · exact bankTrialC5ActualBoundedMeanHolds
      ring root S hsp hlarge hwidth hclean
  · exact bankTrialC5ActualNonreturnBadHolds
      ring root S hsp hlarge hwidth hclean
  · exact bankTrialC5ActualGoodReturnHolds
      ring root S hsp hlarge hwidth hclean
  · exact hrare
  · exact bankTrialC5ActualCoverageHolds
      ring root S hsp hlarge hwidth

/-- A full actual-data kernel conditional ONLY on the explicit
local-to-physical WHOLE-SUFFIX mass adapter; this is not the
unconditional kernel theorem. -/
theorem bankTrialC5ActualWorkerExcursionKernelOfPhysicalMassBridge
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hbridge : BankTrialC5ActualPhysicalWatchdogMassBridge
      ring root S) :
    BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o : BankTrialC5ActualOrigin n q => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o : BankTrialC5ActualOrigin n q =>
        o.increment)
      (heads := fun o : BankTrialC5ActualOrigin n q => o.heads)
      ring root S := by
  exact bankTrialC5ActualWorkerExcursionKernelOfRarity
    ring root S hsp hlarge hwidth hclean
    (bankTrialC5ActualConditionalRarityOfPhysicalMassBridge
      ring root S hsp hlarge hwidth hbridge)

end L3


namespace L3

open Classical

/-- A true actual timeout carries a witness with no classified
return or bad exit on any strict prefix of its pre-service word.
This exposes the repaired guard without unfolding it downstream. -/
theorem bankTrialC5ActualTimeoutHasStrictPrefixGuard {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (word : List (Fin n))
    (h : bankTrialC5ActualTimeout ring root o word = true) :
    ∃ pre tail : List (Fin n), ∃ e : Fin n,
      word = pre ++ (e :: tail) ∧
      (∀ before middle : List (Fin n), ∀ f : Fin n,
        pre = before ++ (f :: middle) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root before o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root before o.after))) := by
  unfold bankTrialC5ActualTimeout at h
  obtain ⟨pre, tail, e, hword, hstrict, _, _, _, _, _, _⟩ :=
    of_decide_eq_true h
  exact ⟨pre, tail, e, hword, hstrict⟩

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Choose a genuinely decreasing original-scheduler edge whenever one
exists. The default is relevant only outside a live worker's pre-exit
states. The selection uses no physical Counter.Config origin. -/
noncomputable def bankTrialC5ActualNominatedEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) : Fin n :=
  if h : ∃ f : Fin n,
      bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z f).bank + 1 ≤
      bankTrialC5ActualWaveRank z.bank
  then Classical.choose h
  else root

/-- Any existing strict wave-rank decrease is selected. -/
theorem bankTrialC5ActualNominatedEdgeDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (h : ∃ f : Fin n,
      bankTrialC5ActualWaveRank
        (bankTrialLocalNext ring root z f).bank + 1 ≤
      bankTrialC5ActualWaveRank z.bank) :
    bankTrialC5ActualWaveRank
      (bankTrialLocalNext ring root z
        (bankTrialC5ActualNominatedEdge ring root z)).bank + 1 ≤
    bankTrialC5ActualWaveRank z.bank := by
  unfold bankTrialC5ActualNominatedEdge
  split
  · rename_i hex
    exact Classical.choose_spec hex
  · rename_i hn
    exact False.elim (hn h)

/-- A concrete designated-edge rank drop for every actual emitted
origin and every unresolved first-exit-reachable BANK state. -/
theorem bankTrialC5ActualNominatedFirstExitDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (z : BankTrialLocalState q)
    (hz : BankTrialC5ActualFirstExitReachable ring root o z)
    (hnot : ¬ (bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z)) :
    bankTrialC5ActualWaveRank
      (bankTrialLocalNext ring root z
        (bankTrialC5ActualNominatedEdge ring root z)).bank + 1 ≤
    bankTrialC5ActualWaveRank z.bank := by
  have hrows := bankTrialC5ActualFirstExitWaveRowsHolds
    ring root S hsp hlarge hwidth hclean
  exact bankTrialC5ActualNominatedEdgeDrop ring root z
    (hrows x e o ho z hz hnot).2

/-- A root-incident letter that is NOT the nominated productive
letter. The disjointness in the moment theorem is built into this
predicate, even for states outside the first-exit reachable class. -/
def bankTrialC5ActualPenaltyEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (e : Fin n) : Prop :=
  (e = root ∨ ring.rightNeighbor e = root) ∧
  e ≠ bankTrialC5ActualNominatedEdge ring root z

theorem bankTrialC5ActualPenaltyDisjoint {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ z : BankTrialLocalState q,
      ¬ bankTrialC5ActualPenaltyEdge ring root z
        (bankTrialC5ActualNominatedEdge ring root z) := by
  intro z hp
  exact hp.2 rfl

private theorem bankTrialC5ActualLeftAfterRight {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  change (((i.val + 1) % n + n - 1) % n) = i.val
  have heq :
      (i.val + 1) % n + n - 1 =
        (i.val + 1) % n + (n - 1) := by
    have hn := ring.hn
    omega
  rw [heq, Nat.mod_add_mod]
  have heq' : i.val + 1 + (n - 1) = i.val + n := by
    have hn := ring.hn
    omega
  rw [heq', Nat.add_mod]
  simp [Nat.mod_eq_of_lt i.isLt]

private theorem bankTrialC5ActualSpikeMass {n : Nat}
    (a : Fin n) (v : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then v else 0)).sum = v := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
      cases a using Fin.cases with
      | zero =>
          have hz : ∀ m : Nat,
              (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0 := by
            intro m
            induction m with
            | zero => rfl
            | succ m ihm =>
                rw [List.ofFn_succ, List.sum_cons, ihm]
          have hf : (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0) =
              fun _ => 0 :=
            funext fun i => if_neg (Fin.succ_ne_zero i)
          simp only [List.ofFn_succ, List.sum_cons]
          rw [hf, hz]
          simp
      | succ a =>
          have hf : (fun i : Fin n =>
              if i.succ = a.succ then v else 0) =
              fun i => if i = a then v else 0 :=
            funext fun i => by simp only [Fin.succ_inj]
          simp only [List.ofFn_succ, List.sum_cons]
          rw [hf, ih a, if_neg (Fin.succ_ne_zero a).symm,
            Nat.zero_add]

/-- At every BANK state there are at most two possible penalty edges,
including at the exceptional cuts where the two ports might alias.
This is the other ALL-STATES premise of adaptedWorkerPenaltyTail. -/
theorem bankTrialC5ActualPenaltyCardinality {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ z : BankTrialLocalState q,
      (List.ofFn (fun e : Fin n =>
        if bankTrialC5ActualPenaltyEdge ring root z e
        then 1 else 0)).sum ≤ 2 := by
  intro z
  have hpoint (e : Fin n) :
      (if bankTrialC5ActualPenaltyEdge ring root z e
       then 1 else 0) ≤
        (if e = root then 1 else 0) +
        (if e = ring.leftNeighbor root then 1 else 0) := by
    by_cases hp : bankTrialC5ActualPenaltyEdge ring root z e
    · simp only [if_pos hp]
      rcases hp.1 with hr | hi
      · subst e
        simp
      · have hl : e = ring.leftNeighbor root := by
          calc
            e = ring.leftNeighbor (ring.rightNeighbor e) :=
              (bankTrialC5ActualLeftAfterRight ring e).symm
            _ = ring.leftNeighbor root :=
              congrArg ring.leftNeighbor hi
        rw [hl]
        simp
    · simp only [if_neg hp]
      exact Nat.zero_le _
  calc
    (List.ofFn (fun e : Fin n =>
        if bankTrialC5ActualPenaltyEdge ring root z e
        then 1 else 0)).sum ≤
      (List.ofFn (fun e : Fin n =>
        (if e = root then 1 else 0) +
        (if e = ring.leftNeighbor root then 1 else 0))).sum :=
        ofFn_sum_le _ _ hpoint
    _ = 1 + 1 := by
      rw [ofFn_sum_add,
        bankTrialC5ActualSpikeMass root 1,
        bankTrialC5ActualSpikeMass (ring.leftNeighbor root) 1]
    _ = 2 := rfl

/-- Exact BANK-local instantiation of the existing generic two-port
adapted penalty-tail bound, on the ORIGINAL Fin n schedule. This
part needs no source-level lease or head-count hypothesis. -/
theorem bankTrialC5ActualBankPenaltyTail {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (T : Nat) :
    CounterTrialLower.workerTimeoutDenominator (compileAdvice q).b *
      CounterTrialLower.workerPenaltyTailMass
        (bankTrialLocalNext ring root)
        (bankTrialC5ActualNominatedEdge ring root)
        (bankTrialC5ActualPenaltyEdge ring root)
        z (2 * (compileAdvice q).b + 2)
          (11 * (compileAdvice q).b + 24) T ≤
    CounterTrialLower.workerTimeoutNumerator (compileAdvice q).b *
      n ^ T := by
  exact CounterTrialLower.adaptedWorkerTimeoutNumerator
    (bankTrialLocalNext ring root)
    (bankTrialC5ActualNominatedEdge ring root)
    (bankTrialC5ActualPenaltyEdge ring root)
    (bankTrialC5ActualPenaltyDisjoint ring root)
    (bankTrialC5ActualPenaltyCardinality ring root)
    z (compileAdvice q).b T

/-- The remaining pathwise BANK assertion. Its word is the exact
postservice local observer run; timeout has the installed strict
first-exit prefix guard. No Counter.Config origin occurs here. -/
def BankTrialC5ActualTimeoutPenaltyCover {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q),
    o ∈ bankTrialC5ActualStarts ring root S x e →
    ∀ w : List (Fin n),
      bankTrialC5ActualTimeout ring root o w = true →
      11 * (compileAdvice q).b + 24 ≤
        CounterTrialLower.workerPenaltyCount
          (bankTrialLocalNext ring root)
          (bankTrialC5ActualNominatedEdge ring root)
          (bankTrialC5ActualPenaltyEdge ring root)
          o.after (2 * (compileAdvice q).b + 2) w

/-- This is the required opaque-Nat lease-margin arithmetic;
the remaining unproved BANK step is the antecedent that a
timeout spends at least the launch lease on the two incident
edges, with at most L nominated productive hits. -/
theorem bankTrialC5ActualLeaseMargin
    (b counted nominated : Nat)
    (hspent : 13 * (b + 2) ≤ counted + nominated)
    (hbudget : nominated ≤ 2 * b + 2) :
    11 * b + 24 ≤ counted := by
  omega

/-- The two finite-word scheduler-sum implementations agree.
The generic penalty bound is phrased with resetColdWordSum, while
the C.5 rarity field is phrased with Prob.scheduleSum. -/
private theorem bankTrialC5ActualScheduleSumEq {n : Nat}
    (T : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n T f =
      Counter.resetColdWordSum n T f := by
  induction T generalizing f with
  | zero =>
      simp [Prob.scheduleSum,
        FixedSpanRenewalPayload.wordSum, allSchedules,
        Counter.resetColdWordSum]
  | succ T ih =>
      change FixedSpanRenewalPayload.wordSum n (T + 1) f =
        Counter.resetColdWordSum n (T + 1) f
      rw [FixedSpanRenewalPayload.wordSum_succ]
      change
        (List.ofFn (fun e : Fin n =>
          FixedSpanRenewalPayload.wordSum n T
            (fun w => f (e :: w)))).sum =
        (List.ofFn (fun e : Fin n =>
          Counter.resetColdWordSum n T
            (fun w => f (e :: w)))).sum
      exact ofFn_sum_eq _ _ (fun e => ih (fun w => f (e :: w)))

/-- A direct, NON-PHYSICAL-ORIGIN reduction of conditionalRarity to
the one missing pathwise BANK lease-payment property. In particular,
the entire exponential-moment estimate is already discharged. -/
theorem bankTrialC5ActualConditionalRarityOfPenaltyCover
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hcover : BankTrialC5ActualTimeoutPenaltyCover ring root S) :
    BankTrialProbabilityC5WorkerRarity
      ring root
      (bankTrialC5ActualStarts ring root S)
      (bankTrialC5ActualTimeout ring root) := by
  unfold BankTrialProbabilityC5WorkerRarity Prob.OriginRarity
  intro x hnonterminal e o ho T
  have hpoint (w : List (Fin n)) :
      Prob.indicator (bankTrialC5ActualTimeout ring root o w) ≤
      (if 11 * (compileAdvice q).b + 24 ≤
        CounterTrialLower.workerPenaltyCount
          (bankTrialLocalNext ring root)
          (bankTrialC5ActualNominatedEdge ring root)
          (bankTrialC5ActualPenaltyEdge ring root)
          o.after (2 * (compileAdvice q).b + 2) w
       then 1 else 0) := by
    cases ht : bankTrialC5ActualTimeout ring root o w with
    | false =>
        simp [Prob.indicator, ht]
    | true =>
        have hc := hcover x e o ho w ht
        simp [Prob.indicator, ht, hc]
  have hsum :
      Prob.scheduleSum n T (fun w =>
        Prob.indicator (bankTrialC5ActualTimeout ring root o w)) ≤
      CounterTrialLower.workerPenaltyTailMass
        (bankTrialLocalNext ring root)
        (bankTrialC5ActualNominatedEdge ring root)
        (bankTrialC5ActualPenaltyEdge ring root)
        o.after (2 * (compileAdvice q).b + 2)
          (11 * (compileAdvice q).b + 24) T := by
    calc
      Prob.scheduleSum n T (fun w =>
          Prob.indicator (bankTrialC5ActualTimeout ring root o w)) ≤
        Prob.scheduleSum n T (fun w =>
          if 11 * (compileAdvice q).b + 24 ≤
            CounterTrialLower.workerPenaltyCount
              (bankTrialLocalNext ring root)
              (bankTrialC5ActualNominatedEdge ring root)
              (bankTrialC5ActualPenaltyEdge ring root)
              o.after (2 * (compileAdvice q).b + 2) w
          then 1 else 0) :=
            bankTrialProbabilityScheduleSumMono n T _ _ hpoint
      _ = CounterTrialLower.workerPenaltyTailMass
          (bankTrialLocalNext ring root)
          (bankTrialC5ActualNominatedEdge ring root)
          (bankTrialC5ActualPenaltyEdge ring root)
          o.after (2 * (compileAdvice q).b + 2)
            (11 * (compileAdvice q).b + 24) T := by
        rw [bankTrialC5ActualScheduleSumEq]
        rfl
  have hconstants := bankTrialC5ActualRarityConstantsAgree q
  rw [hconstants.1, hconstants.2]
  exact Nat.le_trans
    (Nat.mul_le_mul_left
      (CounterTrialLower.workerTimeoutDenominator
        (compileAdvice q).b) hsum)
    (bankTrialC5ActualBankPenaltyTail ring root o.after T)

/-- Once the explicit BANK-first-exit pathwise cover is proved, the
remaining kernel fields assemble using the already compiled theorem.
There is NO new unconditional rarity claim in this declaration. -/
theorem bankTrialC5ActualWorkerExcursionKernelOfPenaltyCover
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hcover : BankTrialC5ActualTimeoutPenaltyCover ring root S) :
    BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o : BankTrialC5ActualOrigin n q => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o : BankTrialC5ActualOrigin n q =>
        o.increment)
      (heads := fun o : BankTrialC5ActualOrigin n q => o.heads)
      ring root S := by
  exact bankTrialC5ActualWorkerExcursionKernelOfRarity
    ring root S hsp hlarge hwidth hclean
    (bankTrialC5ActualConditionalRarityOfPenaltyCover
      ring root S hcover)

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Exact source-level ARMED/IR lease launch. The old first digit
is empty; an IWAIT successor forces the first old bit to be true. -/
private theorem bankTrialC5ActualRawArmedLaunchLease
    (b : Nat) (theta : Nat → Bool) (a d : BankCell)
    (hb : 1 ≤ b) (ha : a.role = 0) (hd : d.role = 1)
    (hg : a.grant = false) (hm : a.mode = .ARMED)
    (ht : d.tok = .E)
    (hnew : (bankPair a d 1 b theta).1.mode = .IWAIT) :
    (bankPair a d 1 b theta).1.lease = 13 * (b + 2) := by
  cases hbit : d.bit with
  | false =>
      have hc : (bankPair a d 1 b theta).1.mode = .CSTART := by
        simp [bankPair, ha, hd, hg, hm, ht, hbit, hb,
          isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
      rw [hc] at hnew
      cases hnew
  | true =>
      simp [bankPair, ha, hd, hg, hm, ht, hbit, hb,
        isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- Exact source-level CSTART/CR lease launch. -/
private theorem bankTrialC5ActualRawComparatorLaunchLease
    (b : Nat) (theta : Nat → Bool) (a d : BankCell)
    (hb : 1 ≤ b) (ha : a.role = 0) (hd : d.role = 1)
    (hg : a.grant = false) (hm : a.mode = .CSTART)
    (ht : d.tok = .E) :
    (bankPair a d 1 b theta).1.lease = 13 * (b + 2) := by
  simp [bankPair, ha, hd, hg, hm, ht, hb,
    isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- The actual root lease is the numeric fourth field of the
clamped BANK observer. -/
def bankTrialC5ActualRootLease {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  (z.bank.fields ⟨0, by omega⟩).2.2.2

/-- L1: BOTH kinds of emitted actual worker launch with the
full BANK lease, not merely a bounded or positive one. -/
theorem bankTrialC5ActualLaunchLeaseHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    bankTrialC5ActualRootLease o.after =
      13 * ((compileAdvice q).b + 2) := by
  obtain ⟨_, ⟨pre, hreach⟩, he,
    ⟨begun, nextBegun, hlive, hnext⟩, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  subst e
  have hcanonical :
      x = (⟨x.bank, .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta x begun hlive
  have hactual :
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        (⟨x.bank, .live begun⟩ : BankTrialLocalState q) :=
    hreach.trans hcanonical
  have hf : x.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean pre x.bank begun hactual
  have htok :
      bankTrialLiveWaveToken x.bank
        ⟨0, bankTrialWindowWidthPos q⟩ = .E :=
    (bankTrialC5ActualLaunchTokenFacts ring root S
      hlarge hclean pre x hreach.symm root o ho).1
  have hdigit :
      (GrantBankReference.bankLocalReferenceCell x.bank
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok =
        .E := htok
  have hbank :
      (bankTrialLocalNext ring root x root).bank =
        GrantBankReference.bankLocalReferenceStepClamped
          ring root x.bank root := by
    rw [hcanonical]
    exact bankTrialLocalNextLiveBank
      ring root root x.bank begun
  have hproj := bankTrialCmpRoot ring root
    (bankTrialProbabilityUpperWindow hlarge) x.bank hf
  have hrawLease :
      (GrantBankReference.bankLocalReferenceInternalPair q
        x.bank ⟨0, bankTrialWindowWidthPos q⟩).1.lease =
          (compileAdvice q).bankLeaseCap := by
    rcases hmodes with hinc | hcomp
    · have hmode :
          (GrantBankReference.bankLocalReferenceInternalPair q
            x.bank ⟨0, bankTrialWindowWidthPos q⟩).1.mode =
              .IWAIT := by
        apply hproj.1.symm.trans
        rw [← hbank]
        exact hinc.2
      change (bankPair
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        1 (compileAdvice q).b (compileAdvice q).theta).1.lease =
          (compileAdvice q).bankLeaseCap
      exact bankTrialC5ActualRawArmedLaunchLease
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        (by have hb := bankTrialCmpWidth q; omega)
        rfl rfl rfl hinc.1 hdigit hmode
    · change (bankPair
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        1 (compileAdvice q).b (compileAdvice q).theta).1.lease =
          (compileAdvice q).bankLeaseCap
      exact bankTrialC5ActualRawComparatorLaunchLease
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell x.bank
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        (by have hb := bankTrialCmpWidth q; omega)
        rfl rfl rfl hcomp.1 hdigit
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hfield :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root x.bank root).fields ⟨0, by omega⟩).2.2.2 =
      (GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair
          q x.bank ⟨0, bankTrialWindowWidthPos q⟩).1)).2.2.2 := by
    rw [bankTrialLocalStepField ring root root x.bank hs hf,
      bankTrialLocalFieldRootOutgoing ring root x.bank]
  have hclamped := bankTrialLocalClampedLease q
    ((GrantBankReference.bankLocalReferenceInternalPair
      q x.bank ⟨0, bankTrialWindowWidthPos q⟩).1)
    (by rw [hrawLease]; exact Nat.le_refl _)
  calc
    bankTrialC5ActualRootLease o.after =
        ((bankTrialLocalNext ring root x root).bank.fields
          ⟨0, by omega⟩).2.2.2 := by
            rw [bankTrialC5ActualStartPost ring root S x root o ho]
            rfl
    _ = ((GrantBankReference.bankLocalReferenceStepClamped
          ring root x.bank root).fields ⟨0, by omega⟩).2.2.2 := by
            rw [hbank]
    _ = (GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair
            q x.bank ⟨0, bankTrialWindowWidthPos q⟩).1)).2.2.2 :=
              hfield
    _ = (GrantBankReference.bankLocalReferenceInternalPair
          q x.bank ⟨0, bankTrialWindowWidthPos q⟩).1.lease :=
            hclamped
    _ = 13 * ((compileAdvice q).b + 2) := hrawLease

/-- L3: every nonincident scheduler service frames the actual
numeric root lease on a genuine unresolved origin prefix. -/
theorem bankTrialC5ActualUnresolvedNonincidentLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n)) (f : Fin n)
    (hnot : ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root pre o.after) ∨
        bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root pre o.after)))
    (hne : f ≠ root) (hin : ring.rightNeighbor f ≠ root) :
    bankTrialC5ActualRootLease
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f) =
      bankTrialC5ActualRootLease
        (bankTrialLocalRun ring root pre o.after) := by
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o
      (bankTrialLocalRun ring root pre o.after) hnot
  have hcanonical :
      bankTrialLocalRun ring root pre o.after =
        (⟨(bankTrialLocalRun ring root pre o.after).bank,
          .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta
      (bankTrialLocalRun ring root pre o.after) begun hlive
  have hf :
      (bankTrialLocalRun ring root pre o.after).bank.success =
        false :=
    bankTrialC5ActualPrefixLiveUnlatched
      ring root S hclean x e o ho pre begun hlive
  have hbank :
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre o.after) f).bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root (bankTrialLocalRun ring root pre o.after).bank f := by
    rw [hcanonical]
    exact bankTrialLocalNextLiveBank ring root f
      (bankTrialLocalRun ring root pre o.after).bank begun
  have hframe := bankTrialLocalRootNonincidentFrame
    ring root f (bankTrialLocalRun ring root pre o.after).bank
    hf hne hin
  change
    ((bankTrialLocalNext ring root
      (bankTrialLocalRun ring root pre o.after) f).bank.fields
        ⟨0, by omega⟩).2.2.2 =
    ((bankTrialLocalRun ring root pre o.after).bank.fields
        ⟨0, by omega⟩).2.2.2
  rw [hbank]
  exact congrArg
    (fun v : Mode × Bool × BTok × Nat => v.2.2.2) hframe

/-- The actual source has a matching AL-return branch which
SETS THE ROOT LEASE DIRECTLY TO ZERO, not to oldLease - 1. -/
def bankTrialC5ActualALCollapseRootCell (b : Nat) : BankCell :=
  { role := 0, mode := .IWAIT, bit := false, tok := .E,
    lease := 13 * (b + 2), grant := false }

def bankTrialC5ActualALCollapseDigitCell : BankCell :=
  { role := 1, mode := .RESET, bit := false, tok := .AL,
    lease := 0, grant := false }

/-- Literal one-service obstruction to L2 AS STATED: the old
root has an active IWAIT with full lease; a matching AL across
the outgoing root edge returns CSTART and drops more than one
lease unit in one service. -/
theorem bankTrialC5ActualRawALReturnLeaseCollapse
    (b : Nat) (theta : Nat → Bool) (hb : 1 ≤ b) :
    (bankPair (bankTrialC5ActualALCollapseRootCell b)
      bankTrialC5ActualALCollapseDigitCell 1 b theta).1.mode =
        .CSTART ∧
    (bankPair (bankTrialC5ActualALCollapseRootCell b)
      bankTrialC5ActualALCollapseDigitCell 1 b theta).1.lease = 0 ∧
    1 < (bankTrialC5ActualALCollapseRootCell b).lease := by
  have hpair :
      (bankPair (bankTrialC5ActualALCollapseRootCell b)
        bankTrialC5ActualALCollapseDigitCell 1 b theta).1.mode =
          .CSTART ∧
      (bankPair (bankTrialC5ActualALCollapseRootCell b)
        bankTrialC5ActualALCollapseDigitCell 1 b theta).1.lease =
          0 := by
    simp [bankPair, bankTrialC5ActualALCollapseRootCell,
      bankTrialC5ActualALCollapseDigitCell, hb,
      isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  refine ⟨hpair.1, hpair.2, ?_⟩
  change 1 < 13 * (b + 2)
  omega

/-- Count nominated services, without stopping the original BANK
scheduler tape or introducing an auxiliary worker scheduler. -/
noncomputable def bankTrialC5ActualNominatedHits {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLocalState q → List (Fin n) → Nat
  | _, [] => 0
  | z, f :: tail =>
      (if f = bankTrialC5ActualNominatedEdge ring root z
       then 1 else 0) +
      bankTrialC5ActualNominatedHits ring root
        (bankTrialLocalNext ring root z f) tail

/-- L4's rank-accounting core: before any first exit, total
nominated hits PLUS the residual actual wave rank never exceeds
the starting wave rank. This is stronger than a raw hit cap. -/
theorem bankTrialC5ActualNominatedHitsRankBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    ∀ (z : BankTrialLocalState q),
      BankTrialC5ActualFirstExitReachable ring root o z →
      ∀ (w : List (Fin n)),
        (∀ before middle : List (Fin n), ∀ f : Fin n,
          w = before ++ (f :: middle) →
          ¬ (bankTrialC5ActualReturned o
              (bankTrialLocalRun ring root before z) ∨
            bankTrialC5ActualBadExit o
              (bankTrialLocalRun ring root before z))) →
        bankTrialC5ActualNominatedHits ring root z w +
          bankTrialC5ActualWaveRank
            (bankTrialLocalRun ring root w z).bank ≤
        bankTrialC5ActualWaveRank z.bank := by
  intro z hz w
  induction w generalizing z with
  | nil =>
      intro _
      simp [bankTrialC5ActualNominatedHits, bankTrialLocalRun]
  | cons f tail ih =>
      intro hstrict
      have hnot :
          ¬ (bankTrialC5ActualReturned o z ∨
            bankTrialC5ActualBadExit o z) := by
        have hh := hstrict [] tail f rfl
        simpa only [bankTrialLocalRun] using hh
      have hzNext :
          BankTrialC5ActualFirstExitReachable ring root o
            (bankTrialLocalNext ring root z f) :=
        BankTrialC5ActualFirstExitReachable.advance z hz hnot f
      have hstrictNext :
          ∀ before middle : List (Fin n), ∀ g : Fin n,
            tail = before ++ (g :: middle) →
            ¬ (bankTrialC5ActualReturned o
                (bankTrialLocalRun ring root before
                  (bankTrialLocalNext ring root z f)) ∨
              bankTrialC5ActualBadExit o
                (bankTrialLocalRun ring root before
                  (bankTrialLocalNext ring root z f))) := by
        intro before middle g hw
        have hword :
            f :: tail = (f :: before) ++ (g :: middle) := by
          rw [hw]
          rfl
        have hh := hstrict (f :: before) middle g hword
        exact hh
      have hchild := ih
        (bankTrialLocalNext ring root z f) hzNext hstrictNext
      by_cases hd : f = bankTrialC5ActualNominatedEdge ring root z
      · have hdrop := bankTrialC5ActualNominatedFirstExitDrop
          ring root S hsp hlarge hwidth hclean
          x e o ho z hz hnot
        rw [← hd] at hdrop
        simp only [bankTrialC5ActualNominatedHits,
          if_pos hd, bankTrialLocalRun]
        omega
      · have hweak :=
          (bankTrialC5ActualFirstExitWaveRowsHolds
            ring root S hsp hlarge hwidth hclean
            x e o ho z hz hnot).1 f
        simp only [bankTrialC5ActualNominatedHits,
          if_neg hd, Nat.zero_add, bankTrialLocalRun]
        omega

/-- A concrete unconditional part of L4: the nominated hits
strictly BEFORE the timeout service cost at most L = 2b+2. -/
theorem bankTrialC5ActualNominatedHitsBeforeTimeoutBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (w : List (Fin n))
    (htime : bankTrialC5ActualTimeout ring root o w = true) :
    ∃ pre tail : List (Fin n), ∃ f : Fin n,
      w = pre ++ (f :: tail) ∧
      bankTrialC5ActualNominatedHits ring root o.after pre ≤
        2 * (compileAdvice q).b + 2 := by
  obtain ⟨pre, tail, f, hword, hstrict⟩ :=
    bankTrialC5ActualTimeoutHasStrictPrefixGuard ring root o w htime
  have hrank := bankTrialC5ActualNominatedHitsRankBound
    ring root S hsp hlarge hwidth hclean x e o ho
    o.after BankTrialC5ActualFirstExitReachable.start pre hstrict
  have hcap := bankTrialC5ActualWaveRankCap o.after.bank
  refine ⟨pre, tail, f, hword, ?_⟩
  omega

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Exact raw outgoing-root lease payment when an IWAIT/CWAIT
worker remains in the SAME waiting mode. This excludes the
matching AL/CL return branches, whose lease is reset to zero. -/
private theorem bankTrialC5ActualRawOutgoingWaitSpend
    (b : Nat) (theta : Nat → Bool) (a d : BankCell)
    (hb : 1 < b) (ha : a.role = 0) (hd : d.role = 1)
    (hg : a.grant = false)
    (hm : a.mode = .IWAIT ∨ a.mode = .CWAIT)
    (hnext : (bankPair a d 1 b theta).1.mode = a.mode) :
    (bankPair a d 1 b theta).1.lease + 1 = a.lease := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hm with hi | hc
  · cases ht : d.tok <;>
      by_cases hl : 1 < a.lease <;>
      simp [bankPair, ha, hd, hg, hi, ht, hl, hbpos,
        hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnext ⊢ <;> omega
  · cases ht : d.tok <;>
      by_cases hl : 1 < a.lease <;>
      simp [bankPair, ha, hd, hg, hc, ht, hl, hbpos,
        hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnext ⊢ <;> omega

/-- The incoming-root unary map makes the same exact payment
when it leaves a waiting root in its old waiting mode. -/
private theorem bankTrialC5ActualRawIncomingWaitSpend
    (a : BankCell)
    (hm : a.mode = .IWAIT ∨ a.mode = .CWAIT)
    (hnext :
      (GrantBankReference.incomingRootBankMap a).mode = a.mode) :
    (GrantBankReference.incomingRootBankMap a).lease + 1 =
      a.lease := by
  rcases hm with hi | hc
  · by_cases hl : 1 < a.lease <;>
      simp [GrantBankReference.incomingRootBankMap, hi,
        isWaitMode, hl] at hnext ⊢ <;> omega
  · by_cases hl : 1 < a.lease <;>
      simp [GrantBankReference.incomingRootBankMap, hc,
        isWaitMode, hl] at hnext ⊢ <;> omega

/-- Every actual origin prefix has the inherited CLEAN numeric
lease cap. This is a theorem of the original BANK local model,
not a physical Counter.Config origin hypothesis. -/
theorem bankTrialC5ActualOriginPrefixLeaseCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n)) :
    BankTrialLocalLeaseCap q
      (bankTrialLocalRun ring root pre o.after).bank := by
  obtain ⟨_, ⟨launch, hlaunch⟩, _, _, _⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x e o ho
  have hrun := bankTrialC5GoodReturnReachable
    ring root S launch x hlaunch.symm e o ho pre
  rw [hrun]
  exact bankTrialLocalLeaseCapRun
    ring root (launch ++ (e :: pre))
    (bankTrialLocalStart S)
    (bankTrialLocalCleanLeaseCap S hclean)

/-- The clamped outgoing-root BANK reference faithfully deducts
one lease unit when its old and new modes are the same wait. -/
private theorem bankTrialC5ActualOutgoingWaitSpend
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hf : B.success = false)
    (hcap : BankTrialLocalLeaseCap q B)
    (hwait : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hnext :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        bankTrialLiveWaveRootMode B) :
    ((bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank.fields
        ⟨0, by omega⟩).2.2.2 + 1 =
      (B.fields ⟨0, by omega⟩).2.2.2 := by
  have hmode :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, bankTrialWindowWidthPos q⟩).1.mode =
        bankTrialLiveWaveRootMode B := by
    calc
      (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, bankTrialWindowWidthPos q⟩).1.mode =
          bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B root) :=
        ((bankTrialCmpRoot ring root hw B hf).1).symm
      _ = bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank := by
        rw [bankTrialLocalNextLiveBank]
      _ = bankTrialLiveWaveRootMode B := hnext
  have hraw :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, bankTrialWindowWidthPos q⟩).1.lease + 1 =
        (B.fields ⟨0, by omega⟩).2.2.2 := by
    change (bankPair
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      1 (compileAdvice q).b (compileAdvice q).theta).1.lease + 1 =
        (B.fields ⟨0, by omega⟩).2.2.2
    exact bankTrialC5ActualRawOutgoingWaitSpend
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      (by have hb := bankTrialCmpWidth q; omega)
      rfl rfl rfl hwait hmode
  have hrawCap :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, bankTrialWindowWidthPos q⟩).1.lease ≤
        (compileAdvice q).bankLeaseCap := by
    have hold := hcap 0 (by omega)
    omega
  have hclamp := bankTrialLocalClampedLease q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, bankTrialWindowWidthPos q⟩).1) hrawCap
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  rw [bankTrialLocalNextLiveBank,
    bankTrialLocalStepField ring root root B hs hf,
    bankTrialLocalFieldRootOutgoing ring root B, hclamp]
  exact hraw

/-- The clamped incoming-root reference deducts exactly one lease
unit on any still-waiting successor. -/
private theorem bankTrialC5ActualIncomingWaitSpend
    {n q : Nat}
    (ring : DirectedRing n) (root f : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hf : B.success = false)
    (hcap : BankTrialLocalLeaseCap q B)
    (hwait : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hin : ring.rightNeighbor f = root)
    (hnext :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank =
        bankTrialLiveWaveRootMode B) :
    ((bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank.fields
        ⟨0, by omega⟩).2.2.2 + 1 =
      (B.fields ⟨0, by omega⟩).2.2.2 := by
  have hne := bankTrialC5IncomingNotRoot ring root f hw hin
  have hsource :
      ¬ (0 < (compileAdvice q).b ∧
        f = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa only [Counter.site] using h.2)
  have htarget :
      ¬ (0 < (0 : Nat) ∧
        f = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have htop :
      ¬ ((0 : Nat) = (compileAdvice q).b ∧
        f = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hb := bankTrialCmpWidth q
    omega
  have hselected :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B f).fields ⟨0, by omega⟩ =
      GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by omega⟩)) := by
    exact (bankTrialLocalStepField ring root f B
      (Or.inl hin) hf ⟨0, by omega⟩).trans
      (bankTrialLocalSelectedIncoming ring root f B
        ⟨0, by omega⟩ hsource htarget htop ⟨rfl, hin⟩)
  have hrawMode :
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode =
      bankTrialLiveWaveRootMode B := by
    calc
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode =
        (GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨0, by omega⟩))).1 :=
        (bankTrialC5ClampedMode q _).symm
      _ = bankTrialLiveWaveRootMode
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B f) :=
        (congrArg
          (fun v : Mode × Bool × BTok × Nat => v.1)
          hselected).symm
      _ = bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) f).bank := by
        rw [bankTrialLocalNextLiveBank]
      _ = bankTrialLiveWaveRootMode B := hnext
  have hraw :
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).lease + 1 =
      (B.fields ⟨0, by omega⟩).2.2.2 :=
    bankTrialC5ActualRawIncomingWaitSpend
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩) hwait hrawMode
  have hrawCap :
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).lease ≤
        (compileAdvice q).bankLeaseCap := by
    have hold := hcap 0 (by omega)
    omega
  have hclamp := bankTrialLocalClampedLease q
    (GrantBankReference.incomingRootBankMap
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩)) hrawCap
  rw [bankTrialLocalNextLiveBank, hselected, hclamp]
  exact hraw

/-- L2, guarded and STRONGER than the requested prefix formulation:
for an actual origin, any incident service whose old and new
states are both unresolved spends exactly one root-lease unit.
In particular the mode-changing AL/CL returns are excluded
without an extra ad-hoc token assumption. -/
theorem bankTrialC5ActualGuardedIncidentSpend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n)) (f : Fin n)
    (hbefore : ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root pre o.after) ∨
        bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root pre o.after)))
    (hafter : ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root (pre ++ [f]) o.after) ∨
        bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root (pre ++ [f]) o.after)))
    (hincident : f = root ∨ ring.rightNeighbor f = root) :
    bankTrialC5ActualRootLease
        (bankTrialLocalRun ring root (pre ++ [f]) o.after) + 1 =
      bankTrialC5ActualRootLease
        (bankTrialLocalRun ring root pre o.after) := by
  have hrun :
      bankTrialLocalRun ring root (pre ++ [f]) o.after =
        bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f := by
    rw [bankTrialLocalRunAppend]
    rfl
  rw [hrun] at hafter ⊢
  obtain ⟨⟨begun, hlive⟩, _⟩ :=
    bankTrialC5ActualUnresolvedIsActive o
      (bankTrialLocalRun ring root pre o.after) hbefore
  have hactiveOld := bankTrialC5ActualUnresolvedIsActive
    o (bankTrialLocalRun ring root pre o.after) hbefore
  have hactiveNew := bankTrialC5ActualUnresolvedIsActive
    o (bankTrialLocalNext ring root
      (bankTrialLocalRun ring root pre o.after) f) hafter
  have hmode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre o.after) f).bank =
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre o.after).bank :=
    hactiveNew.2.trans hactiveOld.2.symm
  have hcanon :
      bankTrialLocalRun ring root pre o.after =
        (⟨(bankTrialLocalRun ring root pre o.after).bank,
          .live begun⟩ : BankTrialLocalState q) :=
    bankTrialCmpStateEta
      (bankTrialLocalRun ring root pre o.after) begun hlive
  have hmodeCanon :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨(bankTrialLocalRun ring root pre o.after).bank,
            .live begun⟩ : BankTrialLocalState q) f).bank =
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre o.after).bank := by
    rw [← hcanon]
    exact hmode
  have hf :
      (bankTrialLocalRun ring root pre o.after).bank.success =
        false :=
    bankTrialC5ActualPrefixLiveUnlatched
      ring root S hclean x e o ho pre begun hlive
  have hcap := bankTrialC5ActualOriginPrefixLeaseCap
    ring root S hclean x e o ho pre
  have hwait := bankTrialC5ActualActiveWaitMode
    o (bankTrialLocalRun ring root pre o.after) hactiveOld
  rcases hincident with he | hin
  · subst f
    have hpaid := bankTrialC5ActualOutgoingWaitSpend
      ring root (bankTrialProbabilityUpperWindow hlarge)
      (bankTrialLocalRun ring root pre o.after).bank
      begun hf hcap hwait hmodeCanon
    rw [← hcanon] at hpaid
    exact hpaid
  · have hpaid := bankTrialC5ActualIncomingWaitSpend
      ring root f (bankTrialProbabilityUpperWindow hlarge)
      (bankTrialLocalRun ring root pre o.after).bank
      begun hf hcap hwait hin hmodeCanon
    rw [← hcanon] at hpaid
    exact hpaid

/-- The watchdog witness already includes the exact upper
bound on the old root lease at its final root-incident service. -/
theorem bankTrialC5ActualTimeoutPreLeaseAtMostOne {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (w : List (Fin n))
    (h : bankTrialC5ActualTimeout ring root o w = true) :
    ∃ pre tail : List (Fin n), ∃ f : Fin n,
      w = pre ++ (f :: tail) ∧
      bankTrialC5ActualRootLease
        (bankTrialLocalRun ring root pre o.after) ≤ 1 ∧
      (f = root ∨ ring.rightNeighbor f = root) := by
  unfold bankTrialC5ActualTimeout at h
  obtain ⟨pre, tail, f, hword, _, _, _, hlease,
    hincident, _, _⟩ := of_decide_eq_true h
  exact ⟨pre, tail, f, hword, hlease, hincident⟩

end L3


namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
W1-W3 after the two explicit replacements
above. The original timeout witness omitted the unresolved pre
state, although the first-exit nonreturnBad proof already had it.
All W1-W3 assumptions are discharged from that repaired witness
and the existing L1/L2/L3 rows.

The W4 incident split below is unconditional. The separate
CounterTrialLower.workerPenaltyCount cutoff comparison remains
open; no conditional kernel theorem is asserted.
-/

/-- W1. Every chronological prefix of the witnessed pre-service
word, INCLUDING the entire pre itself, is unresolved. -/
theorem bankTrialC5ActualTimeoutAllPrefixUnresolved {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (w : List (Fin n))
    (htime : bankTrialC5ActualTimeout ring root o w = true) :
    ∃ pre tail : List (Fin n), ∃ f : Fin n,
      w = pre ++ (f :: tail) ∧
      (∀ before suffix : List (Fin n),
        pre = before ++ suffix →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root before o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root before o.after))) ∧
      bankTrialC5ActualRootLease
        (bankTrialLocalRun ring root pre o.after) ≤ 1 ∧
      (f = root ∨ ring.rightNeighbor f = root) := by
  unfold bankTrialC5ActualTimeout at htime
  obtain ⟨pre, tail, f, hword, hstrict, _, _, hlease,
    hincident, _, _, hcurrent⟩ := of_decide_eq_true htime
  refine ⟨pre, tail, f, hword, ?_, hlease, hincident⟩
  intro before suffix hsplit
  cases suffix with
  | nil =>
      have heq : before = pre := by
        simpa only [List.append_nil] using hsplit.symm
      rw [heq]
      exact hcurrent
  | cons g more =>
      exact hstrict before more g hsplit

/-- The raw chronological number of services whose selected
edge is incident to the root; this is independent of the
worker's nominated edge and of any future scheduler word. -/
def bankTrialC5ActualIncidentCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → Nat
  | [] => 0
  | f :: rest =>
      (if f = root ∨ ring.rightNeighbor f = root then 1 else 0) +
        bankTrialC5ActualIncidentCount ring root rest

theorem bankTrialC5ActualIncidentCountAppend {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre : List (Fin n)) (f : Fin n),
      bankTrialC5ActualIncidentCount ring root (pre ++ [f]) =
        bankTrialC5ActualIncidentCount ring root pre +
          (if f = root ∨ ring.rightNeighbor f = root then 1 else 0) := by
  intro pre
  induction pre with
  | nil =>
      intro f
      simp only [List.nil_append, bankTrialC5ActualIncidentCount,
        Nat.add_zero, Nat.zero_add]
  | cons g rest ih =>
      intro f
      change
        (if g = root ∨ ring.rightNeighbor g = root then 1 else 0) +
          bankTrialC5ActualIncidentCount ring root (rest ++ [f]) =
        ((if g = root ∨ ring.rightNeighbor g = root then 1 else 0) +
          bankTrialC5ActualIncidentCount ring root rest) +
          (if f = root ∨ ring.rightNeighbor f = root then 1 else 0)
      rw [ih f]
      omega

/-- W2: the exact L2/L3 telescope. Each successive prefix has a
proved unresolved certificate, and therefore each incident edge
pays one lease unit, while a nonincident edge pays zero.
No stopped shadow run and no assumed source transition occur. -/
theorem bankTrialC5ActualPrefixLeaseIncidentTelescope {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    ∀ pre : List (Fin n),
      (∀ before suffix : List (Fin n),
        pre = before ++ suffix →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root before o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root before o.after))) →
      bankTrialC5ActualRootLease o.after ≤
        bankTrialC5ActualRootLease
          (bankTrialLocalRun ring root pre o.after) +
        bankTrialC5ActualIncidentCount ring root pre := by
  have hclean : BankTrialLocalClean q S :=
    (bankTrialC5ActualStartGuardFacts ring root S x e o ho).1
  have hrev : ∀ rev : List (Fin n),
      (∀ before suffix : List (Fin n),
        rev.reverse = before ++ suffix →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root before o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root before o.after))) →
      bankTrialC5ActualRootLease o.after ≤
        bankTrialC5ActualRootLease
          (bankTrialLocalRun ring root rev.reverse o.after) +
        bankTrialC5ActualIncidentCount ring root rev.reverse := by
    intro rev
    induction rev with
    | nil =>
        intro _
        change bankTrialC5ActualRootLease o.after ≤
          bankTrialC5ActualRootLease o.after + 0
        omega
    | cons f rest ih =>
        intro hprefix
        have hbefore :
            ¬ (bankTrialC5ActualReturned o
                 (bankTrialLocalRun ring root rest.reverse o.after) ∨
               bankTrialC5ActualBadExit o
                 (bankTrialLocalRun ring root rest.reverse o.after)) :=
          hprefix rest.reverse [f] (by simp only [List.reverse_cons])
        have hafter :
            ¬ (bankTrialC5ActualReturned o
                 (bankTrialLocalRun ring root
                   (rest.reverse ++ [f]) o.after) ∨
               bankTrialC5ActualBadExit o
                 (bankTrialLocalRun ring root
                   (rest.reverse ++ [f]) o.after)) :=
          hprefix (rest.reverse ++ [f]) []
            (by simp only [List.reverse_cons, List.append_nil])
        have hprefixRest :
            ∀ before suffix : List (Fin n),
              rest.reverse = before ++ suffix →
              ¬ (bankTrialC5ActualReturned o
                   (bankTrialLocalRun ring root before o.after) ∨
                 bankTrialC5ActualBadExit o
                   (bankTrialLocalRun ring root before o.after)) := by
          intro before suffix hs
          apply hprefix before (suffix ++ [f])
          rw [List.reverse_cons, hs]
          simp only [List.append_assoc]
        have hbound := ih hprefixRest
        simp only [List.reverse_cons]
        by_cases hincident : f = root ∨ ring.rightNeighbor f = root
        · have hpaid := bankTrialC5ActualGuardedIncidentSpend
            ring root S hlarge hclean x e o ho
            rest.reverse f hbefore hafter hincident
          have hcount :
              bankTrialC5ActualIncidentCount ring root
                (rest.reverse ++ [f]) =
              bankTrialC5ActualIncidentCount ring root rest.reverse + 1 := by
            rw [bankTrialC5ActualIncidentCountAppend, if_pos hincident]
          calc
            bankTrialC5ActualRootLease o.after ≤
                bankTrialC5ActualRootLease
                  (bankTrialLocalRun ring root rest.reverse o.after) +
                bankTrialC5ActualIncidentCount ring root rest.reverse :=
              hbound
            _ =
                (bankTrialC5ActualRootLease
                  (bankTrialLocalRun ring root
                    (rest.reverse ++ [f]) o.after) + 1) +
                bankTrialC5ActualIncidentCount ring root rest.reverse := by
              rw [hpaid]
            _ =
                bankTrialC5ActualRootLease
                  (bankTrialLocalRun ring root
                    (rest.reverse ++ [f]) o.after) +
                bankTrialC5ActualIncidentCount
                  ring root (rest.reverse ++ [f]) := by
              rw [hcount]
              omega
        · have hne : f ≠ root := by
            intro he
            exact hincident (Or.inl he)
          have hin : ring.rightNeighbor f ≠ root := by
            intro he
            exact hincident (Or.inr he)
          have hframe :
              bankTrialC5ActualRootLease
                (bankTrialLocalRun ring root
                  (rest.reverse ++ [f]) o.after) =
              bankTrialC5ActualRootLease
                (bankTrialLocalRun ring root rest.reverse o.after) := by
            rw [bankTrialLocalRunAppend]
            exact bankTrialC5ActualUnresolvedNonincidentLeaseFrame
              ring root S hclean x e o ho rest.reverse f hbefore hne hin
          have hcount :
              bankTrialC5ActualIncidentCount ring root
                (rest.reverse ++ [f]) =
              bankTrialC5ActualIncidentCount ring root rest.reverse := by
            rw [bankTrialC5ActualIncidentCountAppend,
              if_neg hincident, Nat.add_zero]
          calc
            bankTrialC5ActualRootLease o.after ≤
                bankTrialC5ActualRootLease
                  (bankTrialLocalRun ring root rest.reverse o.after) +
                bankTrialC5ActualIncidentCount ring root rest.reverse :=
              hbound
            _ =
                bankTrialC5ActualRootLease
                  (bankTrialLocalRun ring root
                    (rest.reverse ++ [f]) o.after) +
                bankTrialC5ActualIncidentCount
                  ring root (rest.reverse ++ [f]) := by
              rw [hframe, hcount]
  intro pre hprefix
  have hrun := hrev pre.reverse (by
    intro before suffix hs
    apply hprefix before suffix
    simpa only [List.reverse_reverse] using hs)
  simpa only [List.reverse_reverse] using hrun

/-- W3: the launched 13(b+2) lease is paid by at most one
remaining pre-timeout unit and the actual incident services
strictly before the timeout edge. The timeout edge itself is NOT
included in this count. -/
theorem bankTrialC5ActualTimeoutIncidentLeaseBudget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (w : List (Fin n))
    (htime : bankTrialC5ActualTimeout ring root o w = true) :
    ∃ pre tail : List (Fin n), ∃ f : Fin n,
      w = pre ++ (f :: tail) ∧
      13 * ((compileAdvice q).b + 2) ≤
        1 + bankTrialC5ActualIncidentCount ring root pre ∧
      (f = root ∨ ring.rightNeighbor f = root) := by
  obtain ⟨pre, tail, f, hword, hprefix, hlease, hincident⟩ :=
    bankTrialC5ActualTimeoutAllPrefixUnresolved
      ring root o w htime
  have hclean : BankTrialLocalClean q S :=
    (bankTrialC5ActualStartGuardFacts ring root S x e o ho).1
  have hlaunch := bankTrialC5ActualLaunchLeaseHolds
    ring root S hlarge hclean x e o ho
  have htel := bankTrialC5ActualPrefixLeaseIncidentTelescope
    ring root S hlarge x e o ho pre hprefix
  rw [hlaunch] at htel
  refine ⟨pre, tail, f, hword, ?_, hincident⟩
  omega

/-- Literal (untruncated) physical penalty count on a chronological
word, used only for the W4 partition. The cap comparison against
CounterTrialLower.workerPenaltyCount is still required. -/
noncomputable def bankTrialC5ActualUntruncatedPenalties {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLocalState q → List (Fin n) → Nat
  | _, [] => 0
  | z, f :: rest =>
      (if bankTrialC5ActualPenaltyEdge ring root z f then 1 else 0) +
        bankTrialC5ActualUntruncatedPenalties ring root
          (bankTrialLocalNext ring root z f) rest

/-- At any individual source state, every incident service is
either nominated or a penalty. These classes are disjoint. -/
theorem bankTrialC5ActualIncidentPaidOrNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (f : Fin n) :
    (if f = root ∨ ring.rightNeighbor f = root then 1 else 0) ≤
      (if bankTrialC5ActualPenaltyEdge ring root z f then 1 else 0) +
      (if f = bankTrialC5ActualNominatedEdge ring root z
       then 1 else 0) := by
  classical
  by_cases hi : f = root ∨ ring.rightNeighbor f = root
  · by_cases hd : f = bankTrialC5ActualNominatedEdge ring root z
    · simp only [if_pos hi, if_pos hd]
      omega
    · have hp : bankTrialC5ActualPenaltyEdge ring root z f :=
        ⟨hi, hd⟩
      simp only [if_pos hi, if_pos hp, if_neg hd]
      omega
  · simp only [if_neg hi]
    exact Nat.zero_le _

/-- W4's unconditional counting half: root incidents partition
between the actual nominated edge and its complement penalty
on every chronological source prefix. -/
theorem bankTrialC5ActualIncidentSplitBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (z : BankTrialLocalState q) (pre : List (Fin n)),
      bankTrialC5ActualIncidentCount ring root pre ≤
        bankTrialC5ActualUntruncatedPenalties ring root z pre +
        bankTrialC5ActualNominatedHits ring root z pre := by
  intro z pre
  induction pre generalizing z with
  | nil =>
      exact Nat.zero_le _
  | cons f rest ih =>
      have hstep := bankTrialC5ActualIncidentPaidOrNominated
        ring root z f
      have hrest := ih (bankTrialLocalNext ring root z f)
      change
        (if f = root ∨ ring.rightNeighbor f = root then 1 else 0) +
          bankTrialC5ActualIncidentCount ring root rest ≤
        ((if bankTrialC5ActualPenaltyEdge ring root z f then 1 else 0) +
          bankTrialC5ActualUntruncatedPenalties ring root
            (bankTrialLocalNext ring root z f) rest) +
        ((if f = bankTrialC5ActualNominatedEdge ring root z then 1 else 0) +
          bankTrialC5ActualNominatedHits ring root
            (bankTrialLocalNext ring root z f) rest)
      omega

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The exact nominal-hit count on a one-edge extension. -/
theorem bankTrialC5ActualNominatedHitsSnoc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre : List (Fin n)) (f : Fin n)
      (z : BankTrialLocalState q),
      bankTrialC5ActualNominatedHits ring root z (pre ++ [f]) =
        bankTrialC5ActualNominatedHits ring root z pre +
          (if f = bankTrialC5ActualNominatedEdge ring root
                (bankTrialLocalRun ring root pre z)
           then 1 else 0) := by
  intro pre
  induction pre with
  | nil =>
      intro f z
      change
        (if f = bankTrialC5ActualNominatedEdge ring root z
         then 1 else 0) + 0 =
        0 + (if f = bankTrialC5ActualNominatedEdge ring root z
             then 1 else 0)
      omega
  | cons g rest ih =>
      intro f z
      change
        (if g = bankTrialC5ActualNominatedEdge ring root z
         then 1 else 0) +
          bankTrialC5ActualNominatedHits ring root
            (bankTrialLocalNext ring root z g) (rest ++ [f]) =
        ((if g = bankTrialC5ActualNominatedEdge ring root z
          then 1 else 0) +
          bankTrialC5ActualNominatedHits ring root
            (bankTrialLocalNext ring root z g) rest) +
          (if f = bankTrialC5ActualNominatedEdge ring root
                (bankTrialLocalRun ring root rest
                  (bankTrialLocalNext ring root z g))
           then 1 else 0)
      rw [ih f (bankTrialLocalNext ring root z g)]
      omega

/-- The untruncated penalty count on the same one-edge extension. -/
theorem bankTrialC5ActualUntruncatedPenaltiesSnoc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre : List (Fin n)) (f : Fin n)
      (z : BankTrialLocalState q),
      bankTrialC5ActualUntruncatedPenalties
          ring root z (pre ++ [f]) =
        bankTrialC5ActualUntruncatedPenalties ring root z pre +
          (if bankTrialC5ActualPenaltyEdge ring root
                (bankTrialLocalRun ring root pre z) f
           then 1 else 0) := by
  intro pre
  induction pre with
  | nil =>
      intro f z
      change
        (if bankTrialC5ActualPenaltyEdge ring root z f
         then 1 else 0) + 0 =
        0 + (if bankTrialC5ActualPenaltyEdge ring root z f
             then 1 else 0)
      omega
  | cons g rest ih =>
      intro f z
      change
        (if bankTrialC5ActualPenaltyEdge ring root z g
         then 1 else 0) +
          bankTrialC5ActualUntruncatedPenalties ring root
            (bankTrialLocalNext ring root z g) (rest ++ [f]) =
        ((if bankTrialC5ActualPenaltyEdge ring root z g
          then 1 else 0) +
          bankTrialC5ActualUntruncatedPenalties ring root
            (bankTrialLocalNext ring root z g) rest) +
          (if bankTrialC5ActualPenaltyEdge ring root
                (bankTrialLocalRun ring root rest
                  (bankTrialLocalNext ring root z g)) f
           then 1 else 0)
      rw [ih f (bankTrialLocalNext ring root z g)]
      omega

/-- C1. Every penalty in a prefix before exhausting the nominee
budget is seen by the original-tape, STOPPED workerPenaltyCount,
even when an arbitrary suffix follows that prefix. The strict
bound is essential: when budget=0 the generic counter stops
before its next letter, even if that letter is a penalty. -/
theorem bankTrialC5ActualPenaltyPrefixLeStopped {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre suffix : List (Fin n))
      (z : BankTrialLocalState q) (budget : Nat),
      bankTrialC5ActualNominatedHits ring root z pre < budget →
      bankTrialC5ActualUntruncatedPenalties ring root z pre ≤
        CounterTrialLower.workerPenaltyCount
          (bankTrialLocalNext ring root)
          (bankTrialC5ActualNominatedEdge ring root)
          (bankTrialC5ActualPenaltyEdge ring root)
          z budget (pre ++ suffix) := by
  intro pre
  induction pre with
  | nil =>
      intro suffix z budget _
      change 0 ≤ CounterTrialLower.workerPenaltyCount
        (bankTrialLocalNext ring root)
        (bankTrialC5ActualNominatedEdge ring root)
        (bankTrialC5ActualPenaltyEdge ring root)
        z budget suffix
      exact Nat.zero_le _
  | cons f rest ih =>
      intro suffix z budget hstrict
      cases budget with
      | zero =>
          have hz : bankTrialC5ActualNominatedHits
              ring root z (f :: rest) < 0 := hstrict
          omega
      | succ budget =>
          by_cases hd :
              f = bankTrialC5ActualNominatedEdge ring root z
          · have hrest :
                bankTrialC5ActualNominatedHits ring root
                  (bankTrialLocalNext ring root z f) rest <
                budget := by
              have heq :
                  bankTrialC5ActualNominatedHits
                    ring root z (f :: rest) =
                  1 + bankTrialC5ActualNominatedHits ring root
                    (bankTrialLocalNext ring root z f) rest := by
                simp only [bankTrialC5ActualNominatedHits,
                  if_pos hd]
              omega
            have hnot :
                ¬ bankTrialC5ActualPenaltyEdge ring root z f := by
              intro hp
              exact hp.2 hd
            have htail := ih suffix
              (bankTrialLocalNext ring root z f) budget hrest
            simpa only [List.cons_append,
              bankTrialC5ActualUntruncatedPenalties,
              CounterTrialLower.workerPenaltyCount,
              if_pos hd, if_neg hnot, Nat.zero_add]
              using htail
          · have hrest :
                bankTrialC5ActualNominatedHits ring root
                  (bankTrialLocalNext ring root z f) rest <
                budget + 1 := by
              have heq :
                  bankTrialC5ActualNominatedHits
                    ring root z (f :: rest) =
                  bankTrialC5ActualNominatedHits ring root
                    (bankTrialLocalNext ring root z f) rest := by
                simp only [bankTrialC5ActualNominatedHits,
                  if_neg hd, Nat.zero_add]
              omega
            have htail := ih suffix
              (bankTrialLocalNext ring root z f)
              (budget + 1) hrest
            by_cases hp :
                bankTrialC5ActualPenaltyEdge ring root z f
            · have hadd := Nat.add_le_add_left htail 1
              simpa only [List.cons_append,
                bankTrialC5ActualUntruncatedPenalties,
                CounterTrialLower.workerPenaltyCount,
                if_neg hd, if_pos hp] using hadd
            · simpa only [List.cons_append,
                bankTrialC5ActualUntruncatedPenalties,
                CounterTrialLower.workerPenaltyCount,
                if_neg hd, if_neg hp, Nat.zero_add]
                using htail

/-- C1 at the exact timeout edge: if the strict pre-service
nominated budget remains, the STOPPED counter includes all
penalties THROUGH that edge. If the last edge is nominated, it
adds no penalty; if it is not nominated, the budget remains
strict through it. -/
theorem bankTrialC5ActualStoppedCountCoversEnd {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pre tail : List (Fin n)) (f : Fin n)
    (z : BankTrialLocalState q) (budget : Nat)
    (hstrict :
      bankTrialC5ActualNominatedHits ring root z pre < budget) :
    bankTrialC5ActualUntruncatedPenalties ring root
      z (pre ++ [f]) ≤
    CounterTrialLower.workerPenaltyCount
      (bankTrialLocalNext ring root)
      (bankTrialC5ActualNominatedEdge ring root)
      (bankTrialC5ActualPenaltyEdge ring root)
      z budget ((pre ++ [f]) ++ tail) := by
  by_cases hd :
      f = bankTrialC5ActualNominatedEdge ring root
        (bankTrialLocalRun ring root pre z)
  · have hnot :
        ¬ bankTrialC5ActualPenaltyEdge ring root
          (bankTrialLocalRun ring root pre z) f := by
      intro hp
      exact hp.2 hd
    have hpen := bankTrialC5ActualUntruncatedPenaltiesSnoc
      ring root pre f z
    have hcount := bankTrialC5ActualPenaltyPrefixLeStopped
      ring root pre (f :: tail) z budget hstrict
    rw [hpen, if_neg hnot, Nat.add_zero]
    have heq :
        (pre ++ [f]) ++ tail = pre ++ (f :: tail) := by
      simp only [List.append_assoc, List.singleton_append]
    rw [heq]
    exact hcount
  · have hnom := bankTrialC5ActualNominatedHitsSnoc
      ring root pre f z
    have htail :
        bankTrialC5ActualNominatedHits ring root
          z (pre ++ [f]) < budget := by
      rw [hnom, if_neg hd, Nat.add_zero]
      exact hstrict
    exact bankTrialC5ActualPenaltyPrefixLeStopped
      ring root (pre ++ [f]) tail z budget htail

/-- A first-exit-prefix word stays inside the actual reachable
class. Unlike a global closure hypothesis, only its own genuine
unresolved prefixes are used for each inductive advance. -/
theorem bankTrialC5ActualReachableOfUnresolvedPrefix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    ∀ (pre : List (Fin n)) (z : BankTrialLocalState q),
      BankTrialC5ActualFirstExitReachable ring root o z →
      (∀ before suffix : List (Fin n),
        pre = before ++ suffix →
        ¬ (bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root before z) ∨
          bankTrialC5ActualBadExit o
            (bankTrialLocalRun ring root before z))) →
      BankTrialC5ActualFirstExitReachable ring root o
        (bankTrialLocalRun ring root pre z) := by
  intro pre
  induction pre with
  | nil =>
      intro z hz _
      exact hz
  | cons f rest ih =>
      intro z hz hall
      have hnot :
          ¬ (bankTrialC5ActualReturned o z ∨
            bankTrialC5ActualBadExit o z) :=
        hall [] (f :: rest) rfl
      have hzNext :
          BankTrialC5ActualFirstExitReachable ring root o
            (bankTrialLocalNext ring root z f) :=
        BankTrialC5ActualFirstExitReachable.advance z hz hnot f
      have htail :
          ∀ before suffix : List (Fin n),
            rest = before ++ suffix →
            ¬ (bankTrialC5ActualReturned o
                (bankTrialLocalRun ring root before
                  (bankTrialLocalNext ring root z f)) ∨
              bankTrialC5ActualBadExit o
                (bankTrialLocalRun ring root before
                  (bankTrialLocalNext ring root z f))) := by
        intro before suffix hsplit
        have hword :
            f :: rest = (f :: before) ++ suffix := by
          rw [hsplit]
          rfl
        exact hall (f :: before) suffix hword
      change BankTrialC5ActualFirstExitReachable ring root o
        (bankTrialLocalRun ring root rest
          (bankTrialLocalNext ring root z f))
      exact ih (bankTrialLocalNext ring root z f) hzNext htail

/-- The strengthened nominated-hit budget needed at a timeout:
the pre-service wave rank is POSITIVE, so the pre-service count
is strictly below L, not merely at most L. This is what
prevents a spurious cutoff before a final penalty service. -/
theorem bankTrialC5ActualUnresolvedPrefixNominatedStrict
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hall : ∀ before suffix : List (Fin n),
      pre = before ++ suffix →
      ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root before o.after) ∨
        bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root before o.after))) :
    bankTrialC5ActualNominatedHits ring root o.after pre <
      2 * (compileAdvice q).b + 2 := by
  have hstrict :
      ∀ before middle : List (Fin n), ∀ f : Fin n,
        pre = before ++ (f :: middle) →
        ¬ (bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root before o.after) ∨
          bankTrialC5ActualBadExit o
            (bankTrialLocalRun ring root before o.after)) := by
    intro before middle f heq
    exact hall before (f :: middle) heq
  have hrank := bankTrialC5ActualNominatedHitsRankBound
    ring root S hsp hlarge hwidth hclean x e o ho
    o.after BankTrialC5ActualFirstExitReachable.start
    pre hstrict
  have hreach := bankTrialC5ActualReachableOfUnresolvedPrefix
    ring root o pre o.after
    BankTrialC5ActualFirstExitReachable.start hall
  have hnot :
      ¬ (bankTrialC5ActualReturned o
            (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
            (bankTrialLocalRun ring root pre o.after)) :=
    hall pre [] (by simp only [List.append_nil])
  have hpositive := bankTrialC5ActualFirstExitNoZeroRankOfRows
    ring root S
    (bankTrialC5ActualFirstExitWaveRowsHolds
      ring root S hsp hlarge hwidth hclean)
    x e o ho (bankTrialLocalRun ring root pre o.after)
    hreach hnot
  have hcap := bankTrialC5ActualWaveRankCap o.after.bank
  omega

/-- C1's full nominated-service bound through the timeout
service, using the same witness as W1. -/
theorem bankTrialC5ActualTimeoutNominatedBudgetHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (w : List (Fin n))
    (htime : bankTrialC5ActualTimeout ring root o w = true) :
    ∃ pre tail : List (Fin n), ∃ f : Fin n,
      w = pre ++ (f :: tail) ∧
      bankTrialC5ActualNominatedHits ring root o.after
        (pre ++ [f]) ≤ 2 * (compileAdvice q).b + 2 := by
  obtain ⟨pre, tail, f, hword, hall, _, _⟩ :=
    bankTrialC5ActualTimeoutAllPrefixUnresolved
      ring root o w htime
  have hstrict := bankTrialC5ActualUnresolvedPrefixNominatedStrict
    ring root S hsp hlarge hwidth hclean x e o ho pre hall
  have hsnoc := bankTrialC5ActualNominatedHitsSnoc
    ring root pre f o.after
  have hextra :
      (if f = bankTrialC5ActualNominatedEdge ring root
          (bankTrialLocalRun ring root pre o.after)
       then 1 else 0) ≤ 1 := by
    split <;> omega
  refine ⟨pre, tail, f, hword, ?_⟩
  omega

/-- C2. The W1 witness fixes ONE chronological pre-timeout
prefix. L1+W2 give W3 at precisely that prefix, W4 partitions
its incident services, and C1 includes the timeout edge in the
stopped penalty count. No physical Counter.Config adapter or
assumed leaf is used. -/
theorem bankTrialC5ActualTimeoutPenaltyCoverHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5ActualTimeoutPenaltyCover ring root S := by
  intro x e o ho w htime
  obtain ⟨pre, tail, f, hword, hall, hlease, hincident⟩ :=
    bankTrialC5ActualTimeoutAllPrefixUnresolved
      ring root o w htime
  have hlaunch := bankTrialC5ActualLaunchLeaseHolds
    ring root S hlarge hclean x e o ho
  have htelescope := bankTrialC5ActualPrefixLeaseIncidentTelescope
    ring root S hlarge x e o ho pre hall
  rw [hlaunch] at htelescope
  have hspent :
      13 * ((compileAdvice q).b + 2) ≤
        1 + bankTrialC5ActualIncidentCount ring root pre := by
    omega
  have hpartition := bankTrialC5ActualIncidentSplitBound
    ring root o.after pre
  have hstrict := bankTrialC5ActualUnresolvedPrefixNominatedStrict
    ring root S hsp hlarge hwidth hclean x e o ho pre hall
  have hpenSnoc := bankTrialC5ActualUntruncatedPenaltiesSnoc
    ring root pre f o.after
  have hnomSnoc := bankTrialC5ActualNominatedHitsSnoc
    ring root pre f o.after
  have htailWord : w = (pre ++ [f]) ++ tail := by
    rw [hword]
    simp only [List.append_assoc, List.singleton_append]
  have hcount := bankTrialC5ActualStoppedCountCoversEnd
    ring root pre tail f o.after
    (2 * (compileAdvice q).b + 2) hstrict
  rw [← htailWord] at hcount
  have hpaid := bankTrialC5ActualIncidentPaidOrNominated
    ring root (bankTrialLocalRun ring root pre o.after) f
  rw [if_pos hincident] at hpaid
  have hextra :
      (if f = bankTrialC5ActualNominatedEdge ring root
          (bankTrialLocalRun ring root pre o.after)
       then 1 else 0) ≤ 1 := by
    split <;> omega
  have hbudget :
      bankTrialC5ActualNominatedHits ring root o.after
        (pre ++ [f]) ≤ 2 * (compileAdvice q).b + 2 := by
    omega
  have hcharged :
      13 * ((compileAdvice q).b + 2) ≤
        CounterTrialLower.workerPenaltyCount
          (bankTrialLocalNext ring root)
          (bankTrialC5ActualNominatedEdge ring root)
          (bankTrialC5ActualPenaltyEdge ring root)
          o.after (2 * (compileAdvice q).b + 2) w +
        bankTrialC5ActualNominatedHits ring root o.after
          (pre ++ [f]) := by
    omega
  exact bankTrialC5ActualLeaseMargin
    (compileAdvice q).b
    (CounterTrialLower.workerPenaltyCount
      (bankTrialLocalNext ring root)
      (bankTrialC5ActualNominatedEdge ring root)
      (bankTrialC5ActualPenaltyEdge ring root)
      o.after (2 * (compileAdvice q).b + 2) w)
    (bankTrialC5ActualNominatedHits ring root o.after
      (pre ++ [f]))
    hcharged hbudget

/-- C3. The actual G11c kernel, with the final C.1 rarity
field obtained from BANK-local chronological accounting. -/
theorem bankTrialC5ActualWorkerExcursionKernelHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o : BankTrialC5ActualOrigin n q => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o : BankTrialC5ActualOrigin n q =>
        o.increment)
      (heads := fun o : BankTrialC5ActualOrigin n q => o.heads)
      ring root S := by
  exact bankTrialC5ActualWorkerExcursionKernelOfPenaltyCover
    ring root S hsp hlarge hwidth hclean
    (bankTrialC5ActualTimeoutPenaltyCoverHolds
      ring root S hsp hlarge hwidth hclean)

end L3
#print axioms L3.bankTrialC5RemainingLiveRowsHolds
#print axioms L3.bankTrialProbabilityC5CompletedHeadSoundHolds
#print axioms L3.bankTrialProbabilityThetaLowerOfCompletedHeadMass
#print axioms L3.bankTrialC5ActualNonreturnBadOfOwnerRows
#print axioms L3.bankTrialC5ActualOriginHeadCreditLeCount
#print axioms L3.bankTrialC5ActualTimeoutAppend
#print axioms L3.bankTrialC5ActualFirstBadTimeoutRowOfIncidentRows
#print axioms L3.bankTrialC5ActualOriginHeadCountExact
#print axioms L3.bankTrialC5ActualFirstBadRootIncident
#print axioms L3.bankTrialC5IncomingWaitBadFinish
#print axioms L3.bankTrialC5OutgoingWaitRawClassification
#print axioms L3.bankTrialC5ActualNonreturnBadOfOutgoing
#print axioms L3.bankTrialC5ActualOriginRunLedger
#print axioms L3.bankTrialC5ActualOriginChronologicalHeadLedger
#print axioms L3.bankTrialC5ActualHeadCountZeroBeforeFirstExit
#print axioms L3.bankTrialC5OutgoingWaitPhysicalCases
#print axioms L3.bankTrialC5ActualLaterArmedBad
#print axioms L3.bankTrialC5ActualNonreturnBadOfOutgoing
#print axioms L3.bankTrialC5OutgoingALReturnExact
#print axioms L3.bankTrialC5ActualCLZeroBeforeK
#print axioms L3.bankTrialC5CWaitCLoneCountExact
#print axioms L3.bankTrialC5ActualOutgoingBadFinishRowHolds
#print axioms L3.bankTrialC5ActualNonreturnBadHolds
#print axioms L3.bankTrialC5ActualCLZeroArmedAtOrigin
#print axioms L3.bankTrialC5ActualCoverageHolds
#print axioms L3.bankTrialC5ActualPrefixChargeOfModeEntry
#print axioms L3.bankTrialC5ActualStartCapOfModeEntry
#print axioms L3.bankTrialC5ActualGoodReturnOfModeEntry
#print axioms L3.bankTrialC5ActualStartsZeroOfInterstage
#print axioms L3.bankTrialC5ActualLiveModeEntryHolds
#print axioms L3.bankTrialC5ActualStartCapHolds
#print axioms L3.bankTrialC5ActualGoodReturnHolds
#print axioms L3.bankTrialC5ActualMeanOfFirstExitNominatedRank
#print axioms L3.bankTrialC5ActualBoundedMeanOfFirstExitWaveRows
#print axioms L3.bankTrialC5ActualWaveRankCap
#print axioms L3.bankTrialC5ActualFirstExitNoZeroRankOfRows
#print axioms L3.bankTrialC5ActualFirstExitCleanReachable
#print axioms L3.bankTrialC5ActualFirstExitLocked
#print axioms L3.bankTrialC5ActualFirstExitUniqueToken
#print axioms L3.bankTrialC5ActualFirstExitNoTopIR
#print axioms L3.bankTrialC5ActualOriginFirstTokenNonempty
#print axioms L3.bankTrialC5ActualIncomingWaveRankFrame
#print axioms L3.bankTrialC5ActualOutsideWaveRankFrame
#print axioms L3.bankTrialC5ActualTopWaveRankFrame
#print axioms L3.bankTrialC5ActualRawRootWaitTokenRankNonincrease
#print axioms L3.bankTrialC5ActualOutgoingWaveRankNonincrease
#print axioms L3.bankTrialC5ActualFirstExitRootRankNonincrease
#print axioms L3.bankTrialC5ActualFirstExitWorkerPersists
#print axioms L3.bankTrialC5ActualFirstExitWaveRowsHolds
#print axioms L3.bankTrialC5ActualBoundedMeanHolds
#print axioms L3.bankTrialC5ActualRarityConstantsAgree
#print axioms L3.bankTrialC5ActualConditionalRarityOfPhysicalMassBridge
#print axioms L3.bankTrialC5ActualWorkerExcursionKernelOfRarity
#print axioms L3.bankTrialC5ActualTimeoutHasStrictPrefixGuard
#print axioms L3.bankTrialC5ActualNonreturnBadHolds
#print axioms L3.bankTrialC5ActualTimeoutDependsOnlyOnAfter
#print axioms L3.bankTrialC5ActualNominatedEdgeDrop
#print axioms L3.bankTrialC5ActualNominatedFirstExitDrop
#print axioms L3.bankTrialC5ActualPenaltyDisjoint
#print axioms L3.bankTrialC5ActualPenaltyCardinality
#print axioms L3.bankTrialC5ActualBankPenaltyTail
#print axioms L3.bankTrialC5ActualLeaseMargin
#print axioms L3.bankTrialC5ActualConditionalRarityOfPenaltyCover
#print axioms L3.bankTrialC5ActualWorkerExcursionKernelOfPenaltyCover
#print axioms L3.bankTrialC5ActualLaunchLeaseHolds
#print axioms L3.bankTrialC5ActualUnresolvedNonincidentLeaseFrame
#print axioms L3.bankTrialC5ActualRawALReturnLeaseCollapse
#print axioms L3.bankTrialC5ActualNominatedHitsRankBound
#print axioms L3.bankTrialC5ActualNominatedHitsBeforeTimeoutBound
#print axioms L3.bankTrialC5ActualOriginPrefixLeaseCap
#print axioms L3.bankTrialC5ActualGuardedIncidentSpend
#print axioms L3.bankTrialC5ActualTimeoutPreLeaseAtMostOne
#print axioms L3.bankTrialC5ActualTimeoutAllPrefixUnresolved
#print axioms L3.bankTrialC5ActualIncidentCountAppend
#print axioms L3.bankTrialC5ActualPrefixLeaseIncidentTelescope
#print axioms L3.bankTrialC5ActualTimeoutIncidentLeaseBudget
#print axioms L3.bankTrialC5ActualIncidentPaidOrNominated
#print axioms L3.bankTrialC5ActualIncidentSplitBound
#print axioms L3.bankTrialC5ActualNonreturnBadHolds
#print axioms L3.bankTrialC5ActualGuardedIncidentSpend
#print axioms L3.bankTrialC5ActualNominatedHitsSnoc
#print axioms L3.bankTrialC5ActualUntruncatedPenaltiesSnoc
#print axioms L3.bankTrialC5ActualPenaltyPrefixLeStopped
#print axioms L3.bankTrialC5ActualStoppedCountCoversEnd
#print axioms L3.bankTrialC5ActualReachableOfUnresolvedPrefix
#print axioms L3.bankTrialC5ActualUnresolvedPrefixNominatedStrict
#print axioms L3.bankTrialC5ActualTimeoutNominatedBudgetHolds
#print axioms L3.bankTrialC5ActualTimeoutPenaltyCoverHolds
#print axioms L3.bankTrialC5ActualWorkerExcursionKernelHolds
