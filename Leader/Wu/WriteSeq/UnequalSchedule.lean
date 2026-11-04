import Leader.Wu.WriteSeq.UnequalPhases

/-!
# Complete arbitrary-width unequal WRITE_SEQ schedules

The lower-level unequal regression module proves mismatch discovery, clockwise
command transport, terminal activation, and the counterclockwise action sweep.
This module composes those phases into the complete target-group schedules and
then prepends the canonical one-group writer transport.
-/

namespace PPLLWriteSeqUnequalRegression

open PPLL PPLLWriteSeqPersistenceRepair
  PPLLWriteSeqPersistenceRegression

/-! ## Complete arbitrary-width unequal schedules

For a strict nonterminal mismatch, the real schedule compares the equal
prefix, discovers the command, transports it to the terminal component,
revisits the terminal edge to activate it, and executes the common backward
sweep. A terminal mismatch omits the two command-transport phases because its
discovery interaction activates the command immediately.
-/

/-- Complete action schedule when the first mismatch is strictly before the
terminal label. -/
def writerUnequalStrictActionSchedule {ψ : Nat} (hψ : 0 < ψ)
    (mismatch : Nat) : DetSchedule (2 * ψ) :=
  writerEqualPrefixSchedule hψ mismatch ++
    [genericWriterPos hψ (ψ + mismatch - 1)] ++
    writerUnequalCommandSchedule hψ mismatch (ψ - 1 - mismatch) ++
    [genericWriterPos hψ (ψ + (ψ - 1) - 1)] ++
    writerMoveFlipSchedule hψ (ψ - 1)

/-- **Complete strict-nonterminal unequal action.** The actual ring schedule
executes all five phases and retires every target component. Each final payload
and bit is the exact image of `writerUnequalPayload` and
`writerUnequalBit`; source bits, labels, and clean control frames survive. -/
theorem writerUnequalStrictActionSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcomparePrefix : ∀ k, k < mismatch →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hcompareMismatch :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + mismatch))).bit
        (payload mismatch).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerUnequalStrictActionSchedule (by omega) mismatch)
    WriterUnequalSweepState (by omega) reference D payload command ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let comparePrefix := writerEqualPrefixSchedule hp mismatch
  let discovery := genericWriterPos hp (ψ + mismatch - 1)
  let forward := writerUnequalCommandSchedule hp mismatch
    (ψ - 1 - mismatch)
  let terminal := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let backward := writerMoveFlipSchedule hp (ψ - 1)
  let C₁ := applySchedule ring T C comparePrefix
  have hprefix := writerEqualPrefixSchedule_reaches hψ C reference payload
    mismatch (by omega) hpayload hcomparePrefix hstate hclean hlabel hbit
  change WriterEqualPrefixState hp C₁ payload mismatch ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hprefix
  rcases hprefix with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
  let C₂ := stepConfig ring T C₁ discovery
  have hdiscovery := WriterEqualPrefixState.unequal_discovery_step hψ C₁
    reference payload mismatch comparison flag command hmismatch hpayload
    hpayloadFlag hcompareMismatch hdecision hstate₁ hclean₁ hlabel₁ hbit₁
  change WriterUnequalForwardState hp C₂ payload mismatch mismatch
      comparison ∧
    WriterCommandConfigurationFrame hp C₂ mismatch command ∧
    WriterLabelFrame hp C₂ ∧ WriterBitFrame reference C₂ at hdiscovery
  rcases hdiscovery with ⟨hstate₂, hframe₂, hlabel₂, hbit₂⟩
  let C₃ := applySchedule ring T C₂ forward
  have hforward := writerUnequalCommandSchedule_reaches hψ C₂ reference
    payload mismatch mismatch (ψ - 1 - mismatch) comparison flag command
    (by omega) hdecision hpayload hstate₂ hframe₂ hlabel₂ hbit₂
  change WriterUnequalForwardState hp C₃ payload mismatch
      (mismatch + (ψ - 1 - mismatch)) comparison ∧
    WriterCommandConfigurationFrame hp C₃
      (mismatch + (ψ - 1 - mismatch)) command ∧
    WriterLabelFrame hp C₃ ∧ WriterBitFrame reference C₃ at hforward
  have hfrontier : mismatch + (ψ - 1 - mismatch) = ψ - 1 := by omega
  rw [hfrontier] at hforward
  rcases hforward with ⟨hstate₃, hframe₃, hlabel₃, hbit₃⟩
  let C₄ := stepConfig ring T C₃ terminal
  have hterminal := WriterUnequalForwardState.command_terminal_step hψ C₃
    reference payload mismatch comparison flag command hmismatch hdecision
    hpayload hstate₃ hframe₃ hlabel₃ hbit₃
  change WriterUnequalSweepState hp reference C₄ payload command 1 ∧
    (∀ i, WriterTransportCleanFrame (C₄ i)) ∧
    WriterLabelFrame hp C₄ ∧ WriterSourceBitFrame hp reference C₄ at hterminal
  rcases hterminal with ⟨hstate₄, hclean₄, hlabel₄, hsourceBit₄⟩
  let D := applySchedule ring T C₄ backward
  have hbackward := writerUnequalSweepSchedule_reaches hψ C₄ reference
    payload comparison flag command (ψ - 1) (by omega) hdecision hpayload
    hstate₄ hclean₄ hlabel₄ hsourceBit₄
  change WriterUnequalSweepState hp reference D payload command
      (ψ - 1 + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D at hbackward
  have hdone : ψ - 1 + 1 = ψ := by omega
  rw [hdone] at hbackward
  change WriterUnequalSweepState hp reference
      (applySchedule ring T C (writerUnequalStrictActionSchedule hp mismatch))
      payload command ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerUnequalStrictActionSchedule hp mismatch) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerUnequalStrictActionSchedule hp mismatch)) ∧
    WriterSourceBitFrame hp reference
      (applySchedule ring T C (writerUnequalStrictActionSchedule hp mismatch))
  rw [writerUnequalStrictActionSchedule, applySchedule_append,
    applySchedule_append, applySchedule_append, applySchedule_append]
  simpa [applySchedule, comparePrefix, discovery, forward, terminal, backward,
    C₁, C₂, C₃, C₄, D, ring, T] using hbackward

/-- Complete action schedule when the first mismatch is the terminal label. -/
def writerUnequalTerminalActionSchedule {ψ : Nat} (hψ : 0 < ψ) :
    DetSchedule (2 * ψ) :=
  writerEqualPrefixSchedule hψ (ψ - 1) ++
    [genericWriterPos hψ (ψ + (ψ - 1) - 1)] ++
    writerMoveFlipSchedule hψ (ψ - 1)

/-- **Complete terminal unequal action.** The proper prefix compares equal,
the terminal mismatch selects and executes its command in one interaction, and
the common backward sweep retires the remaining components. -/
theorem writerUnequalTerminalActionSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcomparePrefix : ∀ k, k < ψ - 1 →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hcompareTerminal :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + (ψ - 1)))).bit
        (payload (ψ - 1)).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerUnequalTerminalActionSchedule (by omega))
    WriterUnequalSweepState (by omega) reference D payload command ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let comparePrefix := writerEqualPrefixSchedule hp (ψ - 1)
  let terminal := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let backward := writerMoveFlipSchedule hp (ψ - 1)
  let C₁ := applySchedule ring T C comparePrefix
  have hprefix := writerEqualPrefixSchedule_reaches hψ C reference payload
    (ψ - 1) (by omega) hpayload hcomparePrefix hstate hclean hlabel hbit
  change WriterEqualPrefixState hp C₁ payload (ψ - 1) ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hprefix
  rcases hprefix with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
  let C₂ := stepConfig ring T C₁ terminal
  have hterminal := WriterEqualPrefixState.unequal_terminal_step hψ C₁
    reference payload comparison flag command hdecision hpayload hpayloadFlag
    hcompareTerminal hstate₁ hclean₁ hlabel₁ hbit₁
  change WriterUnequalSweepState hp reference C₂ payload command 1 ∧
    (∀ i, WriterTransportCleanFrame (C₂ i)) ∧
    WriterLabelFrame hp C₂ ∧ WriterSourceBitFrame hp reference C₂ at hterminal
  rcases hterminal with ⟨hstate₂, hclean₂, hlabel₂, hsourceBit₂⟩
  let D := applySchedule ring T C₂ backward
  have hbackward := writerUnequalSweepSchedule_reaches hψ C₂ reference
    payload comparison flag command (ψ - 1) (by omega) hdecision hpayload
    hstate₂ hclean₂ hlabel₂ hsourceBit₂
  change WriterUnequalSweepState hp reference D payload command
      (ψ - 1 + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D at hbackward
  have hdone : ψ - 1 + 1 = ψ := by omega
  rw [hdone] at hbackward
  change WriterUnequalSweepState hp reference
      (applySchedule ring T C (writerUnequalTerminalActionSchedule hp))
      payload command ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerUnequalTerminalActionSchedule hp) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerUnequalTerminalActionSchedule hp)) ∧
    WriterSourceBitFrame hp reference
      (applySchedule ring T C (writerUnequalTerminalActionSchedule hp))
  rw [writerUnequalTerminalActionSchedule, applySchedule_append,
    applySchedule_append]
  simpa [applySchedule, comparePrefix, terminal, backward, C₁, C₂, D, ring,
    T] using hbackward

/-- Unified unequal-processing schedule, selecting the shorter direct terminal
route exactly when the first mismatch is terminal. -/
def writerUnequalActionSchedule {ψ : Nat} (hψ : 0 < ψ)
    (mismatch : Nat) : DetSchedule (2 * ψ) :=
  if mismatch = ψ - 1 then writerUnequalTerminalActionSchedule hψ
  else writerUnequalStrictActionSchedule hψ mismatch

/-- **All arbitrary-width unequal outcomes.** For any first mismatch label,
the selected actual-edge schedule executes exactly one of overwrite,
move-flip, or move across the complete writer. The endpoint is fully retired
and carries the exact command-dependent payload and physical-bit image. -/
theorem writerUnequalActionSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcomparePrefix : ∀ k, k < mismatch →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hcompareMismatch :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + mismatch))).bit
        (payload mismatch).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerUnequalActionSchedule (by omega) mismatch)
    WriterUnequalSweepState (by omega) reference D payload command ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  by_cases hterminal : mismatch = ψ - 1
  · subst mismatch
    simpa [writerUnequalActionSchedule] using
      writerUnequalTerminalActionSchedule_reaches hψ C reference payload
        comparison flag command hpayload hpayloadFlag hcomparePrefix
        hcompareMismatch hdecision hstate hclean hlabel hbit
  · have hstrict : mismatch < ψ - 1 := by omega
    simpa [writerUnequalActionSchedule, hterminal] using
      writerUnequalStrictActionSchedule_reaches hψ C reference payload
        mismatch comparison flag command hstrict hpayload hpayloadFlag
        hcomparePrefix hcompareMismatch hdecision hstate hclean hlabel hbit

/-- One source-to-target block crossing followed by the complete unequal action
at target group one. -/
def writerFirstUnequalSchedule {ψ : Nat} (hψ : 0 < ψ)
    (mismatch : Nat) : DetSchedule (2 * ψ) :=
  writerBlockTransportSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ ++
    writerUnequalActionSchedule hψ mismatch

/-- A clean source writer crosses into target group one and executes any of the
three unequal outcomes under one repaired lifecycle. This composes the full C4
writer route through first mismatch, command transport, action, and retirement.
-/
theorem writerFirstUnequalSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcomparePrefix : ∀ k, k < mismatch →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hcompareMismatch :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + mismatch))).bit
        (payload mismatch).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterRoundState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerFirstUnequalSchedule (by omega) mismatch)
    WriterUnequalSweepState (by omega) reference D payload command ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let transport := writerBlockTransportSchedule ring
    (genericWriterStart hp) ψ
  let C₁ := applySchedule ring T C transport
  have htransport := writerBlockTransportSchedule_from_zero hp C payload
    reference hpayload hstate hclean hlabel hbit
  change WriterRoundState hp C₁ payload ψ ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at htransport
  rcases htransport with ⟨hround, hclean₁, hlabel₁, hbit₁⟩
  have hequal : WriterEqualPrefixState hp C₁ payload 0 :=
    WriterRoundState.toEqualPrefix hp C₁ payload hround
  have haction := writerUnequalActionSchedule_reaches hψ C₁ reference
    payload mismatch comparison flag command hmismatch hpayload hpayloadFlag
    hcomparePrefix hcompareMismatch hdecision hequal hclean₁ hlabel₁ hbit₁
  change WriterUnequalSweepState hp reference
      (applySchedule ring T C (writerFirstUnequalSchedule hp mismatch))
      payload command ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerFirstUnequalSchedule hp mismatch) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerFirstUnequalSchedule hp mismatch)) ∧
    WriterSourceBitFrame hp reference
      (applySchedule ring T C (writerFirstUnequalSchedule hp mismatch))
  rw [writerFirstUnequalSchedule, applySchedule_append]
  simpa [transport, C₁, ring, T] using haction

end PPLLWriteSeqUnequalRegression
