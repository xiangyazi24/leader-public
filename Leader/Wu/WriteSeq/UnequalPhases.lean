import Leader.Wu.WriteSeq.PersistenceRegression

/-!
# Arbitrary-width unequal WRITE_SEQ schedules

The equal comparison branches already execute on arbitrary-width rings.  This
module treats the first unequal writer bit.  A mismatch creates one of the
three commands prescribed by Algorithm 16: overwrite for a flag-one `larger`
result, move-flip for a flag-zero `larger` result, or move for `less`.  The
repair transports that command clockwise to the terminal component, executes
it counterclockwise through the whole writer, and retires every component.

The original transition in `Leader.Wu.Protocol.Algorithm` remains unchanged.  All command
transport and stale-command retirement rules used here belong to the
separately named repair in `Leader.Wu.WriteSeq.PersistenceRepair`.
-/

namespace PPLLWriteSeqUnequalRegression

open PPLL PPLLWriteSeqPersistenceRepair
  PPLLWriteSeqPersistenceRegression

/-- A single nonempty command is attached to `frontier`; every other ring
position retains the ordinary clean writer-control frame.  This packages the
temporary exception to global cleanliness during clockwise command transport.
-/
def WriterCommandConfigurationFrame {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (frontier : Nat)
    (command : WriteAction) : Prop :=
  WriterTransportCommandFrame
      (C (genericWriterPos hψ (ψ + frontier))) command ∧
    ∀ i, i ≠ genericWriterPos hψ (ψ + frontier) →
      WriterTransportCleanFrame (C i)

/-- After the first mismatch at label `mismatch`, a command has advanced to
`frontier`.  Earlier equal comparison states remain to the left, the cell just
before the mismatch records the unequal result, traversed cells are `ready`,
the frontier is `depart`, and the untouched suffix is idle. -/
def WriterUnequalForwardState {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (mismatch frontier : Nat) (comparison : WriteState) : Prop :=
  mismatch ≤ frontier ∧ frontier < ψ ∧
    (C (genericWriterPos hψ (ψ - 1))).path3 = none ∧
    ∀ k, k < ψ →
      WriterTokenAt C (genericWriterPos hψ (ψ + k)) (payload k)
        (if k + 1 < mismatch then .equal
          else if k + 1 = mismatch then comparison
          else if k < frontier then .ready
          else if k = frontier then .depart else .none)

/-- After `processed` rightmost components have executed an unequal action,
the processed suffix has its exact payload/bit image and is retired.  The
frontier immediately to its left carries the action; all still earlier states
need only remain active, since they can be equal, unequal, or command-transport
`ready` states depending on where the first mismatch occurred. -/
def WriterUnequalSweepState {ψ : Nat} (hψ : 0 < ψ)
    (reference C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (command : WriteAction)
    (processed : Nat) : Prop :=
  1 ≤ processed ∧ processed ≤ ψ ∧
    (C (genericWriterPos hψ (ψ - 1))).path3 = none ∧
    ∀ k, k < ψ →
      (C (genericWriterPos hψ (ψ + k))).path3 =
          some (if k + processed < ψ then payload k
            else writerUnequalPayload command (payload k)) ∧
        (if k + processed + 1 < ψ then
            (C (genericWriterPos hψ (ψ + k))).write_state ≠ .none
          else if k + processed + 1 = ψ then
            (C (genericWriterPos hψ (ψ + k))).write_state =
              writeActionToState command
          else
            (C (genericWriterPos hψ (ψ + k))).write_state = .depart) ∧
        (C (genericWriterPos hψ (ψ + k))).bit =
          if k + processed < ψ then
            (reference (genericWriterPos hψ (ψ + k))).bit
          else writerUnequalBit command (payload k)
            (reference (genericWriterPos hψ (ψ + k))).bit

/-- Endpoint label/bit preservation lifts to an arbitrary ring without any
clean-frame premise.  This is used while one unequal command deliberately
violates the ordinary clean writer frame. -/
theorem stepConfig_global_label_bit_of_endpoint_contract {ψ n : Nat}
    (ring : DirectedRing n) (hn : 1 < n)
    (T : AgentState ψ → AgentState ψ →
      AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hleftLabel : (T (C e) (C (ring.rightNeighbor e))).1.label =
      (C e).label)
    (hrightLabel : (T (C e) (C (ring.rightNeighbor e))).2.label =
      (C (ring.rightNeighbor e)).label)
    (hleftBit : (T (C e) (C (ring.rightNeighbor e))).1.bit =
      (C e).bit)
    (hrightBit : (T (C e) (C (ring.rightNeighbor e))).2.bit =
      (C (ring.rightNeighbor e)).bit) :
    let D := stepConfig ring T C e
    ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  dsimp only
  intro i
  by_cases hi : i = e
  · subst i
    simpa [stepConfig] using And.intro hleftLabel hleftBit
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [stepConfig, hne] using And.intro hrightLabel hrightBit
    · simp [stepConfig, hi, hj]

/-- Endpoint label preservation lifts globally even when overwrite changes the
responder bit. -/
theorem stepConfig_global_label_of_endpoint_contract {ψ n : Nat}
    (ring : DirectedRing n) (hn : 1 < n)
    (T : AgentState ψ → AgentState ψ →
      AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hleftLabel : (T (C e) (C (ring.rightNeighbor e))).1.label =
      (C e).label)
    (hrightLabel : (T (C e) (C (ring.rightNeighbor e))).2.label =
      (C (ring.rightNeighbor e)).label) :
    let D := stepConfig ring T C e
    ∀ i, (D i).label = (C i).label := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  dsimp only
  intro i
  by_cases hi : i = e
  · subst i
    simpa [stepConfig] using hleftLabel
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [stepConfig, hne] using hrightLabel
    · simp [stepConfig, hi, hj]

/-! ## Lifting the mismatch discovery edge

The comparison schedule reaches an exact equal prefix before its first
mismatch. The next edge creates the corresponding command and is the only
point where the ordinary global clean frame is replaced by a one-command
configuration frame.
-/

/-- A mismatch at target label zero creates the command directly on that
component. The source-terminal predecessor remains pathless and clean, all
other target components remain idle, and labels and physical bits are framed.
-/
theorem writerUnequalSeedStep {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcompare :
      checkBitWS (reference (genericWriterPos (by omega) ψ)).bit
        (payload 0).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ - 1))
    WriterUnequalForwardState (by omega) D payload 0 0 comparison ∧
      WriterCommandConfigurationFrame (by omega) D 0 command ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ - 1)
  let j := genericWriterPos hp ψ
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    congr 2
    omega
  have hje : j ≠ e := by
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hDe : D e = (T (C e) (C j)).1 := by
    simp only [D, stepConfig, if_pos, hj]
  have hDj : D j = (T (C e) (C j)).2 := by
    simp only [D, stepConfig, hje, if_false, hj, if_true]
  have htoken := htokens 0 (by omega)
  have hsourcePath : (C e).path3 = none := by
    simpa [e] using hboundary
  have htargetPath : (C j).path3 = some (payload 0) := by
    simpa [j, WriterTokenAt] using htoken.1
  have htargetState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using htoken.2
  have htargetLabelVal : (C j).label.val = 0 := by
    simpa [j] using hlabel ψ (by omega)
  have htargetZero : (C j).label = ⟨0, hp⟩ := by
    apply Fin.ext
    exact htargetLabelVal
  have htargetAlign : (C j).label.val = (payload 0).label := by
    rw [htargetLabelVal, hpayload 0 (by omega)]
  have htargetCompare :
      checkBitWS (C j).bit (payload 0).bit = comparison := by
    rw [hbit j]
    simpa [j] using hcompare
  have htargetNotTerminal :
      (C j).label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hterminal
    have hv := congrArg Fin.val (htargetZero.symm.trans hterminal)
    simp only at hv
    omega
  have hdecisionZero :
      WriterUnequalCommand comparison (payload 0).flag command := by
    simpa [hpayloadFlag 0 (by omega)] using hdecision
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_unequal_seed hp
      (C e) (C j) (payload 0) comparison command hsourcePath htargetPath
      htargetState htargetZero htargetAlign htargetCompare hdecisionZero
      htargetNotTerminal (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPath, _, hleftLabel, hleftBit,
    hleftClean, hrightPath, hrightState, _, hrightLabel,
    hrightBit, hrightFrame⟩
  have hleftPathT : (T (C e) (C j)).1.path3 = none := by
    simpa only [T] using hleftPath
  have hrightPathT : (T (C e) (C j)).2.path3 = some (payload 0) := by
    simpa only [T] using hrightPath
  have hrightStateT : (T (C e) (C j)).2.write_state = .depart := by
    simpa only [T] using hrightState
  have hleftCleanT : WriterTransportCleanFrame (T (C e) (C j)).1 := by
    simpa only [T] using hleftClean
  have hrightFrameT :
      WriterTransportCommandFrame (T (C e) (C j)).2 command := by
    simpa only [T] using hrightFrame
  have hleftLabelT : (T (C e) (C j)).1.label = (C e).label := by
    simpa only [T] using hleftLabel
  have hrightLabelT : (T (C e) (C j)).2.label = (C j).label := by
    simpa only [T] using hrightLabel
  have hleftBitT : (T (C e) (C j)).1.bit = (C e).bit := by
    simpa only [T] using hleftBit
  have hrightBitT : (T (C e) (C j)).2.bit = (C j).bit := by
    simpa only [T] using hrightBit
  have hlabelBitAfter :=
    stepConfig_global_label_bit_of_endpoint_contract ring (by omega) T C e
      (by simpa [hj] using hleftLabelT)
      (by simpa [hj] using hrightLabelT)
      (by simpa [hj] using hleftBitT)
      (by simpa [hj] using hrightBitT)
  change WriterUnequalForwardState hp D payload 0 0 comparison ∧
    WriterCommandConfigurationFrame hp D 0 command ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [show genericWriterPos hp (ψ - 1) = e by rfl]
      rw [hDe]
      exact hleftPathT
    · intro k hk
      by_cases hk0 : k = 0
      · subst k
        change WriterTokenAt D (genericWriterPos hp (ψ + 0))
          (payload 0) .depart
        rw [show genericWriterPos hp (ψ + 0) = j by simp [j]]
        unfold WriterTokenAt
        rw [hDj]
        exact ⟨hrightPathT, hrightStateT⟩
      · have hsame : D (genericWriterPos hp (ψ + k)) =
            C (genericWriterPos hp (ψ + k)) := by
          apply stepConfig_eq_of_ne ring T C e
          · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
          · rw [hj]
            exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
        unfold WriterTokenAt
        rw [hsame]
        simpa [WriterTokenAt, hk0] using htokens k hk
  · constructor
    · rw [show genericWriterPos hp (ψ + 0) = j by simp [j]]
      rw [hDj]
      exact hrightFrameT
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hDe]
        exact hleftCleanT
      · have hij : i ≠ j := by
          simpa [j] using hi
        have hsame : D i = C i := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e i hie
            (by simpa [hj] using hij)
        rw [hsame]
        exact hclean i
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- A mismatch after a nonempty equal prefix creates the same command at its
discovery component. The predecessor records the unequal comparison result,
the new command frontier is the unique non-clean position, and the rest of the
writer is unchanged. -/
theorem writerUnequalNonterminalStep {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (count : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hcountPos : 0 < count) (hcount : count < ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcompare :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + count))).bit
        (payload count).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterEqualPrefixState (by omega) C payload count)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + count - 1))
    WriterUnequalForwardState (by omega) D payload count count comparison ∧
      WriterCommandConfigurationFrame (by omega) D count command ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + count - 1)
  let j := genericWriterPos hp (ψ + count)
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + count - 1 = ψ + (count - 1) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hje : j ≠ e := by
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hDe : D e = (T (C e) (C j)).1 := by
    simp only [D, stepConfig, if_pos, hj]
  have hDj : D j = (T (C e) (C j)).2 := by
    simp only [D, stepConfig, hje, if_false, hj, if_true]
  have hleftToken := htokens (count - 1) (by omega)
  have hrightToken := htokens count (by omega)
  have hleftPath : (C e).path3 = some (payload (count - 1)) := by
    simpa [e, WriterTokenAt, heIndex] using hleftToken.1
  have hleftState : (C e).write_state = .equal := by
    have hlt : count - 1 < count := by omega
    simpa [e, WriterTokenAt, heIndex, hlt] using hleftToken.2
  have hrightPath : (C j).path3 = some (payload count) := by
    simpa [j, WriterTokenAt] using hrightToken.1
  have hrightState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using hrightToken.2
  have hleftLabelVal : (C e).label.val = count - 1 := by
    calc
      (C e).label.val = (ψ + count - 1) % ψ := hlabel _ (by omega)
      _ = count - 1 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = count := by
    calc
      (C j).label.val = (ψ + count) % ψ := hlabel _ (by omega)
      _ = count := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload (count - 1)).label := by
    rw [hleftLabelVal, hpayload (count - 1) (by omega)]
  have hrightAlign : (C j).label.val = (payload count).label := by
    rw [hrightLabelVal, hpayload count (by omega)]
  have hrightCompare :
      checkBitWS (C j).bit (payload count).bit = comparison := by
    rw [hbit j]
    simpa [j] using hcompare
  have hleftCompare : (C e).label.val < ψ - 1 := by
    rw [hleftLabelVal]
    omega
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have hrightNotTerminal :
      (C j).label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hterminal
    have hv := congrArg Fin.val hterminal
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hdecisionCount :
      WriterUnequalCommand comparison (payload count).flag command := by
    simpa [hpayloadFlag count (by omega)] using hdecision
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_unequal_nonterminal hp
      (C e) (C j) (payload (count - 1)) (payload count) comparison
      command hleftPath hrightPath hleftState hrightState hleftAlign
      hrightAlign hrightCompare hdecisionCount hleftCompare hrightZero
      hrightNotTerminal horder (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    _, hrightLabelAfter, hrightBitAfter, hrightFrameAfter⟩
  have hleftPathT :
      (T (C e) (C j)).1.path3 = some (payload (count - 1)) := by
    simpa only [T] using hleftPathAfter
  have hleftStateT : (T (C e) (C j)).1.write_state = comparison := by
    simpa only [T] using hleftStateAfter
  have hrightPathT :
      (T (C e) (C j)).2.path3 = some (payload count) := by
    simpa only [T] using hrightPathAfter
  have hrightStateT : (T (C e) (C j)).2.write_state = .depart := by
    simpa only [T] using hrightStateAfter
  have hleftCleanT : WriterTransportCleanFrame (T (C e) (C j)).1 := by
    simpa only [T] using hleftCleanAfter
  have hrightFrameT :
      WriterTransportCommandFrame (T (C e) (C j)).2 command := by
    simpa only [T] using hrightFrameAfter
  have hleftLabelT : (T (C e) (C j)).1.label = (C e).label := by
    simpa only [T] using hleftLabelAfter
  have hrightLabelT : (T (C e) (C j)).2.label = (C j).label := by
    simpa only [T] using hrightLabelAfter
  have hleftBitT : (T (C e) (C j)).1.bit = (C e).bit := by
    simpa only [T] using hleftBitAfter
  have hrightBitT : (T (C e) (C j)).2.bit = (C j).bit := by
    simpa only [T] using hrightBitAfter
  have hlabelBitAfter :=
    stepConfig_global_label_bit_of_endpoint_contract ring (by omega) T C e
      (by simpa [hj] using hleftLabelT)
      (by simpa [hj] using hrightLabelT)
      (by simpa [hj] using hleftBitT)
      (by simpa [hj] using hrightBitT)
  change WriterUnequalForwardState hp D payload count count comparison ∧
    WriterCommandConfigurationFrame hp D count command ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hkc : k = count
      · subst k
        have hstateExpr :
            (if count + 1 < count then .equal
              else if count + 1 = count then comparison
              else if count < count then .ready
              else if count = count then .depart else .none) =
                WriteState.depart := by simp
        rw [hstateExpr]
        rw [show genericWriterPos hp (ψ + count) = j by rfl]
        unfold WriterTokenAt
        rw [hDj]
        exact ⟨hrightPathT, hrightStateT⟩
      · by_cases hkp : k = count - 1
        · subst k
          have hsum : count - 1 + 1 = count := by omega
          have hstateExpr :
              (if count - 1 + 1 < count then .equal
                else if count - 1 + 1 = count then comparison
                else if count - 1 < count then .ready
                else if count - 1 = count then .depart else .none) =
                  comparison := by simp [hsum]
          rw [hstateExpr]
          have hpos : genericWriterPos hp (ψ + (count - 1)) = e := by
            simp [e, heIndex]
          rw [hpos]
          change (D e).path3 = some (payload (count - 1)) ∧
            (D e).write_state = comparison
          rw [hDe]
          exact ⟨hleftPathT, hleftStateT⟩
        · have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          have hltIff : k + 1 < count ↔ k < count := by omega
          have hneMismatch : k + 1 ≠ count := by omega
          unfold WriterTokenAt
          rw [hsame]
          by_cases hlt : k < count
          · have hltOne : k + 1 < count := hltIff.mpr hlt
            simpa [WriterTokenAt, hlt, hltOne] using htokens k hk
          · have hnotOne : ¬k + 1 < count := by omega
            simpa [WriterTokenAt, hlt, hnotOne, hneMismatch, hkc] using
              htokens k hk
  · constructor
    · rw [show genericWriterPos hp (ψ + count) = j by rfl]
      rw [hDj]
      exact hrightFrameT
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hDe]
        exact hleftCleanT
      · have hij : i ≠ j := by
          simpa [j] using hi
        have hsame : D i = C i := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e i hie
            (by simpa [hj] using hij)
        rw [hsame]
        exact hclean i
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- Uniform mismatch-discovery theorem for every strict nonterminal label.
Label zero uses the pathless boundary edge; positive labels use the preceding
equal component. Both cases establish the same command-frontier invariant. -/
theorem WriterEqualPrefixState.unequal_discovery_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcompare :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + mismatch))).bit
        (payload mismatch).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterEqualPrefixState (by omega) C payload mismatch)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + mismatch - 1))
    WriterUnequalForwardState (by omega) D payload mismatch mismatch
        comparison ∧
      WriterCommandConfigurationFrame (by omega) D mismatch command ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  cases mismatch with
  | zero =>
      simpa using writerUnequalSeedStep hψ C reference payload comparison
        flag command hpayload hpayloadFlag hcompare hdecision hstate hclean
        hlabel hbit
  | succ mismatch =>
      exact writerUnequalNonterminalStep hψ C reference payload
        (mismatch + 1) comparison flag command (by omega) (by omega) hpayload
        hpayloadFlag hcompare hdecision hstate hclean hlabel hbit

/-! ## Clockwise command transport

Once a mismatch has selected an action, the command moves independently of
the frozen comparison prefix. Each clockwise edge cleans the old frontier and
makes its successor the unique command-bearing component.
-/

/-- One actual target-group edge advances an unequal command from `frontier`
to `frontier+1`, preserving the mismatch record, every payload, all labels,
and all physical bits. -/
theorem WriterUnequalForwardState.command_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch frontier : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hfrontier : frontier < ψ - 1)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalForwardState (by omega) C payload mismatch
      frontier comparison)
    (hframe : WriterCommandConfigurationFrame (by omega) C frontier command)
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + frontier))
    WriterUnequalForwardState (by omega) D payload mismatch
        (frontier + 1) comparison ∧
      WriterCommandConfigurationFrame (by omega) D (frontier + 1) command ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨hmf, hfψ, hboundary, htokens⟩
  rcases hframe with ⟨hfrontierFrame, hclean⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + frontier)
  let j := genericWriterPos hp (ψ + frontier + 1)
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hJIndex : ψ + frontier + 1 = ψ + (frontier + 1) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
  have hje : j ≠ e := by
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hDe : D e = (T (C e) (C j)).1 := by
    simp only [D, stepConfig, if_pos, hj]
  have hDj : D j = (T (C e) (C j)).2 := by
    simp only [D, stepConfig, hje, if_false, hj, if_true]
  have hleftToken := htokens frontier (by omega)
  have hrightToken := htokens (frontier + 1) (by omega)
  have hleftPath : (C e).path3 = some (payload frontier) := by
    simpa [e, WriterTokenAt] using hleftToken.1
  have hleftState : (C e).write_state = .depart := by
    have hnotBefore : ¬frontier + 1 < mismatch := by omega
    have hnotAtMismatch : frontier + 1 ≠ mismatch := by omega
    simpa [e, WriterTokenAt, hnotBefore, hnotAtMismatch] using
      hleftToken.2
  have hrightPath : (C j).path3 = some (payload (frontier + 1)) := by
    simpa [j, WriterTokenAt, hJIndex] using hrightToken.1
  have hrightState : (C j).write_state = .none := by
    have hnotBefore : ¬frontier + 1 + 1 < mismatch := by omega
    have hnotAtMismatch : frontier + 1 + 1 ≠ mismatch := by omega
    have hnotFrontier : ¬frontier + 1 < frontier := by omega
    simpa [j, WriterTokenAt, hJIndex, hnotBefore, hnotAtMismatch,
      hnotFrontier] using hrightToken.2
  have hleftLabelVal : (C e).label.val = frontier := by
    calc
      (C e).label.val = (ψ + frontier) % ψ := hlabel _ (by omega)
      _ = frontier := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = frontier + 1 := by
    calc
      (C j).label.val = (ψ + frontier + 1) % ψ := hlabel _ (by omega)
      _ = frontier + 1 := by
        rw [show ψ + frontier + 1 = ψ + (frontier + 1) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload frontier).label := by
    rw [hleftLabelVal, hpayload frontier (by omega)]
  have hrightAlign :
      (C j).label.val = (payload (frontier + 1)).label := by
    rw [hrightLabelVal, hpayload (frontier + 1) (by omega)]
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hrightClean : WriterTransportCleanFrame (C j) := by
    apply hclean j
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_command_forward hp
      (C e) (C j) (payload frontier) (payload (frontier + 1)) comparison
      flag command hleftPath hrightPath hleftState hrightState hleftAlign
      hrightAlign hrightZero horder hdecision
      (by simpa [e] using hfrontierFrame) hrightClean
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    _, hrightLabelAfter, hrightBitAfter, hrightFrameAfter⟩
  have hleftPathT : (T (C e) (C j)).1.path3 = some (payload frontier) := by
    simpa only [T] using hleftPathAfter
  have hleftStateT : (T (C e) (C j)).1.write_state = .ready := by
    simpa only [T] using hleftStateAfter
  have hrightPathT :
      (T (C e) (C j)).2.path3 = some (payload (frontier + 1)) := by
    simpa only [T] using hrightPathAfter
  have hrightStateT : (T (C e) (C j)).2.write_state = .depart := by
    simpa only [T] using hrightStateAfter
  have hleftCleanT : WriterTransportCleanFrame (T (C e) (C j)).1 := by
    simpa only [T] using hleftCleanAfter
  have hrightFrameT :
      WriterTransportCommandFrame (T (C e) (C j)).2 command := by
    simpa only [T] using hrightFrameAfter
  have hleftLabelT : (T (C e) (C j)).1.label = (C e).label := by
    simpa only [T] using hleftLabelAfter
  have hrightLabelT : (T (C e) (C j)).2.label = (C j).label := by
    simpa only [T] using hrightLabelAfter
  have hleftBitT : (T (C e) (C j)).1.bit = (C e).bit := by
    simpa only [T] using hleftBitAfter
  have hrightBitT : (T (C e) (C j)).2.bit = (C j).bit := by
    simpa only [T] using hrightBitAfter
  have hlabelBitAfter :=
    stepConfig_global_label_bit_of_endpoint_contract ring (by omega) T C e
      (by simpa [hj] using hleftLabelT)
      (by simpa [hj] using hrightLabelT)
      (by simpa [hj] using hleftBitT)
      (by simpa [hj] using hrightBitT)
  change WriterUnequalForwardState hp D payload mismatch (frontier + 1)
      comparison ∧
    WriterCommandConfigurationFrame hp D (frontier + 1) command ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hke : k = frontier
      · subst k
        have hnotBefore : ¬frontier + 1 < mismatch := by omega
        have hnotAtMismatch : frontier + 1 ≠ mismatch := by omega
        have hstateExpr :
            (if frontier + 1 < mismatch then .equal
              else if frontier + 1 = mismatch then comparison
              else if frontier < frontier + 1 then .ready
              else if frontier = frontier + 1 then .depart else .none) =
                WriteState.ready := by
          simp [hnotBefore, hnotAtMismatch]
        rw [hstateExpr]
        rw [show genericWriterPos hp (ψ + frontier) = e by rfl]
        change (D e).path3 = some (payload frontier) ∧
          (D e).write_state = .ready
        rw [hDe]
        exact ⟨hleftPathT, hleftStateT⟩
      · by_cases hkj : k = frontier + 1
        · subst k
          have hnotBefore : ¬frontier + 1 + 1 < mismatch := by omega
          have hnotAtMismatch : frontier + 1 + 1 ≠ mismatch := by omega
          have hstateExpr :
              (if frontier + 1 + 1 < mismatch then .equal
                else if frontier + 1 + 1 = mismatch then comparison
                else if frontier + 1 < frontier + 1 then .ready
                else if frontier + 1 = frontier + 1 then .depart
                else .none) = WriteState.depart := by
            simp [hnotBefore, hnotAtMismatch]
          rw [hstateExpr]
          have hpos : genericWriterPos hp (ψ + (frontier + 1)) = j := by
            simp [j, hJIndex]
          rw [hpos]
          change (D j).path3 = some (payload (frontier + 1)) ∧
            (D j).write_state = .depart
          rw [hDj]
          exact ⟨hrightPathT, hrightStateT⟩
        · have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          have hltFrontier : k < frontier + 1 ↔ k < frontier := by omega
          unfold WriterTokenAt
          rw [hsame]
          simpa [WriterTokenAt, hltFrontier, hke, hkj] using htokens k hk
  · constructor
    · have hpos : genericWriterPos hp (ψ + (frontier + 1)) = j := by
        simp [j, hJIndex]
      rw [hpos]
      rw [hDj]
      exact hrightFrameT
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hDe]
        exact hleftCleanT
      · have hij : i ≠ j := by
          simpa [j, hJIndex] using hi
        have hsame : D i = C i := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e i hie
            (by simpa [hj] using hij)
        rw [hsame]
        apply hclean i
        exact hie
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- The first `steps` clockwise command-handoff edges starting at a mismatch
frontier. Each listed initiator is the current command-bearing component. -/
def writerUnequalCommandSchedule {ψ : Nat} (hψ : 0 < ψ)
    (frontier : Nat) : Nat → DetSchedule (2 * ψ)
  | 0 => []
  | steps + 1 =>
      writerUnequalCommandSchedule hψ frontier steps ++
        [genericWriterPos hψ (ψ + frontier + steps)]

/-- Recursive composition of the physical command-forward edges. At the full
length `ψ-1-frontier`, the command is attached to the terminal component. -/
theorem writerUnequalCommandSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch frontier steps : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hsteps : steps ≤ ψ - 1 - frontier)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalForwardState (by omega) C payload mismatch
      frontier comparison)
    (hframe : WriterCommandConfigurationFrame (by omega) C frontier command)
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerUnequalCommandSchedule (by omega) frontier steps)
    WriterUnequalForwardState (by omega) D payload mismatch
        (frontier + steps) comparison ∧
      WriterCommandConfigurationFrame (by omega) D (frontier + steps)
        command ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  induction steps with
  | zero =>
      simpa [writerUnequalCommandSchedule, applySchedule] using
        And.intro hstate (And.intro hframe (And.intro hlabel hbit))
  | succ steps ih =>
      have hprev := ih (by omega) hstate hframe hlabel
      let hp : 0 < ψ := by omega
      let ring := genericWriterRing hp
      let T := writeSeqPersistentComparisonTransportLifecycle hp
      let C₁ := applySchedule ring T C
        (writerUnequalCommandSchedule hp frontier steps)
      change WriterUnequalForwardState hp C₁ payload mismatch
          (frontier + steps) comparison ∧
        WriterCommandConfigurationFrame hp C₁ (frontier + steps) command ∧
        WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hprev
      rcases hprev with ⟨hstate₁, hframe₁, hlabel₁, hbit₁⟩
      have hnext := WriterUnequalForwardState.command_step hψ C₁ reference
        payload mismatch (frontier + steps) comparison flag command
        (by omega) hdecision hpayload hstate₁ hframe₁ hlabel₁ hbit₁
      change WriterUnequalForwardState hp
          (stepConfig ring T C₁
            (genericWriterPos hp (ψ + (frontier + steps))))
          payload mismatch (frontier + steps + 1) comparison ∧
        WriterCommandConfigurationFrame hp
          (stepConfig ring T C₁
            (genericWriterPos hp (ψ + (frontier + steps))))
          (frontier + steps + 1) command ∧
        WriterLabelFrame hp
          (stepConfig ring T C₁
            (genericWriterPos hp (ψ + (frontier + steps)))) ∧
        WriterBitFrame reference
          (stepConfig ring T C₁
            (genericWriterPos hp (ψ + (frontier + steps)))) at hnext
      dsimp only
      rw [writerUnequalCommandSchedule, applySchedule_append]
      simpa [applySchedule, C₁, ring, T, Nat.add_assoc] using hnext

/-! ## Terminal activation and backward unequal action

The command-bearing terminal component consumes its command on the terminal
edge. This removes the sole temporary command-frame exception and starts a
uniform backward sweep whose unprocessed prefix need only remain active.
-/

/-- Pure projection of a terminal command frontier. A strict nonterminal
mismatch guarantees that the terminal predecessor is `ready`, the terminal is
`depart`, and every earlier component still has its original payload and a
non-idle state. No transition definition is unfolded here. -/
theorem WriterUnequalForwardState.frontier_terminal_facts {ψ : Nat}
    (hψ : 1 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState)
    (hmismatch : mismatch < ψ - 1)
    (hdecision : comparison = .larger ∨ comparison = .less)
    (hstate : WriterUnequalForwardState (by omega) C payload mismatch
      (ψ - 1) comparison) :
    (C (genericWriterPos (by omega) (ψ - 1))).path3 = none ∧
      WriterTokenAt C (genericWriterPos (by omega) (ψ + (ψ - 2)))
        (payload (ψ - 2)) .ready ∧
      WriterTokenAt C (genericWriterPos (by omega) (ψ + (ψ - 1)))
        (payload (ψ - 1)) .depart ∧
      ∀ k, k + 2 < ψ →
        (C (genericWriterPos (by omega) (ψ + k))).path3 = some (payload k) ∧
          (C (genericWriterPos (by omega) (ψ + k))).write_state ≠ .none := by
  rcases hstate with ⟨_, _, hboundary, htokens⟩
  refine ⟨hboundary, ?_, ?_, ?_⟩
  · have htoken := htokens (ψ - 2) (by omega)
    have hnotBefore : ¬ψ - 2 + 1 < mismatch := by omega
    have hnotAt : ψ - 2 + 1 ≠ mismatch := by omega
    have hbeforeFrontier : ψ - 2 < ψ - 1 := by omega
    simpa [WriterTokenAt, hnotBefore, hnotAt, hbeforeFrontier] using htoken
  · have htoken := htokens (ψ - 1) (by omega)
    have hnotBefore : ¬ψ - 1 + 1 < mismatch := by omega
    have hnotAt : ψ - 1 + 1 ≠ mismatch := by omega
    simpa [WriterTokenAt, hnotBefore, hnotAt] using htoken
  · intro k hk
    have htoken := htokens k (by omega)
    refine ⟨htoken.1, ?_⟩
    have hstateAt := htoken.2
    by_cases hbefore : k + 1 < mismatch
    · rw [if_pos hbefore] at hstateAt
      rw [hstateAt]
      decide
    · rw [if_neg hbefore] at hstateAt
      by_cases hat : k + 1 = mismatch
      · rw [if_pos hat] at hstateAt
        intro hnone
        have hcomparisonNone : comparison = .none :=
          hstateAt.symm.trans hnone
        rcases hdecision with hc | hc <;>
          rw [hc] at hcomparisonNone <;> cases hcomparisonNone
      · rw [if_neg hat] at hstateAt
        have hkFrontier : k < ψ - 1 := by omega
        rw [if_pos hkFrontier] at hstateAt
        rw [hstateAt]
        decide

/-- Componentwise characterization of the one-step unequal sweep base. Labels
strictly before the terminal predecessor are unchanged and active; the
predecessor carries the action; the terminal component has executed it. This
small constructor keeps the executable endpoint proof separate from arithmetic
normalization of the global invariant. -/
theorem WriterUnequalSweepState.one_of_components {ψ : Nat} (hψ : 1 < ψ)
    (reference C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (command : WriteAction)
    (hboundary : (C (genericWriterPos (by omega) (ψ - 1))).path3 = none)
    (hbefore : ∀ k, k + 2 < ψ →
      (C (genericWriterPos (by omega) (ψ + k))).path3 = some (payload k) ∧
        (C (genericWriterPos (by omega) (ψ + k))).write_state ≠ .none ∧
        (C (genericWriterPos (by omega) (ψ + k))).bit =
          (reference (genericWriterPos (by omega) (ψ + k))).bit)
    (hpredPath :
      (C (genericWriterPos (by omega) (ψ + (ψ - 2)))).path3 =
        some (payload (ψ - 2)))
    (hpredState :
      (C (genericWriterPos (by omega) (ψ + (ψ - 2)))).write_state =
        writeActionToState command)
    (hpredBit :
      (C (genericWriterPos (by omega) (ψ + (ψ - 2)))).bit =
        (reference (genericWriterPos (by omega) (ψ + (ψ - 2)))).bit)
    (hterminalPath :
      (C (genericWriterPos (by omega) (ψ + (ψ - 1)))).path3 =
        some (writerUnequalPayload command (payload (ψ - 1))))
    (hterminalState :
      (C (genericWriterPos (by omega) (ψ + (ψ - 1)))).write_state =
        .depart)
    (hterminalBit :
      (C (genericWriterPos (by omega) (ψ + (ψ - 1)))).bit =
        writerUnequalBit command (payload (ψ - 1))
          (reference (genericWriterPos (by omega) (ψ + (ψ - 1)))).bit) :
    WriterUnequalSweepState (by omega) reference C payload command 1 := by
  refine ⟨by omega, by omega, hboundary, ?_⟩
  intro k hk
  by_cases hearly : k + 2 < ψ
  · have hunprocessed : k + 1 < ψ := by omega
    simp only [hunprocessed, if_true, hearly]
    exact hbefore k hearly
  · have hkCases : k = ψ - 2 ∨ k = ψ - 1 := by omega
    rcases hkCases with rfl | rfl
    · have hpredUnprocessed : ψ - 2 + 1 < ψ := by omega
      have hpredFrontier : ψ - 2 + 1 + 1 = ψ := by omega
      have hpredNotEarly : ¬ψ < ψ := Nat.lt_irrefl ψ
      simp only [hpredUnprocessed, if_true, hpredFrontier,
        hpredNotEarly, if_false]
      exact ⟨hpredPath, hpredState, hpredBit⟩
    · have hterminalDone : ψ - 1 + 1 = ψ := by omega
      have hterminalLate : ¬ψ + 1 < ψ := by omega
      have hterminalNotFrontier : ψ + 1 ≠ ψ := by omega
      simp only [hterminalDone, Nat.lt_irrefl, if_false,
        hterminalLate, hterminalNotFrontier]
      exact ⟨hterminalPath, hterminalState, hterminalBit⟩

/-- Exact two-endpoint result of terminal command activation, stated directly
on the updated configuration so later configuration proofs never unfold the
full local lifecycle. -/
structure WriterUnequalTerminalPairResult {ψ : Nat} (hψ : 0 < ψ)
    (reference before D : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (command : WriteAction) : Prop where
  predPath :
    (D (genericWriterPos hψ (ψ + (ψ - 2)))).path3 = some (payload (ψ - 2))
  predState :
    (D (genericWriterPos hψ (ψ + (ψ - 2)))).write_state =
      writeActionToState command
  predBit :
    (D (genericWriterPos hψ (ψ + (ψ - 2)))).bit =
      (reference (genericWriterPos hψ (ψ + (ψ - 2)))).bit
  predClean :
    WriterTransportCleanFrame (D (genericWriterPos hψ (ψ + (ψ - 2))))
  predLabelEq :
    (D (genericWriterPos hψ (ψ + (ψ - 2)))).label =
      (before (genericWriterPos hψ (ψ + (ψ - 2)))).label
  predLabel :
    (D (genericWriterPos hψ (ψ + (ψ - 2)))).label.val = ψ - 2
  terminalPath :
    (D (genericWriterPos hψ (ψ + (ψ - 1)))).path3 =
      some (writerUnequalPayload command (payload (ψ - 1)))
  terminalState :
    (D (genericWriterPos hψ (ψ + (ψ - 1)))).write_state = .depart
  terminalBit :
    (D (genericWriterPos hψ (ψ + (ψ - 1)))).bit =
      writerUnequalBit command (payload (ψ - 1))
        (reference (genericWriterPos hψ (ψ + (ψ - 1)))).bit
  terminalClean :
    WriterTransportCleanFrame (D (genericWriterPos hψ (ψ + (ψ - 1))))
  terminalLabelEq :
    (D (genericWriterPos hψ (ψ + (ψ - 1)))).label =
      (before (genericWriterPos hψ (ψ + (ψ - 1)))).label
  terminalLabel :
    (D (genericWriterPos hψ (ψ + (ψ - 1)))).label.val = ψ - 1

/-- The repaired local terminal contract lifted only to the two scheduled
configuration positions. All global locality and invariant reconstruction are
deliberately postponed to separate lemmas. -/
theorem writerUnequalCommandTerminalPairResult {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ - 1)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalForwardState (by omega) C payload mismatch
      (ψ - 1) comparison)
    (hframe : WriterCommandConfigurationFrame (by omega) C (ψ - 1)
      command)
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + (ψ - 1) - 1))
    WriterUnequalTerminalPairResult (by omega) reference C D payload
      command := by
  have hcomparison : comparison = .larger ∨ comparison = .less := by
    rcases hdecision with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨_, hpredToken, hterminalToken, _⟩ :=
    WriterUnequalForwardState.frontier_terminal_facts hψ C payload mismatch
      comparison hmismatch hcomparison hstate
  rcases hframe with ⟨hterminalFrame, hclean⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + (ψ - 2))
  let j := genericWriterPos hp (ψ + (ψ - 1))
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heSchedule : genericWriterPos hp (ψ + (ψ - 1) - 1) = e := by
    simp [e]
    congr 2
    omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hje : j ≠ e := by
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hDe : D e = (T (C e) (C j)).1 := by
    simp only [D, stepConfig, if_pos, hj]
  have hDj : D j = (T (C e) (C j)).2 := by
    simp only [D, stepConfig, hje, if_false, hj, if_true]
  have hleftPath : (C e).path3 = some (payload (ψ - 2)) := by
    simpa [e, WriterTokenAt] using hpredToken.1
  have hleftState : (C e).write_state = .ready := by
    simpa [e, WriterTokenAt] using hpredToken.2
  have hrightPath : (C j).path3 = some (payload (ψ - 1)) := by
    simpa [j, WriterTokenAt] using hterminalToken.1
  have hrightState : (C j).write_state = .depart := by
    simpa [j, WriterTokenAt] using hterminalToken.2
  have hleftLabelVal : (C e).label.val = ψ - 2 := by
    calc
      (C e).label.val = (ψ + (ψ - 2)) % ψ := hlabel _ (by omega)
      _ = ψ - 2 := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = ψ - 1 := by
    calc
      (C j).label.val = (ψ + (ψ - 1)) % ψ := hlabel _ (by omega)
      _ = ψ - 1 := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload (ψ - 2)).label := by
    rw [hleftLabelVal, hpayload (ψ - 2) (by omega)]
  have hrightAlign : (C j).label.val = (payload (ψ - 1)).label := by
    rw [hrightLabelVal, hpayload (ψ - 1) (by omega)]
  have hrightTerminal : (C j).label = ⟨ψ - 1, by omega⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val (hzero.symm.trans hrightTerminal)
    simp only at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hleftClean : WriterTransportCleanFrame (C e) := by
    apply hclean e
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hrightFrame : WriterTransportCommandFrame (C j) command := by
    simpa [j] using hterminalFrame
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_command_terminal hp
      (C e) (C j) (payload (ψ - 2)) (payload (ψ - 1)) comparison flag
      command hleftPath hrightPath hleftState hrightState hleftAlign
      hrightAlign hdecision hrightTerminal hrightZero horder hleftClean
      hrightFrame
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hpredPos : genericWriterPos hp (ψ + (ψ - 2)) = e := by rfl
  have hterminalPos : genericWriterPos hp (ψ + (ψ - 1)) = j := by rfl
  have hStepE : stepConfig ring T C e e = (T (C e) (C j)).1 := by
    simpa only [D] using hDe
  have hStepJ : stepConfig ring T C e j = (T (C e) (C j)).2 := by
    simpa only [D] using hDj
  change WriterUnequalTerminalPairResult hp reference C
    (stepConfig ring T C (genericWriterPos hp (ψ + (ψ - 1) - 1)))
      payload command
  rw [heSchedule]
  refine
    { predPath := by rw [hpredPos, hStepE]; simpa only [T] using hleftPathAfter
      predState := by rw [hpredPos, hStepE]; simpa only [T] using hleftStateAfter
      predBit := by
        rw [hpredPos, hStepE]
        simpa only [T] using hleftBitAfter.trans (hbit e)
      predClean := by rw [hpredPos, hStepE]; simpa only [T] using hleftCleanAfter
      predLabelEq := by rw [hpredPos, hStepE]; simpa only [T] using hleftLabelAfter
      predLabel := by
        rw [hpredPos, hStepE]
        calc
          (T (C e) (C j)).1.label.val = (C e).label.val := by
            rw [show (T (C e) (C j)).1.label = (C e).label by
              simpa only [T] using hleftLabelAfter]
          _ = ψ - 2 := hleftLabelVal
      terminalPath := by
        rw [hterminalPos, hStepJ]
        simpa only [T] using hrightPathAfter
      terminalState := by
        rw [hterminalPos, hStepJ]
        simpa only [T] using hrightStateAfter
      terminalBit := by
        rw [hterminalPos, hStepJ]
        simpa only [T] using hrightBitAfter.trans (by
          rw [hbit j])
      terminalClean := by
        rw [hterminalPos, hStepJ]
        simpa only [T] using hrightCleanAfter
      terminalLabelEq := by
        rw [hterminalPos, hStepJ]
        simpa only [T] using hrightLabelAfter
      terminalLabel := by
        rw [hterminalPos, hStepJ]
        calc
          (T (C e) (C j)).2.label.val = (C j).label.val := by
            rw [show (T (C e) (C j)).2.label = (C j).label by
              simpa only [T] using hrightLabelAfter]
          _ = ψ - 1 := hrightLabelVal }

/-- A first mismatch discovered at the terminal component creates and executes
its unequal command in the same interaction. This is the terminal analogue of
`writerUnequalCommandTerminalPairResult`, with no clockwise command phase. -/
theorem writerUnequalDirectTerminalPairResult {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcompare :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + (ψ - 1)))).bit
        (payload (ψ - 1)).bit = comparison)
    (hstate : WriterEqualPrefixState (by omega) C payload (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + (ψ - 1) - 1))
    WriterUnequalTerminalPairResult (by omega) reference C D payload
      command := by
  rcases hstate with ⟨_, _, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + (ψ - 2))
  let j := genericWriterPos hp (ψ + (ψ - 1))
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heSchedule : genericWriterPos hp (ψ + (ψ - 1) - 1) = e := by
    simp [e]
    congr 2
    omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hje : j ≠ e := by
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hStepE : stepConfig ring T C e e = (T (C e) (C j)).1 := by
    simp [stepConfig, hj]
  have hStepJ : stepConfig ring T C e j = (T (C e) (C j)).2 := by
    simp [stepConfig, hj, hje]
  have hleftToken := htokens (ψ - 2) (by omega)
  have hrightToken := htokens (ψ - 1) (by omega)
  have hleftPath : (C e).path3 = some (payload (ψ - 2)) := by
    simpa [e, WriterTokenAt] using hleftToken.1
  have hleftState : (C e).write_state = .equal := by
    have hlt : ψ - 2 < ψ - 1 := by omega
    simpa [e, WriterTokenAt, hlt] using hleftToken.2
  have hrightPath : (C j).path3 = some (payload (ψ - 1)) := by
    simpa [j, WriterTokenAt] using hrightToken.1
  have hrightState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using hrightToken.2
  have hleftLabelVal : (C e).label.val = ψ - 2 := by
    calc
      (C e).label.val = (ψ + (ψ - 2)) % ψ := hlabel _ (by omega)
      _ = ψ - 2 := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = ψ - 1 := by
    calc
      (C j).label.val = (ψ + (ψ - 1)) % ψ := hlabel _ (by omega)
      _ = ψ - 1 := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload (ψ - 2)).label := by
    rw [hleftLabelVal, hpayload (ψ - 2) (by omega)]
  have hrightAlign : (C j).label.val = (payload (ψ - 1)).label := by
    rw [hrightLabelVal, hpayload (ψ - 1) (by omega)]
  have hrightCompare :
      checkBitWS (C j).bit (payload (ψ - 1)).bit = comparison := by
    rw [hbit j]
    simpa [j] using hcompare
  have hrightTerminal : (C j).label = ⟨ψ - 1, by omega⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val (hzero.symm.trans hrightTerminal)
    simp only at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hdecisionTerminal :
      WriterUnequalCommand comparison (payload (ψ - 1)).flag command := by
    simpa [hpayloadFlag (ψ - 1) (by omega)] using hdecision
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_unequal_terminal hp
      (C e) (C j) (payload (ψ - 2)) (payload (ψ - 1)) comparison
      command hleftPath hrightPath hleftState hrightState hleftAlign
      hrightAlign hrightCompare hdecisionTerminal (by omega) hrightTerminal
      hrightZero horder (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  change WriterUnequalTerminalPairResult hp reference C
    (stepConfig ring T C (genericWriterPos hp (ψ + (ψ - 1) - 1)))
      payload command
  rw [heSchedule]
  refine
    { predPath := by rw [hStepE]; simpa only [T] using hleftPathAfter
      predState := by rw [hStepE]; simpa only [T] using hleftStateAfter
      predBit := by
        rw [hStepE]
        simpa only [T] using hleftBitAfter.trans (hbit e)
      predClean := by rw [hStepE]; simpa only [T] using hleftCleanAfter
      predLabelEq := by rw [hStepE]; simpa only [T] using hleftLabelAfter
      predLabel := by
        rw [hStepE]
        calc
          (T (C e) (C j)).1.label.val = (C e).label.val := by
            rw [show (T (C e) (C j)).1.label = (C e).label by
              simpa only [T] using hleftLabelAfter]
          _ = ψ - 2 := hleftLabelVal
      terminalPath := by rw [hStepJ]; simpa only [T] using hrightPathAfter
      terminalState := by rw [hStepJ]; simpa only [T] using hrightStateAfter
      terminalBit := by
        rw [hStepJ]
        simpa only [T] using hrightBitAfter.trans (by rw [hbit j])
      terminalClean := by rw [hStepJ]; simpa only [T] using hrightCleanAfter
      terminalLabelEq := by rw [hStepJ]; simpa only [T] using hrightLabelAfter
      terminalLabel := by
        rw [hStepJ]
        calc
          (T (C e) (C j)).2.label.val = (C j).label.val := by
            rw [show (T (C e) (C j)).2.label = (C j).label by
              simpa only [T] using hrightLabelAfter]
          _ = ψ - 1 := hrightLabelVal }

/-- A terminal first mismatch establishes the same one-component backward
action invariant as a transported command, but the mismatch edge itself both
selects and executes the terminal action. -/
theorem WriterEqualPrefixState.unequal_terminal_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcompare :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + (ψ - 1)))).bit
        (payload (ψ - 1)).bit = comparison)
    (hstate : WriterEqualPrefixState (by omega) C payload (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + (ψ - 1) - 1))
    WriterUnequalSweepState (by omega) reference D payload command 1 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  have hstateCopy := hstate
  rcases hstateCopy with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let j := genericWriterPos hp (ψ + (ψ - 1))
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hePos : genericWriterPos hp (ψ + (ψ - 2)) = e := by
    simp [e]
    congr 2
    omega
  have hjPos : genericWriterPos hp (ψ + (ψ - 1)) = j := by rfl
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hpair := writerUnequalDirectTerminalPairResult hψ C reference payload
    comparison flag command hdecision hpayload hpayloadFlag hcompare hstate
    hclean hlabel hbit
  change WriterUnequalTerminalPairResult hp reference C D payload command at hpair
  have hboundaryD :
      (D (genericWriterPos hp (ψ - 1))).path3 = none := by
    have hsame : D (genericWriterPos hp (ψ - 1)) =
        C (genericWriterPos hp (ψ - 1)) := by
      apply stepConfig_eq_of_ne ring T C e
      · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      · rw [hj]
        exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    rw [hsame]
    exact hboundary
  have hbeforeD : ∀ k, k + 2 < ψ →
      (D (genericWriterPos hp (ψ + k))).path3 = some (payload k) ∧
        (D (genericWriterPos hp (ψ + k))).write_state ≠ .none ∧
        (D (genericWriterPos hp (ψ + k))).bit =
          (reference (genericWriterPos hp (ψ + k))).bit := by
    intro k hk
    have hsame : D (genericWriterPos hp (ψ + k)) =
        C (genericWriterPos hp (ψ + k)) := by
      apply stepConfig_eq_of_ne ring T C e
      · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      · rw [hj]
        exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    rw [hsame]
    have htoken := htokens k (by omega)
    have hkEqual : k < ψ - 1 := by omega
    refine ⟨htoken.1, ?_, hbit _⟩
    rw [show (C (genericWriterPos hp (ψ + k))).write_state = .equal by
      simpa [WriterTokenAt, hkEqual] using htoken.2]
    decide
  have hsweep := WriterUnequalSweepState.one_of_components hψ reference D
    payload command hboundaryD hbeforeD hpair.predPath hpair.predState
    hpair.predBit hpair.terminalPath hpair.terminalState hpair.terminalBit
  have hcleanAfter : ∀ i, WriterTransportCleanFrame (D i) := by
    intro i
    by_cases hie : i = e
    · subst i
      simpa only [hePos] using hpair.predClean
    · by_cases hij : i = j
      · subst i
        simpa only [hjPos] using hpair.terminalClean
      · have hsame : D i = C i := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e i hie
            (by simpa [hj] using hij)
        rw [hsame]
        exact hclean i
  change WriterUnequalSweepState hp reference D payload command 1 ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨hsweep, hcleanAfter, ?_, ?_⟩
  · intro x hx
    by_cases hxe : genericWriterPos hp x = e
    · have hEqLabel : (D e).label = (C e).label := by
        simpa only [hePos] using hpair.predLabelEq
      rw [show (D (genericWriterPos hp x)).label =
          (C (genericWriterPos hp x)).label by
        rw [hxe]
        exact hEqLabel]
      exact hlabel x hx
    · by_cases hxj : genericWriterPos hp x = j
      · have hEqLabel : (D j).label = (C j).label := by
          simpa only [hjPos] using hpair.terminalLabelEq
        rw [show (D (genericWriterPos hp x)).label =
            (C (genericWriterPos hp x)).label by
          rw [hxj]
          exact hEqLabel]
        exact hlabel x hx
      · have hsame : D (genericWriterPos hp x) = C (genericWriterPos hp x) := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e _ hxe
            (by simpa [hj] using hxj)
        rw [hsame]
        exact hlabel x hx
  · intro k hk
    have hsourceNeE : genericWriterPos hp k ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    have hsourceNeJ : genericWriterPos hp k ≠ j :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
      dsimp only [D]
      exact stepConfig_eq_of_ne ring T C e _ hsourceNeE
        (by simpa [hj] using hsourceNeJ)
    rw [hsame, hbit]

/-- A command transported from a strict nonterminal mismatch activates at the
terminal component. The terminal payload receives the exact unequal action,
its predecessor carries the corresponding action state, and global cleanliness
is restored. -/
theorem WriterUnequalForwardState.command_terminal_step {ψ : Nat}
    (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ - 1)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalForwardState (by omega) C payload mismatch
      (ψ - 1) comparison)
    (hframe : WriterCommandConfigurationFrame (by omega) C (ψ - 1)
      command)
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + (ψ - 1) - 1))
    WriterUnequalSweepState (by omega) reference D payload command 1 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  have hcomparison : comparison = .larger ∨ comparison = .less := by
    rcases hdecision with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hboundary, _, _, hbefore⟩ :=
    WriterUnequalForwardState.frontier_terminal_facts hψ C payload mismatch
      comparison hmismatch hcomparison hstate
  have hclean := hframe.2
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let j := genericWriterPos hp (ψ + (ψ - 1))
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hePos : genericWriterPos hp (ψ + (ψ - 2)) = e := by
    simp [e]
    congr 2
    omega
  have hjPos : genericWriterPos hp (ψ + (ψ - 1)) = j := by rfl
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hje : j ≠ e := by
    exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
  have hDe : D e = (T (C e) (C j)).1 := by
    simp only [D, stepConfig, if_pos, hj]
  have hDj : D j = (T (C e) (C j)).2 := by
    simp only [D, stepConfig, hje, if_false, hj, if_true]
  have hpair := writerUnequalCommandTerminalPairResult hψ C reference payload
    mismatch comparison flag command hmismatch hdecision hpayload hstate
    hframe hlabel hbit
  change WriterUnequalTerminalPairResult hp reference C D payload command at hpair
  have hboundaryD :
      (D (genericWriterPos hp (ψ - 1))).path3 = none := by
    have hsame : D (genericWriterPos hp (ψ - 1)) =
        C (genericWriterPos hp (ψ - 1)) := by
      apply stepConfig_eq_of_ne ring T C e
      · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      · rw [hj]
        exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    rw [hsame]
    exact hboundary
  have hbeforeD : ∀ k, k + 2 < ψ →
      (D (genericWriterPos hp (ψ + k))).path3 = some (payload k) ∧
        (D (genericWriterPos hp (ψ + k))).write_state ≠ .none ∧
        (D (genericWriterPos hp (ψ + k))).bit =
          (reference (genericWriterPos hp (ψ + k))).bit := by
    intro k hk
    have hsame : D (genericWriterPos hp (ψ + k)) =
        C (genericWriterPos hp (ψ + k)) := by
      apply stepConfig_eq_of_ne ring T C e
      · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      · rw [hj]
        exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    rw [hsame]
    exact ⟨(hbefore k hk).1, (hbefore k hk).2, hbit _⟩
  have hsweep := WriterUnequalSweepState.one_of_components hψ reference D
    payload command hboundaryD hbeforeD hpair.predPath hpair.predState
    hpair.predBit hpair.terminalPath hpair.terminalState hpair.terminalBit
  have hcleanAfter : ∀ i, WriterTransportCleanFrame (D i) := by
    intro i
    by_cases hie : i = e
    · subst i
      simpa only [hePos] using hpair.predClean
    · by_cases hij : i = j
      · subst i
        simpa only [hjPos] using hpair.terminalClean
      · have hsame : D i = C i := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e i hie
            (by simpa [hj] using hij)
        rw [hsame]
        apply hclean i
        simpa [j] using hij
  change WriterUnequalSweepState hp reference D payload command 1 ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨hsweep, hcleanAfter, ?_, ?_⟩
  · intro x hx
    by_cases hxe : genericWriterPos hp x = e
    · have hEqLabel : (D e).label = (C e).label := by
        simpa only [hePos] using hpair.predLabelEq
      rw [show (D (genericWriterPos hp x)).label =
          (C (genericWriterPos hp x)).label by
        rw [hxe]
        exact hEqLabel]
      exact hlabel x hx
    · by_cases hxj : genericWriterPos hp x = j
      · have hEqLabel : (D j).label = (C j).label := by
          simpa only [hjPos] using hpair.terminalLabelEq
        rw [show (D (genericWriterPos hp x)).label =
            (C (genericWriterPos hp x)).label by
          rw [hxj]
          exact hEqLabel]
        exact hlabel x hx
      · have hsame : D (genericWriterPos hp x) = C (genericWriterPos hp x) := by
          dsimp only [D]
          exact stepConfig_eq_of_ne ring T C e _ hxe
            (by simpa [hj] using hxj)
        rw [hsame]
        exact hlabel x hx
  · intro k hk
    have hsourceNeE : genericWriterPos hp k ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    have hsourceNeJ : genericWriterPos hp k ≠ j :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
      dsimp only [D]
      exact stepConfig_eq_of_ne ring T C e _ hsourceNeE
        (by simpa [hj] using hsourceNeJ)
    rw [hsame, hbit]

/-- While the unequal-action frontier has positive label, one actual
counterclockwise edge executes the action at the old frontier and hands its
state to the active predecessor. The exact command-dependent payload and bit
image grows by one component. -/
theorem WriterUnequalSweepState.nonzero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction) (processed : Nat)
    (hprocessed : processed < ψ - 1)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalSweepState (by omega) reference C payload command
      processed)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hsourceBit : WriterSourceBitFrame (by omega) reference C) :
    let frontier := ψ - processed - 1
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + frontier - 1))
    WriterUnequalSweepState (by omega) reference D payload command
        (processed + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  rcases hstate with ⟨hprocessedPos, hprocessedLe, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let frontier := ψ - processed - 1
  have hfrontierPos : 0 < frontier := by
    dsimp only [frontier]
    omega
  have hfrontierLt : frontier < ψ := by
    dsimp only [frontier]
    omega
  have hfrontierSum : frontier + processed + 1 = ψ := by
    dsimp only [frontier]
    omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + frontier - 1)
  let j := genericWriterPos hp (ψ + frontier)
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + frontier - 1 = ψ + (frontier - 1) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hleftData := htokens (frontier - 1) (by omega)
  have hrightData := htokens frontier hfrontierLt
  have hleftPayloadOld : frontier - 1 + processed < ψ := by omega
  have hleftStateOld : frontier - 1 + processed + 1 < ψ := by omega
  have hrightPayloadOld : frontier + processed < ψ := by omega
  have hrightStateNotEarly : ¬frontier + processed + 1 < ψ := by omega
  have hrightStateFrontier : frontier + processed + 1 = ψ := hfrontierSum
  have hleftPath : (C e).path3 = some (payload (frontier - 1)) := by
    simpa [e, heIndex, hleftPayloadOld] using hleftData.1
  let prior := (C e).write_state
  have hprior : prior ≠ .none := by
    simpa [prior, e, heIndex, hleftPayloadOld, hleftStateOld] using
      hleftData.2.1
  have hrightPath : (C j).path3 = some (payload frontier) := by
    simpa [j, hrightPayloadOld] using hrightData.1
  have hrightState : (C j).write_state = writeActionToState command := by
    simpa [j, hrightPayloadOld, hrightStateNotEarly,
      hrightStateFrontier] using hrightData.2.1
  have hleftBitOld : (C e).bit =
      (reference (genericWriterPos hp (ψ + (frontier - 1)))).bit := by
    simpa [e, heIndex, hleftPayloadOld] using hleftData.2.2
  have hrightBitOld : (C j).bit =
      (reference (genericWriterPos hp (ψ + frontier))).bit := by
    simpa [j, hrightPayloadOld] using hrightData.2.2
  have hleftLabelVal : (C e).label.val = frontier - 1 := by
    calc
      (C e).label.val = (ψ + frontier - 1) % ψ := hlabel _ (by omega)
      _ = frontier - 1 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = frontier := by
    calc
      (C j).label.val = (ψ + frontier) % ψ := hlabel _ (by omega)
      _ = frontier := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hfrontierLt]
  have hleftAlign : (C e).label.val = (payload (frontier - 1)).label := by
    rw [hleftLabelVal, hpayload (frontier - 1) (by omega)]
  have hrightAlign : (C j).label.val = (payload frontier).label := by
    rw [hrightLabelVal, hpayload frontier hfrontierLt]
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_unequal_action_nonzero hp
      (C e) (C j) (payload (frontier - 1)) (payload frontier) prior
      comparison flag command hleftPath hrightPath rfl hrightState hprior
      hleftAlign hrightAlign hdecision hrightZero horder (hclean e)
      (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_clean_label_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; simpa only [T] using hleftCleanAfter)
    (by rw [hj]; simpa only [T] using hrightCleanAfter)
    (by rw [hj]; simpa only [T] using hleftLabelAfter)
    (by rw [hj]; simpa only [T] using hrightLabelAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label at hframes
  rcases hframes with ⟨hcleanAfter, hlabelAfter⟩
  dsimp only
  change WriterUnequalSweepState hp reference D payload command
      (processed + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hkLeft : k = frontier - 1
      · subst k
        have hpayloadOriginal : frontier - 1 + (processed + 1) < ψ := by
          omega
        have hstateFrontier :
            frontier - 1 + (processed + 1) + 1 = ψ := by omega
        simp only [hpayloadOriginal, if_true, hstateFrontier,
          Nat.lt_irrefl, if_false]
        rw [show genericWriterPos hp (ψ + (frontier - 1)) = e by
          simp [e, heIndex], hleftD]
        exact ⟨by simpa only [T] using hleftPathAfter,
          by simpa only [T] using hleftStateAfter,
          by
            rw [show (T (C e) (C j)).1.bit = (C e).bit by
              simpa only [T] using hleftBitAfter]
            simpa [e, heIndex] using hleftBitOld⟩
      · by_cases hkRight : k = frontier
        · subst k
          have hpayloadChanged : ¬frontier + (processed + 1) < ψ := by
            omega
          have hstateNotEarly :
              ¬frontier + (processed + 1) + 1 < ψ := by omega
          have hstateNotFrontier :
              frontier + (processed + 1) + 1 ≠ ψ := by omega
          simp only [hpayloadChanged, if_false, hstateNotEarly,
            hstateNotFrontier]
          rw [show genericWriterPos hp (ψ + frontier) = j by rfl, hrightD]
          exact ⟨by simpa only [T] using hrightPathAfter,
            by simpa only [T] using hrightStateAfter,
            by
              rw [show (T (C e) (C j)).2.bit =
                  writerUnequalBit command (payload frontier) (C j).bit by
                simpa only [T] using hrightBitAfter]
              exact congrArg (writerUnequalBit command (payload frontier))
                hrightBitOld⟩
        · have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          rw [hsame]
          by_cases hkEarly : k < frontier
          · have hpayloadOld : k + processed < ψ := by omega
            have hpayloadNew : k + (processed + 1) < ψ := by omega
            have hstateOld : k + processed + 1 < ψ := by omega
            have hstateNew : k + (processed + 1) + 1 < ψ := by omega
            simpa [hpayloadOld, hpayloadNew, hstateOld, hstateNew] using
              htokens k hk
          · have hpayloadOld : ¬k + processed < ψ := by omega
            have hpayloadNew : ¬k + (processed + 1) < ψ := by omega
            have hstateOldEarly : ¬k + processed + 1 < ψ := by omega
            have hstateOldFrontier : k + processed + 1 ≠ ψ := by omega
            have hstateNewEarly : ¬k + (processed + 1) + 1 < ψ := by omega
            have hstateNewFrontier :
                k + (processed + 1) + 1 ≠ ψ := by omega
            simpa [hpayloadOld, hpayloadNew, hstateOldEarly,
              hstateOldFrontier, hstateNewEarly, hstateNewFrontier] using
                htokens k hk
  · intro x hx
    rw [hlabelAfter (genericWriterPos hp x)]
    exact hlabel x hx
  · intro k hk
    have hsourceNeE : genericWriterPos hp k ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    have hsourceNeJ : genericWriterPos hp k ≠ j :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
      dsimp only [D]
      exact stepConfig_eq_of_ne ring T C e _ hsourceNeE
        (by simpa [hj] using hsourceNeJ)
    rw [hsame]
    exact hsourceBit k hk

/-- The wrap edge executes the final unequal action at label zero without
propagating it into the preceding source group. All target components are then
retired with their exact command-dependent payload and bit images. -/
theorem WriterUnequalSweepState.zero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalSweepState (by omega) reference C payload command
      (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hsourceBit : WriterSourceBitFrame (by omega) reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ - 1))
    WriterUnequalSweepState (by omega) reference D payload command ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  rcases hstate with ⟨_, _, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ - 1)
  let j := genericWriterPos hp ψ
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    congr 2
    omega
  have hrightData := htokens 0 (by omega)
  have hpayloadOld : ψ - 1 < ψ := by omega
  have hstateNotEarly : ¬ψ - 1 + 1 < ψ := by omega
  have hstateFrontier : ψ - 1 + 1 = ψ := by omega
  have hleftPath : (C e).path3 = none := by
    simpa [e] using hboundary
  have hrightPath : (C j).path3 = some (payload 0) := by
    simpa [j, hpayloadOld] using hrightData.1
  have hrightState : (C j).write_state = writeActionToState command := by
    simpa [j, hpayloadOld, hstateNotEarly, hstateFrontier] using
      hrightData.2.1
  have hrightBitOld : (C j).bit =
      (reference (genericWriterPos hp ψ)).bit := by
    simpa [j, hpayloadOld] using hrightData.2.2
  have hrightLabelVal : (C j).label.val = 0 := by
    calc
      (C j).label.val = ψ % ψ := hlabel ψ (by omega)
      _ = 0 := Nat.mod_self ψ
  have hrightZero : (C j).label = ⟨0, hp⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightAlign : (C j).label.val = (payload 0).label := by
    rw [hrightLabelVal, hpayload 0 (by omega)]
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_unequal_action_zero hp
      (C e) (C j) (payload 0) comparison flag command hleftPath hrightPath
      hrightState hrightZero hrightAlign hdecision (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_clean_label_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; simpa only [T] using hleftCleanAfter)
    (by rw [hj]; simpa only [T] using hrightCleanAfter)
    (by rw [hj]; simpa only [T] using hleftLabelAfter)
    (by rw [hj]; simpa only [T] using hrightLabelAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label at hframes
  rcases hframes with ⟨hcleanAfter, hlabelAfter⟩
  change WriterUnequalSweepState hp reference D payload command ψ ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · change (D e).path3 = none
      rw [hleftD]
      simpa only [T] using hleftPathAfter
    · intro k hk
      by_cases hkZero : k = 0
      · subst k
        simp only [Nat.zero_add, Nat.lt_irrefl, if_false,
          show ¬ψ + 1 < ψ by omega, show ψ + 1 ≠ ψ by omega]
        rw [show genericWriterPos hp (ψ + 0) = j by simp [j], hrightD]
        exact ⟨by simpa only [T] using hrightPathAfter,
          by simpa only [T] using hrightStateAfter,
          by
            rw [show (T (C e) (C j)).2.bit =
                writerUnequalBit command (payload 0) (C j).bit by
              simpa only [T] using hrightBitAfter]
            exact congrArg (writerUnequalBit command (payload 0))
              hrightBitOld⟩
      · have hsame : D (genericWriterPos hp (ψ + k)) =
            C (genericWriterPos hp (ψ + k)) := by
          apply stepConfig_eq_of_ne ring T C e
          · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
          · rw [hj]
            exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
        have hpayloadOldChanged : ¬k + (ψ - 1) < ψ := by omega
        have hpayloadNewChanged : ¬k + ψ < ψ := by omega
        have hstateOldNotEarly : ¬k + (ψ - 1) + 1 < ψ := by omega
        have hstateOldNotFrontier : k + (ψ - 1) + 1 ≠ ψ := by omega
        have hstateNewNotEarly : ¬k + ψ + 1 < ψ := by omega
        have hstateNewNotFrontier : k + ψ + 1 ≠ ψ := by omega
        rw [hsame]
        simpa [hpayloadOldChanged, hpayloadNewChanged,
          hstateOldNotEarly, hstateOldNotFrontier, hstateNewNotEarly,
          hstateNewNotFrontier] using htokens k hk
  · intro x hx
    rw [hlabelAfter (genericWriterPos hp x)]
    exact hlabel x hx
  · intro k hk
    by_cases hke : genericWriterPos hp k = e
    · rw [hke, hleftD]
      rw [show (T (C e) (C j)).1.bit = (C e).bit by
        simpa only [T] using hleftBitAfter]
      simpa [hke] using hsourceBit k hk
    · have hkj : genericWriterPos hp k ≠ j :=
        genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
        dsimp only [D]
        exact stepConfig_eq_of_ne ring T C e _ hke
          (by simpa [hj] using hkj)
      rw [hsame]
      exact hsourceBit k hk

/-- The existing counterclockwise edge list is action-independent. Starting
from a one-component unequal-action base, its first `steps` interactions grow
the exact processed suffix to `steps+1` components. -/
theorem writerUnequalSweepSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (comparison : WriteState)
    (flag : Nat) (command : WriteAction) (steps : Nat)
    (hsteps : steps ≤ ψ - 1)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterUnequalSweepState (by omega) reference C payload command 1)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hsourceBit : WriterSourceBitFrame (by omega) reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerMoveFlipSchedule (by omega) steps)
    WriterUnequalSweepState (by omega) reference D payload command
        (steps + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  induction steps generalizing C with
  | zero =>
      simpa [writerMoveFlipSchedule, applySchedule] using
        And.intro hstate (And.intro hclean (And.intro hlabel hsourceBit))
  | succ steps ih =>
      have hprev := ih (C := C) (by omega) hstate hclean hlabel hsourceBit
      let hp : 0 < ψ := by omega
      let C₁ := applySchedule (genericWriterRing hp)
        (writeSeqPersistentComparisonTransportLifecycle hp) C
        (writerMoveFlipSchedule hp steps)
      change WriterUnequalSweepState hp reference C₁ payload command
          (steps + 1) ∧
        (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
        WriterLabelFrame hp C₁ ∧ WriterSourceBitFrame hp reference C₁ at hprev
      rcases hprev with ⟨hstate₁, hclean₁, hlabel₁, hsourceBit₁⟩
      have hnext :
          let frontier := ψ - (steps + 1) - 1
          let D := stepConfig (genericWriterRing hp)
            (writeSeqPersistentComparisonTransportLifecycle hp) C₁
            (genericWriterPos hp (ψ + frontier - 1))
          WriterUnequalSweepState hp reference D payload command
              (steps + 1 + 1) ∧
            (∀ i, WriterTransportCleanFrame (D i)) ∧
            WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D := by
        by_cases hnonzero : steps + 1 < ψ - 1
        · simpa using WriterUnequalSweepState.nonzero_step hψ C₁ reference
            payload comparison flag command (steps + 1) hnonzero hdecision
            hpayload hstate₁ hclean₁ hlabel₁ hsourceBit₁
        · have hterminal : steps + 1 = ψ - 1 := by omega
          have hstateTerminal : WriterUnequalSweepState hp reference C₁
              payload command (ψ - 1) := by
            simpa [hterminal] using hstate₁
          have hfrontierZero : ψ - (ψ - 1) - 1 = 0 := by omega
          have hprocessedDone : ψ - 1 + 1 = ψ := by omega
          rw [hterminal, hfrontierZero, Nat.add_zero, hprocessedDone]
          exact WriterUnequalSweepState.zero_step hψ C₁ reference payload
            comparison flag command hdecision hpayload hstateTerminal hclean₁
            hlabel₁ hsourceBit₁
      dsimp only
      rw [writerMoveFlipSchedule, applySchedule_append]
      simpa [applySchedule, C₁, hp] using hnext

end PPLLWriteSeqUnequalRegression
