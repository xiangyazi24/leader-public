import Leader.Wu.WriteSeq.UnequalSchedule

/-!
# Relocating the writer kernel to arbitrary ring windows

The arbitrary-width writer theorems are proved on a canonical two-group ring
`Fin (2*ψ)`.  Their schedules never fire the edge leaving the second group.
This module embeds that non-wrapping window at an arbitrary position of a
larger directed ring and proves that configuration steps and finite schedules
commute with the embedding.  The result is the geometric bridge needed before
iterating the writer through successive ruler groups.
-/

namespace PPLLWriteSeqRelocation

open PPLL PPLLWriteSeqPersistenceRepair
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqUnequalRegression

/-- Translation by an arbitrary ring start is injective on one full residue
interval.  The proof separates the wrapped and non-wrapped representatives of
`start+k`; no group structure beyond modular arithmetic is assumed. -/
theorem groupOffset_ne_of_lt {n a b : Nat} (ring : DirectedRing n)
    (start : Fin n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    groupOffset ring start a ≠ groupOffset ring start b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [groupOffset] at hv
  by_cases haWrap : start.val + a < n
  · rw [Nat.mod_eq_of_lt haWrap] at hv
    by_cases hbWrap : start.val + b < n
    · rw [Nat.mod_eq_of_lt hbWrap] at hv
      exact hab (by omega)
    · have hbGe : n ≤ start.val + b := by omega
      rw [Nat.mod_eq_sub_mod hbGe,
        Nat.mod_eq_of_lt (by omega : start.val + b - n < n)] at hv
      omega
  · have haGe : n ≤ start.val + a := by omega
    rw [Nat.mod_eq_sub_mod haGe,
      Nat.mod_eq_of_lt (by omega : start.val + a - n < n)] at hv
    by_cases hbWrap : start.val + b < n
    · rw [Nat.mod_eq_of_lt hbWrap] at hv
      omega
    · have hbGe : n ≤ start.val + b := by omega
      rw [Nat.mod_eq_sub_mod hbGe,
        Nat.mod_eq_of_lt (by omega : start.val + b - n < n)] at hv
      exact hab (by omega)

/-- Embed the canonical two-group writer ring into a window beginning at
`start` in a larger ring. -/
def writerWindowEmbed {ψ n : Nat} (ring : DirectedRing n)
    (start : Fin n) (i : Fin (2 * ψ)) : Fin n :=
  groupOffset ring start i.val

/-- A window of length `2ψ` is pointwise injective when it fits in the larger
ring. -/
theorem writerWindowEmbed_injective {ψ n : Nat} (_hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n) :
    Function.Injective (writerWindowEmbed ring start : Fin (2 * ψ) → Fin n) := by
  intro i j hij
  apply Fin.ext
  by_cases hval : i.val = j.val
  · exact hval
  · exact False.elim
      (groupOffset_ne_of_lt ring start (by omega) (by omega) hval hij)

/-- Before the end of the second group, the window embedding preserves the
clockwise neighbor edge exactly. -/
theorem writerWindowEmbed_rightNeighbor {ψ n : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n) (i : Fin (2 * ψ))
    (hi : i.val + 1 < 2 * ψ) :
    ring.rightNeighbor (writerWindowEmbed ring start i) =
      writerWindowEmbed ring start
        ((genericWriterRing hψ).rightNeighbor i) := by
  rw [show writerWindowEmbed ring start i =
      groupOffset ring start i.val by rfl,
    rightNeighbor_groupOffset]
  congr 1
  simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hi]

/-- A large configuration agrees with a canonical two-group configuration on
every embedded writer-window position. Outside the window it is unconstrained.
-/
def WriterWindowAgrees {ψ n : Nat} (ring : DirectedRing n)
    (start : Fin n) (small : Fin (2 * ψ) → AgentState ψ)
    (large : Fin n → AgentState ψ) : Prop :=
  ∀ i, large (writerWindowEmbed ring start i) = small i

/-- One non-wrapping canonical interaction and its embedded large-ring edge
produce configurations that still agree on the whole writer window. -/
theorem WriterWindowAgrees.step {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (small : Fin (2 * ψ) → AgentState ψ)
    (large : Fin n → AgentState ψ) (e : Fin (2 * ψ))
    (he : e.val + 1 < 2 * ψ)
    (hagree : WriterWindowAgrees ring start small large) :
    WriterWindowAgrees ring start
      (stepConfig (genericWriterRing (by omega)) T small e)
      (stepConfig ring T large (writerWindowEmbed ring start e)) := by
  let smallRing := genericWriterRing (by omega : 0 < ψ)
  let embed : Fin (2 * ψ) → Fin n :=
    writerWindowEmbed (ψ := ψ) ring start
  change ∀ i, stepConfig ring T large (embed e) (embed i) =
    stepConfig smallRing T small e i
  have hinj : Function.Injective embed :=
    writerWindowEmbed_injective (by omega) ring start hwindow
  have hneighbor : ring.rightNeighbor (embed e) =
      embed (smallRing.rightNeighbor e) := by
    exact writerWindowEmbed_rightNeighbor (by omega) ring start e he
  have hsmallNe : smallRing.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt smallRing (by omega) e
  have heLarge : embed (smallRing.rightNeighbor e) ≠ embed e := by
    exact fun h => hsmallNe (hinj h)
  have heAgree : large (embed e) = small e := by
    simpa [embed] using hagree e
  have hjAgree : large (embed (smallRing.rightNeighbor e)) =
      small (smallRing.rightNeighbor e) := by
    simpa [embed] using hagree (smallRing.rightNeighbor e)
  have hsmallLeft : stepConfig smallRing T small e e =
      (T (small e) (small (smallRing.rightNeighbor e))).1 := by
    simp [stepConfig]
  have hsmallRight :
      stepConfig smallRing T small e (smallRing.rightNeighbor e) =
        (T (small e) (small (smallRing.rightNeighbor e))).2 := by
    simp [stepConfig, hsmallNe]
  have hlargeLeft : stepConfig ring T large (embed e) (embed e) =
      (T (large (embed e))
        (large (embed (smallRing.rightNeighbor e)))).1 := by
    simp [stepConfig, hneighbor]
  have hlargeRight : stepConfig ring T large (embed e)
      (embed (smallRing.rightNeighbor e)) =
        (T (large (embed e))
          (large (embed (smallRing.rightNeighbor e)))).2 := by
    simp [stepConfig, hneighbor, heLarge]
  intro i
  by_cases hie : i = e
  · subst i
    rw [hlargeLeft, hsmallLeft, heAgree, hjAgree]
  · by_cases hij : i = smallRing.rightNeighbor e
    · subst i
      rw [hlargeRight, hsmallRight, heAgree, hjAgree]
    · have hieLarge : embed i ≠ embed e := fun h => hie (hinj h)
      have hijLarge : embed i ≠ ring.rightNeighbor (embed e) := by
        rw [hneighbor]
        exact fun h => hij (hinj h)
      rw [stepConfig_eq_of_ne ring T large (embed e) (embed i) hieLarge
          hijLarge,
        stepConfig_eq_of_ne smallRing T small e i hie hij]
      simpa [embed] using hagree i

/-! ## Finite schedule relocation

Mapping each canonical edge to its window position preserves a whole schedule
provided no canonical edge leaves the second group. This condition is exactly
what the writer transport and target-action schedules satisfy.
-/

/-- Relocate a canonical two-group schedule to a window of a larger ring. -/
def relocateWriterSchedule {ψ n : Nat} (ring : DirectedRing n)
    (start : Fin n) (schedule : DetSchedule (2 * ψ)) : DetSchedule n :=
  schedule.map (writerWindowEmbed ring start)

/-- A schedule stays inside the two-group window when every initiator has a
successor before canonical position `2ψ`. -/
def WriterScheduleNonwrapping {ψ : Nat}
    (schedule : DetSchedule (2 * ψ)) : Prop :=
  ∀ e, e ∈ schedule → e.val + 1 < 2 * ψ

/-- Exact schedule-level simulation of a canonical writer window inside an
arbitrary larger ring. States outside the embedded window never enter the
proof and may be arbitrary. -/
theorem WriterWindowAgrees.applySchedule {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (small : Fin (2 * ψ) → AgentState ψ)
    (large : Fin n → AgentState ψ) (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule)
    (hagree : WriterWindowAgrees ring start small large) :
    WriterWindowAgrees ring start
      (applySchedule (genericWriterRing (by omega)) T small schedule)
      (applySchedule ring T large
        (relocateWriterSchedule ring start schedule)) := by
  induction schedule generalizing small large with
  | nil =>
      change WriterWindowAgrees ring start small large
      exact hagree
  | cons e rest ih =>
      have he : e.val + 1 < 2 * ψ := hnonwrap e (by simp)
      have hrest : WriterScheduleNonwrapping rest := by
        intro x hx
        exact hnonwrap x (by simp [hx])
      have hstep := WriterWindowAgrees.step hψ ring start hwindow T small
        large e he hagree
      have htail := ih (small := stepConfig
          (genericWriterRing (ψ := ψ) (by omega))
          T small e)
        (large := stepConfig ring T large (writerWindowEmbed ring start e))
        hrest hstep
      change WriterWindowAgrees ring start
        (_root_.applySchedule (genericWriterRing (ψ := ψ) (by omega)) T
          (stepConfig (genericWriterRing (ψ := ψ) (by omega)) T small e)
          rest)
        (_root_.applySchedule ring T
          (stepConfig ring T large (writerWindowEmbed ring start e))
          (relocateWriterSchedule ring start rest))
      exact htail

/-- A relocated non-wrapping schedule leaves every position outside the
embedded two-group window unchanged. -/
theorem relocateWriterSchedule_eq_of_outside {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (_hwindow : 2 * ψ ≤ n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule)
    (i : Fin n)
    (houtside : ∀ j : Fin (2 * ψ), i ≠ writerWindowEmbed ring start j) :
    _root_.applySchedule ring T C
      (relocateWriterSchedule ring start schedule) i = C i := by
  induction schedule generalizing C with
  | nil => rfl
  | cons e rest ih =>
      have he : e.val + 1 < 2 * ψ := hnonwrap e (by simp)
      have hrest : WriterScheduleNonwrapping rest := by
        intro x hx
        exact hnonwrap x (by simp [hx])
      have hright : ring.rightNeighbor (writerWindowEmbed ring start e) =
          writerWindowEmbed ring start
            ((genericWriterRing (by omega : 0 < ψ)).rightNeighbor e) :=
        writerWindowEmbed_rightNeighbor (by omega) ring start e he
      have hleftNe : i ≠ writerWindowEmbed ring start e := houtside e
      have hrightNe :
          i ≠ ring.rightNeighbor (writerWindowEmbed ring start e) := by
        rw [hright]
        exact houtside _
      have hhead : stepConfig ring T C (writerWindowEmbed ring start e) i =
          C i :=
        stepConfig_eq_of_ne ring T C _ i hleftNe hrightNe
      have htail := ih (C := stepConfig ring T C
          (writerWindowEmbed ring start e)) hrest
      change _root_.applySchedule ring T
          (stepConfig ring T C (writerWindowEmbed ring start e))
          (relocateWriterSchedule ring start rest) i = C i
      rw [htail, hhead]

/-! ## Non-wrapping certificates for writer schedules

The simulation theorem has one purely geometric premise. The following lemmas
discharge it compositionally for the schedules used by the writer kernel.
-/

/-- Concatenating two non-wrapping schedules preserves the property. -/
theorem WriterScheduleNonwrapping.append {ψ : Nat}
    {left right : DetSchedule (2 * ψ)}
    (hleft : WriterScheduleNonwrapping left)
    (hright : WriterScheduleNonwrapping right) :
    WriterScheduleNonwrapping (left ++ right) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hleft e he
  · exact hright e he

/-- Inside the canonical two-group ring, an offset below `2ψ` has that exact
numeric position rather than a reduced residue. -/
theorem genericWriterPos_val_of_lt {ψ x : Nat} (hψ : 0 < ψ)
    (hx : x < 2 * ψ) :
    (genericWriterPos hψ x).val = x := by
  simp [genericWriterPos, genericWriterStart, groupOffset,
    Nat.mod_eq_of_lt hx]

/-- Every proper-prefix comparison edge remains inside the canonical
two-group window. -/
theorem writerEqualPrefixSchedule_nonwrapping {ψ count : Nat}
    (hψ : 0 < ψ) (hcount : count ≤ ψ) :
    WriterScheduleNonwrapping (writerEqualPrefixSchedule hψ count) := by
  induction count with
  | zero =>
      intro e he
      simp [writerEqualPrefixSchedule] at he
  | succ count ih =>
      intro e he
      simp only [writerEqualPrefixSchedule, List.mem_append,
        List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih (by omega) e he
      · rw [genericWriterPos_val_of_lt hψ (by omega)]
        omega

/-- Clockwise command handoff stays inside the target group for every allowed
prefix length. -/
theorem writerUnequalCommandSchedule_nonwrapping {ψ frontier steps : Nat}
    (hψ : 0 < ψ) (hsteps : steps ≤ ψ - 1 - frontier) :
    WriterScheduleNonwrapping
      (writerUnequalCommandSchedule hψ frontier steps) := by
  induction steps with
  | zero =>
      intro e he
      simp [writerUnequalCommandSchedule] at he
  | succ steps ih =>
      intro e he
      simp only [writerUnequalCommandSchedule, List.mem_append,
        List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih (by omega) e he
      · rw [genericWriterPos_val_of_lt hψ (by omega)]
        omega

/-- Every allowed counterclockwise action edge remains inside the source/target
window, including its final source-terminal to target-zero boundary edge. -/
theorem writerMoveFlipSchedule_nonwrapping {ψ steps : Nat}
    (hψ : 0 < ψ) (hsteps : steps ≤ ψ - 1) :
    WriterScheduleNonwrapping (writerMoveFlipSchedule hψ steps) := by
  induction steps with
  | zero =>
      intro e he
      simp [writerMoveFlipSchedule] at he
  | succ steps ih =>
      intro e he
      simp only [writerMoveFlipSchedule, List.mem_append,
        List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih (by omega) e he
      · rw [genericWriterPos_val_of_lt hψ (by omega)]
        omega

/-- The canonical `ψ²` block-transport schedule never fires the edge leaving
the second group. -/
theorem writerBlockTransportSchedule_nonwrapping {ψ : Nat} (hψ : 0 < ψ) :
    WriterScheduleNonwrapping
      (writerBlockTransportSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) ψ) := by
  intro e he
  simp only [writerBlockTransportSchedule, List.mem_flatMap] at he
  obtain ⟨round, hround, he⟩ := he
  have hroundLt : round < ψ := List.mem_range.mp hround
  unfold writerBlockSweepSchedule at he
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
  have hkLt : k < ψ := by
    simpa using hk
  change (0 + round + k) % (2 * ψ) + 1 < 2 * ψ
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- A single canonical edge is non-wrapping when its numeric initiator has a
successor inside the two-group window. -/
theorem writerSingletonSchedule_nonwrapping {ψ x : Nat} (hψ : 0 < ψ)
    (hx : x + 1 < 2 * ψ) :
    WriterScheduleNonwrapping ([genericWriterPos hψ x] : DetSchedule (2 * ψ)) := by
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  rw [genericWriterPos_val_of_lt hψ (by omega)]
  exact hx

/-- The complete strict-nonterminal unequal action never uses the edge leaving
the target group. -/
theorem writerUnequalStrictActionSchedule_nonwrapping {ψ mismatch : Nat}
    (hψ : 0 < ψ) (hmismatch : mismatch < ψ - 1) :
    WriterScheduleNonwrapping
      (writerUnequalStrictActionSchedule hψ mismatch) := by
  unfold writerUnequalStrictActionSchedule
  intro e he
  simp only [List.mem_append] at he
  rcases he with he | he
  · rcases he with he | he
    · rcases he with he | he
      · rcases he with he | he
        · exact writerEqualPrefixSchedule_nonwrapping hψ (by omega) e he
        · exact writerSingletonSchedule_nonwrapping hψ (by omega) e he
      · exact writerUnequalCommandSchedule_nonwrapping hψ (by omega) e he
    · exact writerSingletonSchedule_nonwrapping hψ (by omega) e he
  · exact writerMoveFlipSchedule_nonwrapping hψ (by omega) e he

/-- The terminal-mismatch action schedule is non-wrapping. -/
theorem writerUnequalTerminalActionSchedule_nonwrapping {ψ : Nat}
    (hψ : 0 < ψ) :
    WriterScheduleNonwrapping (writerUnequalTerminalActionSchedule hψ) := by
  unfold writerUnequalTerminalActionSchedule
  intro e he
  simp only [List.mem_append] at he
  rcases he with he | he
  · rcases he with he | he
    · exact writerEqualPrefixSchedule_nonwrapping hψ (by omega) e he
    · exact writerSingletonSchedule_nonwrapping hψ (by omega) e he
  · exact writerMoveFlipSchedule_nonwrapping hψ (by omega) e he

/-- The unified unequal action is non-wrapping for every valid mismatch
position. -/
theorem writerUnequalActionSchedule_nonwrapping {ψ mismatch : Nat}
    (hψ : 0 < ψ) (hmismatch : mismatch < ψ) :
    WriterScheduleNonwrapping (writerUnequalActionSchedule hψ mismatch) := by
  unfold writerUnequalActionSchedule
  split
  · exact writerUnequalTerminalActionSchedule_nonwrapping hψ
  · exact writerUnequalStrictActionSchedule_nonwrapping hψ (by omega)

/-- The complete initial crossing plus unequal action stays inside the same
two-group window, so it can be relocated without assumptions on outside
agents. -/
theorem writerFirstUnequalSchedule_nonwrapping {ψ mismatch : Nat}
    (hψ : 0 < ψ) (hmismatch : mismatch < ψ) :
    WriterScheduleNonwrapping (writerFirstUnequalSchedule hψ mismatch) := by
  unfold writerFirstUnequalSchedule
  exact (writerBlockTransportSchedule_nonwrapping hψ).append
    (writerUnequalActionSchedule_nonwrapping hψ hmismatch)

/-- The common-flag-one equal action is non-wrapping. -/
theorem writerEqualFlagOneActionSchedule_nonwrapping {ψ : Nat}
    (hψ : 0 < ψ) :
    WriterScheduleNonwrapping (writerEqualFlagOneActionSchedule hψ) := by
  unfold writerEqualFlagOneActionSchedule
  intro e he
  simp only [List.mem_append] at he
  rcases he with he | he
  · rcases he with he | he
    · exact writerEqualPrefixSchedule_nonwrapping hψ (by omega) e he
    · exact writerSingletonSchedule_nonwrapping hψ (by omega) e he
  · exact writerMoveFlipSchedule_nonwrapping hψ (by omega) e he

/-- The initial crossing plus common-flag-one equal action is non-wrapping. -/
theorem writerFirstEqualFlagOneSchedule_nonwrapping {ψ : Nat}
    (hψ : 0 < ψ) :
    WriterScheduleNonwrapping (writerFirstEqualFlagOneSchedule hψ) := by
  unfold writerFirstEqualFlagOneSchedule
  exact (writerBlockTransportSchedule_nonwrapping hψ).append
    (writerEqualFlagOneActionSchedule_nonwrapping hψ)

/-- The common-flag-zero exact increment action is non-wrapping. -/
theorem writerEqualFlagZeroActionSchedule_nonwrapping {ψ : Nat}
    (hψ : 0 < ψ) :
    WriterScheduleNonwrapping (writerEqualFlagZeroActionSchedule hψ) := by
  unfold writerEqualFlagZeroActionSchedule
  intro e he
  simp only [List.mem_append] at he
  rcases he with he | he
  · rcases he with he | he
    · exact writerEqualPrefixSchedule_nonwrapping hψ (by omega) e he
    · exact writerSingletonSchedule_nonwrapping hψ (by omega) e he
  · exact writerMoveFlipSchedule_nonwrapping hψ (by omega) e he

/-- The initial crossing plus common-flag-zero increment is non-wrapping. -/
theorem writerFirstEqualFlagZeroSchedule_nonwrapping {ψ : Nat}
    (hψ : 0 < ψ) :
    WriterScheduleNonwrapping (writerFirstEqualFlagZeroSchedule hψ) := by
  unfold writerFirstEqualFlagZeroSchedule
  exact (writerBlockTransportSchedule_nonwrapping hψ).append
    (writerEqualFlagZeroActionSchedule_nonwrapping hψ)

/-! ## Completed-window seam

All action invariants end with the target writer in `depart`. The small
predicate below forgets the action history and retains exactly the payload/state
facts needed to reinterpret that target group as the source of the next window.
-/

/-- A canonical target group contains a complete retired writer with payload
family `nextPayload`. -/
def WriterCanonicalCompletedState {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ)
    (nextPayload : Nat → Path3Info) : Prop :=
  ∀ k, k < ψ →
    WriterTokenAt C (genericWriterPos hψ (ψ + k)) (nextPayload k) .depart

/-- A completed common-flag-one sweep yields the pointwise flag-complemented
payload family. -/
theorem WriterMoveFlipSweepState.toCompleted {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (hstate : WriterMoveFlipSweepState hψ C payload ψ) :
    WriterCanonicalCompletedState hψ C
      (fun k => { payload k with flag := 1 - (payload k).flag }) := by
  rcases hstate with ⟨_, _, _, htokens⟩
  intro k hk
  have hpayload : ¬k + ψ < ψ := by omega
  have hstateEarly : ¬k + ψ + 1 < ψ := by omega
  have hstateFrontier : k + ψ + 1 ≠ ψ := by omega
  simpa [WriterTokenAt, hpayload, hstateEarly, hstateFrontier] using
    htokens k hk

/-- A completed exact increment sweep has the same flag-complemented payload
family; its physical-bit update is orthogonal to the next transport state. -/
theorem WriterIncrementSweepState.toCompleted {ψ : Nat} (hψ : 0 < ψ)
    (reference C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hstate : WriterIncrementSweepState hψ reference C payload ψ) :
    WriterCanonicalCompletedState hψ C
      (fun k => { payload k with flag := 1 - (payload k).flag }) := by
  rcases hstate with ⟨_, _, _, htokens⟩
  intro k hk
  have hpayload : ¬k + ψ < ψ := by omega
  have hstateEarly : ¬k + ψ + 1 < ψ := by omega
  have hstateFrontier : k + ψ + 1 ≠ ψ := by omega
  have htoken := htokens k hk
  simpa [WriterTokenAt, hpayload, hstateEarly, hstateFrontier] using htoken.1

/-- A completed unequal sweep yields its exact command-dependent payload
family. -/
theorem WriterUnequalSweepState.toCompleted {ψ : Nat} (hψ : 0 < ψ)
    (reference C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (command : WriteAction)
    (hstate : WriterUnequalSweepState hψ reference C payload command ψ) :
    WriterCanonicalCompletedState hψ C
      (fun k => writerUnequalPayload command (payload k)) := by
  rcases hstate with ⟨_, _, _, htokens⟩
  intro k hk
  have hpayload : ¬k + ψ < ψ := by omega
  have hstateEarly : ¬k + ψ + 1 < ψ := by omega
  have hstateFrontier : k + ψ + 1 ≠ ψ := by omega
  have htoken := htokens k hk
  exact ⟨by simpa [hpayload] using htoken.1,
    by simpa [hstateEarly, hstateFrontier] using htoken.2.1⟩

/-! ## Relocated complete unequal action

Pulling a large configuration back along the window embedding produces the
canonical configuration consumed by the existing theorem. Schedule simulation
then places its exact endpoint inside the selected large-ring window.
-/

/-- Restrict a large-ring configuration to the canonical two-group writer
window beginning at `start`. -/
def writerWindowPullback {ψ n : Nat} (ring : DirectedRing n)
    (start : Fin n) (C : Fin n → AgentState ψ) :
    Fin (2 * ψ) → AgentState ψ :=
  fun i => C (writerWindowEmbed ring start i)

/-- The pullback agrees definitionally with its large configuration on the
embedded window. -/
theorem writerWindowPullback_agrees {ψ n : Nat} (ring : DirectedRing n)
    (start : Fin n) (C : Fin n → AgentState ψ) :
    WriterWindowAgrees ring start (writerWindowPullback ring start C) C := by
  intro i
  rfl

/-- Moving the window start by one group identifies its offset `x` with offset
`ψ+x` from the old start. -/
theorem writerWindowEmbed_next_offset {ψ n x : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hx : x < 2 * ψ) :
    writerWindowEmbed ring (groupOffset ring start ψ)
        (genericWriterPos hψ x) =
      groupOffset ring start (ψ + x) := by
  unfold writerWindowEmbed
  rw [genericWriterPos_val_of_lt hψ hx, groupOffset_compose]

/-- The source component `k` of the next window is the target component `k` of
the old window. -/
theorem writerWindowEmbed_next_source {ψ n k : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hk : k < ψ) :
    writerWindowEmbed ring (groupOffset ring start ψ)
        (genericWriterPos hψ k) =
      writerWindowEmbed ring start (genericWriterPos hψ (ψ + k)) := by
  rw [writerWindowEmbed_next_offset hψ ring start (by omega)]
  unfold writerWindowEmbed
  rw [genericWriterPos_val_of_lt hψ (by omega)]

/-- A completed target writer becomes `WriterRoundState ... 0` at the source of
the next window, provided the next physical group was empty before the current
non-wrapping schedule. This is the exact seam for successive-group induction.
-/
theorem WriterCanonicalCompletedState.toNextRoundState {ψ n : Nat}
    (hψ : 1 < ψ) (ring : DirectedRing n) (start : Fin n)
    (hthree : 3 * ψ ≤ n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule)
    (smallAfter : Fin (2 * ψ) → AgentState ψ)
    (nextPayload : Nat → Path3Info)
    (hagree : WriterWindowAgrees ring start smallAfter
      (_root_.applySchedule ring T C
        (relocateWriterSchedule ring start schedule)))
    (hcomplete : WriterCanonicalCompletedState (by omega) smallAfter
      nextPayload)
    (hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none) :
    let largeAfter := _root_.applySchedule ring T C
      (relocateWriterSchedule ring start schedule)
    let nextStart := groupOffset ring start ψ
    WriterRoundState (by omega)
      (writerWindowPullback ring nextStart largeAfter) nextPayload 0 := by
  let hp : 0 < ψ := by omega
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  let nextStart := groupOffset ring start ψ
  change WriterRoundState hp
    (writerWindowPullback ring nextStart largeAfter) nextPayload 0
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro k hk
    have hcoord := writerWindowEmbed_next_source hp ring start hk
    have hagreeK := hagree (genericWriterPos hp (ψ + k))
    have htoken := hcomplete k hk
    change WriterTokenAt
      (writerWindowPullback ring nextStart largeAfter)
      (genericWriterPos hp (0 + k)) (nextPayload k)
      (if 0 = ψ then .none else .depart)
    have hψne : (0 : Nat) ≠ ψ := by omega
    simp only [Nat.zero_add, hψne, if_false]
    change WriterTokenAt largeAfter
      (writerWindowEmbed ring nextStart (genericWriterPos hp k))
      (nextPayload k) .depart
    rw [show nextStart = groupOffset ring start ψ by rfl, hcoord]
    have hOldCoord : writerWindowEmbed ring start
        (genericWriterPos hp (ψ + k)) =
          groupOffset ring start (ψ + k) := by
      unfold writerWindowEmbed
      rw [genericWriterPos_val_of_lt hp (by omega)]
    rw [hOldCoord]
    rw [hOldCoord] at hagreeK
    have hagreeK' : largeAfter (groupOffset ring start (ψ + k)) =
          smallAfter (genericWriterPos hp (ψ + k)) := by
      simpa [largeAfter] using hagreeK
    unfold WriterTokenAt at htoken ⊢
    rw [hagreeK']
    exact htoken
  · intro x hx
    omega
  · intro x hxLower hxUpper
    have hxWindow : x < 2 * ψ := hxUpper
    have hcoord := writerWindowEmbed_next_offset hp ring start hxWindow
    let i := groupOffset ring start (ψ + x)
    have hiOutside : ∀ j : Fin (2 * ψ),
        i ≠ writerWindowEmbed ring start j := by
      intro j
      unfold i writerWindowEmbed
      apply groupOffset_ne_of_lt ring start
      · omega
      · omega
      · omega
    have houtside := relocateWriterSchedule_eq_of_outside hψ ring start
      (by omega) T C schedule hnonwrap i hiOutside
    have hk : x - ψ < ψ := by omega
    have hoffset : ψ + x = 2 * ψ + (x - ψ) := by omega
    change (largeAfter
      (writerWindowEmbed ring nextStart (genericWriterPos hp x))).path3 = none
    rw [hcoord]
    change (largeAfter i).path3 = none
    have houtside' : largeAfter i = C i := by
      simpa [largeAfter] using houtside
    rw [houtside']
    rw [show i = groupOffset ring start (2 * ψ + (x - ψ)) by
      unfold i
      rw [hoffset]]
    exact hnextEmpty (x - ψ) hk

/-- **Arbitrary-position unequal writer execution.** If the pullback of a
large-ring window satisfies the canonical source-writer hypotheses, relocating
the full transport/action schedule yields a large endpoint that agrees with the
kernel-checked canonical endpoint. The latter has every component retired with
the exact overwrite/move-flip/move payload and bit image. -/
theorem writerFirstUnequalSchedule_relocated {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcomparePrefix : ∀ k, k < mismatch →
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hcompareMismatch :
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + mismatch))).bit
        (payload mismatch).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C)) :
    let schedule := writerFirstUnequalSchedule (ψ := ψ) (by omega) mismatch
    let smallAfter := _root_.applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega))
      (writerWindowPullback ring start C) schedule
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    WriterWindowAgrees ring start smallAfter largeAfter ∧
      WriterUnequalSweepState (by omega)
        (writerWindowPullback ring start reference) smallAfter payload command
        ψ := by
  let hp : 0 < ψ := by omega
  let schedule := writerFirstUnequalSchedule hp mismatch
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hsim := WriterWindowAgrees.applySchedule hψ ring start hwindow T small C
    schedule (writerFirstUnequalSchedule_nonwrapping hp hmismatch)
    (writerWindowPullback_agrees ring start C)
  change WriterWindowAgrees ring start smallAfter largeAfter at hsim
  have hcanonical := writerFirstUnequalSchedule_reaches hψ small
    smallReference payload mismatch comparison flag command hmismatch hpayload
    hpayloadFlag hcomparePrefix hcompareMismatch hdecision hstate hclean hlabel
    hbit
  change WriterUnequalSweepState hp smallReference smallAfter payload command
      ψ ∧
    (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
    WriterLabelFrame hp smallAfter ∧
    WriterSourceBitFrame hp smallReference smallAfter at hcanonical
  exact ⟨hsim, hcanonical.1⟩

/-- The full common-flag-one equal schedule relocates to every fitting
two-group window of an arbitrary ring. -/
theorem writerFirstEqualFlagOneSchedule_relocated {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 1)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C)) :
    let schedule := writerFirstEqualFlagOneSchedule (by omega)
    let smallAfter := _root_.applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega))
      (writerWindowPullback ring start C) schedule
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    WriterWindowAgrees ring start smallAfter largeAfter ∧
      WriterMoveFlipSweepState (by omega) smallAfter payload ψ := by
  let hp : 0 < ψ := by omega
  let schedule := writerFirstEqualFlagOneSchedule hp
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hsim := WriterWindowAgrees.applySchedule hψ ring start hwindow T small C
    schedule (writerFirstEqualFlagOneSchedule_nonwrapping hp)
    (writerWindowPullback_agrees ring start C)
  change WriterWindowAgrees ring start smallAfter largeAfter at hsim
  have hcanonical := writerFirstEqualFlagOneSchedule_reaches hψ small
    smallReference payload hpayload hcompare hpayloadFlag hstate hclean hlabel
    hbit
  change WriterMoveFlipSweepState hp smallAfter payload ψ ∧
    (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
    WriterLabelFrame hp smallAfter ∧
    WriterBitFrame smallReference smallAfter at hcanonical
  exact ⟨hsim, hcanonical.1⟩

/-- The full common-flag-zero exact increment schedule relocates to every
fitting two-group window of an arbitrary ring. -/
theorem writerFirstEqualFlagZeroSchedule_relocated {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 0)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C)) :
    let schedule := writerFirstEqualFlagZeroSchedule (by omega)
    let smallAfter := _root_.applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega))
      (writerWindowPullback ring start C) schedule
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    WriterWindowAgrees ring start smallAfter largeAfter ∧
      WriterIncrementSweepState (by omega)
        (writerWindowPullback ring start reference) smallAfter payload ψ := by
  let hp : 0 < ψ := by omega
  let schedule := writerFirstEqualFlagZeroSchedule hp
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hsim := WriterWindowAgrees.applySchedule hψ ring start hwindow T small C
    schedule (writerFirstEqualFlagZeroSchedule_nonwrapping hp)
    (writerWindowPullback_agrees ring start C)
  change WriterWindowAgrees ring start smallAfter largeAfter at hsim
  have hcanonical := writerFirstEqualFlagZeroSchedule_reaches hψ small
    smallReference payload hpayload hcompare hpayloadFlag hstate hclean hlabel
    hbit
  change WriterIncrementSweepState hp smallReference smallAfter payload ψ ∧
    (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
    WriterLabelFrame hp smallAfter ∧
    WriterSourceBitFrame hp smallReference smallAfter at hcanonical
  exact ⟨hsim, hcanonical.1⟩

/-! ## Relocated actions prepared for the next window

The following corollaries combine each relocated action with the completed
window seam. They are the direct step interfaces for a future induction over
successive ruler groups.
-/

/-- A relocated unequal action leaves its exact transformed writer ready as
round zero of the next window. -/
theorem writerFirstUnequalSchedule_relocated_toNextRoundState
    {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hthree : 3 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ)
    (payload : Nat → Path3Info) (mismatch : Nat)
    (comparison : WriteState) (flag : Nat) (command : WriteAction)
    (hmismatch : mismatch < ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hcomparePrefix : ∀ k, k < mismatch →
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hcompareMismatch :
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + mismatch))).bit
        (payload mismatch).bit = comparison)
    (hdecision : WriterUnequalCommand comparison flag command)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C))
    (hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none) :
    let schedule := writerFirstUnequalSchedule (ψ := ψ) (by omega) mismatch
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    let nextStart := groupOffset ring start ψ
    WriterRoundState (by omega)
      (writerWindowPullback ring nextStart largeAfter)
      (fun k => writerUnequalPayload command (payload k)) 0 := by
  let hp : 0 < ψ := by omega
  let schedule := writerFirstUnequalSchedule hp mismatch
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hrelocated := writerFirstUnequalSchedule_relocated hψ ring start
    (by omega) C reference payload mismatch comparison flag command hmismatch
    hpayload hpayloadFlag hcomparePrefix hcompareMismatch hdecision hstate
    hclean hlabel hbit
  change WriterWindowAgrees ring start smallAfter largeAfter ∧
    WriterUnequalSweepState hp smallReference smallAfter payload command ψ at hrelocated
  rcases hrelocated with ⟨hagree, hprocessed⟩
  have hcomplete := WriterUnequalSweepState.toCompleted hp smallReference
    smallAfter payload command hprocessed
  exact WriterCanonicalCompletedState.toNextRoundState hψ ring start hthree T C
    schedule (writerFirstUnequalSchedule_nonwrapping hp hmismatch) smallAfter
    (fun k => writerUnequalPayload command (payload k)) hagree hcomplete
    hnextEmpty

/-- A relocated common-flag-one equal action leaves the complemented writer as
round zero of the next window. -/
theorem writerFirstEqualFlagOneSchedule_relocated_toNextRoundState
    {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hthree : 3 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 1)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C))
    (hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none) :
    let schedule := writerFirstEqualFlagOneSchedule (ψ := ψ) (by omega)
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    let nextStart := groupOffset ring start ψ
    WriterRoundState (by omega)
      (writerWindowPullback ring nextStart largeAfter)
      (fun k => { payload k with flag := 1 - (payload k).flag }) 0 := by
  let hp : 0 < ψ := by omega
  let schedule := writerFirstEqualFlagOneSchedule hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hrelocated := writerFirstEqualFlagOneSchedule_relocated hψ ring start
    (by omega) C reference payload hpayload hcompare hpayloadFlag hstate hclean
    hlabel hbit
  change WriterWindowAgrees ring start smallAfter largeAfter ∧
    WriterMoveFlipSweepState hp smallAfter payload ψ at hrelocated
  rcases hrelocated with ⟨hagree, hprocessed⟩
  have hcomplete := WriterMoveFlipSweepState.toCompleted hp smallAfter payload
    hprocessed
  exact WriterCanonicalCompletedState.toNextRoundState hψ ring start hthree T C
    schedule (writerFirstEqualFlagOneSchedule_nonwrapping hp) smallAfter
    (fun k => { payload k with flag := 1 - (payload k).flag }) hagree
    hcomplete hnextEmpty

/-- A relocated common-flag-zero exact increment leaves the complemented writer
as round zero of the next window. -/
theorem writerFirstEqualFlagZeroSchedule_relocated_toNextRoundState
    {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hthree : 3 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 0)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C))
    (hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none) :
    let schedule := writerFirstEqualFlagZeroSchedule (ψ := ψ) (by omega)
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    let nextStart := groupOffset ring start ψ
    WriterRoundState (by omega)
      (writerWindowPullback ring nextStart largeAfter)
      (fun k => { payload k with flag := 1 - (payload k).flag }) 0 := by
  let hp : 0 < ψ := by omega
  let schedule := writerFirstEqualFlagZeroSchedule hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hrelocated := writerFirstEqualFlagZeroSchedule_relocated hψ ring start
    (by omega) C reference payload hpayload hcompare hpayloadFlag hstate hclean
    hlabel hbit
  change WriterWindowAgrees ring start smallAfter largeAfter ∧
    WriterIncrementSweepState hp smallReference smallAfter payload ψ at hrelocated
  rcases hrelocated with ⟨hagree, hprocessed⟩
  have hcomplete := WriterIncrementSweepState.toCompleted hp smallReference
    smallAfter payload hprocessed
  exact WriterCanonicalCompletedState.toNextRoundState hψ ring start hthree T C
    schedule (writerFirstEqualFlagZeroSchedule_nonwrapping hp) smallAfter
    (fun k => { payload k with flag := 1 - (payload k).flag }) hagree
    hcomplete hnextEmpty

end PPLLWriteSeqRelocation
