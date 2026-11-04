import Leader.Wu.Entrance.LocalReverseFill
import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel

/-!
# B6 sanitation interface

This file packages the local sanitation normal form.  It does not
postulate the missing absorber word.  The quantitative theorem below is
conditional on an explicit `SanitationWord` certificate, exactly as
`B6LocalReverseFill.localReverseFill_mass` is conditional on its local word.

`SanCell` intentionally does not constrain `shield`, `stall`, the resident bit,
the ruler registers, WAIT/generation registers, or writer registers.  Ruler and
writer silence are separate workspace predicates.  In particular, stall zero
is allowed on the empty sanitation substrate; positive stall is a later
ReadyCell/delivery obligation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6Sanitation

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
  BirthCheckChainR1PerBlock BirthCheckChainR1Mass
open B6WindowLocality B9OrderedWindowMatcher
open BirthTwoStageEscape BirthLeaderlessBirthMassRenewal
open FiniteUniformStoppingTree FixedSpanRenewalPayload
open ThreePortSerialCount B9SpliceTripleHitWords
open B6LocalReverseFill

attribute [local irreducible] BirthCheckPermitRepairLeaf.step1

variable {n ψ κ τ : Nat}

/-- Raw physical record under the finite authorized/expiring wrappers. -/
def rawCell (q : ExpiringAgentState ψ κ τ) : AgentState ψ :=
  q.core.erase.core

/--
Comparison/control sanitation for one empty route-substrate cell.

Deliberately absent: `shield` and `stall`.  The latter may be zero here.
`bit`, `label`, WAIT/generation state and writer state are also handled by
separate interfaces.
-/
def SanCell (q : ExpiringAgentState ψ κ τ) : Prop :=
  let u := rawCell q
  u.leader = false ∧
  u.state = .none ∧
  u.path = .bot ∧
  u.path2 = none ∧
  u.path4 = none ∧
  u.path5 = none ∧
  u.p = false ∧
  u.p_carry = false ∧
  u.reset_cmd = false ∧
  u.echo = false ∧
  u.signal_B = 0 ∧
  u.bullet = 0 ∧
  q.core.erase.path0Crossed = false

/-- Cellwise sanitation on an actual `B6LocalReverseFill.Interval`. -/
def SanCells (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∀ i, support I i = true → SanCell (C i)

/-- Canonical local ruler: the interval starts at physical label zero. -/
def RulerNF (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∀ k : Fin I.size,
    (rawCell (C (cell ring I.first k.val))).label.val = k.val % ψ

/-- Candidate bit-silent mode 1 from the entrance analysis. -/
def EmptyWriter (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∀ i, support I i = true → (rawCell (C i)).path3 = none

/-- Candidate bit-silent mode 2: interval-wide blocked writer occupancy. -/
def BlockedWriter (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∀ i, support I i = true →
    (rawCell (C i)).path3 ≠ none ∧
    (rawCell (C i)).write_state = .depart ∧
    (rawCell (C i)).write = .none ∧
    (rawCell (C i)).last = false ∧
    (rawCell (C i)).last_set = false ∧
    (rawCell (C i)).last_unset = false

/-- The two interval-wide bit-silent modes; not a per-cell disjunction. -/
def WriterSilent (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  EmptyWriter ring I C ∨ BlockedWriter ring I C

/-- Resident bits agree on the workspace. -/
def ResidentBitsAgree (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ) : Prop :=
  ∀ i, support I i = true → (rawCell (C i)).bit = (rawCell (D i)).bit

/-- Full sanitation endpoint: ruler + writer silence + comparison/control NF. -/
def SanNF (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  RulerNF ring I C ∧ WriterSilent ring I C ∧ SanCells ring I C

/-- Once writer silence is acquired, every later requested prefix preserves bits. -/
def BitsStableAfter
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (base tail : List (Fin n))
    (C : Config n ψ κ τ) : Prop :=
  ∀ p : List (Fin n), p <+: tail →
    ResidentBitsAgree ring I
      (runR hψ h2 ring base C)
      (runR hψ h2 ring (base ++ p) C)

/-- A physical leader/ReadyWindow hit at some requested prefix. -/
def HitByPrefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n))
    (C : Config n ψ κ τ) : Prop :=
  ∃ p : List (Fin n), p <+: w ∧
    HitInside ring I (runR hψ h2 ring p C)

/-! ## Easy exact R1 dispatch facts -/

theorem sanCell_pendingTerminalDisposal_false
    (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) (hq : SanCell q) :
    pendingTerminalDisposal hψ q.core.erase.core = false := by
  simp only [SanCell, rawCell] at hq
  rcases hq with
    ⟨_, _, _, hpath2, _, _, _, _, _, _, _, _, _⟩
  simp [pendingTerminalDisposal, hpath2]

theorem prepareExpiringDisposal_eq_of_sanCell
    (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) (hq : SanCell q) :
    prepareExpiringDisposal hψ q = q := by
  have hclear := sanCell_pendingTerminalDisposal_false hψ q hq
  unfold prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hψ q.core hclear]

/-- A sanitized cell is inactive at the exact prepared deletion-priority gate. -/
theorem sanCell_preparedDeletion_inactive
    (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) (hq : SanCell q) :
    deletionActive
      (normalizeDeletion (prepareExpiringDisposal hψ q).core.erase) = false := by
  rw [prepareExpiringDisposal_eq_of_sanCell hψ q hq]
  simp only [SanCell, rawCell] at hq
  rcases hq with
    ⟨_, hstate, hpath, _, _, _, _, _, _, _, _, _, _⟩
  simp [normalizeDeletion, deletionActive, pathPresent, hstate, hpath]

/--
Two sanitized endpoints satisfy the exact `PreparedOrdinaryOpen` gate.
This is stronger than the refuted raw `NoActiveDeletion` shortcut because
preparation has already been accounted for.
-/
theorem sanCell_pair_preparedOrdinaryOpen
    (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hl : SanCell l) (hr : SanCell r) :
    BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hψ l r := by
  unfold BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
  dsimp only
  exact ⟨sanCell_preparedDeletion_inactive hψ r hr,
    sanCell_preparedDeletion_inactive hψ l hl⟩

/-- The exact authorized dispatch selected inside the R1 expiring row. -/
theorem authorized_eq_ordinary_of_preparedOpen
    (hψ : 0 < ψ) (hwidth : 0 < 2) (h2 : 2 ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hψ l r) :
    let pl := prepareExpiringDisposal hψ l
    let pr := prepareExpiringDisposal hψ r
    BirthCheckPermitRepair.authorized hψ hwidth h2 κ
        pl.core.erase pr.core.erase =
      BirthCheckPermitRepair.ordinary hψ hwidth h2 κ
        (normalizeDeletion pl.core.erase) (normalizeDeletion pr.core.erase) := by
  unfold BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen at hopen
  dsimp only at hopen ⊢
  unfold BirthCheckPermitRepair.authorized
  dsimp only
  simp [hopen.1, hopen.2]

/-- SanCell on both endpoints therefore forces the R1 metadata dispatch ordinary. -/
theorem sanCell_pair_uses_ordinary_dispatch
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : SanCell l) (hr : SanCell r) :
    let pl := prepareExpiringDisposal hψ l
    let pr := prepareExpiringDisposal hψ r
    BirthCheckPermitRepair.authorized hψ (by decide : 0 < 2) h2 κ
        pl.core.erase pr.core.erase =
      BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ
        (normalizeDeletion pl.core.erase) (normalizeDeletion pr.core.erase) := by
  exact authorized_eq_ordinary_of_preparedOpen hψ (by decide) h2 l r
    (sanCell_pair_preparedOrdinaryOpen hψ l r hl hr)

-- END PART 1
/-! ## Workspace locality and the sanitation certificate -/

theorem sanCells_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : SanCells ring I C) : SanCells ring I D := by
  intro i hi
  rw [← hCD i hi]
  exact h i hi

theorem rulerNF_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : RulerNF ring I C) : RulerNF ring I D := by
  intro k
  have hi := support_cell I k.isLt
  rw [← hCD (cell ring I.first k.val) hi]
  exact h k

theorem emptyWriter_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : EmptyWriter ring I C) : EmptyWriter ring I D := by
  intro i hi
  rw [← hCD i hi]
  exact h i hi

theorem blockedWriter_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : BlockedWriter ring I C) : BlockedWriter ring I D := by
  intro i hi
  rw [← hCD i hi]
  exact h i hi

theorem writerSilent_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : WriterSilent ring I C) : WriterSilent ring I D := by
  rcases h with h | h
  · exact Or.inl (emptyWriter_of_agree ring I C D hCD h)
  · exact Or.inr (blockedWriter_of_agree ring I C D hCD h)

theorem sanNF_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : SanNF ring I C) : SanNF ring I D := by
  exact ⟨rulerNF_of_agree ring I C D hCD h.1,
    writerSilent_of_agree ring I C D hCD h.2.1,
    sanCells_of_agree ring I C D hCD h.2.2⟩

/-- Local success relevant to sanitation: physical hit or sanitation endpoint. -/
def SanitationHit (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  HitInside ring I C ∨ SanNF ring I C

/-- Alive class for the stopped event used by the matcher proof. -/
def SanitationUnfinished (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
    ¬ (ReadyWindow ring C ∨ SanNF ring I C)

theorem sanitationHit_of_agree
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : SanitationHit ring I C) : SanitationHit ring I D := by
  rcases h with h | h
  · exact Or.inl (hitInside_of_agree ring I C D hCD h)
  · exact Or.inr (sanNF_of_agree ring I C D hCD h)

theorem sanitationHit_not_unfinished
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) (h : SanitationHit ring I C) :
    ¬ SanitationUnfinished ring I C := by
  intro hU
  rcases h with hhit | hsan
  · have hOld : Unfinished ring C :=
      ⟨hU.1, fun hready => hU.2 (Or.inl hready)⟩
    exact hitInside_not_unfinished ring I C hhit hOld
  · exact hU.2 (Or.inr hsan)

/-- Generic avoidance bookkeeping specialized to ReadyWindow-or-SanNF. -/
theorem avoidCount_eq_alive_sanitation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ) (T : Nat) :
    avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (fun D => ReadyWindow ring D ∨ SanNF ring I D) C T =
      aliveCount (step1 hψ h2 ring)
        (SanitationUnfinished ring I) C T := by
  exact B6LocalReverseFill.avoidCount_eq_alive_complement
    (step1 hψ h2 ring)
    BirthShortDoneTerminalFirstHit.Leaderless
    (fun D => ReadyWindow ring D ∨ SanNF ring I D) C T

/--
Stopped three-phase sanitation certificate.

* `wWriter`: acquire interval-wide writer silence;
* `wJoint`: sanitize controls, with any required per-edge ruler preparation
  interleaved by the eventual constructor;
* `wFinal`: final canonical ruler sweep after the control substrate is clean.

The single `InternalWord I w` clause is the no-cut-edge condition: every
requested edge has both endpoints in the envelope.  There is deliberately no
no-reentry/monotonic-cleanliness premise.
-/
def SanitationWord
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n))
    (C : Config n ψ κ τ) : Prop :=
  InternalWord I w ∧
  ∃ wWriter wJoint wFinal : List (Fin n),
    w = wWriter ++ wJoint ++ wFinal ∧
    let CWriter := runR hψ h2 ring wWriter C
    let CJoint := runR hψ h2 ring (wWriter ++ wJoint) C
    let CFinal := runR hψ h2 ring w C
    HitByPrefix hψ h2 ring I w C ∨
      (WriterSilent ring I CWriter ∧
       BitsStableAfter hψ h2 ring I wWriter (wJoint ++ wFinal) C ∧
       WriterSilent ring I CJoint ∧
       SanCells ring I CJoint ∧
       SanNF ring I CFinal)

private theorem prefix_length_le_san {α : Type} {p w : List α}
    (hp : p <+: w) : p.length ≤ w.length := by
  rcases hp with ⟨v, rfl⟩
  simp only [List.length_append]
  omega

/-- Every sanitation certificate supplies a local successful requested prefix. -/
theorem sanitationWord_success_prefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C : Config n ψ κ τ)
    (h : SanitationWord hψ h2 ring I w C) :
    ∃ p : List (Fin n), p <+: w ∧ InternalWord I p ∧
      SanitationHit ring I (runR hψ h2 ring p C) := by
  rcases h with ⟨hint, wWriter, wJoint, wFinal, _, hphase⟩
  dsimp only at hphase
  rcases hphase with hhit | hnormal
  · rcases hhit with ⟨p, hp, hpHit⟩
    exact ⟨p, hp, internalWord_prefix I hint hp, Or.inl hpHit⟩
  · rcases hnormal with ⟨_, _, _, _, hfinal⟩
    have hp : w <+: w := by simp
    exact ⟨w, hp, hint, Or.inr hfinal⟩

/-- Ordered-matcher success cannot coexist with sanitation avoidance. -/
theorem matcher_success_not_sanitation_alive
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (req : List (Fin n)) (C : Config n ψ κ τ)
    (hne : req ≠ []) (hint : InternalWord I req)
    (hhit : SanitationHit ring I (runR hψ h2 ring req C))
    (u : List (Fin n))
    (hs : runNode (ordStep (touchOf ring (support I))) (.active req) u =
      StopNode.success) :
    aliveBit (step1 hψ h2 ring) (SanitationUnfinished ring I) C u = 0 := by
  classical
  rcases B6WindowLocality.success_prefix_agrees
      (step1_pairLocal (kappa := κ) (tau := τ) hψ h2 ring)
      (support I) req hne (fun e he => hint e he) u hs C with
    ⟨p, hp, hagree⟩
  have hpHit : SanitationHit ring I (runR hψ h2 ring p C) :=
    sanitationHit_of_agree ring I
      (runR hψ h2 ring req C) (runR hψ h2 ring p C)
      (fun i hi => (hagree i hi).symm) hhit
  unfold aliveBit
  apply if_neg
  intro halive
  rcases hp with ⟨v, rfl⟩
  have hsplit := (aliveAlong_append (step1 hψ h2 ring)
    (SanitationUnfinished ring I) C p v).mp halive
  have hU : SanitationUnfinished ring I
      (p.foldl (step1 hψ h2 ring) C) := aliveAlong_good hsplit.2
  exact sanitationHit_not_unfinished ring I
    (runR hψ h2 ring p C) hpHit hU

-- END PART 2
/-! ## Original-word mass consequence -/

private theorem power_mono_exp_san (b r s : Nat)
    (hb : 1 ≤ b) (hrs : r ≤ s) : b ^ r ≤ b ^ s := by
  have he : r + (s - r) = s := by omega
  have hd : 1 ≤ b ^ (s - r) := Nat.pow_pos (by omega)
  calc
    b ^ r ≤ b ^ r * b ^ (s - r) := Nat.le_mul_of_pos_right _ hd
    _ = b ^ s := by rw [← Nat.pow_add, he]

private theorem disjoint_escape_san (A B N Q : Nat)
    (hpair : A + B ≤ N) (hmass : N ≤ Q * B) :
    Q * A ≤ (Q - 1) * N := by
  have hs : Q * A + Q * B ≤ Q * N := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left Q hpair
  rw [Nat.sub_one_mul]
  omega

private theorem alive_mass_pad_san {S : Type}
    (step : S → Fin n → S) (Good : S → Prop) (C : S)
    (T U Q : Nat) (hTU : T ≤ U)
    (hbase : Q * aliveCount step Good C T ≤ (Q - 1) * n ^ T) :
    Q * aliveCount step Good C U ≤ (Q - 1) * n ^ U := by
  have hsum : T + (U - T) = U := by omega
  have hp := BirthTwoStageEscape.alive_pad step Good (U - T) T C
  rw [hsum] at hp
  calc
    Q * aliveCount step Good C U
        ≤ Q * (aliveCount step Good C T * n ^ (U - T)) :=
      Nat.mul_le_mul_left Q hp
    _ = (Q * aliveCount step Good C T) * n ^ (U - T) := by
      rw [Nat.mul_assoc]
    _ ≤ ((Q - 1) * n ^ T) * n ^ (U - T) :=
      Nat.mul_le_mul_right _ hbase
    _ = (Q - 1) * n ^ U := by
      rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

private theorem request_sanitation_hit_alive_mass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (req : List (Fin n)) (C : Config n ψ κ τ)
    (L M : Nat) (hM : 1 ≤ M) (hlen : req.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hne : req ≠ []) (hint : InternalWord I req)
    (hhit : SanitationHit ring I (runR hψ h2 ring req C)) :
    (4 * M) ^ L * aliveCount (step1 hψ h2 ring)
        (SanitationUnfinished ring I) C (2 * n * req.length) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * req.length) := by
  classical
  let touch : Fin n → Bool := touchOf ring (support I)
  let st : Config n ψ κ τ → Fin n → Config n ψ κ τ := step1 hψ h2 ring
  let H := 2 * n * req.length
  let A := aliveCount st (SanitationUnfinished ring I) C H
  let B := wordSum n H (fun u =>
    successWeight (runStopped (ordStep touch) (.active req) u))
  let N := n ^ H
  let Q := (4 * M) ^ L
  have hmass := B9OrderedWindowMatcher.ordered_mass touch req hne
    (fun e he => internal_touch I e (hint e he))
  rw [← B9SpliceMatcherMass.wordSum_success_eq_successCount] at hmass
  change 3 ^ req.length * N ≤
    (4 * touchCount touch) ^ req.length * B at hmass
  have hpair : A + B ≤ N := by
    change wordSum n H
        (aliveBit st (SanitationUnfinished ring I) C) +
      wordSum n H (fun u =>
        successWeight (runStopped (ordStep touch) (.active req) u)) ≤ n ^ H
    apply BirthCheckChainR1Mass.wordSum_pair_le
    intro u
    by_cases hsu :
        runStopped (ordStep touch) (.active req) u = StopNode.success
    · have hs : runNode (ordStep touch) (.active req) u = StopNode.success := by
        rw [B9SpliceMatcherMass.runNode_eq_runStopped]
        exact hsu
      have hz := matcher_success_not_sanitation_alive
        hψ h2 ring I req C hne hint hhit u hs
      change aliveBit st (SanitationUnfinished ring I) C u = 0 at hz
      rw [hz, hsu]
      show 0 + 1 ≤ 1
      exact Nat.le_refl 1
    · have hzero :
          successWeight (runStopped (ordStep touch) (.active req) u) = 0 := by
        cases hu : runStopped (ordStep touch) (.active req) u with
        | active x => rfl
        | success => exact (hsu hu).elim
        | failure => rfl
      rw [hzero, Nat.add_zero]
      exact aliveBit_le_one st (SanitationUnfinished ring I) C u
  have hbase : 4 * touchCount touch ≤ 4 * M := Nat.mul_le_mul_left 4 ht
  have hcoef : (4 * touchCount touch) ^ req.length ≤ Q :=
    Nat.le_trans (Nat.pow_le_pow_left hbase req.length)
      (power_mono_exp_san (4 * M) req.length L (by omega) hlen)
  have hthree : 1 ≤ 3 ^ req.length := Nat.pow_pos (by decide : 0 < 3)
  have hN : N ≤ 3 ^ req.length * N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N hthree
  have hscale : N ≤ Q * B :=
    Nat.le_trans hN (Nat.le_trans hmass (Nat.mul_le_mul_right B hcoef))
  change Q * A ≤ (Q - 1) * N
  exact disjoint_escape_san A B N Q hpair hscale

/--
Conditional mass theorem for one certified sanitation word.
The success event is global ReadyWindow or SanNF on this workspace; any local
physical leader also exits the `Leaderless` alive class.
-/
theorem sanitationWord_mass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C : Config n ψ κ τ)
    (L M : Nat) (hM : 1 ≤ M) (hL : w.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hsan : SanitationWord hψ h2 ring I w C) :
    (4 * M) ^ L * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (fun D => ReadyWindow ring D ∨ SanNF ring I D)
        C (2 * n * L) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * L) := by
  rcases sanitationWord_success_prefix hψ h2 ring I w C hsan with
    ⟨p, hp, hint, hhit⟩
  have hpL : p.length ≤ L := Nat.le_trans (prefix_length_le_san hp) hL
  rw [avoidCount_eq_alive_sanitation hψ h2 ring I C (2 * n * L)]
  by_cases hp0 : p = []
  · have hC : SanitationHit ring I C := by
      simpa only [hp0, runR, List.foldl_nil] using hhit
    rw [BirthTwoStageEscape.aliveCount_not_good
      (step1 hψ h2 ring) (SanitationUnfinished ring I) C
      (sanitationHit_not_unfinished ring I C hC) (2 * n * L),
      Nat.mul_zero]
    exact Nat.zero_le _
  · have hm := request_sanitation_hit_alive_mass
      hψ h2 ring I p C L M hM hpL ht hp0 hint hhit
    exact alive_mass_pad_san (step1 hψ h2 ring)
      (SanitationUnfinished ring I) C
      (2 * n * p.length) (2 * n * L) ((4 * M) ^ L)
      (Nat.mul_le_mul_left (2 * n) hpL) hm

/-- Convenient denominator using the interval's built-in touching-edge bound. -/
theorem sanitationWord_mass_interval
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C : Config n ψ κ τ)
    (L : Nat) (hL : w.length ≤ L)
    (hsan : SanitationWord hψ h2 ring I w C) :
    (4 * (I.size + 1)) ^ L * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (fun D => ReadyWindow ring D ∨ SanNF ring I D)
        C (2 * n * L) ≤
      ((4 * (I.size + 1)) ^ L - 1) * n ^ (2 * n * L) := by
  exact sanitationWord_mass hψ h2 ring I w C L (I.size + 1)
    (by omega) hL (touchCount_support_le I) hsan

/-!
PLAN -- deliberately no theorem/axiom is inserted for the missing producer.

The next file/section must construct `SanitationWord` from the intended
leaderless entrance domain.  The source-backed obligations remain:

1. Build a finite two-port active absorber inside an envelope interval; never
   request either cut edge.  Existing controlled-wrap results are global in n
   and do not provide this local word.
2. Acquire one interval-wide `WriterSilent` mode first.  Prove every later
   joint/final request satisfies `BitsStableAfter`; only then may the resident
   bit word be sampled.
3. During the joint phase, before any row whose cancellation law needs a ruler
   relation, establish that edge's local label relation and discharge the exact
   `PreparedOrdinaryOpen` gate.  No no-reentry invariant is assumed.
4. Reach `SanCells` after reset/echo/path/path2/path4/path5/p/p_carry/permit and
   live K2 bullet/signal traffic are gone.  `shield` and `stall` remain free.
5. Run a final ruler sweep and prove it preserves `SanCell` and writer silence.
6. Then package the resulting word with `SanitationWord`; the two mass theorems
   above supply the ordered-matcher consequence without any new probability
   assumption.

A universal entrance theorem should additionally carry the intended positive
`τ` witness needed later by `ReadyCell`; `SanCell` itself intentionally does
not impose `0 < q.stall.val`.
-/

end B6Sanitation

-- END PART 3
