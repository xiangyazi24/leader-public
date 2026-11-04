import Leader.Wu.Birth.LeaderlessBirthMassFirstLeaderGeneric
import Leader.Wu.Birth.TwoStageEscape


/-!
# B8 birth-closed entry contract


This file is step-generic.  The final protocol should instantiate every
predicate and every counting statement on one scheduler-visible `stepFinal`.


The B8 failure count deliberately uses `Good = True`: a cleanup trajectory
which loses all leaders before reaching `PostBirthSafe` is still a B8 failure.
The only stopping event in this count is actual entry into `PostBirthSafe`.
-/


set_option autoImplicit false
set_option Elab.async false


namespace B8EntryContract


open BirthLeaderlessBirthMassRenewal
open BirthLeaderlessBirthMassB7Generic
open BirthTwoStageEscape


/-- Positive physical-leader class relative to an abstract leaderless
predicate. -/
def PositiveLeader {S : Type}
    (Leaderless : S → Prop) (x : S) : Prop :=
  ¬ Leaderless x


/-- Exact B8 failure numerator: every prefix endpoint, including the empty
prefix and the endpoint, has not entered `PostBirthSafe`. -/
noncomputable def postBirthFailureCount
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (PostBirthSafe : S → Prop)
    (x : S) (B : Nat) : Nat :=
  avoidCount step (fun _ : S => True) PostBirthSafe x B


/-- Strengthened B8 gate.  Entry mass is measured on original scheduler
words, and the safe class is closed under the same step. -/
structure BirthClosedEntryContract
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (B Q : Nat) : Prop where
  q_pos : 1 ≤ Q
  closed :
    ∀ x e, PostBirthSafe x → PostBirthSafe (step x e)
  entry_mass :
    ∀ x, PositiveLeader Leaderless x → ¬ PostBirthSafe x →
      Q * postBirthFailureCount step PostBirthSafe x B ≤
        (Q - 1) * n ^ B


/-- Route-facing name for the generic contract. -/
abbrev B8BirthClosedEntryContract
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (B Q : Nat) : Prop :=
  BirthClosedEntryContract step Leaderless PostBirthSafe B Q


/-! ## Stopped-count identities needed by the B7+B8 composition -/


private theorem wordSum_mono_length
    {n T : Nat} (f g : List (Fin n) → Nat)
    (h : ∀ u : List (Fin n), u.length = T → f u ≤ g u) :
    FixedSpanRenewalPayload.wordSum n T f ≤
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)


private theorem avoidAlong_mono_good
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Good Good' R : S → Prop)
    (hGood : ∀ x, Good x → Good' x) :
    ∀ (x : S) (w : List (Fin n)),
      AvoidAlong step Good R x w → AvoidAlong step Good' R x w
  | x, [], h => ⟨hGood x h.1, h.2⟩
  | x, e :: w, h =>
      ⟨⟨hGood x h.1.1, h.1.2⟩,
        avoidAlong_mono_good step Good Good' R hGood
          (step x e) w h.2⟩


private theorem avoidCount_mono_good
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Good Good' R : S → Prop)
    (hGood : ∀ x, Good x → Good' x)
    (x : S) (T : Nat) :
    avoidCount step Good R x T ≤ avoidCount step Good' R x T := by
  unfold avoidCount
  apply wordSum_mono_length
  intro w _
  classical
  unfold avoidBit
  by_cases h : AvoidAlong step Good R x w
  · have h' := avoidAlong_mono_good
      step Good Good' R hGood x w h
    simp [h, h']
  · simp [h]


private theorem avoidAlong_true_safe_iff_alive_not_safe
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Safe : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      AvoidAlong step (fun _ : S => True) Safe x w ↔
        AliveAlong step (fun y => ¬ Safe y) x w
  | x, [] => by
      change (True ∧ ¬ Safe x) ↔ ¬ Safe x
      simp
  | x, e :: w => by
      change
        ((True ∧ ¬ Safe x) ∧
          AvoidAlong step (fun _ : S => True) Safe (step x e) w) ↔
        ((¬ Safe x) ∧
          AliveAlong step (fun y => ¬ Safe y) (step x e) w)
      rw [avoidAlong_true_safe_iff_alive_not_safe
        step Safe (step x e) w]
      simp


/-- The B8 failure count is the generic renewal count for staying outside the
safe set. -/
theorem postBirthFailureCount_eq_alive_not_safe
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Safe : S → Prop)
    (x : S) (T : Nat) :
    postBirthFailureCount step Safe x T =
      aliveCount step (fun y => ¬ Safe y) x T := by
  unfold postBirthFailureCount avoidCount aliveCount
  have hbits :
      avoidBit step (fun _ : S => True) Safe x =
        aliveBit step (fun y => ¬ Safe y) x := by
    funext w
    classical
    unfold avoidBit aliveBit
    rw [avoidAlong_true_safe_iff_alive_not_safe step Safe x w]
  rw [hbits]


private theorem avoidAlong_true_positive_iff_alive_leaderless
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Leaderless : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      AvoidAlong step (fun _ : S => True)
          (PositiveLeader Leaderless) x w ↔
        AliveAlong step Leaderless x w
  | x, [] => by
      change (True ∧ ¬ PositiveLeader Leaderless x) ↔ Leaderless x
      unfold PositiveLeader
      constructor
      · intro h
        exact Classical.byContradiction (fun hn => h.2 hn)
      · intro h
        exact ⟨True.intro, fun hn => hn h⟩
  | x, e :: w => by
      change
        ((True ∧ ¬ PositiveLeader Leaderless x) ∧
          AvoidAlong step (fun _ : S => True)
            (PositiveLeader Leaderless) (step x e) w) ↔
        (Leaderless x ∧ AliveAlong step Leaderless (step x e) w)
      rw [avoidAlong_true_positive_iff_alive_leaderless
        step Leaderless (step x e) w]
      unfold PositiveLeader
      constructor
      · intro h
        have hx : Leaderless x :=
          Classical.byContradiction (fun hn => h.1.2 hn)
        exact ⟨hx, h.2⟩
      · intro h
        exact ⟨⟨True.intro, fun hn => hn h.1⟩, h.2⟩


/-- Avoiding the positive-leader class while otherwise unrestricted is exactly
remaining leaderless along every prefix endpoint. -/
theorem avoidCount_true_positive_eq_alive_leaderless
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Leaderless : S → Prop)
    (x : S) (T : Nat) :
    avoidCount step (fun _ : S => True)
        (PositiveLeader Leaderless) x T =
      aliveCount step Leaderless x T := by
  unfold avoidCount aliveCount
  have hbits :
      avoidBit step (fun _ : S => True)
          (PositiveLeader Leaderless) x =
        aliveBit step Leaderless x := by
    funext w
    classical
    unfold avoidBit aliveBit
    rw [avoidAlong_true_positive_iff_alive_leaderless
      step Leaderless x w]
  rw [hbits]


-- END PART 1
/-! ## B7 first leader followed by B8 birth-closed entry -/


/-- One two-stage block: either the B7 stage reaches the positive-leader class,
or the B8 stage reaches `PostBirthSafe`.  The surviving bad class is exactly
`¬ PostBirthSafe`; no premise says that a leader must survive the B8 stage. -/
theorem b7_then_birthClosedEntry_uniformEscape
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (L B Q : Nat)
    (hB7 : UniformFirstHitBirthMass step Leaderless L)
    (hB8 : BirthClosedEntryContract
      step Leaderless PostBirthSafe B Q) :
    UniformEscapeMass step (fun x => ¬ PostBirthSafe x)
      (L + B) (8 * Q) := by
  have hB7' : UniformEscapeMass step Leaderless L 8 := hB7
  refine BirthTwoStageEscape.two_stage_escape
    step (fun x => ¬ PostBirthSafe x) (PositiveLeader Leaderless)
      L B 8 Q (by decide) hB8.q_pos ?_ ?_
  · intro x hx
    by_cases hp : PositiveLeader Leaderless x
    · have hz := BirthTwoStageEscape.avoidCount_zero_of
        step (fun y => ¬ PostBirthSafe y)
          (PositiveLeader Leaderless) x
          (fun h => h.2 hp) L
      rw [hz]
      simp
    · have hL : Leaderless x := by
        exact Classical.byContradiction (fun hn => hp hn)
      have hmono := avoidCount_mono_good
        step (fun y => ¬ PostBirthSafe y) (fun _ : S => True)
          (PositiveLeader Leaderless) (fun _ _ => True.intro) x L
      have heq := avoidCount_true_positive_eq_alive_leaderless
        step Leaderless x L
      have hb :
          8 * aliveCount step Leaderless x L ≤
            (8 - 1) * n ^ L :=
        hB7' x hL
      calc
        8 * avoidCount step (fun y => ¬ PostBirthSafe y)
              (PositiveLeader Leaderless) x L
            ≤ 8 * avoidCount step (fun _ : S => True)
              (PositiveLeader Leaderless) x L :=
          Nat.mul_le_mul_left 8 hmono
        _ = 8 * aliveCount step Leaderless x L := by rw [heq]
        _ ≤ (8 - 1) * n ^ L := hb
  · intro x hx hp
    have hm := hB8.entry_mass x hp hx
    rw [postBirthFailureCount_eq_alive_not_safe
      step PostBirthSafe x B] at hm
    exact hm


/-- Boost the product denominator `8 * Q` back to the public B7 denominator
8. -/
theorem b7_then_birthClosedEntry_uniformFirstHit
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (L B Q : Nat)
    (hB7 : UniformFirstHitBirthMass step Leaderless L)
    (hB8 : BirthClosedEntryContract
      step Leaderless PostBirthSafe B Q) :
    UniformFirstHitBirthMass step (fun x => ¬ PostBirthSafe x)
      (3 * (8 * Q) * (L + B)) := by
  change UniformEscapeMass step (fun x => ¬ PostBirthSafe x)
    (3 * (8 * Q) * (L + B)) 8
  have hblock := b7_then_birthClosedEntry_uniformEscape
    step Leaderless PostBirthSafe L B Q hB7 hB8
  have h8Q : 1 ≤ 8 * Q := by
    calc
      1 ≤ 8 := by decide
      _ ≤ 8 * Q := Nat.le_mul_of_pos_right 8 hB8.q_pos
  exact BirthLeafBoost.escape_boost
    step (fun x => ¬ PostBirthSafe x) (L + B) (8 * Q) h8Q hblock


/-- Generic B7+B8 capstone: on the same step, failure to enter the closed
post-birth safe class has probability at most `1/n` at the displayed horizon. -/
theorem b7_then_birthClosedEntry_failure_le_one_over_n
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (L B Q : Nat)
    (hB7 : UniformFirstHitBirthMass step Leaderless L)
    (hB8 : BirthClosedEntryContract
      step Leaderless PostBirthSafe B Q)
    (hn : 2 ≤ n) (x : S) (hx : ¬ PostBirthSafe x) :
    n * firstLeaderFailureNumerator
        step (fun y => ¬ PostBirthSafe y) x
        (6 * (Nat.log2 n + 1) * (3 * (8 * Q) * (L + B))) ≤
      n ^ (6 * (Nat.log2 n + 1) * (3 * (8 * Q) * (L + B))) := by
  have hm := b7_then_birthClosedEntry_uniformFirstHit
    step Leaderless PostBirthSafe L B Q hB7 hB8
  exact firstLeader_failure_le_one_over_n_of_uniformBirthMass
    step (fun y => ¬ PostBirthSafe y)
      (3 * (8 * Q) * (L + B)) hm hn x hx


/-! ## Named generic obligations used by the eventual final-step instance -/


/-- B7 must be established on exactly the same scheduler-visible step. -/
def B7FinalFirstLeaderMassObligation
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Leaderless : S → Prop)
    (L : Nat) : Prop :=
  UniformFirstHitBirthMass step Leaderless L


/-- B9 must close the full post-birth safe set under the final step. -/
def B9PostBirthSafeClosureObligation
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (PostBirthSafe : S → Prop) : Prop :=
  ∀ x e, PostBirthSafe x → PostBirthSafe (step x e)


/-- B10 is only a bounded producer.  It deliberately makes no mass claim. -/
def B10PositiveLeaderEntryWordObligation
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop) (B : Nat) : Prop :=
  ∀ x, PositiveLeader Leaderless x → ¬ PostBirthSafe x →
    ∃ w : List (Fin n),
      w.length ≤ B ∧ PostBirthSafe (w.foldl step x)


/-- B11 is the original-scheduler mass upgrade actually required by B8. -/
def B11PositiveLeaderEntryMassObligation
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (B Q : Nat) : Prop :=
  ∀ x, PositiveLeader Leaderless x → ¬ PostBirthSafe x →
    Q * postBirthFailureCount step PostBirthSafe x B ≤
      (Q - 1) * n ^ B


/-- B9 closure plus B11 mass package exactly into the generic B8 contract.
B10 is not a premise: existence of one good word does not imply scheduler
mass. -/
theorem birthClosedEntryContract_of_B9_B11
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Leaderless PostBirthSafe : S → Prop)
    (B Q : Nat) (hQ : 1 ≤ Q)
    (hB9 : B9PostBirthSafeClosureObligation step PostBirthSafe)
    (hB11 : B11PositiveLeaderEntryMassObligation
      step Leaderless PostBirthSafe B Q) :
    BirthClosedEntryContract step Leaderless PostBirthSafe B Q := by
  exact ⟨hQ, hB9, hB11⟩


/-!
PLAN — final B9+R1 instantiation only; nothing in this block is parsed code.


On source snapshot 464d461f855d188036e40f4d0e74a0bf84297500,
`Leader/Wu/Splice/HostTable.lean` is not a tracked source file.  Do not invent a
`FinalState` carrier or `stepFinal` here.  Once the host-parametric B9 table
lands, instantiate the generic declarations above on that exact carrier and
step, with the following final names/obligations:


* `FinalLeaderless`: current-state physical leaderlessness predicate.
* `PostBirthSafeFinal`: current-state closed safe predicate; it must not be a
  future-quantified reachability predicate.
* `b9_postBirthSafe_closed`: proves one-step closure of `PostBirthSafeFinal`
  under `stepFinal`.
* `b10_positiveLeader_entry_word`: bounded producer from every positive-leader
  state outside `PostBirthSafeFinal`.
* `b11_positiveLeader_entry_mass`: original-scheduler mass inequality matching
  `B11PositiveLeaderEntryMassObligation`.
* `b8_birthClosedEntryContract_stepFinal`: packages B9 closure and B11 mass by
  `birthClosedEntryContract_of_B9_B11`.
* `final_reach_postBirthSafe_failure_le_one_over_n`: instantiates
  `b7_then_birthClosedEntry_failure_le_one_over_n` with the B7 generic tail and
  the B8 contract on the same `stepFinal`.


B9 must prove closure of the full final safe predicate, not merely an older
controller-only `SpliceSafe`.  B10 may use bounded progress/cohort/lineage
machinery to manufacture a word.  B11 must count original `stepFinal` scheduler
words directly (or through a proved bounded-fiber coupling); B10 existence by
itself is not enough.
-/


end B8EntryContract


-- END PART 2
