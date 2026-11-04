import Leader.PPL.ReachCPB.Capped
import Leader.PPL.Modes.DetectionEntryClosed


/-!
# Lemma 16: mode-capped Lemma-6 block


Truth audit: the capped statement is true with the frozen horizon and constant.


The useful normalization is not to trust a stale stored Detect bit.  Before
running Lemma 6, erase only a Detect/Construct bit whose clock is strictly
below kappa.  A scheduled pair immediately passes through DetermineMode, which
overwrites both modes from the post-update clocks before Algorithms 2 and 3
read them.  Thus this erasure is semantically invisible to the physical pair
step.  Conversely, every Detect bit in the scrubbed execution is backed by an
actual clock value kappa.


Therefore ordinary Lemma-6 success in the scrubbed execution implies either
CPB or DetectReadyCapped in the original execution.  The already-proved
unconditional Lemma 6 then gives exactly


  H6 = 16 * n * kappa * 2^psi
  coefficient = 8.


No change to lemma16_wordBound_capped is required.


This bounded file leaves exactly one single-interaction obligation:
ModeScrubOneStepSpec.  It is the literal statement that the relation below is
preserved by one P_PL interaction.  Its source proof is a finite unfolding of
DetermineMode plus the fact that the Algorithms 2/3/5 suffix does not restore
the pre-DetermineMode mode.
-/


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


private def eraseStoredMode {psi kappa : Nat}
    (q : PPL.State psi kappa) : PPL.State psi kappa :=
  { q with mode := false }


private def modeScrubState {psi kappa : Nat}
    (q : PPL.State psi kappa) : PPL.State psi kappa :=
  if q.clock.val < kappa then
    { q with mode := false }
  else
    q


private def modeScrubConfig
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Config n psi kappa :=
  fun i => modeScrubState (C i)


/-- The two configurations agree on every field except possibly the stored
mode.  A Detect bit on the scrubbed side is trustworthy: the original side
also has Detect and its clock is actually capped. -/
def ModeScrubRelState {psi kappa : Nat}
    (q d : PPL.State psi kappa) : Prop :=
  And
    (eraseStoredMode q = eraseStoredMode d)
    (d.mode = true →
      And (q.mode = true) (q.clock.val = kappa))


def ModeScrubRel
    {n psi kappa : Nat}
    (C D : Config n psi kappa) : Prop :=
  ∀ i : Fin n, ModeScrubRelState (C i) (D i)


private theorem modeScrubState_rel
    {psi kappa : Nat}
    (q : PPL.State psi kappa) :
    ModeScrubRelState q (modeScrubState q) := by
  unfold ModeScrubRelState modeScrubState
  by_cases hlt : q.clock.val < kappa
  · rw [if_pos hlt]
    apply And.intro
    · rfl
    · intro hmode
      simp at hmode
  · rw [if_neg hlt]
    apply And.intro
    · rfl
    · intro hmode
      apply And.intro hmode
      have hbound := q.clock.isLt
      omega


private theorem modeScrubConfig_rel
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    ModeScrubRel C (modeScrubConfig C) := by
  intro i
  exact modeScrubState_rel (C i)


private theorem modeRel_leader
    {psi kappa : Nat}
    {q d : PPL.State psi kappa}
    (h : ModeScrubRelState q d) :
    q.leader = d.leader := by
  have hx :=
    congrArg
      (fun z : PPL.State psi kappa => z.leader)
      h.1
  simpa [eraseStoredMode] using hx


private theorem modeRel_signalR
    {psi kappa : Nat}
    {q d : PPL.State psi kappa}
    (h : ModeScrubRelState q d) :
    q.signalR = d.signalR := by
  have hx :=
    congrArg
      (fun z : PPL.State psi kappa => z.signalR)
      h.1
  simpa [eraseStoredMode] using hx


/-- The sole remaining literal one-interaction leaf.


For the scheduled pair, eraseStoredMode equality says that the inputs differ
only in mode.  DetermineMode does not branch on the incoming mode and its
finishModes assignment overwrites both endpoint modes from clock = kappa.
The rest of P_PL preserves those timer/mode fields.  Off the selected pair the
configuration is unchanged. -/
def ModeScrubOneStepSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C D : Config n psi kappa)
      (e : Fin n),
    ModeScrubRel C D →
      ModeScrubRel
        (PPL.Probability.pplStep ring C e)
        (PPL.Probability.pplStep ring D e)


/-! Small Boolean folds, copied locally because the corresponding Lemma-6
helpers are private. -/


private theorem mcFoldlAnd_gen :
    ∀ (xs : List Bool) (init : Bool),
      xs.foldl (fun a b => a && b) init = true ->
        And (init = true) (∀ b, b ∈ xs -> b = true)
  | [], init, h => by
      refine ⟨by simpa using h, ?_⟩
      intro b hb
      simp at hb
  | x :: xs, init, h => by
      have h' := mcFoldlAnd_gen xs (init && x) h
      have hix : And (init = true) (x = true) := by
        simpa using h'.1
      refine ⟨hix.1, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb]
        exact hix.2
      · exact h'.2 b hb


private theorem mcFoldlAndTrue_allTrue
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = true) :
    ∀ b, b ∈ xs → b = true :=
  (mcFoldlAnd_gen xs true h).2


private theorem mcFoldlAndTrue_of_allTrue
    (xs : List Bool)
    (h : ∀ b, b ∈ xs → b = true) :
    xs.foldl (fun a b => a && b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      have ha : a = true :=
        h a (by simp)
      have ht : ∀ b, b ∈ xs → b = true := by
        intro b hb
        exact h b (by simp [hb])
      simpa [List.foldl_cons, ha] using ih ht


private theorem mcAllAgents_true_at
    {n : Nat}
    (p : Fin n → Bool)
    (h : PPL.Modes.Lemma6.allAgentsB p = true)
    (i : Fin n) :
    p i = true := by
  unfold PPL.Modes.Lemma6.allAgentsB at h
  have hall :=
    mcFoldlAndTrue_allTrue
      (List.ofFn p) h
  apply hall (p i)
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩


private theorem mcAllAgents_true_of
    {n : Nat}
    (p : Fin n → Bool)
    (h : ∀ i : Fin n, p i = true) :
    PPL.Modes.Lemma6.allAgentsB p = true := by
  unfold PPL.Modes.Lemma6.allAgentsB
  apply mcFoldlAndTrue_of_allTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  exact h i


private theorem mcFoldlOr_true
    (xs : List Bool) :
    xs.foldl (fun a b => a || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simpa [List.foldl_cons] using ih


private theorem mcFoldlOr_false_allFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a || b) false = false) :
    ∀ b, b ∈ xs → b = false := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht :
              xs.foldl (fun u v => u || v) false = false := by
            simpa [List.foldl_cons, ha] using h
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            rfl
          · exact ih ht b hb
      | true =>
          have ht :
              xs.foldl (fun u v => u || v) true = true :=
            mcFoldlOr_true xs
          rw [List.foldl_cons, ha] at h
          simp only [Bool.false_or] at h
          rw [ht] at h
          cases h


private theorem mcFoldlOr_true_existsTrue
    (xs : List Bool)
    (h : xs.foldl (fun a b => a || b) false = true) :
    ∃ b, And (b ∈ xs) (b = true) := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | true =>
          exact
            ⟨true, And.intro (by simp) rfl⟩
      | false =>
          have ht :
              xs.foldl (fun u v => u || v) false = true := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hb⟩ := ih ht
          exact
            ⟨b, And.intro (by simp [hb.1]) hb.2⟩


private theorem mcLeaderPresent_false_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : PPL.Probability.leaderPresent C = false)
    (i : Fin n) :
    (C i).leader = false := by
  unfold PPL.Probability.leaderPresent at h
  have hall :=
    mcFoldlOr_false_allFalse
      (List.ofFn
        (fun j : Fin n => (C j).leader))
      h
  apply hall (C i).leader
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩


private theorem mcLeaderPresent_true_exists
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : PPL.Probability.leaderPresent C = true) :
    ∃ i : Fin n, (C i).leader = true := by
  unfold PPL.Probability.leaderPresent at h
  obtain ⟨b, hbmem, hbt⟩ :=
    mcFoldlOr_true_existsTrue
      (List.ofFn
        (fun i : Fin n => (C i).leader))
      h
  rw [List.mem_ofFn] at hbmem
  obtain ⟨i, hi⟩ := hbmem
  exact ⟨i, hi.trans hbt⟩


/-- Ordinary Lemma-6 success on the scrubbed side is already the desired
capped success on the original side. -/
private theorem mcLemma6Good_of_modeScrub
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (hrel : ModeScrubRel C D)
    (hpeace : AllLivePeaceful ring C)
    (hgood : PPL.Modes.Lemma6.lemma6GoodB D = true) :
    Or (PPL.CPB ring C) (DetectReadyCapped ring C) := by
  unfold PPL.Modes.Lemma6.lemma6GoodB at hgood
  cases hl : PPL.Probability.leaderPresent D with
  | true =>
      obtain ⟨i, hiD⟩ :=
        mcLeaderPresent_true_exists D hl
      have hiC : (C i).leader = true := by
        have heq :=
          modeRel_leader (hrel i)
        rw [heq]
        exact hiD
      exact
        Or.inl
          (cpb_of_allLivePeaceful_hasLeader
            ring C hpeace ⟨i, hiC⟩)
  | false =>
      cases hs : PPL.Modes.Lemma6.signalFreeB D with
      | false =>
          simp [hl, hs] at hgood
      | true =>
          cases hd : PPL.Modes.Lemma6.allDetectB D with
          | false =>
              simp [hl, hs, hd] at hgood
          | true =>
              have hsAll :
                  PPL.Modes.Lemma6.allAgentsB
                    (fun i : Fin n =>
                      decide ((D i).signalR.val = 0)) = true := by
                simpa [PPL.Modes.Lemma6.signalFreeB] using hs
              have hdAll :
                  PPL.Modes.Lemma6.allAgentsB
                    (fun i : Fin n =>
                      decide ((D i).mode = true)) = true := by
                simpa [PPL.Modes.Lemma6.allDetectB] using hd
              have hDmode :
                  ∀ i : Fin n, (D i).mode = true := by
                intro i
                have hb :=
                  mcAllAgents_true_at
                    (fun j : Fin n =>
                      decide ((D j).mode = true))
                    hdAll i
                exact of_decide_eq_true hb
              have hleaderC :
                  ∀ i : Fin n, (C i).leader = false := by
                intro i
                have hD :=
                  mcLeaderPresent_false_at D hl i
                have heq :=
                  modeRel_leader (hrel i)
                rw [heq]
                exact hD
              have hsignalC :
                  PPL.Modes.Lemma6.signalFreeB C = true := by
                unfold PPL.Modes.Lemma6.signalFreeB
                apply mcAllAgents_true_of
                intro i
                have hb :=
                  mcAllAgents_true_at
                    (fun j : Fin n =>
                      decide ((D j).signalR.val = 0))
                    hsAll i
                have hDz :
                    (D i).signalR.val = 0 :=
                  of_decide_eq_true hb
                have heq :=
                  modeRel_signalR (hrel i)
                have hCz :
                    (C i).signalR.val = 0 := by
                  rw [heq]
                  exact hDz
                simp [hCz]
              have hdetectC :
                  PPL.Modes.Lemma6.allDetectB C = true := by
                unfold PPL.Modes.Lemma6.allDetectB
                apply mcAllAgents_true_of
                intro i
                have hm :=
                  (hrel i).2 (hDmode i)
                simp [hm.1]
              have hcapC :
                  ∀ i : Fin n, (C i).clock.val = kappa := by
                intro i
                exact ((hrel i).2 (hDmode i)).2
              have hready :
                  DetectReady ring C :=
                And.intro hpeace
                  (And.intro hleaderC
                    (And.intro hsignalC hdetectC))
              exact
                Or.inr
                  (And.intro hready hcapC)


/-- A Lemma-6 success prefix on the scrubbed execution gives a capped success
prefix on the original execution. -/
private theorem mcReachesAux_implies_capped
    (hstep : ModeScrubOneStepSpec)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (word : DetSchedule n)
    (hrel : ModeScrubRel C D)
    (hpeace : AllLivePeaceful ring C)
    (haux :
      PPL.Modes.Lemma6.reachesAux
        ring D word = true) :
    reachesDetectCappedOrCPB
      ring C word = true := by
  induction word generalizing C D with
  | nil =>
      have hgood :
          PPL.Modes.Lemma6.lemma6GoodB D = true := by
        simpa [PPL.Modes.Lemma6.reachesAux] using haux
      have hor :=
        mcLemma6Good_of_modeScrub
          ring C D hrel hpeace hgood
      have htarget :
          detectCappedOrCPBB ring C = true := by
        simp [detectCappedOrCPBB, hor]
      simpa [reachesDetectCappedOrCPB] using htarget
  | cons e rest ih =>
      cases hgood :
          PPL.Modes.Lemma6.lemma6GoodB D with
      | true =>
          have hor :=
            mcLemma6Good_of_modeScrub
              ring C D hrel hpeace hgood
          have htarget :
              detectCappedOrCPBB ring C = true := by
            simp [detectCappedOrCPBB, hor]
          simp [reachesDetectCappedOrCPB, htarget]
      | false =>
          have htail :
              PPL.Modes.Lemma6.reachesAux
                  ring
                  (PPL.Probability.pplStep ring D e)
                  rest = true := by
            simpa [PPL.Modes.Lemma6.reachesAux, hgood]
              using haux
          have hrel' :
              ModeScrubRel
                (PPL.Probability.pplStep ring C e)
                (PPL.Probability.pplStep ring D e) :=
            hstep hpsi ring C D e hrel
          have hpeace' :
              AllLivePeaceful ring
                (PPL.Probability.pplStep ring C e) := by
            simpa [PPL.Probability.pplStep] using
              (allLivePeaceful_step_closed
                hn3 hpsi ring C e hpeace)
          have htailReach :=
            ih
              (C := PPL.Probability.pplStep ring C e)
              (D := PPL.Probability.pplStep ring D e)
              hrel' hpeace' htail
          have htailReach' :
              reachesDetectCappedOrCPB
                ring
                (PopulationProtocol.step
                  (PPL.protocol psi kappa) ring C e)
                rest = true := by
            simpa [PPL.Probability.pplStep] using
              htailReach
          simp [reachesDetectCappedOrCPB, htailReach']


private theorem mcCountP_mono
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (hpq : ∀ x, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true :=
            hpq x hp
          simp [hp, hqx]
          omega


/-- Capped Lemma-16 mode phase, reduced to one literal one-step scrub lemma.


The supplied Lemma6ClockRiseCount hypothesis is not needed after importing
Lemma6Closed: the unconditional Lemma-6 theorem already contains its proved
clock-rise argument. -/
theorem lemma16ModeCappedReachCount
    (hstep : ModeScrubOneStepSpec) :
    Lemma16ModeCappedReachCountSpec := by
  unfold Lemma16ModeCappedReachCountSpec
  intro n psi kappa modeC
  intro hn3 hpsi hc hkappa hnpow
  intro ring C hpeace _hclock


  let D : Config n psi kappa :=
    modeScrubConfig C


  have hrel0 :
      ModeScrubRel C D := by
    dsimp [D]
    exact modeScrubConfig_rel C


  have hH :=
    lemma16H6_eq_lemma6Horizon
      (n := n) (psi := psi)
      (kappa := kappa) (modeC := modeC)
      hkappa


  have hmono :
      lemma16ModeCappedReachFailureCount
          ring C (lemma16H6 n psi kappa) ≤
        PPL.Modes.Lemma6.lemma6FailureCount
          ring D modeC := by
    rw [hH]
    unfold lemma16ModeCappedReachFailureCount
      PPL.Modes.Lemma6.lemma6FailureCount
    apply mcCountP_mono
    intro word hbad
    have hcapFalse :
        reachesDetectCappedOrCPB
          ring C word = false := by
      cases hr :
          reachesDetectCappedOrCPB ring C word with
      | false =>
          rfl
      | true =>
          simp [hr] at hbad
    cases haux :
        PPL.Modes.Lemma6.reachesAux
          ring D word with
    | false =>
        simp [haux]
    | true =>
        have hcapTrue :=
          mcReachesAux_implies_capped
            hstep hn3 hpsi
            ring C D word hrel0 hpeace haux
        rw [hcapFalse] at hcapTrue
        cases hcapTrue


  have hscaled :=
    Nat.mul_le_mul_left n hmono


  have h6 :=
    PPL.Modes.Lemma6.lemma6_wordBound_closed
      hn3 hpsi hc hkappa hnpow
      ring D


  unfold PPL.Modes.Lemma6.Lemma6WordBound at h6


  have hfinal :
      n *
          lemma16ModeCappedReachFailureCount
            ring C (lemma16H6 n psi kappa) ≤
        8 *
          n ^
            PPL.Modes.Lemma6.lemma6Horizon
              n psi modeC :=
    Nat.le_trans hscaled h6


  simpa [hH] using hfinal


#print axioms PPL.Convergence.ReachCPB.lemma16ModeCappedReachCount


end PPL.Convergence.ReachCPB


