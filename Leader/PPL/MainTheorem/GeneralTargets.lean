import Leader.PPL.MainTheorem.Statement

/-!
# P_PL Theorem 1, general targets: hitting tests and bad events with the target as a parameter

The `psi < n` chain (`PPL.PsiBelowN`, target `S_PL`) and the `n ≤ psi`
chain (`PPL.PsiAtLeastN`, the safe target) use the same argument with two
different targets:

* the global target, tested along the full `P_PL` run by a prefix-hitting
  Boolean (`theorem1ReachesSPL` or `theorem1ReachesSafeTarget`);
* the rooted target, tested along the `P_PL'` run of the L18 slice
  (`l18HitsSPL` or `l18HitsSafe`), which enters the L18 bad events through
  "every leader root misses".

Here the target is a parameter: `theorem1ReachesB ring tgt` and
`theorem1L18HitsB ring loc` are the prefix-hitting tests for a Boolean
predicate; `theorem1AllLeaderRootsMissGen`, `theorem1Bad18Gen` and
`theorem1L18FirstHitPhaseBadGen` are the L18 miss, bad and phase events for
a rooted Boolean predicate.  The bridging equalities at the end identify the
`S_PL` definitions of `PPL` with these; the safe ones are identified in
`PPL.PsiAtLeastN.SafeRows`.

P_PL Theorem 1 cleanup, phase 2, steps 6b-6c.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Prefix-hitting tests for a Boolean target -/

/-- Prefix-hitting test along the full `P_PL` run for a Boolean target
`tgt`: some prefix endpoint, including the initial and the final
configuration, satisfies `tgt`. -/
def theorem1ReachesB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (tgt : Config n psi kappa → Bool) :
    Config n psi kappa → DetSchedule n → Bool
  | C, [] =>
      tgt C
  | C, e :: rest =>
      tgt C ||
        theorem1ReachesB ring tgt
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          rest

/-- Prefix-hitting test along the `P_PL'` run for a Boolean predicate
(the shape of `PPL.Convergence.L18.l18HitsSPL`). -/
def theorem1L18HitsB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (loc : Config n psi kappa → Bool) :
    Config n psi kappa → DetSchedule n → Bool
  | C, [] =>
      loc C
  | C, e :: es =>
      loc C ||
        theorem1L18HitsB ring loc
          (PPL.Convergence.L18.pprimeStep ring C e) es

/-- Every leader root misses its rooted predicate along the `P_PL'` run
(`PPL.theorem1AllLeaderRootsMissB` with the rooted predicate a
parameter). -/
def theorem1AllLeaderRootsMissGen
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  (List.ofFn
      (fun root : Fin n =>
        (!(C root).leader) ||
          !(theorem1L18HitsB ring (loc root) C word))).foldl
    (fun a b => a && b) true

/-- The L18 bad event (`PPL.theorem1Bad18B`) with the rooted predicate a
parameter. -/
def theorem1Bad18Gen
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match theorem1MidCut ring C0 word,
      theorem1MidState ring C0 word with
  | some t, some Cmid =>
      let C17 :=
        theorem1Prime17End ring Cmid t word
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) &&
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word) &&
        decide
          (PPL.LiteralL1
            (theorem1Literal17End
              ring Cmid t word)) &&
        theorem1AllLeaderRootsMissGen
          ring loc C17
          (theorem1L18Word psi t word)
  | _, _ => false

/-- The L18 phase event at a dynamic first-hit cut
(`PPL.theorem1L18FirstHitPhaseBad`) with the rooted predicate a parameter. -/
def theorem1L18FirstHitPhaseBadGen
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  let Cmid :=
    PPL.Probability.runPPL ring C0 p
  let w17 :=
    phase.take (theorem1H17 n)
  let C17 :=
    PPL.Convergence.ConstructCoupling.runPrime
      ring Cmid w17
  (PPL.Modes.Lemma5.constructAlong
      ring Cmid phase &&
    @decide
      (PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring
          (PPL.Elim.viewConfig Cmid)
          w17))
      (theorem1LiteralL1Decidable _)) &&
    theorem1AllLeaderRootsMissGen
      ring loc C17
      ((phase.drop (theorem1H17 n)).take
        (theorem1H18 n psi))

/-! ## Hitting lemmas -/

/-- Prefix hitting is monotone under appending a suffix. -/
theorem theorem1ReachesB_append_of_left
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (tgt : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (pre suf : DetSchedule n)
    (hpre : theorem1ReachesB ring tgt C pre = true) :
    theorem1ReachesB ring tgt C (pre ++ suf) = true := by
  induction pre generalizing C with
  | nil =>
      cases suf with
      | nil =>
          simpa using hpre
      | cons e rest =>
          have hhere : tgt C = true := by
            simpa [theorem1ReachesB] using hpre
          simp [theorem1ReachesB, hhere]
  | cons e rest ih =>
      simp only [List.cons_append, theorem1ReachesB] at hpre ⊢
      cases hhere : tgt C with
      | false =>
          simp only [hhere, Bool.false_or] at hpre ⊢
          exact
            ih (C := PopulationProtocol.step (protocol psi kappa) ring C e)
              hpre
      | true =>
          simp

/-- A hit of the run started after `pre` is a hit of `pre ++ suf`. -/
theorem theorem1ReachesB_append_right
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (tgt : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (pre suf : DetSchedule n)
    (hsuf :
      theorem1ReachesB ring tgt
        (PPL.Probability.runPPL ring C pre) suf = true) :
    theorem1ReachesB ring tgt C (pre ++ suf) = true := by
  induction pre generalizing C with
  | nil =>
      simpa
        [PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
        using hsuf
  | cons e rest ih =>
      have htail :
          theorem1ReachesB ring tgt
              (PPL.Probability.runPPL ring
                (PPL.Probability.pplStep ring C e) rest)
              suf =
            true := by
        simpa
          [PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule,
            PPL.Probability.pplStep]
          using hsuf
      have hih :=
        ih (C := PPL.Probability.pplStep ring C e) htail
      simp only [List.cons_append, theorem1ReachesB]
      change
        (tgt C ||
            theorem1ReachesB ring tgt
              (PPL.Probability.pplStep ring C e)
              (rest ++ suf)) =
          true
      simp [hih]

/-- A word whose `P_PL` endpoint satisfies the target hits it. -/
theorem theorem1ReachesB_of_endpoint
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (tgt : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hend : tgt (PPL.Probability.runPPL ring C word) = true) :
    theorem1ReachesB ring tgt C word = true := by
  have hnil :
      theorem1ReachesB ring tgt
          (PPL.Probability.runPPL ring C word) [] =
        true := by
    simp [theorem1ReachesB, hend]
  simpa using
    theorem1ReachesB_append_right ring tgt C word [] hnil

/-- A `P_PL'` hit is witnessed by a prefix whose `P_PL'` endpoint satisfies
the predicate. -/
theorem theorem1L18HitsB_exists_prefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (loc : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hhit : theorem1L18HitsB ring loc C word = true) :
    ∃ pre suf : DetSchedule n,
      word = pre ++ suf ∧
        loc (PPL.Convergence.L18.runPPrime ring C pre) = true := by
  induction word generalizing C with
  | nil =>
      exact
        ⟨[], [], rfl,
          by simpa [theorem1L18HitsB, PPL.Convergence.L18.runPPrime] using hhit⟩
  | cons e rest ih =>
      cases hnow : loc C with
      | true =>
          refine ⟨[], e :: rest, by simp, ?_⟩
          simpa [PPL.Convergence.L18.runPPrime] using hnow
      | false =>
          have htail :
              theorem1L18HitsB ring loc
                  (PPL.Convergence.L18.pprimeStep ring C e) rest =
                true := by
            simpa [theorem1L18HitsB, hnow] using hhit
          obtain ⟨pre, suf, hrest, hloc⟩ :=
            ih (C := PPL.Convergence.L18.pprimeStep ring C e) htail
          refine ⟨e :: pre, suf, ?_, ?_⟩
          · simp [hrest]
          · simpa [PPL.Convergence.L18.runPPrime] using hloc

/-- A left fold of `&&` that is false has a false entry. -/
theorem theorem1FoldlAnd_false_exists
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = false) :
    ∃ b, b ∈ xs ∧ b = false := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | false =>
          exact ⟨false, by simp, rfl⟩
      | true =>
          have ht :
              xs.foldl (fun u v => u && v) true = false := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hbmem, hb⟩ := ih ht
          exact ⟨b, by simp [hbmem], hb⟩

/-- If not every leader root misses, some leader root hits. -/
theorem theorem1AllLeaderRootsMissGen_false_exists_hit
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hmiss : theorem1AllLeaderRootsMissGen ring loc C word = false) :
    ∃ root : Fin n,
      (C root).leader = true ∧
        theorem1L18HitsB ring (loc root) C word = true := by
  unfold theorem1AllLeaderRootsMissGen at hmiss
  obtain ⟨b, hbmem, hbfalse⟩ :=
    theorem1FoldlAnd_false_exists
      (List.ofFn
        (fun root : Fin n =>
          (!(C root).leader) ||
            !(theorem1L18HitsB ring (loc root) C word)))
      hmiss
  rw [List.mem_ofFn] at hbmem
  obtain ⟨root, hroot⟩ := hbmem
  have hfalse :
      ((!(C root).leader) ||
          !(theorem1L18HitsB ring (loc root) C word)) =
        false :=
    hroot.trans hbfalse
  have hleader : (C root).leader = true := by
    cases hl : (C root).leader with
    | false => simp [hl] at hfalse
    | true => rfl
  have hhit : theorem1L18HitsB ring (loc root) C word = true := by
    cases hh : theorem1L18HitsB ring (loc root) C word with
    | false => simp [hh] at hfalse
    | true => rfl
  exact ⟨root, hleader, hhit⟩

/-- A left fold of `&&` that is true has every entry true. -/
theorem theorem1FoldlAnd_true
    (xs : List Bool) :
    ∀ acc : Bool,
      xs.foldl (fun a b => a && b) acc = true →
        acc = true ∧ ∀ b ∈ xs, b = true := by
  induction xs with
  | nil =>
      intro acc h
      exact ⟨h, fun b hb => by simp at hb⟩
  | cons x xs ih =>
      intro acc h
      rw [List.foldl_cons] at h
      obtain ⟨hax, hall⟩ := ih (acc && x) h
      rw [Bool.and_eq_true] at hax
      refine ⟨hax.1, ?_⟩
      intro b hb
      rw [List.mem_cons] at hb
      rcases hb with hbx | hbxs
      · rw [hbx]
        exact hax.2
      · exact hall b hbxs

/-- If every leader root misses, a given leader root misses. -/
theorem theorem1AllLeaderRootsMissGen_root
    {n psi : Nat}
    (ring : DirectedRing n)
    (loc : Fin n → Config n psi (theorem1Kappa psi) → Bool)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (root : Fin n)
    (hleader : (C root).leader = true)
    (hmiss : theorem1AllLeaderRootsMissGen ring loc C word = true) :
    theorem1L18HitsB ring (loc root) C word = false := by
  unfold theorem1AllLeaderRootsMissGen at hmiss
  have hall := (theorem1FoldlAnd_true _ true hmiss).2
  have hroot :=
    hall
      ((!(C root).leader) || !(theorem1L18HitsB ring (loc root) C word))
      (List.mem_ofFn.mpr ⟨root, rfl⟩)
  rw [hleader] at hroot
  cases hh : theorem1L18HitsB ring (loc root) C word with
  | false => rfl
  | true =>
      rw [hh] at hroot
      simp at hroot

/-! ## The `S_PL` instance -/

/-- `theorem1ReachesSPL` is the prefix-hitting test for `S_PL`. -/
theorem theorem1ReachesSPL_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      theorem1ReachesSPL ring C word =
        theorem1ReachesB ring (fun C => decide (SPL ring C)) C word := by
  intro C word
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [theorem1ReachesSPL, theorem1ReachesB, ih]

/-- `l18HitsSPL` is the `P_PL'` prefix-hitting test for rooted `S_PL`. -/
theorem l18HitsSPL_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      PPL.Convergence.L18.l18HitsSPL ring root C word =
        theorem1L18HitsB ring (fun C => decide (SPLAt ring root C)) C word := by
  intro C word
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [PPL.Convergence.L18.l18HitsSPL, theorem1L18HitsB, ih]

/-- `theorem1AllLeaderRootsMissB` is the miss event for rooted `S_PL`. -/
theorem theorem1AllLeaderRootsMissB_eq
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    theorem1AllLeaderRootsMissB ring C word =
      theorem1AllLeaderRootsMissGen ring
        (fun root C => decide (SPLAt ring root C)) C word := by
  unfold theorem1AllLeaderRootsMissB theorem1AllLeaderRootsMissGen
  simp only [l18HitsSPL_eq]

/-- `theorem1Bad18B` is the L18 bad event for rooted `S_PL`. -/
theorem theorem1Bad18B_eq
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    theorem1Bad18B ring C0 word =
      theorem1Bad18Gen ring (fun root C => decide (SPLAt ring root C))
        C0 word := by
  unfold theorem1Bad18B theorem1Bad18Gen
  cases theorem1MidCut ring C0 word <;>
    cases theorem1MidState ring C0 word <;>
    simp only [theorem1AllLeaderRootsMissB_eq]

end PPL.Theorem1General
