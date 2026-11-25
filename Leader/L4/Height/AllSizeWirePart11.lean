import Leader.L4.Height.AllSizeWirePart10
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section Display

open Classical
open L4.Compiler.Native

variable {S : Type} {n : Nat}

/-- Identifies the physical original-epoch ledger underlying one trial. -/
abbrev DisplayOrigin (D : AllSizeData S n) :=
  ∀ j : D.Chart, D.State j → Nat → Nat → (List (Fin n) → Fin (D.m j) → Nat) → Prop

/-- One stopped raw display trial. Its floor, opening and lifted counts all
come from the same original-epoch witness. -/
structure RawDisplayTrial (D : AllSizeData S n) (hn : 0 < n) (bL : Nat)
    (origin : DisplayOrigin D) (j : D.Chart) (z : D.State j) where
  lo : Nat
  opening : Nat
  level : List (Fin n) → Fin (D.m j) → Nat
  historical : origin j z lo opening level
  floor : ∀ i, lo ≤ level [] i
  depth : opening + 32 * (2 ^ 19 * D.m j) + 1 ≤
    lo + (D.m j + 233 + 32 * (2 ^ 19 * D.m j))
  split :
    4 * failureCount
        (fun w => ¬ D.display hn (runWord (D.next hn) (D.raw j z) w))
        (D.deadline bL j) ≤
      n ^ (D.deadline bL j) + 4 *
        failureCount (fun w => ∃ i, level w i ≤ opening + 32 * (2 ^ 19 * D.m j))
          (D.deadline bL j)

/-- Every legitimate stop has a raw trial on its actual historical tape. -/
def RawDisplay (D : AllSizeData S n) (hn : 0 < n) (bL : Nat)
    (origin : DisplayOrigin D) : Prop :=
  ∀ j z, Recover.Chain.LgSet (D.clock j) z → Nonempty (RawDisplayTrial D hn bL origin j z)

/-- The physical ledger uses the same enumeration, residues and genuine
increment action as the clock chart. -/
def DisplayTraceCompatibility (D : AllSizeData S n) (origin : DisplayOrigin D) : Prop :=
  ∀ j z lo opening level, Recover.Chain.LgSet (D.clock j) z → origin j z lo opening level →
    LegitCoset (modulus D.r) (D.hm j) ⟨(D.clock j).cfg z, level []⟩ ∧
    ∀ w e,
      let C := D.clock j
      let y := runWord C.next z w
      level (w ++ [e]) =
        match C.act y e with
        | none => level w
        | some (i, b) =>
            (activate (heightMod D.r) (modulus D.r) (D.hm j)
              ⟨C.cfg y, level w⟩ i b).lift

noncomputable def selectedDisplayTrial (D : AllSizeData S n) (hn : 0 < n)
    (bL : Nat) (origin : DisplayOrigin D) (hDisplay : RawDisplay D hn bL origin)
    (j : D.Chart) (z : D.State j) (hz : Recover.Chain.LgSet (D.clock j) z) :
    RawDisplayTrial D hn bL origin j z :=
  Classical.choice (hDisplay j z hz)

/-- Install the opening and levels from a single trial chosen at each
legitimate start. At each failed restart the new state has its own trial. -/
noncomputable def withDisplayTrials (D : AllSizeData S n) (hn : 0 < n) (bL : Nat)
    (origin : DisplayOrigin D) (hDisplay : RawDisplay D hn bL origin) : AllSizeData S n :=
  { D with
    opening := fun j z =>
      if hz : Recover.Chain.LgSet (D.clock j) z then
        (selectedDisplayTrial D hn bL origin hDisplay j z hz).opening
      else 0
    level := fun j z =>
      if hz : Recover.Chain.LgSet (D.clock j) z then
        (selectedDisplayTrial D hn bL origin hDisplay j z hz).level
      else fun _ _ => 0 }

theorem selected_display_values (D : AllSizeData S n) (hn : 0 < n) (bL : Nat)
    (origin : DisplayOrigin D) (hDisplay : RawDisplay D hn bL origin)
    (j : D.Chart) (z : D.State j) (hz : Recover.Chain.LgSet (D.clock j) z) :
    (withDisplayTrials D hn bL origin hDisplay).opening j z =
      (selectedDisplayTrial D hn bL origin hDisplay j z hz).opening ∧
    (withDisplayTrials D hn bL origin hDisplay).level j z =
      (selectedDisplayTrial D hn bL origin hDisplay j z hz).level := by
  exact ⟨dif_pos hz, dif_pos hz⟩

theorem selected_display_miss (D : AllSizeData S n) (hn : 0 < n) (bL : Nat)
    (origin : DisplayOrigin D) (hDisplay : RawDisplay D hn bL origin)
    (j : D.Chart) (z : D.State j) (hz : Recover.Chain.LgSet (D.clock j) z) :
    (withDisplayTrials D hn bL origin hDisplay).miss j z =
      fun w => ∃ i, (selectedDisplayTrial D hn bL origin hDisplay j z hz).level w i ≤
        (selectedDisplayTrial D hn bL origin hDisplay j z hz).opening +
          32 * (2 ^ 19 * D.m j) := by
  funext w
  simp [AllSizeData.miss, withDisplayTrials, hz]

/-- A unique true readout on all raw suffixes is the spine's fixed-winner
predicate, including the empty suffix. -/
theorem permanent_iff_unique_reference {α : Type}
    (next : α → Fin n → α) (read : α → Fin n → Bool) (x : α) :
    Permanent next read x ↔
      ∃ v : Fin n, ∀ (w : List (Fin n)) j, read (runWord next x w) j = true ↔ j = v := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, fun w j => ?_⟩
    rw [hv w j]
    simp
  · rintro ⟨v, hv⟩
    refine ⟨v, fun w j => ?_⟩
    by_cases hj : j = v
    · subst j
      simpa using (hv w v).2 rfl
    · cases hr : read (runWord next x w) j
      · simp [hj]
      · exact (hj ((hv w j).1 hr)).elim

theorem display_project_run {α β : Type}
    (f : α → β) (a : α → Fin n → α) (b : β → Fin n → β)
    (hf : ∀ y e, f (a y e) = b (f y) e) (x : α) (w : List (Fin n)) :
    f (runWord a x w) = runWord b (f x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      exact (ih (a x e)).trans (congrArg (fun y => runWord b y w) (hf x e))

/-- Transport the raw display count across the same-letter chart projection. -/
theorem displaySplit_of_rawDisplay (D : AllSizeData S n) (hn : 0 < n) {bL : Nat}
    (hRaw : ∀ j z e, D.raw j ((D.clock j).next z e) = D.next hn (D.raw j z) e)
    (origin : DisplayOrigin D) (hDisplay : RawDisplay D hn bL origin) :
    let E := withDisplayTrials D hn bL origin hDisplay
    ∀ j z, Recover.Chain.LgSet (E.clock j) z → ¬ E.display hn (E.raw j z) →
      4 * failureCount
          (fun w => ¬ E.display hn (E.raw j (runWord (E.clock j).next z w)))
          (E.deadline bL j) ≤
        n ^ (E.deadline bL j) + 4 * failureCount (E.miss j z) (E.deadline bL j) := by
  let E := withDisplayTrials D hn bL origin hDisplay
  change ∀ (j : D.Chart) (z : D.State j),
    Recover.Chain.LgSet (D.clock j) z → ¬ D.display hn (D.raw j z) →
    4 * failureCount (fun w => ¬ D.display hn (D.raw j (runWord (D.clock j).next z w)))
      (D.deadline bL j) ≤ n ^ (D.deadline bL j) + 4 * failureCount (E.miss j z) (D.deadline bL j)
  intro j z hz _
  rw [selected_display_miss D hn bL origin hDisplay j z hz]
  let trial := selectedDisplayTrial D hn bL origin hDisplay j z hz
  have hfun : (fun w => ¬ D.display hn (D.raw j (runWord (D.clock j).next z w))) =
      (fun w => ¬ D.display hn (runWord (D.next hn) (D.raw j z) w)) := by
    funext w
    rw [display_project_run (D.raw j) (D.clock j).next (D.next hn) (hRaw j)]
  rw [hfun]
  exact trial.split

theorem display_run_append_mark {α : Type}
    (next : α → Fin n → α) (x : α) (w : List (Fin n)) (e : Fin n) :
    runWord next x (w ++ [e]) = next (runWord next x w) e := by
  simp [runWord, List.foldl_append]

/-- Record each raw continuation without changing any clock or service fields. -/
def displayHistoryClock {α : Type} {m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm) (x : α) :
    Recover.Chain.ClockChain (List (Fin n)) n m B M hm where
  next := fun w e => w ++ [e]
  cfg := fun w => C.cfg (runWord C.next x w)
  act := fun w e => C.act (runWord C.next x w) e
  lastAct := fun w => C.lastAct (runWord C.next x w)
  cfg_next := by
    intro w e
    simp only [display_run_append_mark]
    exact C.cfg_next _ _
  last_next := by
    intro w e
    simp only [display_run_append_mark]
    exact C.last_next _ _

theorem display_history_run (w u : List (Fin n)) :
    Thru.runWord (fun v e => v ++ [e]) w u = w ++ u := by
  induction u generalizing w with
  | nil => simp [Thru.runWord]
  | cons e u ih =>
      change Thru.runWord (fun v e => v ++ [e]) (w ++ [e]) u = w ++ e :: u
      rw [ih]
      simp [List.append_assoc]

/-- Erasing nonpublications gives a pathwise identity for the chosen trace. -/
theorem display_trace_publications {α : Type} {m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm) (x : α)
    (lift : List (Fin n) → Fin m → Nat)
    (hLift : ∀ w e, lift (w ++ [e]) =
      match C.act (runWord C.next x w) e with
      | none => lift w
      | some (i, b) =>
          (activate B M hm ⟨C.cfg (runWord C.next x w), lift w⟩ i b).lift)
    (u : List (Fin n)) :
    (physicalRun B M hm ⟨C.cfg x, lift []⟩
      (publicationWord (displayHistoryClock C x) [] u)).lift = lift u := by
  let H := displayHistoryClock C x
  have hStep : ∀ w e, lift (H.next w e) =
      match H.act w e with
      | none => lift w
      | some (i, b) => (activate B M hm ⟨H.cfg w, lift w⟩ i b).lift := hLift
  have hRun (w v : List (Fin n)) : runWord H.next w v = w ++ v := by
    induction v generalizing w with
    | nil => simp [runWord]
    | cons e v ih =>
        change runWord H.next (w ++ [e]) v = w ++ e :: v
        rw [ih]
        simp [List.append_assoc]
  have hh := publication_word_lifts H lift hStep [] u
  rw [hRun, List.nil_append] at hh
  exact hh

theorem display_history_wait {α : Type}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (w u : List (Fin n)) :
    Thru.wait (fun v e => v ++ [e]) (fun v => A (runWord next x v)) w u =
      Thru.wait next A (runWord next x w) u := by
  induction u generalizing w with
  | nil => rfl
  | cons e u ih =>
      simp only [Thru.wait, ih, display_run_append_mark]

theorem display_modulus_params {r : Nat}
    (hM : Recover.StageTwo.ClockParams (modulus r)) : ClockParams (modulus r) := by
  cases r with
  | zero =>
      have h := hM.1
      simp [modulus] at h
  | succ r =>
      refine ⟨?_, hM.2⟩
      have hp : 0 < (16 : Nat) ^ r := Nat.pow_pos (by decide)
      simp only [modulus, Nat.pow_succ]
      omega

theorem display_activate_mono {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (i : Fin m) (b : Bool) (j : Fin m) :
    s.lift j ≤ (activate B M hm s i b).lift j := by
  by_cases he : j = i
  · subst j
    cases h : clockAction M hm s i <;> simp [activate, h, advanceLift]
  · simp [activate, he]

theorem display_activate_progress {m B M : Nat} (hm : 0 < m)
    (hM : ClockParams M) (s : WordState m) (hs : LegitCoset M hm s)
    (i : Fin m) (b : Bool) (k : Nat)
    (hl : k ≤ s.lift (left hm i)) (hc : k ≤ s.lift i)
    (hr : k ≤ s.lift (right hm i)) :
    k + 1 ≤ (activate B M hm s i b).lift i := by
  by_cases hi : k + 1 ≤ s.lift i
  · exact Nat.le_trans hi (display_activate_mono hm s i b i)
  · have hNearL := hs.near (i := i) (j := left hm i) (Or.inl rfl)
    have hNearR := hs.near (i := i) (j := right hm i) (Or.inr rfl)
    unfold Near at hNearL hNearR
    have hFront : CanAdvance hm s.lift i := ⟨by omega, by omega⟩
    have hInc :=
      (action_inc_iff hM hm (canon M s) (canon_legit hs) i).2 hFront
    rw [coset_activate_lift hM hm s hs i b]
    change k + 1 ≤ setAt (canon M s).lift i
      (advanceLift (clockAction M hm (canon M s) i) ((canon M s).lift i)) i
    rw [setAt_self, hInc]
    exact Nat.succ_le_succ hc

/-- The stopped trace and strict publication service bound the missed-cap
mass at the same deadline used in the physical display split. -/
theorem missQuarter_of_rawDisplay (D : AllSizeData S n) (hn : 0 < n) {bL : Nat}
    (hParameters : ∀ j : D.Chart, Recover.StageTwo.ClockParams (modulus D.r) ∧
      D.m j / 2 < modulus D.r / 2 ∧ 0 < D.block j ∧
      4 * (2 ^ (5 * bL + 1) * D.block j) ≤ D.scale bL ∧ D.m j * D.r ≤ n)
    (hService : ∀ j i z, n ^ (D.block j) ≤ 2 ^ (5 * bL + 1) *
      RawService.publicationMass (D.clock j).next ((D.clock j).served i) z (D.block j))
    (origin : DisplayOrigin D) (hDisplay : RawDisplay D hn bL origin)
    (hCompat : DisplayTraceCompatibility D origin) :
    let E := withDisplayTrials D hn bL origin hDisplay
    ∀ j z, Recover.Chain.LgSet (E.clock j) z → ¬ E.display hn (E.raw j z) →
      4 * failureCount (E.miss j z) (E.deadline bL j) ≤ n ^ (E.deadline bL j) := by
  let E := withDisplayTrials D hn bL origin hDisplay
  change ∀ (j : D.Chart) (z : D.State j),
    Recover.Chain.LgSet (D.clock j) z → ¬ D.display hn (D.raw j z) →
    4 * failureCount (E.miss j z) (D.deadline bL j) ≤ n ^ (D.deadline bL j)
  intro j z hz _
  rw [selected_display_miss D hn bL origin hDisplay j z hz]
  let trial := selectedDisplayTrial D hn bL origin hDisplay j z hz
  obtain ⟨hStart, hTrace⟩ := hCompat j z trial.lo trial.opening trial.level hz trial.historical
  obtain ⟨hM, _, hBlock, hScale, _⟩ := hParameters j
  let C := D.clock j
  let H := displayHistoryClock C z
  let lift := trial.level
  have hTrace' : ∀ w e, lift (H.next w e) =
      match H.act w e with
      | none => lift w
      | some (i, b) =>
          (activate (heightMod D.r) (modulus D.r) (D.hm j) ⟨H.cfg w, lift w⟩ i b).lift := by
    intro w e
    simpa only [H, displayHistoryClock, C, lift] using hTrace w e
  have hClock := display_modulus_params hM
  have hcosBase : LegitCoset (modulus D.r) (D.hm j) ⟨H.cfg [], lift []⟩ := hStart
  have hcosStep (w : List (Fin n)) (e : Fin n)
      (hw : LegitCoset (modulus D.r) (D.hm j) ⟨H.cfg w, lift w⟩) :
      LegitCoset (modulus D.r) (D.hm j) ⟨H.cfg (H.next w e), lift (H.next w e)⟩ := by
    cases ha : H.act w e with
    | none =>
        have hcfg := H.cfg_next w e
        rw [ha] at hcfg
        have hlevel := hTrace' w e
        rw [ha] at hlevel
        rw [hcfg, hlevel]
        exact hw
    | some p =>
        obtain ⟨i, b⟩ := p
        let before : WordState (D.m j) := ⟨H.cfg w, lift w⟩
        let after := activate (heightMod D.r) (modulus D.r) (D.hm j) before i b
        have hcfg : H.cfg (H.next w e) = after.cfg := by
          rw [show after.cfg = _ from clock_activate_cfg (D.hm j) before i b]
          simpa only [ha] using H.cfg_next w e
        have hlevel : lift (H.next w e) = after.lift := by
          simpa only [ha] using hTrace' w e
        have hstate : (⟨H.cfg (H.next w e), lift (H.next w e)⟩ : WordState (D.m j)) = after :=
          wordState_ext hcfg hlevel
        rw [hstate]
        exact coset_activate (B := heightMod D.r) hClock hw i b
  have hcos (w : List (Fin n)) :
      LegitCoset (modulus D.r) (D.hm j) ⟨H.cfg w, lift w⟩ := by
    have go (a v : List (Fin n))
        (ha : LegitCoset (modulus D.r) (D.hm j) ⟨H.cfg a, lift a⟩) :
        LegitCoset (modulus D.r) (D.hm j) ⟨H.cfg (a ++ v), lift (a ++ v)⟩ := by
      induction v generalizing a with
      | nil => simpa only [List.append_nil] using ha
      | cons e v ih =>
          have hstep := ih (a ++ [e]) (hcosStep a e ha)
          simpa only [List.append_assoc, List.singleton_append] using hstep
    simpa only [List.nil_append] using go [] w hcosBase
  have hMono (w : List (Fin n)) (e : Fin n) (i : Fin (D.m j)) :
      lift w i ≤ lift (H.next w e) i := by
    rw [hTrace']
    cases H.act w e with
    | none => exact Nat.le_refl _
    | some p =>
        obtain ⟨k, b⟩ := p
        exact display_activate_mono (B := heightMod D.r) (M := modulus D.r)
          (D.hm j) ⟨H.cfg w, lift w⟩ k b i
  have hProgress (w : List (Fin n)) (e : Fin n) (i : Fin (D.m j)) (k : Nat)
      (hs : H.served i (H.next w e))
      (hl : k ≤ lift w (left (D.hm j) i)) (hc : k ≤ lift w i)
      (hr : k ≤ lift w (right (D.hm j) i)) : k + 1 ≤ lift (H.next w e) i := by
    change H.lastAct (H.next w e) = some i at hs
    rw [H.last_next] at hs
    cases ha : H.act w e with
    | none => simp [ha] at hs
    | some p =>
        obtain ⟨k', b⟩ := p
        have he : k' = i := by simpa [ha] using hs
        subst k'
        rw [hTrace', ha]
        exact display_activate_progress (D.hm j) hClock _ (hcos w) i b k hl hc hr
  have hL : 1 ≤ D.scale bL := by
    have hd : 0 < 2 ^ (5 * bL + 1) := Nat.two_pow_pos _
    have hPos := Nat.mul_pos hd hBlock
    omega
  have hMoment (i : Fin (D.m j)) (w : List (Fin n)) :
      Thru.MomentAt H.next (H.served i) (D.scale bL) w := by
    have hm :=
      RawService.publication_moment_of_block C.next (C.served i)
        (D.block j) (2 ^ (5 * bL + 1)) (D.scale bL) (by omega) (Nat.two_pow_pos _)
        hScale (hService j i) (runWord C.next z w)
    intro t
    have harg (u : List (Fin n)) :
        Thru.wait H.next (H.served i) w u =
          Thru.wait C.next (C.served i) (runWord C.next z w) u :=
      display_history_wait C.next (C.served i) z w u
    simpa only [harg] using hm t
  let cap := trial.opening + 32 * (2 ^ 19 * D.m j)
  let depth := max 1 (cap + 1 - trial.lo)
  have hDepth := trial.depth
  have hDepth' : depth ≤ D.m j + 233 + 32 * (2 ^ 19 * D.m j) := by
    dsimp [depth, cap]
    omega
  have hpos : 0 < depth := by dsimp [depth]; omega
  have hCap : cap + 1 ≤ trial.lo + depth := by dsimp [depth]; omega
  let T := rawLevelTime H.next lift [] trial.lo
  let miss := fun w => ∃ i, lift w i ≤ cap
  have hRec := raw_level_recurrence (D.hm j) H.next lift H.served [] trial.lo
    trial.floor hMono hProgress
  have hZero (u : List (Fin n)) (i : Fin (D.m j)) : T u i 0 ≤ 0 := by
    simp [T, rawLevelTime]
  have hMiss (u : List (Fin n)) (_ : u.length = 2 ^ 29 * D.scale bL * D.m j)
      (hf : miss u) : ∃ i, u.length ≤ T u i depth := by
    obtain ⟨i, hi⟩ := hf
    refine ⟨i, Nat.le_of_eq ?_⟩
    symm
    apply raw_level_miss H.next lift [] trial.lo u i depth hMono hpos
    change lift (Thru.runWord (fun v e => v ++ [e]) [] u) i < trial.lo + depth
    rw [display_history_run, List.nil_append]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hi) hCap
  exact display_deadline_quarter (D.hm j) H.next [] H.served (D.scale bL) depth T
    miss hL hMoment hRec hZero hDepth' hMiss

end Display

end L4.Height.AllSizeWire
