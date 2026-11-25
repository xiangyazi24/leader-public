import Leader.L4.EntranceQuiet

/-! Projection of actual all-original-tag observers to the fresh-bullet mask. -/

namespace L4

open TaggedTrace

/-- The omitted sites are precisely those with no surviving original tag. -/
def originalTagAt {p c1 n : Nat} (s : AllObs p c1 n) (b : Fin n) : Prop :=
  ∃ origin : Fin n, (s origin).carrier = some b

/-- One exact physical mark applied to the inherited-tag mask. -/
def nextTagMask {p c1 n : Nat} (x : Config p c1 n)
    (tagged : Fin n → Prop) (e b : Fin n) : Prop :=
  ∃ a, tagged a ∧ carrierStep x e (some a) = some b

/-- Every present live bullet with no original observer is peaceful. -/
def freshAt {p c1 n : Nat} (x : Config p c1 n) (tagged : Fin n → Prop) : Prop :=
  ∀ b, (x b).bullet = .live → ¬ tagged b → RootPeacefulAt x b

/-- The literal one-mark fresh invariant needed by the entrance composition.
Only a mask of physically live original tags is permitted. -/
def FreshMaskStep : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (tagged : Fin n → Prop) (e : Fin n),
    2 ≤ p → 12 ≤ c1 → 4 ≤ n → (¬ p ∣ n) → MCOV x → COV x →
    (∀ b, tagged b → (x b).bullet = .live) →
    freshAt x tagged → freshAt (step x e) (nextTagMask x tagged e)

private theorem advance_carrier_eq {p c1 n : Nat} (s : Obs p c1 n) (e : Fin n) :
    (advance s e).carrier = carrierStep s.config e s.carrier := by
  cases h : s.carrier <;> simp [advance, h, carrierStep]

/-- All observers apply the same physical transition; a mask site survives
exactly when a previous original observer reaches it on that mark. -/
theorem originalTagAt_step_iff {p c1 n : Nat} {x : Config p c1 n} {s : AllObs p c1 n}
    (hs : ∀ i, (s i).config = x) (e b : Fin n) :
    originalTagAt (allAdvance s e) b ↔ nextTagMask x (originalTagAt s) e b := by
  constructor
  · rintro ⟨i,hi⟩
    change (advance (s i) e).carrier = some b at hi
    rw [advance_carrier_eq, hs i] at hi
    cases h : (s i).carrier with
    | none => simp [h, carrierStep] at hi
    | some a => exact ⟨a, ⟨i,h⟩, h ▸ hi⟩
  · rintro ⟨a,⟨i,hi⟩,ha⟩
    refine ⟨i, ?_⟩
    change (advance (s i) e).carrier = some b
    rwa [advance_carrier_eq, hs i, hi]

/-- Immediately after tagging every existing live bullet, its origin is
present at its actual site, and no nonlive site is marked. -/
theorem originalTagAt_init_iff {p c1 n : Nat} (x : Config p c1 n) (b : Fin n) :
    originalTagAt (allInit x) b ↔ (x b).bullet = .live := by
  have beqLive (v : Bullet) : (v == .live) = true ↔ v = .live := by
    cases v <;> decide
  constructor
  · rintro ⟨i,hi⟩
    have h : (x i).bullet = .live ∧ i = b := by
      simpa [allInit, init, beqLive] using hi
    exact h.2 ▸ h.1
  · intro h
    exact ⟨b, by simp [allInit, init, beqLive, h]⟩

private theorem successor_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) :
    rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val+1)%n = e.val at he
  by_cases hh : e.val+1 < n
  · rw [Nat.mod_eq_of_lt hh] at he; omega
  · have ht := e.isLt
    have hs : e.val+1 = n := by omega
    rw [hs, Nat.mod_self] at he
    omega

/-- Neither an old initiator carrier nor any other original carrier can
finish the mark at its initiator. -/
theorem nextTagMask_initiator_false {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (tagged : Fin n → Prop) (e : Fin n) :
    ¬ nextTagMask x tagged e e := by
  rintro ⟨a,_,h⟩
  by_cases he : a = e
  · subst a
    exact successor_ne hn e (carrierStep_selected_survives x e e h).1.symm
  · exact he (carrierStep_not_selected_stays x e a e he h).symm

/-- The responder's original mask is the exact OR of transferred donor
and surviving resident. No Boolean mask is assumed as extra protocol state. -/
theorem nextTagMask_responder_iff {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (tagged : Fin n → Prop) (e : Fin n) :
    nextTagMask x tagged e (rightNeighbor e) ↔
      (tagged e ∧ tagTransfer (x e) (x (rightNeighbor e)) = true) ∨
      (tagged (rightNeighbor e) ∧ tagResident (x e) (x (rightNeighbor e)) = true) := by
  have hn' := successor_ne hn e
  constructor
  · rintro ⟨a,ha,ht⟩
    by_cases he : a = e
    · subst a
      exact Or.inl ⟨ha,(carrierStep_selected_survives x e _ ht).2⟩
    · have hr := (carrierStep_not_selected_stays x e a _ he ht).symm
      subst a
      have hs : tagResident (x e) (x (rightNeighbor e)) = true := by
        by_cases hh : tagResident (x e) (x (rightNeighbor e)) = true
        · exact hh
        · simp [carrierStep, hn', hh] at ht
      exact Or.inr ⟨ha,hs⟩
  · rintro (⟨h,ht⟩ | ⟨h,ht⟩)
    · exact ⟨e,h,by simp [carrierStep, ht]⟩
    · exact ⟨rightNeighbor e,h,by simp [carrierStep, hn', ht]⟩

/-- A mark does not change the original mask at a nonparticipant. -/
theorem nextTagMask_offPair_iff {p c1 n : Nat} (x : Config p c1 n)
    (tagged : Fin n → Prop) (e b : Fin n) (he : b ≠ e) (hr : b ≠ rightNeighbor e) :
    nextTagMask x tagged e b ↔ tagged b := by
  constructor
  · rintro ⟨a,ha,ht⟩
    by_cases hea : a = e
    · subst a
      exact False.elim (hr (carrierStep_selected_survives x e _ ht).1)
    · exact (carrierStep_not_selected_stays x e a b hea ht).symm ▸ ha
  · intro h
    exact ⟨b,h,by simp [carrierStep, he, hr]⟩

/-- A mark cannot leave an original tag on a nonlive physical bullet. -/
theorem nextTagMask_live {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (tagged : Fin n → Prop)
    (hreal : ∀ b, tagged b → (x b).bullet = .live) (e b : Fin n)
    (h : nextTagMask x tagged e b) : (step x e b).bullet = .live := by
  rcases h with ⟨a,ha,hmove⟩
  by_cases he : a = e
  · subst a
    have ⟨hb,ht⟩ := carrierStep_selected_survives x e b hmove
    subst b
    simpa [step, successor_ne hn e] using tagTransfer_live (x e) (x (rightNeighbor e)) ht
  · have hb := carrierStep_not_selected_stays x e a b he hmove
    subst b
    by_cases hr : a = rightNeighbor e
    · subst a
      have ht : tagResident (x e) (x (rightNeighbor e)) = true := by
        by_cases htr : tagResident (x e) (x (rightNeighbor e)) = true
        · exact htr
        · simp [carrierStep, he, htr] at hmove
      simpa [step, he] using ((tagResident_iff (x e) (x (rightNeighbor e))).mp ht).2.2
    · simpa [step, he, hr] using hreal a ha

/-- Tracking an arbitrary finite physical scheduler word aligns all
observer configurations and retains exactly live carriers; if the
one-mark invariant holds, every other live bullet is peaceful. -/
theorem fresh_trace_of_maskStep (hstep : FreshMaskStep)
    {p c1 n : Nat} (x : Config p c1 n) (w : List (Fin n))
    (hp : 2 ≤ p) (hcal : 12 ≤ c1) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hm : MCOV x) (hc : COV x) :
    freshAt (run x w) (originalTagAt (trackAll (allInit x) w)) := by
  have loop (w : List (Fin n)) (x : Config p c1 n) (s : AllObs p c1 n)
      (hs : ∀ i, (s i).config = x) (hm : MCOV x) (hc : COV x)
      (hlive : ∀ b, originalTagAt s b → (x b).bullet = .live)
      (hfresh : freshAt x (originalTagAt s)) :
      freshAt (run x w) (originalTagAt (trackAll s w)) := by
    induction w generalizing x s with
    | nil => exact hfresh
    | cons e w ih =>
      have hmask := originalTagAt_step_iff hs e
      have ⟨hm',hc'⟩ := EntranceCover.cover_closed hn x e ⟨hm,hc⟩
      apply ih (step x e) (allAdvance s e) (fun i => by
        change (advance (s i) e).config = step x e
        rw [projection_step, hs i]) hm' hc'
      · intro b h
        exact nextTagMask_live hn x _ hlive e b ((hmask b).mp h)
      · intro b hbl hbt
        exact hstep x _ e hp hcal hn hnd hm hc hlive hfresh b hbl
          (fun ht => hbt ((hmask b).mpr ht))
  exact loop w x (allInit x) (fun _ => rfl) hm hc
    (fun b => (originalTagAt_init_iff x b).mp)
    (fun b hl hn => False.elim (hn ((originalTagAt_init_iff x b).mpr hl)))

/-- All original observers ended means every surviving physical live bullet
is in the proved fresh class. No stopping-time or probabilistic premise
is used in this implication. -/
theorem freshPeaceAfterExtinction_of_maskStep (hstep : FreshMaskStep) :
    FreshPeaceAfterExtinction := by
  intro p c1 n x w hp hcal hn hnd hm hc hend b hbl
  apply fresh_trace_of_maskStep hstep x w hp hcal hn hnd hm hc b hbl
  rintro ⟨i,hi⟩
  apply hend
  refine ⟨i, ?_⟩
  intro h
  have hh : (trackAll (allInit x) w i).carrier = none := h
  rw [hi] at hh
  contradiction

end L4

