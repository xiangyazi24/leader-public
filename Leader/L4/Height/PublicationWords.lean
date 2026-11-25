import Leader.L4.Height.ClockHead

namespace L4.Height

/-- Erase raw administrative marks, retaining each successful publication
with its actually committed site and bit. An identity publication is retained:
the test is whether act returns some, not whether records change. -/
def publicationWord {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm) :
    α → List (Fin n) → List (Fin (2 * m))
  | _, [] => []
  | x, e :: u =>
      let tail := publicationWord C (C.next x e) u
      match C.act x e with
      | none => tail
      | some (i, b) => PhysicalDelay.siteLetter i b :: tail

/-- One publication gives precisely the next native record configuration.
This equality does not constrain or inspect the current lifted levels. -/
private theorem publication_step_cfg {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (x : α) (e : Fin n) (s : WordState m)
    (hc : s.cfg = C.cfg x)
    (i : Fin m) (b : Bool)
    (he : C.act x e = some (i, b)) :
    (physicalNext B M hm s (PhysicalDelay.siteLetter i b)).cfg =
      C.cfg (C.next x e) := by
  have hcfg :
      C.cfg (C.next x e) =
        Recover.StageThree.activate B M hm (C.cfg x) i b := by
    simpa only [he] using C.cfg_next x e
  change
    (activate B M hm s
      (physicalSite (PhysicalDelay.siteLetter i b))
      (physicalBit (PhysicalDelay.siteLetter i b))).cfg =
      C.cfg (C.next x e)
  rw [PhysicalDelay.siteLetter_site, PhysicalDelay.siteLetter_bit,
    clock_activate_cfg, hc]
  exact hcfg.symm

/-- Erasing administrative marks preserves the native configuration on
every finite raw word, starting from any lift over the specified cfg. -/
theorem publication_word_projects {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (x : α) (s : WordState m) (hc : s.cfg = C.cfg x)
    (u : List (Fin n)) :
    (physicalRun B M hm s (publicationWord C x u)).cfg =
      C.cfg (runWord C.next x u) := by
  induction u generalizing x s with
  | nil =>
      change s.cfg = C.cfg x
      exact hc
  | cons e u ih =>
      cases hact : C.act x e with
      | none =>
          have hc' : s.cfg = C.cfg (C.next x e) := by
            rw [hc]
            have h := C.cfg_next x e
            simpa only [hact] using h.symm
          have ht := ih (C.next x e) s hc'
          simpa only [publicationWord, hact, runWord,
            List.foldl_cons] using ht
      | some p =>
          rcases p with ⟨i, b⟩
          let s' : WordState m :=
            physicalNext B M hm s (PhysicalDelay.siteLetter i b)
          have hc' : s'.cfg = C.cfg (C.next x e) :=
            publication_step_cfg C x e s hc i b hact
          have ht := ih (C.next x e) s' hc'
          simpa only [publicationWord, hact, physicalRun, runWord,
            List.foldl_cons, s'] using ht

/-- One raw step is a stutter or an activation of the entire coherent
WordState, provided the chart's lift follows its actual INC action. -/
private theorem publication_step_state {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (lift : α → Fin m → Nat)
    (hLift : ∀ x e, lift (C.next x e) =
      match C.act x e with
      | none => lift x
      | some (i, b) =>
          (activate B M hm ⟨C.cfg x, lift x⟩ i b).lift)
    (x : α) (e : Fin n) :
    (match C.act x e with
      | none => (⟨C.cfg x, lift x⟩ : WordState m)
      | some (i, b) =>
          physicalNext B M hm ⟨C.cfg x, lift x⟩
            (PhysicalDelay.siteLetter i b)) =
      (⟨C.cfg (C.next x e), lift (C.next x e)⟩ :
        WordState m) := by
  cases hact : C.act x e with
  | none =>
      have hcfg : C.cfg (C.next x e) = C.cfg x := by
        simpa only [hact] using C.cfg_next x e
      have hlift : lift (C.next x e) = lift x := by
        simpa only [hact] using hLift x e
      simp only [hact]
      exact wordState_ext hcfg.symm hlift.symm
  | some p =>
      rcases p with ⟨i, b⟩
      have hcfg :
          C.cfg (C.next x e) =
            Recover.StageThree.activate B M hm (C.cfg x) i b := by
        simpa only [hact] using C.cfg_next x e
      have hlift :
          lift (C.next x e) =
            (activate B M hm ⟨C.cfg x, lift x⟩ i b).lift := by
        simpa only [hact] using hLift x e
      simp only [hact]
      change
        (activate B M hm ⟨C.cfg x, lift x⟩
          (physicalSite (PhysicalDelay.siteLetter i b))
          (physicalBit (PhysicalDelay.siteLetter i b))) =
        (⟨C.cfg (C.next x e), lift (C.next x e)⟩ :
          WordState m)
      rw [PhysicalDelay.siteLetter_site, PhysicalDelay.siteLetter_bit]
      apply wordState_ext
      · rw [clock_activate_cfg]
        exact hcfg.symm
      · exact hlift.symm

/-- A coherent chart follows the publication list as an entire lifted
native execution. This stronger statement supplies the lift theorem. -/
private theorem publication_word_state {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (lift : α → Fin m → Nat)
    (hLift : ∀ x e, lift (C.next x e) =
      match C.act x e with
      | none => lift x
      | some (i, b) =>
          (activate B M hm ⟨C.cfg x, lift x⟩ i b).lift) :
    ∀ (x : α) (u : List (Fin n)),
      physicalRun B M hm ⟨C.cfg x, lift x⟩
        (publicationWord C x u) =
      (⟨C.cfg (runWord C.next x u),
        lift (runWord C.next x u)⟩ : WordState m) := by
  intro x u
  induction u generalizing x with
  | nil =>
      rfl
  | cons e u ih =>
      have hs := publication_step_state C lift hLift x e
      cases hact : C.act x e with
      | none =>
          have hstep :
              (⟨C.cfg x, lift x⟩ : WordState m) =
                ⟨C.cfg (C.next x e), lift (C.next x e)⟩ := by
            simpa only [hact] using hs
          change
            physicalRun B M hm ⟨C.cfg x, lift x⟩
              (publicationWord C x (e :: u)) =
            (⟨C.cfg (runWord C.next (C.next x e) u),
              lift (runWord C.next (C.next x e) u)⟩ :
              WordState m)
          calc
            physicalRun B M hm ⟨C.cfg x, lift x⟩
                (publicationWord C x (e :: u)) =
              physicalRun B M hm ⟨C.cfg x, lift x⟩
                (publicationWord C (C.next x e) u) := by
                  simp only [publicationWord, hact]
            _ = physicalRun B M hm
                  ⟨C.cfg (C.next x e), lift (C.next x e)⟩
                  (publicationWord C (C.next x e) u) := by
                    exact congrArg
                      (fun s : WordState m =>
                        physicalRun B M hm s
                          (publicationWord C (C.next x e) u))
                      hstep
            _ = ⟨C.cfg (runWord C.next (C.next x e) u),
                  lift (runWord C.next (C.next x e) u)⟩ :=
                    ih (C.next x e)
      | some p =>
          rcases p with ⟨i, b⟩
          have hstep :
              physicalNext B M hm ⟨C.cfg x, lift x⟩
                (PhysicalDelay.siteLetter i b) =
              (⟨C.cfg (C.next x e), lift (C.next x e)⟩ :
                WordState m) := by
            simpa only [hact] using hs
          change
            physicalRun B M hm ⟨C.cfg x, lift x⟩
              (publicationWord C x (e :: u)) =
            (⟨C.cfg (runWord C.next (C.next x e) u),
              lift (runWord C.next (C.next x e) u)⟩ :
              WordState m)
          calc
            physicalRun B M hm ⟨C.cfg x, lift x⟩
                (publicationWord C x (e :: u)) =
              physicalRun B M hm
                (physicalNext B M hm ⟨C.cfg x, lift x⟩
                  (PhysicalDelay.siteLetter i b))
                (publicationWord C (C.next x e) u) := by
                  simp only [publicationWord, hact, physicalRun]
            _ = physicalRun B M hm
                  ⟨C.cfg (C.next x e), lift (C.next x e)⟩
                  (publicationWord C (C.next x e) u) := by
                    exact congrArg
                      (fun s : WordState m =>
                        physicalRun B M hm s
                          (publicationWord C (C.next x e) u))
                      hstep
            _ = ⟨C.cfg (runWord C.next (C.next x e) u),
                  lift (runWord C.next (C.next x e) u)⟩ :=
                    ih (C.next x e)

/-- The chart's coherent increment counts are exactly those of its
publication word, without treating the shortened list as IID. -/
theorem publication_word_lifts {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (lift : α → Fin m → Nat)
    (hLift : ∀ x e, lift (C.next x e) =
      match C.act x e with
      | none => lift x
      | some (i, b) =>
          (activate B M hm ⟨C.cfg x, lift x⟩ i b).lift)
    (x : α) (u : List (Fin n)) :
    (physicalRun B M hm ⟨C.cfg x, lift x⟩
      (publicationWord C x u)).lift =
        lift (runWord C.next x u) := by
  exact congrArg WordState.lift
    (publication_word_state C lift hLift x u)

/-- Publication erasure commutes with concatenation at the actual
intermediate raw state. -/
theorem publication_word_append {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (x : α) (u v : List (Fin n)) :
    publicationWord C x (u ++ v) =
      publicationWord C x u ++
        publicationWord C (runWord C.next x u) v := by
  induction u generalizing x with
  | nil =>
      simp [publicationWord, runWord]
  | cons e u ih =>
      cases hact : C.act x e with
      | none =>
          simpa [publicationWord, hact, runWord, List.cons_append]
            using (ih (C.next x e))
      | some p =>
          rcases p with ⟨i, b⟩
          simpa [publicationWord, hact, runWord, List.cons_append]
            using
              (congrArg
                (fun w : List (Fin (2 * m)) =>
                  PhysicalDelay.siteLetter i b :: w)
                (ih (C.next x e)))

/-- Each raw mark emits at most one publication letter, even when it
commits an identity update of the selected clock record. -/
theorem publication_word_length_le {α : Type} {n m B M : Nat}
    {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (x : α) (u : List (Fin n)) :
    (publicationWord C x u).length ≤ u.length := by
  induction u generalizing x with
  | nil =>
      exact Nat.le_refl _
  | cons e u ih =>
      cases hact : C.act x e with
      | none =>
          calc
            (publicationWord C x (e :: u)).length =
                (publicationWord C (C.next x e) u).length := by
                  simp only [publicationWord, hact]
            _ ≤ u.length := ih (C.next x e)
            _ ≤ (e :: u).length := by simp
      | some p =>
          rcases p with ⟨i, b⟩
          calc
            (publicationWord C x (e :: u)).length =
                Nat.succ (publicationWord C (C.next x e) u).length := by
                  simp only [publicationWord, hact, List.length_cons]
            _ ≤ Nat.succ u.length :=
              Nat.succ_le_succ (ih (C.next x e))
            _ = (e :: u).length := rfl

end L4.Height

