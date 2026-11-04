import Leader.Wu.Elimination.SinkTwoGapRankTransfer

set_option autoImplicit false

open PPLL PPLLRepair FiniteUniformStoppingTree
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant LDSinkKernelC
open LDTwoGapFrame LDSinkTwoGapEpochDefs
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapReachInvariant LDSinkTwoGapRankTransfer

namespace SeekingStretchCharge

noncomputable section

variable {n psi : Nat}

/-!
FIRE equations, untouched-shooter obstruction, and phase obstruction are
separate from the conditional service renewal theorem. The latter still has
one physical-row residual. Scaling obstructions require the stated drift or
plateau premise; no reachable witness is fabricated here.
-/

theorem initiator_fire_fields (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) (hs : l.signal_B = (1 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hpsi l r).1.bullet = (2 : Fin 3) ∧
    (eliminateLeadersNoCollisionFire hpsi l r).1.signal_B = (0 : Fin 2) ∧
    (eliminateLeadersNoCollisionFire hpsi l r).1.shield = true := by
  have hs' : l.signal_B = (⟨1, by omega⟩ : Fin 2) := by
    apply Fin.ext
    exact congrArg Fin.val hs
  have hguard : l.leader = true ∧ l.signal_B = (⟨1, by omega⟩ : Fin 2) :=
    ⟨hl, hs'⟩
  dsimp only [eliminateLeadersNoCollisionFire]
  rw [if_pos hguard]
  exact ⟨rfl, rfl, rfl⟩

theorem responder_fire_fields (hpsi : psi > 0) (l r : AgentState psi)
    (hr : r.leader = true) (hs : r.signal_B = (1 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hpsi l r).2.bullet = (1 : Fin 3) ∧
    (eliminateLeadersNoCollisionFire hpsi l r).2.signal_B = (0 : Fin 2) ∧
    (eliminateLeadersNoCollisionFire hpsi l r).2.shield = false := by
  have hs' : r.signal_B = (⟨1, by omega⟩ : Fin 2) := by
    apply Fin.ext
    exact congrArg Fin.val hs
  have hguard : r.leader = true ∧ r.signal_B = (⟨1, by omega⟩ : Fin 2) :=
    ⟨hr, hs'⟩
  dsimp only [eliminateLeadersNoCollisionFire]
  rw [if_pos hguard]
  exact ⟨rfl, rfl, rfl⟩

theorem zero_signal_disables_initiator_fire
    (hpsi : psi > 0) (l r : AgentState psi)
    (hs : l.signal_B = (0 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hpsi l r).1 = l := by
  have hf : ¬ (l.leader = true ∧ l.signal_B = (⟨1, by omega⟩ : Fin 2)) := by
    intro h
    have hzero : l.signal_B.val = 0 := congrArg Fin.val hs
    have hone : l.signal_B.val = 1 := congrArg Fin.val h.2
    omega
  dsimp only [eliminateLeadersNoCollisionFire]
  exact if_neg hf

/-- The nonincidence premises are explicit geometry obligations. -/
theorem untouched_shooter_stays_unarmed
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AActive hpsi F) (e : Fin n)
    (hl : F.attack.pos F.attack.d ≠ e)
    (hr : F.attack.pos F.attack.d ≠ F.attack.ring.rightNeighbor e) :
    (attemptStepConf hpsi F x.1 e (F.attack.pos F.attack.d)).signal_B =
      (0 : Fin 2) := by
  rw [attemptStepConf_eq_sinkStepC,
    sinkStepC_other hpsi F.attack x.1.conf e
      (F.attack.pos F.attack.d) hl hr]
  exact LDSinkTwoGapAttemptCells.attack_shooter_signal_zero hpsi F x

theorem parked_rearm_without_pos_one_not_tag
    (F : TwoGapFrame n) (x : AState n psi) (C : Fin n → AgentState psi)
    (hp : x.phase = .parked)
    (hb : (C (F.attack.pos 1)).bullet ≠ (2 : Fin 3)) :
    ¬ TagDomain F (advanceAState F x C) := by
  intro ht
  have hp' : (advanceAState F x C).phase = .parked := by
    simp only [advanceAState, advanceAPhase, hp]
  exact hb (ht.parked_iff.mp hp')

/-- C5 applies before the attack gap is done, without a shot certificate. -/
theorem raw_rankLaw_of_not_done
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi)
    (hi : GapPair hpsi F x) (hd : ¬ GapDoneC F.attack x.conf) :
    RawEntranceRankLaw hpsi F x := by
  constructor
  · intro e
    have hw : W F (attemptStepConf hpsi F x e) ≤ W F x.conf := by
      rw [activeGapProjectionNoReset]
      exact LDSinkGapCleanupBound.gapWC_step_le'
        hpsi F.attack x.conf hi.attack hd e
    have hr := R_advance_le F x (attemptStepConf hpsi F x e) hw
    unfold entranceStep
    dsimp only
    split
    · exact Nat.zero_le _
    · unfold attemptStepRaw
      dsimp only
      split
      · exact Nat.zero_le _
      · split
        · exact hr
        · exact hr
  · obtain ⟨e, he⟩ := LDSinkGapCleanupBound.exists_gapWC_step_lt'
      hpsi F.attack x.conf hi.attack hd
    have hw : W F (attemptStepConf hpsi F x e) < W F x.conf := by
      rw [activeGapProjectionNoReset]
      exact he
    have hr := R_advance_lt F x (attemptStepConf hpsi F x e) hw
    have hp := R_pos F x
    refine ⟨e, ?_⟩
    unfold entranceStep
    dsimp only
    split
    · exact hp
    · unfold attemptStepRaw
      dsimp only
      split
      · exact hp
      · split
        · exact hr
        · exact hr

/-! ## Constant-mode credit: exact accounting, not a supersolution claim -/

def seekCredit (c : Nat) : StopNode (TaggedState n psi) → Nat
  | .active z => match z.mode with
    | .tracking => 0
    | .seeking => c
  | .success => 0
  | .failure => 0

def entrancePotential' (F : TwoGapFrame n) (c : Nat)
    (q : StopNode (TaggedState n psi)) : Nat :=
  entrancePotential F (eraseNode q) + seekCredit c q

theorem seeking_active_child
    (hpsi : psi > 0) (F : TwoGapFrame n) (z : TaggedState n psi)
    (e : Fin n) (y : AState n psi) (hm : z.mode = .seeking)
    (he : entranceStep hpsi F z.raw e = .active y) :
    taggedEntranceStep hpsi F z e = .active ⟨y, .seeking⟩ := by
  simp only [taggedEntranceStep, hm, modeAfter, he]
  rfl

theorem augmented_balance
    (hpsi : psi > 0) (F : TwoGapFrame n) (c : Nat) (z : TaggedState n psi) :
    (n + (List.ofFn (fun e : Fin n =>
      entrancePotential' F c (taggedEntranceStep hpsi F z e))).sum ≤
        n * entrancePotential' F c (.active z)) ↔
    (n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hpsi F z.raw e))).sum +
      (List.ofFn (fun e : Fin n =>
        seekCredit c (taggedEntranceStep hpsi F z e))).sum ≤
      n * entrancePotential F (.active z.raw) + n * seekCredit c (.active z)) := by
  have hs : (List.ofFn (fun e : Fin n =>
      entrancePotential' F c (taggedEntranceStep hpsi F z e))).sum =
      (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hpsi F z.raw e))).sum +
      (List.ofFn (fun e : Fin n =>
        seekCredit c (taggedEntranceStep hpsi F z e))).sum := by
    calc
      _ = (List.ofFn (fun e : Fin n =>
          entrancePotential F (entranceStep hpsi F z.raw e) +
          seekCredit c (taggedEntranceStep hpsi F z e))).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e
        unfold entrancePotential'
        rw [erase_taggedEntranceStep]
      _ = _ := FiniteUniformStoppingTree.ofFn_sum_add _ _
  change (n + _ ≤ n *
    (entrancePotential F (.active z.raw) + seekCredit c (.active z))) ↔ _
  rw [hs, Nat.mul_add, ← Nat.add_assoc]

theorem constant_credit_cancels
    (hpsi : psi > 0) (F : TwoGapFrame n) (c : Nat) (z : TaggedState n psi)
    (hc : ∀ e : Fin n,
      seekCredit c (taggedEntranceStep hpsi F z e) = seekCredit c (.active z)) :
    (n + (List.ofFn (fun e : Fin n =>
      entrancePotential' F c (taggedEntranceStep hpsi F z e))).sum ≤
        n * entrancePotential' F c (.active z)) ↔
    (n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hpsi F z.raw e))).sum ≤
        n * entrancePotential F (.active z.raw)) := by
  have hs := (FiniteUniformStoppingTree.ofFn_sum_eq _ _ hc).trans
    (FiniteUniformStoppingTree.ofFn_sum_const n (seekCredit c (.active z)))
  rw [augmented_balance, hs]
  omega

theorem tracking_recharge_obligation
    (hpsi : psi > 0) (F : TwoGapFrame n) (c : Nat) (z : TaggedState n psi)
    (hm : z.mode = .tracking)
    (hb : n + (List.ofFn (fun e : Fin n =>
      entrancePotential' F c (taggedEntranceStep hpsi F z e))).sum ≤
        n * entrancePotential' F c (.active z)) :
    n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hpsi F z.raw e))).sum +
      (List.ofFn (fun e : Fin n =>
        seekCredit c (taggedEntranceStep hpsi F z e))).sum ≤
      n * entrancePotential F (.active z.raw) := by
  have h := (augmented_balance hpsi F c z).mp hb
  have hz : seekCredit c (.active z) = 0 := by
    simp only [seekCredit, hm]
  simpa only [hz, Nat.mul_zero, Nat.add_zero] using h

theorem no_constant_credit_of_plateau
    (hpsi : psi > 0) (F : TwoGapFrame n) (c : Nat) (z : TaggedState n psi)
    (hm : z.mode = .seeking)
    (hp : ∀ e : Fin n,
      rawStoppedR F (entranceStep hpsi F z.raw e) = R F z.raw) :
    ¬ (n + (List.ofFn (fun e : Fin n =>
      entrancePotential' F c (taggedEntranceStep hpsi F z e))).sum ≤
        n * entrancePotential' F c (.active z)) := by
  have hy : ∀ e : Fin n, ∃ y : AState n psi,
      entranceStep hpsi F z.raw e = .active y ∧ R F y = R F z.raw := by
    intro e
    have hh := hp e
    have hpos := R_pos F z.raw
    cases he : entranceStep hpsi F z.raw e with
    | active y =>
        refine ⟨y, rfl, ?_⟩
        simpa only [he, rawStoppedR] using hh
    | success =>
        have hz : 0 = R F z.raw := by
          simpa only [he, rawStoppedR] using hh
        omega
    | failure =>
        have hz : 0 = R F z.raw := by
          simpa only [he, rawStoppedR] using hh
        omega
  have hc : ∀ e : Fin n,
      seekCredit c (taggedEntranceStep hpsi F z e) = seekCredit c (.active z) := by
    intro e
    obtain ⟨y, he, _⟩ := hy e
    rw [seeking_active_child hpsi F z e y hm he]
    simp only [seekCredit, hm]
  have hs : (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hpsi F z.raw e))).sum =
      n * entrancePotential F (.active z.raw) := by
    calc
      _ = (List.ofFn (fun _ : Fin n =>
          entrancePotential F (.active z.raw))).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e
        obtain ⟨y, he, hr⟩ := hy e
        rw [he]
        exact congrArg (fun r : Nat => n * r) hr
      _ = _ := FiniteUniformStoppingTree.ofFn_sum_const n _
  intro hb
  have h := (constant_credit_cancels hpsi F c z hc).mp hb
  rw [hs] at h
  have hn : 0 < n := by
    have he := (F.attack.pos 0).isLt
    omega
  omega

/-! ## Scalar multiplication does not repair zero or upward drift -/

theorem no_rescale_of_nonnegative_drift {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (V : StopNode S → Nat)
    (x : S) (c : Nat) (hm : 0 < m)
    (h : m * V (.active x) ≤ (List.ofFn (fun e : Fin m => V (step x e))).sum) :
    ¬ (m + (List.ofFn (fun e : Fin m => c * V (step x e))).sum ≤
      m * (c * V (.active x))) := by
  have hh := Nat.mul_le_mul_left c h
  have he : c * (m * V (.active x)) = m * (c * V (.active x)) := by
    ac_rfl
  rw [he] at hh
  intro hb
  rw [FiniteUniformStoppingTree.ofFn_sum_mul_left] at hb
  omega

def scaledEntrancePotential (F : TwoGapFrame n) (c : Nat)
    (q : StopNode (TaggedState n psi)) : Nat :=
  c * entrancePotential F (eraseNode q)

theorem no_scaling_of_raw_plateau
    (hpsi : psi > 0) (F : TwoGapFrame n) (c : Nat) (z : TaggedState n psi)
    (hp : ∀ e : Fin n,
      rawStoppedR F (entranceStep hpsi F z.raw e) = R F z.raw) :
    ¬ (n + (List.ofFn (fun e : Fin n =>
      scaledEntrancePotential F c (taggedEntranceStep hpsi F z e))).sum ≤
      n * scaledEntrancePotential F c (.active z)) := by
  have hn : 0 < n := by
    have he := (F.attack.pos 0).isLt
    omega
  have hv (q : StopNode (AState n psi)) :
      entrancePotential F q = n * rawStoppedR F q := by
    cases q <;> rfl
  have hchild : ∀ e : Fin n,
      entrancePotential F (eraseNode (taggedEntranceStep hpsi F z e)) =
      entrancePotential F (.active z.raw) := by
    intro e
    rw [erase_taggedEntranceStep]
    calc
      _ = n * rawStoppedR F (entranceStep hpsi F z.raw e) := hv _
      _ = n * R F z.raw := congrArg (fun t : Nat => n * t) (hp e)
      _ = _ := rfl
  have hs := (FiniteUniformStoppingTree.ofFn_sum_eq _ _ hchild).trans
    (FiniteUniformStoppingTree.ofFn_sum_const n (entrancePotential F (.active z.raw)))
  exact no_rescale_of_nonnegative_drift (taggedEntranceStep hpsi F)
    (fun q => entrancePotential F (eraseNode q)) z c hn (Nat.le_of_eq hs.symm)

/-! ## Sound retagging: require the certificate, rather than every FIRE -/

def certify (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi) :
    TaggedState n psi := by
  classical
  exact ⟨x, if AInvariant hpsi F x then .tracking else .seeking⟩

theorem certify_corrected
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi)
    (hg : GapPair hpsi F x) : AInvariant' hpsi F (certify hpsi F x) := by
  classical
  refine ⟨hg.recovery, hg.attack, ?_⟩
  intro hm
  by_cases hi : AInvariant hpsi F x
  · exact hi.tag
  · have hmode : (certify hpsi F x).mode = .seeking := by
      change (if AInvariant hpsi F x then TagMode.tracking else TagMode.seeking) =
        TagMode.seeking
      exact if_neg hi
    have hbad : TagMode.seeking = TagMode.tracking := hmode.symm.trans hm
    cases hbad

def certifyingStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TaggedState n psi) (e : Fin n) : StopNode (TaggedState n psi) :=
  match entranceStep hpsi F z.raw e with
  | .active x => .active (certify hpsi F x)
  | .success => .success
  | .failure => .failure

theorem certifying_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TaggedState n psi) (e : Fin n) :
    eraseNode (certifyingStep hpsi F z e) = entranceStep hpsi F z.raw e := by
  unfold certifyingStep
  cases entranceStep hpsi F z.raw e <;> rfl

/-! ## Conditional service renewal -/

theorem one_credit_sum {m : Nat} (a b : Fin m → Nat) (c : Nat) (p : Fin m)
    (hall : ∀ i, a i ≤ b i) (hone : c + a p ≤ b p) :
    c + (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction m generalizing c with
  | zero => exact Fin.elim0 p
  | succ m ih =>
      cases p using Fin.cases with
      | zero =>
          simp only [List.ofFn_succ, List.sum_cons]
          have ht := FiniteUniformStoppingTree.ofFn_sum_le
            (fun i : Fin m => a i.succ) (fun i => b i.succ)
            (fun i => hall i.succ)
          omega
      | succ p =>
          simp only [List.ofFn_succ, List.sum_cons]
          have hh := hall (0 : Fin (m + 1))
          have ht := ih (fun i : Fin m => a i.succ) (fun i => b i.succ)
            c p (fun i => hall i.succ) hone
          omega

theorem sum_point {m : Nat} (p : Fin m) (c : Nat) :
    (List.ofFn (fun e : Fin m => if e = p then c else 0)).sum = c := by
  classical
  induction m generalizing c with
  | zero => exact Fin.elim0 p
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons]
      cases p using Fin.cases with
      | zero =>
          rw [if_pos (Eq.refl (0 : Fin (m + 1)))]
          have ht : ∀ i : Fin m,
              (if i.succ = (0 : Fin (m + 1)) then c else 0) = 0 := by
            intro i
            apply if_neg
            intro h
            have hv := congrArg Fin.val h
            change i.val + 1 = 0 at hv
            omega
          have hz : (List.ofFn (fun _ : Fin m => 0)).sum = 0 := by
            rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero]
          have htail := (FiniteUniformStoppingTree.ofFn_sum_eq _ _ ht).trans hz
          rw [htail, Nat.add_zero]
      | succ p =>
          have h0 : (0 : Fin (m + 1)) ≠ p.succ := by
            intro h
            have hv := congrArg Fin.val h
            change 0 = p.val + 1 at hv
            omega
          rw [if_neg h0, Nat.zero_add]
          have ht : ∀ i : Fin m,
              (if i.succ = p.succ then c else 0) = (if i = p then c else 0) := by
            intro i
            by_cases he : i = p
            · subst i
              rw [if_pos (Eq.refl p.succ), if_pos (Eq.refl p)]
            · have hne : i.succ ≠ p.succ := by
                intro h
                apply he
                apply Fin.ext
                have hv := congrArg Fin.val h
                change i.val + 1 = p.val + 1 at hv
                omega
              rw [if_neg hne, if_neg he]
          exact (FiniteUniformStoppingTree.ofFn_sum_eq _ _ ht).trans (ih p c)

def serviceRank {S : Type} (r : S → Nat) : StopNode S → Nat
  | .active x => r x
  | .success => 0
  | .failure => 0

def servicePotential {S : Type} (m B : Nat) (r : S → Nat) : StopNode S → Nat
  | .active x => m * (r x + B + 1)
  | .success => 0
  | .failure => 0

/-- The one remaining service-row residual. Service terminals must mean
actual exits. No instance for the concrete entrance is asserted. -/
structure SeekingServiceResidual {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (r : S → Nat) (B : Nat) : Prop where
  rows : ∀ x : S,
    (0 < r x →
      (∀ e : Fin m, serviceRank r (step x e) ≤ r x) ∧
      ∃ e : Fin m, serviceRank r (step x e) < r x) ∧
    (r x = 0 → ∃ good bad : Fin m,
      good ≠ bad ∧ step x good = .success ∧
      ∀ e : Fin m, serviceRank r (step x e) ≤ if e = bad then B else 0)

theorem service_child_bound {S : Type} (m B t : Nat) (r : S → Nat)
    (q : StopNode S) (h : serviceRank r q ≤ t) :
    servicePotential m B r q ≤ m * (B + 1) + m * t := by
  cases q with
  | success => exact Nat.zero_le _
  | failure => exact Nat.zero_le _
  | active y =>
      change r y ≤ t at h
      change m * (r y + B + 1) ≤ m * (B + 1) + m * t
      calc
        _ ≤ m * ((B + 1) + t) := Nat.mul_le_mul_left m (by omega)
        _ = _ := Nat.mul_add m (B + 1) t

theorem service_bellman {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (r : S → Nat) (B : Nat)
    (h : SeekingServiceResidual step r B) (x : S) :
    m + (List.ofFn (fun e : Fin m => servicePotential m B r (step x e))).sum ≤
      m * servicePotential m B r (.active x) := by
  classical
  by_cases hz : r x = 0
  · obtain ⟨good, bad, hne, hgood, hreset⟩ := (h.rows x).2 hz
    have hall : ∀ e : Fin m, servicePotential m B r (step x e) ≤
        m * (B + 1) + (if e = bad then m * B else 0) := by
      intro e
      have hh := service_child_bound m B (if e = bad then B else 0)
        r (step x e) (hreset e)
      by_cases he : e = bad
      · simpa only [if_pos he] using hh
      · simpa only [if_neg he, Nat.mul_zero] using hh
    have hone : m * (B + 1) + servicePotential m B r (step x good) ≤
        m * (B + 1) + (if good = bad then m * B else 0) := by
      rw [hgood, if_neg hne]
      exact Nat.le_refl _
    have hc := one_credit_sum
      (fun e : Fin m => servicePotential m B r (step x e))
      (fun e : Fin m => m * (B + 1) + (if e = bad then m * B else 0))
      (m * (B + 1)) good hall hone
    have hs : (List.ofFn (fun e : Fin m =>
        m * (B + 1) + (if e = bad then m * B else 0))).sum =
        m * (m * (B + 1)) + m * B := by
      rw [FiniteUniformStoppingTree.ofFn_sum_add,
        FiniteUniformStoppingTree.ofFn_sum_const, sum_point]
    rw [hs] at hc
    have hp : servicePotential m B r (.active x) = m * (B + 1) := by
      change m * (r x + B + 1) = m * (B + 1)
      rw [hz, Nat.zero_add]
    have hsplit : m * (B + 1) = m * B + m := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [hp]
    omega
  · obtain ⟨hle, e, hlt⟩ := (h.rows x).1 (by omega)
    have hp : servicePotential m B r (.active x) = m * (B + 1) + m * r x := by
      change m * (r x + B + 1) = m * (B + 1) + m * r x
      rw [show r x + B + 1 = (B + 1) + r x by omega, Nat.mul_add]
    have hall : ∀ i : Fin m,
        servicePotential m B r (step x i) ≤ servicePotential m B r (.active x) := by
      intro i
      rw [hp]
      exact service_child_bound m B (r x) r (step x i) (hle i)
    have hone : m + servicePotential m B r (step x e) ≤
        servicePotential m B r (.active x) := by
      cases he : step x e with
      | success =>
          change m ≤ m * (r x + B + 1)
          have hh := Nat.mul_le_mul_left m (show 1 ≤ r x + B + 1 by omega)
          simpa only [Nat.mul_one] using hh
      | failure =>
          change m ≤ m * (r x + B + 1)
          have hh := Nat.mul_le_mul_left m (show 1 ≤ r x + B + 1 by omega)
          simpa only [Nat.mul_one] using hh
      | active y =>
          have hr : r y < r x := by
            simpa only [he, serviceRank] using hlt
          calc
            m + servicePotential m B r (.active y) = m * (r y + B + 1 + 1) := by
              simp only [servicePotential, Nat.mul_add, Nat.mul_one]
              omega
            _ ≤ servicePotential m B r (.active x) :=
              Nat.mul_le_mul_left m (by change r y + B + 1 + 1 ≤ r x + B + 1; omega)
    have hc := one_credit_sum
      (fun i : Fin m => servicePotential m B r (step x i))
      (fun _ : Fin m => servicePotential m B r (.active x)) m e hall hone
    rw [FiniteUniformStoppingTree.ofFn_sum_const] at hc
    exact hc

theorem service_super {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (r : S → Nat) (B : Nat)
    (h : SeekingServiceResidual step r B) :
    NatBellmanSuperSolution step 1 (servicePotential m B r) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  simpa only [Nat.one_mul] using service_bellman step r B h x

theorem service_cost {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (r : S → Nat) (B : Nat)
    (h : SeekingServiceResidual step r B) (q : StopNode S) (T : Nat) :
    truncatedActiveCostNumerator step q T ≤ m ^ T * servicePotential m B r q := by
  simpa only [Nat.one_mul] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      step 1 (servicePotential m B r) (service_super step r B h) q T

theorem service_cost_two_d {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (r : S → Nat) (d : Nat)
    (h : SeekingServiceResidual step r (2 * d)) (x : S)
    (hr : r x ≤ 2 * d) (T : Nat) :
    truncatedActiveCostNumerator step (.active x) T ≤ m ^ T * (m * (4 * d + 1)) := by
  have hc := service_cost step r (2 * d) h (.active x) T
  have hb : r x + 2 * d + 1 ≤ 4 * d + 1 := by omega
  exact Nat.le_trans hc (Nat.mul_le_mul_left (m ^ T) (Nat.mul_le_mul_left m hb))

theorem service_cost_at_pred {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (r : S → Nat) (d : Nat)
    (h : SeekingServiceResidual step r (2 * d)) (x : S)
    (hd : 0 < d) (hr : r x = d - 1) (T : Nat) :
    truncatedActiveCostNumerator step (.active x) T ≤ m ^ T * (m * (3 * d)) := by
  have hc := service_cost step r (2 * d) h (.active x) T
  change truncatedActiveCostNumerator step (.active x) T ≤
    m ^ T * (m * (r x + 2 * d + 1)) at hc
  have he : r x + 2 * d + 1 = 3 * d := by omega
  rw [he] at hc
  exact hc

/-! ## Episode arithmetic and the exact refill obligation -/

def episodeBudget (m span : Nat) : Nat := 2 * 32 * (32 * m * span + 4 * m)

theorem episodeBudget_eq (m span : Nat) :
    episodeBudget m span = 2048 * (m * span) + 256 * m := by
  unfold episodeBudget
  calc
    _ = (2 * 32) * (32 * m * span) + (2 * 32) * (4 * m) :=
      Nat.mul_add _ _ _
    _ = ((2 * 32) * 32) * (m * span) + ((2 * 32) * 4) * m := by ac_rfl
    _ = _ := rfl

theorem one_seek_fits_episode (m span d : Nat) (hd : d ≤ span) :
    m * (4 * d + 1) ≤ episodeBudget m span := by
  have hmd := Nat.mul_le_mul_left m hd
  have he : m * (4 * d + 1) = 4 * (m * d) + m := by
    rw [Nat.mul_add, Nat.mul_one]
    ac_rfl
  rw [he, episodeBudget_eq]
  omega

theorem one_seek_budget_le_double (m span d : Nat) (hd : d ≤ span) :
    episodeBudget m span + m * (4 * d + 1) ≤ 2 * episodeBudget m span := by
  have h := one_seek_fits_episode m span d hd
  omega

def prefixTotal (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | T + 1 => prefixTotal f T + f T

/-- Unit charge counts events; length-weighted charge accounts for rearming.
Refill must be bounded separately; strict event drops alone do not remove it. -/
theorem event_charge_telescope (stock charge refill : Nat → Nat)
    (h : ∀ t : Nat, stock (t + 1) + charge t ≤ stock t + refill t) (T : Nat) :
    stock T + prefixTotal charge T ≤ stock 0 + prefixTotal refill T := by
  induction T with
  | zero => exact Nat.le_refl _
  | succ T ih =>
      have ht := h T
      simp only [prefixTotal]
      omega

/-! ## Exact cost erasure does not read the chosen potential -/

theorem cost_eq_of_erasure
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (step : TaggedState n psi → Fin n → StopNode (TaggedState n psi))
    (he : ∀ z e, eraseNode (step z e) = entranceStep hpsi F z.raw e)
    (q : StopNode (TaggedState n psi)) (T : Nat) :
    truncatedActiveCostNumerator step q T =
      truncatedActiveCostNumerator (entranceStep hpsi F) (eraseNode q) T := by
  induction T generalizing q with
  | zero => rfl
  | succ T ih =>
      cases q with
      | success => rfl
      | failure => rfl
      | active z =>
          change n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
            truncatedActiveCostNumerator step (step z e) T)).sum =
            n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator (entranceStep hpsi F)
                (entranceStep hpsi F z.raw e) T)).sum
          apply congrArg (fun t : Nat => n ^ (T + 1) + t)
          apply FiniteUniformStoppingTree.ofFn_sum_eq
          intro e
          calc
            _ = truncatedActiveCostNumerator (entranceStep hpsi F)
                (eraseNode (step z e)) T := ih (step z e)
            _ = _ := congrArg
              (fun v => truncatedActiveCostNumerator (entranceStep hpsi F) v T)
              (he z e)

theorem tagged_cost_eq (hpsi : psi > 0) (F : TwoGapFrame n)
    (q : StopNode (TaggedState n psi)) (T : Nat) :
    truncatedActiveCostNumerator (taggedEntranceStep hpsi F) q T =
      truncatedActiveCostNumerator (entranceStep hpsi F) (eraseNode q) T :=
  cost_eq_of_erasure hpsi F (taggedEntranceStep hpsi F)
    (erase_taggedEntranceStep hpsi F) q T

theorem certifying_cost_eq (hpsi : psi > 0) (F : TwoGapFrame n)
    (q : StopNode (TaggedState n psi)) (T : Nat) :
    truncatedActiveCostNumerator (certifyingStep hpsi F) q T =
      truncatedActiveCostNumerator (entranceStep hpsi F) (eraseNode q) T :=
  cost_eq_of_erasure hpsi F (certifyingStep hpsi F) (certifying_erases hpsi F) q T

theorem tagged_cost_transfer (hpsi : psi > 0) (F : TwoGapFrame n)
    (V : StopNode (TaggedState n psi) → Nat) (q : StopNode (TaggedState n psi))
    (T : Nat)
    (h : truncatedActiveCostNumerator (taggedEntranceStep hpsi F) q T ≤ n ^ T * V q) :
    truncatedActiveCostNumerator (entranceStep hpsi F) (eraseNode q) T ≤
      n ^ T * V q := by
  rw [tagged_cost_eq hpsi F q T] at h
  exact h

end
end SeekingStretchCharge

#print axioms SeekingStretchCharge.initiator_fire_fields
#print axioms SeekingStretchCharge.responder_fire_fields
#print axioms SeekingStretchCharge.zero_signal_disables_initiator_fire
#print axioms SeekingStretchCharge.untouched_shooter_stays_unarmed
#print axioms SeekingStretchCharge.parked_rearm_without_pos_one_not_tag
#print axioms SeekingStretchCharge.raw_rankLaw_of_not_done
#print axioms SeekingStretchCharge.seeking_active_child
#print axioms SeekingStretchCharge.augmented_balance
#print axioms SeekingStretchCharge.constant_credit_cancels
#print axioms SeekingStretchCharge.tracking_recharge_obligation
#print axioms SeekingStretchCharge.no_constant_credit_of_plateau
#print axioms SeekingStretchCharge.no_rescale_of_nonnegative_drift
#print axioms SeekingStretchCharge.no_scaling_of_raw_plateau
#print axioms SeekingStretchCharge.certify_corrected
#print axioms SeekingStretchCharge.certifying_erases
#print axioms SeekingStretchCharge.one_credit_sum
#print axioms SeekingStretchCharge.sum_point
#print axioms SeekingStretchCharge.service_child_bound
#print axioms SeekingStretchCharge.service_bellman
#print axioms SeekingStretchCharge.service_super
#print axioms SeekingStretchCharge.service_cost
#print axioms SeekingStretchCharge.service_cost_two_d
#print axioms SeekingStretchCharge.service_cost_at_pred
#print axioms SeekingStretchCharge.episodeBudget_eq
#print axioms SeekingStretchCharge.one_seek_fits_episode
#print axioms SeekingStretchCharge.one_seek_budget_le_double
#print axioms SeekingStretchCharge.event_charge_telescope
#print axioms SeekingStretchCharge.cost_eq_of_erasure
#print axioms SeekingStretchCharge.tagged_cost_eq
#print axioms SeekingStretchCharge.certifying_cost_eq
#print axioms SeekingStretchCharge.tagged_cost_transfer
