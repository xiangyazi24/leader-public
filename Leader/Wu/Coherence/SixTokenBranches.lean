import Leader.Wu.Coherence.SixTokenController


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceBranches


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open R2Coherence


variable {n ψ κ τ : Nat}


/-- A cell itself witnesses that its group is quarantined. -/
def NonOpen (u : R2Coherence.Cell ψ κ τ) : Prop :=
  u.ctl.mark ≠ .open ∨ u.ctl.tok ≠ .none


instance nonOpenDecidable (u : R2Coherence.Cell ψ κ τ) :
    Decidable (NonOpen u) := by
  unfold NonOpen
  infer_instance


private theorem mod_add_mod_left_r2c (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem mod_add_mod_right_r2c (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem prefixPos_eq_groupPos
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat) (hk : k ≤ (raw (C i)).label.val) :
    prefixPos ring C i k = groupPos ring C i k := by
  let L := (raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by
    simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by
    dsimp [a]
    exact Nat.mod_lt _ hn
  have hb : b < n := by
    dsimp [b]
    exact Nat.mod_lt _ hn
  have hA : n ≤ A := by
    dsimp [A]
    omega
  have hLmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by
        rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n =
    (((A - (L % n)) % n + k) % n)
  symm
  by_cases hsum : a + b < n
  · have hLm : L % n = a + b := by
      calc
        L % n = (a + b) % n := hLmod
        _ = a + b := Nat.mod_eq_of_lt hsum
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_r2c (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_r2c (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b) + b = A - a := by
          omega
        rw [hnum]
  · have hsumGe : n ≤ a + b := by omega
    have hsumSub : a + b - n < n := by omega
    have hLm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hLmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hsumGe
        _ = a + b - n := Nat.mod_eq_of_lt hsumSub
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_r2c (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_r2c (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b - n) + b = n + (A - a) := by
          omega
        rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]



private theorem groupPos_label_self
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) :
    groupPos ring C i (raw (C i)).label.val = i := by
  rw [← prefixPos_eq_groupPos ring C i
    (raw (C i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [prefixPos, back, Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]



private theorem prefixDead_of_frontier_nonOpen
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (h : NonOpen (C i)) : PrefixDead ring C i := by
  unfold PrefixDead
  refine ⟨(raw (C i)).label, ?_⟩
  change NonOpen (C (groupPos ring C i (raw (C i)).label.val))
  rw [groupPos_label_self]
  exact h


private theorem prefixDead_of_prefix_nonOpen
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Fin ((raw (C i)).label.val + 1))
    (h : NonOpen (C (prefixPos ring C i k.val))) :
    PrefixDead ring C i := by
  have hkψ : k.val < ψ := by
    have hi := (raw (C i)).label.isLt
    omega
  let kk : Fin ψ := ⟨k.val, hkψ⟩
  unfold PrefixDead
  refine ⟨kk, ?_⟩
  change NonOpen (C (groupPos ring C i k.val))
  rw [← prefixPos_eq_groupPos ring C i k.val (by omega)]
  exact h


/-- Generic safety relation used by every non-reopen quarantine branch.
A physical mutation is legal only at a cell which is non-open afterwards;
and an already non-open cell is never silently reopened. -/
def QuarantineMutation
    (C D : R2Coherence.FC n ψ κ τ) : Prop :=
  ∀ p : Fin n,
    ((D p).phys ≠ (C p).phys → NonOpen (D p)) ∧
    (NonOpen (C p) → NonOpen (D p))


private theorem frontier_phys_eq_of_not_dead
    (ring : DirectedRing n) {C D : R2Coherence.FC n ψ κ τ}
    (hM : QuarantineMutation C D) (i : Fin n)
    (hnot : ¬ PrefixDead ring D i) :
    (D i).phys = (C i).phys := by
  by_cases heq : (D i).phys = (C i).phys
  · exact heq
  · have hd : PrefixDead ring D i :=
      prefixDead_of_frontier_nonOpen ring D i ((hM i).1 heq)
    exact (hnot hd).elim



private theorem groupPos_congr_of_frontier_phys
    (ring : DirectedRing n) {C D : R2Coherence.FC n ψ κ τ}
    (i : Fin n) (h : (D i).phys = (C i).phys) (k : Nat) :
    groupPos ring D i k = groupPos ring C i k := by
  simp [groupPos, groupStart, raw, h]


private theorem prefixPos_congr_of_frontier_phys
    (ring : DirectedRing n) {C D : R2Coherence.FC n ψ κ τ}
    (i : Fin n) (h : (D i).phys = (C i).phys) (k : Nat) :
    prefixPos ring D i k = prefixPos ring C i k := by
  simp [prefixPos, raw, h]


private theorem old_dead_implies_new_dead
    (ring : DirectedRing n) {C D : R2Coherence.FC n ψ κ τ}
    (hM : QuarantineMutation C D) (i : Fin n)
    (hfront : (D i).phys = (C i).phys)
    (hdead : PrefixDead ring C i) : PrefixDead ring D i := by
  rcases hdead with ⟨k, hk⟩
  have hpos := groupPos_congr_of_frontier_phys ring i hfront k.val
  have hnC : NonOpen (C (groupPos ring C i k.val)) := hk
  have hnD := (hM (groupPos ring C i k.val)).2 hnC
  unfold PrefixDead
  refine ⟨k, ?_⟩
  change NonOpen (D (groupPos ring D i k.val))
  simpa [hpos] using hnD


theorem coherentPrefixes_of_quarantineMutation
    (ring : DirectedRing n) {C D : R2Coherence.FC n ψ κ τ}
    (hM : QuarantineMutation C D)
    (hC : CoherentPrefixes ring C) : CoherentPrefixes ring D := by
  intro i hEqD
  by_cases hdeadD : PrefixDead ring D i
  · exact Or.inl hdeadD
  · have hfront : (D i).phys = (C i).phys :=
      frontier_phys_eq_of_not_dead ring hM i hdeadD
    have hrawFront : raw (D i) = raw (C i) := by
      exact congrArg (fun p : R2.Cell ψ κ τ => p.base.core.core) hfront
    have hEqC : (raw (C i)).state = .equal := by
      simpa [hrawFront] using hEqD
    rcases hC i hEqC with hdeadC | hfreshC
    · exact (hdeadD
        (old_dead_implies_new_dead ring hM i hfront hdeadC)).elim
    · right
      intro k
      let pD := prefixPos ring D i k.val
      have hpPhys : (D pD).phys = (C pD).phys := by
        by_cases heq : (D pD).phys = (C pD).phys
        · exact heq
        · have hd : PrefixDead ring D i :=
            prefixDead_of_prefix_nonOpen ring D i k ((hM pD).1 heq)
          exact (hdeadD hd).elim
      have hpos : pD = prefixPos ring C i k.val :=
        prefixPos_congr_of_frontier_phys ring i hfront k.val
      have hkC : k.val < (raw (C i)).label.val + 1 := by
        have hkD := k.isLt
        simpa [hrawFront] using hkD
      let kC : Fin ((raw (C i)).label.val + 1) := ⟨k.val, hkC⟩
      have hf := hfreshC kC
      have hpPhys' :
          (D pD).phys = (C (prefixPos ring C i k.val)).phys := by
        simpa [hpos] using hpPhys
      have hrawPos :
          raw (D pD) = raw (C (prefixPos ring C i k.val)) := by
        exact congrArg (fun p : R2.Cell ψ κ τ => p.base.core.core) hpPhys'
      unfold freshComponent at hf ⊢
      rw [hrawPos]
      exact hf



/-! ## Lifting the local wrapper branches -/

/-- Pair form of the generic mutation relation. -/
def PairQuarantineMutation
    (l r : R2Coherence.Cell ψ κ τ)
    (q : R2Coherence.Cell ψ κ τ × R2Coherence.Cell ψ κ τ) : Prop :=
  (q.1.phys ≠ l.phys → NonOpen q.1) ∧
  (q.2.phys ≠ r.phys → NonOpen q.2) ∧
  (NonOpen l → NonOpen q.1) ∧
  (NonOpen r → NonOpen q.2)

private theorem quarantineMutation_step_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2Coherence.FC n ψ κ τ) (e : Fin n)
    (hPair : PairQuarantineMutation
      (C e) (C (ring.rightNeighbor e))
      (row hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e)))) :
    QuarantineMutation C (R2Coherence.step hψ h2 ring C e) := by
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step] using (And.intro hLM hLN)
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hpe] using (And.intro hRM hRN)
    · have hSame :
          ((C p).phys ≠ (C p).phys → NonOpen (C p)) ∧
            (NonOpen (C p) → NonOpen (C p)) :=
        ⟨fun h => (h rfl).elim, fun h => h⟩
      simpa [R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hpe, hpj] using hSame



private theorem pairMutation_self
    (l r : R2Coherence.Cell ψ κ τ) :
    PairQuarantineMutation l r (l, r) := by
  simp [PairQuarantineMutation]

private theorem pairMutation_seekStage
    (l r : R2Coherence.Cell ψ κ τ) :
    PairQuarantineMutation l r (seekStage l r) := by
  unfold seekStage
  split
  · simp [PairQuarantineMutation, NonOpen, setControl]
  · split
    · simp [PairQuarantineMutation, NonOpen, setControl]
    · simp [PairQuarantineMutation, NonOpen, setControl]

private theorem pairMutation_sweepStage
    (l r : R2Coherence.Cell ψ κ τ) :
    PairQuarantineMutation l r (sweepStage l r) := by
  unfold sweepStage
  split
  · simp [PairQuarantineMutation, NonOpen, setControl]
  · exact pairMutation_self l r

private theorem pairMutation_commitStage
    (l r : R2Coherence.Cell ψ κ τ) :
    PairQuarantineMutation l r (commitStage l r) := by
  unfold commitStage
  dsimp only
  split
  · simp [PairQuarantineMutation, NonOpen, setControl]
  · split
    · simp [PairQuarantineMutation, NonOpen, setControl]
    · simp [PairQuarantineMutation, NonOpen, setControl]

private theorem pairMutation_releaseStage
    (l r : R2Coherence.Cell ψ κ τ) :
    PairQuarantineMutation l r (releaseStage l r) := by
  unfold releaseStage
  split
  · split
    · simp [PairQuarantineMutation, NonOpen, setControl]
    · split
      · simp [PairQuarantineMutation, NonOpen, setControl]
      · simp [PairQuarantineMutation, NonOpen, setControl]
  · exact pairMutation_self l r

private theorem pairMutation_sealedStage_of_marks
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ)
    (hl : l.ctl.mark = .sealed) (hr : r.ctl.mark = .sealed) :
    PairQuarantineMutation l r
      (sealedStage hψ (by decide : 0 < 2) h2 l r) := by
  unfold sealedStage
  split
  · simp [PairQuarantineMutation, NonOpen, setControl, hl, hr]
  · dsimp only
    split
    · exact pairMutation_self l r
    · simp [PairQuarantineMutation, NonOpen, install, hl, hr]

private theorem pairMutation_openStage_of_hazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ)
    (hHaz :
      pairHazard l.phys r.phys
        (proposal hψ (by decide : 0 < 2) h2 l r).1
        (proposal hψ (by decide : 0 < 2) h2 l r).2 = true) :
    PairQuarantineMutation l r
      (openStage hψ (by decide : 0 < 2) h2 l r) := by
  unfold openStage
  dsimp only
  rw [if_pos hHaz]
  split
  · simp [PairQuarantineMutation, NonOpen, startClosing, setControl]
  · simp [PairQuarantineMutation, NonOpen, startClosing, setControl]

private theorem pairMutation_of_safe_branch
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2Coherence.FC n ψ κ τ) (e : Fin n) (b : Branch)
    (hb : branchAt hψ h2 ring C e = b)
    (hReopen : b ≠ .reopen) (hOpen : b ≠ .openNoHazard) :
    PairQuarantineMutation
      (C e) (C (ring.rightNeighbor e))
      (row hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))) := by
  have hb' := hb
  unfold branchAt at hb'
  dsimp only at hb'
  unfold row
  by_cases hSeek : (C (ring.rightNeighbor e)).ctl.tok = .seek
  · rw [if_pos hSeek]
    exact pairMutation_seekStage
      (C e) (C (ring.rightNeighbor e))
  · rw [if_neg hSeek]
    rw [if_neg hSeek] at hb'
    by_cases hSweep : (C e).ctl.tok = .sweep
    · rw [if_pos hSweep]
      exact pairMutation_sweepStage
        (C e) (C (ring.rightNeighbor e))
    · rw [if_neg hSweep]
      rw [if_neg hSweep] at hb'
      by_cases hCommit : (C (ring.rightNeighbor e)).ctl.tok = .commit
      · rw [if_pos hCommit]
        exact pairMutation_commitStage
          (C e) (C (ring.rightNeighbor e))
      · rw [if_neg hCommit]
        rw [if_neg hCommit] at hb'
        by_cases hRelease : (C e).ctl.tok = .release
        · rw [if_pos hRelease]
          exact pairMutation_releaseStage
            (C e) (C (ring.rightNeighbor e))
        · rw [if_neg hRelease]
          rw [if_neg hRelease] at hb'
          by_cases hReopenTok :
              (C (ring.rightNeighbor e)).ctl.tok = .reopen
          · rw [if_pos hReopenTok] at hb'
            exact (hReopen hb'.symm).elim
          · rw [if_neg hReopenTok]
            rw [if_neg hReopenTok] at hb'
            by_cases hNone :
                (C e).ctl.tok = .none ∧
                  (C (ring.rightNeighbor e)).ctl.tok = .none
            · rw [if_pos hNone] at hb'
              unfold ordinaryStage
              rw [if_pos hNone]
              by_cases hSealed :
                  (C e).ctl.mark = .sealed ∧
                    (C (ring.rightNeighbor e)).ctl.mark = .sealed
              · rw [if_pos hSealed]
                exact pairMutation_sealedStage_of_marks hψ h2
                  (C e) (C (ring.rightNeighbor e))
                  hSealed.1 hSealed.2
              · rw [if_neg hSealed] at hb'
                rw [if_neg hSealed]
                by_cases hOpenCtl :
                    (C e).ctl.mark = .open ∧
                      (C (ring.rightNeighbor e)).ctl.mark = .open
                · rw [if_pos hOpenCtl] at hb'
                  rw [if_pos hOpenCtl]
                  by_cases hHaz :
                      pairHazard
                        (C e).phys
                        (C (ring.rightNeighbor e)).phys
                        (proposal hψ (by decide : 0 < 2) h2
                          (C e) (C (ring.rightNeighbor e))).1
                        (proposal hψ (by decide : 0 < 2) h2
                          (C e) (C (ring.rightNeighbor e))).2 = true
                  · exact pairMutation_openStage_of_hazard hψ h2
                      (C e) (C (ring.rightNeighbor e)) hHaz
                  · rw [if_neg hHaz] at hb'
                    exact (hOpen hb'.symm).elim
                · rw [if_neg hOpenCtl]
                  exact pairMutation_self
                    (C e) (C (ring.rightNeighbor e))
            · unfold ordinaryStage
              rw [if_neg hNone]
              exact pairMutation_self
                (C e) (C (ring.rightNeighbor e))



private theorem safeBranchPreservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (b : Branch)
    (hReopen : b ≠ .reopen) (hOpen : b ≠ .openNoHazard) :
    BranchPreservationObligation (κ := κ) (τ := τ) hψ h2 ring b := by
  intro C e _hGeom hC hb
  apply coherentPrefixes_of_quarantineMutation ring
    (C := C) (D := R2Coherence.step hψ h2 ring C e)
  · exact quarantineMutation_step_of_pair hψ h2 ring C e
      (pairMutation_of_safe_branch hψ h2 ring C e b hb hReopen hOpen)
  · exact hC

/-- Sealed services either stay control-only or install an output whose main
carrier has been cleared. Every physical mutation therefore remains behind a
non-open cell. -/
theorem sealed_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SealedPreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .sealed (by decide) (by decide)

/-- Hazardous open proposals are held physically; the selected endpoint only
acquires `.closing/.seek`. -/
theorem openHazard_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    OpenHazardPreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .openHazard (by decide) (by decide)

/-- SEEK moves only finite controller state and never removes the non-open
witness carried by the request. -/
theorem seek_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SeekPreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .seek (by decide) (by decide)

/-- SWEEP may erase main carriers at the serviced pair, but both visited cells
remain `.closing`, hence any prefix touching a changed cell is dead. -/
theorem sweep_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SweepPreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .sweep (by decide) (by decide)

/-- COMMIT clears main material and changes swept cells only to `.sealed` or
keeps the leftward `.closing/.commit` witness. -/
theorem commit_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    CommitPreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .commit (by decide) (by decide)

/-- RELEASE is physically frozen. The token owner remains non-open, or aborts
back to a sealed/commit state. -/
theorem release_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ReleasePreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .release (by decide) (by decide)

/-- MIXED is the wrapper's fail-closed identity lane. -/
theorem mixed_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    MixedPreservationObligation (κ := κ) (τ := τ) hψ h2 ring := by
  exact safeBranchPreservation (κ := κ) (τ := τ)
    hψ h2 ring .mixed (by decide) (by decide)

/-! ## Exact CHECK algebra and the two false obligations -/

/-- The missing current-state premise: a stored ready state must actually be
aligned with the resident label. -/
def ReadyAlignedRaw (u : AgentState ψ) : Prop :=
  u.state = .CHECK_ready →
    match u.path with
    | .bot => False
    | .some lab _ => lab = u.label.val

/-- Freshness of the one component which CHECK has just compared. -/
def FreshRaw (u : AgentState ψ) : Prop :=
  match u.path with
  | .bot => False
  | .some lab b =>
      lab = u.label.val ∧ b = (if u.bit then 1 else 0)

instance readyAlignedRawDecidable (u : AgentState ψ) :
    Decidable (ReadyAlignedRaw u) := by
  unfold ReadyAlignedRaw
  cases hp : u.path with
  | bot =>
      simp only [hp]
      infer_instance
  | some lab bit =>
      simp only [hp]
      infer_instance


instance freshRawDecidable (u : AgentState ψ) : Decidable (FreshRaw u) := by
  unfold FreshRaw
  cases hp : u.path with
  | bot =>
      simp only [hp]
      infer_instance
  | some lab bit =>
      simp only [hp]
      infer_instance


theorem checkBit_equal_iff (agentBit : Bool) (signalBit : Nat) :
    checkBit agentBit signalBit = .equal ↔
      signalBit = (if agentBit then 1 else 0) := by
  cases agentBit with
  | false =>
      by_cases h : signalBit = 0
      · subst signalBit
        simp [checkBit]
      · have h0 : (0 : Nat) ≠ signalBit := by
          intro h'
          exact h h'.symm
        simp [checkBit, h, h0]
  | true =>
      by_cases h : signalBit = 1
      · subst signalBit
        simp [checkBit]
      · have h1 : (1 : Nat) ≠ signalBit := by
          intro h'
          exact h h'.symm
        by_cases h0 : signalBit = 0
        · subst signalBit
          simp [checkBit]
        · have hgt : ¬(1 : Nat) > signalBit := by
            omega
          simp [checkBit, h, h1, h0, hgt]



/-- Correct left-end CHECK freshness lemma. The extra `ReadyAlignedRaw` premise
is necessary only for an arbitrarily initialized old CHECK_ready. -/
theorem checkSigCheckL_new_equal_fresh
    (hψ : 0 < ψ) (u : AgentState ψ)
    (hready : ReadyAlignedRaw u) (hold : u.state ≠ .equal)
    (hout :
      (checkSigCheckL hψ (checkSigSetReady u)).state = .equal) :
    FreshRaw u := by
  cases hp : u.path with
  | bot =>
      simp_all [ReadyAlignedRaw, FreshRaw, checkSigSetReady, checkSigCheckL]
  | some lab bit =>
      unfold checkSigCheckL at hout
      simp only [checkSigSetReady, hp] at hout
      repeat' split at hout <;>
        simp_all [ReadyAlignedRaw, FreshRaw, hp, checkBit]


private theorem checkSigSetReady_path_r2c (u : AgentState ψ) :
    (checkSigSetReady u).path = u.path := by
  unfold checkSigSetReady
  cases hp : u.path <;> repeat (first | rfl | exact hp | split)

private theorem checkSigSetReady_bit_r2c (u : AgentState ψ) :
    (checkSigSetReady u).bit = u.bit := by
  unfold checkSigSetReady
  cases hp : u.path <;> repeat (first | rfl | split)

private theorem checkSigSetReady_not_equal_r2c
    (u : AgentState ψ) (h : u.state ≠ .equal) :
    (checkSigSetReady u).state ≠ .equal := by
  cases hp : u.path <;> simp [checkSigSetReady, hp, h] <;> split <;> simp_all

private theorem checkSigSetReady_ready_aligned_r2c
    (u : AgentState ψ) (lab bit : Nat)
    (hp : u.path = .some lab bit)
    (hready : ReadyAlignedRaw u)
    (hs : (checkSigSetReady u).state = .CHECK_ready) :
    lab = u.label.val := by
  have hready' : u.state = .CHECK_ready → lab = u.label.val := by
    simpa [ReadyAlignedRaw, hp] using hready
  by_cases hlabel : u.label.val = lab
  · exact hlabel.symm
  · apply hready'
    simpa [checkSigSetReady, hp, hlabel] using hs

theorem checkSigCheckR_new_equal_fresh
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hready : ReadyAlignedRaw r) (hold : r.state ≠ .equal)
    (hout :
      (checkSigCheckR hψ
        (checkSigCheckL hψ (checkSigSetReady l))
        (checkSigSetReady r)).state = .equal) :
    FreshRaw r := by
  cases hp : r.path with
  | bot =>
      have hrPath : (checkSigSetReady r).path = .bot := by
        calc
          (checkSigSetReady r).path = r.path :=
            checkSigSetReady_path_r2c r
          _ = .bot := hp
      have hrNotEq : (checkSigSetReady r).state ≠ .equal :=
        checkSigSetReady_not_equal_r2c r hold
      let l1 := checkSigCheckL hψ (checkSigSetReady l)
      change (checkSigCheckR hψ l1 (checkSigSetReady r)).state = .equal at hout
      unfold checkSigCheckR at hout
      rw [hrPath] at hout
      change (checkSigSetReady r).state = .equal at hout
      exact (hrNotEq hout).elim
  | some lab bit =>
      have hrPath : (checkSigSetReady r).path = .some lab bit := by
        calc
          (checkSigSetReady r).path = r.path :=
            checkSigSetReady_path_r2c r
          _ = .some lab bit := hp
      have hrBit : (checkSigSetReady r).bit = r.bit :=
        checkSigSetReady_bit_r2c r
      have hrNotEq : (checkSigSetReady r).state ≠ .equal :=
        checkSigSetReady_not_equal_r2c r hold
      let l1 := checkSigCheckL hψ (checkSigSetReady l)
      change (checkSigCheckR hψ l1 (checkSigSetReady r)).state = .equal at hout
      unfold checkSigCheckR at hout
      rw [hrPath] at hout
      dsimp only at hout
      split at hout
      · split at hout
        · rename_i hrReady
          dsimp only at hout
          unfold FreshRaw
          rw [hp]
          constructor
          · exact checkSigSetReady_ready_aligned_r2c
              r lab bit hp hready hrReady
          · have hbit :
                bit = (if (checkSigSetReady r).bit then 1 else 0) :=
              (checkBit_equal_iff (checkSigSetReady r).bit bit).1 hout
            rw [hrBit] at hbit
            exact hbit
        · exact (hrNotEq hout).elim
      · exact (hrNotEq hout).elim



namespace Counterexamples

private abbrev PCfg := R2.FC 3 3 3 48
private abbrev WCfg := R2Coherence.FC 3 3 3 48

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

/-- Complete bounded literal, using `clean` only as a finite record template. -/
private def literal (i : Fin 3)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (bit : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) i
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      state := state
      path := path
      bit := bit
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def openCell (p : R2.Cell 3 3 48) : R2Coherence.Cell 3 3 48 :=
  ⟨p, ⟨.open, .none⟩⟩

/-! ### False branch 1: OPEN-NO-HAZARD -/

/-- Cell 0 is a genuinely fresh equal prefix of length one. Cell 1 is a forged
misaligned CHECK_ready: resident label 1, payload label 0. There are no bit or
label writers and every quarantine control is open. -/
private def badReadyInput : WCfg := fun i =>
  match i.val with
  | 0 => openCell (literal 0 .equal (.some 0 0))
  | 1 => openCell (literal 1 .CHECK_ready (.some 0 0))
  | _ => openCell (literal 2 .none .bot)

private def badReadyAfter : WCfg :=
  R2Coherence.step h3 h23 ring3 badReadyInput 0

theorem badReady_geometry :
    AdmittedPostBirthGeometry h3 ring3 badReadyInput := by
  decide +kernel

theorem badReady_before_coherent :
    CoherentPrefixes ring3 badReadyInput := by
  decide +kernel

/-- This closed check includes the complete R2 proposal and proves that the
wrapper classifies the service as exact open/no-hazard. -/
theorem badReady_branch :
    branchAt h3 h23 ring3 badReadyInput 0 = .openNoHazard := by
  decide +kernel

/-- Exact field image to audit if the regression ever changes. -/
theorem badReady_after_fields :
    (raw (badReadyAfter 1)).label = (1 : Fin 3) ∧
    (raw (badReadyAfter 1)).bit = false ∧
    (raw (badReadyAfter 1)).state = .equal ∧
    (raw (badReadyAfter 1)).path = .some 0 0 ∧
    (badReadyAfter 1).ctl = ⟨.open, .none⟩ := by
  decide +kernel

/-- The new equality is bit-equal but label-incoherent, hence not a fresh
component at label one. -/
theorem badReady_after_not_coherent :
    ¬ CoherentPrefixes ring3 badReadyAfter := by
  decide +kernel

theorem openNoHazardPreservation_false :
    ¬ OpenNoHazardPreservationObligation
      (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro h
  exact badReady_after_not_coherent
    (h badReadyInput 0 badReady_geometry badReady_before_coherent badReady_branch)

/-! ### False branch 2: REOPEN -/

private def reopenPhys : PCfg := fun i =>
  match i.val with
  | 0 => literal 0 .none (.some 0 0)
  | 1 => literal 1 .none (.some 1 0)
  | _ => literal 2 .equal (.some 2 0)

/-- The responder's malformed final reopen token is the sole witness making
cell 2's equality logically dead. -/
private def reopenInput : WCfg := fun i =>
  match i.val with
  | 0 => openCell (reopenPhys 0)
  | 1 => ⟨reopenPhys 1, ⟨.releasing, .reopen⟩⟩
  | _ => openCell (reopenPhys 2)

private def reopenAfter : WCfg :=
  R2Coherence.step h3 h23 ring3 reopenInput 0

theorem reopen_geometry :
    AdmittedPostBirthGeometry h3 ring3 reopenInput := by
  decide +kernel

theorem reopen_before_coherent :
    CoherentPrefixes ring3 reopenInput := by
  decide +kernel

theorem reopen_branch :
    branchAt h3 h23 ring3 reopenInput 0 = .reopen := by
  decide +kernel

/-- Final root reopen clears only cells 0 and 1, consumes the last non-open
witness, and leaves the remote equality at cell 2. -/
theorem reopen_after_fields :
    (raw (reopenAfter 0)).path = .bot ∧
    (raw (reopenAfter 1)).path = .bot ∧
    (raw (reopenAfter 2)).state = .equal ∧
    (raw (reopenAfter 2)).path = .some 2 0 ∧
    (∀ i : Fin 3, (reopenAfter i).ctl = ⟨.open, .none⟩) := by
  decide +kernel

theorem reopen_after_not_coherent :
    ¬ CoherentPrefixes ring3 reopenAfter := by
  decide +kernel

theorem reopenPreservation_false :
    ¬ ReopenPreservationObligation
      (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro h
  exact reopen_after_not_coherent
    (h reopenInput 0 reopen_geometry reopen_before_coherent reopen_branch)

end Counterexamples

/-! ## Corrected current-state obligations and assembly -/

/-- Bounded form of the CHECK-ready alignment condition. -/
def ReadyAlignedCell (u : R2Coherence.Cell ψ κ τ) : Prop :=
  (raw u).state = .CHECK_ready →
    match (raw u).path with
    | .bot => False
    | .some lab _ => lab = (raw u).label

instance readyAlignedCellDecidable (u : R2Coherence.Cell ψ κ τ) :
    Decidable (ReadyAlignedCell u) := by
  unfold ReadyAlignedCell
  cases hp : (raw u).path with
  | bot =>
      simp only [hp]
      infer_instance
  | some lab bit =>
      simp only [hp]
      infer_instance


def ReadyAlignedAll (C : R2Coherence.FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, ReadyAlignedCell (C i)

instance readyAlignedAllDecidable (C : R2Coherence.FC n ψ κ τ) :
    Decidable (ReadyAlignedAll C) := by
  unfold ReadyAlignedAll
  infer_instance

/-- Local executable correction for arbitrary garbage: a misaligned or
pathless stored CHECK_ready is retired before the open-lane R2 proposal. -/
def sanitizeReadyPhys (u : R2.Cell ψ κ τ) : R2.Cell ψ κ τ :=
  let b := u.base.core.core
  if b.state = .CHECK_ready then
    match b.path with
    | .bot => clearMainPhys u
    | .some lab _ =>
        if lab = b.label then u else clearMainPhys u
  else u

theorem sanitizeReadyPhys_eq_self
    (u : R2.Cell ψ κ τ)
    (h :
      u.base.core.core.state = .CHECK_ready →
        match u.base.core.core.path with
        | .bot => False
        | .some lab _ => lab = u.base.core.core.label) :
    sanitizeReadyPhys u = u := by
  unfold sanitizeReadyPhys
  dsimp only
  by_cases hs : u.base.core.core.state = .CHECK_ready
  · rw [if_pos hs]
    cases hp : u.base.core.core.path with
    | bot =>
        have hf : False := by
          have hh := h hs
          simpa [hp] using hh
        exact hf.elim
    | some lab bit =>
        have ha : lab = u.base.core.core.label := by
          have hh := h hs
          simpa [hp] using hh
        simp [hp, ha]
  · rw [if_neg hs]


def readySanitizedProposal
    {width : Nat}
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ) :
    R2.Cell ψ κ τ × R2.Cell ψ κ τ :=
  R2.row hψ hw hle (sanitizeReadyPhys l.phys) (sanitizeReadyPhys r.phys)


/-- Main-carrier emptiness needed by a legitimate reopen suffix. -/
def MainClear (u : R2Coherence.Cell ψ κ τ) : Prop :=
  (raw u).state = .none ∧
  (raw u).path = .bot ∧
  (raw u).path2 = none ∧
  (raw u).path4 = none ∧
  (raw u).path5 = none ∧
  (raw u).p = false ∧
  (raw u).p_carry = false

instance mainClearDecidable (u : R2Coherence.Cell ψ κ τ) :
    Decidable (MainClear u) := by
  unfold MainClear
  infer_instance

/-- Current-state certificate carried by a legitimate right-to-left reopen
wave: the token holder and every already traversed more-significant cell have
actually been main-cleared. No history/source ID is stored. -/
def ReopenSuffixClear
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ) (e : Fin n) : Prop :=
  let r := C (ring.rightNeighbor e)
  r.ctl.tok = .reopen →
    ∀ k : Fin ψ, (raw r).label.val ≤ k.val →
      MainClear (C (groupPos ring C (ring.rightNeighbor e) k.val))

instance reopenSuffixClearDecidable
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ) (e : Fin n) :
    Decidable (ReopenSuffixClear ring C e) := by
  unfold ReopenSuffixClear
  infer_instance

/-- Corrected OPEN-NO-HAZARD theorem boundary. The raw CHECK lemmas in Part 3
identify `ReadyAlignedAll` as the missing finite premise. -/
def OpenNoHazardAlignedObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : R2Coherence.FC n ψ κ τ) (e : Fin n),
    AdmittedPostBirthGeometry hψ ring C →
    CoherentPrefixes ring C →
    ReadyAlignedAll C →
    branchAt hψ h2 ring C e = .openNoHazard →
    CoherentPrefixes ring (R2Coherence.step hψ h2 ring C e)

/-- Corrected REOPEN theorem boundary. A legitimate wave has this suffix
certificate inductively; the arbitrary-token counterexample does not. -/
def ReopenCertifiedObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : R2Coherence.FC n ψ κ τ) (e : Fin n),
    AdmittedPostBirthGeometry hψ ring C →
    CoherentPrefixes ring C →
    ReopenSuffixClear ring C e →
    branchAt hψ h2 ring C e = .reopen →
    CoherentPrefixes ring (R2Coherence.step hψ h2 ring C e)

/-- Requested assembly against the *old* nine-field interface. The only
remaining hypotheses are exactly the two branches refuted in Part 3. Because
those global old Props are false, this theorem is an interface reducer, not a
claim that the present gate has passed. -/
theorem coherentPrefixes_step_unconditional
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hReopen : ReopenPreservationObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hOpen : OpenNoHazardPreservationObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : R2Coherence.FC n ψ κ τ)
    (hGeom : AdmittedPostBirthGeometry hψ ring C)
    (hC : CoherentPrefixes ring C) (e : Fin n) :
    CoherentPrefixes ring (R2Coherence.step hψ h2 ring C e) := by
  let hO : PreservationObligations (κ := κ) (τ := τ) hψ h2 ring :=
    { seek := seek_preservation hψ h2 ring
      sweep := sweep_preservation hψ h2 ring
      commit := commit_preservation hψ h2 ring
      release := release_preservation hψ h2 ring
      reopen := hReopen
      sealed := sealed_preservation hψ h2 ring
      openHazard := openHazard_preservation hψ h2 ring
      openNoHazard := hOpen
      mixed := mixed_preservation hψ h2 ring }
  exact R2Coherence.coherentPrefixes_step hψ h2 ring hO C hGeom hC e

/-- Meaningful corrected-domain dispatcher. It keeps the seven proved branches
and asks only for the two strengthened, satisfiable branch lemmas. -/
theorem coherentPrefixes_step_corrected_domain
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hOpen : OpenNoHazardAlignedObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hReopen : ReopenCertifiedObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : R2Coherence.FC n ψ κ τ)
    (hGeom : AdmittedPostBirthGeometry hψ ring C)
    (hC : CoherentPrefixes ring C)
    (hReady : ReadyAlignedAll C)
    (hReopenCert : ∀ e : Fin n, ReopenSuffixClear ring C e)
    (e : Fin n) :
    CoherentPrefixes ring (R2Coherence.step hψ h2 ring C e) := by
  cases hb : branchAt hψ h2 ring C e with
  | seek => exact seek_preservation hψ h2 ring C e hGeom hC hb
  | sweep => exact sweep_preservation hψ h2 ring C e hGeom hC hb
  | commit => exact commit_preservation hψ h2 ring C e hGeom hC hb
  | release => exact release_preservation hψ h2 ring C e hGeom hC hb
  | reopen => exact hReopen C e hGeom hC (hReopenCert e) hb
  | sealed => exact sealed_preservation hψ h2 ring C e hGeom hC hb
  | openHazard => exact openHazard_preservation hψ h2 ring C e hGeom hC hb
  | openNoHazard => exact hOpen C e hGeom hC hReady hb
  | mixed => exact mixed_preservation hψ h2 ring C e hGeom hC hb

end R2CoherenceBranches
