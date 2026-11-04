import Leader.Wu.Coherence.SixTokenBranches

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZShadowR2CoherenceRepaired

open R2Coherence
open R2CoherenceBranches

variable {n ψ κ τ width : Nat}

/-- Shadow repair A: malformed sweep restarts closing/seek. -/
def sweepStageRepaired
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    let l' := setControl (clearMain l) .closing .none
    let r' := setControl (clearMain r) .closing
      (if atTerminalB r then .commit else .sweep)
    (l', r')
  else
    (startClosing l, r)

/-- Shadow repair B: malformed release also restarts closing/seek. -/
def releaseStageRepaired
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if successorB l r then
    if writerQuiet r then
      let l' := setControl l .releasing .none
      let r' := setControl r .releasing
        (if atTerminalB r then .reopen else .release)
      (l', r')
    else if atRootB l then
      (setControl l .sealed .none, r)
    else
      (setControl l .closing .commit, r)
  else
    (startClosing l, r)

/-- Shadow repair C: token-free mixed marks fail closed without touching phys. -/
def ordinaryStageRepaired
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if l.ctl.tok = .none ∧ r.ctl.tok = .none then
    if l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed then
      sealedStage hψ hw hle l r
    else if l.ctl.mark = .open ∧ r.ctl.mark = .open then
      openStage hψ hw hle l r
    else
      (l, startClosing r)
  else
    (l, r)

/-- Same old six-token dispatcher, with exactly A/B/C replaced. -/
def rowRepaired
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if r.ctl.tok = .seek then seekStage l r
  else if l.ctl.tok = .sweep then sweepStageRepaired l r
  else if r.ctl.tok = .commit then commitStage l r
  else if l.ctl.tok = .release then releaseStageRepaired l r
  else if r.ctl.tok = .reopen then reopenStage l r
  else ordinaryStageRepaired hψ hw hle l r

def protocolRepaired
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := Cell ψ κ τ
  Y := Bool
  transition := rowRepaired hψ (by decide : 0 < 2) h2
  output := fun u => (raw u).leader

def stepRepaired
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (protocolRepaired hψ h2 κ τ).step ring C e

private theorem mod_add_mod_left (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem mod_add_mod_right (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem prefixPos_eq_groupPos
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) (k : Nat) (hk : k ≤ (raw (C i)).label.val) :
    prefixPos ring C i k = groupPos ring C i k := by
  let L := (raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by exact Nat.mod_lt _ hn
  have hb : b < n := by exact Nat.mod_lt _ hn
  have hA : n ≤ A := by dsimp [A]; omega
  have hLmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n = (((A - (L % n)) % n + k) % n)
  symm
  by_cases hsum : a + b < n
  · have hLm : L % n = a + b := by
      calc
        L % n = (a + b) % n := hLmod
        _ = a + b := Nat.mod_eq_of_lt hsum
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n := mod_add_mod_left _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (mod_add_mod_right (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b) + b = A - a := by omega
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
          (A - (L % n) + k) % n := mod_add_mod_left _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (mod_add_mod_right (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

private theorem groupPos_label_self
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    groupPos ring C i (raw (C i)).label.val = i := by
  rw [← prefixPos_eq_groupPos ring C i (raw (C i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [prefixPos, back, Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem prefixDead_of_frontier_nonOpen
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) (h : NonOpen (C i)) : PrefixDead ring C i := by
  unfold PrefixDead
  refine ⟨(raw (C i)).label, ?_⟩
  change NonOpen (C (groupPos ring C i (raw (C i)).label.val))
  rw [groupPos_label_self]
  exact h

private theorem prefixDead_of_prefix_nonOpen
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) (k : Fin ((raw (C i)).label.val + 1))
    (h : NonOpen (C (prefixPos ring C i k.val))) : PrefixDead ring C i := by
  have hkψ : k.val < ψ := by
    have hi := (raw (C i)).label.isLt
    omega
  let kk : Fin ψ := ⟨k.val, hkψ⟩
  unfold PrefixDead
  refine ⟨kk, ?_⟩
  change NonOpen (C (groupPos ring C i k.val))
  rw [← prefixPos_eq_groupPos ring C i k.val (by omega)]
  exact h

def QuarantineMutationRepaired (C D : FC n ψ κ τ) : Prop :=
  ∀ p : Fin n,
    ((D p).phys ≠ (C p).phys → NonOpen (D p)) ∧
      (NonOpen (C p) → NonOpen (D p))

private theorem coherentPrefixes_of_quarantineMutation
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hM : QuarantineMutationRepaired C D)
    (hC : CoherentPrefixes ring C) : CoherentPrefixes ring D := by
  intro i hEqD
  by_cases hdeadD : PrefixDead ring D i
  · exact Or.inl hdeadD
  · have hfront : (D i).phys = (C i).phys := by
      by_cases heq : (D i).phys = (C i).phys
      · exact heq
      · exact (hdeadD (prefixDead_of_frontier_nonOpen ring D i ((hM i).1 heq))).elim
    have hrawFront : raw (D i) = raw (C i) :=
      congrArg (fun p : R2.Cell ψ κ τ => p.base.core.core) hfront
    have hEqC : (raw (C i)).state = .equal := by simpa [hrawFront] using hEqD
    rcases hC i hEqC with hdeadC | hfreshC
    · rcases hdeadC with ⟨k, hk⟩
      have hpos : groupPos ring D i k.val = groupPos ring C i k.val := by
        simp [groupPos, groupStart, raw, hfront]
      have hnD := (hM (groupPos ring C i k.val)).2 hk
      exact (hdeadD ⟨k, by rw [hpos]; exact hnD⟩).elim
    · right
      intro k
      let pD := prefixPos ring D i k.val
      have hpPhys : (D pD).phys = (C pD).phys := by
        by_cases heq : (D pD).phys = (C pD).phys
        · exact heq
        · exact (hdeadD
            (prefixDead_of_prefix_nonOpen ring D i k ((hM pD).1 heq))).elim
      have hpos : pD = prefixPos ring C i k.val := by
        simp [pD, prefixPos, raw, hfront]
      have hkC : k.val < (raw (C i)).label.val + 1 := by
        have hkD := k.isLt
        simpa [hrawFront] using hkD
      let kC : Fin ((raw (C i)).label.val + 1) := ⟨k.val, hkC⟩
      have hf := hfreshC kC
      have hpPhys' : (D pD).phys = (C (prefixPos ring C i k.val)).phys := by
        simpa [hpos] using hpPhys
      have hrawPos : raw (D pD) = raw (C (prefixPos ring C i k.val)) :=
        congrArg (fun p : R2.Cell ψ κ τ => p.base.core.core) hpPhys'
      unfold freshComponent at hf ⊢
      rw [hrawPos]
      exact hf

def PairQuarantineMutationRepaired
    (l r : Cell ψ κ τ) (q : Cell ψ κ τ × Cell ψ κ τ) : Prop :=
  (q.1.phys ≠ l.phys → NonOpen q.1) ∧
  (q.2.phys ≠ r.phys → NonOpen q.2) ∧
  (NonOpen l → NonOpen q.1) ∧
  (NonOpen r → NonOpen q.2)

private theorem pairMutation_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPair : PairQuarantineMutationRepaired
      (C e) (C (ring.rightNeighbor e))
      (rowRepaired hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e)))) :
    QuarantineMutationRepaired C (stepRepaired hψ h2 ring C e) := by
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [stepRepaired, protocolRepaired, PopulationProtocol.step] using
      (And.intro hLM hLN)
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [stepRepaired, protocolRepaired, PopulationProtocol.step, hpe] using
        (And.intro hRM hRN)
    · simp [stepRepaired, protocolRepaired, PopulationProtocol.step, hpe, hpj]

private theorem pairMutation_self (l r : Cell ψ κ τ) :
    PairQuarantineMutationRepaired l r (l, r) := by
  simp [PairQuarantineMutationRepaired]

private theorem pairMutation_safe
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (b : Branch)
    (hb : branchAt hψ h2 ring C e = b)
    (hReopen : b ≠ .reopen) (hOpen : b ≠ .openNoHazard) :
    PairQuarantineMutationRepaired
      (C e) (C (ring.rightNeighbor e))
      (rowRepaired hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))) := by
  have hb' := hb
  unfold branchAt at hb'
  dsimp only at hb'
  unfold rowRepaired
  by_cases hSeek : (C (ring.rightNeighbor e)).ctl.tok = .seek
  · rw [if_pos hSeek]
    unfold seekStage
    repeat' split <;> simp [PairQuarantineMutationRepaired, NonOpen, setControl]
  · rw [if_neg hSeek]; rw [if_neg hSeek] at hb'
    by_cases hSweep : (C e).ctl.tok = .sweep
    · rw [if_pos hSweep]
      unfold sweepStageRepaired
      split <;> simp [PairQuarantineMutationRepaired, NonOpen, startClosing, setControl]
    · rw [if_neg hSweep]; rw [if_neg hSweep] at hb'
      by_cases hCommit : (C (ring.rightNeighbor e)).ctl.tok = .commit
      · rw [if_pos hCommit]
        unfold commitStage
        dsimp only
        repeat' split <;> simp [PairQuarantineMutationRepaired, NonOpen, setControl]
      · rw [if_neg hCommit]; rw [if_neg hCommit] at hb'
        by_cases hRelease : (C e).ctl.tok = .release
        · rw [if_pos hRelease]
          unfold releaseStageRepaired
          repeat' split <;> simp [PairQuarantineMutationRepaired, NonOpen,
            startClosing, setControl]
        · rw [if_neg hRelease]; rw [if_neg hRelease] at hb'
          by_cases hReopenTok : (C (ring.rightNeighbor e)).ctl.tok = .reopen
          · rw [if_pos hReopenTok] at hb'
            exact (hReopen hb'.symm).elim
          · rw [if_neg hReopenTok]; rw [if_neg hReopenTok] at hb'
            by_cases hNone : (C e).ctl.tok = .none ∧
                (C (ring.rightNeighbor e)).ctl.tok = .none
            · rw [if_pos hNone] at hb'
              unfold ordinaryStageRepaired
              rw [if_pos hNone]
              by_cases hSealed : (C e).ctl.mark = .sealed ∧
                  (C (ring.rightNeighbor e)).ctl.mark = .sealed
              · rw [if_pos hSealed]
                unfold sealedStage
                repeat' split <;> simp [PairQuarantineMutationRepaired,
                  NonOpen, setControl, install, hSealed.1, hSealed.2]
              · rw [if_neg hSealed] at hb'; rw [if_neg hSealed]
                by_cases hOpenCtl : (C e).ctl.mark = .open ∧
                    (C (ring.rightNeighbor e)).ctl.mark = .open
                · rw [if_pos hOpenCtl] at hb'; rw [if_pos hOpenCtl]
                  by_cases hHaz : pairHazard
                      (C e).phys (C (ring.rightNeighbor e)).phys
                      (proposal hψ (by decide : 0 < 2) h2
                        (C e) (C (ring.rightNeighbor e))).1
                      (proposal hψ (by decide : 0 < 2) h2
                        (C e) (C (ring.rightNeighbor e))).2 = true
                  · unfold openStage
                    dsimp only
                    rw [if_pos hHaz]
                    split <;> simp [PairQuarantineMutationRepaired, NonOpen,
                      startClosing, setControl]
                  · rw [if_neg hHaz] at hb'
                    exact (hOpen hb'.symm).elim
                · rw [if_neg hOpenCtl]
                  simp [PairQuarantineMutationRepaired, NonOpen,
                    startClosing, setControl]
            · unfold ordinaryStageRepaired
              rw [if_neg hNone]
              exact pairMutation_self _ _

def BranchPreservationObligationRepaired
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (b : Branch) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    AdmittedPostBirthGeometry hψ ring C → CoherentPrefixes ring C →
    branchAt hψ h2 ring C e = b →
    CoherentPrefixes ring (stepRepaired hψ h2 ring C e)

private theorem safeBranchPreservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (b : Branch)
    (hReopen : b ≠ .reopen) (hOpen : b ≠ .openNoHazard) :
    BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring b := by
  intro C e _hGeom hC hb
  apply coherentPrefixes_of_quarantineMutation ring
  · exact pairMutation_step hψ h2 ring C e
      (pairMutation_safe hψ h2 ring C e b hb hReopen hOpen)
  · exact hC

theorem sweep_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .sweep :=
  safeBranchPreservation hψ h2 ring .sweep (by decide) (by decide)

theorem release_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .release :=
  safeBranchPreservation hψ h2 ring .release (by decide) (by decide)

theorem mixed_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .mixed :=
  safeBranchPreservation hψ h2 ring .mixed (by decide) (by decide)

structure PreservationObligationsRepaired
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop where
  seek : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .seek
  sweep : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .sweep
  commit : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .commit
  release : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .release
  reopen : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .reopen
  sealed : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .sealed
  openHazard : BranchPreservationObligationRepaired
    (κ := κ) (τ := τ) hψ h2 ring .openHazard
  openNoHazard : BranchPreservationObligationRepaired
    (κ := κ) (τ := τ) hψ h2 ring .openNoHazard
  mixed : BranchPreservationObligationRepaired (κ := κ) (τ := τ) hψ h2 ring .mixed

theorem preservationObligations_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hReopen : BranchPreservationObligationRepaired
      (κ := κ) (τ := τ) hψ h2 ring .reopen)
    (hOpen : BranchPreservationObligationRepaired
      (κ := κ) (τ := τ) hψ h2 ring .openNoHazard) :
    PreservationObligationsRepaired (κ := κ) (τ := τ) hψ h2 ring where
  seek := safeBranchPreservation hψ h2 ring .seek (by decide) (by decide)
  sweep := sweep_preservation hψ h2 ring
  commit := safeBranchPreservation hψ h2 ring .commit (by decide) (by decide)
  release := release_preservation hψ h2 ring
  reopen := hReopen
  sealed := safeBranchPreservation hψ h2 ring .sealed (by decide) (by decide)
  openHazard := safeBranchPreservation hψ h2 ring .openHazard (by decide) (by decide)
  openNoHazard := hOpen
  mixed := mixed_preservation hψ h2 ring

private theorem successor_false_of_terminal_left
    (l r : Cell ψ κ τ)
    (hterm : (raw l).label.val + 1 = ψ) : successorB l r = false := by
  unfold successorB
  rw [hterm]
  simp [Nat.ne_of_lt (raw r).label.isLt]

theorem plateauA_malformed_terminal_sweep_not_identity
    (l r : Cell ψ κ τ)
    (hterm : (raw l).label.val + 1 = ψ)
    (htok : l.ctl.tok = .sweep) :
    sweepStageRepaired l r ≠ (l, r) := by
  have hs := successor_false_of_terminal_left l r hterm
  intro h
  have ht := congrArg (fun q : Cell ψ κ τ × Cell ψ κ τ => q.1.ctl.tok) h
  simp [sweepStageRepaired, hs, startClosing, setControl, htok] at ht

theorem plateauB_tokenfree_mixed_not_identity
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hln : l.ctl.tok = .none) (hrn : r.ctl.tok = .none)
    (hSealed : ¬(l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed))
    (hOpen : ¬(l.ctl.mark = .open ∧ r.ctl.mark = .open)) :
    ordinaryStageRepaired hψ hw hle l r ≠ (l, r) := by
  intro h
  have ht := congrArg (fun q : Cell ψ κ τ × Cell ψ κ τ => q.2.ctl.tok) h
  simp [ordinaryStageRepaired, hln, hrn, hSealed, hOpen,
    startClosing, setControl] at ht

theorem malformed_release_not_identity
    (l r : Cell ψ κ τ)
    (hs : successorB l r = false)
    (htok : l.ctl.tok = .release) :
    releaseStageRepaired l r ≠ (l, r) := by
  intro h
  have ht := congrArg (fun q : Cell ψ κ τ × Cell ψ κ τ => q.1.ctl.tok) h
  simp [releaseStageRepaired, hs, startClosing, setControl, htok] at ht

end ZZShadowR2CoherenceRepaired
