import Leader.Wu.Coherence.ReachableRootSpacing


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableRootSpacing2


open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31BirthEntrance R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableFreshSeek
open R2CoherenceV31ReachableRootSpacing


variable {n ψ κ τ : Nat}


/-- Exact producer-side theorem missing from the frozen birth handoff.
The upstream B6 ruler is only workspace-local; this is the whole-ring
projection required by the R2 entrance. -/
def BirthLabelProfileV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C0 : BirthCheckPermitRepairLeaf.FC n ψ κ τ)
    (C : FC n ψ κ τ),
    BirthEntranceV31 hψ h2 ring C0 C →
      RootSpacingV31 ring C


/-- The producer label profile closes the global entrance residual. -/
theorem birthRootSpacing_of_birthLabelProfile
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hProfile : BirthLabelProfileV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    BirthRootSpacingV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro Q hBirth
  rcases hBirth.1 with ⟨C0, C, hBC, hEq⟩
  rw [hEq]
  exact (rootSpacing_quarantineInit_iff ring C).2
    (hProfile C0 C hBC)


/-- The local anchoring invariant is genuinely free at quarantine: no cell
carries `.scrubL`, hence no pending openR owner exists. -/
theorem pendingOwnerWindowAnchored_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    PendingOwnerWindowAnchoredV31 ring (quarantineInitV31 C) := by
  intro owner j ko q hPending _
  have hs := hPending.1
  simp [quarantineInitV31, setControl] at hs


private theorem back_zero_rs2
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.back ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]


private theorem pending_successor_groupStart_rs2
    (ring : DirectedRing n) (C : FC n ψ κ τ) (owner : Fin n)
    (hPending : PendingOpenROwnerV31 ring C owner) :
    R2Coherence.groupStart ring (eraseCfgV3 C)
        (ring.rightNeighbor owner) = owner := by
  have h0 : (raw (C owner)).label.val = 0 := by
    simpa [atRootB] using hPending.2.2
  have h1 :
      (raw (C (ring.rightNeighbor owner))).label.val =
        (raw (C owner)).label.val + 1 := by
    simpa [successorB] using hPending.2.1
  unfold R2Coherence.groupStart
  change R2Coherence.back ring (ring.rightNeighbor owner)
      (raw (C (ring.rightNeighbor owner))).label.val = owner
  rw [h1, h0]
  calc
    R2Coherence.back ring (ring.rightNeighbor owner) (0 + 1) =
        R2Coherence.back ring owner 0 := by
      simpa using
        (R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
          ring owner 0)
    _ = owner := back_zero_rs2 ring owner



private theorem modL_rs2 (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem modR_rs2 (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


/-- Pure ring arithmetic: a prefix offset not exceeding the front label is the
same physical site as that offset in the front's computed group. -/
private theorem prefixPos_eq_groupPos_rs2
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat)
    (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k =
      R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by dsimp [a]; exact Nat.mod_lt _ hn
  have hb : b < n := by dsimp [b]; exact Nat.mod_lt _ hn
  have hA : n ≤ A := by dsimp [A]; omega
  have hmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n = (((A - (L % n)) % n + k) % n)
  symm
  by_cases hs : a + b < n
  · have hm : L % n = a + b := hmod.trans (Nat.mod_eq_of_lt hs)
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n := modL_rs2 _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_rs2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have hx : A - (a + b) + b = A - a := by omega
        rw [hx]
  · have hge : n ≤ a + b := by omega
    have hlt : a + b - n < n := by omega
    have hm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hge
        _ = a + b - n := Nat.mod_eq_of_lt hlt
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n := modL_rs2 _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_rs2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have hx : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hx, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]


/-- The weaker local invariant is already sufficient for the FreshSeek
containment; global `PsiWindowLinearV31` is unnecessary. -/
theorem pendingOpenRFootprintInScrubGroup_of_anchored
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hAnchor : PendingOwnerWindowAnchoredV31 ring C) :
    PendingOpenRFootprintInScrubGroupV31 ring C := by
  intro owner p hPending hFoot
  rcases hFoot with ⟨j, ko, q, hOwner, k, hPrefix⟩
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hStartFront :
      R2Coherence.groupStart ring (eraseCfgV3 C) front = owner := by
    simpa [front] using hAnchor owner j ko q hPending hOwner
  have hStartSucc :
      R2Coherence.groupStart ring (eraseCfgV3 C)
        (ring.rightNeighbor owner) = owner :=
    pending_successor_groupStart_rs2 ring C owner hPending
  have hk : k.val ≤ (raw (C front)).label.val :=
    Nat.le_of_lt_succ k.isLt
  have hpg := prefixPos_eq_groupPos_rs2
    ring (eraseCfgV3 C) front k.val hk
  have hFront :
      R2Coherence.groupPos ring (eraseCfgV3 C) front k.val = p := by
    exact hpg.symm.trans (by simpa [front] using hPrefix)
  have hkψ : k.val < ψ := by
    have hl := (raw (C front)).label.isLt
    omega
  let kp : Fin ψ := ⟨k.val, hkψ⟩
  refine ⟨kp, ?_⟩
  change R2Coherence.groupPos ring (eraseCfgV3 C)
      (ring.rightNeighbor owner) k.val = p
  calc
    R2Coherence.groupPos ring (eraseCfgV3 C)
        (ring.rightNeighbor owner) k.val =
      R2Coherence.groupPos ring (eraseCfgV3 C) front k.val := by
        unfold R2Coherence.groupPos
        rw [hStartSucc, hStartFront]
    _ = p := hFront



/-- Exact hole in the installed local preservation theorem: only a post-state
pending owner which did not exist before needs new anchoring.  Source census
reduces this to the terminal RELEASE arm that creates the responder `.scrubL`. -/
def NewPendingOwnerWindowAnchoredStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner j : Fin n) (ko q : Fin ψ),
    PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner →
    ¬ PendingOpenROwnerV31 ring C owner →
    R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e)) j ko.val = owner →
      R2Coherence.groupStart ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val) = owner


private theorem groupPos_eq_labels_rs2
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]


theorem pendingOwnerWindowAnchored_stepV3_of_new
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hNew : NewPendingOwnerWindowAnchoredStepV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hOld : PendingOwnerWindowAnchoredV31 ring C) :
    PendingOwnerWindowAnchoredV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner j ko q hPending hHit
  by_cases hp : PendingOpenROwnerV31 ring C owner
  · have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
    have hko := groupPos_eq_labels_rs2 ring hLab j ko.val
    have hq := groupPos_eq_labels_rs2 ring hLab j q.val
    have hHitC :
        R2Coherence.groupPos ring (eraseCfgV3 C) j ko.val = owner :=
      hko.symm.trans hHit
    have h := hOld owner j ko q hp hHitC
    unfold R2Coherence.groupStart at h ⊢
    rw [hq]
    change R2Coherence.back ring
        (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val)
        (raw (stepV3 hψ h2 ring C e
          (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val))).label.val =
      owner
    change R2Coherence.back ring
        (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val)
        (raw (C
          (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val))).label.val =
      owner at h
    rw [hLab]
    exact h
  · exact hNew C e owner j ko q hPending hp hHit


/-- RELEASE-specialized producer of the new-owner case.  This is the first
unclosed local preservation clause after replacing global root spacing by
pending-owner anchoring. -/
def ReleaseNewPendingOwnerWindowAnchoredV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner j : Fin n) (ko q : Fin ψ),
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
    PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner →
    ¬ PendingOpenROwnerV31 ring C owner →
    R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e)) j ko.val = owner →
      R2Coherence.groupStart ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val) = owner


end R2CoherenceV31ReachableRootSpacing2
