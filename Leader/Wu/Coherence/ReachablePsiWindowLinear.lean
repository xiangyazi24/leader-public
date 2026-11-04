import Leader.Wu.Coherence.ReachableFreshSeekWindow


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableFreshSeek2


open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard
open R2CoherenceV31ReachableFreshSeek


variable {n ψ κ τ : Nat}


/-- Exact arithmetic gap left by ElectionGeometryV31: no second root/reset
occurs inside one ψ-window.  Equivalently, group offset d carries label d. -/
def PsiWindowLinearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (j : Fin n) (d : Fin ψ),
    (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) j d.val))).label.val =
      d.val


private theorem modL_fs2 (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem modR_fs2 (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem back_zero_fs2
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.back ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]


private theorem fwd_succ_fs2
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.fwd ring i (d + 1) =
      ring.rightNeighbor (R2Coherence.fwd ring i d) := by
  apply Fin.ext
  unfold R2Coherence.fwd DirectedRing.rightNeighbor
  dsimp only
  rw [modL_fs2]
  congr 1


private theorem back_fwd_cancel_fs2
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.back ring (R2Coherence.fwd ring i d) d = i := by
  induction d with
  | zero =>
      rw [back_zero_fs2]
      apply Fin.ext
      simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
      rw [fwd_succ_fs2 ring i d]
      rw [R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach]
      exact ih


/-- Under the one missing linearity sentence, every position in a groupPos
window has the same computed group start. -/
theorem groupStart_groupPos_of_psiWindowLinear
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hLin : PsiWindowLinearV31 ring C)
    (j : Fin n) (d : Fin ψ) :
    R2Coherence.groupStart ring (eraseCfgV3 C)
        (R2Coherence.groupPos ring (eraseCfgV3 C) j d.val) =
      R2Coherence.groupStart ring (eraseCfgV3 C) j := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring
      (R2Coherence.groupPos ring (eraseCfgV3 C) j d.val)
      (raw (C
        (R2Coherence.groupPos ring (eraseCfgV3 C) j d.val))).label.val =
    R2Coherence.back ring j (raw (C j)).label.val
  rw [hLin j d]
  change R2Coherence.back ring
      (R2Coherence.fwd ring
        (R2Coherence.groupStart ring (eraseCfgV3 C) j) d.val) d.val =
    R2Coherence.groupStart ring (eraseCfgV3 C) j
  exact back_fwd_cancel_fs2 ring
    (R2Coherence.groupStart ring (eraseCfgV3 C) j) d.val


/-- Generic prefix/group arithmetic copied from the ThreeBranches2 helper. -/
private theorem prefixPos_eq_groupPos_fs2
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
          (A - (L % n) + k) % n := modL_fs2 _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_fs2 (A - (L % n)) k n).symm
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
          (A - (L % n) + k) % n := modL_fs2 _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_fs2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have hx : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hx, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]



private theorem groupStart_pending_successor_fs2
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
    _ = owner := back_zero_fs2 ring owner


/-- Containment itself, modulo exactly the no-internal-reset arithmetic gap. -/
theorem pendingOpenRFootprintInScrubGroup_of_psiWindowLinear
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hLin : PsiWindowLinearV31 ring C) :
    PendingOpenRFootprintInScrubGroupV31 ring C := by
  intro owner p hPending hFoot
  rcases hFoot with ⟨j, ko, q, hOwner, k, hPrefix⟩
  let front :=
    R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hRoot : (raw (C owner)).label.val = 0 := by
    simpa [atRootB] using hPending.2.2
  have hStartOwner :
      R2Coherence.groupStart ring (eraseCfgV3 C) owner = owner := by
    unfold R2Coherence.groupStart
    change R2Coherence.back ring owner
      (raw (C owner)).label.val = owner
    rw [hRoot]
    exact back_zero_fs2 ring owner
  have hStartJ :
      R2Coherence.groupStart ring (eraseCfgV3 C) j = owner := by
    have hs := groupStart_groupPos_of_psiWindowLinear
      ring C hLin j ko
    rw [hOwner, hStartOwner] at hs
    exact hs.symm
  have hStartFront :
      R2Coherence.groupStart ring (eraseCfgV3 C) front = owner := by
    have hs := groupStart_groupPos_of_psiWindowLinear
      ring C hLin j q
    change R2Coherence.groupStart ring (eraseCfgV3 C) front =
      R2Coherence.groupStart ring (eraseCfgV3 C) j at hs
    exact hs.trans hStartJ
  have hStartSucc :
      R2Coherence.groupStart ring (eraseCfgV3 C)
          (ring.rightNeighbor owner) = owner :=
    groupStart_pending_successor_fs2 ring C owner hPending
  have hPrefixFront :
      R2Coherence.prefixPos ring (eraseCfgV3 C) front k.val = p := by
    simpa [front] using hPrefix
  have hk : k.val ≤
      (R2Coherence.raw ((eraseCfgV3 C) front)).label.val := by
    change k.val ≤ (raw (C front)).label.val
    exact Nat.le_of_lt_succ k.isLt
  have hpg := prefixPos_eq_groupPos_fs2
    ring (eraseCfgV3 C) front k.val hk
  have hGroupFront :
      R2Coherence.groupPos ring (eraseCfgV3 C) front k.val = p :=
    hpg.symm.trans hPrefixFront
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
    _ = p := hGroupFront


/-- Reachable form of the single arithmetic gap. -/
def PsiWindowLinearReachableV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
    ElectionGeometryV31 ring C →
      PsiWindowLinearV31 ring C


/-- Therefore FreshSeek's shared residual is discharged as soon as the
reachable no-internal-reset sentence is established. -/
theorem pendingFootprintContainmentReachable_of_psiWindowLinear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hLin : PsiWindowLinearReachableV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PendingFootprintContainmentReachableV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C hTrace hGeom
  exact pendingOpenRFootprintInScrubGroup_of_psiWindowLinear
    ring C (hLin C hTrace hGeom)


/-
STOP: `PsiWindowLinearReachableV31` is the exact remaining arithmetic gap.
ElectionGeometryV31 alone cannot prove it: for n=6, ψ=3, the cyclic label
pattern 0,1,0,1,0,1 satisfies every local election edge, yet the ψ-window
starting at the first root contains a second root at offset 2.  This is not a
"held label" problem inside `stepV3_labels_eq_or_held`; it is that the current
geometry intentionally allows multiple label-zero boundaries less than ψ
physical cells apart.  A stronger reachable spacing/unique-root theorem is
needed to prove `PsiWindowLinearReachableV31`.
-/


end R2CoherenceV31ReachableFreshSeek2
