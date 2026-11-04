import Leader.Wu.Coherence.ReachableOverlapPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31FootprintBand

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceV31Closure
open R2CoherenceV31ReachablePlus2

variable {n ψ κ τ : Nat}

private theorem modL_band (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem modR_band (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem back_zero_band
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.back ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem fwd_zero_band
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]

private theorem fwd_succ_band
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.fwd ring i (d + 1) =
      ring.rightNeighbor (R2Coherence.fwd ring i d) := by
  apply Fin.ext
  unfold R2Coherence.fwd DirectedRing.rightNeighbor
  dsimp only
  rw [modL_band]
  congr 1

private theorem back_fwd_cancel_band
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.back ring (R2Coherence.fwd ring i d) d = i := by
  induction d with
  | zero =>
      rw [fwd_zero_band, back_zero_band]
  | succ d ih =>
      rw [fwd_succ_band ring i d]
      rw [R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach]
      exact ih

private theorem fwd_back_cancel_band
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.fwd ring (R2Coherence.back ring i d) d = i := by
  let a := d % n
  have ha : a < n := by
    dsimp [a]
    exact Nat.mod_lt _ ring.hn
  have hle : a ≤ i.val + n := by omega
  apply Fin.ext
  unfold R2Coherence.fwd R2Coherence.back
  dsimp only
  change ((((i.val + n - a) % n) + d) % n) = i.val
  calc
    ((((i.val + n - a) % n) + d) % n) =
        (i.val + n - a + d) % n :=
      modL_band (i.val + n - a) d n
    _ = (i.val + n - a + (d % n)) % n := by
      exact (modR_band (i.val + n - a) d n).symm
    _ = (i.val + n - a + a) % n := by
      rw [show d % n = a by rfl]
    _ = (i.val + n) % n := by rw [Nat.sub_add_cancel hle]
    _ = i.val := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
        Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem fwd_add_band
    (ring : DirectedRing n) (i : Fin n) (a b : Nat) :
    R2Coherence.fwd ring (R2Coherence.fwd ring i a) b =
      R2Coherence.fwd ring i (a + b) := by
  apply Fin.ext
  unfold R2Coherence.fwd
  dsimp only
  calc
    (((i.val + a) % n + b) % n) =
        (i.val + a + b) % n := modL_band (i.val + a) b n
    _ = (i.val + (a + b)) % n := by rw [Nat.add_assoc]

private theorem back_fwd_sub_band
    (ring : DirectedRing n) (i : Fin n) (q d : Nat)
    (hd : d ≤ q) :
    R2Coherence.back ring (R2Coherence.fwd ring i q) d =
      R2Coherence.fwd ring i (q - d) := by
  calc
    R2Coherence.back ring (R2Coherence.fwd ring i q) d =
        R2Coherence.back ring
          (R2Coherence.fwd ring i ((q - d) + d)) d := by
            rw [Nat.sub_add_cancel hd]
    _ = R2Coherence.back ring
        (R2Coherence.fwd ring
          (R2Coherence.fwd ring i (q - d)) d) d := by
            rw [fwd_add_band]
    _ = R2Coherence.fwd ring i (q - d) :=
      back_fwd_cancel_band ring
        (R2Coherence.fwd ring i (q - d)) d

private theorem fwd_fwd_sub_band
    (ring : DirectedRing n) (i : Fin n) (a b : Nat)
    (hab : a ≤ b) :
    R2Coherence.fwd ring (R2Coherence.fwd ring i a) (b - a) =
      R2Coherence.fwd ring i b := by
  calc
    R2Coherence.fwd ring (R2Coherence.fwd ring i a) (b - a) =
        R2Coherence.fwd ring i (a + (b - a)) :=
      fwd_add_band ring i a (b - a)
    _ = R2Coherence.fwd ring i b := by
      have h : a + (b - a) = b := by omega
      rw [h]

private theorem groupPos_label_self_band
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val)
      (raw (C i)).label.val = i
  exact fwd_back_cancel_band ring i (raw (C i)).label.val

private theorem groupPos_rightNeighbor_band
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat) :
    ring.rightNeighbor (R2Coherence.groupPos ring C i k) =
      R2Coherence.groupPos ring C i (k + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor R2Coherence.groupPos R2Coherence.fwd
  dsimp only
  rw [modL_band]
  congr 1

private theorem successor_labels_band
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem election_edge_label_cases_band
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C) (p : Fin n) :
    (raw (C (ring.rightNeighbor p))).label.val = 0 ∨
      (raw (C (ring.rightNeighbor p))).label.val =
        (raw (C p)).label.val + 1 := by
  by_cases hz : (raw (C (ring.rightNeighbor p))).label.val = 0
  · exact Or.inl hz
  · right
    have hRootFalse : atRootB (C (ring.rightNeighbor p)) = false := by
      simp [atRootB, hz]
    have hEdge := hElection p
    unfold passiveEdgeOKV3 at hEdge
    rw [hRootFalse] at hEdge
    have hSucc :
        successorB (C p) (C (ring.rightNeighbor p)) = true := by
      simpa using hEdge
    exact successor_labels_band _ _ hSucc

private theorem groupPos_zero_label_zero_band
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C) (i : Fin n) :
    (raw (C
      (R2Coherence.groupPos ring (eraseCfgV3 C) i 0))).label.val = 0 := by
  let L := (raw (C i)).label.val
  let a0 :=
    (raw (C
      (R2Coherence.groupPos ring (eraseCfgV3 C) i 0))).label.val
  have hSelf :
      R2Coherence.groupPos ring (eraseCfgV3 C) i L = i := by
    simpa [L] using groupPos_label_self_band ring C i
  have hInv : ∀ t : Nat, t ≤ L →
      (raw (C
        (R2Coherence.groupPos ring (eraseCfgV3 C) i t))).label.val =
          a0 + t ∨
        (raw (C
          (R2Coherence.groupPos ring (eraseCfgV3 C) i t))).label.val < t := by
    intro t
    induction t with
    | zero =>
        intro _
        left
        simp [a0]
    | succ t ih =>
        intro ht
        have hPrev := ih (by omega)
        have hEdge := election_edge_label_cases_band
          ring C hElection
          (R2Coherence.groupPos ring (eraseCfgV3 C) i t)
        have hMove := groupPos_rightNeighbor_band
          ring (eraseCfgV3 C) i t
        rcases hEdge with hz | hs
        · right
          rw [hMove] at hz
          rw [hz]
          omega
        · rw [hMove] at hs
          rcases hPrev with hlin | hsmall
          · left
            omega
          · right
            omega
  have hFinal := hInv L (Nat.le_refl L)
  rw [hSelf] at hFinal
  rcases hFinal with hlin | hsmall
  · have ha0 : a0 = 0 := by
      dsimp [L] at hlin
      omega
    simpa [a0] using ha0
  · dsimp [L] at hsmall
    omega

private theorem groupPos_label_le_band
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C)
    (i : Fin n) (q : Nat) :
    (raw (C
      (R2Coherence.groupPos ring (eraseCfgV3 C) i q))).label.val ≤ q := by
  induction q with
  | zero =>
      have h0 := groupPos_zero_label_zero_band ring C hElection i
      omega
  | succ q ih =>
      have hEdge := election_edge_label_cases_band
        ring C hElection
        (R2Coherence.groupPos ring (eraseCfgV3 C) i q)
      have hMove := groupPos_rightNeighbor_band
        ring (eraseCfgV3 C) i q
      rcases hEdge with hz | hs
      · rw [hMove] at hz
        rw [hz]
        omega
      · rw [hMove] at hs
        omega

theorem openRFreshFootprintBand_of_root
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner p : Fin n)
    (hElection : ElectionGeometryV31 ring C)
    (_hRoot : atRootB (C owner) = true)
    (hFoot : InOpenRFreshFootprintV31 ring C owner p) :
    (∃ d : Fin ψ, 0 < d.val ∧
      p = R2Coherence.back ring owner d.val) ∨
    (∃ d : Fin ψ,
      p = R2Coherence.fwd ring owner d.val) := by
  rcases hFoot with ⟨j, ko, q, hOwner, k, hPrefix⟩
  let s := R2Coherence.groupStart ring (eraseCfgV3 C) j
  let front :=
    R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hOwnerFwd :
      R2Coherence.fwd ring s ko.val = owner := by
    unfold R2Coherence.groupPos at hOwner
    change R2Coherence.fwd ring s ko.val = owner at hOwner
    exact hOwner
  have hFrontFwd :
      front = R2Coherence.fwd ring s q.val := by
    rfl
  have hLq :
      (raw (C front)).label.val ≤ q.val := by
    simpa [front] using
      (groupPos_label_le_band ring C hElection j q.val)
  let drop := (raw (C front)).label.val - k.val
  have hDropQ : drop ≤ q.val := by
    dsimp [drop]
    exact Nat.le_trans (Nat.sub_le _ _) hLq
  let t := q.val - drop
  have htq : t ≤ q.val := by
    dsimp [t]
    exact Nat.sub_le _ _
  have htψ : t < ψ :=
    Nat.lt_of_le_of_lt htq q.isLt
  have hPrefixBack :
      R2Coherence.back ring front drop = p := by
    unfold R2Coherence.prefixPos at hPrefix
    change R2Coherence.back ring front drop = p at hPrefix
    exact hPrefix
  have hpFwd :
      p = R2Coherence.fwd ring s t := by
    calc
      p = R2Coherence.back ring front drop := hPrefixBack.symm
      _ = R2Coherence.back ring
          (R2Coherence.fwd ring s q.val) drop := by
        rw [hFrontFwd]
      _ = R2Coherence.fwd ring s (q.val - drop) :=
        back_fwd_sub_band ring s q.val drop hDropQ
      _ = R2Coherence.fwd ring s t := by rfl
  by_cases hBefore : t < ko.val
  · let d : Fin ψ := ⟨ko.val - t, by omega⟩
    refine Or.inl ⟨d, ?_, ?_⟩
    · dsimp [d]
      omega
    · have hBack :
          R2Coherence.back ring owner d.val =
            R2Coherence.fwd ring s t := by
        calc
          R2Coherence.back ring owner d.val =
              R2Coherence.back ring
                (R2Coherence.fwd ring s ko.val) d.val := by
            rw [hOwnerFwd]
          _ = R2Coherence.fwd ring s (ko.val - d.val) :=
            back_fwd_sub_band ring s ko.val d.val (by
              dsimp [d]
              omega)
          _ = R2Coherence.fwd ring s t := by
            have hEq : ko.val - d.val = t := by
              dsimp [d]
              omega
            rw [hEq]
      exact hpFwd.trans hBack.symm
  · have hko : ko.val ≤ t := by omega
    let d : Fin ψ := ⟨t - ko.val, by omega⟩
    refine Or.inr ⟨d, ?_⟩
    have hGo :
        R2Coherence.fwd ring owner d.val =
          R2Coherence.fwd ring s t := by
      calc
        R2Coherence.fwd ring owner d.val =
            R2Coherence.fwd ring
              (R2Coherence.fwd ring s ko.val) d.val := by
          rw [hOwnerFwd]
        _ = R2Coherence.fwd ring s t := by
          simpa [d] using
            (fwd_fwd_sub_band ring s ko.val t hko)
    exact hpFwd.trans hGo.symm

end R2CoherenceV31FootprintBand
