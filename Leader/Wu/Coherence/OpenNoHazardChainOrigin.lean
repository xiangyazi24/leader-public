import Leader.Wu.Coherence.NewEqualLocal
import Leader.Wu.Coherence.OpenNoHazardFrame

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31OpenNoHazardExt

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard
open R2NewEqualLocal

variable {n ψ κ τ width : Nat}

/-- The missing CHECK-chain provenance companion to
`SanitizedR2NewEqualFreshAtOwnLabelNoMainMutation`.

Left CHECK can create a new equality only at the label-0 base.  A new right
non-root equality can only extend an equality already present on the left
*output* of the same R2 row.  The latter intentionally permits the service in
which CHECK-L first creates the root equality and CHECK-R immediately extends
it. -/
def SanitizedR2NewEqualChainOriginNoMainMutation
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let q := R2.row hψ hw hle
      (sanitizeReadyPhys l) (sanitizeReadyPhys r)
    R2MainCarrierFrame l r q →
      (q.1.base.core.core.state = .equal →
        l.base.core.core.state ≠ .equal →
        q.1.base.core.core.label.val = 0) ∧
      (q.2.base.core.core.state = .equal →
        r.base.core.core.state ≠ .equal →
        q.2.base.core.core.label.val = 0 ∨
          q.1.base.core.core.state = .equal)

private theorem back_rightNeighbor_succ_ext
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.back ring (ring.rightNeighbor i) (d + 1) =
      R2Coherence.back ring i d := by
  apply Fin.ext
  unfold R2Coherence.back DirectedRing.rightNeighbor
  dsimp only
  by_cases hn1 : n = 1
  · subst n
    simp
  · have hn : 0 < n := ring.hn
    have hn2 : 2 ≤ n := by omega
    have hOne : 1 < n := by omega
    have hdlt : d % n < n := Nat.mod_lt _ ring.hn
    have hdmod : (d + 1) % n = (d % n + 1) % n := by
      calc
        (d + 1) % n = (d % n + 1 % n) % n := Nat.add_mod _ _ _
        _ = (d % n + 1) % n := by rw [Nat.mod_eq_of_lt hOne]
    rw [hdmod]
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi]
      by_cases hd : d % n + 1 < n
      · rw [Nat.mod_eq_of_lt hd]
        have hnum :
            i.val + 1 + n - (d % n + 1) =
              i.val + n - d % n := by omega
        rw [hnum]
      · have hdeq : d % n + 1 = n := by omega
        rw [hdeq, Nat.mod_self, Nat.sub_zero]
        have hr : i.val + n - d % n = i.val + 1 := by omega
        rw [hr, Nat.mod_eq_of_lt hi]
        have hl : i.val + 1 + n = n + (i.val + 1) := by omega
        rw [hl, Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_mod, Nat.mod_eq_of_lt hi]
    · have hieq : i.val + 1 = n := by omega
      rw [hieq, Nat.mod_self, Nat.zero_add]
      by_cases hd : d % n + 1 < n
      · rw [Nat.mod_eq_of_lt hd]
        have hvlt : n - (d % n + 1) < n := by omega
        rw [Nat.mod_eq_of_lt hvlt]
        have hr :
            i.val + n - d % n =
              n + (n - (d % n + 1)) := by omega
        rw [hr, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hvlt]
      · have hdeq : d % n + 1 = n := by omega
        rw [hdeq, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
        have hr : i.val + n - d % n = n := by omega
        rw [hr, Nat.mod_self]

private theorem successor_labels_ext
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem groupStart_successor_ext
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
      R2Coherence.groupStart ring (eraseCfgV3 C) e := by
  unfold R2Coherence.groupStart
  change
    R2Coherence.back ring (ring.rightNeighbor e)
        (raw (C (ring.rightNeighbor e))).label.val =
      R2Coherence.back ring e (raw (C e)).label.val
  rw [successor_labels_ext (C e) (C (ring.rightNeighbor e)) hs]
  exact back_rightNeighbor_succ_ext ring e (raw (C e)).label.val

private theorem groupPos_same_successor_ext
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 C)
        (ring.rightNeighbor e) k =
      R2Coherence.groupPos ring (eraseCfgV3 C) e k := by
  unfold R2Coherence.groupPos
  rw [groupStart_successor_ext ring C e hs]

private theorem prefixPos_successor_ext
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (k : Nat) (hk : k ≤ (raw (C e)).label.val) :
    R2Coherence.prefixPos ring (eraseCfgV3 C)
        (ring.rightNeighbor e) k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) e k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring (ring.rightNeighbor e)
        ((raw (C (ring.rightNeighbor e))).label.val - k) =
      R2Coherence.back ring e ((raw (C e)).label.val - k)
  rw [successor_labels_ext (C e) (C (ring.rightNeighbor e)) hs]
  have hsub :
      (raw (C e)).label.val + 1 - k =
        ((raw (C e)).label.val - k) + 1 := by
    omega
  rw [hsub]
  exact back_rightNeighbor_succ_ext ring e
    ((raw (C e)).label.val - k)

private theorem prefixPos_own_ext
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) :
    R2Coherence.prefixPos ring C i
        (R2Coherence.raw (C i)).label.val = i := by
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem prefixDead_successor_ext
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hdead : R2Coherence.PrefixDead ring (eraseCfgV3 C) e) :
    R2Coherence.PrefixDead ring (eraseCfgV3 C) (ring.rightNeighbor e) := by
  rcases hdead with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hp := groupPos_same_successor_ext ring C e hs k.val
  rw [hp]
  exact hk

theorem freshEqualPrefix_successor_ext
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (heqL : (raw (C e)).state = .equal)
    (hLeft :
      R2Coherence.FreshEqualPrefix ring (eraseCfgV3 C) e)
    (hOwn :
      R2Coherence.freshComponent
        (eraseCellV3 (C (ring.rightNeighbor e)))
        (raw (C (ring.rightNeighbor e))).label.val) :
    R2Coherence.FreshEqualPrefix ring (eraseCfgV3 C)
      (ring.rightNeighbor e) := by
  intro _heqR
  rcases hLeft heqL with hdead | hfresh
  · exact Or.inl (prefixDead_successor_ext ring C e hs hdead)
  · right
    intro k
    have hLab := successor_labels_ext
      (C e) (C (ring.rightNeighbor e)) hs
    by_cases htop :
        k.val = (raw (C (ring.rightNeighbor e))).label.val
    · rw [htop]
      have hp := prefixPos_own_ext ring (eraseCfgV3 C) (ring.rightNeighbor e)
      change
        R2Coherence.prefixPos ring (eraseCfgV3 C) (ring.rightNeighbor e)
            (raw (C (ring.rightNeighbor e))).label.val =
          ring.rightNeighbor e at hp
      rw [hp]
      simpa [eraseCfgV3] using hOwn
    · have hkRlt :
          k.val < (raw (C (ring.rightNeighbor e))).label.val + 1 := by
        exact k.isLt
      have hkR :
          k.val ≤ (raw (C (ring.rightNeighbor e))).label.val :=
        Nat.le_of_lt_succ hkRlt
      have hkLtR :
          k.val < (raw (C (ring.rightNeighbor e))).label.val :=
        Nat.lt_of_le_of_ne hkR htop
      rw [hLab] at hkLtR
      have hkL : k.val ≤ (raw (C e)).label.val :=
        Nat.le_of_lt_succ hkLtR
      let kL : Fin ((raw (C e)).label.val + 1) :=
        ⟨k.val, Nat.lt_succ_of_le hkL⟩
      have hp := prefixPos_successor_ext ring C e hs k.val hkL
      rw [hp]
      exact hfresh kL

end R2CoherenceV31OpenNoHazardExt
