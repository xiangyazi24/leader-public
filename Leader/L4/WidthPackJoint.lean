import Leader.L4.WidthPackedBridge
import Leader.L4.WidthCacheAllSites

namespace L4.WidthPackJoint
open AllSizeProtocol PhysicalCustody WidthPackedBridge BStarLongFixedRouting
open BStarH6Ordinal BStarH6WordChart ShortResetChart ShortLayerGeometry WidthOrdinalSpan
open WidthCacheAllSites

variable {n : Nat}

def Header (h : Fin n → Bool) := {q : Fin n // h q = true}

def SiteInOwnerWord (h : Fin n → Bool) (q : Header h) (i : Fin n) : Prop :=
  ∃ d j, Gap h q.val d ∧ j < d ∧ nextAt q.val j = i

theorem ordinal_of_gap {h : Fin n → Bool} (hh : ∃ i, h i = true)
    (q : Header h) {d j : Nat} (g : Gap h q.val d) (J : j < d) :
    ordinal h hh (nextAt q.val j) = j := by
  induction j with
  | zero => exact (ordinal_zero h hh q.val).mpr q.property
  | succ j ih =>
    exact (ordinal_body h hh (nextAt q.val j)
      (g.interior (j+1) (by omega) J)).trans (congrArg (·+1) (ih (by omega)))

/-- A genuine cyclic gap partition gives every site its unique header and
unique offset, including words crossing the seam and singleton-header rings. -/
theorem site_word_coordinate {h : Fin n → Bool} (hh : ∃ i, h i = true)
    (gaps : ∀ q : Header h, ∃ d, Gap h q.val d) (i : Fin n) :
    (∃ d, Gap h (back i (ordinal h hh i)) d ∧ ordinal h hh i < d ∧
      nextAt (back i (ordinal h hh i)) (ordinal h hh i) = i) ∧
    ∀ (q : Header h) (d j : Nat), Gap h q.val d → j < d → nextAt q.val j = i →
      q.val = back i (ordinal h hh i) ∧ j = ordinal h hh i := by
  let k := ordinal h hh i
  have H := (ordinal_spec h hh i).2
  let q : Header h := ⟨back i k, H.1⟩
  obtain ⟨d, G⟩ := gaps q
  have next : nextAt q.val k = i := nextAt_back i k
  have K : k < d := by
    apply Nat.lt_of_not_ge
    intro N
    have A : k = d + (k-d) := by omega
    have E := back_nextAt_add q.val d (k-d)
    rw [← A, next] at E
    have F := H.2 (k-d) (by have := G.positive; omega)
    rw [E, G.atEnd] at F
    contradiction
  refine ⟨⟨d, G, K, next⟩, ?_⟩
  intro a b j g J E
  have O := ordinal_of_gap hh a g J
  rw [E] at O
  have B := back_nextAt_add a.val 0 j
  simp only [Nat.zero_add] at B
  rw [E, ← O] at B
  exact ⟨B.symm, O.symm⟩

theorem site_word_cover {h : Fin n → Bool} (hh : ∃ i, h i = true)
    (gaps : ∀ q : Header h, ∃ d, Gap h q.val d) (i : Fin n) :
    ∃ q : Header h, SiteInOwnerWord h q i := by
  obtain ⟨d,G,J,E⟩ := (site_word_coordinate hh gaps i).1
  exact ⟨⟨_, (ordinal_spec h hh i).2.1⟩, d, _, G, J, E⟩

def Qwidth {s : Nat} (P6 : Raw s n → Prop) (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (OwnerGood : Header h → Raw s n → Prop) (y : Raw s n) : Prop :=
  P6 y ∧ WidthCorrect h hh P6 y ∧ ∀ q, OwnerGood q y

def OwnerWordFlagsCorrect {s : Nat} (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (q : Header h) (y : Raw s n) : Prop :=
  ∀ i, SiteInOwnerWord h q i →
    (longGeometry (rows s) (y i)).inside = decide (ordinal h hh i < radWidth s) ∧
    (longGeometry (rows s) (y i)).last = decide (ordinal h hh i + 1 = radWidth s)

theorem settled_owner_flags {s : Nat} (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (y : Raw s n) (mask : oldH6 (rows s) y = h) (spacing : CertifiedSpacing y)
    (flags : ∀ q, OwnerWordFlagsCorrect h hh q y) :
    FlagsCorrect y (mask.symm ▸ hh) ∧
    ∀ i, Layout (rows s) y i =
      (h i, decide (ordinal h hh i < radWidth s), decide (ordinal h hh i + 1 = radWidth s)) := by
  have gaps : ∀ q : Header h, ∃ d, Gap h q.val d := by
    intro q
    obtain ⟨d,_,_,G⟩ := spacing q.val (mask.symm ▸ q.property)
    exact ⟨d, mask ▸ G⟩
  have all (i : Fin n) :
      (longGeometry (rows s) (y i)).inside = decide (ordinal h hh i < radWidth s) ∧
      (longGeometry (rows s) (y i)).last = decide (ordinal h hh i + 1 = radWidth s) := by
    obtain ⟨q,Q⟩ := site_word_cover hh gaps i
    exact flags q i Q
  have ord (a b : Fin n → Bool) (E : a=b) (aa : ∃ j,a j=true) (bb : ∃ j,b j=true)
      (i : Fin n) : ordinal a aa i=ordinal b bb i := by subst b; rfl
  constructor
  · intro i
    unfold oldOrdinal
    rw [ord _ _ mask _ hh i]
    exact all i
  · intro i
    have M : oldH6 (rows s) y i = h i := congrFun mask i
    change (oldH6 (rows s) y i, (longGeometry (rows s) (y i)).inside,
      (longGeometry (rows s) (y i)).last) = _
    rw [M, (all i).1, (all i).2]

/-- Conditional W17 assembly only. The owner raw closure and flag safety
are supplied by item 16, not inferred from a historical receipt. -/
theorem packed_of_width_joint {s : Nat} (hs : 6 ≤ s) (N : 1 < n)
    (P6 : Raw s n → Prop) (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (lower_closed : ∀ y e, P6 y → P6 (rawNext s y e))
    (mask : ∀ y, P6 y → ∀ i, oldH6 (rows s) y i = h i)
    (spacing : ∀ y, P6 y → CertifiedSpacing y)
    (OwnerGood : Header h → Raw s n → Prop)
    (owner_closed : ∀ q y e, OwnerGood q y → OwnerGood q (rawNext s y e))
    (owner_flags : ∀ q y, OwnerGood q y → OwnerWordFlagsCorrect h hh q y)
    (z : Raw s n) (Z : Qwidth P6 h hh OwnerGood z) :
    Nonempty (PackedFiber z) := by
  have cache := (width_raw N h hh P6 lower_closed mask z Z.1).1
  have closed (y : Raw s n) (e : Fin n) (Y : Qwidth P6 h hh OwnerGood y) :
      Qwidth P6 h hh OwnerGood (rawNext s y e) :=
    ⟨lower_closed y e Y.1, cache y e Y.2.1, fun q => owner_closed q y e (Y.2.2 q)⟩
  have data (y : Raw s n) (Y : Qwidth P6 h hh OwnerGood y) :=
    settled_owner_flags h hh y (funext (mask y Y.1)) (spacing y Y.1)
      (fun q => owner_flags q y (Y.2.2 q))
  exact packed_fiber_from_closed_width hs z _ Z closed
    (fun y Y i => ((data z Z).2 i).trans ((data y Y).2 i).symm)
    _ (spacing z Z.1) (data z Z).1

end L4.WidthPackJoint
