import Init.Data.List.OfFn
import Init.Data.List.TakeDrop
import Init.Data.List.Nat.Sum
import Init.Data.List.Count
import Init.Data.List.Pairwise
import Init.Data.List.Perm
import Init.Omega

set_option autoImplicit false

namespace Leader.GapOwnershipArcs

/-!
Leader/Wu/Elimination/GapOwnershipArcs.lean

This is a standalone geometry. `gapPos` is the positional part of
the proposed gap frame, `support` is half-open ownership, and the local `Cell`
and potential formulas follow the interface. `PhysicalBridge` records
the configuration projection, two-site frame property, and potential
identities still needed to connect this model to a protocol. No identification
with the full physical state is asserted here. The companion
`ReadSupportContact` connects this fixed-layout model to the repository's
actual `PerGapOffPay` consumer. Target: Lean 4.33 core.

DECISION: distinguish ownership from reads. Ownership is (left,right]:
positive local indices 1 through d, including the RIGHT endpoint. These sets
partition the sites. For a one-gap full ring, indices 0 and d denote the same
site, which necessarily is owned; exclusion of the left endpoint as a SITE
requires distinct endpoints. No positive number of gaps is silently assumed.

Unrestricted half-open phi_support is FALSE for the stated gapWC. The example
below keeps all owned cells identical but deletes the excluded left leader,
changing the value from 2 to 0. It also satisfies the outside-two-cells law
for the directed pair (5,0); no particular protocol transition is asserted.
Agreement of the left LEADER FLAG, not its whole cell, repairs locality.

Recommended repair: retain half-open ownership for accounting and use the
separate readSupport = ownership union the left endpoint for touches/frame.
Its closed-arc locality is proved below. Do not reuse the disjoint-support
contact lemma for readSupport: an arbitrary pair has the proved four-gap
cover below. `ReadSupportContact.adjacent_pair_contact_count` supplies the
separate sharp bound of two for adjacent pairs when every gap length is at
least two.
For two leaders the closed arcs share BOTH leaders, not exactly one cell.
Dropping the left-deletion test changes the potential and requires new drift
and stopping arguments; no such replacement is asserted here.

The only repository integration contract is PhysicalBridge. Its two value
identities explicitly require the SAME geometric frame on both sides of an
ordinary step. Relabelling, merging, and the >=2 spacing invariant are not
proved protocol properties by this construction. A caller must supply the
contract on the fixed-layout slice where it applies.
-/

def partialSum {m : Nat} (d : Fin m → Nat) (k : Nat) : Nat :=
  ((List.ofFn d).take k).sum

def offset {m : Nat} (d : Fin m → Nat) (g : Fin m) : Nat :=
  partialSum d g.val

theorem take_sum_mono (xs : List Nat) :
    ∀ a b, a ≤ b → (xs.take a).sum ≤ (xs.take b).sum := by
  induction xs with
  | nil =>
    intro a b hab
    simpa only [List.take_nil, List.sum_nil] using Nat.le_refl 0
  | cons v vs ih =>
    intro a b hab
    cases a with
    | zero => exact Nat.zero_le _
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simpa only [List.take_succ_cons, List.sum_cons] using
          Nat.add_le_add_left (ih a b (by omega)) v

theorem partialSum_succ {m : Nat} (d : Fin m → Nat) (g : Fin m) :
    partialSum d (g.val + 1) = partialSum d g.val + d g := by
  have hg : g.val < (List.ofFn d).length := by
    simpa only [List.length_ofFn] using g.isLt
  unfold partialSum
  rw [List.take_succ_eq_append_getElem hg]
  simp only [List.sum_append_nat, List.sum_cons, List.sum_nil,
    Nat.add_zero, List.getElem_ofFn]

theorem partialSum_total {m : Nat} (d : Fin m → Nat) :
    partialSum d m = (List.ofFn d).sum := by
  exact congrArg (fun xs : List Nat => xs.sum)
    (List.take_of_length_le (by
      rw [List.length_ofFn]
      exact Nat.le_refl m))

theorem offset_end_le {m n : Nat} (d : Fin m → Nat)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) : offset d g + d g ≤ n := by
  have h := congrArg (fun xs : List Nat => xs.sum)
    (List.take_append_drop (g.val + 1) (List.ofFn d))
  rw [List.sum_append_nat] at h
  change partialSum d (g.val + 1) +
    ((List.ofFn d).drop (g.val + 1)).sum = (List.ofFn d).sum at h
  rw [partialSum_succ d g, hsum] at h
  change partialSum d g.val + d g ≤ n
  omega

theorem offset_separated {m : Nat} (d : Fin m → Nat) (g h : Fin m)
    (hgh : g.val < h.val) : offset d g + d g ≤ offset d h := by
  have ht := take_sum_mono (List.ofFn d) (g.val + 1) h.val (by omega)
  change partialSum d (g.val + 1) ≤ offset d h at ht
  rw [partialSum_succ d g] at ht
  exact ht

theorem ring_pos {m n : Nat} (d : Fin m → Nat) (hm : 0 < m)
    (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n) : 0 < n := by
  have he := offset_end_le d hsum ⟨0, hm⟩
  have hp := hd ⟨0, hm⟩
  omega

/-- Represent site zero by n, so every site has a coordinate in (0,n]. -/
def lift {n : Nat} (x : Fin n) : Nat := if x.val = 0 then n else x.val

theorem lift_range {n : Nat} (x : Fin n) : 0 < lift x ∧ lift x ≤ n := by
  have hx := x.isLt
  unfold lift
  split <;> omega

theorem lift_mod {n : Nat} (x : Fin n) : lift x % n = x.val := by
  unfold lift
  split
  · rename_i h
    rw [Nat.mod_self]
    exact h.symm
  · exact Nat.mod_eq_of_lt x.isLt

theorem mod_inj_positive {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (han : a ≤ n) (hbn : b ≤ n) (he : a % n = b % n) : a = b := by
  by_cases h₁ : a < n
  · by_cases h₂ : b < n
    · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at he
      exact he
    · have hb' : b = n := by omega
      rw [Nat.mod_eq_of_lt h₁, hb', Nat.mod_self] at he
      omega
  · have ha' : a = n := by omega
    by_cases h₂ : b < n
    · rw [ha', Nat.mod_self, Nat.mod_eq_of_lt h₂] at he
      omega
    · omega

theorem lift_of_mod {n : Nat} (hn : 0 < n) (t : Nat)
    (ht : 0 < t) (htn : t ≤ n) :
    lift (⟨t % n, Nat.mod_lt t hn⟩ : Fin n) = t := by
  have hr := lift_range (⟨t % n, Nat.mod_lt t hn⟩ : Fin n)
  exact mod_inj_positive hr.1 ht hr.2 htn (lift_mod _)

def gapPos {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (g : Fin m) (k : Nat) : Fin n :=
  ⟨(offset d g + k) % n, Nat.mod_lt _ hn⟩

def support {m n : Nat} (d : Fin m → Nat) (g : Fin m) (x : Fin n) : Prop :=
  offset d g < lift x ∧ lift x ≤ offset d g + d g

instance {m n : Nat} (d : Fin m → Nat) (g : Fin m) (x : Fin n) :
    Decidable (support d g x) := by
  unfold support
  infer_instance

theorem interval_cover (xs : List Nat) :
    ∀ t, 0 < t → t ≤ xs.sum →
      ∃ j : Fin xs.length,
        (xs.take j.val).sum < t ∧ t ≤ (xs.take j.val).sum + xs[j.val] := by
  induction xs with
  | nil =>
    intro t ht hs
    simp only [List.sum_nil] at hs
    omega
  | cons v vs ih =>
    intro t ht hs
    simp only [List.sum_cons] at hs
    by_cases hv : t ≤ v
    · refine ⟨⟨0, Nat.zero_lt_succ vs.length⟩, ?_, ?_⟩
      · simpa only [List.take_zero, List.sum_nil] using ht
      · simpa only [List.take_zero, List.sum_nil, List.getElem_cons_zero,
          Nat.zero_add] using hv
    · rcases ih (t - v) (by omega) (by omega) with ⟨j, hj₁, hj₂⟩
      refine ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, ?_, ?_⟩
      · change ((v :: vs).take (j.val + 1)).sum < t
        rw [List.take_succ_cons, List.sum_cons]
        omega
      · change t ≤ ((v :: vs).take (j.val + 1)).sum + (v :: vs)[j.val + 1]
        rw [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
        omega

theorem support_total {m n : Nat} (d : Fin m → Nat)
    (hsum : (List.ofFn d).sum = n) (x : Fin n) : ∃ g, support d g x := by
  have hr := lift_range x
  have ht : lift x ≤ (List.ofFn d).sum := hsum.symm ▸ hr.2
  rcases interval_cover (List.ofFn d) (lift x) hr.1 ht with ⟨j, hj₁, hj₂⟩
  let g : Fin m := ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩
  have hg : g =
      (⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩ : Fin m) := rfl
  refine ⟨g, hj₁, ?_⟩
  rw [hg]
  change lift x ≤ ((List.ofFn d).take j.val).sum +
    d ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩
  simpa only [List.getElem_ofFn] using hj₂

theorem gapPos_lift {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (k : Nat)
    (hk : 1 ≤ k) (hkd : k ≤ d g) : lift (gapPos d hn g k) = offset d g + k := by
  have he := offset_end_le d hsum g
  exact lift_of_mod hn (offset d g + k) (by omega) (by omega)

theorem support_iff_pos {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (x : Fin n) :
    support d g x ↔ ∃ k, 1 ≤ k ∧ k ≤ d g ∧ gapPos d hn g k = x := by
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨lift x - offset d g, by omega, by omega, ?_⟩
    apply Fin.ext
    change (offset d g + (lift x - offset d g)) % n = x.val
    have he : offset d g + (lift x - offset d g) = lift x := by omega
    rw [he]
    exact lift_mod x
  · rintro ⟨k, hk, hkd, rfl⟩
    change offset d g < lift (gapPos d hn g k) ∧
      lift (gapPos d hn g k) ≤ offset d g + d g
    rw [gapPos_lift d hn hsum g k hk hkd]
    omega

theorem support_unique {m n : Nat} (d : Fin m → Nat) (g h : Fin m)
    (x : Fin n) (hg : support d g x) (hh : support d h x) : g = h := by
  rcases hg with ⟨hg₁, hg₂⟩
  rcases hh with ⟨hh₁, hh₂⟩
  apply Fin.ext
  by_cases hlt : g.val < h.val
  · have he := offset_separated d g h hlt
    omega
  · by_cases hgt : h.val < g.val
    · have he := offset_separated d h g hgt
      omega
    · omega

theorem support_disjoint {m n : Nat} (d : Fin m → Nat) (g h : Fin m)
    (x : Fin n) (hne : g ≠ h) (hg : support d g x) : ¬ support d h x :=
  fun hh => hne (support_unique d g h x hg hh)

/-- The unique geometric owner; no choice-dependent ownership remains. -/
noncomputable def owner {m n : Nat} (d : Fin m → Nat)
    (hsum : (List.ofFn d).sum = n) (x : Fin n) : Fin m :=
  Classical.choose (support_total d hsum x)

theorem owner_support {m n : Nat} (d : Fin m → Nat)
    (hsum : (List.ofFn d).sum = n) (x : Fin n) : support d (owner d hsum x) x :=
  Classical.choose_spec (support_total d hsum x)

theorem support_iff_owner {m n : Nat} (d : Fin m → Nat)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (x : Fin n) :
    support d g x ↔ g = owner d hsum x := by
  constructor
  · intro h
    exact support_unique d g _ x h (owner_support d hsum x)
  · intro h
    rw [h]
    exact owner_support d hsum x

theorem ownership_touches_two {m n : Nat} (d : Fin m → Nat)
    (hsum : (List.ofFn d).sum = n) (l r : Fin n) :
    ∃ a b : Fin m, ∀ g, support d g l ∨ support d g r → g = a ∨ g = b := by
  refine ⟨owner d hsum l, owner d hsum r, ?_⟩
  intro g h
  exact h.imp (support_iff_owner d hsum g l).mp (support_iff_owner d hsum g r).mp

def cyclicSucc {m : Nat} (g : Fin m) : Fin m :=
  if h : g.val + 1 < m then ⟨g.val + 1, h⟩
  else ⟨0, by have hg := g.isLt; omega⟩

theorem gapPos_shared {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) :
    gapPos d hn g (d g) = gapPos d hn (cyclicSucc g) 0 := by
  apply Fin.ext
  change (offset d g + d g) % n = (offset d (cyclicSucc g) + 0) % n
  by_cases h : g.val + 1 < m
  · have hv : (cyclicSucc g).val = g.val + 1 := by
      simp only [cyclicSucc, dif_pos h]
    have ho : offset d (cyclicSucc g) = offset d g + d g :=
      (congrArg (partialSum d) hv).trans (partialSum_succ d g)
    rw [ho, Nat.add_zero]
  · have hg := g.isLt
    have hm : g.val + 1 = m := by omega
    have hv : (cyclicSucc g).val = 0 := by
      simp only [cyclicSucc, dif_neg h]
    have ho : offset d (cyclicSucc g) = 0 := congrArg (partialSum d) hv
    have he : offset d g + d g = n := by
      calc
        offset d g + d g = partialSum d (g.val + 1) := (partialSum_succ d g).symm
        _ = partialSum d m := congrArg (partialSum d) hm
        _ = n := (partialSum_total d).trans hsum
    rw [he, ho, Nat.add_zero, Nat.mod_self, Nat.zero_mod]

def ownedSites {m n : Nat} (d : Fin m → Nat) (hn : 0 < n) (g : Fin m) :
    List (Fin n) := List.ofFn (fun j : Fin (d g) => gapPos d hn g (j.val + 1))

theorem ofFn_nodup {α : Type} {r : Nat} (f : Fin r → α)
    (hf : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction r with
  | zero =>
    rw [List.ofFn_zero]
    exact List.nodup_nil
  | succ r ih =>
    rw [List.ofFn_succ]
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_ofFn.mp hm with ⟨i, hi⟩
      have hv := congrArg Fin.val (hf i.succ 0 hi)
      change i.val + 1 = 0 at hv
      omega
    · apply ih
      intro i j he
      have hv := congrArg Fin.val (hf i.succ j.succ he)
      apply Fin.ext
      change i.val + 1 = j.val + 1 at hv
      omega

theorem mem_ownedSites {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (x : Fin n) :
    x ∈ ownedSites d hn g ↔ support d g x := by
  constructor
  · intro hx
    rcases List.mem_ofFn.mp hx with ⟨j, hj⟩
    have hb := j.isLt
    exact (support_iff_pos d hn hsum g x).mpr ⟨j.val + 1, by omega, by omega, hj⟩
  · intro hx
    rcases (support_iff_pos d hn hsum g x).mp hx with ⟨k, hk, hkd, hp⟩
    let j : Fin (d g) := ⟨k - 1, by omega⟩
    apply List.mem_ofFn.mpr
    refine ⟨j, ?_⟩
    have hj : j.val + 1 = k := by dsimp [j]; omega
    change gapPos d hn g (j.val + 1) = x
    rw [hj]
    exact hp

theorem ownedSites_nodup {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) : (ownedSites d hn g).Nodup := by
  apply ofFn_nodup
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg lift he
  rw [gapPos_lift d hn hsum g (i.val + 1) (by omega) (by omega),
      gapPos_lift d hn hsum g (j.val + 1) (by omega) (by omega)] at hv
  apply Fin.ext
  omega

/-- Cardinality counts all actual ring sites, not just local index witnesses. -/
theorem support_card {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) :
    (List.ofFn (fun x : Fin n => x)).countP (fun x => decide (support d g x)) = d g := by
  let allSites := List.ofFn (fun x : Fin n => x)
  let p : Fin n → Bool := fun x => decide (support d g x)
  have hall : allSites.Nodup := ofFn_nodup (fun x : Fin n => x) (fun _ _ h => h)
  have hfilter : (allSites.filter p).Nodup :=
    List.Nodup.sublist List.filter_sublist hall
  have hp : List.Perm (allSites.filter p) (ownedSites d hn g) := by
    apply (List.perm_ext_iff_of_nodup hfilter (ownedSites_nodup d hn hsum g)).mpr
    intro x
    constructor
    · intro hx
      have hs : support d g x := by
        simpa only [p, decide_eq_true_eq] using (List.mem_filter.mp hx).2
      exact (mem_ownedSites d hn hsum g x).mpr hs
    · intro hx
      have hs := (mem_ownedSites d hn hsum g x).mp hx
      refine List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨x, rfl⟩, ?_⟩
      simpa only [p, decide_eq_true_eq] using hs
  calc
    allSites.countP p = (allSites.filter p).length := List.countP_eq_length_filter
    _ = (ownedSites d hn g).length := hp.length_eq
    _ = d g := List.length_ofFn

def readSupport {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (g : Fin m) (x : Fin n) : Prop := support d g x ∨ x = gapPos d hn g 0

instance {m n : Nat} (d : Fin m → Nat) (hn : 0 < n) (g : Fin m) (x : Fin n) :
    Decidable (readSupport d hn g x) := by
  unfold readSupport
  infer_instance

theorem readSupport_iff_pos {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (x : Fin n) :
    readSupport d hn g x ↔ ∃ k, k ≤ d g ∧ gapPos d hn g k = x := by
  constructor
  · intro h
    rcases h with h | h
    · rcases (support_iff_pos d hn hsum g x).mp h with ⟨k, hk, hkd, hp⟩
      exact ⟨k, hkd, hp⟩
    · exact ⟨0, Nat.zero_le _, h.symm⟩
  · rintro ⟨k, hkd, hp⟩
    by_cases hk : k = 0
    · right
      simpa only [hk] using hp.symm
    · left
      exact (support_iff_pos d hn hsum g x).mpr ⟨k, by omega, hkd, hp⟩

theorem left_endpoint_injective {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n) {g h : Fin m}
    (he : gapPos d hn g 0 = gapPos d hn h 0) : g = h := by
  have eg := offset_end_le d hsum g
  have eh := offset_end_le d hsum h
  have dg := hd g
  have dh := hd h
  have bg : offset d g < n := by omega
  have bh : offset d h < n := by omega
  have hv := congrArg Fin.val he
  change (offset d g + 0) % n = (offset d h + 0) % n at hv
  simp only [Nat.add_zero, Nat.mod_eq_of_lt bg, Nat.mod_eq_of_lt bh] at hv
  apply Fin.ext
  by_cases hl : g.val < h.val
  · have hs := offset_separated d g h hl
    omega
  · by_cases hr : h.val < g.val
    · have hs := offset_separated d h g hr
      omega
    · omega

theorem readSupport_cover {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n) (x : Fin n) :
    ∃ a b : Fin m, ∀ g, readSupport d hn g x → g = a ∨ g = b := by
  rcases support_total d hsum x with ⟨a, ha⟩
  by_cases hex : ∃ b : Fin m, x = gapPos d hn b 0
  · rcases hex with ⟨b, hb⟩
    refine ⟨a, b, ?_⟩
    intro g hg
    rcases hg with hg | hg
    · exact Or.inl (support_unique d g a x hg ha)
    · exact Or.inr (left_endpoint_injective d hn hd hsum (hg.symm.trans hb))
  · refine ⟨a, a, ?_⟩
    intro g hg
    rcases hg with hg | hg
    · exact Or.inl (support_unique d g a x hg ha)
    · exact False.elim (hex ⟨g, hg⟩)

theorem read_touches_four {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hd : ∀ g, 2 ≤ d g) (hsum : (List.ofFn d).sum = n) (l r : Fin n) :
    ∃ a b c q : Fin m, ∀ g, readSupport d hn g l ∨ readSupport d hn g r →
      g = a ∨ g = b ∨ g = c ∨ g = q := by
  rcases readSupport_cover d hn hd hsum l with ⟨a, b, hab⟩
  rcases readSupport_cover d hn hd hsum r with ⟨c, q, hcq⟩
  refine ⟨a, b, c, q, ?_⟩
  intro g hg
  rcases hg with hl | hr
  · rcases hab g hl with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hcq g hr))

structure Cell where
  leader : Bool
  bullet : Nat
  signal_B : Nat
  deriving DecidableEq

def top (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => if p (k + 1) then k + 1 else top p k

theorem top_congr (p q : Nat → Bool) :
    ∀ t, (∀ k, 1 ≤ k → k ≤ t → p k = q k) → top p t = top q t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
    intro h
    have ht := h (t + 1) (by omega) (Nat.le_refl _)
    have hr := ih (fun k hk hkt => h k hk (by omega))
    simp only [top, ht, hr]

def bulletTop {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) : Nat :=
  top (fun k => decide ((C (pos k)).bullet ≠ 0)) dd

def signalTop {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) : Nat :=
  top (fun k => decide ((C (pos k)).signal_B = 1)) dd

def CleanReady {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) : Prop :=
  (C (pos dd)).signal_B = 1 ∧ ∀ j : Fin dd, (C (pos (j.val + 1))).bullet = 0

def EndpointDeleted {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) : Prop :=
  (C (pos 0)).leader = false ∨ (C (pos dd)).leader = false

def GapDoneC {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) : Prop :=
  CleanReady dd pos C ∨ EndpointDeleted dd pos C

instance {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) :
    Decidable (CleanReady dd pos C) := by
  unfold CleanReady
  infer_instance

instance {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) :
    Decidable (GapDoneC dd pos C) := by
  unfold GapDoneC EndpointDeleted
  infer_instance

def gapWC {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Fin n → Cell) : Nat :=
  if GapDoneC dd pos C then 0
  else if bulletTop dd pos C = 0 then dd - signalTop dd pos C
  else dd + bulletTop dd pos C

/-- The excluded endpoint contributes only its leader flag to this formula. -/
theorem gapWC_congr {n : Nat} (dd : Nat) (pos : Nat → Fin n) (hdd : 1 ≤ dd)
    (C D : Fin n → Cell)
    (hown : ∀ k, 1 ≤ k → k ≤ dd → C (pos k) = D (pos k))
    (hleft : (C (pos 0)).leader = (D (pos 0)).leader) :
    gapWC dd pos C = gapWC dd pos D := by
  have hr := hown dd hdd (Nat.le_refl _)
  have hi : ∀ j : Fin dd, C (pos (j.val + 1)) = D (pos (j.val + 1)) := by
    intro j
    have hj := j.isLt
    exact hown _ (by omega) (by omega)
  have hc : CleanReady dd pos C = CleanReady dd pos D := by
    simp only [CleanReady, hr, hi]
  have he : EndpointDeleted dd pos C = EndpointDeleted dd pos D := by
    simp only [EndpointDeleted, hleft, hr]
  have hd : GapDoneC dd pos C = GapDoneC dd pos D := by
    unfold GapDoneC
    rw [hc, he]
  have hb : bulletTop dd pos C = bulletTop dd pos D := by
    unfold bulletTop
    apply top_congr
    intro k hk hkd
    rw [hown k hk hkd]
  have hs : signalTop dd pos C = signalTop dd pos D := by
    unfold signalTop
    apply top_congr
    intro k hk hkd
    rw [hown k hk hkd]
  simp only [gapWC, hd, hb, hs]

theorem gapWC_owned_plus_left {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (hdd : 1 ≤ d g)
    (C D : Fin n → Cell) (hown : ∀ x, support d g x → C x = D x)
    (hleft : (C (gapPos d hn g 0)).leader = (D (gapPos d hn g 0)).leader) :
    gapWC (d g) (gapPos d hn g) C = gapWC (d g) (gapPos d hn g) D := by
  apply gapWC_congr (d g) (gapPos d hn g) hdd C D
  · intro k hk hkd
    exact hown _ ((support_iff_pos d hn hsum g _).mpr ⟨k, hk, hkd, rfl⟩)
  · exact hleft

theorem gapWC_read_support {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (hsum : (List.ofFn d).sum = n) (g : Fin m) (hdd : 1 ≤ d g)
    (C D : Fin n → Cell) (h : ∀ x, readSupport d hn g x → C x = D x) :
    gapWC (d g) (gapPos d hn g) C = gapWC (d g) (gapPos d hn g) D := by
  apply gapWC_owned_plus_left d hn hsum g hdd C D
  · exact fun x hx => h x (Or.inl hx)
  · exact congrArg Cell.leader (h _ (Or.inr rfl))

def demoLengths (_ : Fin 3) : Nat := 2

def demoPos : Nat → Fin 6 := gapPos demoLengths (by decide) 0

def demoBefore (x : Fin 6) : Cell :=
  ⟨decide (x.val = 0 ∨ x.val = 2 ∨ x.val = 4), 0, 0⟩

def demoAfter (x : Fin 6) : Cell :=
  ⟨decide (x.val = 2 ∨ x.val = 4), 0, 0⟩

theorem demo_geometry :
    (∀ g, 2 ≤ demoLengths g) ∧ (List.ofFn demoLengths).sum = 6 := by decide

theorem demo_agree : ∀ x : Fin 6,
    support demoLengths (0 : Fin 3) x → demoBefore x = demoAfter x := by decide

theorem demo_values : gapWC 2 demoPos demoBefore = 2 ∧
    gapWC 2 demoPos demoAfter = 0 := by decide

theorem not_halfOpen_phi_support :
    ¬ (∀ C D : Fin 6 → Cell,
      (∀ x, support demoLengths (0 : Fin 3) x → C x = D x) →
      gapWC 2 demoPos C = gapWC 2 demoPos D) := by
  intro h
  have he := h demoBefore demoAfter demo_agree
  have hb := demo_values.1
  have ha := demo_values.2
  omega

theorem demo_pairOutside : ∀ x : Fin 6, x ≠ 5 → x ≠ 0 →
    demoAfter x = demoBefore x := by decide

theorem demo_untouched : ¬ support demoLengths (0 : Fin 3) (5 : Fin 6) ∧
    ¬ support demoLengths (0 : Fin 3) (0 : Fin 6) := by decide

theorem two_leader_overlap :
    let d : Fin 2 → Nat := fun _ => 2
    let hn : 0 < 4 := by decide
    (List.ofFn d).sum = 4 ∧
    readSupport d hn 0 0 ∧ readSupport d hn 1 0 ∧
    readSupport d hn 0 2 ∧ readSupport d hn 1 2 := by decide

/-- All remaining repository-specific obligations, on a fixed geometric slice. -/
structure PhysicalBridge {m n : Nat} (d : Fin m → Nat) (hn : 0 < n) where
  State : Type
  Event : Type
  cfg : State → Fin n → Cell
  next : State → Event → State
  scheduledLeft : State → Event → Fin n
  scheduledRight : State → Event → Fin n
  Phi : Fin m → State → Nat
  Ordinary : State → Event → Prop
  minimum : ∀ g, 2 ≤ d g
  total : (List.ofFn d).sum = n
  phi_before : ∀ (g : Fin m) (s : State) (e : Event), Ordinary s e →
    Phi g s = gapWC (d g) (gapPos d hn g) (cfg s)
  phi_after : ∀ (g : Fin m) (s : State) (e : Event), Ordinary s e →
    Phi g (next s e) = gapWC (d g) (gapPos d hn g) (cfg (next s e))
  step_outside_eq : ∀ (s : State) (e : Event), Ordinary s e →
    ∀ x, x ≠ scheduledLeft s e → x ≠ scheduledRight s e →
      cfg (next s e) x = cfg s x

theorem frameOutside {m n : Nat} (d : Fin m → Nat) (hn : 0 < n)
    (B : PhysicalBridge d hn) (g : Fin m) (s : B.State) (e : B.Event)
    (ho : B.Ordinary s e)
    (hnt : ¬ (readSupport d hn g (B.scheduledLeft s e) ∨
      readSupport d hn g (B.scheduledRight s e))) :
    B.Phi g (B.next s e) = B.Phi g s := by
  have hdd : 1 ≤ d g := by have hm := B.minimum g; omega
  rw [B.phi_after g s e ho, B.phi_before g s e ho]
  apply gapWC_read_support d hn B.total g hdd (B.cfg (B.next s e)) (B.cfg s)
  intro x hx
  apply B.step_outside_eq s e ho x
  · intro he
    exact hnt (Or.inl (he ▸ hx))
  · intro he
    exact hnt (Or.inr (he ▸ hx))

end Leader.GapOwnershipArcs

#print axioms Leader.GapOwnershipArcs.take_sum_mono
#print axioms Leader.GapOwnershipArcs.partialSum_succ
#print axioms Leader.GapOwnershipArcs.partialSum_total
#print axioms Leader.GapOwnershipArcs.offset_end_le
#print axioms Leader.GapOwnershipArcs.offset_separated
#print axioms Leader.GapOwnershipArcs.ring_pos
#print axioms Leader.GapOwnershipArcs.lift_range
#print axioms Leader.GapOwnershipArcs.lift_mod
#print axioms Leader.GapOwnershipArcs.mod_inj_positive
#print axioms Leader.GapOwnershipArcs.lift_of_mod
#print axioms Leader.GapOwnershipArcs.interval_cover
#print axioms Leader.GapOwnershipArcs.support_total
#print axioms Leader.GapOwnershipArcs.gapPos_lift
#print axioms Leader.GapOwnershipArcs.support_iff_pos
#print axioms Leader.GapOwnershipArcs.support_unique
#print axioms Leader.GapOwnershipArcs.support_disjoint
#print axioms Leader.GapOwnershipArcs.owner_support
#print axioms Leader.GapOwnershipArcs.support_iff_owner
#print axioms Leader.GapOwnershipArcs.ownership_touches_two
#print axioms Leader.GapOwnershipArcs.gapPos_shared
#print axioms Leader.GapOwnershipArcs.ofFn_nodup
#print axioms Leader.GapOwnershipArcs.mem_ownedSites
#print axioms Leader.GapOwnershipArcs.ownedSites_nodup
#print axioms Leader.GapOwnershipArcs.support_card
#print axioms Leader.GapOwnershipArcs.readSupport_iff_pos
#print axioms Leader.GapOwnershipArcs.left_endpoint_injective
#print axioms Leader.GapOwnershipArcs.readSupport_cover
#print axioms Leader.GapOwnershipArcs.read_touches_four
#print axioms Leader.GapOwnershipArcs.top_congr
#print axioms Leader.GapOwnershipArcs.gapWC_congr
#print axioms Leader.GapOwnershipArcs.gapWC_owned_plus_left
#print axioms Leader.GapOwnershipArcs.gapWC_read_support
#print axioms Leader.GapOwnershipArcs.demo_geometry
#print axioms Leader.GapOwnershipArcs.demo_agree
#print axioms Leader.GapOwnershipArcs.demo_values
#print axioms Leader.GapOwnershipArcs.not_halfOpen_phi_support
#print axioms Leader.GapOwnershipArcs.demo_pairOutside
#print axioms Leader.GapOwnershipArcs.demo_untouched
#print axioms Leader.GapOwnershipArcs.two_leader_overlap
#print axioms Leader.GapOwnershipArcs.frameOutside
