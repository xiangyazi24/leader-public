import Leader.L3.Bank.RepairDigitCohortDomination

/-!
# Lemma e-packet: the export alignment of the source block

The source half of the e-packet lane (`out`, cells `0, ..., R-1`) determines the tail bits of
all its future exports. `srcWord R out` is that word, oldest first: a cell `j ≥ 1` holding `U`
or `D false` contributes one non-tail; a tail `D true` at cell `j` contributes itself and the
`R - j` non-tails it will rearm on its way out (at cells `j, ..., R - 1`), except at cell `0`,
whose rearm is the next tail; cell `0` holding `U` or `D true` contributes a whole group
`blk R = T F^(R-1)`.

Once cell `0` holds `U` or `D true` (`CZero`, closed under every letter), every lane letter
leaves `srcWord` unchanged, appends one group (a tail leaving cell `0`), or exports its first
letter into the target border (`srcStep`). Hence (`alignStep`, `preStep`):

* `Align R a out`: the word is `F^a (T F^(R-1))^(b+1)` with `a ≤ R - 1`. It is kept by every
  letter, and an export is a tail exactly when `a = 0`; the group counter is `g = R - 1 - a`
  and the next export is a tail iff `g = R - 1`.
* `Pre R m out`: the word is `Y (T F^(R-1))^(c+1)` with `|Y| = m` (the inherited prefix and
  the distinguished group of the cell-0 token). Every `CZero` state is `Pre` (`preOfCZero`); each
  export lowers `m`, and the export at `m = 0` is the distinguished tail, after which the block
  is `Align (R - 1)`.

Structural proof from the literal rows `bankRepairDigitPipeStep` and `bankRepairDigitDelStep`
(acceptance arbitrary).
-/

namespace L3.PacketMomentAlign

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3.RenewalReferenceClock
open L3.CohortDomination

/-! ### The word of the source block -/

/-- One group of exports: a tail, then `R - 1` non-tails (the export order). Consumer:
`srcWord`. -/
def blk (R : Nat) : List Bool := true :: List.replicate (R - 1) false

/-- The future exports owed by one source cell. Consumer: `wFrom`. -/
def cw (R j : Nat) : BankRepairDigitOutSh → List Bool
  | .E => []
  | .U => if j = 0 then blk R else [false]
  | .D false => [false]
  | .D true => true :: List.replicate (if j = 0 then R - 1 else R - j) false

/-- The future exports of cells `k - 1, ..., 0`. Consumer: `srcWord`. -/
def wFrom (R : Nat) (out : Nat → BankRepairDigitOutSh) : Nat → List Bool
  | 0 => []
  | k + 1 => cw R k (out k) ++ wFrom R out k

/-- The future exports of cells `lo + m - 1, ..., lo`. Consumer: `wordSplit`. -/
def wSeg (R : Nat) (out : Nat → BankRepairDigitOutSh) (lo : Nat) : Nat → List Bool
  | 0 => []
  | m + 1 => cw R (lo + m) (out (lo + m)) ++ wSeg R out lo m

/-- **The export word of the source block**, oldest first. Consumer: `srcStep`, `Align`. -/
def srcWord (R : Nat) (out : Nat → BankRepairDigitOutSh) : List Bool := wFrom R out R

/-- Cell `0` owes the next tail. Consumer: `srcStep`. -/
def CZero (out : Nat → BankRepairDigitOutSh) : Prop := out 0 = .U ∨ out 0 = .D true

/-- Splitting the word at a cell. Consumer: `wordSplit`. -/
theorem wFromAdd (R : Nat) (out : Nat → BankRepairDigitOutSh) (lo : Nat) :
    ∀ m, wFrom R out (lo + m) = wSeg R out lo m ++ wFrom R out lo
  | 0 => by simp [wSeg]
  | m + 1 => by
      show cw R (lo + m) (out (lo + m)) ++ wFrom R out (lo + m) = _
      rw [wFromAdd R out lo m]
      simp [wSeg, List.append_assoc]

/-- The low word reads only low cells. Consumer: `srcStep`. -/
theorem wFromCongr (R : Nat) (out out' : Nat → BankRepairDigitOutSh) :
    ∀ k, (∀ j, j < k → out' j = out j) → wFrom R out' k = wFrom R out k
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      simp only [wFrom]
      rw [h k (by omega), wFromCongr R out out' k (fun j hj => h j (by omega))]

/-- The segment word reads only its cells. Consumer: `srcStep`. -/
theorem wSegCongr (R : Nat) (out out' : Nat → BankRepairDigitOutSh) (lo : Nat) :
    ∀ m, (∀ j, lo ≤ j → j < lo + m → out' j = out j) → wSeg R out' lo m = wSeg R out lo m
  | 0 => fun _ => rfl
  | m + 1 => fun h => by
      simp only [wSeg]
      rw [h (lo + m) (by omega) (by omega),
        wSegCongr R out out' lo m (fun j h1 h2 => h j h1 (by omega))]

/-- The word around an internal edge `k`. Consumer: `srcStep`. -/
theorem wordSplit (R : Nat) (out : Nat → BankRepairDigitOutSh) (k : Nat) (hk : k + 2 ≤ R) :
    srcWord R out = wSeg R out (k + 2) (R - (k + 2)) ++
      (cw R (k + 1) (out (k + 1)) ++ (cw R k (out k) ++ wFrom R out k)) := by
  have h := wFromAdd R out (k + 2) (R - (k + 2))
  rw [show k + 2 + (R - (k + 2)) = R by omega] at h
  unfold srcWord
  rw [h]
  rfl

/-- The word at the port cell. Consumer: `srcStep`. -/
theorem wordPort (R : Nat) (out : Nat → BankRepairDigitOutSh) (hR : 1 ≤ R) :
    srcWord R out = cw R (R - 1) (out (R - 1)) ++ wFrom R out (R - 1) := by
  unfold srcWord
  obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
  rfl

/-- Appending a non-tail. Consumer: `pipeWordInner`. -/
theorem repSnoc (n : Nat) : List.replicate n false ++ [false] = List.replicate (n + 1) false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-! ### Local rows -/

/-- **An internal edge away from cell `0`** keeps the owed exports of its two cells.
Consumer: `srcStep`. -/
theorem pipeWordInner (R k : Nat) (hk : 1 ≤ k) (hk1 : k + 1 < R) (x y : BankRepairDigitOutSh) :
    cw R (k + 1) (bankRepairDigitPipeStep false x y).2 ++
        cw R k (bankRepairDigitPipeStep false x y).1 =
      cw R (k + 1) y ++ cw R k x := by
  have h0 : k ≠ 0 := by omega
  have h1 : k + 1 ≠ 0 := by omega
  have hr : R - k = (R - (k + 1)) + 1 := by omega
  rcases x with _ | _ | ⟨_ | _⟩ <;> rcases y with _ | _ | ⟨_ | _⟩ <;>
    simp only [bankRepairDigitPipeStep, cw, if_neg h0, if_neg h1, if_true, if_false,
      Bool.false_eq_true, List.nil_append, List.append_nil, List.cons_append, List.singleton_append]
  · rw [hr, repSnoc]

/-- **The edge at cell `0`**: a tail leaving cell `0` appends one group; nothing else changes
the owed exports. Consumer: `srcStep`. -/
theorem pipeWordZero (R : Nat) (x y : BankRepairDigitOutSh)
    (hx : x = .U ∨ x = .D true) :
    cw R 1 (bankRepairDigitPipeStep true x y).2 ++ cw R 0 (bankRepairDigitPipeStep true x y).1 =
      cw R 1 y ++ cw R 0 x ++ (if x = .D true ∧ y = .E then blk R else []) := by
  rcases hx with rfl | rfl
  · simp [bankRepairDigitPipeStep, cw, blk]
  · rcases y with _ | _ | ⟨_ | _⟩ <;> simp [bankRepairDigitPipeStep, cw, blk]

/-- **The delivery edge**: an export removes the first owed letter and writes the pending
packet into the empty carry-free border; otherwise the port cell owes the same and the border
is cleaned up at most. Consumer: `srcStep`. -/
theorem portWord (R : Nat) (hR : 2 ≤ R) (x : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) :
    (∃ B, x = .D B ∧ ky = false ∧ iy = .E ∧
        (bankRepairDigitDelStep x iy ky).2 = (.P B, false) ∧
        cw R (R - 1) x = B :: cw R (R - 1) (bankRepairDigitDelStep x iy ky).1) ∨
      (cw R (R - 1) (bankRepairDigitDelStep x iy ky).1 = cw R (R - 1) x ∧
        (bankRepairDigitDelStep x iy ky).2 = ((if ky then .E else iy), ky)) := by
  have h0 : R - 1 ≠ 0 := by omega
  have h1 : R - (R - 1) = 1 := by omega
  rcases x with _ | _ | ⟨_ | _⟩
  · right; cases ky <;> simp [bankRepairDigitDelStep]
  · right; cases ky <;> simp [bankRepairDigitDelStep, cw, h0]
  · cases ky
    · cases iy
      · left; exact ⟨false, rfl, rfl, rfl, rfl, by simp [bankRepairDigitDelStep, cw]⟩
      all_goals (right; simp [bankRepairDigitDelStep])
    · right; simp [bankRepairDigitDelStep]
  · cases ky
    · cases iy
      · left; exact ⟨true, rfl, rfl, rfl, rfl, by simp [bankRepairDigitDelStep, cw, h0, h1]⟩
      all_goals (right; simp [bankRepairDigitDelStep])
    · right; simp [bankRepairDigitDelStep]

/-! ### One lane letter -/

/-- An export of the lane letter `k` with tail bit `B`: the border was empty and carry-free and
now holds the pending packet. Consumer: `srcStep`. -/
def Exported (R : Nat) (s : CohortLane) (k : Nat) (B : Bool) : Prop :=
  k + 1 = R ∧ s.inp R = .E ∧ s.live R = false ∧ (cohortEdge R s k).inp R = .P B ∧
    (cohortEdge R s k).live R = false

/-- `CZero` is kept by every letter. Consumer: `srcStep`. -/
theorem c0Step (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : CZero s.out) :
    CZero (cohortEdge R s k).out := by
  unfold cohortEdge
  by_cases h1 : k + 1 < R
  · rw [if_pos h1]
    show CZero (cohortUpd (cohortUpd s.out k _) (k + 1) _)
    unfold CZero cohortUpd
    rw [if_neg (by omega)]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      rcases h with h | h <;> rw [h] <;> simp [bankRepairDigitPipeStep]
      split <;> simp
    · rw [if_neg (by omega)]; exact h
  · rw [if_neg h1]
    by_cases h2 : k + 1 = R
    · rw [if_pos h2]
      show CZero (cohortUpd s.out k _)
      unfold CZero cohortUpd
      rw [if_neg (by omega)]; exact h
    · rw [if_neg h2]
      split
      · exact h
      · split
        · exact h
        · exact h

/-- **One lane letter on the export word.** From a `CZero` state the word is unchanged (and a
port letter only cleans up the border), or one group is appended (a tail leaving cell `0`), or
the first letter is exported into the border. Consumer: `alignStep`, `preStep`, the
pending-word join. -/
theorem srcStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : CZero s.out) :
    (srcWord R (cohortEdge R s k).out = srcWord R s.out ∧
        (k + 1 = R → (cohortEdge R s k).inp R = (if s.live R then .E else s.inp R) ∧
          (cohortEdge R s k).live R = s.live R)) ∨
      (k = 0 ∧ srcWord R (cohortEdge R s k).out = srcWord R s.out ++ blk R) ∨
      (∃ B, Exported R s k B ∧ srcWord R s.out = B :: srcWord R (cohortEdge R s k).out) := by
  by_cases h1 : k + 1 < R
  · have hout : (cohortEdge R s k).out =
        cohortUpd (cohortUpd s.out k (bankRepairDigitPipeStep (decide (k = 0)) (s.out k)
          (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      unfold cohortEdge; rw [if_pos h1]
    have hsplit' := wordSplit R (cohortEdge R s k).out k (by omega)
    have hsplit := wordSplit R s.out k (by omega)
    have hseg : wSeg R (cohortEdge R s k).out (k + 2) (R - (k + 2)) =
        wSeg R s.out (k + 2) (R - (k + 2)) :=
      wSegCongr R _ _ _ _ (fun j hj _ => by
        rw [hout]; simp [cohortUpd, show j ≠ k by omega, show j ≠ k + 1 by omega])
    have hlow : wFrom R (cohortEdge R s k).out k = wFrom R s.out k :=
      wFromCongr R _ _ _ (fun j hj => by
        rw [hout]; simp [cohortUpd, show j ≠ k by omega, show j ≠ k + 1 by omega])
    have ek1 : (cohortEdge R s k).out (k + 1) =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      rw [hout]; simp [cohortUpd]
    have ek : (cohortEdge R s k).out k =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 := by
      rw [hout]; simp [cohortUpd]
    rw [hsplit', hsplit, hseg, hlow, ek1, ek]
    by_cases hk : k = 0
    · subst hk
      have hz := pipeWordZero R (s.out 0) (s.out 1) h
      have e0 : decide ((0 : Nat) = 0) = true := rfl
      rw [e0]
      have hw0 : wFrom R s.out 0 = [] := rfl
      rw [hw0]
      by_cases hc : s.out 0 = .D true ∧ s.out (0 + 1) = .E
      · right; left
        refine ⟨rfl, ?_⟩
        simp only [List.append_nil] at hz ⊢
        rw [show (0 : Nat) + 1 = 1 from rfl, hz, if_pos hc]
        simp [List.append_assoc]
      · left
        refine ⟨?_, fun h' => by omega⟩
        simp only [List.append_nil] at hz ⊢
        rw [show (0 : Nat) + 1 = 1 from rfl, hz, if_neg hc]
        simp [List.append_assoc]
    · left
      refine ⟨?_, fun h' => by omega⟩
      have e0 : decide (k = 0) = false := by simp [hk]
      rw [e0]
      have hi := pipeWordInner R k (by omega) h1 (s.out k) (s.out (k + 1))
      congr 1
      rw [← List.append_assoc, hi, List.append_assoc]
  · by_cases h2 : k + 1 = R
    · have hd := portWord R hR (s.out k) (s.inp (k + 1)) (s.live (k + 1))
      have hout : (cohortEdge R s k).out =
          cohortUpd s.out k (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
      have hinp : (cohortEdge R s k).inp R =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.inp (k + 1) _ R = _
        simp [cohortUpd, h2]
      have hlive : (cohortEdge R s k).live R =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.2 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.live (k + 1) _ R = _
        simp [cohortUpd, h2]
      have hk : k = R - 1 := by omega
      have hw' := wordPort R (cohortEdge R s k).out (by omega)
      have hw := wordPort R s.out (by omega)
      have hlow : wFrom R (cohortEdge R s k).out (R - 1) = wFrom R s.out (R - 1) :=
        wFromCongr R _ _ _ (fun j hj => by rw [hout]; simp [cohortUpd, show j ≠ k by omega])
      have ek : (cohortEdge R s k).out (R - 1) =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
        rw [hout, ← hk]; simp [cohortUpd]
      rw [h2] at hd hinp hlive ek
      rw [← hk] at hw hw' hlow ek
      rw [hw', hw, hlow, ek]
      rcases hd with ⟨B, hx, hky, hiy, hd2, hcw⟩ | ⟨hcw, hd2⟩
      · right; right
        refine ⟨B, ⟨h2, hiy, hky, ?_, ?_⟩, ?_⟩
        · rw [hinp, hd2]
        · rw [hlive, hd2]
        · rw [← hk] at hcw; rw [hcw]; rfl
      · left
        rw [← hk] at hcw
        refine ⟨by rw [hcw], fun _ => ?_⟩
        rw [hinp, hlive, hd2]
        exact ⟨rfl, rfl⟩
    · left
      have hout : (cohortEdge R s k).out = s.out := by
        unfold cohortEdge; rw [if_neg h1, if_neg h2]
        split
        · rfl
        · split <;> rfl
      exact ⟨by rw [hout], fun h' => absurd h' h2⟩

/-! ### The alignment invariant -/

/-- `b` groups. Consumer: `Align`. -/
def grp (R : Nat) : Nat → List Bool
  | 0 => []
  | b + 1 => grp R b ++ blk R

/-- The first group in front. Consumer: `alignStep`, `preStep`. -/
theorem grpCons (R : Nat) : ∀ b, grp R (b + 1) = blk R ++ grp R b
  | 0 => by simp [grp]
  | b + 1 => by
      show grp R (b + 1) ++ blk R = blk R ++ (grp R b ++ blk R)
      rw [grpCons R b, List.append_assoc]

/-- **The alignment of the source block**: the owed exports are `F^a (T F^(R-1))^(b+1)` with
`a ≤ R - 1`; the next export is a tail iff `a = 0` (group counter `R - 1 - a`).
Consumer: the renewal preparation `V` (via the pending-word join). -/
def Align (R a : Nat) (out : Nat → BankRepairDigitOutSh) : Prop :=
  CZero out ∧ a + 1 ≤ R ∧ ∃ b, srcWord R out = List.replicate a false ++ grp R (b + 1)

/-- The inherited prefix before the distinguished group. Consumer: `preStep`. -/
def Pre (R m : Nat) (out : Nat → BankRepairDigitOutSh) : Prop :=
  CZero out ∧ ∃ Y c, Y.length = m ∧ srcWord R out = Y ++ grp R (c + 1)

/-- A `CZero` word ends with a group. Consumer: `preOfCZero`. -/
theorem wordCZero (R : Nat) (hR : 1 ≤ R) (out : Nat → BankRepairDigitOutSh) (h : CZero out) :
    srcWord R out = wSeg R out 1 (R - 1) ++ blk R := by
  have h1 := wFromAdd R out 1 (R - 1)
  rw [show 1 + (R - 1) = R by omega] at h1
  unfold srcWord
  rw [h1]
  show _ ++ (cw R 0 (out 0) ++ []) = _
  rcases h with h | h <;> rw [h] <;> simp [cw, blk]

/-- **Every `CZero` state is `Pre`.** Consumer: the renewal preparation `V`. -/
theorem preOfCZero (R : Nat) (hR : 1 ≤ R) (out : Nat → BankRepairDigitOutSh) (h : CZero out) :
    Pre R (wSeg R out 1 (R - 1)).length out :=
  ⟨h, _, 0, rfl, by rw [wordCZero R hR out h]; simp [grp]⟩

/-- No group fits in non-tails only. Consumer: `alignStep`, `preStep`. -/
theorem noTailRep (R a : Nat) (Y : List Bool) : List.replicate a false ≠ Y ++ blk R := by
  intro h
  have : true ∈ List.replicate a false := by rw [h]; simp [blk]
  simp at this

/-- **The alignment is kept, and fixes the tail bit of every export.**
Consumer: the renewal preparation `V` (the pending-word join). -/
theorem alignStep (R a : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : Align R a s.out) :
    (Align R a (cohortEdge R s k).out ∧ ∀ B, ¬ (Exported R s k B ∧
        srcWord R s.out = B :: srcWord R (cohortEdge R s k).out)) ∨
      (∃ B, Exported R s k B ∧ srcWord R s.out = B :: srcWord R (cohortEdge R s k).out ∧
        B = decide (a = 0) ∧ Align R (if a = 0 then R - 1 else a - 1) (cohortEdge R s k).out) := by
  obtain ⟨hc, ha, b, hw⟩ := h
  have hc' := c0Step R hR s k hc
  rcases srcStep R hR s k hc with ⟨he, _⟩ | ⟨_, he⟩ | ⟨B, hex, he⟩
  · left
    refine ⟨⟨hc', ha, b, by rw [he, hw]⟩, fun B ⟨_, hB⟩ => ?_⟩
    rw [he] at hB
    have := congrArg List.length hB
    simp at this
  · left
    refine ⟨⟨hc', ha, b + 1, by rw [he, hw, List.append_assoc]; rfl⟩, fun B ⟨_, hB⟩ => ?_⟩
    rw [he] at hB
    have := congrArg List.length hB
    simp [blk] at this
    omega
  · right
    refine ⟨B, hex, he, ?_⟩
    rw [hw] at he
    obtain ⟨Y, hY⟩ : ∃ Y, srcWord R (cohortEdge R s k).out = Y ++ blk R :=
      ⟨_, wordCZero R (by omega) _ hc'⟩
    by_cases h0 : a = 0
    · subst h0
      rw [grpCons] at he
      simp only [List.replicate_zero, List.nil_append, blk, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      refine ⟨by rw [← hB]; rfl, ?_⟩
      rw [if_pos rfl]
      refine ⟨hc', by omega, ?_⟩
      cases b with
      | zero =>
          exfalso
          simp [grp] at hrest
          exact noTailRep R (R - 1) Y (by rw [hrest, hY])
      | succ b => exact ⟨b, by rw [← hrest]⟩
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      refine ⟨by rw [← hB]; simp, ?_⟩
      rw [if_neg (by omega)]
      exact ⟨hc', by omega, b, by rw [← hrest]; rfl⟩

/-- **The inherited prefix shrinks with each export; the export at `m = 0` is the
distinguished tail, after which the block is aligned.** Consumer: the renewal preparation `V`
(the distinguished-tail phase `F`). -/
theorem preStep (R m : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : Pre R m s.out) :
    (Pre R m (cohortEdge R s k).out ∧ ∀ B, ¬ (Exported R s k B ∧
        srcWord R s.out = B :: srcWord R (cohortEdge R s k).out)) ∨
      (∃ B, Exported R s k B ∧ srcWord R s.out = B :: srcWord R (cohortEdge R s k).out ∧
        (m = 0 → B = true ∧ Align R (R - 1) (cohortEdge R s k).out) ∧
        (0 < m → Pre R (m - 1) (cohortEdge R s k).out)) := by
  obtain ⟨hc, Y, c, hY, hw⟩ := h
  have hc' := c0Step R hR s k hc
  rcases srcStep R hR s k hc with ⟨he, _⟩ | ⟨_, he⟩ | ⟨B, hex, he⟩
  · left
    refine ⟨⟨hc', Y, c, hY, by rw [he, hw]⟩, fun B ⟨_, hB⟩ => ?_⟩
    rw [he] at hB
    have := congrArg List.length hB
    simp at this
  · left
    refine ⟨⟨hc', Y, c + 1, hY, by rw [he, hw, List.append_assoc]; rfl⟩,
      fun B ⟨_, hB⟩ => ?_⟩
    rw [he] at hB
    have := congrArg List.length hB
    simp [blk] at this
    omega
  · right
    refine ⟨B, hex, he, ?_, ?_⟩
    · intro hm
      rw [hm] at hY
      have hY0 : Y = [] := List.eq_nil_of_length_eq_zero hY
      rw [hw, hY0, List.nil_append, grpCons] at he
      simp only [blk, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      obtain ⟨Z, hZ⟩ : ∃ Z, srcWord R (cohortEdge R s k).out = Z ++ blk R :=
        ⟨_, wordCZero R (by omega) _ hc'⟩
      refine ⟨hB.symm, hc', by omega, ?_⟩
      cases c with
      | zero =>
          exfalso
          simp [grp] at hrest
          exact noTailRep R (R - 1) Z (by rw [hrest, hZ])
      | succ c => exact ⟨c, by rw [← hrest]⟩
    · intro hm
      cases Y with
      | nil => simp at hY; omega
      | cons y Y' =>
          rw [hw] at he
          simp only [List.cons_append, List.cons.injEq] at he
          exact ⟨hc', Y', c, by simp at hY; omega, he.2.symm⟩

end L3.PacketMomentAlign

#print axioms L3.PacketMomentAlign.srcStep
#print axioms L3.PacketMomentAlign.alignStep
#print axioms L3.PacketMomentAlign.preStep
#print axioms L3.PacketMomentAlign.preOfCZero
