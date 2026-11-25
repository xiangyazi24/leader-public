import Leader.L4.BStarResetChartTouch
import Leader.L4.BStarCommitOperands
import Leader.L4.BStarCopyRightStrip

namespace L4.BStarOwnerChartWidth
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarResetChartTouch BStarAcquireVisitOrder
open BStarCopyRightStrip (addr addr_next)
open BStarCommitOperands (first_word right_back)

variable {n : Nat}

/-- A uniform upper bound at word tails also bounds every ordinal in the chart. -/
theorem ordinal_lt_of_width_bound (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (W : Nat) (width : ∀ i, h (rightNeighbor i) = true → ordinal h hh i + 1 ≤ W)
    (i : Fin n) : ordinal h hh i < W := by
  suffices aux : ∀ k (j : Fin n), n - ordinal h hh j = k → ordinal h hh j < W by
    exact aux _ i rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro j hk
    cases E : h (rightNeighbor j) with
    | true => exact width j E
    | false =>
      have J := ordinal_body h hh j E
      have bound := (ordinal_spec h hh j).1
      have lt : n - ordinal h hh (rightNeighbor j) < k := by omega
      have r := ih _ lt (rightNeighbor j) rfl
      omega

private theorem addr_zero (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem addr_add (a : Fin n) (i j : Nat) :
    addr (addr a i) j=addr a (i+j) := by
  apply Fin.ext
  change ((a.val+i)%n+j)%n=(a.val+(i+j))%n
  rw [Nat.mod_add_mod,Nat.add_assoc]

private theorem back_addr (i : Fin n) (d u : Nat) : addr (back i (d+u)) u=back i d := by
  induction u with
  | zero => exact addr_zero _
  | succ u ih =>
    rw [show d+(u+1)=d+u+1 by omega,
      show u+1=1+u by omega,←addr_add,addr_next,addr_zero,right_back]
    exact ih

theorem site_eq_of_word_eq_of_ordinal_eq (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (i j : Fin n) (words : word h i = word h j) (ordinals : ordinal h hh i = ordinal h hh j) :
    i = j := by
  have I := (ordinal_spec h hh i).2
  have J := (ordinal_spec h hh j).2
  have eqback := congrArg Subtype.val (header_word_injective h
    (a₁ := ⟨back i (ordinal h hh i), I.1⟩)
    (a₂ := ⟨back j (ordinal h hh j), J.1⟩)
    ((first_word hh i _ I).trans (words.trans (first_word hh j _ J).symm)))
  change back i (ordinal h hh i) = back j (ordinal h hh j) at eqback
  have addr_i := back_addr i 0 (ordinal h hh i)
  have addr_j := back_addr j 0 (ordinal h hh j)
  simp only [Nat.zero_add, back_zero] at addr_i addr_j
  exact addr_i.symm.trans (by rwa [eqback, ordinals])

theorem word_eq_of_commandOwner_eq (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (i j : Fin n) (occ : Fin 11) (owners : commandOwner h i occ = commandOwner h j occ) :
    word h i = word h j := by
  have E := congrArg (fun k => addressWord (total h) k (cmdDispl occ)) owners
  change addressWord (total h) (owner (total h) (word h i) (cmdDispl occ)) (cmdDispl occ)
    = addressWord (total h) (owner (total h) (word h j) (cmdDispl occ)) (cmdDispl occ) at E
  rw [address_inverse, address_inverse,
    Int.emod_eq_of_lt (word_range h i hh).1 (word_range h i hh).2,
    Int.emod_eq_of_lt (word_range h j hh).1 (word_range h j hh).2] at E
  exact E

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- A command occurrence fixes the cyclic word of an owner. Inside that word,
the old H6 ordinal is injective. No timing or successor snapshot is used. -/
theorem chart_length_le_width_mul {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback) (W : Nat)
    (width : ∀ i, oldH6 B base (rightNeighbor i) = true →
      ordinal (oldH6 B base) hh i + 1 ≤ W) :
    S.length ≤ 11 * W := by
  let h := oldH6 B base
  let code (u : Pos n) : Fin (11 * W) :=
    ⟨11 * ordinal h hh u.1 + u.2.val, by
      have U := ordinal_lt_of_width_bound h hh W width u.1
      have V := u.2.isLt
      omega⟩
  have inj (u v : Pos n) (U : u ∈ S) (V : v ∈ S) (E : code u = code v) : u = v := by
    have e := congrArg Fin.val E
    change 11 * ordinal h hh u.1 + u.2.val = 11 * ordinal h hh v.1 + v.2.val at e
    have lu := u.2.isLt
    have lv := v.2.isLt
    have ord : ordinal h hh u.1 = ordinal h hh v.1 := by omega
    have occ : u.2 = v.2 := Fin.ext (by omega)
    have same := (chart.entries u U).2.trans ((chart.entries v V).2.symm)
    have same' : commandOwner h u.1 u.2 = commandOwner h v.1 u.2 := by rw [← occ] at same; exact same
    exact Prod.ext
      (site_eq_of_word_eq_of_ordinal_eq h hh u.1 v.1
        (word_eq_of_commandOwner_eq h hh u.1 v.1 u.2 same') ord)
      occ
  have nodup : (S.map code).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun U V H E => H (inj _ _ U V E))
      (List.nodup_iff_pairwise_ne.mp chart.nodup)
  have subset : S.map code ⊆ List.finRange (11 * W) := fun {u} _ => List.mem_finRange u
  simpa using nodup.length_le_of_subset subset

end L4.BStarOwnerChartWidth
