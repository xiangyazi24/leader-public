import Leader.L4.BStarH6WordChart
import Leader.L4.BStarLongSector

/-! Distance back to the most recent H6 header on the actual physical ring.
No assertion that this header predicate stabilizes. -/
namespace L4.BStarH6Ordinal
open AllSizeProtocol BStarH6WordChart

def back {n : Nat} (i : Fin n) (k : Nat) : Fin n :=
  ⟨(((i.val : Int)-(k : Int)) % (n : Int)).toNat,by
    have P : 0<(n : Int) := by have := i.isLt; omega
    have U := Int.emod_lt_of_pos ((i.val : Int)-(k : Int)) P
    omega⟩

theorem back_zero {n : Nat} (i : Fin n) : back i 0=i := by
  apply Fin.ext
  change (((i.val : Int)-0) % (n : Int)).toNat=i.val
  rw [Int.sub_zero,Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)]
  simp

theorem back_right_succ {n : Nat} (i : Fin n) (k : Nat) :
    back (rightNeighbor i) (k+1)=back i k := by
  apply Fin.ext
  change (((((i.val+1)%n : Nat) : Int)-((k+1 : Nat) : Int)) % (n : Int)).toNat = _
  simp only [Int.natCast_emod,Int.natCast_add,Int.natCast_one]
  congr 1
  rw [Int.sub_emod,Int.emod_emod,← Int.sub_emod]
  congr 1
  omega

theorem back_hits {n : Nat} (i j : Fin n) : ∃ k<n, back i k=j := by
  by_cases h : j.val≤i.val
  · refine ⟨i.val-j.val,by have := i.isLt; omega,Fin.ext ?_⟩
    change (((i.val : Int)-((i.val-j.val : Nat) : Int))%(n : Int)).toNat=j.val
    rw [show (i.val : Int)-((i.val-j.val : Nat) : Int)=(j.val : Int) by omega,
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)]
    simp
  · refine ⟨n+i.val-j.val,by have := j.isLt; omega,Fin.ext ?_⟩
    change (((i.val : Int)-((n+i.val-j.val : Nat) : Int))%(n : Int)).toNat=j.val
    rw [show (i.val : Int)-((n+i.val-j.val : Nat) : Int)=(j.val : Int)-(n : Int) by
      have := j.isLt; omega]
    rw [Int.sub_emod,Int.emod_self,Int.sub_zero,Int.emod_emod,
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)]
    simp

def First {n : Nat} (h : Fin n → Bool) (i : Fin n) (k : Nat) : Prop :=
  h (back i k)=true ∧ ∀ l<k, h (back i l)=false

theorem first_unique {n : Nat} (h : Fin n → Bool) (i : Fin n) {k l : Nat}
    (H : First h i k) (J : First h i l) : k=l := by
  rcases Nat.lt_trichotomy k l with K|E|L
  · exact Bool.noConfusion (H.1.symm.trans (J.2 k K))
  · exact E
  · exact Bool.noConfusion (J.1.symm.trans (H.2 l L))

theorem first_exists {n : Nat} (h : Fin n → Bool) (i : Fin n)
    (hh : ∃ j, h j=true) : ∃ k<n, First h i k := by
  obtain ⟨j,hj⟩ := hh
  obtain ⟨k,hk,E⟩ := back_hits i j
  have H : h (back i k)=true := E ▸ hj
  have search : ∀ u, h (back i u)=true → ∃ v≤u, First h i v := by
    intro u
    induction u using Nat.strongRecOn with
    | ind u ih =>
      intro U
      by_cases w : ∃ v<u, h (back i v)=true
      · obtain ⟨v,hv,V⟩ := w
        obtain ⟨b,hb,B⟩ := ih v hv V
        exact ⟨b,by omega,B⟩
      · refine ⟨u,Nat.le_refl _,U,?_⟩
        intro v hv
        cases b : h (back i v)
        · rfl
        · exact (w ⟨v,hv,b⟩).elim
  obtain ⟨v,hv,V⟩ := search k H
  exact ⟨v,by omega,V⟩

noncomputable def ordinal {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true) (i : Fin n) : Nat :=
  Classical.choose (first_exists h i hh)

theorem ordinal_spec {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true) (i : Fin n) :
    ordinal h hh i<n ∧ First h i (ordinal h hh i) :=
  Classical.choose_spec (first_exists h i hh)

theorem ordinal_zero {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true) (i : Fin n) :
    ordinal h hh i=0 ↔ h i=true := by
  constructor
  · intro E
    have H := (ordinal_spec h hh i).2.1
    rwa [E,back_zero] at H
  · intro H
    exact first_unique h i (ordinal_spec h hh i).2
      ⟨by rwa [back_zero],fun _ E => (Nat.not_lt_zero _ E).elim⟩

theorem ordinal_body {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true) (i : Fin n)
    (body : h (rightNeighbor i)=false) :
    ordinal h hh (rightNeighbor i)=ordinal h hh i+1 := by
  apply first_unique h (rightNeighbor i) (ordinal_spec h hh _).2
  refine ⟨?_,?_⟩
  · rw [back_right_succ]
    exact (ordinal_spec h hh i).2.1
  · intro k K
    cases k with
    | zero => rwa [back_zero]
    | succ k =>
      rw [back_right_succ]
      exact (ordinal_spec h hh i).2.2 k (by omega)

theorem ordinal_right {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true) (i : Fin n) :
    ordinal h hh (rightNeighbor i)=
      if h (rightNeighbor i) then 0 else ordinal h hh i+1 := by
  cases H : h (rightNeighbor i)
  · exact ordinal_body h hh i H
  · exact (ordinal_zero h hh _).mpr H

noncomputable def oldOrdinal {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (hh : ∃ i, oldH6 b x i=true) (i : Fin n) : Nat :=
  ordinal (oldH6 b x) hh i

/-- The existing joined row installs the clipped ordinal at the
responder whenever the old initiator already has its exact offset.
Header reset requires no old initiator accuracy. -/
theorem joined_installs_ordinal (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    {n : Nat} (x : Fin n → LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (i : Fin n) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    ∀ hh : ∃ z, oldH6 b x z=true,
      (oldH6 b x (rightNeighbor i)=false →
        BStarPhysicalDigitSem.off (longGeometry b (x i))=min 5 (oldOrdinal b x hh i)) →
      BStarTrace.offsetL (largePair b (x i,x (rightNeighbor i))).2.long =
        min 5 (oldOrdinal b x hh (rightNeighbor i)) := by
  dsimp only
  intro hh HO
  let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  cases H : oldH6 b x (rightNeighbor i)
  · have A := BStarLongSector.joined_offset_increment k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x i,x (rightNeighbor i)) (oldOrdinal b x hh i) (HO H) H
    change BStarTrace.offsetL (largePair b (x i,x (rightNeighbor i))).2.long = _
    have E := ordinal_body (oldH6 b x) hh i H
    change oldOrdinal b x hh (rightNeighbor i) = oldOrdinal b x hh i+1 at E
    rw [E]
    exact A
  · have A := BStarLongSector.joined_offset_reset k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x i,x (rightNeighbor i)) H
    change BStarTrace.offsetL (largePair b (x i,x (rightNeighbor i))).2.long = _
    have E : oldOrdinal b x hh (rightNeighbor i)=0 :=
      (ordinal_zero (oldH6 b x) hh (rightNeighbor i)).mpr H
    rw [E]
    exact A

/-- Exact S7 outputs and the sampled END cache are sufficient for the
digit-geometry interface. The no-short premise is local to an
incoming H6 seam: its predecessor has completed at least r sites.
Without this premise a short sector can place END across the wrong seam. -/
theorem digitAt_of_accurate {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (hh : ∃ z, oldH6 b x z=true)
    (i : Fin n) (r : Nat) (hr : 1<r)
    (inPrefix : oldOrdinal b x hh i<r)
    (off : BStarPhysicalDigitSem.off (longGeometry b (x i))=min 5 (oldOrdinal b x hh i))
    (flag : ∀ z, (longGeometry b (x z)).inside=decide (oldOrdinal b x hh z<r) ∧
      (longGeometry b (x z)).last=decide (oldOrdinal b x hh z+1=r))
    (cache : (longGeometry b (x i)).successorEnd=
      ((longGeometry b (x (rightNeighbor i))).inside &&
        (longGeometry b (x (rightNeighbor i))).last))
    (notShort : oldH6 b x (rightNeighbor i)=true → r≤oldOrdinal b x hh i+1) :
    BStarLongSector.DigitAt (longGeometry b (x i)) r (oldOrdinal b x hh i) := by
  refine ⟨inPrefix,off,?_,?_⟩
  · rw [(flag i).1,(flag i).2]
    simp [inPrefix]
  · rw [cache,(flag (rightNeighbor i)).1,(flag (rightNeighbor i)).2]
    have E : oldOrdinal b x hh (rightNeighbor i)=
        if oldH6 b x (rightNeighbor i) then 0 else oldOrdinal b x hh i+1 :=
      ordinal_right (oldH6 b x) hh i
    rw [E]
    cases H : oldH6 b x (rightNeighbor i)
    · simp only [Bool.false_eq_true,if_false]
      have K : oldOrdinal b x hh i+1+1=r → oldOrdinal b x hh i+1<r := by omega
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨And.right,fun e => ⟨K e,e⟩⟩
    · have A := notShort H
      have B : ¬oldOrdinal b x hh i+2=r := by omega
      have C : ¬1=r := by omega
      simp [C,B]

end L4.BStarH6Ordinal
