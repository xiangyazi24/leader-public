import Leader.L4.WindowA0FixedSink

namespace L4.WindowA0Masked
open WindowA0FixedSink FIFOCompare

/-- Coordinates are clockwise lifts from the fixed predecessor of the
entry I. Slot 0 is therefore excluded from all retained inventories. -/
def stock {p c n : Nat} (x : Config p c n) (base : Fin n)
    (I J : Nat) (extra : Bool) (l : Nat) : Bool :=
  if I≤l ∧ l<J ∧ ¬(extra=true ∧ l+1=J) then (x (liftedSite base l)).stock else false

/-- A successful J payment consumes its donor and keeps the old J
resident. The new mask excludes precisely this latter newly admitted
resident, whether the premark donor was tracked or was itself extra. -/
theorem paid_j_mask {p c n : Nat} (_hn : 4≤n) (x : Config p c n) (base : Fin n)
    (I J : Nat) (extra : Bool) (hI : I<J) (hJ : J<n)
    (hm : (x (liftedSite base (J-1))).mark=true)
    (hs : (x (liftedSite base (J-1))).stock=true) :
    let e := liftedSite base (J-1)
    let extra' := (x (liftedSite base J)).stock
    stock (step x e) base I (J+1) extra' =
      setStock (stock x base I J extra) (J-1) false := by
  let e := liftedSite base (J-1)
  let r := liftedSite base J
  have he : rightNeighbor e=r := by rw [←liftedSite_succ,show J-1+1=J by omega]
  have hnE : e≠r := fun h => by
    have H := liftedSite_inj base (show J-1<n by omega) hJ h
    omega
  obtain ⟨hL,hR⟩ := GGStockPhysical.marked_stock_consumed (x e) (x (rightNeighbor e)) hm hs
  have hl : (step x e e).stock=false := by simpa [step] using hL
  have hr : (step x e r).stock=(x r).stock := by
    rw [he] at hR
    simpa [step,Ne.symm hnE,he] using hR
  funext l
  change stock (step x e) base I (J+1) (x r).stock l = setStock (stock x base I J extra) (J-1) false l
  by_cases hD : l=J-1
  · subst l
    simp [stock,setStock,hl,show liftedSite base (J-1)=e from rfl]
  by_cases hR0 : l=J
  · subst l
    simp only [setStock,if_neg hD,stock,Nat.lt_irrefl,false_and,and_false,if_false]
    rw [show liftedSite base J=r from rfl,hr]
    cases h : (x r).stock <;> simp [show I≤J by omega]
  by_cases hh : I≤l ∧ l<J
  · have eN : liftedSite base l≠e := fun h =>
      hD (liftedSite_inj base (by omega) (by omega) h)
    have rN : liftedSite base l≠r := fun h =>
      hR0 (liftedSite_inj base (by omega) hJ h)
    have hh1 : ¬(l+1=J) := by omega
    have hFrame : step x e (liftedSite base l)=x (liftedSite base l) := by simp [step,eN,he,rN]
    simp [stock,setStock,hD,hh.1,hh.2,show l<J+1 by omega,hh1,hR0,hFrame]
  · have hh' : ¬(I≤l ∧ l<J+1) := by omega
    simp only [setStock,if_neg hD,stock]
    rw [if_neg (fun h => hh' ⟨h.1,h.2.1⟩),if_neg (fun h => hh ⟨h.1,h.2.1⟩)]

/-- A successful I payment only discards the leftmost old tracked
stock. Any pending extra can never be this top on a surviving paid
mark, because I+1=J would collide into J. -/
theorem paid_i_mask {p c n : Nat} (x : Config p c n) (base : Fin n)
    (I J : Nat) (extra : Bool) (hI : 0<I) (hSep : I+1<J) (hJ : J<n) :
    stock (step x (liftedSite base (I-1))) base (I+1) J extra =
      setStock (stock x base I J extra) I false := by
  let e := liftedSite base (I-1)
  have he : rightNeighbor e=liftedSite base I := by rw [←liftedSite_succ,show I-1+1=I by omega]
  funext l
  change stock (step x e) base (I+1) J extra l = setStock (stock x base I J extra) I false l
  by_cases hl : l=I
  · subst l
    simp [stock,setStock,show ¬I+1≤I by omega]
  by_cases H : I+1≤l ∧ l<J
  · have eN : liftedSite base l≠e := fun h => by
      have h := liftedSite_inj base (show l<n by omega) (show I-1<n by omega) h
      omega
    have rN : liftedSite base l≠rightNeighbor e := fun h =>
      hl (liftedSite_inj base (by omega) (by omega) (h.trans he))
    have hFrame : step x e (liftedSite base l)=x (liftedSite base l) := by simp [step,eN,rN]
    simp [stock,setStock,hl,H.1,H.2,show I≤l by omega,hFrame]
  · have H' : ¬(I≤l ∧ l<J) := by omega
    simp only [setStock,if_neg hl,stock]
    rw [if_neg (fun h => H ⟨h.1,h.2.1⟩),if_neg (fun h => H' ⟨h.1,h.2.1⟩)]

/-- An actual internal selected edge has the full masked exclusion
effect. An existing extra is at the door: if the selected responder
is that socket, its premark occupancy blocks the literal move. -/
theorem interior_mask {p c n : Nat} (hn : 4≤n) (x : Config p c n) (base : Fin n)
    (I J k : Nat) (extra : Bool) (hI : I≤k) (hK : k+1<J) (hJ : J<n)
    (mc : MCOV x) (hm : (x (liftedSite base k)).mark=false)
    (hl : (x (liftedSite base k)).leader=false)
    (hExtra : extra=true → (x (liftedSite base (J-1))).stock=true) :
    let e := liftedSite base k
    let s := stock x base I J extra
    stock (step x e) base I J extra =
      if s k && !(x (liftedSite base (k+1))).stock
        then setStock (setStock s k false) (k+1) true else s := by
  let e := liftedSite base k
  let r := liftedSite base (k+1)
  have er : rightNeighbor e=r := (liftedSite_succ base k).symm
  let s := stock x base I J extra
  have sk : s k=(x e).stock := by simp [s,stock,hI,show k<J by omega,show k+1≠J by omega,e]
  have hrule := interior_exclusion hn x e mc hm hl
  rw [er] at hrule
  change stock (step x e) base I J extra =
    if s k && !(x r).stock then setStock (setStock s k false) (k+1) true else s
  by_cases hit : (s k && !(x r).stock)=true
  · rw [if_pos hit]
    have hh : ((x e).stock && Bool.not (x r).stock)=true := sk ▸ hit
    rw [if_pos hh,Prod.mk.injEq] at hrule
    have vacant : (x r).stock=false := by
      have H := (Bool.and_eq_true_iff.mp hh).2
      cases hs : (x r).stock <;> simp_all
    have hskip : ¬(extra=true ∧ k+1+1=J) := by
      rintro ⟨he,hj⟩
      have H := hExtra he
      rw [show J-1=k+1 by omega] at H
      change (x r).stock=true at H
      simp [vacant] at H
    funext l
    by_cases h1 : l=k
    · subst l
      simp [stock,setStock,show k+1≠J by omega,
        show liftedSite base k=e from rfl,hrule.1]
    · by_cases h2 : l=k+1
      · subst l
        change stock (step x e) base I J extra (k+1) = _
        rw [stock,if_pos ⟨by omega,hK,hskip⟩,setStock,if_pos rfl]
        exact hrule.2
      · have frame : I≤l → l<J → step x e (liftedSite base l)=x (liftedSite base l) := by
          intro h1 h2
          have eN : liftedSite base l≠e := fun h =>
            ‹l≠k› (liftedSite_inj base (by omega) (by omega) h)
          have rN : liftedSite base l≠r := fun h =>
            ‹l≠k+1› (liftedSite_inj base (by omega) (by omega) h)
          simp [step,eN,er,rN]
        simp only [setStock,if_neg h1,if_neg h2,s,stock]
        split
        · rename_i H
          rw [frame H.1 H.2.1]
        · rfl
  · have hh : ¬(((x e).stock && Bool.not (x r).stock)=true) := fun h => hit (sk.symm ▸ h)
    rw [if_neg hh,Prod.mk.injEq] at hrule
    rw [if_neg hit]
    funext l
    simp only [s,stock]
    split
    · rename_i H
      by_cases h1 : l=k
      · subst l
        exact hrule.1
      · by_cases h2 : l=k+1
        · subst l
          exact hrule.2
        · have eN : liftedSite base l≠e := fun h =>
            h1 (liftedSite_inj base (by have := H.2.1; omega) (by omega) h)
          have rN : liftedSite base l≠r := fun h =>
            h2 (liftedSite_inj base (by have := H.2.1; omega) (by omega) h)
          simp [step,eN,er,rN]
    · rfl

/-- Full mask frame for nonmoving boundary and exterior services. The
touch tests can be discharged by comparing lifted coordinates with
the observed physical edge. -/
theorem boundary_or_exterior_mask {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (base e : Fin n) (I J : Nat) (extra : Bool)
    (hLeft : ∀ l, I≤l → l<J → liftedSite base l=e → l+1=J)
    (hRight : ∀ l, I≤l → l<J → liftedSite base l=rightNeighbor e → l=I)
    (hTop : rightNeighbor e=liftedSite base I → (x e).mark=true)
    (hDoor : liftedSite base (J-1)=e →
      (x e).mark=true ∧ (x e).leader=false ∧
      (x (rightNeighbor e)).leader=false ∧
      geometricPay (x e) (x (rightNeighbor e))=false) :
    stock (step x e) base I J extra = stock x base I J extra := by
  funext l
  unfold stock
  split
  · rename_i H
    by_cases hL : liftedSite base l=e
    · have pos := hLeft l H.1 H.2.1 hL
      have hd := hDoor (by simpa [show J-1=l by omega] using hL)
      have hz : (x e).stock=false := by
        apply Bool.eq_false_iff.mpr
        intro hS
        have hP := WindowA0StockDrain.marked_ghost_stock_pays _ _ hd.1 hd.2.2.1 hS
        rw [hd.2.2.2] at hP
        cases hP
      rw [hL,hz]
      simpa [step] using WindowA0Drained.marked_left_no_injection _ _ hd.1 hd.2.1 hz
    · by_cases hR : liftedSite base l=rightNeighbor e
      · have hs := hRight l H.1 H.2.1 hR
        rw [hR]
        exact top_no_import hn x e (hTop (by simpa [hs] using hR.symm))
      · simp [step,hL,hR]
  · rfl

end L4.WindowA0Masked
