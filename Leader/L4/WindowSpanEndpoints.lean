import Leader.L4.WindowFourHeadCut
import Leader.L4.WindowSpan

/-! The physical span between the extreme selected marks, using the
old rightmost incoming label as its only increasing mark. -/
namespace L4.WindowSpanEndpoints

open SevenTagCharge WindowFourHeadTrace

def width {n : Nat} (a b : Fin n) : Nat := (b.val+n-a.val)%n

theorem width_lt {n : Nat} (a b : Fin n) : width a b<n :=
  Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)

theorem width_lift {n : Nat} (a b : Fin n) : liftedSite a (width a b)=b := by
  apply Fin.ext
  change (a.val+(b.val+n-a.val)%n)%n=b.val
  have A : a.val≤b.val+n := by have := a.isLt; omega
  calc
    _ = (a.val+(b.val+n-a.val))%n := by rw [Nat.add_mod_mod]
    _ = (b.val+n)%n := by congr 1; omega
    _ = b.val := by simp [Nat.mod_eq_of_lt b.isLt]

theorem width_unique {n d : Nat} (a b : Fin n) (h : d<n)
    (E : liftedSite a d=b) : width a b=d :=
  liftedSite_inj a (width_lt a b) h ((width_lift a b).trans E.symm)

private theorem width_pos {n : Nat} {a b : Fin n} (neq : a≠b) : 0<width a b := by
  by_cases h : width a b=0
  · exact (neq (by simpa only [h,liftedSite_zero] using width_lift a b)).elim
  · omega

private theorem lift_comp {n : Nat} (a : Fin n) (d e : Nat) :
    liftedSite (liftedSite a d) e=liftedSite a (d+e) := by
  apply Fin.ext
  change ((a.val+d)%n+e)%n=(a.val+(d+e))%n
  simp [Nat.add_assoc]

private theorem wrap_self {n : Nat} (a : Fin n) : liftedSite a n=a := by
  apply Fin.ext
  change (a.val+n)%n=a.val
  simp [Nat.mod_eq_of_lt a.isLt]

def displacement {p c n : Nat} (z : Ledger p c n) (e a : Fin n) : Nat :=
  if moves z e a then 1 else 0

private theorem lands {p c n : Nat} (z : Ledger p c n) (e a : Fin n) :
    landing z e a=liftedSite a (displacement z e a) := by
  by_cases h : moves z e a <;> simp [landing,displacement,h,liftedSite_succ,liftedSite_zero]

/-- No modulo wrap is assumed for a moving endpoint. If the old span
were n−1 and the right endpoint moved alone, the new tagged slots would
coincide, contradicting surviving distinct original IDs. -/
theorem width_landing {p c n : Nat} (z : Ledger p c n) (e a b : Fin n)
    (old : a≠b) (distinctAfter : landing z e a≠landing z e b) :
    width (landing z e a) (landing z e b)=
      width a b+displacement z e b-displacement z e a := by
  let d := width a b
  let i := displacement z e a
  let j := displacement z e b
  have di : i≤1 := by unfold i displacement; split <;> omega
  have dj : j≤1 := by unfold j displacement; split <;> omega
  have dp : 0<d := width_pos old
  have dn : d<n := width_lt a b
  have U : liftedSite (landing z e a) (d+j-i)=landing z e b := by
    rw [lands z e a,lands z e b, lift_comp]
    change liftedSite a (i+(d+j-i))=liftedSite b j
    rw [show i+(d+j-i)=d+j by omega, ←lift_comp, width_lift]
  have D : d+j-i<n := by
    by_cases eq : d+j-i=n
    · rw [eq,wrap_self] at U
      exact (distinctAfter U).elim
    · omega
  exact width_unique _ _ D U

theorem width_one_mark {p c n : Nat} (z : Ledger p c n) (e a b : Fin n)
    (old : a≠b) (distinctAfter : landing z e a≠landing z e b) :
    width (landing z e a) (landing z e b)≤width a b+(if e=b then 1 else 0) := by
  rw [width_landing z e a b old distinctAfter]
  by_cases he : e=b
  · have C : displacement z e b≤1 := by unfold displacement; split <;> omega
    simp only [if_pos he]
    omega
  · simp only [displacement,moves,he,false_and,if_false]
    omega

/-- The physical instantiated form, with identity tracking supplied by
the live ledger and the selected-group-loss test, not by a position oracle. -/
theorem width_tagged_mark {p c n : Nat} (hn : 4≤n) (z : Ledger p c n)
    {init : Config p c n} (g : List (Fin n)) (e a b l r : Fin n)
    (hv : Valid z init) (hl : l∈g) (hr : r∈g) (distinct : l≠r)
    (ha : z.slots a=some l) (hb : z.slots b=some r)
    (keep : WindowLocal.selectedGroupLoss g z e=none) :
    (advance z e).slots (landing z e a)=some l ∧
      (advance z e).slots (landing z e b)=some r ∧
      width (landing z e a) (landing z e b)≤width a b+(if e=b then 1 else 0) := by
  have A := tracked_landing hn z g e a l hv.covers hl ha keep
  have B := tracked_landing hn z g e b r hv.covers hr hb keep
  change (advance z e).slots (landing z e a)=some l at A
  change (advance z e).slots (landing z e b)=some r at B
  have h0 : a≠b := by
    intro E
    exact distinct (Option.some.inj (ha.symm.trans (E.symm ▸ hb)))
  have h1 : landing z e a≠landing z e b := by
    intro E
    exact distinct (Option.some.inj (A.symm.trans (E.symm ▸ B)))
  exact ⟨A,B,width_one_mark z e a b h0 h1⟩

open WindowSpan in
theorem lap {p c n : Nat} (x : Config p c n) (r : Fin (RankPhysical.rank x)) :
    spanK x r (RankPhysical.rank x)=n := by
  let M := RankPhysical.rank x
  have mpos : 0<M := Nat.zero_lt_of_lt r.isLt
  have atZero : spanK x (⟨0,mpos⟩ : Fin M) M=n := by
    unfold spanK
    have z : ∀ j : Fin M, liftedSite (⟨0,mpos⟩ : Fin M) j.val=j := by
      intro j
      apply Fin.ext
      change (0+j.val)%M=j.val
      simp [Nat.mod_eq_of_lt j.isLt]
    simp only [z]
    exact gap_sum x mpos
  have shift (i : Fin M) : spanK x (rightNeighbor i) M=spanK x i M := by
    have A := spanK_add x i 1 M
    have B := spanK_succ x i M
    have lapEq : liftedSite i M=i := wrap_self i
    rw [Nat.add_comm 1 M] at A
    rw [B,lapEq,liftedSite_succ,liftedSite_zero] at A
    have G : spanK x i 1=gap x i := by
      simp only [spanK,Fin.val_zero,liftedSite_zero,TaggedTail.sumEdge,List.ofFn_succ,
        List.ofFn_zero,List.sum_cons,List.sum_nil,Nat.add_zero]
    rw [G] at A
    omega
  suffices T : ∀ (d : Nat) (hd : d<M), spanK x (⟨d,hd⟩ : Fin M) M=n from T r.val r.isLt
  intro d
  induction d with
  | zero => intro hd; exact atZero
  | succ d ih =>
    intro h
    have hd : d<M := by omega
    have Q : rightNeighbor (⟨d,hd⟩ : Fin M)=(⟨d+1,h⟩ : Fin M) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt h
    rw [←Q,shift,ih hd]

open WindowSpan in
theorem spanK_lt {p c n : Nat} (x : Config p c n) (r : Fin (RankPhysical.rank x))
    (d : Nat) (hd : d<RankPhysical.rank x) : spanK x r d<n := by
  let M := RankPhysical.rank x
  have cap : spanK x r (d+1)≤n := by
    have T := spanK_add x r (d+1) (M-(d+1))
    rw [show d+1+(M-(d+1))=M by omega,lap x r] at T
    omega
  rw [spanK_succ] at cap
  have P := gap_pos x (liftedSite r d)
  omega

open WindowSpan WindowRoster in
/-- For the anchored consecutive window, the true endpoint distance
equals its full six-gap span, not merely a lower or upper bound. -/
theorem width_roster {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (h : 7≤RankPhysical.rank x) :
    width (roster x i) (roster x (liftedSite i 6))=span x i :=
  width_unique _ _ (spanK_lt x i 6 (by omega)) (at_spanK x i 6)

end L4.WindowSpanEndpoints
