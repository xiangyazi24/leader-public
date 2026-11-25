import Leader.L4.QueueDAG
import Leader.L4.FIFOCompare
import Leader.L4.RankRootless

namespace L4.RootlessFIFO
open FIFOCompare RankRootless

/-- Rootless virtual line: no source, and a real slot at zero. -/
structure Line where
  stock : Nat → Bool
  departed : Nat

def Line.cross (width : Nat) (q : Line) : Nat → Nat :=
  cuts width q.stock q.departed

/-- The physical service of one oriented virtual bond; the far end absorbs. -/
def lineStep (width j : Nat) (q : Line) : Line :=
  if j < width ∧ q.stock j = true then
    if j+1 = width then ⟨setStock q.stock j false,q.departed+1⟩
    else if q.stock (j+1) then q
    else ⟨setStock (setStock q.stock j false) (j+1) true,q.departed⟩
  else q

/-- Whether the selected lifted bond effects a crossing before its step. -/
def enabled (width j : Nat) (q : Line) : Prop :=
  j < width ∧ q.stock j = true ∧ (j+1 = width ∨ q.stock (j+1) = false)

theorem crossing_exact (width j k : Nat) (q : Line) (hk : k ≤ width) :
    let q' := lineStep width j q
    (enabled width j q → q'.cross width k = q.cross width k + if k=j+1 then 1 else 0) ∧
    (¬ enabled width j q → q'.cross width k = q.cross width k) := by
  dsimp only
  by_cases hy : j<width ∧ q.stock j=true
  · rw [lineStep,if_pos hy]
    by_cases ho : j+1=width
    · rw [if_pos ho]
      refine ⟨fun _ => ?_,fun h => (h ⟨hy.1,hy.2,Or.inl ho⟩).elim⟩
      rw [Line.cross,Line.cross,cuts_outlet _ _ _ _ hy.2 ho _ hk,ho]
    · rw [if_neg ho]
      cases hB : q.stock (j+1)
      · simp only [Bool.false_eq_true,if_false]
        refine ⟨fun _ => ?_,fun h => (h ⟨hy.1,hy.2,Or.inr hB⟩).elim⟩
        exact cuts_move _ _ _ _ hy.2 hB (by omega) _
      · simp only [if_true]
        refine ⟨fun h => ?_,fun _ => True.intro⟩
        rcases h.2.2 with h | h
        · exact (ho h).elim
        · simp [hB] at h
  · rw [lineStep,if_neg hy]
    exact ⟨fun h => (hy ⟨h.1,h.2.1⟩).elim,fun _ => rfl⟩

/-- Write set of one lift service. The two copies of any raw bond are
disjoint, so the second lifted guard sees its original stock bits. -/
theorem lineStep_stock_frame (width j k : Nat) (q : Line) (h₀ : k ≠ j)
    (h₁ : k ≠ j+1) : (lineStep width j q).stock k = q.stock k := by
  unfold lineStep
  split
  · split
    · simp [setStock,h₀]
    · split
      · rfl
      · simp [setStock,h₀,h₁]
  · rfl

/-- Raw edge at offset j independently serves both translated copies
in the length-2n virtual line; no source is added. -/
def duplicatedStep (n j : Nat) (q : Line) : Line :=
  lineStep (2*n) (j+n) (lineStep (2*n) j q)

theorem duplicated_enabled_invariant (n j : Nat) (q : Line) (hn : 2 ≤ n) :
    enabled (2*n) (j+n) (lineStep (2*n) j q) ↔ enabled (2*n) (j+n) q := by
  unfold enabled
  rw [lineStep_stock_frame _ _ _ _ (by omega) (by omega),
      lineStep_stock_frame _ _ _ _ (by omega) (by omega)]

/-- Boolean-to-natural increments on the two possible, distinct cuts. -/
def pulse (width j : Nat) (q : Line) (k : Nat) : Nat :=
  if j < width ∧ q.stock j = true ∧ (j+1=width ∨ q.stock (j+1)=false) ∧ k=j+1
  then 1 else 0

private theorem cross_lineStep (width j k : Nat) (q : Line) (hk : k ≤ width) :
    (lineStep width j q).cross width k = q.cross width k + pulse width j q k := by
  have h := crossing_exact width j k q hk
  by_cases he : enabled width j q
  · rw [h.1 he]
    by_cases hk' : k=j+1
    · have h' : j<width ∧ q.stock j=true ∧
          (j+1=width ∨ q.stock (j+1)=false) ∧ k=j+1 := ⟨he.1,he.2.1,he.2.2,hk'⟩
      simp [pulse,h']
    · simp [pulse,hk']
  · rw [h.2 he]
    have hf : ¬(j<width ∧ q.stock j=true ∧
          (j+1=width ∨ q.stock (j+1)=false) ∧ k=j+1) :=
      fun h' => he ⟨h'.1,h'.2.1,h'.2.2.1⟩
    simp [pulse,hf]

/-- Same-mark selection changes just the two crossing cuts, not an
independent resampling in either translated copy. -/
theorem duplicated_cross (n j k : Nat) (q : Line) (hn : 2 ≤ n) (hk : k ≤ 2*n) :
    (duplicatedStep n j q).cross (2*n) k = q.cross (2*n) k +
      pulse (2*n) j q k + pulse (2*n) (j+n) q k := by
  unfold duplicatedStep
  rw [cross_lineStep _ _ _ _ hk,cross_lineStep _ _ _ _ hk]
  unfold pulse
  rw [lineStep_stock_frame _ _ _ _ (by omega) (by omega),
      lineStep_stock_frame _ _ _ _ (by omega) (by omega)]

/-- Real rootless interaction accounting permits seam relocation: any
forward shift of a resident only improves cuts. At a ready donor on either
lift, the real service makes the corresponding crossing. -/
structure LiftResponses (width a b : Nat) (r : Line) (next : Nat → Nat) : Prop where
  monotone : ∀ k, k≤width → r.cross width k ≤ next k
  ready : ∀ j, (j=a ∨ j=b) → j<width → r.stock j=true →
    (j+1=width ∨ r.stock (j+1)=false) →
    r.cross width (j+1)+1 ≤ next (j+1)
  mass : next 0 = r.cross width 0

private theorem tight_ready (width j : Nat) (r v : Line)
    (hOrder : ∀ k, k≤width → v.cross width k ≤ r.cross width k)
    (he : enabled width j v) (heq : r.cross width (j+1) = v.cross width (j+1)) :
    r.stock j=true ∧ (j+1=width ∨ r.stock (j+1)=false) := by
  have hv := cuts_adjacent width v.stock v.departed j he.1
  have hr := cuts_adjacent width r.stock r.departed j he.1
  change v.cross width j = (v.stock j).toNat + v.cross width (j+1) at hv
  change r.cross width j = (r.stock j).toNat + r.cross width (j+1) at hr
  have hd : r.stock j=true := by
    cases hR : r.stock j
    · have hw := he.1
      have hh := hOrder j (by omega)
      rw [he.2.1] at hv
      rw [hR] at hr
      change v.cross width j = 1+v.cross width (j+1) at hv
      change r.cross width j = 0+r.cross width (j+1) at hr
      omega
    · rfl
  refine ⟨hd,?_⟩
  rcases he.2.2 with h|h
  · exact Or.inl h
  · by_cases hh : j+1=width
    · exact Or.inl hh
    · right
      have hlt : j+1<width := by have := he.1; omega
      have hv := cuts_adjacent width v.stock v.departed (j+1) hlt
      have hr := cuts_adjacent width r.stock r.departed (j+1) hlt
      change v.cross width (j+1) = (v.stock (j+1)).toNat + v.cross width (j+2) at hv
      change r.cross width (j+1) = (r.stock (j+1)).toNat + r.cross width (j+2) at hr
      cases hR : r.stock (j+1)
      · rfl
      · have hh := hOrder (j+2) (by omega)
        rw [h] at hv
        rw [hR] at hr
        change v.cross width (j+1) = 0+v.cross width (j+2) at hv
        change r.cross width (j+1) = 1+r.cross width (j+2) at hr
        omega

/-- Same-mark slack audit. The two virtual copies can both be
enabled, but cannot both be tight: tightness forces the contributing
sender into the single real window. This includes its rightmost sender,
whose outlet service can be a payment at the moving seam. -/
theorem simultaneous_copies_not_both_tight (n j first : Nat) (_hn : 2≤n)
    (v r : Line)
    (hSupport : ∀ k, r.stock k = true → first≤k ∧ k<first+n)
    (hOrder : ∀ k, k≤2*n → v.cross (2*n) k≤r.cross (2*n) k)
    (h₀ : enabled (2*n) j v) (h₁ : enabled (2*n) (j+n) v) :
    ¬ (r.cross (2*n) (j+1)=v.cross (2*n) (j+1) ∧
       r.cross (2*n) (j+n+1)=v.cross (2*n) (j+n+1)) := by
  rintro ⟨ht₀,ht₁⟩
  have hs₀ := hSupport j (tight_ready (2*n) j r v hOrder h₀ ht₀).1
  have hs₁ := hSupport (j+n) (tight_ready (2*n) (j+n) r v hOrder h₁ ht₁).1
  omega

/-- When one simultaneous copy is tight the other spends at most one
unit of its *own* integer slack. -/
theorem simultaneous_second_has_slack (n j first : Nat) (hn : 2≤n)
    (v r : Line)
    (hSupport : ∀ k, r.stock k = true → first≤k ∧ k<first+n)
    (hOrder : ∀ k, k≤2*n → v.cross (2*n) k≤r.cross (2*n) k)
    (h₀ : enabled (2*n) j v) (h₁ : enabled (2*n) (j+n) v)
    (ht : r.cross (2*n) (j+1)=v.cross (2*n) (j+1)) :
    v.cross (2*n) (j+n+1)+1≤r.cross (2*n) (j+n+1) := by
  have hs : j+n+1≤2*n := by have := h₁.1; omega
  have ho := hOrder (j+n+1) hs
  have hne : r.cross (2*n) (j+n+1) ≠ v.cross (2*n) (j+n+1) :=
    fun he => simultaneous_copies_not_both_tight n j first hn v r hSupport hOrder h₀ h₁ ⟨ht,he⟩
  omega

/-- Comparison with both physical copies served. Every cut can require
at most one new unit; at tightness its corresponding real crossing is
forced. This avoids any false clock independence at translated bonds. -/
theorem duplicated_compare (n j : Nat) (hn : 2≤n) (v r : Line) (next : Nat → Nat)
    (hOrder : ∀ k, k≤2*n → v.cross (2*n) k ≤ r.cross (2*n) k)
    (hReal : LiftResponses (2*n) j (j+n) r next) :
    ∀ k, k≤2*n → (duplicatedStep n j v).cross (2*n) k ≤ next k := by
  intro k hk
  rw [duplicated_cross n j k v hn hk]
  let a := j
  let b := j+n
  have diff : a+1 ≠ b+1 := by dsimp [a,b]; omega
  have bump (l : Nat) (hil : l=a ∨ l=b) (he : enabled (2*n) l v) (hk' : k=l+1) :
      v.cross (2*n) k + 1 ≤ next k := by
    subst k
    by_cases heq : r.cross (2*n) (l+1) = v.cross (2*n) (l+1)
    · have hT := tight_ready (2*n) l r v hOrder he heq
      have hh := hReal.ready l hil he.1 hT.1 hT.2
      omega
    · have hh := hOrder (l+1) hk
      have hR := hReal.monotone (l+1) hk
      omega
  change v.cross (2*n) k + pulse (2*n) a v k + pulse (2*n) b v k ≤ next k
  unfold pulse
  split
  · rename_i hA
    have hf : ¬ (b<2*n ∧ v.stock b=true ∧
        (b+1=2*n ∨ v.stock (b+1)=false) ∧ k=b+1) := fun hB =>
        diff (hA.2.2.2.symm.trans hB.2.2.2)
    rw [if_neg hf,Nat.add_zero]
    exact bump a (Or.inl rfl) ⟨hA.1,hA.2.1,hA.2.2.1⟩ hA.2.2.2
  · split
    · rename_i hB
      rw [Nat.add_zero]
      exact bump b (Or.inr rfl) ⟨hB.1,hB.2.1,hB.2.2.1⟩ hB.2.2.2
    · simp only [Nat.add_zero]
      exact Nat.le_trans (hOrder k hk) (hReal.monotone k hk)

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.duplicated_cross
#print axioms L4.RootlessFIFO.duplicated_compare
#print axioms L4.RootlessFIFO.simultaneous_copies_not_both_tight
#print axioms L4.RootlessFIFO.simultaneous_second_has_slack

namespace L4.RootlessFIFO
open FIFOCompare

/-- The exact rootless virtual line conserves occupied-plus-departed;
no translated service is an injection. -/
theorem line_mass (width j : Nat) (q : Line) :
    (lineStep width j q).cross width 0 = q.cross width 0 := by
  have h := crossing_exact width j 0 q (Nat.zero_le _)
  by_cases he : enabled width j q
  · simpa using h.1 he
  · exact h.2 he

theorem duplicated_mass (n j : Nat) (q : Line) :
    (duplicatedStep n j q).cross (2*n) 0 = q.cross (2*n) 0 := by
  simp [duplicatedStep,line_mass]

/-- A forward relocation into a fresh slot can only improve cumulative
crossings. This is the exposed-resident seam rewrite, not a new token. -/
theorem seam_relocate_ge (width i j : Nat) (q : Line)
    (hi : q.stock i = true) (hj : q.stock j = false) (hij : i < j) (hW : j<width) :
    ∀ k, q.cross width k ≤
      cuts width (setStock (setStock q.stock i false) j true) q.departed k := by
  intro k
  have hL := cuts_set width q.stock q.departed i false k
  have hJ := cuts_inject width (setStock q.stock i false) q.departed j
    (by simp [setStock,show j≠i by omega,hj]) hW k
  have hI : i<width := by omega
  change cuts width q.stock q.departed k ≤ _
  simp only [hi,hI,and_true,Bool.toNat_true,Bool.toNat_false] at hL
  by_cases hK : k≤i
  · have hK' : k≤j := by omega
    simp [hK,hK'] at hL hJ
    omega
  · by_cases hJk : k≤j
    · simp [hK,hJk] at hL hJ; omega
    · simp [hK,hJk] at hL hJ; omega

/-- A single occupied coordinate contributes at least one to every
earlier cut. -/
theorem stock_pos_from {width j k : Nat} {s : Nat → Bool}
    (hj : j<width) (hk : k≤j) (hs : s j=true) :
    1 ≤ tailSlots width s k := by
  rw [tailSlots,if_pos (by omega : k<width)]
  by_cases h : k=j
  · subst k; simp [hs]
  · have hh := stock_pos_from hj (by omega : k+1≤j) hs
    omega
termination_by j-k
decreasing_by omega

/-- Once the exactly matched virtual queue is drained, cumulative
domination at the sink and the original real token cap force all real
lifted stock to be absent. No equality of individual lifetimes is used. -/
theorem drain_from_outlet (width initial : Nat) (r v : Line)
    (hBudget : r.cross width 0 ≤ initial)
    (hDep : initial ≤ v.departed)
    (hDom : v.cross width width ≤ r.cross width width) :
    ∀ j, j<width → r.stock j=false := by
  have hD : v.departed ≤ r.departed := by
    simpa [Line.cross,cuts_far width _ _ width (Nat.le_refl _)] using hDom
  intro j hj
  cases hs : r.stock j
  · rfl
  · have hStock := stock_pos_from hj (Nat.zero_le _) hs
    unfold Line.cross cuts at hBudget
    omega

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.seam_relocate_ge
#print axioms L4.RootlessFIFO.drain_from_outlet

namespace L4.RootlessFIFO
open FIFOCompare RankRootless

/-- Real residue lift when the tracked ghost has advanced d times. The
physical ghost's own stock is represented at d, not at the absorbing
endpoint n+d. All other physical sites occur once in this window. -/
def liftedStock {p c n : Nat} (x : Config p c n) (g : Fin n) (d k : Nat) : Bool :=
  if d ≤ k ∧ k < n+d then (x (liftedSite g k)).stock else false

def liftReal {p c n : Nat} (x : Config p c n) (g : Fin n) (d paid : Nat) : Line :=
  ⟨liftedStock x g d,paid⟩

/-- With physical configuration fixed, increasing the window by one
moves only the former leftmost resident, from d to n+d. -/
theorem window_advance_stock {p c n : Nat} (x : Config p c n) (g : Fin n) (d : Nat) :
    liftedStock x g (d+1) =
      setStock (setStock (liftedStock x g d) d false) (n+d)
        (x (liftedSite g d)).stock := by
  funext k
  have hn : 0<n := Nat.zero_lt_of_lt g.isLt
  have liftwrap : liftedSite g (n+d) = liftedSite g d := by
    apply Fin.ext
    change (g.val + (n+d))%n = (g.val+d)%n
    rw [show g.val+(n+d)=g.val+d+n by omega,Nat.add_mod_right]
  by_cases hA : k=n+d
  · subst k
    simp [liftedStock,setStock,liftwrap,show d+1≤n+d by omega,
      show n+d<n+(d+1) by omega]
  · by_cases hB : k=d
    · subst k
      simp [liftedStock,setStock,show n ≠ 0 by omega,show ¬ d+1≤d by omega]
    · have hwin : (d+1≤k ∧ k<n+(d+1)) ↔ (d≤k ∧ k<n+d) := by omega
      simp [liftedStock,setStock,hA,hB,hwin]

/-- In the window used before the stop the seam relabel is forward. It
never blocks the virtual line and never creates a real token. -/
theorem window_advance_cross_ge {p c n : Nat} (x : Config p c n) (g : Fin n)
    (d paid : Nat) (hd : d<n) :
    ∀ k, (liftReal x g d paid).cross (2*n) k ≤
      (liftReal x g (d+1) paid).cross (2*n) k := by
  intro k
  have hn : 0<n := by omega
  rw [Line.cross,Line.cross]
  change cuts (2*n) (liftedStock x g d) paid k ≤ cuts (2*n) (liftedStock x g (d+1)) paid k
  rw [window_advance_stock]
  have hOut : liftedStock x g d (n+d) = false := by simp [liftedStock]
  cases h : (x (liftedSite g d)).stock
  · have hD : liftedStock x g d d = false := by
      simp [liftedStock,h,show d<n+d by omega]
    have h₀ : setStock (liftedStock x g d) d false = liftedStock x g d := by
      rw [← hD,setStock_same]
    rw [h₀,← hOut,setStock_same]
    exact Nat.le_refl _
  · have hD : liftedStock x g d d = true := by
      simp [liftedStock,h,show d<n+d by omega]
    exact seam_relocate_ge (2*n) d (n+d) (liftReal x g d paid)
      hD hOut (by omega) (by omega) k

theorem window_advance_mass {p c n : Nat} (x : Config p c n) (g : Fin n)
    (d paid : Nat) (hd : d<n) :
    (liftReal x g (d+1) paid).cross (2*n) 0 = (liftReal x g d paid).cross (2*n) 0 := by
  rw [Line.cross,Line.cross]
  change cuts (2*n) (liftedStock x g (d+1)) paid 0 = cuts (2*n) (liftedStock x g d) paid 0
  rw [window_advance_stock]
  have hOut : liftedStock x g d (n+d) = false := by simp [liftedStock]
  have hD : liftedStock x g d d = (x (liftedSite g d)).stock := by
    simp [liftedStock,show d<n+d by omega]
  have hd0 : d<2*n := by omega
  have hn0 : n+d<2*n := by omega
  have h₁ := cuts_set (2*n) (liftedStock x g d) paid d false 0
  have h₂ := cuts_set (2*n) (setStock (liftedStock x g d) d false) paid (n+d)
    (x (liftedSite g d)).stock 0
  simp [hD,hd0] at h₁
  simp [setStock,hOut,hn0] at h₂
  omega

/-- A rootless physical lift update needs only the fixed head fence and
the local P2/P3 stock rows. This is the literal residual for the real
side of the two-copy FIFO; the virtual side is already kernel checked. -/
def ConcreteLiftResponses : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (g j : Fin n) (d paid : Nat),
    4≤n → d≤n → MCOV x → NoLiving x →
    (x (RearTrace.predecessor (liftedSite g d))).mark = true →
    let e := liftedSite g j.val
    let q := (geometricPay (x e) (x (rightNeighbor e))).toNat
    let δ := if rightNeighbor e = liftedSite g d then q else 0
    d+δ≤n →
    LiftResponses (2*n) j.val (j.val+n) (liftReal x g d paid)
      ((liftReal (step x e) g (d+δ) (paid+q)).cross (2*n))

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.window_advance_stock
#print axioms L4.RootlessFIFO.window_advance_cross_ge

namespace L4.RootlessFIFO
open FIFOCompare RankRootless StockTokenRows

private theorem covered_mat {p c : Nat} (u v : Site p c)
    (h : (v.leader = true ∨ v.residue ≠ nextResidue u.residue) → u.mark = true) :
    materialize u v = u := by
  by_cases hm : u.mark=true
  · cases u; simp_all [materialize]
  · have hM := Bool.eq_false_iff.mpr hm
    have hL : v.leader=false := Bool.eq_false_iff.mpr (fun hL => hm (h (Or.inl hL)))
    have hr : v.residue=nextResidue u.residue := Classical.not_not.mp (fun hh => hm (h (Or.inr hh)))
    simp [materialize,hL,hM,defect,hr]

private theorem rootless_native {p c : Nat} (u v : Site p c) (hu : u.leader=false)
    (hv : v.leader=false) :
    let z := native u v
    z.1.mark=u.mark ∧ z.1.stock=u.stock ∧ z.2.stock=v.stock ∧
      z.1.leader=false ∧ z.2.leader=false := by
  unfold native
  rw [show fireInitiator u = u by simp [fireInitiator,hu],
      show fireResponder v = v by simp [fireResponder,hv],
      show impact u v = (u,v) by simp [impact,hv]]
  dsimp only
  unfold followerBullet
  split
  · split <;> exact ⟨rfl,rfl,rfl,hu,hv⟩
  · exact ⟨rfl,rfl,rfl,hu,hv⟩

/-- Rootless covered local pair: marked stock is consumed, unmarked
stock moves iff the receiving slot is empty, and no row adds a token. -/
theorem rootless_pair_exact {p c : Nat} (u v : Site p c) (hu : u.leader=false)
    (hv : v.leader=false)
    (hh : (v.leader = true ∨ v.residue ≠ nextResidue u.residue) → u.mark=true) :
    geometricPay u v = (u.mark && u.stock) ∧
    ((pairStep u v).1.stock,(pairStep u v).2.stock) =
      (if u.mark && u.stock then (false,v.stock)
       else if !u.mark && u.stock && !v.stock then (false,true)
       else (u.stock,v.stock)) := by
  have hM := covered_mat u v hh
  have hN := rootless_native u v hu hv
  dsimp only at hN
  have hPay : geometricPay u v = (u.mark && u.stock) := by
    simp [geometricPay,hM,hN.1,hN.2.1,hN.2.2.2.1,hN.2.2.2.2,payer]
  refine ⟨hPay,?_⟩
  let l : Option Unit := if u.stock then some () else none
  let r : Option Unit := if v.stock then some () else none
  have hL : l.isSome = u.stock := by cases h : u.stock <;> simp [l,h]
  have hR : r.isSome = v.stock := by cases h : v.stock <;> simp [r,h]
  have hA : row u v = (if u.mark && u.stock then .drop
    else if !u.mark && u.stock && !v.stock then .transfer else .stay) := by
    unfold row action
    rw [hM]
    simp [hN.1,hN.2.1,hN.2.2.1,hN.2.2.2.1,hN.2.2.2.2,payer]
    cases u.mark <;> cases u.stock <;> cases v.stock <;> decide
  have hV := pair_labels u v l r () hL hR
  rw [hA] at hV
  rw [← hV]
  cases huM : u.mark <;> cases huS : u.stock <;> cases hvS : v.stock <;>
    simp [update,l,r,huS,hvS]

private theorem lift_add {n : Nat} (g : Fin n) (a b : Nat) :
    liftedSite (liftedSite g a) b = liftedSite g (a+b) := by
  apply Fin.ext
  change (((g.val+a)%n)+b)%n = (g.val+(a+b))%n
  rw [Nat.mod_add_mod,Nat.add_assoc]

private theorem lift_wrap {n : Nat} (g : Fin n) (a : Nat) :
    liftedSite g (a+n) = liftedSite g a := by
  rw [← lift_add,liftedSite_full]

private theorem window_inj {n : Nat} (g : Fin n) {d a b : Nat}
    (ha₀ : d≤a) (ha₁ : a<d+n) (hb₀ : d≤b) (hb₁ : b<d+n)
    (h : liftedSite g a = liftedSite g b) : a=b := by
  have h' : liftedSite (liftedSite g d) (a-d) = liftedSite (liftedSite g d) (b-d) := by
    rw [lift_add,lift_add,show d+(a-d)=a by omega,show d+(b-d)=b by omega]
    exact h
  have eq := liftedSite_inj (liftedSite g d) (by omega : a-d<n) (by omega : b-d<n) h'
  omega

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.rootless_pair_exact

namespace L4.RootlessFIFO
open FIFOCompare RankRootless

private theorem raw_no_self {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have H : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hEq := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) H
  omega

private theorem step_stock_payment {p c n : Nat} (_hn : 4≤n) (x : Config p c n) (e : Fin n)
    (h : (pairStep (x e) (x (rightNeighbor e))).1.stock=false ∧
      (pairStep (x e) (x (rightNeighbor e))).2.stock=(x (rightNeighbor e)).stock) :
    ∀ i, (step x e i).stock = if i=e then false else (x i).stock := by
  intro i
  by_cases he : i=e
  · subst i; simp [step,h.1]
  · by_cases hv : i=rightNeighbor e
    · subst i; simp [step,he,h.2]
    · simp [step,he,hv]

private theorem step_stock_transport {p c n : Nat} (_hn : 4≤n) (x : Config p c n) (e : Fin n)
    (h : (pairStep (x e) (x (rightNeighbor e))).1.stock=false ∧
      (pairStep (x e) (x (rightNeighbor e))).2.stock=true) :
    ∀ i, (step x e i).stock = if i=e then false else if i=rightNeighbor e then true else (x i).stock := by
  intro i
  by_cases he : i=e
  · subst i; simp [step,h.1]
  · by_cases hv : i=rightNeighbor e
    · subst i; simp [step,he,h.2]
    · simp [step,he,hv]

private theorem step_stock_idle {p c n : Nat} (x : Config p c n) (e : Fin n)
    (h : (pairStep (x e) (x (rightNeighbor e))).1.stock=(x e).stock ∧
      (pairStep (x e) (x (rightNeighbor e))).2.stock=(x (rightNeighbor e)).stock) :
    ∀ i, (step x e i).stock=(x i).stock := by
  intro i
  by_cases he : i=e
  · subst i; simp [step,h.1]
  · by_cases hv : i=rightNeighbor e
    · subst i; simp [step,he,h.2]
    · simp [step,he,hv]

private theorem lifted_clear {p c n : Nat} (x y : Config p c n) (g : Fin n) (d l : Nat)
    (h₀ : d≤l) (h₁ : l<n+d)
    (h : ∀ i, (y i).stock = if i=liftedSite g l then false else (x i).stock) :
    liftedStock y g d = setStock (liftedStock x g d) l false := by
  funext k
  by_cases hk : d≤k ∧ k<n+d
  · by_cases he : k=l
    · subst k; simp [liftedStock,setStock,h,hk]
    · have hn : liftedSite g k ≠ liftedSite g l := fun ho =>
        he (window_inj g hk.1 (by omega) h₀ (by omega) ho)
      simp [liftedStock,setStock,h,hk,hn,he]
  · have hl : k ≠ l := fun he => hk (he.symm ▸ ⟨h₀,h₁⟩)
    simp [liftedStock,setStock,hk,hl]

private theorem lifted_move {p c n : Nat} (x y : Config p c n) (g : Fin n) (d l : Nat)
    (h₀ : d≤l) (h₁ : l+1<n+d)
    (h : ∀ i, (y i).stock = if i=liftedSite g l then false else
        if i=liftedSite g (l+1) then true else (x i).stock) :
    liftedStock y g d = setStock (setStock (liftedStock x g d) l false) (l+1) true := by
  funext k
  by_cases hk : d≤k ∧ k<n+d
  · have criterion (a : Nat) (ha₀ : d≤a) (ha₁ : a<n+d) :
        liftedSite g k = liftedSite g a ↔ k=a :=
      ⟨fun he => window_inj g hk.1 (by omega) ha₀ (by omega) he, congrArg _⟩
    have hL := criterion l h₀ (by omega)
    have hR := criterion (l+1) (by omega) h₁
    by_cases he : k=l <;> by_cases hv : k=l+1 <;>
      simp [liftedStock,setStock,h,hk,hL,hR,he,hv] <;> omega
  · have hl : k≠l := fun he => hk (he.symm ▸ ⟨h₀,by omega⟩)
    have hv : k≠l+1 := fun he => hk (he.symm ▸ ⟨by omega,h₁⟩)
    simp [liftedStock,setStock,hk,hl,hv]

private theorem lifted_idle {p c n : Nat} (x y : Config p c n) (g : Fin n) (d : Nat)
    (h : ∀ i, (y i).stock=(x i).stock) :
    liftedStock y g d = liftedStock x g d := by funext i; simp [liftedStock,h]

end L4.RootlessFIFO

namespace L4.RootlessFIFO
open FIFOCompare RankRootless

/-- The actual rootless pair supplies both lifted-cut responses without
pausing, by transporting the exposed resident to its new lift. The cap
is a pre/post displacement bound, obtained from the rootless stock ledger. -/
theorem concreteLiftResponses : ConcreteLiftResponses := by
  intro p c n x g j d paid hn hD hm hl hHead
  dsimp only
  let a := j.val
  let e := liftedSite g a
  let b := rightNeighbor e
  let l := if d≤a then a else a+n
  let y := step x e
  have hA : a<n := j.isLt
  have hl₀ : d≤l := by dsimp [l]; split <;> omega
  have hl₁ : l<n+d := by dsimp [l]; split <;> omega
  have hls : l<2*n := by omega
  have hle : liftedSite g l=e := by
    dsimp [l,e]
    split
    · rfl
    · apply lift_wrap
  have hln : liftedSite g (l+1)=b := by rw [liftedSite_succ,hle]
  have hx := rootless_pair_exact (x e) (x b) (hl e) (hl b) (hm e)
  have hlSt : liftedStock x g d l = (x e).stock := by
    simp [liftedStock,hl₀,hl₁,hle]
  have canon (k : Nat) (hk : k=a ∨ k=a+n)
      (hS : (liftReal x g d paid).stock k=true) : k=l := by
    change liftedStock x g d k=true at hS
    have hw : d≤k ∧ k<n+d := by
      by_cases h : d≤k ∧ k<n+d
      · exact h
      · simp [liftedStock,h] at hS
    rcases hk with hk|hk
    · rw [hk] at hw ⊢
      exact (if_pos hw.1).symm
    · rw [hk] at hw ⊢
      have h : ¬ d≤a := by omega
      exact (if_neg h).symm
  have fence : l+1=n+d → (x e).mark=true := by
    intro hh
    have he : b=liftedSite g d := by
      rw [← hln,hh,Nat.add_comm,lift_wrap]
    have hEq : e=RearTrace.predecessor (liftedSite g d) := by
      rw [← he,RearTrace.predecessor_right]
    rw [hEq]
    exact hHead
  change d+(if b=liftedSite g d then (geometricPay (x e) (x b)).toNat else 0) ≤ n → _
  intro hcap
  by_cases hp : ((x e).mark && (x e).stock) = true
  · have hP : geometricPay (x e) (x b) = true := hx.1.trans hp
    have hh : ((pairStep (x e) (x b)).1.stock,(pairStep (x e) (x b)).2.stock) =
        (false,(x b).stock) := by rw [hx.2,if_pos hp]
    have hY : liftedStock y g d = setStock (liftedStock x g d) l false := by
      apply lifted_clear x y g d l hl₀ hl₁
      rw [hle]
      exact step_stock_payment hn x e ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
    have hS : liftedStock x g d l = true := hlSt.trans (Bool.and_eq_true_iff.mp hp).2
    let δ := if b=liftedSite g d then 1 else 0
    have hδ : d+δ ≤ n := by simpa [hP,δ] using hcap
    have hAdvance : ∀ k, (liftReal y g d (paid+1)).cross (2*n) k ≤
        (liftReal y g (d+δ) (paid+1)).cross (2*n) k := by
      intro k
      by_cases he : b=liftedSite g d
      · have hδ1 : δ=1 := if_pos he
        rw [hδ1]
        rw [hδ1] at hδ
        exact window_advance_cross_ge y g d (paid+1) (by omega) k
      · have hδ0 : δ=0 := if_neg he
        rw [hδ0,Nat.add_zero]
        exact Nat.le_refl _
    have hAbs (k : Nat) : (liftReal y g d (paid+1)).cross (2*n) k =
        (liftReal x g d paid).cross (2*n) k + (if l<k then 1 else 0) := by
      simp only [Line.cross,liftReal,hY]
      rw [cuts_absorb _ _ _ _ hS hls]
    have out : LiftResponses (2*n) a (a+n) (liftReal x g d paid)
        ((liftReal y g (d+δ) (paid+1)).cross (2*n)) := by
      constructor
      · intro k _
        have ha := hAdvance k
        have hb := hAbs k
        omega
      · intro k hk _ hToken _
        have hEq := canon k hk hToken
        subst k
        have hb := hAbs (l+1)
        have ha := hAdvance (l+1)
        rw [if_pos (by omega : l<l+1)] at hb
        omega
      · have hZero := hAbs 0
        simp at hZero
        by_cases he : b=liftedSite g d
        · have hδ1 : δ=1 := if_pos he
          rw [hδ1]
          rw [hδ1] at hδ
          rw [window_advance_mass y g d (paid+1) (by omega)]
          exact hZero
        · have hδ0 : δ=0 := if_neg he
          rw [hδ0,Nat.add_zero]
          exact hZero
    simpa [hP,δ,a,e,b,y] using out
  · have hP : geometricPay (x e) (x b) = false := hx.1.trans (Bool.eq_false_iff.mpr hp)
    by_cases hT : (!(x e).mark && (x e).stock && !(x b).stock) = true
    · have hNo : (x e).mark=false := by
        cases ht : (x e).mark <;> simp_all
      have hL : l+1<n+d := by
        by_cases hh : l+1=n+d
        · have hx := fence hh; simp [hNo] at hx
        · omega
      have hW : l+1<2*n := by omega
      have hTok : (x e).stock=true := by
        cases ht : (x e).stock <;> simp_all
      have hVac : (x b).stock=false := by
        cases ht : (x b).stock <;> simp_all
      have hh : ((pairStep (x e) (x b)).1.stock,(pairStep (x e) (x b)).2.stock) =
          (false,true) := by rw [hx.2,if_neg hp,if_pos hT]
      have hY : liftedStock y g d = setStock (setStock (liftedStock x g d) l false) (l+1) true := by
        apply lifted_move x y g d l hl₀ hL
        rw [hle,hln]
        exact step_stock_transport hn x e ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
      have hMove (k : Nat) : (liftReal y g d paid).cross (2*n) k =
          (liftReal x g d paid).cross (2*n) k + if k=l+1 then 1 else 0 := by
        simp only [Line.cross,liftReal,hY]
        have hS : liftedStock x g d (l+1)=false := by
          simp [liftedStock,show d≤l+1 by omega,hL,hln,hVac]
        exact cuts_move _ _ _ _ (hlSt.trans hTok) hS hW k
      have out : LiftResponses (2*n) a (a+n) (liftReal x g d paid)
          ((liftReal y g d paid).cross (2*n)) := by
        constructor
        · intro k _
          have hh := hMove k; omega
        · intro k hk _ hToken _
          have hEq := canon k hk hToken
          subst k
          simp [hMove]
        · simpa using hMove 0
      simpa [hP,a,e,b,y] using out
    · have hh : ((pairStep (x e) (x b)).1.stock,(pairStep (x e) (x b)).2.stock) =
          ((x e).stock,(x b).stock) := by rw [hx.2,if_neg hp,if_neg hT]
      have hY : liftedStock y g d = liftedStock x g d :=
        lifted_idle x y g d (step_stock_idle x e ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩)
      have eq : (liftReal y g d paid).cross (2*n) = (liftReal x g d paid).cross (2*n) := by
        simp [Line.cross,liftReal,hY]
      have out : LiftResponses (2*n) a (a+n) (liftReal x g d paid)
          ((liftReal y g d paid).cross (2*n)) := by
        constructor
        · intro k _; rw [eq]; exact Nat.le_refl _
        · intro k hk _ hToken hRoom
          have hEq := canon k hk hToken
          subst k
          have hDonor : (x e).stock=true := hlSt.symm.trans hToken
          have hm0 : (x e).mark=false := by cases H : (x e).mark <;> simp_all
          have hInside : l+1<n+d := by
            by_cases hh : l+1=n+d
            · have hx := fence hh; simp [hm0] at hx
            · omega
          have hvac : liftedStock x g d (l+1)=false := by
            rcases hRoom with hRoom|hRoom
            · omega
            · exact hRoom
          have hV : (x b).stock=false := by
            simpa [liftedStock,show d≤l+1 by omega,hInside,hln] using hvac
          exact False.elim (hT (by simp [hm0,hDonor,hV]))
        · exact congrFun eq 0
      simpa [hP,a,e,b,y] using out

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.concreteLiftResponses

namespace L4.RootlessFIFO
open QueueDAG FIFOCompare RankRootless

/-- Translate one raw edge into its two competing copies by using the
existing finite lift search; no independent mark is sampled. -/
def rawLiftStep {n : Nat} (g : Fin n) (q : Line) (e : Fin n) : Line :=
  match (List.finRange n).find? (fun k => liftedSite g k.val == e) with
  | none => q
  | some k => duplicatedStep n k.val q

private theorem raw_fin_bond {n : Nat} (g i : Fin n) :
    ((List.finRange n).find? (fun r => liftedSite g r.val == liftedSite g i.val)) = some i := by
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp,i.val,by simp,by simp,?_⟩
  intro j hj
  simp only [List.getElem_finRange,Fin.val_cast]
  change (!(liftedSite g j == liftedSite g i.val)) = true
  have hNe : liftedSite g j ≠ liftedSite g i.val := by
    intro h
    have hEq := liftedSite_inj g (by omega : j<n) i.isLt h
    omega
  simp [hNe]

private theorem raw_at_offset {n : Nat} (g : Fin n) (q : Line) (i : Nat) :
    rawLiftStep g q (liftedSite g i) = duplicatedStep n (i%n) q := by
  let k : Fin n := ⟨i%n,Nat.mod_lt _ (Nat.zero_lt_of_lt g.isLt)⟩
  have he : liftedSite g i = liftedSite g k.val := by
    apply Fin.ext
    change (g.val+i)%n = (g.val+i%n)%n
    rw [Nat.add_mod_mod]
  rw [he,rawLiftStep,raw_fin_bond]

private theorem raw_cross_mono {n : Nat} (hn : 2≤n) (g : Fin n) (q : Line)
    (e : Fin n) (k : Nat) (hk : k≤2*n) :
    q.cross (2*n) k ≤ (rawLiftStep g q e).cross (2*n) k := by
  obtain ⟨j,hj,he⟩ := liftedSite_of_site g e
  rw [← he,raw_at_offset,duplicated_cross _ _ _ _ hn hk]
  omega

private theorem raw_mass {n : Nat} (g : Fin n) (q : Line) (e : Fin n) :
    (rawLiftStep g q e).cross (2*n) 0 = q.cross (2*n) 0 := by
  obtain ⟨j,hj,he⟩ := liftedSite_of_site g e
  rw [← he,raw_at_offset,duplicated_mass]

private theorem raw_improves {n : Nat} (hn : 2≤n) (g : Fin n) (q : Line) (i : Nat)
    (hi : enabled (2*n) i q) :
    q.cross (2*n) (i+1)+1 ≤ (rawLiftStep g q (liftedSite g i)).cross (2*n) (i+1) := by
  have hI := hi.1
  rw [raw_at_offset,duplicated_cross _ _ _ _ hn (by omega : i+1≤2*n)]
  by_cases h : i<n
  · rw [Nat.mod_eq_of_lt h]
    unfold pulse
    rw [if_pos ⟨hi.1,hi.2.1,hi.2.2,rfl⟩]
    omega
  · have heq : i%n + n = i := by
      rw [Nat.mod_eq_sub_mod (by omega : n≤i),Nat.mod_eq_of_lt (by omega : i-n<n)]
      omega
    simp only [heq]
    unfold pulse
    have hPos : i<2*n ∧ q.stock i=true ∧
        (i+1=2*n ∨ q.stock (i+1)=false) ∧ i+1=i+1 := ⟨hi.1,hi.2.1,hi.2.2,rfl⟩
    rw [if_pos hPos]
    omega

/-- Dependency tree for reaching a crossing threshold: k particles at
cut j. At cut zero there is no source, only conserved initial inventory.
The amount k therefore remains capped by that initial inventory. -/
def drainTree {n : Nat} (width : Nat) (edge : Nat → Fin n) (k j : Nat) : Tree n :=
  if k=0 ∨ j=0 then .done
  else .fork (edge (j-1)) (drainTree width edge k (j-1))
    (if j<width then drainTree width edge (k-1) (j+1) else .done)
termination_by 2*k+j
decreasing_by
  all_goals
    have hk' : k ≠ 0 := fun hh => (by assumption : ¬ (k=0 ∨ j=0)) (Or.inl hh)
    omega

theorem drainTree_span {n : Nat} (width : Nat) (edge : Nat → Fin n) (k j : Nat) :
    (drainTree width edge k j).depth ≤ 2*k+j := by
  rw [drainTree]
  split
  · simp [Tree.depth]
  · simp only [Tree.depth]
    have hL := drainTree_span width edge k (j-1)
    split
    · have hR := drainTree_span width edge (k-1) (j+1)
      omega
    · simp [Tree.depth]
      omega
termination_by 2*k+j
decreasing_by
  all_goals
    have hk' : k ≠ 0 := fun hh => (by assumption : ¬ (k=0 ∨ j=0)) (Or.inl hh)
    omega

/-- Both translated edges share the raw mark. The dependency proof
requires only monotonicity and service of each enabled copy on that mark. -/
theorem drainTree_sound {n : Nat} (hn : 2≤n) (g : Fin n) (K k j : Nat)
    (hk : k≤K) (hj : j≤2*n) :
    Sound (rawLiftStep g) (fun q => q.cross (2*n) 0 = K)
      (drainTree (2*n) (liftedSite g) k j) (fun q => k≤q.cross (2*n) j) := by
  rw [drainTree]
  by_cases hbase : k=0 ∨ j=0
  · rw [if_pos hbase]
    apply Sound.done
    intro q hK
    rcases hbase with h|h
    · omega
    · rw [h,hK]; exact hk
  · rw [if_neg hbase]
    have hk0 : 0<k := by omega
    have hj0 : 0<j := by omega
    have hL := drainTree_sound hn g K k (j-1) hk (by omega)
    have hCommit (q : Line) (_ : q.cross (2*n) 0 = K)
        (left : k≤q.cross (2*n) (j-1))
        (right : j<2*n → k-1≤q.cross (2*n) (j+1)) :
        k≤(rawLiftStep g q (liftedSite g (j-1))).cross (2*n) j := by
      by_cases hDone : k≤q.cross (2*n) j
      · exact Nat.le_trans hDone (raw_cross_mono hn g q _ _ hj)
      · have hPrev := cuts_adjacent (2*n) q.stock q.departed (j-1) (by omega)
        rw [show j-1+1=j by omega] at hPrev
        change q.cross (2*n) (j-1) = (q.stock (j-1)).toNat + q.cross (2*n) j at hPrev
        have hS : q.stock (j-1)=true := by
          cases hs : q.stock (j-1)
          · simp [hs] at hPrev; omega
          · rfl
        have hT : k-1≤q.cross (2*n) j := by rw [hS] at hPrev; change _=1+_ at hPrev; omega
        have hEn : enabled (2*n) (j-1) q := by
          refine ⟨by omega,hS,?_⟩
          by_cases hW : j=2*n
          · exact Or.inl (by omega)
          · have hRt := cuts_adjacent (2*n) q.stock q.departed j (by omega)
            change q.cross (2*n) j = (q.stock j).toNat + q.cross (2*n) (j+1) at hRt
            have hR := right (by omega)
            right
            rw [show j-1+1=j by omega]
            cases hz : q.stock j
            · rfl
            · rw [hz] at hRt; change _=1+_ at hRt; omega
        have hGain := raw_improves hn g q (j-1) hEn
        rw [show j-1+1=j by omega] at hGain
        omega
    by_cases hW : j<2*n
    · rw [if_pos hW]
      have hR := drainTree_sound hn g K (k-1) (j+1) (by omega) (by omega)
      exact Sound.fork _ _ _ _ _ _ hL hR
        (fun q e _ h => Nat.le_trans h (raw_cross_mono hn g q e j hj))
        (fun q h a b => hCommit q h a (fun _ => b))
    · rw [if_neg hW]
      exact Sound.fork _ _ _ _ _ _ hL (Sound.done (fun _ => True) (fun _ _ => True.intro))
        (fun q e _ h => Nat.le_trans h (raw_cross_mono hn g q e j hj))
        (fun q h a _ => hCommit q h a (fun b => (hW b).elim))
termination_by 2*k+j
decreasing_by
  all_goals
    have _hk' : k ≠ 0 := fun hh => (by assumption : ¬ (k=0 ∨ j=0)) (Or.inl hh)
    omega

/-- Actual length-2n no-source virtual drain with at most n particles.
The service family uses only common physical bond nominations. -/
theorem drain_paths {n : Nat} (hn : 4≤n) (g : Fin n) (q : Line)
    (hK : q.cross (2*n) 0 ≤ n) :
    ∃ L paths, L≤4*n ∧
      (∀ p ∈ paths, p.length≤L) ∧ paths.length≤2^L ∧
      ∀ w, GGTiming.finished (GGTiming.runMarks GGTiming.advance paths w) →
        q.cross (2*n) 0 ≤ (GGTiming.runMarks (rawLiftStep g) q w).departed := by
  let K := q.cross (2*n) 0
  let T := drainTree (2*n) (liftedSite g) K (2*n)
  refine ⟨2*K+2*n,T.paths,by dsimp [K]; omega,?_,?_,?_⟩
  · intro p hp
    exact Nat.le_trans (Tree.path_span T p hp) (drainTree_span ..)
  · exact Nat.le_trans (Tree.path_count T) (Nat.pow_le_pow_right (by decide) (drainTree_span ..))
  · intro w hw
    have hGood : ∀ z e, z.cross (2*n) 0 = K → (rawLiftStep g z e).cross (2*n) 0 = K :=
      fun z e hz => (raw_mass g z e).trans hz
    have hh := (drainTree_sound (by omega) g K K (2*n) (Nat.le_refl _) (Nat.le_refl _)).of_paths
      hGood q rfl w hw
    simpa [K,Line.cross,cuts_far (2*n) _ _ (2*n) (Nat.le_refl _)] using hh

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.drain_paths

namespace L4.RootlessFIFO
open FIFOCompare RankRootless RearTrace

/-- Literal rootless drain observer, following a marked head even
through a ghost merger. A head merger is already an allowed earlier
stop but is harmless for this stronger drain estimate. -/
structure DrainObs (p c n : Nat) where
  config : Config p c n
  shift : Nat
  paid : Nat

def drainInit {p c n : Nat} (x : Config p c n) : DrainObs p c n := ⟨x,0,0⟩

def headIncrement {p c n : Nat} (g e : Fin n) (s : DrainObs p c n) : Nat :=
  if rightNeighbor e=liftedSite g s.shift then
    (geometricPay (s.config e) (s.config (rightNeighbor e))).toNat
  else 0

def drainStep {p c n : Nat} (g : Fin n) (s : DrainObs p c n) (e : Fin n) : DrainObs p c n :=
  ⟨step s.config e,s.shift+headIncrement g e s,
    s.paid + (geometricPay (s.config e) (s.config (rightNeighbor e))).toNat⟩

def realLine {p c n : Nat} (g : Fin n) (s : DrainObs p c n) : Line :=
  liftReal s.config g s.shift s.paid

/-- The tracked head's incoming mark stays present, including at a
merger onto the resident next mark. -/
theorem moving_head_mark {p c n : Nat} (hn : 4≤n) (g e : Fin n) (s : DrainObs p c n)
    (hm : MCOV s.config)
    (h : (s.config (predecessor (liftedSite g s.shift))).mark = true) :
    ((drainStep g s e).config (predecessor (liftedSite g (drainStep g s e).shift))).mark = true := by
  let x := s.config
  let f := liftedSite g s.shift
  let p := geometricPay (x e) (x (rightNeighbor e))
  change (step x e (predecessor (liftedSite g (s.shift+headIncrement g e s)))).mark = true
  by_cases hp : p=true
  · by_cases he : rightNeighbor e=f
    · have hI : headIncrement g e s=1 := by
        change (if rightNeighbor e=f then p.toNat else 0)=1
        rw [if_pos he,hp]
        rfl
      rw [hI,liftedSite_succ,predecessor_right,covered_step_mark hn x hm e f]
      have hEF : f≠e := by rw [← he]; exact raw_no_self hn e
      simp only [show geometricPay (x e) (x (rightNeighbor e))=true from hp,
        if_true,if_neg hEF,if_pos he.symm]
    · have hI : headIncrement g e s=0 := by
        change (if rightNeighbor e=f then _ else _) = 0
        exact if_neg he
      rw [hI,Nat.add_zero]
      change (step x e (predecessor f)).mark = true
      rw [covered_step_mark hn x hm]
      have hu : predecessor f ≠ e := by
        intro heq; exact he (by rw [← heq,right_predecessor])
      by_cases hh : predecessor f = rightNeighbor e
      · simp [show geometricPay (x e) (x (rightNeighbor e))=true from hp,hh,raw_no_self hn e]
      · simp [show geometricPay (x e) (x (rightNeighbor e))=true from hp,hu,hh,show (x (predecessor f)).mark=true from h]
  · have hp' : p=false := Bool.eq_false_iff.mpr hp
    have hn' : headIncrement g e s=0 := by
      change (if rightNeighbor e=f then p.toNat else 0)=0
      rw [hp']
      split <;> rfl
    rw [hn',Nat.add_zero,covered_step_mark hn x hm]
    simpa [show geometricPay (x e) (x (rightNeighbor e))=false from hp'] using h

/-- Remaining displacement cap is automatic from no minting and the
total stock ledger; no geometric assumption about the moving end is used. -/
theorem drainStep_caps {p c n : Nat} (hn : 4≤n) (g e : Fin n) (s : DrainObs p c n)
    (hm : MCOV s.config) (hl : NoLiving s.config)
    (hd : s.shift ≤ s.paid) (hS : (s.paid : Int)+stockCount s.config ≤ n) :
    let t := drainStep g s e
    t.shift≤t.paid ∧ (t.paid : Int)+stockCount t.config≤n ∧ t.shift≤n := by
  let q := (geometricPay (s.config e) (s.config (rightNeighbor e))).toNat
  have hI : headIncrement g e s ≤ q := by
    unfold headIncrement; split <;> omega
  have hB := stockCount_paid_le hn s.config e hm hl
  have hN := (stockCount_interval hn (step s.config e)).1
  change s.shift+headIncrement g e s≤s.paid+q ∧
    ((s.paid+q : Nat) : Int)+stockCount (step s.config e)≤n ∧
    s.shift+headIncrement g e s≤n
  change stockCount (step s.config e) + (q : Int) ≤ stockCount s.config at hB
  omega

/-- Finish the exact deterministic coupling on any tape of rootless
premarks. An earlier birth is the alternative terminal outcome. -/
theorem actual_coupling {p c n : Nat} (hn : 4≤n)
    (g : Fin n) (s : DrainObs p c n) (q : Line) (w : List (Fin n))
    (hm : MCOV s.config) (hl : RootlessWord s.config w)
    (hHead : (s.config (predecessor (liftedSite g s.shift))).mark=true)
    (hD : s.shift≤s.paid) (hStock : (s.paid:Int)+stockCount s.config≤n)
    (hOrder : ∀ k, k≤2*n → q.cross (2*n) k ≤ (realLine g s).cross (2*n) k) :
    let t := GGTiming.runMarks (drainStep g) s w
    (realLine g t).cross (2*n) 0 = (realLine g s).cross (2*n) 0 ∧
    t.shift≤n ∧ (∀ k, k≤2*n →
      (GGTiming.runMarks (rawLiftStep g) q w).cross (2*n) k ≤ (realLine g t).cross (2*n) k) := by
  induction w generalizing s q with
  | nil =>
    have hN₀ := (stockCount_interval hn s.config).1
    exact ⟨rfl,by change s.shift≤n; omega,hOrder⟩
  | cons e w ih =>
    have hN₀ := (stockCount_interval hn s.config).1
    have hD₀ : s.shift≤n := by omega
    let t := drainStep g s e
    have hCaps := drainStep_caps hn g e s hm hl.1 hD hStock
    have hHead' := moving_head_mark hn g e s hm hHead
    obtain ⟨a,ha,he⟩ := liftedSite_of_site g e
    let j : Fin n := ⟨a,ha⟩
    have hE : liftedSite g j.val=e := he
    have hR := concreteLiftResponses s.config g j s.shift s.paid hn hD₀ hm hl.1 hHead
    have hCap : s.shift + headIncrement g e s ≤ n := hCaps.2.2
    rw [hE] at hR
    have ht : LiftResponses (2*n) a (a+n) (realLine g s) ((realLine g t).cross (2*n)) :=
      hR hCap
    have hVV : rawLiftStep g q e = duplicatedStep n a q := by
      rw [← he,raw_at_offset,Nat.mod_eq_of_lt ha]
    have hOrd := duplicated_compare n a (by omega) q (realLine g s)
      ((realLine g t).cross (2*n)) hOrder ht
    rw [← hVV] at hOrd
    have hg := ih t (rawLiftStep g q e) (mcov_step hn s.config hm e)
      hl.2 hHead' hCaps.1 hCaps.2.1 hOrd
    exact ⟨hg.1.trans ht.mass,hg.2.1,hg.2.2⟩

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.actual_coupling

namespace L4.RootlessFIFO
open FIFOCompare RankRootless RearTrace

private theorem tailSlots_cap (width M k : Nat) (f : Nat→Bool)
    (h : ∀ j, M≤j → f j=false) :
    tailSlots width f k ≤ M-k := by
  rw [tailSlots]
  by_cases hd : k<width
  · rw [if_pos hd]
    have ih := tailSlots_cap width M (k+1) f h
    by_cases hk : M≤k
    · rw [h k hk]
      change 0+tailSlots width f (k+1) ≤ M-k
      omega
    · have hb : (f k).toNat≤1 := by cases f k <;> decide
      omega
  · simp [hd]
termination_by width-k
decreasing_by omega

private theorem init_mass_le {p c n : Nat} (x : Config p c n) (g : Fin n) :
    (realLine g (drainInit x)).cross (2*n) 0 ≤ n := by
  simp only [Line.cross,realLine,liftReal,drainInit,cuts,Nat.zero_add]
  have hh := tailSlots_cap (2*n) n 0 (liftedStock x g 0) (fun j hj => by
    simp [liftedStock,show ¬ j<n by omega])
  simpa using hh

private theorem stock_from_empty_lift {p c n : Nat} (x : Config p c n) (g : Fin n)
    (d : Nat) (hd : d≤n) (h : ∀ k, k<2*n → liftedStock x g d k=false) :
    NoStock x := by
  intro i
  obtain ⟨k,hk,he⟩ := liftedSite_of_site (liftedSite g d) i
  rw [lift_add] at he
  have hh := h (d+k) (by omega)
  simpa [liftedStock,show d≤d+k by omega,show d+k<n+d by omega,he] using hh

theorem drainStep_projection {p c n : Nat} (g : Fin n) (s : DrainObs p c n) (w : List (Fin n)) :
    (GGTiming.runMarks (drainStep g) s w).config = run s.config w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => exact ih (drainStep g s e)

/-- A complete finite rootless path family for the literal machine.
If the selected raw word has no earlier birth and meets all paths,
the physical stock is zero. The proof also tolerates an earlier
retirement (which is already a success in bounded rank). -/
theorem actual_drain_paths {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (g : Fin n) (hm : MCOV x)
    (hHead : (x (predecessor g)).mark=true) :
    ∃ L paths, L≤4*n ∧ (∀ p ∈ paths, p.length≤L) ∧ paths.length≤2^L ∧
      ∀ w, RootlessWord x w → GGTiming.finished (GGTiming.runMarks GGTiming.advance paths w) →
        NoStock (run x w) := by
  let s := drainInit x
  let q := realLine g s
  obtain ⟨L,paths,hL,hs,hc,hDrain⟩ := drain_paths hn g q (init_mass_le x g)
  refine ⟨L,paths,hL,hs,hc,?_⟩
  intro w hw hf
  have hMark : (s.config (predecessor (liftedSite g s.shift))).mark = true := by
    simpa [s,drainInit,liftedSite_zero] using hHead
  have hStock : (s.paid : Int)+stockCount s.config≤n := by
    simpa [s,drainInit] using (stockCount_interval hn x).2
  have hh := actual_coupling hn g s q w hm hw hMark (Nat.le_refl _) hStock (fun _ _ => Nat.le_refl _)
  let t := GGTiming.runMarks (drainStep g) s w
  let v := GGTiming.runMarks (rawLiftStep g) q w
  have hv : q.cross (2*n) 0 ≤ v.departed := hDrain w hf
  have hFin := drain_from_outlet (2*n) (q.cross (2*n) 0) (realLine g t) v
    (Nat.le_of_eq hh.1) hv (hh.2.2 (2*n) (Nat.le_refl _))
  have hPhys := stock_from_empty_lift t.config g t.shift hh.2.1 hFin
  rwa [drainStep_projection] at hPhys

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.actual_drain_paths

namespace L4.RootlessFIFO
open RankRootless

/-- Stop at the first birth or empty stock. Retirement could also be
declared an earlier success, but is unnecessary for the drain theorem. -/
def DrainTarget {p c n : Nat} (x : Config p c n) : Prop := ¬ NoLiving x ∨ NoStock x

private noncomputable def frozenDrain {p c n : Nat} (x : Config p c n) (e : Fin n) :
    Config p c n := by
  classical
  exact if DrainTarget x then x else step x e

private theorem frozen_from_target {p c n : Nat} (x : Config p c n) (w : List (Fin n))
    (ht : DrainTarget x) : GGTiming.runMarks frozenDrain x w = x := by
  induction w with
  | nil => rfl
  | cons e w ih => simpa [GGTiming.runMarks,frozenDrain,ht] using ih

private theorem frozen_or_literal {p c n : Nat} (x : Config p c n) (w : List (Fin n)) :
    let y := GGTiming.runMarks frozenDrain x w
    DrainTarget y ∨ (y=run x w ∧ RootlessWord x w) := by
  classical
  induction w generalizing x with
  | nil => exact Or.inr ⟨rfl,trivial⟩
  | cons e w ih =>
    by_cases hc : DrainTarget x
    · rw [frozen_from_target x (e::w) hc]
      exact Or.inl hc
    · have hN : NoLiving x := Classical.not_not.mp (fun h => hc (Or.inl h))
      simpa [GGTiming.runMarks,frozenDrain,hc,run,RootlessWord,hN] using ih (step x e)

private theorem frozen_cost_eq {p c n : Nat} (t : Nat) (x : Config p c n) :
    iidHitCost (step : Config p c n → Fin n → Config p c n) DrainTarget t x =
      iidHitCost frozenDrain DrainTarget t x := by
  classical
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hc : DrainTarget x
    · rw [iidHitCost_of_target _ _ _ hc,iidHitCost_of_target _ _ _ hc]
    · simp [iidHitCost,hc,frozenDrain,ih]

/-- Fully literal rootless stock drain to first birth or zero stock, in
at most 17 n² expected original raw marks. In particular this discharges
the rootless exclusion part of the first-retirement input. -/
theorem rootless_drain_mean {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (g : Fin n) (hm : MCOV x)
    (hHead : (x (RearTrace.predecessor g)).mark=true) :
    IIDExpectedHittingTimeAtMost step DrainTarget x (17*n^2) := by
  obtain ⟨L,paths,hL,hs,hc,hDrain⟩ := actual_drain_paths hn x g hm hHead
  have hcount : paths.length≤2^(L+1) := Nat.le_trans hc
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  have cert (w : List (Fin n)) (hw : GGTiming.finished (GGTiming.runMarks GGTiming.advance paths w)) :
      DrainTarget (GGTiming.runMarks frozenDrain x w) := by
    rcases frozen_or_literal x w with h|⟨he,hR⟩
    · exact h
    · exact Or.inr (he.symm ▸ hDrain w hR hw)
  have hCost := GGTiming.hittingTime_of_path_certificate frozenDrain DrainTarget x
    (by omega) paths L hs hcount cert
  intro t
  rw [frozen_cost_eq]
  apply Nat.le_trans (hCost t)
  apply Nat.mul_le_mul_right
  calc
    4*n*(L+1) = n*(4*(L+1)) := by rw [Nat.mul_comm 4 n,Nat.mul_assoc]
    _ ≤ n*(17*n) := Nat.mul_le_mul_left _ (by omega)
    _ = 17*n^2 := by rw [Nat.pow_two,← Nat.mul_assoc,Nat.mul_comm n 17,Nat.mul_assoc]

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.rootless_drain_mean

namespace L4.RootlessFIFO

/-- No designated head needs to be supplied on the admitted
nondivisibility domain; MCOV already guarantees one marked bond. -/
theorem rootless_drain_mean_of_mcov {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (hm : MCOV x) (hnd : ¬ p ∣ n) :
    IIDExpectedHittingTimeAtMost step DrainTarget x (17*n^2) := by
  obtain ⟨e,he⟩ := covered_mark_exists_of_not_dvd x ⟨0,by omega⟩ hm hnd
  exact rootless_drain_mean hn x (rightNeighbor e) hm (by
    rwa [RearTrace.predecessor_right])

end L4.RootlessFIFO

#print axioms L4.RootlessFIFO.rootless_drain_mean_of_mcov
