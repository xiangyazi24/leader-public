import Leader.L4.WindowScopedFourHead
import Leader.L4.WindowFourHeadCap

namespace L4.WindowFourHeadShadow
open RankSupplier RankSupplierPhysical WindowScopedSupplier RankPhysical FIFOCompare QueueDAG GGTiming

/-- A short virtual emitting line on the full original ring alphabet.
The extra short-alphabet label m+1 is a hold, used on every original
mark outside 0…m. No raw labels are censored. -/
def encodeLabel (m i : Nat) : Fin (m+2) :=
  if h : i≤m then ⟨i,by omega⟩ else ⟨m+1,by omega⟩

noncomputable def rawIndex {n : Nat} (v e : Fin n) : Fin n :=
  let p := Classical.choose (liftedSite_of_site v e)
  ⟨p,(Classical.choose_spec (liftedSite_of_site v e)).1⟩

theorem rawIndex_eq {n : Nat} (v e : Fin n) :
    liftedSite v (rawIndex v e).val=e :=
  (Classical.choose_spec (liftedSite_of_site v e)).2

theorem rawIndex_lift {n : Nat} (v : Fin n) (i : Nat) (hi : i<n) :
    (rawIndex v (liftedSite v i)).val=i :=
  liftedSite_inj v (rawIndex v _).isLt hi (rawIndex_eq _ _)

private theorem zero_lift (m : Nat) (i : Fin (m+2)) :
    liftedSite (0 : Fin (m+2)) i.val=i := by
  apply Fin.ext
  change (0+i.val)%(m+2)=i.val
  simpa only [Nat.zero_add] using Nat.mod_eq_of_lt i.isLt

noncomputable def next {n : Nat} (m : Nat) (v : Fin n) (s : Virtual (m+2)) (e : Fin n) :
    Virtual (m+2) :=
  virtualStep (0 : Fin (m+2)) s (encodeLabel m (rawIndex v e).val)

theorem heightRules {n : Nat} (m : Nat) (hm : 2≤m) (hn : m≤n-2) (v : Fin n) :
    HeightRules (next m v) (fun _ => True) current m (liftedSite v) := by
  have H := virtual_height_rules (show 4≤m+2 by omega) (0 : Fin (m+2))
  have he : m+2-2=m := by omega
  rw [he] at H
  refine ⟨?_,?_⟩
  · intro z e i hz hi
    exact H.mono z _ i hz hi
  · intro z i k hz hi hk hl hr
    have hIndex := rawIndex_lift v i (by have hp := v.isLt; omega)
    have hE : encodeLabel m (rawIndex v (liftedSite v i)).val = (⟨i,by omega⟩ : Fin (m+2)) := by
      simp [encodeLabel,hIndex,hi]
    have L := H.commit z i k hz hi hk hl hr
    rw [zero_lift m (⟨i,by omega⟩ : Fin (m+2))] at L
    simpa only [next,hE] using L

/-- Replace the size-(m+2) literal index with any index of the actual
ring. Outside the short line the old and new heights exactly agree. -/
theorem virtual_delta {n : Nat} (m : Nat) (hm : 2≤m) (v l : Fin n)
    (q : Virtual (m+2)) :
    let q' := next m v q (liftedSite v l.val)
    VirtualDelta (m+1) l.val (asNatStock q.stock)
      (cuts (m+1) (asNatStock q.stock) q.departures)
      (cuts (m+1) (asNatStock q'.stock) q'.departures) := by
  let j := encodeLabel m l.val
  have hnext : next m v q (liftedSite v l.val)=virtualStep (0 : Fin (m+2)) q j := by
    simp [next,j,rawIndex_lift v l.val l.isLt]
  rw [hnext]
  have H := literal_virtual_delta (show 4≤m+2 by omega) (0 : Fin (m+2)) j q
  rw [zero_lift m j] at H
  have hW : m+2-1=m+1 := by omega
  rw [hW] at H
  by_cases hl : l.val≤m
  · simpa [j,encodeLabel,hl] using H
  · have he : j.val=m+1 := by simp [j,encodeLabel,hl]
    cases H with
    | idle h => exact .idle h
    | inject hiz _ _ => omega
    | move hi hh _ _ _ => omega
    | outlet hi hh _ _ => omega

/-- A kept one-mark projection into the same physical supplier. An exit
requires no projection, so later exterior events are not removed from a word. -/
structure View {α : Type} {p c n : Nat} (f : α → Config p c n)
    (d : α → Nat) (tick : α → Fin n → α) (done : α → Prop)
    (v : Fin n) (d₀ m : Nat) : Prop where
  sticky : ∀ x e, done x → done (tick x e)
  bound : ∀ x, ¬done x → d₀≤d x ∧ d x≤m
  live : ∀ x, ¬done x → Live v (init (f x) (d x))
  kept : ∀ x e, ¬done (tick x e) →
    let y := follow v (d x) (f x) e
    (e=liftedSite v (d x) → retirement (f x) e=false) ∧ Live v y ∧
      f (tick x e)=y.config ∧ d (tick x e)=y.donor

def dominated {p c n : Nat} (m d₀ : Nat) (v : Fin n)
    (x : Config p c n) (d : Nat) (q : Virtual (m+2)) : Prop :=
  ∀ k, 0<k → k≤m+1 →
    cuts (m+1) (asNatStock q.stock) q.departures k ≤
    cuts (m+1) (realStock v (init x d)) (d-d₀) k

theorem compare {α : Type} {p c n m d₀ : Nat} (hn : 4≤n) (hm : 2≤m)
    (hw : m≤n-2) (v : Fin n) (f : α → Config p c n) (d : α → Nat)
    (tick : α → Fin n → α) (done : α → Prop) (V : View f d tick done v d₀ m)
    (x : α) (q : Virtual (m+2)) (e : Fin n) (he : ¬done (tick x e))
    (h : dominated m d₀ v (f x) (d x) q) :
    dominated m d₀ v (f (tick x e)) (d (tick x e)) (next m v q e) := by
  have hx : ¬done x := fun hx => he (V.sticky x e hx)
  let l := rawIndex v e
  have hl : liftedSite v l.val=e := rawIndex_eq v e
  obtain ⟨hmin,hmax⟩ := V.bound x hx
  obtain ⟨_,hnew⟩ := V.bound (tick x e) he
  obtain ⟨hret,hlive,hf,hd⟩ := V.kept x e he
  have hw' : m+1≤n-1 := by omega
  have hp' : 2≤m+1 := by omega
  have hc' : d x<m+1 := by omega
  have hnew' : (follow v (d x) (f x) e).donor<m+1 := by rw [←hd]; omega
  have hv := virtual_delta m hm v l q
  rw [hl] at hv
  have H := WindowScopedFourHead.compare_short_mark hn v (f x) l (V.live x hx) hmin
    (by rw [hl]; exact hret) (by rw [hl]; exact hlive)
    hw' hp' hc' (by rw [hl]; exact hnew') (asNatStock q.stock) q.departures _ hv h
  rw [hl] at H
  have hs : init (f (tick x e)) (d (tick x e)) = follow v (d x) (f x) e := by
    rw [hf,hd]
    rfl
  unfold dominated
  rw [hs,hd]
  exact H

theorem compare_word {α : Type} {p c n m d₀ : Nat} (hn : 4≤n) (hm : 2≤m)
    (hw : m≤n-2) (v : Fin n) (f : α → Config p c n) (d : α → Nat)
    (tick : α → Fin n → α) (done : α → Prop) (V : View f d tick done v d₀ m)
    (x : α) (q : Virtual (m+2)) (w : List (Fin n))
    (h : dominated m d₀ v (f x) (d x) q) (he : ¬done (runMarks tick x w)) :
    let y := runMarks tick x w
    dominated m d₀ v (f y) (d y) (runMarks (next m v) q w) := by
  have keep (z : α) (u : List (Fin n)) : done z → done (runMarks tick z u) := by
    induction u generalizing z with
    | nil => exact id
    | cons e u ih => intro hz; exact ih _ (V.sticky z e hz)
  induction w generalizing x q with
  | nil => exact h
  | cons e w ih =>
    have hn' : ¬done (tick x e) := fun hd => he (keep _ w hd)
    exact ih _ _ (compare hn hm hw v f d tick done V x q e hn' h) he

/-- On the full physical word alphabet, a finite cap on kept donor
advance bounds the time to a scoped exit. No clock-rate hypothesis is used. -/
theorem mean {α : Type} {p c n m d₀ P : Nat} (hn : 4≤n) (hm : 2≤m)
    (hw : m≤n-2) (v : Fin n) (f : α → Config p c n) (d : α → Nat)
    (tick : α → Fin n → α) (done : α → Prop) (V : View f d tick done v d₀ m)
    (x : α) (q : Virtual (m+2)) (h : dominated m d₀ v (f x) (d x) q)
    (hP : ∀ w, ¬done (runMarks tick x w) → d (runMarks tick x w)-d₀<P) :
    IIDExpectedHittingTimeAtMost tick done x (4*n*(2*P+m+1)) := by
  apply WindowScopedFourHead.short_clock_of_shadow (by omega : 0<n) tick done x
    (next m v) (fun _ => True) current (liftedSite v) (heightRules m hm hw v)
    (fun _ _ _ => True.intro) q True.intro
  intro w hw'
  let y := runMarks tick x w
  let t := runMarks (next m v) q w
  have H := compare_word hn hm hw v f d tick done V x q w h hw' (m+1) (by omega) (by omega)
  have hc : m+2-2=m := by omega
  have E : current t m=t.departures := by
    have K := current_outlet t
    rwa [hc] at K
  rw [E]
  change cuts (m+1) (asNatStock t.stock) t.departures (m+1) ≤
    cuts (m+1) (realStock v (init (f y) (d y))) (d y-d₀) (m+1) at H
  rw [cuts_far _ _ _ _ (by omega),cuts_far _ _ _ _ (by omega)] at H
  exact Nat.lt_of_le_of_lt H (hP w hw')

private theorem empty_tail (w k : Nat) :
    tailSlots w (fun _ => false) k=0 := by
  rw [tailSlots]
  split
  · rw [empty_tail w (k+1)]
    decide
  · rfl
termination_by w-k

theorem empty_dominated {p c n m d₀ : Nat} (v : Fin n) (x : Config p c n) (d : Nat) :
    dominated m d₀ v x d ⟨fun _ => false,0⟩ := by
  have Z : asNatStock (n:=m+2) (fun _ => false)=fun _ => false := by
    funext k
    by_cases hk : k<m+2 <;> simp [asNatStock,hk]
  intro k _ _
  change cuts (m+1) (asNatStock (n:=m+2) (fun _ => false)) 0 k≤_
  rw [Z,cuts,empty_tail]
  exact Nat.le_of_lt_succ (Nat.zero_lt_succ _)

theorem mean_empty {α : Type} {p c n m d₀ P : Nat} (hn : 4≤n) (hm : 2≤m)
    (hw : m≤n-2) (v : Fin n) (f : α → Config p c n) (d : α → Nat)
    (tick : α → Fin n → α) (done : α → Prop) (V : View f d tick done v d₀ m)
    (x : α) (hP : ∀ w, ¬done (runMarks tick x w) → d (runMarks tick x w)-d₀<P) :
    IIDExpectedHittingTimeAtMost tick done x (4*n*(2*P+m+1)) :=
  mean hn hm hw v f d tick done V x _ (empty_dominated v (f x) (d x)) hP

/-- The four-head reservoir pays for the same physical marks as the
shadow clock. To instantiate this theorem, the window router supplies
the literal first-mark/kept projection, initial geometry, and a path
observer which counts the selected J payments in its fixed lift. -/
theorem mean_of_count {α : Type} {p c n m d₀ : Nat} {initial : Config p c n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hm : 2≤m) (hw : m≤n-2)
    (v : Fin n) (f : α → Config p c n) (d : α → Nat)
    (tick : α → Fin n → α) (done : α → Prop) (V : View f d tick done v d₀ m)
    (x : α) (q : WindowFourHeadCut.Cursor p c n) (g : List (Fin n))
    (a b k : Fin n) (ha : a∈g) (hb : b∈g) (hk : k∈g) (hab : a≠b)
    (hv : SevenTagCharge.Valid q.ledger initial) (hq : QuietEntrance q.ledger.config)
    (hg : WindowFourHeadCut.Geometry q.ledger q.j q.w q.k a b k q.index q.width)
    (hJ : (q.ledger.config (rightNeighbor q.j)).leader=false)
    (b₀ c₀ : Nat) (hi : q.index+1=b₀) (hwidth : q.width+1=b₀+c₀)
    (observe : ∀ w, ¬done (runMarks tick x w) →
      WindowFourHeadCut.RetainedKeep g q w ∧
      d (runMarks tick x w)-d₀=WindowFourHeadCap.totalJ q w) :
    IIDExpectedHittingTimeAtMost tick done x (4*n*(2*(2*b₀+c₀+1)+m+1)) := by
  apply mean_empty hn hm hw v f d tick done V x
  intro w h
  obtain ⟨hkeep,hcount⟩ := observe w h
  rw [hcount]
  exact WindowFourHeadCap.four_head_payments hp hc hn g a b k ha hb hk hab q w
    hkeep hv hq hg hJ b₀ c₀ hi hwidth

end L4.WindowFourHeadShadow
