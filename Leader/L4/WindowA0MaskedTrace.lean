import Leader.L4.WindowA0Masked

namespace L4.WindowA0MaskedTrace
open WindowA0Masked WindowA0FixedSink FIFOCompare

private theorem no_loop {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have he : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have H := liftedSite_inj e (show 1<n by omega) (show 0<n by omega) he
  omega

/-- No row erases a preoccupied responder stock field, even across
native death or birth. This justifies extra persistence off its own
door. -/
theorem responder_stock_stays {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (e : Fin n) (h : (x (rightNeighbor e)).stock=true) :
    (step x e (rightNeighbor e)).stock=true := by
  let l : Option Unit := if (x e).stock then some () else none
  have hl : l.isSome = (x e).stock := by cases h : (x e).stock <;> simp [l,h]
  have hr : (some () : Option Unit).isSome=(x (rightNeighbor e)).stock := h.symm
  have H := congrArg Prod.snd
    (StockTokenRows.pair_labels (x e) (x (rightNeighbor e)) l (some ()) () hl hr)
  have R := GGStockPhysical.incoming_retains_label (x e) (x (rightNeighbor e)) l () () h
  change (StockTokenRows.update (StockTokenRows.row (x e) (x (rightNeighbor e))) l (some ()) ()).2.isSome =
    (pairStep (x e) (x (rightNeighbor e))).2.stock at H
  rw [R] at H
  simpa [step,no_loop hn e] using H.symm

structure Cursor where
  I : Nat
  J : Nat
  extra : Bool
  spent : Nat

def paymentAt {p c n : Nat} (x : Config p c n) (base e : Fin n) (i : Nat) : Bool :=
  (e == liftedSite base (i-1)) && geometricPay (x e) (x (rightNeighbor e))

def tick {p c n : Nat} (x : Config p c n) (base e : Fin n) (q : Cursor) : Cursor :=
  let thenI := paymentAt x base e q.I
  let thenJ := paymentAt x base e q.J
  let s := stock x base q.I q.J q.extra
  ⟨q.I+thenI.toNat,q.J+thenJ.toNat,
   if thenJ then (x (liftedSite base q.J)).stock else q.extra,
   q.spent + (if thenI then (s q.I).toNat else if thenJ then (s (q.J-1)).toNat else 0)⟩

/-- Physical facts of the continuing old cut, not a stock-trajectory
assumption. Both current dimensions fit the fixed support width. -/
structure Good {p c n : Nat} (x : Config p c n) (base : Fin n) (width : Nat) (q : Cursor) : Prop where
  cap : width<n
  positive : 0<q.I
  order : q.I<q.J
  fits : q.J≤width
  markI : (x (liftedSite base (q.I-1))).mark=true
  markJ : (x (liftedSite base (q.J-1))).mark=true
  ghostJ : (x (liftedSite base q.J)).leader=false
  inner : ∀ k, q.I≤k → k+1<q.J → (x (liftedSite base k)).mark=false
  nonliving : ∀ k, q.I≤k → k<q.J → (x (liftedSite base k)).leader=false
  extraHere : q.extra=true → (x (liftedSite base (q.J-1))).stock=true

private theorem paid_eq {p c n : Nat} (x : Config p c n) (base e : Fin n) (i : Nat) :
    paymentAt x base e i=true ↔
      e=liftedSite base (i-1) ∧ geometricPay (x e) (x (rightNeighbor e))=true := by
  simp [paymentAt,Bool.and_eq_true,beq_iff_eq]

private theorem lift_pred {n : Nat} (base : Fin n) (i : Nat) (hi : 0<i) :
    rightNeighbor (liftedSite base (i-1))=liftedSite base i := by
  rw [←liftedSite_succ,show i-1+1=i by omega]

private theorem masked_absorb {width spent j : Nat} {s : Nat → Bool}
    (hj : 0<j) (hw : j<width) :
    MaskedRow width s spent (setStock s j false) (spent+(s j).toNat) := by
  cases hs : s j
  · rw [show setStock s j false=s by rw [←hs,setStock_same]]
    exact .idle
  · skip
    exact .absorb j hj hw hs

/-- Classify every continuing physical mark, including paused marks.
Only the genuine postmark strict order is needed from the tag cursor. -/
theorem masked_step {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (base e : Fin n) (width : Nat) (q : Cursor)
    (good : Good x base width q) (mc : MCOV x)
    (hOrder : (tick x base e q).I < (tick x base e q).J) :
    let q' := tick x base e q
    MaskedRow width (stock x base q.I q.J q.extra) q.spent
      (stock (step x e) base q'.I q'.J q'.extra) q'.spent := by
  let I := q.I
  let J := q.J
  let s := stock x base I J q.extra
  have hI : 0<I := good.positive
  have hIJ : I<J := good.order
  have hJ : J<n := Nat.lt_of_le_of_lt good.fits good.cap
  have hW : J≤width := good.fits
  have ix {i j : Nat} (hi : i<n) (hj : j<n) (h : liftedSite base i=liftedSite base j) : i=j :=
    liftedSite_inj base hi hj h
  have eIJ : liftedSite base (I-1)≠liftedSite base (J-1) := fun h => by
    have H := ix (by omega) (by omega) h
    omega
  by_cases pi : paymentAt x base e I=true
  · obtain ⟨he,_⟩ := (paid_eq x base e I).mp pi
    have pj : paymentAt x base e J=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact eIJ (he.symm.trans ((paid_eq x base e J).mp h).1)
    have hSep : I+1<J := by simpa [tick,I,J,pi,pj] using hOrder
    change MaskedRow width s q.spent _ _
    rw [show tick x base e q=⟨I+1,J,q.extra,q.spent+(s I).toNat⟩ by
      simp [tick,pi,pj,I,J,s]]
    rw [he,paid_i_mask x base I J q.extra hI hSep hJ]
    exact masked_absorb hI (by omega)
  · have pi0 := Bool.eq_false_iff.mpr pi
    by_cases pj : paymentAt x base e J=true
    · obtain ⟨he,hp⟩ := (paid_eq x base e J).mp pj
      have hl : (x e).leader=false := by
        rw [he]
        exact good.nonliving (J-1) (by omega) (by omega)
      have hReady := RearTrace.geometricPay_ready _ _ hp
      have hStock : (x (liftedSite base (J-1))).stock=true := by
        rw [←he]
        simpa [payer,hl] using hReady
      change MaskedRow width s q.spent _ _
      rw [show tick x base e q=⟨I,J+1,(x (liftedSite base J)).stock,q.spent+(s (J-1)).toNat⟩ by
        simp [tick,pi0,pj,I,J,s]]
      rw [he,paid_j_mask hn x base I J q.extra hIJ hJ good.markJ hStock]
      exact masked_absorb (by omega) (by omega)
    · have pj0 := Bool.eq_false_iff.mpr pj
      change MaskedRow width s q.spent _ _
      rw [show tick x base e q=q by cases q; simp_all [tick,I,J]]
      by_cases hw : ∃ k, I≤k ∧ k+1<J ∧ liftedSite base k=e
      · obtain ⟨k,hk,hl,he⟩ := hw
        rw [←he,interior_mask hn x base I J k q.extra hk hl hJ mc
          (good.inner k hk hl) (good.nonliving k hk (by omega)) good.extraHere]
        change MaskedRow width s q.spent
          (if s k && !(x (liftedSite base (k+1))).stock
            then setStock (setStock s k false) (k+1) true else s) q.spent
        split
        · rename_i hh
          have hOcc := (Bool.and_eq_true_iff.mp hh).1
          have hv : (x (liftedSite base (k+1))).stock=false := by
            have h := (Bool.and_eq_true_iff.mp hh).2
            cases HS : (x (liftedSite base (k+1))).stock <;> simp_all
          have hVac : s (k+1)=false := by simp [s,stock,hv]
          exact .transfer k (by omega) (by omega) hOcc hVac
        · exact .idle
      · have hL (l : Nat) (hl : I≤l) (hr : l<J) (he : liftedSite base l=e) : l+1=J := by
          by_cases h : l+1<J
          · exact (hw ⟨l,hl,h,he⟩).elim
          · omega
        have hR (l : Nat) (hl : I≤l) (hr : l<J) (he : liftedSite base l=rightNeighbor e) : l=I := by
          by_cases h : l=I
          · exact h
          · have he' : liftedSite base (l-1)=e := FreshSeparation.succ_inj
                ((lift_pred base l (by omega)).trans he)
            exact (hw ⟨l-1,by omega,by omega,he'⟩).elim
        have hT (he : rightNeighbor e=liftedSite base I) : (x e).mark=true := by
          have h := FreshSeparation.succ_inj (he.trans (lift_pred base I hI).symm)
          rw [h]
          exact good.markI
        have hD (he : liftedSite base (J-1)=e) :
            (x e).mark=true ∧ (x e).leader=false ∧ (x (rightNeighbor e)).leader=false ∧
              geometricPay (x e) (x (rightNeighbor e))=false := by
          have hnP : geometricPay (x e) (x (rightNeighbor e))=false := by
            apply Bool.eq_false_iff.mpr
            intro hh
            exact pj ((paid_eq x base e J).mpr ⟨he.symm,hh⟩)
          refine ⟨he ▸ good.markJ,he ▸ (good.nonliving (J-1) (by omega) (by omega)),?_,hnP⟩
          rw [←he,lift_pred base J (by omega)]
          exact good.ghostJ
        rw [boundary_or_exterior_mask hn x base e I J q.extra hL hR hT hD]
        exact .idle

/-- The extra bit denotes a stock byte actually present at the current
door. Off a J payment an old extra cannot disappear: an old door hit
would have paid, while an incoming hit preserves the resident. -/
theorem extra_persists {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (base e : Fin n) (width : Nat)
    (q : Cursor) (good : Good x base width q) :
    let q' := tick x base e q
    q'.extra=true → (step x e (liftedSite base (q'.J-1))).stock=true := by
  let J := q.J
  have hJ : 0<J := by have := good.order; omega
  by_cases hp : paymentAt x base e J=true
  · obtain ⟨he,_⟩ := (paid_eq x base e J).mp hp
    have hr : liftedSite base J=rightNeighbor e := by rw [he,lift_pred base J hJ]
    change (if paymentAt x base e J then (x (liftedSite base J)).stock else q.extra)=true →
      (step x e (liftedSite base (J+(paymentAt x base e J).toNat-1))).stock=true
    rw [if_pos hp,hp,Bool.toNat_true,show J+1-1=J by omega,hr]
    exact responder_stock_stays hn x e
  · have hf := Bool.eq_false_iff.mpr hp
    change (if paymentAt x base e J then (x (liftedSite base J)).stock else q.extra)=true →
      (step x e (liftedSite base (J+(paymentAt x base e J).toNat-1))).stock=true
    rw [if_neg hp,hf,Bool.toNat_false,Nat.add_zero]
    intro extra
    have hs := good.extraHere extra
    let r := liftedSite base (J-1)
    have hnE : r≠e := by
      intro he
      have hRight : rightNeighbor e=liftedSite base J := by rw [←he,lift_pred base J hJ]
      have hpay := WindowA0StockDrain.marked_ghost_stock_pays (x e) (x (rightNeighbor e))
        (he ▸ good.markJ) (hRight.symm ▸ good.ghostJ) (he ▸ hs)
      exact hp ((paid_eq x base e J).mpr ⟨he.symm,hpay⟩)
    change (step x e r).stock=true
    by_cases he : r=rightNeighbor e
    · rw [he]
      exact responder_stock_stays hn x e (he ▸ hs)
    · simpa [step,hnE,he] using hs

open FIFOCompare in
/-- Includes every raw mark, even those omitted from the virtual path
cursor because the old J door is stocked. -/
theorem physical_heights {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (base e : Fin n) (width : Nat) (q : Cursor)
    (good : Good x base width q) (mc : MCOV x)
    (hOrder : (tick x base e q).I < (tick x base e q).J) :
    let q' := tick x base e q
    let H := cuts width (stock x base q.I q.J q.extra) q.spent
    let H' := cuts width (stock (step x e) base q'.I q'.J q'.extra) q'.spent
    H 1 = H' 1 ∧ ∀ k, H k≤H' k :=
  (masked_step hn x base e width q good mc hOrder).heights

/-- On precisely the unpaused raw letters, a forced vacancy transfer
attains the bounded DAG height threshold. The initial conserved total
at cut zero supplies the otherwise nonexistent injection. -/
theorem unpaused_commit {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (base : Fin n) (m P i k : Nat) (q : Cursor)
    (good : Good x base (m+1) q) (mc : MCOV x)
    (pause : (x (liftedSite base (q.J-1))).stock=false)
    (hi : i≤m) (hk : 0<k) (hp : k≤P)
    (source : P ≤ cuts (m+1) (stock x base q.I q.J q.extra) q.spent 1)
    (left : 0<i → k≤cuts (m+1) (stock x base q.I q.J q.extra) q.spent (i-1+1))
    (right : i<m → k-1≤cuts (m+1) (stock x base q.I q.J q.extra) q.spent (i+1+1))
    (hOrder : (tick x base (liftedSite base i) q).I < (tick x base (liftedSite base i) q).J) :
    let e := liftedSite base i
    let q' := tick x base e q
    k≤cuts (m+1) (stock (step x e) base q'.I q'.J q'.extra) q'.spent (i+1) := by
  let s := stock x base q.I q.J q.extra
  let e := liftedSite base i
  let t := tick x base e q
  have hf : q.extra=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have H := good.extraHere h
    rw [pause] at H
    cases H
  have hfit := good.fits
  have hnW := good.cap
  have hIJ := good.order
  have hI := good.positive
  have sink : s m=false := by
    by_cases h : m<q.J
    · have qE : q.J-1=m := by omega
      have H := pause
      rw [qE] at H
      simp [s,stock,H]
    · simp [s,stock,h]
  apply closed_cut_commit m P i k q.spent s hi hk hp source sink left right
    (cuts (m+1) (stock (step x e) base t.I t.J t.extra) t.spent (i+1))
    ((physical_heights hn x base e (m+1) q good mc hOrder).2 (i+1))
  intro hip him occ vac
  have hLive : q.I≤i ∧ i<q.J := by
    by_cases h : q.I≤i ∧ i<q.J
    · exact h
    · have hs : s i=false := by
        unfold s stock
        exact if_neg (fun hh => h ⟨hh.1,hh.2.1⟩)
      rw [occ] at hs
      cases hs
  have hInt : i+1<q.J := by
    by_cases hh : i+1=q.J
    · have hj : q.J-1=i := by omega
      have H := pause
      rw [hj] at H
      have hOcc : s i=false := by simp [s,stock,H]
      rw [occ] at hOcc
      cases hOcc
    · omega
  have hv : (x (liftedSite base (i+1))).stock=false := by
    simpa [s,stock,hf,show q.I≤i+1 by omega,hInt] using vac
  have pI : paymentAt x base e q.I=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have he := (paid_eq x base e q.I).mp h |>.1
    have H := liftedSite_inj base (show i<n by omega) (show q.I-1<n by omega) he
    omega
  have pJ : paymentAt x base e q.J=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have he := (paid_eq x base e q.J).mp h |>.1
    have H := liftedSite_inj base (show i<n by omega) (show q.J-1<n by omega) he
    omega
  have T : t=q := by cases q; simp_all [t,tick]
  have H := interior_mask hn x base q.I q.J i q.extra hLive.1 hInt
    (by omega) mc (good.inner i hLive.1 hInt) (good.nonliving i hLive.1 hLive.2) good.extraHere
  change stock (step x e) base q.I q.J q.extra =
    (if s i && !(x (liftedSite base (i+1))).stock then _ else s) at H
  rw [occ,hv] at H
  simp only [Bool.not_false,Bool.and_self,if_true] at H
  rw [T,H,cuts_move (m+1) s q.spent i occ vac (by omega),if_pos rfl]
  exact Nat.le_refl _

end L4.WindowA0MaskedTrace
