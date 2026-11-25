import Leader.L4.RankSupplier
import Leader.L4.FIFOCompare
namespace L4.RankSupplierPhysical
open RankSupplier

theorem inner_bond_shape {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (k : Nat) (hk : k < s.donor) :
    let a := s.config (liftedSite v k)
    let b := s.config (liftedSite v (k+1))
    a.mark = false ∧ b.leader = false ∧ b.residue = nextResidue a.residue := by
  dsimp only
  have hm : (s.config (liftedSite v k)).mark ≠ true := h.2.2.2.2.1.before k hk
  have hCover := h.2.1 (liftedSite v k)
  rw [← liftedSite_succ] at hCover
  refine ⟨Bool.eq_false_iff.mpr hm, Bool.eq_false_iff.mpr (fun h => hm (hCover (Or.inl h))), ?_⟩
  by_cases he : (s.config (liftedSite v (k+1))).residue =
      nextResidue (s.config (liftedSite v k)).residue
  · exact he
  · exact False.elim (hm (hCover (Or.inr he)))

theorem inner_nonleader {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (k : Nat) (hk : 0 < k) (hkd : k ≤ s.donor) :
    (s.config (liftedSite v k)).leader = false := by
  have he := (inner_bond_shape v s h (k-1) (by omega)).2.1
  simpa [show k-1+1=k by omega] using he

theorem inner_stock_rule {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (k : Nat) (hk : k < s.donor) :
    let a := s.config (liftedSite v k)
    let b := s.config (liftedSite v (k+1))
    ((pairStep a b).1.stock,(pairStep a b).2.stock) =
      if payer a && !b.stock then (false,true) else (a.stock,b.stock) := by
  obtain ⟨hm,hl,hr⟩ := inner_bond_shape v s h k hk
  exact ordinary_pair_stock _ _ hm hr hl

theorem inner_exclusion_rule {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (k : Nat) (hk : 0 < k) (hkd : k < s.donor) :
    let a := s.config (liftedSite v k)
    let b := s.config (liftedSite v (k+1))
    ((pairStep a b).1.stock,(pairStep a b).2.stock) =
      if a.stock && !b.stock then (false,true) else (a.stock,b.stock) := by
  dsimp only
  rw [inner_stock_rule v s h k hkd]
  simp [payer, inner_nonleader v s h k hk (by omega : k ≤ s.donor)]

theorem source_stock_rule {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (hd : 0 < s.donor) :
    let a := s.config v
    let b := s.config (rightNeighbor v)
    ((pairStep a b).1.stock,(pairStep a b).2.stock) =
      if !b.stock then (false,true) else (a.stock,b.stock) := by
  have he := inner_stock_rule v s h 0 hd
  simpa [liftedSite_zero,liftedSite_succ,payer,h.2.2.1] using he

private theorem native_fields {p c : Nat} (u z : Site p c) :
    (native u z).1.stock = u.stock ∧ (native u z).1.leader = u.leader ∧
      (native u z).1.mark = u.mark ∧
      (z.leader = false → (native u z).2.leader = false) := by
  have ha : (fireInitiator u).stock = u.stock ∧ (fireInitiator u).mark = u.mark ∧
      (fireInitiator u).leader = u.leader := by
    unfold fireInitiator
    split <;> exact ⟨rfl,rfl,rfl⟩
  have hb : (fireResponder z).leader = z.leader := by
    unfold fireResponder
    split
    · cases z.signal <;> rfl
    · rfl
  unfold native
  generalize fireInitiator u = a at ha ⊢
  generalize fireResponder z = b at hb ⊢
  have hi : (impact a b).1.stock = a.stock ∧ (impact a b).1.mark = a.mark ∧
      (impact a b).1.leader = a.leader ∧ (b.leader = false → (impact a b).2.leader = false) := by
    unfold impact
    split
    · split <;> simp
    · simp
  generalize impact a b = ab at hi ⊢
  rcases ab with ⟨a',b'⟩
  dsimp only at hi ⊢
  have hf (g : Bool) : (followerBullet g a' b').1.stock = a'.stock ∧
      (followerBullet g a' b').1.mark = a'.mark ∧
      (followerBullet g a' b').1.leader = a'.leader ∧
      (followerBullet g a' b').2.leader = b'.leader := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl,rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl,rfl⟩
  obtain ⟨h1,h2,h3,h4⟩ := hf (pinned a' b')
  exact ⟨h1.trans (hi.1.trans ha.1),h3.trans (hi.2.2.1.trans ha.2.2),
    h2.trans (hi.2.1.trans ha.2.1),fun h => h4.trans (hi.2.2.2 (hb.trans h))⟩

theorem ghost_pays_iff_ready {p c : Nat} (u z : Site p c)
    (hm : u.mark = true) (hL : z.leader = false) :
    geometricPay u z = payer u := by
  have hM : materialize u z = {u with mark := true} := by simp [materialize,hm]
  obtain ⟨h1,h2,h3,h5⟩ := native_fields (materialize u z) z
  have hA : (materialize u z).mark = true := by rw [hM]
  have hP : payer (native (materialize u z) z).1 = payer u := by
    unfold payer
    rw [h1,h2,hM]
  unfold geometricPay
  simp [hP,h3,hA,h5 hL]

theorem victim_pays_iff_ready {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) :
    let a := s.config (liftedSite v s.donor)
    let b := s.config (rightNeighbor (liftedSite v s.donor))
    geometricPay a b = payer a := by
  rw [← liftedSite_succ]
  exact ghost_pays_iff_ready _ _ h.2.2.2.2.1.marked h.2.2.2.1

#print axioms inner_exclusion_rule
#print axioms source_stock_rule
#print axioms victim_pays_iff_ready


/-- Every physically occupied positive slot up to the old victim payer
counts, including an exposed resident; no lineage or pause flag is added. -/
def realStock {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n) (k : Nat) : Bool :=
  if 0 < k ∧ k ≤ s.donor then (s.config (liftedSite v k)).stock else false

theorem unstopped_fields {p c n : Nat} (v e : Fin n) (s : RankSupplier.Obs p c n)
    (h : s.stopped = false) (ht : (advance v s e).stopped = false) :
    (advance v s e).config = step s.config e ∧
    (advance v s e).donor =
      s.donor + ((e == liftedSite v s.donor) &&
        geometricPay (s.config e) (s.config (rightNeighbor e))).toNat := by
  unfold advance at ht ⊢
  simp only [h,Bool.false_eq_true,if_false] at ht ⊢
  split at ht
  · contradiction
  · rename_i hN
    simp only [hN]
    exact ⟨rfl,rfl⟩

private theorem right_distinct {n : Nat} (hn : 4 ≤ n) (v : Fin n) : rightNeighbor v ≠ v := by
  intro h
  have he : liftedSite v 1 = liftedSite v 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hf := liftedSite_inj v (by omega : 1<n) (by omega : 0<n) he
  omega

theorem realStock_cutoff {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n) (k : Nat)
    (h : s.donor < k ∨ k = 0) : realStock v s k = false := by
  unfold realStock
  split
  · omega
  · rfl

theorem realStock_of_slot {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (k : Nat) (h : 0 < k) (hk : k ≤ s.donor) :
    realStock v s k = (s.config (liftedSite v k)).stock := by simp [realStock,h,hk]

/-- Retained stock and the payment counter see exactly these local cases.
An exterior operation may alter the unmeasured supplier/victim payload,
but it cannot mutate one of the currently measured positive slots. -/
theorem realStock_unaffected {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (r k : Nat) (hnr : r+1<n) (hkn : k<n) (hr : k ≠ r) (hr' : k ≠ r+1)
    (ht : (advance v s (liftedSite v r)).stopped = false)
    (hs : s.stopped = false)
    (hd : (advance v s (liftedSite v r)).donor = s.donor) :
    realStock v (advance v s (liftedSite v r)) k = realStock v s k := by
  have h0 := (unstopped_fields v (liftedSite v r) s hs ht).1
  have hE : liftedSite v k ≠ liftedSite v r := fun he => hr (liftedSite_inj v hkn (by omega) he)
  have hN : liftedSite v k ≠ rightNeighbor (liftedSite v r) := by
    rw [← liftedSite_succ]
    exact fun he => hr' (liftedSite_inj v hkn hnr he)
  simp [realStock,hd,h0,step,hE,hN]

theorem inner_observer {p c n : Nat} (hn : 4 ≤ n) (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (k : Nat) (hk : k < s.donor)
    (ht : (advance v s (liftedSite v k)).stopped = false) :
    let t := advance v s (liftedSite v k)
    t.donor = s.donor ∧
      (t.config (liftedSite v k)).stock =
        (if payer (s.config (liftedSite v k)) && !(s.config (liftedSite v (k+1))).stock
          then false else (s.config (liftedSite v k)).stock) ∧
      (t.config (liftedSite v (k+1))).stock =
        (if payer (s.config (liftedSite v k)) && !(s.config (liftedSite v (k+1))).stock
          then true else (s.config (liftedSite v (k+1))).stock) := by
  let e := liftedSite v k
  have ht0 := unstopped_fields v e s h.1 ht
  have hd0 := h.2.2.2.2.2
  have he : (e == liftedSite v s.donor) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hh := liftedSite_inj v (by omega : k<n) (by omega : s.donor<n) (beq_iff_eq.mp he)
    omega
  have hd' : (advance v s e).donor = s.donor := by simpa [he] using ht0.2
  have hq := inner_stock_rule v s h k hk
  refine ⟨hd',?_,?_⟩
  · change ((advance v s e).config e).stock = _
    rw [ht0.1]
    have hh := congrArg Prod.fst hq
    cases hp : payer (s.config (liftedSite v k)) && !(s.config (liftedSite v (k+1))).stock <;>
      simpa [step,e,← liftedSite_succ,hp] using hh
  · rw [ht0.1]
    have hr : (step s.config e (liftedSite v (k+1))).stock =
        (pairStep (s.config e) (s.config (liftedSite v (k+1)))).2.stock := by
      rw [liftedSite_succ]
      simp [step,e,right_distinct hn (liftedSite v k)]
    rw [hr]
    have hh := congrArg Prod.snd hq
    cases hp : payer (s.config (liftedSite v k)) && !(s.config (liftedSite v (k+1))).stock <;>
      simpa [e,hp] using hh

theorem victim_observer {p c n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s)
    (ht : (advance v s (liftedSite v s.donor)).stopped = false) :
    let e := liftedSite v s.donor
    let z := rightNeighbor e
    let t := advance v s e
    t.donor = s.donor + (payer (s.config e)).toNat ∧
      (t.config z).stock = (s.config z).stock ∧
      (payer (s.config e) = true → (t.config e).stock = false) := by
  dsimp only
  let e := liftedSite v s.donor
  let z := rightNeighbor e
  obtain ⟨hc,hd⟩ := unstopped_fields v e s h.1 ht
  have hpay := victim_pays_iff_ready v s h
  change geometricPay (s.config e) (s.config z) = payer (s.config e) at hpay
  simp only [← show e = liftedSite v s.donor from rfl, beq_self_eq_true,Bool.true_and] at hd
  rw [show geometricPay (s.config e) (s.config (rightNeighbor e)) = _ from hpay] at hd
  refine ⟨hd,?_,?_⟩
  · rw [hc]
    let resident : Option Unit := if (s.config z).stock then some () else none
    let old : Option Unit := if (s.config e).stock then some () else none
    have ha : old.isSome = (s.config e).stock := by cases hS : (s.config e).stock <;> simp [old,hS]
    have hb : resident.isSome = (s.config z).stock := by cases hS : (s.config z).stock <;> simp [resident,hS]
    have hF := RankSupplier.marked_label_fence (s.config e) (s.config z) old resident () h.2.2.2.2.1.marked
    have hL := StockTokenRows.pair_labels (s.config e) (s.config z) old resident () ha hb
    have hStep : (step s.config e z).stock = (pairStep (s.config e) (s.config z)).2.stock := by
      simp [step,z,right_distinct hn e]
    rw [hStep]
    exact ((congrArg Prod.snd hL).symm.trans (congrArg Option.isSome hF)).trans hb
  · intro hP
    rw [hc]
    have hz : geometricPay (s.config e) (s.config z) = true := hpay.trans hP
    have hPref : (stepPrefix (s.config e) (s.config z)).1.stock = false := by
      unfold stepPrefix
      let a := native (materialize (s.config e) (s.config z)) (s.config z)
      have hp : (!a.2.leader && a.1.mark && payer a.1) = true := hz
      change (payment a.1 a.2).1.stock = false
      unfold payment
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
      simp [hp.1.1,hp.1.2,hp.2]
    have ht' := congrArg Prod.fst (pairStep_stocks_eq_prefix (s.config e) (s.config z))
    simpa [step,e] using ht'.trans hPref

/-- At a victim service the old donor is empty afterwards even when
there was no payer: in that case it was already empty and P3 is idle. -/
theorem victim_donor_empty {p c n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s)
    (ht : (advance v s (liftedSite v s.donor)).stopped = false) :
    ((advance v s (liftedSite v s.donor)).config (liftedSite v s.donor)).stock = false := by
  let e := liftedSite v s.donor
  let u := s.config e
  let z := s.config (rightNeighbor e)
  by_cases hp : payer u = true
  · exact (victim_observer hn v s h ht).2.2 hp
  · have hp0 := Bool.eq_false_iff.mpr hp
    have hu : u.stock = false := (Bool.or_eq_false_iff.mp hp0).1
    have hm : u.mark = true := h.2.2.2.2.1.marked
    have hl : z.leader = false := by
      change (s.config (rightNeighbor (liftedSite v s.donor))).leader = false
      rw [← liftedSite_succ]
      exact h.2.2.2.1
    have hMat : materialize u z = {u with mark := true} := by simp [materialize,hm]
    let a := native (materialize u z) z
    obtain ⟨h1,h2,h3,h4⟩ := native_fields (materialize u z) z
    have hmark : a.1.mark = true := by rw [show a.1.mark = _ from h3,hMat]
    have hPay : payer a.1 = false := by
      unfold payer
      rw [show a.1.stock = _ from h1, show a.1.leader = _ from h2,hMat]
      exact hp0
    have hStock : a.1.stock = false := by rw [show a.1.stock = _ from h1,hMat]; exact hu
    have hLeader : a.2.leader = false := h4 hl
    have hPref : (stepPrefix u z).1.stock = false := by
      change (payment a.1 a.2).1.stock = false
      simp [payment,hmark,hPay,hStock,hLeader]
    have hS := (congrArg Prod.fst (pairStep_stocks_eq_prefix u z)).trans hPref
    have hC := (unstopped_fields v e s h.1 ht).1
    change ((advance v s e).config e).stock = false
    rw [hC]
    simpa [step,u,z] using hS

/-- Outside the old source-to-victim arc neither endpoint is a measured
slot. This covers the wraparound bond n−1→0 without treating 0 as a
queued particle. -/
theorem exterior_observer {p c n : Nat} (v : Fin n) (s : RankSupplier.Obs p c n)
    (h : Live v s) (r : Nat) (hr : s.donor < r) (hrn : r < n)
    (ht : (advance v s (liftedSite v r)).stopped = false) :
    let t := advance v s (liftedSite v r)
    t.donor = s.donor ∧ ∀ k, realStock v t k = realStock v s k := by
  let e := liftedSite v r
  let t := advance v s e
  obtain ⟨hC,hD⟩ := unstopped_fields v e s h.1 ht
  have hd := h.2.2.2.2.2
  have hE : (e == liftedSite v s.donor) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hh := liftedSite_inj v hrn (by omega : s.donor<n) (beq_iff_eq.mp he)
    omega
  have hSame : t.donor = s.donor := by simpa [hE] using hD
  refine ⟨hSame,?_⟩
  intro k
  have htarget : rightNeighbor e = liftedSite v (r+1) := (liftedSite_succ v r).symm
  by_cases hk : 0 < k ∧ k ≤ s.donor
  · have hke : liftedSite v k ≠ e := by
      intro he
      have hh := liftedSite_inj v (by omega : k<n) hrn he
      omega
    have hkn : liftedSite v k ≠ rightNeighbor e := by
      intro he
      rw [htarget] at he
      by_cases hrr : r+1<n
      · have hh := liftedSite_inj v (by omega : k<n) hrr he
        omega
      · rw [show r+1=n by omega,liftedSite_full] at he
        have hh := liftedSite_inj v (by omega : k<n) (by omega : 0<n)
          (he.trans (liftedSite_zero v).symm)
        omega
    show realStock v t k = realStock v s k
    simp [realStock,hSame,hk,show t.config = step s.config e from hC,step,hke,hkn]
  · show realStock v t k = realStock v s k
    simp [realStock,hSame,hk]


theorem inner_realStock_update {p c n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s) (r : Nat) (hr : r < s.donor)
    (ht : (advance v s (liftedSite v r)).stopped = false) :
    let t := advance v s (liftedSite v r)
    let pay := payer (s.config (liftedSite v r)) && !realStock v s (r+1)
    ∀ k, realStock v t k =
      if pay && (k == r+1) then true else
        if pay && (k == r) then false else realStock v s k := by
  let t := advance v s (liftedSite v r)
  obtain ⟨hd,hL,hR⟩ := inner_observer hn v s h r hr ht
  change t.donor = s.donor at hd
  have hdN := h.2.2.2.2.2
  have hR0 := realStock_of_slot v s (r+1) (by omega) (by omega)
  change ∀ k, realStock v t k = if (payer (s.config (liftedSite v r)) && !realStock v s (r+1)) && (k == r+1) then true else if (payer (s.config (liftedSite v r)) && !realStock v s (r+1)) && (k == r) then false else realStock v s k
  intro k
  by_cases hk : k = r+1
  · subst k
    rw [realStock_of_slot v t (r+1) (by omega) (by omega),hR,hR0]
    cases hp : payer (s.config (liftedSite v r)) &&
      !(s.config (liftedSite v (r+1))).stock <;> simp
  · have hkb : (k == r+1) = false := Bool.eq_false_iff.mpr (fun h' => hk (beq_iff_eq.mp h'))
    by_cases hkr : k=r
    · subst k
      rw [hR0]
      by_cases hz : r=0
      · have hZ := realStock_cutoff v t r (Or.inr hz)
        have hZ' := realStock_cutoff v s r (Or.inr hz)
        simp [hZ,hZ',hkb]
      · rw [realStock_of_slot v t r (Nat.pos_of_ne_zero hz) (by omega),
          realStock_of_slot v s r (Nat.pos_of_ne_zero hz) (by omega),hL]
        simp [hkb]
    · have hkrb : (k == r) = false := Bool.eq_false_iff.mpr (fun h' => hkr (beq_iff_eq.mp h'))
      by_cases hkn : k<n
      · simpa [hkb,hkrb] using realStock_unaffected v s r k (by omega) hkn hkr hk ht h.1 hd
      · have hZ := realStock_cutoff v t k (Or.inl (by omega))
        have hZ' := realStock_cutoff v s k (Or.inl (by omega))
        simp [hkb,hkrb,hZ,hZ']

theorem victim_realStock_update {p c n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s)
    (ht : (advance v s (liftedSite v s.donor)).stopped = false) :
    let t := advance v s (liftedSite v s.donor)
    let pay := payer (s.config (liftedSite v s.donor))
    ∀ k, realStock v t k =
      if k = s.donor then false else
      if k = s.donor+1 then pay && (s.config (liftedSite v (s.donor+1))).stock
      else realStock v s k := by
  let e := liftedSite v s.donor
  let t := advance v s e
  let pay := payer (s.config e)
  obtain ⟨hd,hz,_⟩ := victim_observer hn v s h ht
  have hdc : t.donor = s.donor + pay.toNat := hd
  have hC : t.config = step s.config e := (unstopped_fields v e s h.1 ht).1
  have hdN := h.2.2.2.2.2
  have hR : (t.config (liftedSite v (s.donor+1))).stock =
      (s.config (liftedSite v (s.donor+1))).stock := by
    rw [liftedSite_succ]
    exact hz
  dsimp only
  intro k
  by_cases hk : k=s.donor
  · subst k
    rw [if_pos rfl]
    unfold realStock
    split
    · exact victim_donor_empty hn v s h ht
    · rfl
  · rw [if_neg hk]
    by_cases hk' : k=s.donor+1
    · subst k
      rw [if_pos rfl]
      change realStock v t (s.donor+1) = (pay && _)
      cases hp : pay
      · have hZ := realStock_cutoff v t (s.donor+1) (Or.inl (by simp [hp] at hdc; omega))
        simp [hZ]
      · rw [realStock_of_slot v t (s.donor+1) (by omega) (by simp [hp] at hdc; omega),hR]
        rfl
    · rw [if_neg hk']
      have hd1 : t.donor ≤ s.donor+1 := by cases hp : pay <;> simp [hp] at hdc <;> omega
      by_cases hr : 0 < k ∧ k ≤ s.donor
      · have hte : liftedSite v k ≠ e := by
          intro he
          have hh := liftedSite_inj v (by omega : k<n) (by omega : s.donor<n) he
          exact hk hh
        have htn : liftedSite v k ≠ rightNeighbor e := by
          intro he
          rw [← show liftedSite v (s.donor+1) = rightNeighbor e from liftedSite_succ v _] at he
          exact hk' (liftedSite_inj v (by omega : k<n) hdN he)
        have hmono : s.donor ≤ t.donor := donor_mono_step v e s
        change realStock v t k = realStock v s k
        rw [realStock_of_slot v t k hr.1 (by omega),realStock_of_slot v s k hr.1 hr.2,hC]
        simp [step,hte,htn]
      · have hs : s.donor < k ∨ k = 0 := by omega
        have ht' : t.donor < k ∨ k = 0 := by omega
        rw [realStock_cutoff v t k ht',realStock_cutoff v s k hs]


open FIFOCompare

/-- Exact paid-head increment: an advance pays at every cut,
subtracts the old payer below its coordinate, and includes any retained
old-head resident once the corridor grows. At a positive cut the payer
term is equivalently combined with the unit payment as `donor < k`. -/
theorem paid_head_cut_increment {p c n d0 : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s) (hd0 : d0 ≤ s.donor)
    (ht : (advance v s (liftedSite v s.donor)).stopped = false)
    (hp : payer (s.config (liftedSite v s.donor)) = true) (k : Nat) (hk : 0 < k) :
    let t := advance v s (liftedSite v s.donor)
    cuts (n-1) (realStock v t) (t.donor-d0) k =
      cuts (n-1) (realStock v s) (s.donor-d0) k +
      (if s.donor < k then 1 else 0) +
      (if k ≤ s.donor+1 then (s.config (liftedSite v (s.donor+1))).stock.toNat else 0) := by
  let t := advance v s (liftedSite v s.donor)
  let r := realStock v s
  let b := (s.config (liftedSite v (s.donor+1))).stock
  have hd : t.donor = s.donor+1 := by
    have hh := (victim_observer hn v s h ht).1
    simpa [t,hp] using hh
  have hd' : t.donor-d0 = (s.donor-d0)+1 := by omega
  have hw : s.donor+1 < n-1 := by
    have hc := (live_step hn v _ s h ht).2.2.2.2.2
    change t.donor+1 < n at hc
    omega
  have hcut : r (s.donor+1) = false := realStock_cutoff v s _ (Or.inl (by omega))
  have hU : realStock v t = setStock (setStock r s.donor false) (s.donor+1) b := by
    funext j
    have hh := victim_realStock_update hn v s h ht j
    change realStock v t j = _ at hh
    by_cases hj : j = s.donor
    · subst j
      simpa [setStock, show s.donor ≠ s.donor+1 by omega] using hh
    · simpa [hj,hp,setStock,r,b] using hh
  have hb := cuts_set (n-1) (setStock r s.donor false) (s.donor-d0+1)
      (s.donor+1) b k
  simp [setStock,hcut,hw] at hb
  have hPay :
      cuts (n-1) (setStock r s.donor false) (s.donor-d0+1) k =
        cuts (n-1) r (s.donor-d0) k + (if s.donor < k then 1 else 0) := by
    by_cases h0 : s.donor = 0
    · have hR : r s.donor = false := realStock_cutoff v s _ (Or.inr h0)
      rw [show setStock r s.donor false = r by rw [← hR,setStock_same]]
      simp [cuts, h0, hk, Nat.add_comm]
    · have hj : 0 < s.donor := by omega
      have hl := inner_nonleader v s h s.donor hj (Nat.le_refl _)
      have hs : (s.config (liftedSite v s.donor)).stock = true := by simpa [payer,hl] using hp
      exact cuts_absorb _ _ _ _ ((realStock_of_slot v s _ hj (Nat.le_refl _)).trans hs) (by omega) _
  change cuts (n-1) (realStock v t) (t.donor-d0) k = _
  rw [hd', hU, hb, hPay]


theorem literal_real_step {p c n d0 : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s) (hd0 : d0 ≤ s.donor) (i : Fin n)
    (ht : (advance v s (liftedSite v i.val)).stopped = false) :
    RealStep (n-1) i.val (realStock v s) (cuts (n-1) (realStock v s) (s.donor-d0))
      (cuts (n-1) (realStock v (advance v s (liftedSite v i.val)))
        ((advance v s (liftedSite v i.val)).donor-d0)) := by
  let j := i.val
  let t := advance v s (liftedSite v j)
  let r := realStock v s
  let width := n-1
  let dep := s.donor-d0
  change RealStep width j r (cuts width r dep) (cuts width (realStock v t) (t.donor-d0))
  have hdN := h.2.2.2.2.2
  by_cases hInner : j < s.donor
  · have hD : t.donor = s.donor := (inner_observer hn v s h j hInner ht).1
    rw [hD]
    change RealStep width j r (cuts width r dep) (cuts width (realStock v t) dep)
    have hEq := inner_realStock_update hn v s h j hInner ht
    let pay := payer (s.config (liftedSite v j)) && !r (j+1)
    by_cases hPay : pay = true
    · have hz : r (j+1) = false := by
        cases hr : r (j+1) <;> simp [pay,hr] at hPay <;> rfl
      have hU : realStock v t = setStock (setStock r j false) (j+1) true := by
        funext k
        have hh := hEq k
        change realStock v t k = (if pay && (k == j+1) then true else if pay && (k == j)
          then false else r k) at hh
        simpa [hPay,setStock,beq_iff_eq] using hh
      rw [hU]
      by_cases hj : j=0
      · have hr0 : r j = false := realStock_cutoff v s j (Or.inr hj)
        rw [show setStock r j false = r by rw [← hr0,setStock_same]]
        have hm (k : Nat) := cuts_inject width r dep (j+1) hz (by omega) k
        refine ⟨?_,?_,?_⟩
        · intro k _ _
          rw [hm]
          exact Nat.le_add_right _ _
        · intro _ _
          rw [hm,if_pos (by omega : 1 ≤ j+1)]
          exact Nat.le_refl _
        · intro hh; omega
      · have hl : (s.config (liftedSite v j)).leader = false :=
          inner_nonleader v s h j (Nat.pos_of_ne_zero hj) (by omega)
        have hh : (s.config (liftedSite v j)).stock = true := by
          simpa [pay,payer,hl,hz] using hPay
        have hS : r j = true := (realStock_of_slot v s j (Nat.pos_of_ne_zero hj) (by omega)).trans hh
        have hm (k : Nat) := cuts_move width r dep j hS hz (by omega) k
        refine ⟨?_,?_,?_⟩
        · intro k _ _
          rw [hm]
          exact Nat.le_add_right _ _
        · intro hc; contradiction
        · intro _ _ _ _
          rw [hm,if_pos rfl]
          exact Nat.le_refl _
    · have hfalse := Bool.eq_false_iff.mpr hPay
      have hU : realStock v t = r := by
        funext k
        have hh := hEq k
        change realStock v t k = (if pay && (k == j+1) then true else if pay && (k == j)
          then false else r k) at hh
        simpa [hfalse] using hh
      rw [hU]
      refine ⟨fun _ _ _ => Nat.le_refl _,?_,?_⟩
      · intro hj hz
        have hl : (s.config (liftedSite v j)).leader = true := by
          rw [hj,liftedSite_zero]; exact h.2.2.1
        exact False.elim (hPay (by simp [pay,payer,hl,hz,show j+1=1 by omega]))
      · intro hj _ hs hz
        have hr := (realStock_of_slot v s j hj (by omega)).symm.trans hs
        exact False.elim (hPay (by simp [pay,payer,hr,hz]))
  · by_cases hHead : j = s.donor
    · have ht' : (advance v s (liftedSite v s.donor)).stopped = false := by simpa [j,hHead] using ht
      let pay := payer (s.config (liftedSite v j))
      have hD : t.donor = s.donor + pay.toNat := by
        have hh := (victim_observer hn v s h ht').1
        simpa [t,hHead,pay] using hh
      have hEq := victim_realStock_update hn v s h ht'
      let fresh := (s.config (liftedSite v (j+1))).stock
      have hU : realStock v t = setStock (setStock r j false) (j+1) (pay && fresh) := by
        funext k
        have hh := hEq k
        change realStock v (advance v s (liftedSite v s.donor)) k = _ at hh
        by_cases hK : k = j
        · have hK' : k ≠ j+1 := by omega
          simpa [t,hHead,setStock,hK,hK',pay,fresh] using hh
        · have hK0 : k ≠ s.donor := by simpa [hHead] using hK
          simpa [t,hHead,setStock,hK0,pay,fresh,r] using hh
      by_cases hPay : pay = true
      · have hD' : t.donor-d0 = dep+1 := by simp [hPay] at hD; omega
        rw [hD',hU]
        have hAdd (k : Nat) :
            cuts width (setStock r j false) (dep+1) k ≤
              cuts width (setStock (setStock r j false) (j+1) (pay && fresh)) (dep+1) k := by
          have hZ : setStock r j false (j+1) = false := by
            have hh : r (j+1) = false := realStock_cutoff v s (j+1) (Or.inl (by omega))
            simp [setStock,hh]
          have hChange := cuts_set width (setStock r j false) (dep+1) (j+1)
            (pay && fresh) k
          simp [hZ] at hChange
          omega
        by_cases hJ : j=0
        · have hZ := realStock_cutoff v s j (Or.inr hJ)
          have hM (k : Nat) :
              cuts width r dep k + 1 ≤ cuts width
                (setStock (setStock r j false) (j+1) (pay && fresh)) (dep+1) k := by
            have hh := hAdd k
            have hSame : setStock r j false = r := by rw [← hZ,setStock_same]
            rw [hSame] at hh ⊢
            unfold cuts at hh ⊢
            omega
          refine ⟨fun k _ _ => Nat.le_trans (Nat.le_add_right _ 1) (hM k),?_,?_⟩
          · intro _ _
            exact hM 1
          · intro hh; omega
        · have hL : (s.config (liftedSite v j)).leader = false :=
            inner_nonleader v s h j (Nat.pos_of_ne_zero hJ) (by omega)
          have hf : (s.config (liftedSite v j)).stock = true := by
            simpa [pay,payer,hL] using hPay
          have hs : r j = true := (realStock_of_slot v s j (Nat.pos_of_ne_zero hJ)
            (by omega)).trans hf
          have hm (k : Nat) := cuts_absorb width r dep j hs (by omega) k
          refine ⟨?_,?_,?_⟩
          · intro k _ _
            have H := hAdd k
            rw [hm] at H
            exact Nat.le_trans (Nat.le_add_right _ _) H
          · intro hzero; contradiction
          · intro _ _ _ _
            have H := hAdd (j+1)
            rwa [hm,if_pos (by omega : j<j+1)] at H
      · have hf := Bool.eq_false_iff.mpr hPay
        have hD' : t.donor = s.donor := by simpa [hf] using hD
        have hSource : (s.config (liftedSite v j)).stock = false :=
          (Bool.or_eq_false_iff.mp hf).1
        have hJ : r j = false := by simp [r,realStock,hSource]
        have hz : r (j+1) = false := realStock_cutoff v s (j+1) (Or.inl (by omega))
        rw [hD',hU]
        change RealStep width j r (cuts width r dep)
          (cuts width (setStock (setStock r j false) (j+1) (pay && fresh)) dep)
        rw [show setStock r j false = r by rw [← hJ,setStock_same],show (pay && fresh) = false by simp [hf],show setStock r (j+1) false = r by rw [← hz,setStock_same]]
        refine ⟨fun _ _ _ => Nat.le_refl _,?_,?_⟩
        · intro hzero _
          have hl : (s.config (liftedSite v j)).leader = true := by
            rw [hzero,liftedSite_zero]
            exact h.2.2.1
          exact False.elim (hPay (by simp [pay,payer,hl]))
        · intro _ _ ht _
          rw [hJ] at ht
          contradiction
    · have hOuter : s.donor < j := by omega
      have htData := exterior_observer v s h j hOuter i.isLt ht
      have hS : realStock v t = r := funext htData.2
      rw [hS,show t.donor = s.donor from htData.1]
      refine ⟨fun _ _ _ => Nat.le_refl _,?_,?_⟩
      · intro hzero; omega
      · intro _ _ hocc _
        have hf : r j = false := realStock_cutoff v s j (Or.inl hOuter)
        rw [hf] at hocc
        contradiction


theorem virtualInit_stock_eq {p c n : Nat} (v : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live v s) :
    asNatStock (virtualInit v s).stock = realStock v s := by
  funext k
  unfold asNatStock
  split
  · rename_i hk
    rfl
  · rename_i hk
    have hd := h.2.2.2.2.2
    exact (realStock_cutoff v s k (Or.inl (by omega))).symm


#print axioms virtualInit_stock_eq
#print axioms paid_head_cut_increment
#print axioms literal_real_step
#print axioms inner_realStock_update
#print axioms victim_realStock_update
#print axioms inner_observer
#print axioms victim_observer
#print axioms victim_donor_empty
#print axioms exterior_observer

end L4.RankSupplierPhysical
