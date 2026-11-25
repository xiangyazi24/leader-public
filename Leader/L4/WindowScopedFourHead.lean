import Leader.L4.WindowScopedRoute
import Leader.L4.QueueDAG

namespace L4.WindowScopedFourHead
open RankSupplier RankSupplierPhysical FIFOCompare WindowScopedSupplier RankPhysical

private theorem tail_zero (lo width k : Nat) (stock : Nat → Bool)
    (h : ∀ j, lo ≤ j → stock j = false) (hk : lo≤k) : tailSlots width stock k=0 := by
  rw [tailSlots]
  split
  · rw [h k hk,tail_zero lo width (k+1) stock h (by omega)]
    rfl
  · rfl
termination_by width-k

private theorem tail_at_small_width (lo hi : Nat) (stock : Nat → Bool)
    (hle : lo≤hi) (h : ∀ j, lo ≤ j → stock j = false) (k : Nat) :
    tailSlots hi stock k = tailSlots lo stock k := by
  by_cases hk : k < lo
  · have hh : k < hi := by omega
    have hl : tailSlots hi stock k = (stock k).toNat + tailSlots hi stock (k+1) := by rw [tailSlots,if_pos hh]
    have hr : tailSlots lo stock k = (stock k).toNat + tailSlots lo stock (k+1) := by rw [tailSlots,if_pos hk]
    rw [hl,hr,tail_at_small_width lo hi stock hle h (k+1)]
  · rw [tail_zero lo hi k stock h (by omega),tail_zero lo lo k stock h (by omega)]
termination_by lo-k

/-- Exact stock tail refinement at the short fixed outlet (width=m+1).
The caller supplies the four-head geometric cap, not absence of global
events. This is a real counterpart to the virtual short line. -/
theorem short_real_step {p c n d d0 width : Nat} (hn : 4≤n) (v : Fin n)
    (x : Config p c n) (l : Fin n)
    (h : Live v (init x d)) (hd0 : d0≤d)
    (hret : liftedSite v l.val=liftedSite v d →
      retirement x (liftedSite v l.val)=false)
    (hLive : Live v (follow v d x (liftedSite v l.val)))
    (hw : width≤n-1) (hcap : d<width)
    (hcap' : (follow v d x (liftedSite v l.val)).donor<width) :
    let s := init x d
    let t := follow v d x (liftedSite v l.val)
    RealStep width l.val (realStock v s)
      (cuts width (realStock v s) (d-d0))
      (cuts width (realStock v t) (t.donor-d0)) := by
  let s := init x d
  let t := follow v d x (liftedSite v l.val)
  have hs (k : Nat) : cuts (n-1) (realStock v s) (d-d0) k =
      cuts width (realStock v s) (d-d0) k := by
    unfold cuts
    rw [tail_at_small_width width (n-1) _ hw
      (fun j hj => realStock_cutoff v s j (Or.inl (by change d<j; omega)))]
  change t.donor < width at hcap'
  have ht (k : Nat) : cuts (n-1) (realStock v t) (t.donor-d0) k =
      cuts width (realStock v t) (t.donor-d0) k := by
    unfold cuts
    rw [tail_at_small_width width (n-1) _ hw
      (fun j hj => realStock_cutoff v t j (Or.inl (by change t.donor<j; omega)))]
  have H := real_cut_after_local_step hn v x l h hd0 hret hLive
  change RealStep (n-1) l.val (realStock v s) _ _ at H
  exact ⟨fun k hk hl => hs k ▸ ht k ▸ H.monotone k hk (by omega),
    fun hi hv => hs 1 ▸ ht 1 ▸ H.source hi hv,
    fun hi hiw ho hv => hs (l.val+1) ▸ ht (l.val+1) ▸ H.crossing hi (by omega) ho hv⟩

theorem compare_short_mark {p c n d d0 width : Nat} (hn : 4≤n) (v : Fin n)
    (x : Config p c n) (l : Fin n)
    (h : Live v (init x d)) (hd0 : d0≤d)
    (hret : liftedSite v l.val=liftedSite v d →
      retirement x (liftedSite v l.val)=false)
    (hLive : Live v (follow v d x (liftedSite v l.val)))
    (hw : width≤n-1) (hp : 2≤width) (hcap : d<width)
    (hcap' : (follow v d x (liftedSite v l.val)).donor<width)
    (stock : Nat → Bool) (dep : Nat) (V' : Nat → Nat)
    (hV : VirtualDelta width l.val stock (cuts width stock dep) V')
    (hOld : ∀ k, 0<k → k≤width →
      cuts width stock dep k ≤ cuts width (realStock v (init x d)) (d-d0) k) :
    ∀ k, 0<k → k≤width → V' k ≤ cuts width
      (realStock v (follow v d x (liftedSite v l.val)))
      ((follow v d x (liftedSite v l.val)).donor-d0) k :=
  compare_single_step width l.val hp _ stock (d-d0) dep _ V' hV
    (short_real_step hn v x l h hd0 hret hLive hw hcap hcap')
    (realStock_cutoff v (init x d) width (Or.inl hcap)) hOld

/-- Arithmetic cap and nominal clock cost if the farther head's physical
ledger bounds its advance by the two entry gaps. -/
theorem four_head_budget (n a b c j w : Nat)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (h : j<w)
    (hW : w≤a+b+(b+c)) (hJ : j<n) :
    let P := 2*b+c+1
    let m := min (n-2) (a+P-1)
    j-a<P ∧ j≤m+1 ∧ 4*n*(2*P+m+1)≤40*n*(a+b+c+1) := by
  dsimp only
  have H : 2*(2*b+c+1)+min (n-2) (a+(2*b+c+1)-1)+1 ≤ 10*(a+b+c+1) := by
    have := Nat.min_le_right (n-2) (a+(2*b+c+1)-1)
    omega
  refine ⟨by omega,?_,?_⟩
  · rw [Nat.min_def]
    split <;> omega
  · calc
      _ ≤ (4*n)*(10*(a+b+c+1)) := Nat.mul_le_mul_left _ H
      _ = _ := by
        calc
          _ = n*(4*10)*(a+b+c+1) := by ac_rfl
          _ = _ := by rw [Nat.mul_comm n (4*10)]

#print axioms short_real_step
#print axioms compare_short_mark
#print axioms four_head_budget


open SevenTagCharge in
private theorem ordinary_newGhost_after_pay {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (v : Fin n)
    (h : Live v (init x d))
    (hS : (step x (liftedSite v d) v).leader = true)
    (pay : geometricPay (x (liftedSite v d)) (x (rightNeighbor (liftedSite v d)))=true)
    (hret : retirement x (liftedSite v d)=false) :
    (step x (liftedSite v d) (liftedSite v (d+2))).leader = false := by
  let e := liftedSite v d
  let r := rightNeighbor e
  let w := liftedSite v (d+2)
  have hNext := firstMark_after_local_step hn x v e h.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    h.2.2.1 hS (fun _ => hret)
  have hcap : d+2<n := by simpa [e,init,pay] using hNext.2
  have hR : r = liftedSite v (d+1) := (liftedSite_succ v d).symm
  have he : w ≠ e := fun q => by
    have H := liftedSite_inj v hcap (show d<n by omega) q
    omega
  have hr : w ≠ r := fun q => by
    rw [hR] at q
    have H := liftedSite_inj v hcap (show d+1<n by omega) q
    omega
  have hM : (x r).mark = false := by
    change (geometricPay (x e) (x r) && (x r).mark)=false at hret
    simpa [pay,e,r] using hret
  have hW : (x w).leader = false := by
    apply Bool.eq_false_iff.mpr
    intro hw
    have hne : rightNeighbor r = w := by rw [hR,←liftedSite_succ]
    have H := h.2.1 r (.inl (hne.symm ▸ hw))
    change (x r).mark=true at H
    rw [hM] at H
    cases H
  change (step x e w).leader=false
  have hr' : w ≠ rightNeighbor e := hr
  simpa [step,he,hr'] using hW


open SevenTagCharge in
theorem ordinary_follow_of_keep {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n)) (z : Ledger p c n) (e a : Fin n)
    (h : Live v (init z.config d)) (hz : Valid z z0)
    (sv label : Fin n) (hsub : cert ⊆ group) (hcert : label ∈ cert)
    (hsite : rightNeighbor sv=v) (hsupp : WindowLocal.TaggedLeader z sv label)
    (ha : a ∈ group) (hs : z.slots (liftedSite v d)=some a)
    (hkeep : WindowLocal.route group cert (some a) z e = .keep) :
    let t := follow v d z.config e
    (e=liftedSite v d → retirement z.config e=false) ∧
    Live v t ∧ (SevenTagCharge.advance z e).slots (liftedSite v t.donor) = some a := by
  have hc := hz.sourceCover
  have hnoloss : WindowLocal.selectedGroupLoss group z e=none := by
    unfold WindowLocal.route at hkeep
    split at hkeep
    · rename_i b hb
      cases hkeep
    · assumption
  have hret (he : e=liftedSite v d) : retirement z.config e=false :=
    tracked_no_retirement_of_group_keep group z e a ha (he ▸ hs) hnoloss
  let t := follow v d z.config e
  refine ⟨hret,?_,?_⟩
  · have hS := (WindowLocal.certified_stationary_of_keep hn z0 z group cert (some a)
      e sv label hz hsub hcert hsupp hkeep).2
    rw [hsite] at hS
    have hm := (EntranceCover.cover_closed hn z.config e ⟨hz.markCover,hc⟩).1
    have hnext := firstMark_after_local_step hn z.config v e hz.markCover h.2.2.2.2.1
      h.2.2.2.2.2 h.2.2.1 hS hret
    refine ⟨rfl,hm,hS,?_,hnext.1,hnext.2⟩
    by_cases he : e=liftedSite v d
    · subst e
      by_cases hp : geometricPay (z.config (liftedSite v d))
          (z.config (rightNeighbor (liftedSite v d)))=true
      · simpa [follow,init,hp] using ordinary_newGhost_after_pay hn z.config v h hS hp (hret rfl)
      · have hf := Bool.eq_false_iff.mpr hp
        change (step z.config (liftedSite v d)
          (liftedSite v ((follow v d z.config (liftedSite v d)).donor+1))).leader=false
        rw [show (follow v d z.config (liftedSite v d)).donor=d by simp [follow,init,hf]]
        apply Bool.eq_false_iff.mpr
        intro hL
        have hb : WindowLocal.birthAt z.config (liftedSite v d)=true := by
          unfold WindowLocal.birthAt
          have hg : (z.config (liftedSite v (d+1))).leader=false := h.2.2.2.1
          rw [←liftedSite_succ,hg,hL]
          rfl
        have hh := (WindowLocal.target_birth_result hn group cert z (liftedSite v d) a
          hz.markCover hc hs hb).1
        rw [hh] at hkeep
        cases hkeep
    · have hb : (e == liftedSite v d)=false :=
        Bool.eq_false_iff.mpr (fun h => he (beq_iff_eq.mp h))
      change ((step z.config e) (liftedSite v ((follow v d z.config e).donor+1))).leader=false
      rw [show (follow v d z.config e).donor=d by simp [follow,init,hb]]
      let u := liftedSite v (d+1)
      have hR : rightNeighbor e≠u := by
        intro H
        exact he (FreshSeparation.succ_inj (H.trans (liftedSite_succ v d)))
      have hU : (z.config u).leader=false := h.2.2.2.1
      change (step z.config e u).leader=false
      by_cases hE : u=e
      · rw [hE] at hU ⊢
        simp [step,(pair_geometric_fields (z.config e) (z.config (rightNeighbor e))).2.1,hU]
      · simpa [step,hE,Ne.symm hR] using hU
  · by_cases he : e=liftedSite v d
    · subst e
      by_cases hp : geometricPay (z.config (liftedSite v d))
        (z.config (rightNeighbor (liftedSite v d)))=true
      · have hM : (z.config (rightNeighbor (liftedSite v d))).mark=false := by
          have H := hret rfl
          change (geometricPay _ _ && (z.config (rightNeighbor (liftedSite v d))).mark)=false at H
          simpa [hp] using H
        have hm0 : (z.slots (rightNeighbor (liftedSite v d))).isSome=false :=
          (hz.covers _).trans hM
        have hm : z.slots (rightNeighbor (liftedSite v d)) = none := by
          cases hh : z.slots (rightNeighbor (liftedSite v d)) <;> simp_all
        rw [show (follow v d z.config (liftedSite v d)).donor=d+1 by simp [follow,init,hp],
          liftedSite_succ]
        exact (by simpa [SevenTagCharge.advance,slotsStep,hp,hm,hs] using
          (paid_mover_or_resident hn z.slots (liftedSite v d)).2)
      · simp [follow,init,SevenTagCharge.advance,slotsStep,hp,hs]
    · have hb : (e == liftedSite v d)=false := Bool.eq_false_iff.mpr
          (fun h => he (beq_iff_eq.mp h))
      rw [show (follow v d z.config e).donor=d by simp [follow,init,hb]]
      by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
      · by_cases hr : liftedSite v d=rightNeighbor e
        · have hs' : z.slots (rightNeighbor e)=some a := hr ▸ hs
          change slotsStep z.config z.slots e (liftedSite v d)=some a
          rw [hr,show slotsStep z.config z.slots e = SevenTagCharge.move z.slots e by simp [slotsStep,hp],
            (paid_mover_or_resident hn z.slots e).2,hs']
          rfl
        · change slotsStep z.config z.slots e (liftedSite v d)=some a
          simp [slotsStep,hp,SevenTagCharge.move,Ne.symm he,hr,hs]
      · simp [SevenTagCharge.advance,slotsStep,hp,hs]


#print axioms ordinary_follow_of_keep

open SevenTagCharge WindowLocal in
/-- At the quiet entrance every live impact has a nearest living
shooter, including same-mark N0. A living W immediately after a
ghost J therefore stays living and at its old tag. -/
theorem living_after_ghost_stays {p c n d : Nat} (hn : 4≤n)
    (z : Ledger p c n) (e j w label : Fin n)
    (hq : QuietEntrance z.config) (ht : Covers z.config z.slots)
    (hJ : (z.config j).mark=true) (hg : (z.config (rightNeighbor j)).leader=false)
    (hW : TaggedLeader z w label)
    (hF : FirstMark z.config (rightNeighbor j) d)
    (hEnd : liftedSite (rightNeighbor j) d=w) :
    TaggedLeader (SevenTagCharge.advance z e) w label := by
  apply living_tag_stays hn z w e label hq.2.1 hW.1 hW.2
  intro he
  subst e
  apply Bool.eq_false_iff.mpr
  intro hd
  obtain ⟨i,a,f,hi,hLiving,hf,hE,hBefore,_⟩ :=
    killing_shooter_pre_mark hn z w hq ht hd
  have hI : (z.config i).mark=true := by simpa [hi] using (ht i).symm
  have hh := nearest_shooting_root_unique z.config j i d f hJ hI (hEnd.trans hE.symm)
    (fun k hk => Bool.eq_false_iff.mpr (hF.before k hk)) hBefore
  rw [←hh.1,hg] at hLiving
  cases hLiving

#print axioms living_after_ghost_stays

open GGTiming RankRenewal in
/-- Transfer the short-line dependency clock to an arbitrary actual
observer. The wordwise premise is only required if the actual trial
has not exited. The same raw word drives the shadow and the observer. -/
theorem short_clock_of_shadow {α β : Type} {n m P : Nat} (hn : 0<n)
    (next : α → Fin n → α) (done : α → Prop) (x : α)
    (shadow : β → Fin n → β) (good : β → Prop) (height : β → Nat → Nat)
    (edge : Nat → Fin n)
    (rule : QueueDAG.HeightRules shadow good height m edge)
    (keep : ∀ b e, good b → good (shadow b e))
    (b : β) (hb : good b)
    (hcap : ∀ w, ¬done (runMarks next x w) → height (runMarks shadow b w) m<P) :
    IIDExpectedHittingTimeAtMost next done x (4*n*(2*P+m+1)) := by
  apply hittingTime_of_path_certificate next done x hn (QueueDAG.outletPaths m edge P)
    (2*P+m) (QueueDAG.outletPaths_span m edge P) (QueueDAG.outletPaths_count m edge P)
  intro w hw
  apply Classical.byContradiction
  intro h
  have hs := QueueDAG.outletPaths_complete rule keep b hb P w hw
  exact Nat.not_lt_of_ge hs (hcap w h)

#print axioms short_clock_of_shadow

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

/-- The exact paid marked row drops one resident byte if the payer is
nonliving, regardless of the age/rail/type of the victim (which may
have been killed by this action). This is the unit of charge for W,
and offsets at most one newly exposed old-K resident when K moves. -/
theorem paid_nonliving_stock_charge {p c : Nat} (u v : Site p c)
    (hn : u.leader=false) (hm : u.mark=true) (hp : geometricPay u v=true) :
    RearFrontStock.stockBit (pairStep u v).1 +
      RearFrontStock.stockBit (pairStep u v).2 + 1 =
      RearFrontStock.stockBit u + RearFrontStock.stockBit v := by
  let a := native (materialize u v) v
  have hpay : payer a.1=true := by
    change (!a.2.leader && a.1.mark && payer a.1)=true at hp
    exact (Bool.and_eq_true_iff.mp hp).2
  have hf := native_fields (materialize u v) v
  have hmat : materialize u v = {u with mark := true} := by simp [materialize,hm]
  have hs : u.stock=true := by
    unfold payer at hpay
    change (a.1.stock || a.1.leader)=true at hpay
    rw [show a.1.stock = u.stock by simpa [a,hmat] using hf.1,
      show a.1.leader = false by simpa [a,hmat,hn] using hf.2.1] at hpay
    simpa using hpay
  obtain ⟨hl,hr⟩ := GGStockPhysical.marked_stock_consumed u v hm hs
  simp [RearFrontStock.stockBit,hs,hl,hr]
  omega

#print axioms paid_nonliving_stock_charge
end L4.WindowScopedFourHead
