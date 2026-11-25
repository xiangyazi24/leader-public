import Leader.L4.WindowScopedSupplier
import Leader.L4.FreshPaySweep
namespace L4.WindowScopedWait
open RankSupplier RankSupplierPhysical FIFOCompare FreshPaySweep WindowScopedSupplier RankPhysical

private theorem tail_zero_after_donor {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (k : Nat) (hk : s.donor < k) : tailSlots (n-1) (realStock v s) k = 0 := by
  rw [tailSlots]
  split
  · rw [realStock_cutoff v s k (Or.inl hk),
      tail_zero_after_donor v s (k+1) (by omega)]
    rfl
  · rfl
termination_by (n-1)-k
decreasing_by omega

private theorem donor_of_positive {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (h : Live v s) (d : Nat) (hd : s.donor=d)
    (hk : 0 < cuts (n-1) (realStock v s) (s.donor-d) d) :
    realStock v s d = true := by
  have H := cuts_adjacent (n-1) (realStock v s) (s.donor-d) d
    (by have := h.2.2.2.2.2; omega)
  have h0 : cuts (n-1) (realStock v s) (s.donor-d) (d+1) = 0 := by
    rw [cuts,tail_zero_after_donor v s _ (by omega),hd,Nat.sub_self,Nat.add_zero]
  rw [h0] at H
  cases hb : realStock v s d
  · rw [hb] at H
    change _ = 0+0 at H
    omega
  · rfl

theorem ready_nomination_follow {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (d k : Nat) (hd : d≤s.donor)
    (hs : Live v s) (hs0 : s = init s.config s.donor)
    (hret : liftedSite v k=liftedSite v s.donor → retirement s.config (liftedSite v k)=false)
    (ht : Live v (follow v s.donor s.config (liftedSite v k))) (hr : ready v s d k) :
    ready v (follow v s.donor s.config (liftedSite v k)) d (k+1) := by
  let e := liftedSite v k
  let t := follow v s.donor s.config e
  have mono : s.donor ≤ t.donor := Nat.le_add_right _ _
  have hd' : d≤t.donor := Nat.le_trans hd mono
  by_cases hmore : d<t.donor
  · exact Or.inr (Or.inl hmore)
  have hdT : t.donor=d := by omega
  have hdS : s.donor=d := by
    have := mono
    change s.donor≤t.donor at this
    omega
  rcases hr with hR | hR | ⟨hk,hR⟩
  · exact False.elim (Bool.noConfusion (hR.symm.trans hs.1))
  · omega
  have hdN := hs.2.2.2.2.2
  by_cases hK : k=d
  · subst k
    have hp : payer (s.config (liftedSite v d)) = true := by
      by_cases h0 : d=0
      · simp [h0,liftedSite_zero,payer,hs.2.2.1]
      · have hc := hR.resolve_left h0
        have hS := donor_of_positive v s hs d hdS hc
        have hStock := (realStock_of_slot v s d (Nat.pos_of_ne_zero h0) (by omega)).symm.trans hS
        simp [payer,hStock]
    have hg : geometricPay (s.config (liftedSite v d))
        (s.config (rightNeighbor (liftedSite v d)))=true := by
      rw [← hdS]
      exact (victim_pays_iff_ready v s hs).trans (by simpa [hdS] using hp)
    have hOut : t.donor=d+1 := by simp [t,e,follow,init,hdS,hg]
    omega
  · have hk1 : k+1≤d := by omega
    have hw : k+1<n-1 := by omega
    have h0 : 0<k+1 := by omega
    let S := realStock v s
    let R := cuts (n-1) S (s.donor-d)
    let R' := cuts (n-1) (realStock v t) (t.donor-d)
    have hProjection := real_cut_after_local_step hn v s.config (⟨k,by omega⟩ : Fin n)
      (hs0 ▸ hs) hd hret ht
    rw [← hs0] at hProjection
    have H : 0<R' (k+1) := by
      by_cases old : 0<R (k+1)
      · exact Nat.lt_of_lt_of_le old (hProjection.monotone _ h0 (by omega))
      · have hr0 : R (k+1)=0 := by omega
        have hz : S (k+1)=false := by
          have hA := cuts_adjacent (n-1) S (s.donor-d) (k+1) hw
          change R (k+1) = (S (k+1)).toNat + R (k+2) at hA
          cases he : S (k+1)
          · rfl
          · rw [he,hr0] at hA
            change 0 = 1+R (k+2) at hA
            omega
        rcases hR with hk0 | hPos
        · have hz' : S 1=false := by simpa [hk0] using hz
          have hh := hProjection.source hk0 hz'
          simpa [hk0,R,R',t,e] using (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hh)
        · by_cases hk0 : k=0
          · have hz' : S 1=false := by simpa [hk0] using hz
            have hh := hProjection.source hk0 hz'
            simpa [hk0,R,R',t,e] using (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hh)
          have hh := cuts_adjacent (n-1) S (s.donor-d) k (by omega)
          change R k = (S k).toNat + R (k+1) at hh
          have hs' : S k=true := by
            cases he : S k
            · rw [he,hr0] at hh
              change R k = 0+0 at hh
              change 0<R k at hPos
              omega
            · rfl
          have hklt : k < n-1 := by omega
          exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ _)
            (hProjection.crossing (Nat.pos_of_ne_zero hk0) hklt hs' hz)
    exact Or.inr (Or.inr ⟨hk1,Or.inr H⟩)

/-- Any retained mark preserves the current short-watch certificate,
including an exterior retirement. -/
theorem ready_wait_follow {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (d k : Nat) (hd : d≤s.donor) (e : Fin n)
    (hs : Live v s) (hs0 : s = init s.config s.donor)
    (hret : e=liftedSite v s.donor → retirement s.config e=false)
    (ht : Live v (follow v s.donor s.config e)) (hr : ready v s d k) :
    ready v (follow v s.donor s.config e) d k := by
  let t := follow v s.donor s.config e
  have hm : s.donor ≤ t.donor := Nat.le_add_right _ _
  rcases hr with hR | hR | ⟨hk,hR⟩
  · exact False.elim (Bool.noConfusion (hR.symm.trans hs.1))
  · exact Or.inr (Or.inl (Nat.lt_of_lt_of_le hR hm))
  · refine Or.inr (Or.inr ⟨hk,?_⟩)
    rcases hR with heq | hpos
    · exact Or.inl heq
    · by_cases hk0 : k=0
      · exact Or.inl hk0
      obtain ⟨l,hl,he⟩ := liftedSite_of_site v e
      subst e
      have hp := real_cut_after_local_step hn v s.config ⟨l,hl⟩ (hs0 ▸ hs) hd hret ht
      rw [← hs0] at hp
      have hc : k≤n-1 := by have := hs.2.2.2.2.2; omega
      exact Or.inr (Nat.lt_of_lt_of_le hpos (hp.monotone k (by omega) hc))

theorem ready_complete_follow {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (d : Nat) (h : Live v s) (hr : ready v s d (d+1)) : d<s.donor := by
  rcases hr with hs | hs | ⟨hs,_⟩
  · exact False.elim (Bool.noConfusion (hs.symm.trans h.1))
  · exact hs
  · omega

/-- While monitoring the original distance d, foreign marks remain actual
marks but leave the nominated-prefix count unchanged. At completion the
count is capped (we never nominate d+1). -/
def tickCount {n : Nat} (v : Fin n) (d k : Nat) (e : Fin n) : Nat :=
  if k ≤ d ∧ e = liftedSite v k then k+1 else k

theorem tickCount_preserves_ready {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (d k : Nat) (hd : d≤s.donor) (e : Fin n)
    (hs : Live v s) (hs0 : s = init s.config s.donor)
    (hret : e=liftedSite v s.donor → retirement s.config e=false)
    (ht : Live v (follow v s.donor s.config e)) (hr : ready v s d k) :
    ready v (follow v s.donor s.config e) d (tickCount v d k e) := by
  unfold tickCount
  split
  · rename_i he
    have heq := he.2
    subst e
    exact ready_nomination_follow hn v s d k hd hs hs0 hret ht hr
  · exact ready_wait_follow hn v s d k hd e hs hs0 hret ht hr

def rawWatch {p c n : Nat} (v : Fin n) (d : Nat) (s : Obs p c n × Nat)
    (e : Fin n) : Obs p c n × Nat :=
  (follow v s.1.donor s.1.config e, tickCount v d s.2 e)

/-- Conditions on retained prefixes only. The watch does not enforce or
postulate no global rank drop: both its physical projection and its
distance counter always run. -/
inductive RetainedWord {p c n : Nat} (v : Fin n) :
    Obs p c n → List (Fin n) → Prop where
  | nil {s} : RetainedWord v s []
  | cons {s e w} :
      (e = liftedSite v s.donor → retirement s.config e=false) →
      Live v (follow v s.donor s.config e) →
      RetainedWord v (follow v s.donor s.config e) w →
      RetainedWord v s (e::w)

theorem rawWatch_ready {p c n : Nat} (hn : 4≤n) (v : Fin n) (d : Nat)
    (s : Obs p c n) (w : List (Fin n)) (hw : RetainedWord v s w)
    (hd : d≤s.donor) (hs : Live v s) (hs0 : s = init s.config s.donor)
    (k : Nat) (hr : ready v s d k) :
    let r := w.foldl (rawWatch v d) (s,k)
    Live v r.1 ∧ ready v r.1 d r.2 := by
  induction hw generalizing k with
  | nil => exact ⟨hs,hr⟩
  | @cons s e w hret ht hw ih =>
    let t := follow v s.donor s.config e
    have hd' : d≤t.donor := Nat.le_trans hd (Nat.le_add_right _ _)
    exact ih hd' ht rfl _ (tickCount_preserves_ready hn v s d k hd e hs hs0 hret ht hr)

theorem rawWatch_complete {p c n : Nat} (hn : 4≤n) (v : Fin n) (d : Nat)
    (x : Config p c n) (w : List (Fin n))
    (hw : RetainedWord v (init x d) w) (hs : Live v (init x d))
    (hDone : w.foldl (tickCount v d) 0=d+1) :
    d < (w.foldl (rawWatch v d) (init x d,0)).1.donor := by
  have proj (s : Obs p c n) (k : Nat) :
      (w.foldl (rawWatch v d) (s,k)).2 = w.foldl (tickCount v d) k := by
    clear hw hDone
    induction w generalizing s k with
    | nil => rfl
    | cons e w ih => exact ih (follow v s.donor s.config e) (tickCount v d k e)
  have H := rawWatch_ready hn v d (init x d) w hw (Nat.le_refl _) hs rfl 0
    (Or.inr (Or.inr ⟨Nat.zero_le _, Or.inl rfl⟩))
  exact ready_complete_follow v _ d H.1 (by simpa [proj,hDone] using H.2)

end L4.WindowScopedWait
