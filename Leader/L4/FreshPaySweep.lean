import Leader.L4.RankSupplierPhysical

namespace L4.FreshPaySweep
open RankSupplier RankSupplierPhysical FIFOCompare

def ready {p c n : Nat} (v : Fin n) (s : Obs p c n) (d k : Nat) : Prop :=
  s.stopped = true ∨ d < s.donor ∨
    (k ≤ d ∧ (k = 0 ∨ 0 < cuts (n-1) (realStock v s) (s.donor-d) k))

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

private theorem real_projection {p c n : Nat} (hn : 4≤n)
    (v : Fin n) (s : Obs p c n) (d : Nat) (hd : d≤s.donor)
    (hs : Live v s) (e : Fin n) (ht : (advance v s e).stopped=false) :
    ∃ l, l<n ∧ liftedSite v l=e ∧
      RealStep (n-1) l (realStock v s)
        (cuts (n-1) (realStock v s) (s.donor-d))
        (cuts (n-1) (realStock v (advance v s e)) ((advance v s e).donor-d)) := by
  obtain ⟨l,hl,he⟩ := liftedSite_of_site v e
  refine ⟨l,hl,he,?_⟩
  have H := literal_real_step hn v s hs hd ⟨l,hl⟩ (he.symm ▸ ht)
  rwa [he] at H

theorem ready_wait {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (d k : Nat) (hd : d≤s.donor) (e : Fin n)
    (h : Live v s ∨ s.stopped=true) (hr : ready v s d k) :
    ready v (advance v s e) d k := by
  let t := advance v s e
  by_cases ht : t.stopped=true
  · exact Or.inl ht
  have ht' : t.stopped=false := Bool.eq_false_iff.mpr ht
  have hs : Live v s := h.resolve_right (fun H => ht (by simp [t,advance,H]))
  rcases hr with hR | hR | ⟨hk,hR⟩
  · exact False.elim (Bool.noConfusion (hR.symm.trans hs.1))
  · exact Or.inr (Or.inl (Nat.lt_of_lt_of_le hR (donor_mono_step v e s)))
  · refine Or.inr (Or.inr ⟨hk,?_⟩)
    rcases hR with heq | hpos
    · exact Or.inl heq
    · by_cases hk0 : k=0
      · exact Or.inl hk0
      have hc : k≤n-1 := by have := hs.2.2.2.2.2; omega
      obtain ⟨_,_,_,hp⟩ := real_projection hn v s d hd hs e ht'
      exact Or.inr (Nat.lt_of_lt_of_le hpos (hp.monotone k (by omega) hc))

theorem ready_nomination {p c n : Nat} (hn : 4≤n) (v : Fin n)
    (s : Obs p c n) (d k : Nat) (hd : d≤s.donor)
    (h : Live v s ∨ s.stopped=true) (hr : ready v s d k) :
    ready v (advance v s (liftedSite v k)) d (k+1) := by
  let e := liftedSite v k
  let t := advance v s e
  by_cases ht : t.stopped=true
  · exact Or.inl ht
  have ht' : t.stopped=false := Bool.eq_false_iff.mpr ht
  have hs : Live v s := h.resolve_right (fun H => ht (by simp [t,advance,H]))
  have hd' : d≤t.donor := Nat.le_trans hd (donor_mono_step v e s)
  by_cases hmore : d<t.donor
  · exact Or.inr (Or.inl hmore)
  have hdT : t.donor=d := by omega
  have hdS : s.donor=d := by
    have := donor_mono_step v e s
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
    have ht0 : (advance v s (liftedSite v s.donor)).stopped=false := by
      simpa [e,t,hdS] using ht'
    have hGo := (victim_observer hn v s hs ht0).1
    have hOut : t.donor=d+1 := by simpa [t,e,hdS,hp] using hGo
    omega
  · have hk1 : k+1≤d := by omega
    have hw : k+1<n-1 := by omega
    have h0 : 0<k+1 := by omega
    let S := realStock v s
    let R := cuts (n-1) S (s.donor-d)
    let R' := cuts (n-1) (realStock v t) (t.donor-d)
    have hProjection := literal_real_step hn v s hs hd (⟨k,by omega⟩ : Fin n) ht'
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

/-- Contiguous segment of the nominated lifted edges, in order. This
word is fixed at the epoch entry; matches need not be consecutive raw marks. -/
def path {n : Nat} (v : Fin n) (i : Nat) : Nat → List (Fin n)
  | 0 => []
  | m+1 => liftedSite v i :: path v (i+1) m

private theorem live_or_stopped_step {p c n : Nat} (hn : 4≤n)
    (v e : Fin n) (s : Obs p c n) (h : Live v s ∨ s.stopped=true) :
    Live v (advance v s e) ∨ (advance v s e).stopped=true := by
  by_cases ht : (advance v s e).stopped=true
  · exact Or.inr ht
  have hs := h.resolve_right (fun h' => ht (by simp [advance,h']))
  exact Or.inl (live_step hn v e s hs (Bool.eq_false_iff.mpr ht))

theorem ready_after_sublist {p c n : Nat} (hn : 4≤n)
    (v : Fin n) (d : Nat) {u w : List (Fin n)} (sub : u.Sublist w) :
      ∀ (s : Obs p c n) (k m : Nat),
        u = path v k m → d≤s.donor → (Live v s ∨ s.stopped=true) →
        ready v s d k → ready v (track v s w) d (k+m) := by
  induction sub with
  | slnil =>
    intro s k m he _ _ hr
    cases m with
    | zero => simpa [track,GGTiming.runMarks] using hr
    | succ m => simp [path] at he
  | @cons u w e _ ih =>
    intro s k m he hd hs hr
    exact ih (advance v s e) k m he
      (Nat.le_trans hd (donor_mono_step v e s))
      (live_or_stopped_step hn v e s hs) (ready_wait hn v s d k hd e hs hr)
  | @cons_cons u w e _ ih =>
    intro s k m he hd hs hr
    cases m with
    | zero => simp [path] at he
    | succ m =>
      have hh := List.cons.inj he
      obtain ⟨heq,hu⟩ := hh
      subst e
      have h := ih (advance v s (liftedSite v k)) (k+1) m hu
        (Nat.le_trans hd (donor_mono_step v _ s))
        (live_or_stopped_step hn v _ s hs) (ready_nomination hn v s d k hd hs hr)
      change ready v (track v (advance v s (liftedSite v k)) w) d (k+(m+1))
      simpa only [show k + (m+1) = k+1+m by omega] using h

/-- No strict, unpaid epoch can contain all h nominated services.
The terminal mark may stop without the observer crediting a payment. -/
theorem paid_or_stopped_of_path {p c n : Nat} (hn : 4≤n)
    (v : Fin n) (s : Obs p c n) (hs : Live v s) (w : List (Fin n))
    (sub : (path v 0 (s.donor+1)).Sublist w) :
    (track v s w).stopped=true ∨ s.donor<(track v s w).donor := by
  have hh := ready_after_sublist hn v s.donor sub s 0 (s.donor+1) rfl
    (Nat.le_refl _) (Or.inl hs) (Or.inr (Or.inr ⟨Nat.zero_le _,Or.inl rfl⟩))
  rcases hh with ha | hb | ⟨hc,_⟩
  · exact Or.inl ha
  · exact Or.inr hb
  · omega

end L4.FreshPaySweep

