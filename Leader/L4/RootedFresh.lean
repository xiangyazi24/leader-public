import Leader.L4.FreshInvariant

namespace L4.RootedFresh
open TaggedTrace

theorem mark_exists_step {p c n : Nat} (hn : 4≤n) (x : Config p c n) (e : Fin n)
    (hm : MCOV x) (h : ∃ i, (x i).mark=true) : ∃ i, (step x e i).mark=true := by
  by_cases hp : geometricPay (x e) (x (rightNeighbor e))=true
  · refine ⟨rightNeighbor e,?_⟩
    have hn' : rightNeighbor e≠e := by
      intro h
      have H : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
      have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) H
      omega
    rw [covered_step_mark hn x hm]
    simp [hp,hn']
  obtain ⟨i,hi⟩ := h
  exact ⟨i,by rw [covered_step_mark hn x hm]; simp [hp,hi]⟩

theorem quiet_step {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hq : QuietEntrance x) :
    QuietEntrance (step x e) := by
  have hCover := EntranceCover.cover_closed hn x e ⟨hq.1,hq.2.1⟩
  refine ⟨hCover.1,hCover.2,mark_exists_step hn x e hq.1 hq.2.2.1,?_⟩
  have hf : freshAt x (fun _ => False) := fun i hi _ => hq.2.2.2 i hi
  have H := rootIndependentFreshMaskStep x (fun _ => False) e hp hc hn
    hq.1 hq.2.1 (fun _ hv => hv.elim) hf
  exact fun b hb => H b hb (fun ⟨_,h,_⟩ => h)

theorem quiet_run {p c n : Nat} (x : Config p c n) (w : List (Fin n))
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hq : QuietEntrance x) :
    QuietEntrance (run x w) := by
  induction w generalizing x with
  | nil => exact hq
  | cons e w ih => exact ih (step x e) (quiet_step x e hp hc hn hq)

theorem fresh_trace {p c n : Nat} (x : Config p c n) (w : List (Fin n))
    (hp : 2≤p) (hcal : 12≤c) (hn : 4≤n) (hm : MCOV x) (hc : COV x) :
    freshAt (run x w) (originalTagAt (trackAll (allInit x) w)) := by
  have loop (w : List (Fin n)) (x : Config p c n) (s : AllObs p c n)
      (hs : ∀ i,(s i).config=x) (hm : MCOV x) (hc : COV x)
      (hlive : ∀ b, originalTagAt s b → (x b).bullet=.live)
      (hfresh : freshAt x (originalTagAt s)) :
      freshAt (run x w) (originalTagAt (trackAll s w)) := by
    induction w generalizing x s with
    | nil => exact hfresh
    | cons e w ih =>
      have hmask := originalTagAt_step_iff hs e
      have ⟨hm',hc'⟩ := EntranceCover.cover_closed hn x e ⟨hm,hc⟩
      apply ih (step x e) (allAdvance s e) (fun i => by
        change (advance (s i) e).config=step x e
        rw [projection_step,hs i]) hm' hc'
      · intro b h
        exact nextTagMask_live hn x _ hlive e b ((hmask b).mp h)
      · intro b hbl hbt
        exact rootIndependentFreshMaskStep x _ e hp hcal hn hm hc hlive hfresh b hbl
          (fun h => hbt ((hmask b).mpr h))
  exact loop w x (allInit x) (fun _ => rfl) hm hc
    (fun b => (originalTagAt_init_iff x b).mp)
    (fun b hl hn => False.elim (hn ((originalTagAt_init_iff x b).mpr hl)))

theorem peace_after_extinction {p c n : Nat} (x : Config p c n) (w : List (Fin n))
    (hp : 2≤p) (hcal : 12≤c) (hn : 4≤n) (hm : MCOV x) (hc : COV x)
    (hend : allEnded (trackAll (allInit x) w)) :
    PeacefulLive (run x w) := by
  intro b hb
  apply fresh_trace x w hp hcal hn hm hc b hb
  rintro ⟨i,hi⟩
  apply hend
  refine ⟨i,?_⟩
  intro h
  have H : (trackAll (allInit x) w i).carrier=none := h
  rw [hi] at H
  contradiction

end L4.RootedFresh
