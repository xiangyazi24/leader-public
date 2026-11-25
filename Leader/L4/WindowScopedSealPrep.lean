import Leader.L4.WindowScopedRace
import Leader.L4.WindowScopedSealedMean
import Leader.L4.TripleDirtyPrep

/-! Scoped physical sealing, with unrelated events left on the original
raw tape. Here d is the last donor offset, so sector length is d+1. -/
namespace L4.WindowScopedSealPrep
open WindowLocalNative WindowLocal SevenTagCharge WindowScopedRace FixedResidual TripleRenewal

structure Sector {p c n : Nat} (initial : Config p c n)
    (group cert : List (Fin n)) (d : Nat) where
  hn : 4≤n
  bd : d+1<n
  l : Fin n
  r : Fin n
  s : Fin n
  t : Fin n
  sub : cert ⊆ group
  hl : l ∈ cert
  hr : r ∈ cert

variable {p c n d : Nat} {initial : Config p c n} {group cert : List (Fin n)}

def Sector.Valid (S : Sector initial group cert d) (z : Cursor p c n) : Prop :=
  Cursor.exit z ∨ (SevenTagCharge.Valid z.1 initial ∧ CertifiedSector z.1 S.l S.r S.s S.t d)

theorem Sector.keep (S : Sector initial group cert d) (z : Cursor p c n) (e : Fin n)
    (h : S.Valid z) : S.Valid (cursorNext group cert z e) := by
  by_cases he : route group cert none z.1 e=Event.keep
  · cases h with
    | inl h => exact .inl (by simp [cursorNext,Cursor.exit,show z.2=true from h])
    | inr h =>
      exact .inr ⟨valid_step S.hn z.1 initial e h.1,
        certifiedSector_keep S.hn initial z.1 group cert none e S.l S.r S.s S.t d
          h.1 S.sub S.hl S.hr h.2 he⟩
  · exact .inl (by simp [cursorNext,Cursor.exit,he])

theorem Sector.valid_run (S : Sector initial group cert d) (z : Cursor p c n)
    (w : List (Fin n)) (h : S.Valid z) : S.Valid (GGTiming.runMarks (cursorNext group cert) z w) := by
  induction w generalizing z with
  | nil => exact h
  | cons e w ih => exact ih _ (S.keep z e h)

private theorem find_least {p c n d : Nat} (x : Config p c n) (s : Fin n) :
    (∃ q, q≤d ∧ LeastBullet x s q) ∨ ∀ j, j≤d → (x (liftedSite s j)).bullet=.none := by
  classical
  induction d with
  | zero =>
    by_cases H : (x (liftedSite s 0)).bullet=.none
    · right
      intro j hj
      have eq : j=0 := by omega
      rwa [eq]
    · left
      exact ⟨0,Nat.zero_le _,H,fun i hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ d ih =>
    rcases ih with h|h
    · left
      obtain ⟨q,hq,hL⟩ := h
      exact ⟨q,by omega,hL⟩
    · by_cases hE : (x (liftedSite s (d+1))).bullet=.none
      · right
        intro j hj
        by_cases H : j=d+1
        · rwa [H]
        · exact h j (by omega)
      · left
        exact ⟨d+1,Nat.le_refl _,hE,fun j hj => h j (by omega)⟩

inductive DirtyPhase where
  | bullet (q : Nat)
  | returning (q : Nat)

def DirtyPhase.Valid {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) : DirtyPhase → Prop
  | .bullet q => q≤d ∧ LeastBullet x s q
  | .returning q => DirtyReturn x s d q

private theorem phase_exists {p c n d : Nat} (x : Config p c n) (s : Fin n) :
    ∃ ph : DirtyPhase, ph.Valid x s d := by
  rcases find_least (d:=d) x s with h|h
  · obtain ⟨q,h⟩ := h
    exact ⟨.bullet q,h⟩
  · obtain ⟨q,h⟩ := dirtyReturn_exists x s h
    exact ⟨.returning q,h⟩

noncomputable def pickPhase {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) : DirtyPhase :=
  Classical.choose (phase_exists (d:=d) x s)

private theorem pickPhase_valid {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) :
    (pickPhase x s d).Valid x s d := Classical.choose_spec (phase_exists (d:=d) x s)

private theorem phase_unique {p c n d : Nat} {x : Config p c n} {s : Fin n}
    (ph ph' : DirtyPhase) (h : ph.Valid x s d) (h' : ph'.Valid x s d) : ph=ph' := by
  cases ph with
  | bullet q =>
    cases ph' with
    | bullet r =>
      have a : q≤r := by
        by_cases H : q≤r
        · exact H
        · exact (h'.2.occupied (h.2.before r (by omega))).elim
      have b : r≤q := by
        by_cases H : r≤q
        · exact H
        · exact (h.2.occupied (h'.2.before q (by omega))).elim
      have E : q=r := by omega
      rw [E]
    | returning r => exact (h.2.occupied (h'.empty q h.1)).elim
  | returning q =>
    cases ph' with
    | bullet r => exact (h'.2.occupied (h.empty r h'.1)).elim
    | returning r =>
      have a : q≤r := by
        by_cases H : q≤r
        · exact H
        · have hq := h.le
          exact (h'.positive (by omega) (h.before r (by omega))).elim
      have b : r≤q := by
        by_cases H : r≤q
        · exact H
        · have hr := h'.le
          exact (h.positive (by omega) (h'.before q (by omega))).elim
      have E : q=r := by omega
      rw [E]

def DirtyPhase.reserve (d : Nat) : DirtyPhase → Nat
  | .bullet q => 2*(d+1)-q
  | .returning q => q

def DirtyPhase.nominate {n : Nat} (s : Fin n) : DirtyPhase → Fin n
  | .bullet q => liftedSite s q
  | .returning q => liftedSite s (q-1)


def Positive (s : Fin n) (z : Cursor p c n) : Prop :=
  Cursor.exit z ∨ (z.1.config s).signal≠.zero

noncomputable def reserve (s : Fin n) (d : Nat) (z : Cursor p c n) : Nat := by
  classical
  exact if Positive s z then 0 else (pickPhase z.1.config s d).reserve d

private theorem phase_budget_pos {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (ph : DirtyPhase) (h : ph.Valid x s d) (hs : (x s).signal=.zero) :
    0<ph.reserve d := by
  cases ph with
  | bullet q =>
    have hh : q≤d := h.1
    simp only [DirtyPhase.reserve]
    omega
  | returning q =>
    apply Nat.pos_of_ne_zero
    intro H
    change q=0 at H
    subst q
    exact h.positive (Nat.zero_le _) (by simpa [liftedSite_zero] using hs)

theorem reserve_step (S : Sector initial group cert d) (y : Cursor p c n)
    (e : Fin n) (hg : S.Valid y) (hl : ¬ Positive (rightNeighbor S.s) y) :
    reserve (rightNeighbor S.s) d (cursorNext group cert y e) +
      (if e=(pickPhase y.1.config (rightNeighbor S.s) d).nominate (rightNeighbor S.s)
        then 1 else 0) ≤ reserve (rightNeighbor S.s) d y := by
  classical
  let s := rightNeighbor S.s
  have hn := S.hn
  have bd := S.bd
  let ph := pickPhase y.1.config s d
  have hV : ph.Valid y.1.config s d := pickPhase_valid _ _ _
  have h0 : (y.1.config s).signal=.zero := Classical.not_not.mp (fun hh => hl (.inr hh))
  have G := hg.resolve_left (fun hh => hl (.inl hh))
  have hSource : (y.1.config s).leader=true := G.2.left_live.2
  have hDest : (y.1.config (liftedSite s (d+1))).leader=true := by
    dsimp [s]
    rw [G.2.terminal_site]
    exact G.2.right_live.2
  have B := phase_budget_pos y.1.config s ph hV h0
  by_cases hp : Positive s (cursorNext group cert y e)
  · rw [reserve,if_pos hp,reserve,if_neg hl]
    change 0+(if e=ph.nominate s then 1 else 0)≤ph.reserve d
    split <;> omega
  · have he : route group cert none y.1 e = Event.keep := by
      apply Classical.not_not.mp; intro hh
      apply hp
      exact .inl (by simp [cursorNext,Cursor.exit,hh])
    have noS : rightNeighbor e=s → nativeDeath y.1.config e=false :=
      certified_no_death_on_keep hn initial y.1 group cert none e S.s S.l
        G.1 S.sub S.hl G.2.left_live he
    have hstep : (cursorNext group cert y e).1.config=step y.1.config e := rfl
    rw [reserve,if_neg hp,reserve,if_neg hl,hstep]
    change (pickPhase (step y.1.config e) s d).reserve d +
      (if e=ph.nominate s then 1 else 0)≤ph.reserve d
    cases hph : ph with
    | bullet q =>
      have H : q≤d ∧ LeastBullet y.1.config s q := by
        rw [hph] at hV
        exact hV
      by_cases he' : e=liftedSite s q
      · subst e
        by_cases hq : q<d
        · have hh := leastBullet_progress hn y.1.config s G.1.markCover G.1.sourceCover G.2.gap bd hq h0 H.2
          have eq := phase_unique (pickPhase (step y.1.config (liftedSite s q)) s d) (.bullet (q+1))
            (pickPhase_valid _ _ _) (show _ ∧ _ from ⟨by omega,hh⟩)
          rw [eq]
          simp [DirtyPhase.reserve,DirtyPhase.nominate]
          omega
        · have Hq : q=d := by have := H.1; omega
          subst q
          have noT := certified_no_death_on_keep hn initial y.1 group cert none
            (liftedSite s d) S.t S.r G.1 S.sub S.hr G.2.right_live he
            (by rw [←liftedSite_succ]; exact G.2.terminal_site)
          have E := leastBullet_terminal y.1.config s bd H.2 hDest noT
          obtain ⟨r,hR⟩ := dirtyReturn_exists (step y.1.config (liftedSite s d)) s E
          have eq := phase_unique (pickPhase (step y.1.config (liftedSite s d)) s d) (.returning r)
            (pickPhase_valid _ _ _) hR
          rw [eq]
          have hh := hR.le
          simp [DirtyPhase.reserve,DirtyPhase.nominate]
          omega
      · have K := leastBullet_wait y.1.config s e G.1.markCover G.1.sourceCover G.2.gap hSource
          h0 H.1 H.2 noS he'
        have eq := phase_unique (pickPhase (step y.1.config e) s d) (.bullet q)
          (pickPhase_valid _ _ _) (show _ ∧ _ from ⟨H.1,K⟩)
        rw [eq]
        simp [DirtyPhase.reserve,DirtyPhase.nominate,he']
    | returning q =>
      have H : DirtyReturn y.1.config s d q := by rw [hph] at hV; exact hV
      cases q with
      | zero =>
        have hz : (y.1.config (liftedSite s 0)).signal=.zero := by simpa [liftedSite_zero] using h0
        exact (H.positive (Nat.zero_le _) hz).elim
      | succ q =>
        have hh := dirtyReturn_step y.1.config s e G.1.markCover G.1.sourceCover G.2.gap bd
          hSource hDest H noS
        have eq := phase_unique (pickPhase (step y.1.config e) s d)
          (.returning (if e=liftedSite s q then q else q+1)) (pickPhase_valid _ _ _) hh
        rw [eq]
        by_cases hE : e=liftedSite s q <;> simp [DirtyPhase.reserve,DirtyPhase.nominate,hE]

private theorem reserve_bound {p c n : Nat} (s : Fin n) (d : Nat) (y : Cursor p c n) :
    reserve s d y ≤ 2*(d+1) := by
  classical
  have H := pickPhase_valid y.1.config s d
  unfold reserve
  split
  · exact Nat.zero_le _
  · cases h : pickPhase y.1.config s d with
    | bullet q =>
      simp only [DirtyPhase.reserve]
      exact Nat.sub_le _ _
    | returning q =>
      rw [h] at H
      have hh : q≤d+1 := H.le
      simp only [DirtyPhase.reserve]
      omega

/-- Initial leftmost-bullet cleanup and backward first-positive colour
cost at most twice the sector length in nominated hits. -/
theorem expected_positive (S : Sector initial group cert d)
    (y : Cursor p c n) (h : S.Valid y) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) (Positive (rightNeighbor S.s)) y
      (n*(2*(d+1))) := by
  let s := rightNeighbor S.s
  let next := cursorNext (p:=p) (c:=c) group cert
  let clock : Countdown next (Positive s) y :=
    { budget := fun w => reserve s d (GGTiming.runMarks next y w)
      nominate := fun w => (pickPhase (GGTiming.runMarks next y w).1.config s d).nominate s
      decrease := by
        intro w hw e
        rw [GGTiming.runMarks_append]
        exact reserve_step S _ e (S.valid_run y w h) hw }
  intro t
  exact Nat.le_trans (expected_of_countdown _ _ _ clock t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (reserve_bound s d y)))


def Launched (s : Fin n) (d : Nat) (z : Cursor p c n) : Prop :=
  Cursor.exit z ∨ ReturnFront z.1.config s d 0 ∨ ∃ q, q≤d ∧ ZeroFront z.1.config s q

def Sealed (s : Fin n) (d : Nat) (z : Cursor p c n) : Prop :=
  Cursor.exit z ∨ ReturnFront z.1.config s d 0

theorem incident_or_hold (S : Sector initial group cert d) (z : Cursor p c n)
    (e : Fin n) (hG : S.Valid z) (hp : Positive (rightNeighbor S.s) z) :
    let s := rightNeighbor S.s
    let y := cursorNext group cert z e
    Launched s d y ∨ (Positive s y ∧ e≠s) := by
  let s := rightNeighbor S.s
  by_cases hs : Cursor.exit z
  · exact .inl (.inl (by simp [cursorNext,Cursor.exit,show z.2=true from hs]))
  by_cases he : route group cert none z.1 e=Event.keep
  · have G := hG.resolve_left hs
    have pos := hp.resolve_left hs
    by_cases hE : e=s
    · subst e
      apply Or.inl
      apply Or.inr
      by_cases hd : d=0
      · left
        have ht : rightNeighbor s=rightNeighbor S.t := by
          simpa [s,hd,liftedSite_succ,liftedSite_zero] using G.2.terminal_site
        have hL : (z.1.config (rightNeighbor s)).leader=true := ht.symm ▸ G.2.right_live.2
        have hD := certified_no_death_on_keep S.hn initial z.1 group cert none s S.t S.r
          G.1 S.sub S.hr G.2.right_live he ht
        change ReturnFront (step z.1.config s) s d 0
        simpa [hd] using (sourceOutgoing_adjacent_ready _ _ G.2.left_live.2 hL pos hD).1
      · right
        have hD := Nat.pos_of_ne_zero hd
        exact ⟨1,hD,(sourceOutgoing_starts_front S.hn _ s G.1.markCover G.1.sourceCover
          G.2.gap hD G.2.left_live.2 pos).1⟩
    · by_cases hR : rightNeighbor e=s
      · have hD := certified_no_death_on_keep S.hn initial z.1 group cert none e S.s S.l
          G.1 S.sub S.hl G.2.left_live he hR
        exact .inl (.inr (.inr ⟨0,Nat.zero_le _,
          (sourceIncoming_starts_front S.hn _ e s hR G.2.left_live.2 pos hD).1⟩))
      · refine .inr ⟨.inr ?_,hE⟩
        change (step z.1.config e s).signal≠.zero
        simpa [step,Ne.symm hE,Ne.symm hR] using pos
  · exact .inl (.inl (by simp [cursorNext,Cursor.exit,he]))

theorem expected_launch (S : Sector initial group cert d)
    (y : Cursor p c n) (h : S.Valid y) (hP : Positive (rightNeighbor S.s) y) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) (Launched (rightNeighbor S.s) d) y n := by
  let s := rightNeighbor S.s
  let next := cursorNext (p:=p) (c:=c) group cert
  classical
  let good := fun z : Cursor p c n => S.Valid z ∧ (Launched s d z ∨ Positive s z)
  let budget := fun z : Cursor p c n => if Launched s d z then 0 else 1
  have H := TripleControlled.mean_of_potential next (Launched s d) good budget
    (fun z e hz hL => by
      have H := incident_or_hold S z e hz.1 (hz.2.resolve_left hL)
      refine ⟨S.keep z e hz.1,?_⟩
      rcases H with hh|hh
      · exact .inl hh
      · exact .inr hh.1)
    (fun z hz hL => by
      by_cases hY : Launched s d (next z s)
      · apply TripleControlled.progress_raw_drift (budget z) s (fun e => budget (next z e))
        · simp [budget,hL,hY]
        · intro e
          dsimp [budget]
          rw [if_neg hL]
          split <;> decide
      · have K := (incident_or_hold S z s hz.1 (hz.2.resolve_left hL)).resolve_left hY
        exact (K.2 rfl).elim) y ⟨h,.inr hP⟩
  intro t
  refine Nat.le_trans (H t) (Nat.mul_le_mul_right _ ?_)
  simp only [budget]
  split <;> simp

private theorem mean_compose {α : Type} {n : Nat} (next : α → Fin n → α)
    (cut goal good : α → Prop) (keep : ∀ y e, good y → good (next y e))
    (A B : Nat) (y : α) (hy : good y)
    (first : IIDExpectedHittingTimeAtMost next cut y A)
    (rest : ∀ z, good z → cut z → IIDExpectedHittingTimeAtMost next goal z B) :
    IIDExpectedHittingTimeAtMost next goal y (A+B) := by
  intro t
  have H := glue_until_stop next next id (fun _ _ => rfl) goal cut good keep B t
    (fun z u hG hC _ _ => rest z hG hC u) t (Nat.le_refl _) y hy
  rw [Nat.add_mul]
  exact Nat.le_trans H (Nat.add_le_add (first t)
    (Nat.mul_le_mul_left _ (terminalMass_le_total next cut (fun z => ¬goal z) t y)))


inductive Sweep where
  | front (q : Nat)
  | back (q : Nat)

def Sweep.Valid (x : Config p c n) (s : Fin n) (d : Nat) : Sweep → Prop
  | .front q => q≤d ∧ ZeroFront x s q
  | .back q => ReturnFront x s d q

def Sweep.budget (d : Nat) : Sweep → Nat
  | .front q => 2*d+1-q
  | .back q => q

def Sweep.edge (s : Fin n) : Sweep → Fin n
  | .front q => liftedSite s q
  | .back q => liftedSite s (q-1)

theorem Sweep.unique {x : Config p c n} {s : Fin n} (a b : Sweep)
    (ha : a.Valid x s d) (hb : b.Valid x s d) : a=b := by
  cases a with
  | front q =>
    cases b with
    | front r =>
      have h1 : ¬q<r := fun h => ha.2.bullet (hb.2.swept q h).2
      have h2 : ¬r<q := fun h => hb.2.bullet (ha.2.swept r h).2
      rw [show q=r by omega]
    | back r => exact (ha.2.bullet (hb.empty q ha.1)).elim
  | back q =>
    cases b with
    | front r => exact (hb.2.bullet (ha.empty r hb.1)).elim
    | back r =>
      have h1 : ¬q<r := fun h => by
        have H := hb.before q h
        rw [ha.one] at H
        cases H
      have h2 : ¬r<q := fun h => by
        have H := ha.before r h
        rw [hb.one] at H
        cases H
      rw [show q=r by omega]

noncomputable def sweepPick (x : Config p c n) (s : Fin n) (d : Nat) : Sweep := by
  classical
  exact if h : ∃ Q : Sweep, Q.Valid x s d then Classical.choose h else .back 0

theorem sweep_pick_valid (x : Config p c n) (s : Fin n) (d : Nat)
    (h : ∃ Q : Sweep, Q.Valid x s d) : (sweepPick x s d).Valid x s d := by
  unfold sweepPick
  rw [dif_pos h]
  exact Classical.choose_spec h

def SweepGood (S : Sector initial group cert d) (z : Cursor p c n) : Prop :=
  S.Valid z ∧ (Cursor.exit z ∨ ∃ Q : Sweep, Q.Valid z.1.config (rightNeighbor S.s) d)

theorem sweep_of_launch (S : Sector initial group cert d) (z : Cursor p c n)
    (hv : S.Valid z) (h : Launched (rightNeighbor S.s) d z) : SweepGood S z := by
  refine ⟨hv,?_⟩
  rcases h with he|hh
  · exact .inl he
  · apply Or.inr
    rcases hh with hR|⟨q,hq,hF⟩
    · exact ⟨.back 0,hR⟩
    · exact ⟨.front q,hq,hF⟩

theorem sweep_next (S : Sector initial group cert d) (z : Cursor p c n) (e : Fin n)
    (h : SweepGood S z) (hActive : ¬ Sealed (rightNeighbor S.s) d z) :
    let s := rightNeighbor S.s
    let y := cursorNext group cert z e
    Cursor.exit y ∨ ∀ Q : Sweep, Q.Valid z.1.config s d →
      ∃ R : Sweep, R.Valid y.1.config s d ∧
        R.budget d+(if e=Q.edge s then 1 else 0) ≤ Q.budget d := by
  let s := rightNeighbor S.s
  by_cases hx : Cursor.exit z
  · exact .inl (by simp [cursorNext,Cursor.exit,show z.2=true from hx])
  by_cases he : route group cert none z.1 e=Event.keep
  · have G := h.1.resolve_left hx
    have H := scoped_sweep_or_return_step S.hn initial z.1 group cert none e S.l S.r S.s S.t
      d S.bd G.1 S.sub S.hl S.hr G.2 he
    right
    intro Q hq
    cases Q with
    | front q =>
      have hh := H.2.1 q hq.1 hq.2
      by_cases hE : e=liftedSite s q
      · rw [if_pos hE] at hh
        by_cases hqd : q<d
        · rw [if_pos hqd] at hh
          exact ⟨.front (q+1),⟨by omega,hh⟩,by simp [Sweep.edge,Sweep.budget,s,hE]; omega⟩
        · rw [if_neg hqd] at hh
          have Hqd : q=d := by have := hq.1; omega
          subst q
          exact ⟨.back d,hh,by simp [Sweep.edge,Sweep.budget,s,hE]; omega⟩
      · rw [if_neg hE] at hh
        exact ⟨.front q,⟨hq.1,hh⟩,by simp [Sweep.edge,s,hE]⟩
    | back q =>
      cases q with
      | zero =>
        exact (hActive (.inr hq)).elim
      | succ q =>
        have hh := H.2.2.1 q hq
        by_cases hE : e=liftedSite s q
        · rw [if_pos hE] at hh
          exact ⟨.back q,hh,by simp [Sweep.edge,Sweep.budget,s,hE]⟩
        · rw [if_neg hE] at hh
          exact ⟨.back (q+1),hh,by simp [Sweep.edge,s,hE]⟩
  · exact .inl (by simp [cursorNext,Cursor.exit,he])

noncomputable def sweepValue (s : Fin n) (d : Nat) (z : Cursor p c n) : Nat := by
  classical
  exact if Sealed s d z then 0 else (sweepPick z.1.config s d).budget d

theorem Sweep.budget_pos {x : Config p c n} {s : Fin n} (Q : Sweep)
    (h : Q.Valid x s d) (hN : ¬ReturnFront x s d 0) : 0<Q.budget d := by
  cases Q with
  | front q =>
    have hh := h.1
    simp only [Sweep.budget]
    omega
  | back q =>
    cases q with
    | zero => exact (hN h).elim
    | succ q => exact Nat.succ_pos _

theorem Sweep.budget_le {x : Config p c n} {s : Fin n} (Q : Sweep)
    (h : Q.Valid x s d) : Q.budget d ≤ 2*d+1 := by
  cases Q with
  | front q => exact Nat.sub_le _ _
  | back q =>
    have hh := h.le
    simp only [Sweep.budget]
    omega

theorem expected_sweep (S : Sector initial group cert d) (z : Cursor p c n)
    (hV : S.Valid z) (hL : Launched (rightNeighbor S.s) d z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) (Sealed (rightNeighbor S.s) d) z
      (n*(2*d+1)) := by
  classical
  let s := rightNeighbor S.s
  let next := cursorNext (p:=p) (c:=c) group cert
  have hg := sweep_of_launch S z hV hL
  have pick (w : Cursor p c n) (hw : SweepGood S w) (hs : ¬Sealed s d w) :
      (sweepPick w.1.config s d).Valid w.1.config s d :=
    sweep_pick_valid _ _ _ (hw.2.resolve_left (fun he => hs (.inl he)))
  have closed (w : Cursor p c n) (e : Fin n) (hw : SweepGood S w) (hs : ¬Sealed s d w) :
      SweepGood S (next w e) := by
    refine ⟨S.keep w e hw.1,?_⟩
    rcases sweep_next S w e hw hs with he|hE
    · exact .inl he
    · obtain ⟨R,hR,_⟩ := hE _ (pick w hw hs)
      exact .inr ⟨R,hR⟩
  have spend (w : Cursor p c n) (e : Fin n) (hw : SweepGood S w) (hs : ¬Sealed s d w) :
      sweepValue s d (next w e)+(if e=(sweepPick w.1.config s d).edge s then 1 else 0)
        ≤ sweepValue s d w := by
    let Q := sweepPick w.1.config s d
    have hQ : Q.Valid w.1.config s d := pick w hw hs
    simp only [sweepValue,if_neg hs]
    by_cases he : Sealed s d (next w e)
    · rw [if_pos he]
      have hP := Q.budget_pos hQ (fun hh => hs (.inr hh))
      change 0+(if e=Q.edge s then 1 else 0)≤Q.budget d
      split <;> omega
    · rw [if_neg he]
      have hh := (sweep_next S w e hw hs).resolve_left (fun hh => he (.inl hh))
      obtain ⟨R,hR,hB⟩ := hh Q hQ
      have H : sweepPick (next w e).1.config s d=R :=
        Sweep.unique _ _ (sweep_pick_valid _ _ _ ⟨R,hR⟩) hR
      change (sweepPick (next w e).1.config s d).budget d+(if e=Q.edge s then 1 else 0)≤Q.budget d
      rwa [H]
  have M := TripleControlled.mean_of_potential next (Sealed s d) (SweepGood S)
    (sweepValue s d) closed
    (fun w hw hs => by
      let e := (sweepPick w.1.config s d).edge s
      exact TripleControlled.progress_raw_drift _ e _
        (by simpa only [e,if_true] using spend w e hw hs)
        (fun i => Nat.le_trans (Nat.le_add_right _ _) (spend w i hw hs))) z hg
  apply TripleRenewal.expected_mono M
  apply Nat.mul_le_mul_left
  by_cases hz : Sealed s d z
  · simp [sweepValue,hz]
  · rw [sweepValue,if_neg hz]
    exact Sweep.budget_le _ (pick z hg hz)

/-- The advertised six-hit coefficient can in fact be four. Bounds
are uniform over inherited native payload and exterior kill/retirement. -/
theorem expected_seal (S : Sector initial group cert d) (z : Cursor p c n)
    (h : S.Valid z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) (Sealed (rightNeighbor S.s) d) z
      (4*n*(d+1)) := by
  let s := rightNeighbor S.s
  let next := cursorNext (p:=p) (c:=c) group cert
  have launchMean := mean_compose next (Positive s) (Launched s d) S.Valid S.keep
    _ _ z h (expected_positive S z h) (expected_launch S)
  have H := mean_compose next (Launched s d) (Sealed s d) S.Valid S.keep
    _ _ z h launchMean (expected_sweep S)
  have he : n*(2*(d+1))+n+n*(2*d+1)=4*n*(d+1) := by
    calc
      _ = n*(2*(d+1)+1+(2*d+1)) := by simp only [Nat.mul_add,Nat.mul_one]
      _ = n*(4*(d+1)) := congrArg (n*·) (by omega)
      _ = _ := by ac_rfl
  simpa only [he] using H

#print axioms reserve_step
#print axioms expected_positive
#print axioms incident_or_hold
#print axioms expected_launch
#print axioms sweep_next
#print axioms expected_seal

open TriplePhase

def Context.leftSector {v : Fin n} {a b : Nat} (C : Context initial group cert v a b) :
    Sector initial group cert a :=
  ⟨C.hn,by have := C.size; omega,C.l,C.m,C.s,C.t,C.sub,C.left_mem,C.mid_mem⟩

def Context.rightSector {v : Fin n} {a b : Nat} (C : Context initial group cert v a b) :
    Sector initial group cert b :=
  ⟨C.hn,by have := C.size; omega,C.m,C.r,C.t,C.u,C.sub,C.mid_mem,C.right_mem⟩

def PairGeom {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (z : Cursor p c n) : Prop :=
  (Context.leftSector C).Valid z ∧ (Context.rightSector C).Valid z

def LeftPrepared {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (z : Cursor p c n) : Prop :=
  PairGeom C z ∧ (Cursor.exit z ∨ ∃ l : Phase, l.Holds z.1.config (rightNeighbor C.s) a)

theorem pairGeom_keep {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (z : Cursor p c n) (e : Fin n) (h : PairGeom C z) :
    PairGeom C (cursorNext group cert z e) :=
  ⟨(Context.leftSector C).keep z e h.1,(Context.rightSector C).keep z e h.2⟩

theorem leftPrepared_keep {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (z : Cursor p c n) (e : Fin n) (h : LeftPrepared C z) :
    LeftPrepared C (cursorNext group cert z e) := by
  refine ⟨pairGeom_keep C z e h.1,?_⟩
  by_cases hx : Cursor.exit z
  · exact .inl (by simp [cursorNext,Cursor.exit,show z.2=true from hx])
  by_cases he : route group cert none z.1 e=Event.keep
  · obtain ⟨ph,hph⟩ := h.2.resolve_left hx
    have H := h.1.1.resolve_left hx
    have T := WindowSealed.certified_tick_keep C.hn initial z.1 group cert none e C.l C.m C.s C.t
      (Context.leftSector C).bd H.1 C.sub C.left_mem C.mid_mem H.2 he ph hph
    exact .inr ⟨_,T.2⟩
  · exact .inl (by simp [cursorNext,Cursor.exit,he])

private theorem mean_weaken_on {α : Type} {n : Nat} (next : α → Fin n → α)
    (P Q good : α → Prop) (keep : ∀ x e, good x → good (next x e))
    (imp : ∀ x, good x → P x → Q x) (x : α) (hx : good x) (A : Nat)
    (h : IIDExpectedHittingTimeAtMost next P x A) :
    IIDExpectedHittingTimeAtMost next Q x A := by
  intro t
  have hh := glue_until_stop next next id (fun _ _ => rfl) Q P good keep 0 t
    (fun z _ hg hp hn _ => (hn (imp z hg hp)).elim) t (Nat.le_refl _) x hx
  exact Nat.le_trans (by simpa using hh) (h t)

theorem expected_pair {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (hBase : rightNeighbor C.s=v)
    (z : Cursor p c n) (h : PairGeom C z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert)
      (fun z => Cursor.exit z ∨ C.Certified z) z (4*n*((a+1)+(b+1))) := by
  let next := cursorNext (p:=p) (c:=c) group cert
  have hLeft := expected_seal (Context.leftSector C) z h.1
  have hFirst : IIDExpectedHittingTimeAtMost next (LeftPrepared C) z (4*n*(a+1)) :=
    mean_weaken_on next (Sealed (rightNeighbor C.s) a) (LeftPrepared C) (PairGeom C)
      (pairGeom_keep C) (fun w wg wR => by
        refine ⟨wg,?_⟩
        rcases wR with he|hr
        · exact .inl he
        · exact .inr ⟨.ready,⟨hr.le,hr.empty,hr.binary,hr.one,hr.before⟩⟩)
      z h _ hLeft
  have hSecond (w : Cursor p c n) (hw : LeftPrepared C w) :
      IIDExpectedHittingTimeAtMost next (fun q => Cursor.exit q ∨ C.Certified q)
        w (4*n*(b+1)) :=
    mean_weaken_on next (Sealed (rightNeighbor C.t) b) (fun q => Cursor.exit q ∨ C.Certified q) (LeftPrepared C)
      (leftPrepared_keep C) (fun q hq hR => by
        rcases hR with he|hr
        · exact .inl he
        · by_cases he : Cursor.exit q
          · exact .inl he
          · have H := hq.1.1.resolve_left he
            have I := hq.1.2.resolve_left he
            obtain ⟨lp,hp⟩ := hq.2.resolve_left he
            have ht : liftedSite v (a+1)=rightNeighbor C.t := by
              exact (congrArg (fun z => liftedSite z (a+1)) hBase).symm.trans H.2.terminal_site
            refine .inr ⟨lp,.ready,H.1,hBase,H.2,I.2,?_,?_⟩
            · exact (congrArg (fun s => lp.Holds q.1.config s a) hBase).mp hp
            · rw [ht]
              exact ⟨hr.le,hr.empty,hr.binary,hr.one,hr.before⟩)
      w hw _ (expected_seal (Context.rightSector C) w hw.1.2)
  have H := mean_compose next (LeftPrepared C) (fun q => Cursor.exit q ∨ C.Certified q)
    (PairGeom C) (pairGeom_keep C) _ _ z h hFirst (fun w _ hW => hSecond w hW)
  simpa only [Nat.mul_add] using H

/-- The complete dirty-seal plus sealed deletion clock. This stops on
the same selected retirement or certified native death throughout. -/
theorem expected_scoped_deletion {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (hBase : rightNeighbor C.s=v)
    (z : Cursor p c n) (h : PairGeom C z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) Cursor.exit z
      (2564*n*((a+1)+(b+1))) := by
  let next := cursorNext (p:=p) (c:=c) group cert
  have H := mean_compose next (fun q => Cursor.exit q ∨ C.Certified q) Cursor.exit (PairGeom C)
    (pairGeom_keep C) _ _ z h (expected_pair C hBase z h) (fun w _ hW => by
      rcases hW with hE|hP
      · intro t
        rw [iidHitCost_of_target _ _ _ hE]; exact Nat.zero_le _
      · exact WindowScopedSealedMean.mean C w hP)
  simpa only [show 2564=4+2560 by decide,Nat.add_mul] using H

#print axioms expected_pair
#print axioms expected_scoped_deletion
end L4.WindowScopedSealPrep
