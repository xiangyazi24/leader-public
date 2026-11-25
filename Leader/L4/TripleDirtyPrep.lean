import Leader.L4.TriplePhase
import Leader.L4.FixedResidual
import Leader.L4.TripleRenewal
import Leader.L4.TripleControlled

/-! Arbitrary native residual preparation on one stationary consecutive
leader sector. Old bullets progress by least occupied offset, not provenance. -/
namespace L4.TripleDirtyPrep
open TripleResidual TriplePrep TriplePhase FixedResidual TripleRenewal
private theorem separate_neighbor {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

private theorem terminal_safe {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hl : (x (rightNeighbor e)).leader = true) (he : death x e = false) :
    (fireInitiator (x e)).bullet ≠ .live ∨
    (fireResponder (x (rightNeighbor e))).shield = true := by
  by_cases hf : (fireInitiator (x e)).bullet = .live
  · right
    cases hs : (fireResponder (x (rightNeighbor e))).shield
    · have hk := (death_iff_nativeKill x e).mpr ⟨hl,hf,hs⟩
      simp [he] at hk
    · rfl
  · exact .inl hf

private theorem sector_ordinary {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d) {j : Nat} (hj : j < d) :
    (x (liftedSite s j)).mark = false ∧
    (x (rightNeighbor (liftedSite s j))).residue = nextResidue (x (liftedSite s j)).residue ∧
    (x (rightNeighbor (liftedSite s j))).leader = false := by
  have h := coveredOrdinary hc ((covered_noRoot_iff hm).mpr
    (Bool.eq_false_iff.mpr (hF.before j hj)))
  exact ⟨h.1,h.2.1,h.2.2.1⟩

structure LeastBullet {p c n : Nat} (x : Config p c n) (s : Fin n) (q : Nat) : Prop where
  occupied : (x (liftedSite s q)).bullet ≠ .none
  before : ∀ j, j < q → (x (liftedSite s j)).bullet = .none

private theorem ordinary_bullet_transport {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue) (hl : v.leader = false)
    (hNoFire : u.leader = false ∨ u.signal = .zero) (hB : u.bullet ≠ .none) :
    (pairStep u v).1.bullet = .none ∧ (pairStep u v).2.bullet ≠ .none := by
  have hf : fireInitiator u = u := by rcases hNoFire with h | h <;> simp [fireInitiator,h]
  have q := ordinary_native_payload u v hm hr hl
  simp [native,hf,fireResponder,hl,impact,pinned,hm,followerBullet,hB] at q
  refine ⟨q.1,?_⟩
  rw [q.2.2.2.1]
  split
  · exact hB
  · assumption

/-- Dirty leftmost-front phase, on its nominated forward mark. A
follower's own inherited two is allowed; only at the source does this
use the nonreadiness assumption to forbid a replacement N0 firing. -/
theorem leastBullet_progress {p c n d q : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (s : Fin n) (hm : MCOV x) (hc : COV x)
    (hF : FirstMark x s d) (hD : d+1<n) (hQ : q<d)
    (h0 : (x s).signal = .zero) (h : LeastBullet x s q) :
    LeastBullet (step x (liftedSite s q)) s (q+1) := by
  let e := liftedSite s q
  have ho := sector_ordinary x s hm hc hF hQ
  have hN : (x e).leader = false ∨ (x e).signal = .zero := by
    cases q with
    | zero => exact .inr (by simpa [e,liftedSite_zero] using h0)
    | succ q =>
      have hg := sector_ordinary x s hm hc hF (show q<d by omega)
      exact .inl (by simpa [e,liftedSite_succ] using hg.2.2)
  have hp := ordinary_bullet_transport _ _ ho.1 ho.2.1 ho.2.2 hN h.occupied
  have hR : liftedSite s (q+1) = rightNeighbor e := liftedSite_succ s q
  have hn' := separate_neighbor hn e
  refine ⟨?_,?_⟩
  · have hPost : step x e (liftedSite s (q+1)) = (pairStep (x e) (x (rightNeighbor e))).2 := by
      simp [step,hR,hn']
    rw [hPost]
    exact hp.2
  · intro j hj
    by_cases he : j=q
    · subst j
      simpa [step,e] using hp.1
    · have hx : liftedSite s j ≠ e := fun H => he (liftedSite_inj s (by omega) (by omega) H)
      have hy : liftedSite s j ≠ rightNeighbor e := by
        rw [← hR]
        intro H
        have hEq := liftedSite_inj s (by omega : j<n) (by omega : q+1<n) H
        omega
      change (step x e (liftedSite s j)).bullet = .none
      simpa only [step,if_neg hx,if_neg hy] using h.before j (by omega)

/-- On all nonnominated marks the least bullet keeps its offset and no
new bullet gets into the vacated left prefix. The source can become
ready on this mark; until then the same least bullet remains usable. -/
theorem leastBullet_wait {p c n d q : Nat} (x : Config p c n) (s e : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader = true) (h0 : (x s).signal = .zero) (hq : q≤d)
    (h : LeastBullet x s q) (he : rightNeighbor e = s → death x e = false)
    (hw : e ≠ liftedSite s q) : LeastBullet (step x e) s q := by
  have noFire (j : Nat) (hj : j≤q) :
      (x (liftedSite s j)).leader = false ∨ (x (liftedSite s j)).signal = .zero := by
    cases j with
    | zero => exact .inr (by simpa [liftedSite_zero] using h0)
    | succ j =>
      exact .inl (by simpa [liftedSite_succ] using
        (sector_ordinary x s hm hc hF (show j<d by omega)).2.2)
  have prop (j : Nat) (hj : j≤q) :
      (step x e (liftedSite s j)).bullet = (x (liftedSite s j)).bullet := by
    by_cases hE : liftedSite s j = e
    · have hjq : j<q := by
        by_cases H : j=q
        · subst j; exact (hw hE.symm).elim
        · omega
      have ho := sector_ordinary x s hm hc hF (show j<d by omega)
      have hh := ordinary_empty_donor _ _ ho.1 ho.2.1 ho.2.2 (h.before j hjq) (noFire j hj)
      rw [← hE]
      simpa [step] using hh.1.trans (h.before j hjq).symm
    · by_cases hR : liftedSite s j = rightNeighbor e
      · cases j with
        | zero =>
          have hr : rightNeighbor e = s := by simpa [liftedSite_zero] using hR.symm
          have hl : (x (rightNeighbor e)).leader = true := hr ▸ hL
          have hz : (x (rightNeighbor e)).signal = .zero := hr ▸ h0
          have hS := terminal_safe x e hl (he hr)
          rw [show fireResponder (x (rightNeighbor e)) = x (rightNeighbor e) by simp [fireResponder,hl,hz]] at hS
          have hh := zero_incoming_stable _ _ hl hz hS
          simpa only [step,if_neg hE,if_pos hR] using hh.1.trans
            (congrArg (fun i => (x i).bullet) hR.symm)
        | succ j =>
          have hE' : liftedSite s j = e := FreshSeparation.succ_inj (by simpa [liftedSite_succ] using hR)
          have hO := sector_ordinary x s hm hc hF (show j < d by omega)
          have hh := ordinary_empty_donor _ _ hO.1 hO.2.1 hO.2.2
            (h.before j (by omega)) (noFire j (by omega))
          simp only [step,if_neg hE,if_pos hR]
          rw [← hE',← liftedSite_succ]
          simpa only [liftedSite_succ] using hh.2.2.1
      · simp only [step,if_neg hE,if_neg hR]
  exact ⟨fun hb => h.occupied ((prop q (Nat.le_refl _)).symm.trans hb),
    fun j hj => (prop j (by omega)).trans (h.before j hj)⟩

/-- Last nominated forward mark empties a dirty sector. The donor may
hold inherited colour two; this statement does not mistakenly assert
that the resulting first return is necessarily binary. -/
theorem leastBullet_terminal {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hD : d+1<n) (h : LeastBullet x s d)
    (hL : (x (liftedSite s (d+1))).leader = true)
    (hn : death x (liftedSite s d) = false) :
    ∀ j, j≤d → (step x (liftedSite s d) (liftedSite s j)).bullet = .none := by
  let e := liftedSite s d
  have hR : liftedSite s (d+1) = rightNeighbor e := liftedSite_succ s d
  have hl : (x (rightNeighbor e)).leader = true := hR ▸ hL
  have hp := surviving_terminal _ _ hl (terminal_safe x e hl hn)
  intro j hj
  by_cases he : j=d
  · subst j
    simpa [step,e] using hp.1
  · have hx : liftedSite s j ≠ e := fun H => he (liftedSite_inj s (by omega) (by omega) H)
    have hy : liftedSite s j ≠ rightNeighbor e := by
      rw [← hR]
      intro H
      have hEq := liftedSite_inj s (by omega : j<n) hD H
      omega
    change (step x e (liftedSite s j)).bullet = .none
    simpa only [step,if_neg hx,if_neg hy] using h.before j (by omega)

/-- Covers and fixed endpoints until actual stopped monitor fires. -/
structure Geometry {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) : Prop where
  markCov : MCOV x
  sourceCov : COV x
  gap : FirstMark x s d
  startLeader : (x s).leader=true
  endLeader : (x (liftedSite s (d+1))).leader=true

def GeomLive {p c n : Nat} (s : Fin n) (d : Nat) (y : Obs p c n) : Prop :=
  y.stopped = true ∨ Geometry y.config s d

theorem geomLive_step {p c n d : Nat} (hn : 4≤n) (bd : d+1<n)
    (s : Fin n) (y : Obs p c n) (e : Fin n) (h : GeomLive s d y) :
    GeomLive s d (advance y e) := by
  by_cases hs : y.stopped=true
  · left; simp [advance,hs]
  · have hs' : y.stopped=false := Bool.eq_false_iff.mpr hs
    have hg := h.resolve_left hs
    by_cases he : event y.config e=true
    · left; simp [advance,hs',he]
    · have he' : event y.config e=false := Bool.eq_false_iff.mpr he
      have hC := EntranceCover.cover_closed hn y.config e ⟨hg.markCov,hg.sourceCov⟩
      have hG : Geometry (step y.config e) s d :=
        ⟨hC.1,hC.2,no_event_sector hn _ _ _ hg.markCov hg.sourceCov he' hg.startLeader hg.endLeader hg.gap bd,
          no_event_preserves_leader hn _ _ _ hg.sourceCov he' hg.startLeader,
          no_event_preserves_leader hn _ _ _ hg.sourceCov he' hg.endLeader⟩
      right
      simpa only [advance,hs',Bool.false_eq_true,if_false] using hG

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

/-- This is first nonzero source signal, not yet the sealed READY
state. Inherited two is allowed here and triggers correct N0/N1. -/
def Positive {p c n : Nat} (s : Fin n) (y : Obs p c n) : Prop :=
  y.stopped=true ∨ (y.config s).signal≠.zero

noncomputable def reserve {p c n : Nat} (s : Fin n) (d : Nat) (y : Obs p c n) : Nat := by
  classical
  exact if Positive s y then 0 else (pickPhase y.config s d).reserve d

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

/-- Every actual raw interaction preserves or decreases the predictable
dirty-sector reserve; the nominated interaction strictly decreases it.
An early source readiness or actual stop uses no unobserved future. -/
theorem reserve_step {p c n d : Nat} (hn : 4≤n) (bd : d+1<n) (s : Fin n)
    (y : Obs p c n) (e : Fin n) (hg : GeomLive s d y) (hl : ¬ Positive s y) :
    reserve s d (advance y e) + (if e=(pickPhase y.config s d).nominate s then 1 else 0) ≤
      reserve s d y := by
  classical
  let ph := pickPhase y.config s d
  have hV : ph.Valid y.config s d := pickPhase_valid _ _ _
  have hs' : y.stopped=false := Bool.eq_false_iff.mpr (fun hh => hl (.inl hh))
  have h0 : (y.config s).signal=.zero := Classical.not_not.mp (fun hh => hl (.inr hh))
  have G := hg.resolve_left (fun hh => hl (.inl hh))
  have B := phase_budget_pos y.config s ph hV h0
  by_cases hp : Positive s (advance y e)
  · rw [reserve,if_pos hp,reserve,if_neg hl]
    change 0+(if e=ph.nominate s then 1 else 0)≤ph.reserve d
    split <;> omega
  · have he : event y.config e=false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      apply hp
      exact .inl (by simp [advance,hs',hh])
    have hstep : (advance y e).config=step y.config e := by simp [advance,hs']
    rw [reserve,if_neg hp,reserve,if_neg hl,hstep]
    change (pickPhase (step y.config e) s d).reserve d +
      (if e=ph.nominate s then 1 else 0)≤ph.reserve d
    cases hph : ph with
    | bullet q =>
      have H : q≤d ∧ LeastBullet y.config s q := by
        rw [hph] at hV
        exact hV
      by_cases he' : e=liftedSite s q
      · subst e
        by_cases hq : q<d
        · have hh := leastBullet_progress hn y.config s G.markCov G.sourceCov G.gap bd hq h0 H.2
          have eq := phase_unique (pickPhase (step y.config (liftedSite s q)) s d) (.bullet (q+1))
            (pickPhase_valid _ _ _) (show _ ∧ _ from ⟨by omega,hh⟩)
          rw [eq]
          simp [DirtyPhase.reserve,DirtyPhase.nominate]
          omega
        · have Hq : q=d := by have := H.1; omega
          subst q
          have E := leastBullet_terminal y.config s bd H.2 G.endLeader (Bool.or_eq_false_iff.mp he).1
          obtain ⟨r,hR⟩ := dirtyReturn_exists (step y.config (liftedSite s d)) s E
          have eq := phase_unique (pickPhase (step y.config (liftedSite s d)) s d) (.returning r)
            (pickPhase_valid _ _ _) hR
          rw [eq]
          have hh := hR.le
          simp [DirtyPhase.reserve,DirtyPhase.nominate]
          omega
      · have K := leastBullet_wait y.config s e G.markCov G.sourceCov G.gap G.startLeader
          h0 H.1 H.2 (fun _ => (Bool.or_eq_false_iff.mp he).1) he'
        have eq := phase_unique (pickPhase (step y.config e) s d) (.bullet q)
          (pickPhase_valid _ _ _) (show _ ∧ _ from ⟨H.1,K⟩)
        rw [eq]
        simp [DirtyPhase.reserve,DirtyPhase.nominate,he']
    | returning q =>
      have H : DirtyReturn y.config s d q := by rw [hph] at hV; exact hV
      cases q with
      | zero =>
        have hz : (y.config (liftedSite s 0)).signal=.zero := by simpa [liftedSite_zero] using h0
        exact (H.positive (Nat.zero_le _) hz).elim
      | succ q =>
        have hh := dirtyReturn_step y.config s e G.markCov G.sourceCov G.gap bd
          G.startLeader G.endLeader H he
        have eq := phase_unique (pickPhase (step y.config e) s d)
          (.returning (if e=liftedSite s q then q else q+1)) (pickPhase_valid _ _ _) hh
        rw [eq]
        by_cases hE : e=liftedSite s q <;> simp [DirtyPhase.reserve,DirtyPhase.nominate,hE]

private theorem reserve_bound {p c n : Nat} (s : Fin n) (d : Nat) (y : Obs p c n) :
    reserve s d y ≤ 2*(d+1) := by
  classical
  have H := pickPhase_valid y.config s d
  unfold reserve
  split
  · exact Nat.zero_le _
  · cases h : pickPhase y.config s d with
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
theorem expected_positive {p c n d : Nat} (hn : 4≤n) (bd : d+1<n) (s : Fin n)
    (y : Obs p c n) (h : GeomLive s d y) :
    IIDExpectedHittingTimeAtMost advance (Positive s) y (n*(2*(d+1))) := by
  let clock : Countdown advance (Positive s) y :=
    { budget := fun w => reserve s d (GGTiming.runMarks advance y w)
      nominate := fun w => (pickPhase (GGTiming.runMarks advance y w).config s d).nominate s
      decrease := by
        intro w hw e
        rw [GGTiming.runMarks_append]
        have HH (z : Obs p c n) (w : List (Fin n)) (h : GeomLive s d z) :
            GeomLive s d (GGTiming.runMarks advance z w) := by
          induction w generalizing z with
          | nil => exact h
          | cons e w ih => exact ih _ (geomLive_step hn bd s z e h)
        exact reserve_step hn bd s _ e (HH y w h) hw }
  intro t
  exact Nat.le_trans (expected_of_countdown _ _ _ clock t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (reserve_bound s d y)))

/-- Either the physical sector is sealed, or a genuine clearing front
(with swept zero/empty trail, not merely a least bullet) is available. -/
def Launched {p c n : Nat} (s : Fin n) (d : Nat) (y : Obs p c n) : Prop :=
  y.stopped=true ∨ Ready y.config s d ∨ ∃ q, q≤d ∧ ZeroFront y.config s q

def Sealed {p c n : Nat} (s : Fin n) (d : Nat) (y : Obs p c n) : Prop :=
  y.stopped=true ∨ Ready y.config s d

private theorem incident_or_hold {p c n d : Nat} (hn : 4≤n)
    (s : Fin n) (y : Obs p c n) (e : Fin n)
    (hG : GeomLive s d y) (hp : Positive s y) :
    Launched s d (advance y e) ∨ (Positive s (advance y e) ∧ e≠s) := by
  by_cases hs : y.stopped=true
  · exact .inl (.inl (by simp [advance,hs]))
  · have G := hG.resolve_left hs
    have pos := hp.resolve_left hs
    have hs' : y.stopped=false := Bool.eq_false_iff.mpr hs
    by_cases he : event y.config e=true
    · exact .inl (.inl (by simp [advance,hs',he]))
    · have he' : event y.config e=false := Bool.eq_false_iff.mpr he
      have proj : (advance y e).config=step y.config e := by simp [advance,hs']
      by_cases hE : e=s
      · subst e
        left; right
        by_cases hd : d=0
        · subst d
          have hL : (y.config (rightNeighbor s)).leader=true := by
            simpa [liftedSite_succ,liftedSite_zero] using G.endLeader
          left
          rw [proj]
          exact (sourceOutgoing_adjacent_ready _ _ G.startLeader hL pos he').1
        · have HD : 0<d := Nat.pos_of_ne_zero hd
          have hh := sourceOutgoing_starts_front hn y.config s G.markCov G.sourceCov
            G.gap HD G.startLeader pos
          exact .inr ⟨1,HD,proj.symm ▸ hh.1⟩
      · by_cases hR : rightNeighbor e=s
        · have hh := sourceIncoming_starts_front hn y.config e s hR G.startLeader pos he'
          exact .inl (.inr (.inr ⟨0,Nat.zero_le _,proj.symm ▸ hh.1⟩))
        · right
          refine ⟨.inr ?_,hE⟩
          rw [proj]
          simpa [step,Ne.symm hE,Ne.symm hR] using pos

/-- Starting at first positive, the first genuine incident launch
(or an earlier seal/stop) waits no longer than one nominated raw label. -/
theorem expected_launch {p c n d : Nat} (hn : 4≤n) (bd : d+1<n)
    (s : Fin n) (y : Obs p c n) (h : GeomLive s d y) (hP : Positive s y) :
    IIDExpectedHittingTimeAtMost advance (Launched s d) y n := by
  classical
  let good := fun z : Obs p c n => GeomLive s d z ∧ (Launched s d z ∨ Positive s z)
  let budget := fun z : Obs p c n => if Launched s d z then 0 else 1
  have H := TripleControlled.mean_of_potential advance (Launched s d) good budget
    (fun z e hz hL => by
      have H := incident_or_hold hn s z e hz.1 (hz.2.resolve_left hL)
      refine ⟨geomLive_step hn bd s z e hz.1,?_⟩
      rcases H with hh|hh
      · exact .inl hh
      · exact .inr hh.1)
    (fun z hz hL => by
      by_cases hY : Launched s d (advance z s)
      · apply TripleControlled.progress_raw_drift (budget z) s (fun e => budget (advance z e))
        · simp [budget,hL,hY]
        · intro e
          dsimp [budget]
          rw [if_neg hL]
          split <;> decide
      · have K := (incident_or_hold hn s z s hz.1 (hz.2.resolve_left hL)).resolve_left hY
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

/-- A genuine clearing-front cut costs at most 2h-1 more nominated
hits. This lift handles the physical stop already set. -/
theorem expected_seal_of_launched {p c n d : Nat} (hn : 4≤n) (bd : d+1<n)
    (s : Fin n) (y : Obs p c n) (hg : GeomLive s d y) (hl : Launched s d y) :
    IIDExpectedHittingTimeAtMost advance (Sealed s d) y (n*(2*d+1)) := by
  by_cases h : Sealed s d y
  · intro t
    rw [iidHitCost_of_target _ _ _ h]
    exact Nat.zero_le _
  · have hs : y.stopped=false := Bool.eq_false_iff.mpr (fun hh => h (.inl hh))
    have G := hg.resolve_left (fun hh => h (.inl hh))
    obtain ⟨q,hq,hF⟩ := (hl.resolve_left (fun hh => h (.inl hh))).resolve_left (fun hh => h (.inr hh))
    have e : y=init y.config := by cases y; simp_all [init]
    have H := expected_ready_after_front y.config s hn bd G.markCov G.sourceCov G.gap
      G.startLeader G.endLeader hq hF
    intro t
    rw [e]
    refine Nat.le_trans (H t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_))
    exact Nat.sub_le _ _

/-- Clean the native payload of one arbitrary covered consecutive
root sector, or stop at the first physical death/retirement. The exact
bound is 4*h raw expected marks per unit n, where h=d+1. -/
theorem expected_seal {p c n d : Nat} (hn : 4≤n) (bd : d+1<n) (s : Fin n)
    (y : Obs p c n) (h : GeomLive s d y) :
    IIDExpectedHittingTimeAtMost advance (Sealed s d) y (4*n*(d+1)) := by
  have keep := geomLive_step (p:=p) (c:=c) hn bd s
  have launchMean : IIDExpectedHittingTimeAtMost advance (Launched s d) y (n*(2*(d+1))+n) :=
    mean_compose advance (Positive s) (Launched s d) (GeomLive s d) keep _ _ y h
      (expected_positive hn bd s y h) (expected_launch hn bd s)
  have H := mean_compose advance (Launched s d) (Sealed s d) (GeomLive s d) keep _ _ y h
    launchMean (expected_seal_of_launched hn bd s)
  have he : n*(2*(d+1))+n+n*(2*d+1)=4*n*(d+1) := by
    calc
      _ = n*(2*(d+1)+1+(2*d+1)) := by simp only [Nat.mul_add,Nat.mul_one]
      _ = n*(4*(d+1)) := congrArg (n*·) (by omega)
      _ = _ := by rw [← Nat.mul_assoc,Nat.mul_comm n 4]
  simpa only [he] using H

def PairGeom {p c n : Nat} (v : Fin n) (a b : Nat) (y : Obs p c n) : Prop :=
  y.stopped=true ∨ (MCOV y.config ∧ COV y.config ∧ Start y.config v a b)

def LeftCut {p c n : Nat} (v : Fin n) (a : Nat) (y : Obs p c n) : Prop :=
  y.stopped=true ∨ ∃ ph : Phase, ph.Holds y.config v a

/-- At the paired cut both actual sealed phases have certificates; they
need not be READY at the same instant. -/
def PairCut {p c n : Nat} (v : Fin n) (a b : Nat) (y : Obs p c n) : Prop :=
  y.stopped=true ∨ ∃ l r, Paired y.config v a b l r

private theorem pair_geom_step {p c n : Nat} (hn : 4≤n)
    (v : Fin n) (a b : Nat) (y : Obs p c n) (e : Fin n) (h : PairGeom v a b y) :
    PairGeom v a b (advance y e) := by
  by_cases hs : y.stopped=true
  · left; simp [advance,hs]
  · obtain ⟨hm,hc,hG⟩ := h.resolve_left hs
    have hs' : y.stopped=false := Bool.eq_false_iff.mpr hs
    by_cases he : event y.config e=true
    · left; simp [advance,hs',he]
    · have he' : event y.config e=false := Bool.eq_false_iff.mpr he
      have cv := EntranceCover.cover_closed hn y.config e ⟨hm,hc⟩
      have hh := no_event_preserves_start hn _ e v hm hc he' hG
      right
      simpa only [advance,hs',Bool.false_eq_true,if_false] using ⟨cv.1,cv.2,hh⟩

private theorem left_cut_step {p c n : Nat} (hn : 4≤n)
    (v : Fin n) (a b : Nat) (y : Obs p c n) (e : Fin n)
    (h : PairGeom v a b y) (hl : LeftCut v a y) :
    LeftCut v a (advance y e) := by
  by_cases hs : y.stopped=true
  · left; simp [advance,hs]
  · obtain ⟨hm,hc,hG⟩ := h.resolve_left hs
    obtain ⟨ph,hp⟩ := hl.resolve_left hs
    have hs' : y.stopped=false := Bool.eq_false_iff.mpr hs
    by_cases he : event y.config e=true
    · left; simp [advance,hs',he]
    · have he' : event y.config e=false := Bool.eq_false_iff.mpr he
      have hh := phase_tick_literal hn y.config v e hG.at_least_two hm hc hG.first_gap
        hG.first_leader hG.second_leader ph hp he'
      exact .inr ⟨_,by simpa only [advance,hs',Bool.false_eq_true,if_false] using hh⟩

private theorem left_geom {p c n : Nat} (v : Fin n) (a b : Nat) (y : Obs p c n)
    (h : PairGeom v a b y) : GeomLive v a y := by
  rcases h with hs|⟨hm,hc,h⟩
  · exact .inl hs
  · exact .inr ⟨hm,hc,h.first_gap,h.first_leader,h.second_leader⟩

private theorem right_geom {p c n : Nat} (v : Fin n) (a b : Nat) (y : Obs p c n)
    (h : PairGeom v a b y) : GeomLive (liftedSite v (a+1)) b y := by
  rcases h with hs|⟨hm,hc,h⟩
  · exact .inl hs
  · exact .inr ⟨hm,hc,h.second_gap,h.second_leader,h.third_leader⟩

private theorem mean_weaken_on {α : Type} {n : Nat} (next : α → Fin n → α)
    (cut goal good : α → Prop) (keep : ∀ y e, good y → good (next y e))
    (sub : ∀ y, good y → cut y → goal y) (A : Nat) (y : α) (hy : good y)
    (first : IIDExpectedHittingTimeAtMost next cut y A) :
    IIDExpectedHittingTimeAtMost next goal y A := by
  have h := mean_compose next cut goal good keep A 0 y hy first (fun z hz hc t => by
    rw [iidHitCost_of_target next goal z (sub z hz hc)]
    exact Nat.zero_le _)
  simpa only [Nat.add_zero] using h

/-- Sequential native preparation of both sectors, with the first
sector cycling under every intervening physical mark. No conditioning
on simultaneous readiness, and rank-two alias is already in Start. -/
theorem expected_pair_cut {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (y : Obs p c n) (h : PairGeom v a b y) (ha : a+1<n) (hb : b+1<n) :
    IIDExpectedHittingTimeAtMost advance (PairCut v a b) y (4*n*(a+b+2)) := by
  let K := PairGeom (p:=p) (c:=c) v a b
  let LG := fun z : Obs p c n => K z ∧ LeftCut v a z
  have keep := pair_geom_step (p:=p) (c:=c) hn v a b
  have keepL : ∀ z e, LG z → LG (advance z e) :=
    fun z e h => ⟨keep z e h.1,left_cut_step hn v a b z e h.1 h.2⟩
  have first := mean_weaken_on advance (Sealed v a) (LeftCut v a) K keep
    (fun z _ H => H.elim Or.inl (fun hh => .inr ⟨.ready,hh⟩)) _ y h
    (expected_seal hn ha v y (left_geom v a b y h))
  have rest (z : Obs p c n) (hK : K z) (hL : LeftCut v a z) :
      IIDExpectedHittingTimeAtMost advance (PairCut v a b) z (4*n*(b+1)) := by
    let s := liftedSite v (a+1)
    apply mean_weaken_on advance (Sealed s b) (PairCut v a b) LG keepL _ _ z ⟨hK,hL⟩
      (expected_seal hn hb s z (right_geom v a b z hK))
    intro w hw H
    by_cases hh : w.stopped=true
    · exact .inl hh
    · have geom := (hw.1.resolve_left hh).2.2
      obtain ⟨l,hs⟩ := hw.2.resolve_left hh
      exact .inr ⟨l,.ready,geom,hs,H.resolve_left hh⟩
  have E := mean_compose advance (LeftCut v a) (PairCut v a b) K keep _ _ y h first rest
  rw [← Nat.mul_add] at E
  simpa only [show a+1+(b+1)=a+b+2 by omega] using E

/-- Physical Stage interface for the prepared-pair cutoff. Its observer
is exactly the stopped raw ring state; the phase witnesses are decoded
at the observed cut. -/
def pairPrepStage {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (y : Obs p c n) (h : PairGeom v a b y) : Stage advance y where
  State := Obs p c n
  start := y
  next := advance
  project := id
  ready := PairCut v a b
  reachable := PairGeom v a b
  projInit := rfl
  projStep := fun _ _ => rfl
  reachStart := h
  reachStep := pair_geom_step hn v a b

end L4.TripleDirtyPrep
