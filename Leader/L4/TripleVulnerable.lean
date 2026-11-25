import Leader.L4.TriplePhase
import Leader.L4.TripleControlled
import Leader.L4.TripleCylinder

/-! Literal vulnerable-stage projection and potential drift. -/
namespace L4.TripleVulnerable
open TriplePhase TripleResidual TripleControlled

/-- The target is in a dummy/return cycle. At READY the incoming mark
itself unshields the responder before N2. -/
def DummyCycle : Phase → Prop
  | .ready | .forward .dummy _ | .returning .dummy _ => True
  | _ => False

theorem dummy_cycle_on_tick {n : Nat} (s : Fin n) (d : Nat)
    (ph : Phase) (e : Fin n) (h : DummyCycle ph) (hb : ph.isReady=true → e≠s) :
    DummyCycle (ph.tick s d e) := by
  cases ph with
  | ready =>
    have he : e≠s := hb rfl
    by_cases hi : rightNeighbor e=s <;> simp [Phase.tick,he,hi,DummyCycle]
  | forward k q =>
    cases k with
    | live => exact h.elim
    | dummy =>
      by_cases he : e=liftedSite s q
      · by_cases hq : q<d
        · simp [Phase.tick,he,hq,DummyCycle]
        · by_cases hd : d=0 <;> simp [Phase.tick,he,hq,hd,DummyCycle]
      · simp [Phase.tick,he,DummyCycle]
  | returning k q =>
    cases k with
    | live => exact h.elim
    | dummy =>
      by_cases he : e=liftedSite s q
      · by_cases hq : q=0 <;> simp [Phase.tick,he,hq,DummyCycle]
      · simp [Phase.tick,he,DummyCycle]

theorem cycle_vulnerable {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (q : Phase) (h : q.Holds x s d) (hc : DummyCycle q) :
    (x s).signal=.one ∨ ((x s).signal=.zero ∧ (x s).shield=false) := by
  cases q with
  | ready => exact .inl (by simpa [liftedSite_zero] using h.one)
  | forward k q =>
    cases k with
    | live => exact hc.elim
    | dummy =>
      have hh : SealedFront x s d q .dummy := h
      have hz : (x s).signal=.zero := by
        by_cases hq : q=0
        · have hZ := hh.trail.signal
          simpa [hq,liftedSite_zero] using hZ
        · simpa [liftedSite_zero] using (hh.trail.swept 0 (Nat.pos_of_ne_zero hq)).1
      exact .inr ⟨hz,hh.shield⟩
  | returning k q =>
    cases k with
    | live => exact hc.elim
    | dummy =>
      have hz := h.1.before 0 (Nat.zero_lt_succ q)
      exact .inr ⟨by simpa [liftedSite_zero] using hz,h.2⟩

private theorem attack_event {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hL : (x (rightNeighbor e)).leader=true) (hB : (fireInitiator (x e)).bullet=.live)
    (hV : (x (rightNeighbor e)).signal=.one ∨
      ((x (rightNeighbor e)).signal=.zero ∧ (x (rightNeighbor e)).shield=false)) :
    event x e = true := by
  have H := vulnerable_mark_stops x e hL hB hV
  exact H

/-- Physical terminal action of a live prepared front into a vulnerable
target: the actual stopped monitor terminates on exactly this mark. -/
theorem live_terminal_stops {p c n a b : Nat} (x : Config p c n) (s : Fin n) (r : Phase)
    (h : Paired x s a b (.forward .live a) r) (hd : DummyCycle r) :
    event x (liftedSite s a)=true := by
  have hr : rightNeighbor (liftedSite s a)=liftedSite s (a+1) := (liftedSite_succ _ _).symm
  have hV := cycle_vulnerable x _ r h.target hd
  have hh : SealedFront x s a a .live := h.attacker
  have hb : (x (liftedSite s a)).bullet=.live := by simpa [Kind.bullet] using hh.unique a (Nat.le_refl _)
  have hL : (x (rightNeighbor (liftedSite s a))).leader=true := hr.symm ▸ h.geom.second_leader
  exact attack_event x _ hL (poised_live _ (.inl hb)) (hr.symm ▸ hV)

/-- Immediate live impact at a length-one attacking sector. -/
theorem ready_adjacent_stops {p c n b : Nat} (x : Config p c n) (s : Fin n) (r : Phase)
    (h : Paired x s 0 b .ready r) (hd : DummyCycle r) :
    event x s=true := by
  have hr : rightNeighbor s=liftedSite s (0+1) := by rw [liftedSite_succ,liftedSite_zero]
  have hV := cycle_vulnerable x _ r h.target hd
  have hR : (x s).signal=.one := (ready_iff_signal_one x s .ready h.attacker).mp rfl
  have hB := poised_live (x s) (.inr ⟨h.geom.first_leader,by rw [hR]; decide⟩)
  exact attack_event x s (hr.symm ▸ h.geom.second_leader) hB (hr.symm ▸ hV)

/-- Preserve complete physical state (including stock, markings, timers)
under the controlled redirection. Only the selected edge changes. -/
structure Physical (p c n : Nat) where
  obs : Obs p c n
  left : Phase
  right : Phase

def effective {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n) (raw : Fin n) : Fin n :=
  controlledEdge x.right.isReady (liftedSite s a) (liftedSite s (a+1)) raw

def effectiveNext {p c n : Nat} (s : Fin n) (a b : Nat) (x : Physical p c n) (e : Fin n) :
    Physical p c n :=
  ⟨advance x.obs e,x.left.tick s a e,x.right.tick (liftedSite s (a+1)) b e⟩

def controlledPhysical {p c n : Nat} (s : Fin n) (a b : Nat) (x : Physical p c n) (raw : Fin n) :
    Physical p c n :=
  effectiveNext s a b x (effective s a x raw)

def Good {p c n : Nat} (s : Fin n) (a b : Nat) (x : Physical p c n) : Prop :=
  x.obs.stopped=true ∨
    (MCOV x.obs.config ∧ COV x.obs.config ∧ Paired x.obs.config s a b x.left x.right ∧ DummyCycle x.right)

private theorem adjacent_ne {n : Nat} (s : Fin n) (a : Nat) (hn : a+1<n) :
    liftedSite s a≠liftedSite s (a+1) := by
  intro H
  have H := liftedSite_inj s (by omega) hn H
  omega

theorem effective_ready_ne_out {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n)
    (hn : a+1<n) (hR : x.right.isReady=true) (raw : Fin n) :
    effective s a x raw ≠ liftedSite s (a+1) := by
  have hne := adjacent_ne s a hn
  intro hh
  have H : controlledEdge true (liftedSite s a) (liftedSite s (a+1)) raw = liftedSite s (a+1) := by
    simpa only [effective,hR] using hh
  exact ((controlled_ready_fibers _ _ _ hne).2 _ (Ne.symm hne)).mp H |>.2 rfl

theorem physical_controlled_good {p c n : Nat} (hn : 4≤n) (s : Fin n) (a b : Nat)
    (x : Physical p c n) (raw : Fin n) (h : Good s a b x) :
    Good s a b (controlledPhysical s a b x raw) := by
  rcases h with hs|⟨hm,hc,hp,hd⟩
  · left
    simp [controlledPhysical,effectiveNext,advance,hs]
  · let e := effective s a x raw
    by_cases hs : x.obs.stopped=true
    · left; simp [controlledPhysical,effectiveNext,advance,hs]
    · have hF : x.obs.stopped=false := Bool.eq_false_iff.mpr hs
      by_cases he : event x.obs.config e = true
      · left; simpa [controlledPhysical,effectiveNext,advance,hF] using he
      · have heF : event x.obs.config e=false := Bool.eq_false_iff.mpr he
        have H := paired_tick_literal hn x.obs.config s e hm hc x.left x.right hp heF
        have C := EntranceCover.cover_closed hn x.obs.config e ⟨hm,hc⟩
        have R := dummy_cycle_on_tick (liftedSite s (a+1)) b x.right e hd
          (fun hR => effective_ready_ne_out s a x hp.geom.at_least_two hR raw)
        right
        simpa [controlledPhysical,effectiveNext,advance,hF] using
          (show MCOV (step x.obs.config e) ∧ COV (step x.obs.config e) ∧ _ from ⟨C.1,C.2,H,R⟩)

/-- The potential uses the physical sector length, one more than
the last donor offset. The target_cycle is separate and not counted. -/
def coordinate : Phase → Attack
  | .ready => .ready
  | .forward .live q => .live q
  | .forward .dummy q => .dummy q
  | .returning _ q => .returning (q+1)

def actualAttack {p c n : Nat} (x : Physical p c n) : Attack :=
  if x.obs.stopped then .stopped else coordinate x.left

theorem coordinate_valid {p c n a : Nat} (x : Config p c n) (s : Fin n) (q : Phase)
    (h : q.Holds x s a) : (coordinate q).Valid (a+1) := by
  cases q with
  | ready => trivial
  | forward k q =>
    have hq : q≤a := (show SealedFront x s a q k from h).within
    cases k <;> exact Nat.lt_succ_of_le hq
  | returning k q =>
    have hh : q+1≤a := h.1.le
    exact ⟨Nat.zero_lt_succ _,Nat.lt_succ_of_le hh⟩

private theorem eff_attack {p c n : Nat} (s : Fin n) (a b : Nat) (x : Physical p c n) (e : Fin n)
    (hs : x.obs.stopped=false) :
    actualAttack (effectiveNext s a b x e) =
      if event x.obs.config e then .stopped else coordinate (x.left.tick s a e) := by
  simp [actualAttack,effectiveNext,advance,hs]

private theorem pred_for {n : Nat} (s e : Fin n) :
    rightNeighbor e=s ↔ e=RearTrace.predecessor s := by
  constructor
  · intro h
    rw [← h,RearTrace.predecessor_right]
  · intro h
    rw [h,RearTrace.right_predecessor]

private theorem pred_distinct {n : Nat} (hn : 4≤n) (s : Fin n) :
    RearTrace.predecessor s≠s := by
  intro h
  have H := RearTrace.right_predecessor s
  rw [h] at H
  have H' : liftedSite s 1=liftedSite s 0 := by simpa [liftedSite_succ,liftedSite_zero] using H
  have hh := liftedSite_inj s (by omega : 1<n) (by omega : 0<n) H'
  omega

private theorem controlled_stable_edge {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n)
    (raw : Fin n) (he : raw≠liftedSite s (a+1)) :
    effective s a x raw=raw := by simp [effective,controlledEdge,he]

/-- The ready attack column has at most one adverse physical label,
the incoming orientation. Its outgoing service gains at least twice
the sector length even at the length-one boundary. -/
theorem effective_ready_bounds {p c n a b : Nat} (hn : 4≤n) (s : Fin n)
    (x : Physical p c n) (hs : x.obs.stopped=false)
    (h : Paired x.obs.config s a b .ready x.right) (hl : x.left=.ready)
    (hd : DummyCycle x.right) :
    (∀ e, e=s →
      (((actualAttack (effectiveNext s a b x e)).value (a+1) : Nat) : Int) ≤
        (3*(a+1)-1 : Nat) - (2*(a+1) : Nat)) ∧
    (∀ e, e=RearTrace.predecessor s →
      (actualAttack (effectiveNext s a b x e)).value (a+1) ≤ (3*(a+1)-1)+(2*(a+1)-1)) ∧
    (∀ e, e≠RearTrace.predecessor s →
      (actualAttack (effectiveNext s a b x e)).value (a+1) ≤ 3*(a+1)-1) := by
  have hi : RearTrace.predecessor s≠s := pred_distinct hn s
  constructor
  · intro e he
    subst e
    rw [eff_attack s a b x _ hs]
    by_cases hq : a=0
    · subst a
      simp [ready_adjacent_stops x.obs.config s x.right h hd,Attack.value]
    · by_cases he : event x.obs.config s=true
      · simp [he,Attack.value]
        omega
      · simp [he,hl,Phase.tick,hq,coordinate,Attack.value]
        omega
  constructor
  · intro e he
    subst e
    rw [eff_attack s a b x _ hs]
    by_cases he : event x.obs.config (RearTrace.predecessor s)=true
    · simp [he,Attack.value]
    · simp [he,hl,Phase.tick,hi,RearTrace.right_predecessor,coordinate,Attack.value,Nat.add_comm]
  · intro e hE
    rw [eff_attack s a b x _ hs]
    by_cases he : event x.obs.config e=true
    · simp [he,Attack.value]
    · by_cases hE' : e=s
      · subst e
        by_cases hq : a=0
        · simp [he,hl,Phase.tick,hq,coordinate]
          exact Nat.le_refl _
        · simp [he,hl,Phase.tick,hq,coordinate,Attack.value]
          omega
      · simp [he,hl,Phase.tick,hE',pred_for,hE,coordinate,Attack.value]

private theorem forward_match (a q : Nat) (k : Kind) (hq : q≤a)
    (hle : k≠.live ∨ q<a) :
    coordinate (if q<a then .forward k (q+1) else if a=0 then .ready else .returning k (a-1)) =
      (coordinate (.forward k q)).progress (a+1) := by
  cases k with
  | live =>
    have H := hle.resolve_left (by simp)
    have H' : q+1<a+1 := by omega
    simp [H,H',coordinate,Attack.progress]
  | dummy =>
    by_cases hl : q<a
    · have H : q+1<a+1 := by omega
      simp [hl,H,coordinate,Attack.progress]
    · have hh : ¬ q+1<a+1 := by omega
      by_cases ha : a=0
      · simp [ha,coordinate,Attack.progress]
      · have H : 1<a+1 := by omega
        simp [hl,hh,ha,H,coordinate,Attack.progress]
        omega

private theorem return_match (a q : Nat) (k : Kind) :
    coordinate (if q=0 then .ready else .returning k (q-1)) =
      (coordinate (.returning k q)).progress (a+1) := by
  by_cases hq : q=0
  · simp [hq,coordinate,Attack.progress]
  · have he : 1<q+1 := by omega
    simp [hq,he,coordinate,Attack.progress]
    omega

/-- At non-READY, the selected nominal mark strictly decreases V/n;
every other effective label is neutral or an actual global stop. -/
theorem effective_nonready_bounds {p c n a b : Nat} (s : Fin n)
    (x : Physical p c n) (hs : x.obs.stopped=false)
    (h : Paired x.obs.config s a b x.left x.right) (hd : DummyCycle x.right)
    (hnr : x.left≠.ready) :
    ∃ q, q≤a ∧
      (actualAttack (effectiveNext s a b x (liftedSite s q))).value (a+1) + 1 ≤
        (coordinate x.left).value (a+1) ∧
      ∀ e, (actualAttack (effectiveNext s a b x e)).value (a+1) ≤
        (coordinate x.left).value (a+1) := by
  have hval := coordinate_valid _ s x.left h.attacker
  cases hl : x.left with
  | ready => exact (hnr hl).elim
  | forward k q =>
    have hh : SealedFront x.obs.config s a q k := by
      have H := h.attacker
      rw [hl] at H
      exact H
    have hP : Paired x.obs.config s a b (.forward k q) x.right := hl ▸ h
    have v : (coordinate (.forward k q)).Valid (a+1) := hl ▸ hval
    have Hprog := Attack.progress_pays (a+1) (coordinate (.forward k q)) v
      (by cases k <;> intro h <;> cases h) (by cases k <;> intro h <;> cases h)
    have pay : (actualAttack (effectiveNext s a b x (liftedSite s q))).value (a+1)+1 ≤
        (coordinate (.forward k q)).value (a+1) := by
      rw [eff_attack s a b x _ hs]
      by_cases he : event x.obs.config (liftedSite s q)=true
      · rw [if_pos he]
        have hh' : 1 ≤ (coordinate (.forward k q)).value (a+1) :=
          Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) Hprog
        exact hh'
      · have hh' : k≠.live ∨ q<a := by
          cases hK : k
          · exact .inl (by decide)
          · right
            by_cases H : q<a
            · exact H
            · have E : q=a := by have H' := hh.within; omega
              subst q
              have T : Paired x.obs.config s a b (.forward .live a) x.right := hK ▸ hP
              exact (he (live_terminal_stops _ _ _ T hd)).elim
        rw [if_neg he,hl]
        simp only [Phase.tick,if_true]
        rw [forward_match a q k hh.within hh']
        exact Hprog
    refine ⟨q,hh.within,pay,?_⟩
    intro e
    by_cases he : e=liftedSite s q
    · rw [he]
      omega
    · rw [eff_attack s a b x _ hs]
      by_cases ht : event x.obs.config e=true
      · simp [ht,Attack.value]
      · simp [ht,hl,Phase.tick,he]
  | returning k q =>
    have hh : TriplePrep.ReturnFront x.obs.config s a (q+1) := by
      have H := h.attacker
      rw [hl] at H
      exact H.1
    have v : (coordinate (.returning k q)).Valid (a+1) := hl ▸ hval
    have Hprog := Attack.progress_pays (a+1) (coordinate (.returning k q)) v
      (by intro h; cases h) (by intro h; cases h)
    have pay : (actualAttack (effectiveNext s a b x (liftedSite s q))).value (a+1)+1 ≤
        (coordinate (.returning k q)).value (a+1) := by
      rw [eff_attack s a b x _ hs]
      by_cases he : event x.obs.config (liftedSite s q)=true
      · rw [if_pos he]
        exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) Hprog
      · rw [if_neg he,hl]
        simp only [Phase.tick,if_true]
        rw [return_match]
        exact Hprog
    refine ⟨q,by have H := hh.le; omega,pay,?_⟩
    intro e
    by_cases he : e=liftedSite s q
    · rw [he]
      omega
    · rw [eff_attack s a b x _ hs]
      by_cases ht : event x.obs.config e=true
      · simp [ht,Attack.value]
      · simp [ht,hl,Phase.tick,he]

private theorem offset_not_pred {n : Nat} (s : Fin n) (j : Nat) (hj : j+1<n) :
    liftedSite s j ≠ RearTrace.predecessor s := by
  intro H
  have H' : liftedSite s (j+1)=liftedSite s 0 := by
    rw [liftedSite_succ,H,RearTrace.right_predecessor,liftedSite_zero]
  have h := liftedSite_inj s hj (by omega : 0<n) H'
  omega

private theorem effective_not_pred {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n)
    (ha : a+1<n) (raw : Fin n) (hn : raw≠RearTrace.predecessor s) :
    effective s a x raw≠RearTrace.predecessor s := by
  unfold effective controlledEdge
  split
  · exact offset_not_pred s a ha
  · exact hn

/-- Exact finite-word IID controlled duration for the vulnerable
trial with b+1≥2. The gain/loss labels are counted on the raw alphabet
while the whole physical step is redirected. -/
theorem controlled_attack_mean {p c n : Nat} (hn : 4≤n)
    (s : Fin n) (a b : Nat) (hb : 0<b) (x : Physical p c n) (hx : Good s a b x) :
    IIDExpectedHittingTimeAtMost (controlledPhysical s a b)
      (fun y => y.obs.stopped=true) x (n*(5*(a+1)-2)) := by
  have hv : (actualAttack x).Valid (a+1) := by
    cases he : x.obs.stopped
    · rcases hx with h|⟨_,_,ph,_⟩
      · rw [he] at h; cases h
      · simp only [actualAttack,he,Bool.false_eq_true,if_false]
        exact coordinate_valid _ s x.left ph.attacker
    · simp [actualAttack,he,Attack.Valid]
  apply attack_clock _ _ (Good s a b) (a+1) (Nat.zero_lt_succ _) actualAttack
    (fun y e hy _ => physical_controlled_good hn s a b y e hy) _ x hx hv
  intro y hy hs
  have hF : y.obs.stopped=false := Bool.eq_false_iff.mpr hs
  rcases hy with hs'|⟨_,_,hPair,hd⟩
  · exact (hs hs').elim
  have len : a+b+2≤n := by rcases hPair.geom.arity with h|⟨h,_⟩ <;> omega
  have ha : a+1<n := hPair.geom.at_least_two
  have R : ∀ j, j≤a → liftedSite s j≠liftedSite s (a+1) :=
    fun j hj H => (by have E := liftedSite_inj s (by omega : j<n) ha H; omega)
  simp only [actualAttack,hF,Bool.false_eq_true,if_false]
  -- Keep the poststep actualAttack at its full definition; the old
  -- expression above needed only its known live bit.
  change (coordinate y.left).RawLaw (a+1)
    (fun e => (actualAttack (effectiveNext s a b y (effective s a y e))).value (a+1))
  by_cases hR : y.left=.ready
  · have hP : Paired y.obs.config s a b .ready y.right := hR ▸ hPair
    have H := effective_ready_bounds hn s y hF hP hR hd
    have hd' : RearTrace.predecessor s ≠ liftedSite s (a+1) :=
      Ne.symm (offset_not_pred s (a+1) (by omega))
    have hs' : s ≠ liftedSite s (a+1) := by
      intro he
      exact R 0 (Nat.zero_le _) ((liftedSite_zero s).trans he)
    rw [hR]
    refine ⟨RearTrace.predecessor s,s,pred_distinct hn s,?_,?_,?_⟩
    · simpa only [controlled_stable_edge s a y s hs'] using
        H.1 s rfl
    · simpa only [controlled_stable_edge s a y _ hd'] using
        H.2.1 (RearTrace.predecessor s) rfl
    · intro e he _
      exact H.2.2 _ (effective_not_pred s a y ha e he)
  · obtain ⟨q,hq,hN,hA⟩ := effective_nonready_bounds s y hF hPair hd hR
    have eff : effective s a y (liftedSite s q) = liftedSite s q :=
      controlled_stable_edge s a y _ (R q hq)
    cases hp : y.left with
    | ready => exact (hR hp).elim
    | forward k r =>
      cases k <;> exact ⟨liftedSite s q,by simpa only [eff,hp] using hN,
        fun e => by simpa only [hp] using hA (effective s a y e)⟩
    | returning k r =>
      exact ⟨liftedSite s q,by simpa only [eff,hp] using hN,
        fun e => by simpa only [hp] using hA (effective s a y e)⟩

end L4.TripleVulnerable
