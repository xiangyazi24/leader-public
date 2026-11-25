import Leader.L4.WindowScopedDummy
import Leader.L4.WindowScopedOneEdge

namespace L4.WindowScopedModerate
open WindowScopedRace TripleResidual TripleBoundary TriplePhase TripleControlled TripleVulnerable
open SevenTagCharge WindowLocal Classical

variable {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
  {s : Fin n} {a b : Nat}

def exitBit (_C : Context initial group cert s a b) (x : WindowScopedRace.State p c n) (e : Fin n) : Bool :=
  decide (route group cert none x.ledger e≠Event.keep)

def physicalStep (_C : Context initial group cert s a b) (x : WindowScopedRace.State p c n) (e : Fin n) :
    WindowScopedRace.State p c n := WindowScopedRace.next group cert s a b x e

def effective (s : Fin n) (a : Nat) (x : WindowScopedRace.State p c n) (e : Fin n) : Fin n :=
  controlledEdge x.right.isReady (liftedSite s a) (liftedSite s (a+1)) e

def controlled (C : Context initial group cert s a b) (x : WindowScopedRace.State p c n) (e : Fin n) :
    WindowScopedRace.State p c n := physicalStep C x (effective s a x e)

def actualAttack (x : WindowScopedRace.State p c n) : Attack :=
  if x.exited then .stopped else coordinate x.left

def Good (C : Context initial group cert s a b) (x : WindowScopedRace.State p c n) : Prop :=
  x.exited=true ∨ (C.Holds x ∧ DummyCycle x.right)

def stop (x : WindowScopedRace.State p c n) : Prop := x.exited=true

private theorem eff_attack (C : Context initial group cert s a b)
    (x : WindowScopedRace.State p c n) (e : Fin n) (hs : x.exited=false) :
    actualAttack (physicalStep C x e) =
      if exitBit C x e then .stopped else coordinate (x.left.tick s a e) := by
  simp [actualAttack,physicalStep,WindowScopedRace.next,exitBit,hs]

private theorem pred_for {n : Nat} (s e : Fin n) : rightNeighbor e=s ↔ e=RearTrace.predecessor s := by
  constructor
  · intro h; rw [←h,RearTrace.predecessor_right]
  · intro h; rw [h,RearTrace.right_predecessor]

private theorem pred_distinct {n : Nat} (hn : 4≤n) (s : Fin n) : RearTrace.predecessor s≠s :=
  fun h => TripleLongMonitor.in_out_distinct hn s ((pred_for s s).mpr h.symm)

private theorem ready_adjacent_exit {p c n : Nat} {initial : Config p c n}
    {group cert : List (Fin n)} {v : Fin n} {b : Nat}
    (C : Context initial group cert v 0 b) (x : WindowScopedRace.State p c n)
    (h : C.Holds x) (hl : x.left=.ready) (hd : DummyCycle x.right) :
    route group cert none x.ledger v≠Event.keep := by
  intro he
  have hp := h.2.paired C.size
  have ht : rightNeighbor v=rightNeighbor C.t := by
    rw [←h.2.left.terminal_site,h.2.base,liftedSite_succ,liftedSite_zero]
  have hND := certified_no_death_on_keep C.hn initial x.ledger group cert none
    v C.t C.m h.1 C.sub C.mid_mem h.2.left.right_live he ht
  have hV := cycle_vulnerable _ _ _ hp.target hd
  have hL := hp.geom.second_leader
  have hR : (x.ledger.config v).signal=.one := (ready_iff_signal_one _ _ _ hp.attacker).mp (by rw [hl]; rfl)
  rw [liftedSite_succ,liftedSite_zero] at hV hL
  have hShield : (fireResponder (x.ledger.config (rightNeighbor v))).shield=false := by
    rcases hV with hV|⟨hV,hs⟩
    · simp [fireResponder,hL,hV]
    · simp [fireResponder,hL,hV,hs]
  have H := (nativeDeath_iff _ _).mpr
    ⟨hL,TripleResidual.poised_live _ (.inr ⟨hp.geom.first_leader,by rw [hR]; decide⟩),hShield⟩
  rw [hND] at H
  contradiction

theorem effective_ready_bounds {p c n a b : Nat} {initial : Config p c n} {group cert : List (Fin n)} {s : Fin n} (C : Context initial group cert s a b)
    (x : WindowScopedRace.State p c n) (hs : x.exited=false)
    (hSeal : C.Holds x) (hl : x.left=.ready)
    (hd : DummyCycle x.right) :
    (∀ e, e=s →
      (((actualAttack (physicalStep C x e)).value (a+1) : Nat) : Int) ≤
        (3*(a+1)-1 : Nat) - (2*(a+1) : Nat)) ∧
    (∀ e, e=RearTrace.predecessor s →
      (actualAttack (physicalStep C x e)).value (a+1) ≤ (3*(a+1)-1)+(2*(a+1)-1)) ∧
    (∀ e, e≠RearTrace.predecessor s →
      (actualAttack (physicalStep C x e)).value (a+1) ≤ 3*(a+1)-1) := by
  have hi : RearTrace.predecessor s≠s := pred_distinct C.hn s
  constructor
  · intro e he
    subst e
    rw [eff_attack C x _ hs]
    by_cases hq : a=0
    · subst a
      simp [ready_adjacent_exit C x hSeal hl hd,exitBit,Attack.value]
    · by_cases he : exitBit C x s=true
      · simp [he,Attack.value]
        omega
      · simp [he,hl,Phase.tick,hq,coordinate,Attack.value]
        omega
  constructor
  · intro e he
    subst e
    rw [eff_attack C x _ hs]
    by_cases he : exitBit C x (RearTrace.predecessor s)=true
    · simp [he,Attack.value]
    · simp [he,hl,Phase.tick,hi,RearTrace.right_predecessor,coordinate,Attack.value,Nat.add_comm]
  · intro e hE
    rw [eff_attack C x _ hs]
    by_cases he : exitBit C x e=true
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
theorem effective_nonready_bounds {p c n a b : Nat} {initial : Config p c n} {group cert : List (Fin n)} {s : Fin n} (C : Context initial group cert s a b)
    (x : WindowScopedRace.State p c n) (hs : x.exited=false)
    (hSeal : C.Holds x) (hd : DummyCycle x.right)
    (hnr : x.left≠.ready) :
    ∃ q, q≤a ∧
      (actualAttack (physicalStep C x (liftedSite s q))).value (a+1) + 1 ≤
        (coordinate x.left).value (a+1) ∧
      ∀ e, (actualAttack (physicalStep C x e)).value (a+1) ≤
        (coordinate x.left).value (a+1) := by
  have h := hSeal.2.paired C.size
  have hval := coordinate_valid _ s x.left h.attacker
  cases hl : x.left with
  | ready => exact (hnr hl).elim
  | forward k q =>
    have hh : SealedFront x.ledger.config s a q k := by
      have H := h.attacker
      rw [hl] at H
      exact H
    have hP : Paired x.ledger.config s a b (.forward k q) x.right := hl ▸ h
    have v : (coordinate (.forward k q)).Valid (a+1) := hl ▸ hval
    have Hprog := Attack.progress_pays (a+1) (coordinate (.forward k q)) v
      (by cases k <;> intro h <;> cases h) (by cases k <;> intro h <;> cases h)
    have pay : (actualAttack (physicalStep C x (liftedSite s q))).value (a+1)+1 ≤
        (coordinate (.forward k q)).value (a+1) := by
      rw [eff_attack C x _ hs]
      by_cases he : exitBit C x (liftedSite s q)=true
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
              have T : Paired x.ledger.config s a b (.forward .live a) x.right := hK ▸ hP
              have he' : route group cert none x.ledger (liftedSite s a)=Event.keep := by
                simpa [exitBit] using he
              exact (WindowScopedRace.live_no_impact C.hn initial group cert _ a C.size
                hSeal.1 C.sub C.mid_mem hSeal.2 he' (hK ▸ hl) hd ⟨rfl,rfl⟩).elim
        rw [if_neg he,hl]
        simp only [Phase.tick,if_true]
        rw [forward_match a q k hh.within hh']
        exact Hprog
    refine ⟨q,hh.within,pay,?_⟩
    intro e
    by_cases he : e=liftedSite s q
    · rw [he]
      omega
    · rw [eff_attack C x _ hs]
      by_cases ht : exitBit C x e=true
      · simp [ht,Attack.value]
      · simp [ht,hl,Phase.tick,he]
  | returning k q =>
    have hh : TriplePrep.ReturnFront x.ledger.config s a (q+1) := by
      have H := h.attacker
      rw [hl] at H
      exact H.1
    have v : (coordinate (.returning k q)).Valid (a+1) := hl ▸ hval
    have Hprog := Attack.progress_pays (a+1) (coordinate (.returning k q)) v
      (by intro h; cases h) (by intro h; cases h)
    have pay : (actualAttack (physicalStep C x (liftedSite s q))).value (a+1)+1 ≤
        (coordinate (.returning k q)).value (a+1) := by
      rw [eff_attack C x _ hs]
      by_cases he : exitBit C x (liftedSite s q)=true
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
    · rw [eff_attack C x _ hs]
      by_cases ht : exitBit C x e=true
      · simp [ht,Attack.value]
      · simp [ht,hl,Phase.tick,he]

private theorem offset_not_pred {n : Nat} (s : Fin n) (j : Nat) (hj : j+1<n) :
    liftedSite s j ≠ RearTrace.predecessor s := by
  intro H
  have H' : liftedSite s (j+1)=liftedSite s 0 := by
    rw [liftedSite_succ,H,RearTrace.right_predecessor,liftedSite_zero]
  have h := liftedSite_inj s hj (by omega : 0<n) H'
  omega

private theorem effective_not_pred (x : WindowScopedRace.State p c n)
    (ha : a+1<n) (raw : Fin n) (hn : raw≠RearTrace.predecessor s) :
    effective s a x raw≠RearTrace.predecessor s := by
  unfold effective controlledEdge
  split
  · exact offset_not_pred s a ha
  · exact hn

theorem effective_stable (s : Fin n) (a : Nat) (x : WindowScopedRace.State p c n)
    (e : Fin n) (h : e≠liftedSite s (a+1)) : effective s a x e=e := by
  simp [effective,controlledEdge,h]

theorem effective_ne_right (C : Context initial group cert s a b)
    (x : WindowScopedRace.State p c n) (h : x.right.isReady=true) (e : Fin n) :
    effective s a x e≠liftedSite s (a+1) := by
  have hn : liftedSite s a≠liftedSite s (a+1) := fun he =>
    (by have hh := liftedSite_inj s (i:=a) (j:=a+1) (by have := C.size; omega)
         (by have := C.size; omega) he; omega)
  unfold effective controlledEdge
  simp only [h,Bool.true_and]
  split
  · exact hn
  · rename_i he
    exact fun h => he (beq_iff_eq.mpr h)

theorem controlled_good (C : Context initial group cert s a b)
    (x : WindowScopedRace.State p c n) (raw : Fin n) (h : Good C x) :
    Good C (controlled C x raw) := by
  let e := effective s a x raw
  by_cases hx : x.exited=true
  · exact Or.inl (by simp [controlled,physicalStep,WindowScopedRace.next,hx])
  by_cases he : route group cert none x.ledger e=Event.keep
  · have h' := h.resolve_left hx
    refine .inr ⟨C.holds_keep x e h'.1 he,?_⟩
    change DummyCycle (x.right.tick (liftedSite s (a+1)) b e)
    exact dummy_cycle_on_tick _ _ _ _ h'.2 (fun h => effective_ne_right C x h raw)
  · apply Or.inl
    change (x.exited || decide (route group cert none x.ledger e≠Event.keep))=true
    simp [he]

/-- Exact finite-word IID controlled duration for the vulnerable
trial with b+1≥2. The gain/loss labels are counted on the raw alphabet
while the whole physical step is redirected. -/
theorem controlled_attack_mean (C : Context initial group cert s a b)
    (hb : 0<b) (x : WindowScopedRace.State p c n) (hx : Good C x) :
    IIDExpectedHittingTimeAtMost (controlled C)
      stop x (n*(5*(a+1)-2)) := by
  have hv : (actualAttack x).Valid (a+1) := by
    cases he : x.exited
    · rcases hx with h|⟨h,_⟩
      · rw [he] at h; cases h
      · simp only [actualAttack,he,Bool.false_eq_true,if_false]
        exact coordinate_valid _ s x.left (h.2.paired C.size).attacker
    · simp [actualAttack,he,Attack.Valid]
  apply attack_clock _ _ (Good C) (a+1) (Nat.zero_lt_succ _) actualAttack
    (fun y e hy _ => controlled_good C y e hy) _ x hx hv
  intro y hy hs
  have hF : y.exited=false := Bool.eq_false_iff.mpr hs
  rcases hy with hs'|⟨hSeal,hd⟩
  · exact (hs hs').elim
  have hPair := hSeal.2.paired C.size
  have len : a+b+2≤n := by rcases hPair.geom.arity with h|⟨h,_⟩ <;> omega
  have ha : a+1<n := hPair.geom.at_least_two
  have R : ∀ j, j≤a → liftedSite s j≠liftedSite s (a+1) :=
    fun j hj H => (by have E := liftedSite_inj s (by omega : j<n) ha H; omega)
  simp only [actualAttack,hF,Bool.false_eq_true,if_false]
  -- Keep the poststep actualAttack at its full definition; the old
  -- expression above needed only its known live bit.
  change (coordinate y.left).RawLaw (a+1)
    (fun e => (actualAttack (physicalStep C y (effective s a y e))).value (a+1))
  by_cases hR : y.left=.ready
  · have H := effective_ready_bounds C y hF hSeal hR hd
    have hd' : RearTrace.predecessor s ≠ liftedSite s (a+1) :=
      Ne.symm (offset_not_pred s (a+1) (by omega))
    have hs' : s ≠ liftedSite s (a+1) := by
      intro he
      exact R 0 (Nat.zero_le _) ((liftedSite_zero s).trans he)
    rw [hR]
    refine ⟨RearTrace.predecessor s,s,pred_distinct C.hn s,?_,?_,?_⟩
    · simpa only [effective_stable s a y s hs'] using
        H.1 s rfl
    · simpa only [effective_stable s a y _ hd'] using
        H.2.1 (RearTrace.predecessor s) rfl
    · intro e he _
      exact H.2.2 _ (effective_not_pred (s:=s) (a:=a) y ha e he)
  · obtain ⟨q,hq,hN,hA⟩ := effective_nonready_bounds C y hF hSeal hd hR
    have eff : effective s a y (liftedSite s q) = liftedSite s q :=
      effective_stable s a y _ (R q hq)
    cases hp : y.left with
    | ready => exact (hR hp).elim
    | forward k r =>
      cases k <;> exact ⟨liftedSite s q,by simpa only [eff,hp] using hN,
        fun e => by simpa only [hp] using hA (effective s a y e)⟩
    | returning k r =>
      exact ⟨liftedSite s q,by simpa only [eff,hp] using hN,
        fun e => by simpa only [hp] using hA (effective s a y e)⟩

open TripleCylinder BarrierIID
open TripleCycleCount (workOf cycleProgress)

def hit {p c n : Nat} (s : Fin n) (a : Nat) (x : WindowScopedRace.State p c n) (e : Fin n) : Int :=
  match cycleProgress (liftedSite s (a+1)) x.right with
  | none => 0
  | some k => if e=k then 1 else 0

def workOf (b : Nat) : Phase → Nat
  | .ready => 2*b+1
  | .forward _ j => j
  | .returning _ q => 2*b-q

def work {p c n : Nat} (b : Nat) (x : WindowScopedRace.State p c n) : Nat :=
  if x.exited then 0 else workOf b x.right

def charge {p c n : Nat} (s : Fin n) (a : Nat) : WindowScopedRace.State p c n → Fin n → Int :=
  rawCharge (fun x => x.right.isReady) (liftedSite s a) (liftedSite s (a+1))

private theorem edge_zero (n : Nat) : edgeSum (fun _ : Fin n => (0:Int))=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons,Int.zero_add] at *
    exact ih

private theorem hit_sum_le {p c n : Nat} (s : Fin n) (a : Nat) (x : WindowScopedRace.State p c n) :
    edgeSum (hit s a x)≤1 := by
  cases h : cycleProgress (liftedSite s (a+1)) x.right with
  | none =>
    have hf : hit s a x=(fun _ => (0:Int)) := funext fun e => by simp [hit,h]
    rw [hf,edge_zero]
    decide
  | some k =>
    have hf : hit s a x=(fun e => if e=k then (1:Int) else 0) :=
      funext fun e => by simp [hit,h]
    rw [hf,edgeSum_selector]
    decide

private theorem raw_same_when_nonready {p c n : Nat} (s : Fin n) (a : Nat) (x : WindowScopedRace.State p c n)
    (h : x.right.isReady=false) (e : Fin n) : effective s a x e=e := by
  simp [effective,controlledEdge,h]

private theorem work_step_bound (hb : 0<b)
    (C : Context initial group cert s a b) (x : WindowScopedRace.State p c n) (raw : Fin n)
    (h : Paired x.ledger.config s a b x.left x.right)
    (_hD : DummyCycle x.right) (hs : x.exited=false) :
    (2*b+1 : Nat) * charge s a x raw +
      (work b (controlled C x raw) : Int) ≤
      (work b x : Int) + hit s a x raw := by
  let e := effective s a x raw
  have cdef : charge s a x raw = ((x.right.isReady && e == liftedSite s a).toNat : Int) := rfl
  have hWork : work b (controlled C x raw) =
      if exitBit C x e then 0 else workOf b (x.right.tick (liftedSite s (a+1)) b e) := by
    simp [work,controlled,physicalStep,WindowScopedRace.next,hs,e,exitBit]
  rw [hWork,cdef]
  simp only [work,hs,Bool.false_eq_true,if_false]
  cases H : x.right with
  | ready =>
    have ne := effective_ne_right C x
      (by simp [H,Phase.isReady]) raw
    have kn : rightNeighbor e=liftedSite s (a+1) ↔ e=liftedSite s a := by
      constructor
      · intro hE
        have EQ : rightNeighbor e=rightNeighbor (liftedSite s a) :=
          hE.trans (liftedSite_succ s a)
        exact FreshSeparation.succ_inj EQ
      · intro hE
        rw [hE,← liftedSite_succ]
    by_cases hE : e=liftedSite s a
    · have hN := kn.mpr hE
      have neq : e ≠ liftedSite s (a+1) := ne
      have EQ : (e == liftedSite s a) = true := beq_iff_eq.mpr hE
      simp only [Phase.isReady,Bool.true_and,EQ,Bool.toNat_true,Int.natCast_one,Int.mul_one]
      have ht : Phase.tick (liftedSite s (a+1)) b .ready e = .forward .dummy 0 := by
        simp [Phase.tick,neq,hN]
      rw [ht]
      simp [hit,H,cycleProgress,workOf]
    · have hN : ¬rightNeighbor e=liftedSite s (a+1) := fun h => hE (kn.mp h)
      have neq : e ≠ liftedSite s (a+1) := ne
      have EQ : (e == liftedSite s a) = false := Bool.eq_false_iff.mpr
        (fun H => hE (beq_iff_eq.mp H))
      simp only [Phase.isReady,Bool.true_and,EQ,Bool.toNat_false,Int.natCast_zero,Int.mul_zero,Int.zero_add]
      have ht : Phase.tick (liftedSite s (a+1)) b .ready e = .ready := by
        simp [Phase.tick,neq,hN]
      rw [ht]
      simp [hit,H,cycleProgress,workOf]
      split <;> omega
  | forward k q =>
    have ht : SealedFront x.ledger.config (liftedSite s (a+1)) b q k := by
      have D := h.target; rw [H] at D; exact D
    have eh : e=raw := raw_same_when_nonready s a x (by simp [H,Phase.isReady]) raw
    have hq := ht.within
    simp only [Phase.isReady,Bool.false_and,Bool.toNat_false,Int.natCast_zero,Int.mul_zero,Int.zero_add]
    by_cases g : raw=liftedSite (liftedSite s (a+1)) q
    · rw [eh]
      simp only [Phase.tick,if_pos g]
      by_cases hq' : q<b
      · simp [hq',workOf,hit,H,cycleProgress,g]
        split <;> omega
      · have h0 : b≠0 := Nat.ne_of_gt hb
        simp [hq',h0,workOf,hit,H,cycleProgress,g]
        split <;> omega
    · rw [eh]
      simp [Phase.tick,g,workOf,hit,H,cycleProgress]
      split <;> omega
  | returning k q =>
    have qt : TriplePrep.ReturnFront x.ledger.config (liftedSite s (a+1)) b (q+1) := by
      have D := h.target; rw [H] at D; exact D.1
    have eh : e=raw := raw_same_when_nonready s a x (by simp [H,Phase.isReady]) raw
    have hq := qt.le
    simp only [Phase.isReady,Bool.false_and,Bool.toNat_false,Int.natCast_zero,Int.mul_zero,Int.zero_add]
    by_cases g : raw=liftedSite (liftedSite s (a+1)) q
    · rw [eh]
      simp only [Phase.tick,if_pos g]
      by_cases hq' : q=0
      · simp [hq',workOf,hit,H,cycleProgress,g]
        split <;> omega
      · simp [hq',workOf,hit,H,cycleProgress,g]
        split <;> omega
    · rw [eh]
      simp [Phase.tick,g,workOf,hit,H,cycleProgress]
      split <;> omega

/-- The initial dummy was just fired, so no previous work can be
credited to the next effective incoming service. Include progress
on the stopping mark and do not assume independent sector clocks. -/
theorem zero_credit_moment (C : Context initial group cert s a b) (m : Nat)
    (hb : 0<b) (x : WindowScopedRace.State p c n) (hg : Good C x)
    (hw : work b x=0) (hm : n*(5*(a+1)-2)≤n*(2*b+1)*m) :
    ∀ t, stoppedDriftNumerator (controlled C)
      stop (charge s a) t x ≤ (m:Int)*(n:Int)^t := by
  have mean := controlled_attack_mean C hb x hg
  have hn := C.hn
  apply moment_of_zero_credit (controlled C) stop (charge s a)
    (2*b+1) m (n*(5*(a+1)-2)) x (by omega) (by omega) mean hm
  intro t
  have h := TripleControlled.charge_expectation (controlled C)
    stop (Good C) (hit s a) (charge s a) (work b) (2*b+1)
    (fun z e hz _ => controlled_good C z e hz)
    (by
      intro z e hz hL
      have hF : z.exited=false := Bool.eq_false_iff.mpr hL
      have hG := hz.resolve_left hL
      exact work_step_bound hb C z e (hG.1.2.paired C.size) hG.2 hF)
    (fun z _ => hit_sum_le s a z) x hg t
  simpa only [hw,Int.natCast_zero,Int.mul_zero,Int.add_zero] using h

theorem moderate_from_fresh_dummy (C : Context initial group cert s a b) (hb : 1≤b) (ha : a+1≤2*(b+1))
    (x : WindowScopedRace.State p c n) (hg : Good C x) (hphase : x.right=.forward .dummy 0) :
    ∀ t, stoppedDriftNumerator (controlled C)
      stop (charge s a) t x ≤ 6*(n:Int)^t := by
  apply zero_credit_moment C 6 (by omega) x hg
  · simp [work,hphase,workOf]
  · have h := moderate_charge_budget (a+1) (b+1) n (by omega) ha
    simpa only [show 2*(b+1)-1=2*b+1 by omega] using h

open TripleRenewal

/-- One original-scheduler attempt. In READY a right service ends
this attempt on the completed N0…P5 pair; a physical event on that
same mark still wins over the comparison-only boundary. -/
structure Trial (p c n : Nat) where
  phys : WindowScopedRace.State p c n
  leave : Bool

def trialHit {p c n : Nat} (z : Trial p c n) : Prop :=
  z.phys.exited=true ∨ z.leave=true

def trialNext (C : Context initial group cert s a b)
    (z : Trial p c n) (e : Fin n) : Trial p c n :=
  if z.leave || z.phys.exited then z else
    ⟨physicalStep C z.phys e,
      !allowed (fun x => x.right.isReady) (liftedSite s (a+1)) z.phys e⟩

private theorem effective_of_allowed {p c n : Nat} (s : Fin n) (a : Nat)
    (x : WindowScopedRace.State p c n) (e : Fin n)
    (h : allowed (fun x => x.right.isReady) (liftedSite s (a+1)) x e=true) :
    effective s a x e=e := by
  simp only [allowed,Bool.not_eq_true'] at h
  simp [effective,controlledEdge,h]

private theorem agreement (C : Context initial group cert s a b) :
    Agreement (physicalStep C) (fun x => x.right.isReady)
      (liftedSite s (a+1)) (fun x => x.exited=true) (Good C)
      (trialNext C) trialHit (fun z => z.phys.exited=true)
      (fun x => ⟨x,false⟩) := by
  constructor
  · intro x e hG _ ha
    have he := effective_of_allowed s a x e ha
    simpa only [controlled,he] using controlled_good C x e hG
  · intro x e _ hL ha
    have hF : x.exited=false := Bool.eq_false_iff.mpr hL
    simp [trialNext,hF,ha]
  · intro x _ h
    simpa [trialHit] using h
  · intro x _ h
    exact ⟨Or.inl h,h⟩

/-- Moderate geometry, conditional on the just-fired dummy boundary,
now admits an original-scheduler attempt: duration is controlled by
the redirection clock and the actual failed endpoint has mass ≤63/64.
This does not yet establish access to the just-fired dummy boundary. -/
theorem moderate_trial_from_fresh_dummy (C : Context initial group cert s a b) (hb : 1≤b) (ha : a+1≤2*(b+1))
    (x : WindowScopedRace.State p c n) (hG : Good C x) (hLive : x.exited=false)
    (hphase : x.right=.forward .dummy 0) :
    IIDExpectedHittingTimeAtMost (trialNext C) trialHit ⟨x,false⟩ (n*(5*(a+1)-2)) ∧
    ∀ t, 64*TripleRenewal.terminalMass (trialNext C) trialHit
      (fun y => y.phys.exited≠true) t ⟨x,false⟩≤63*n^t := by
  let stop := fun x : WindowScopedRace.State p c n => x.exited=true
  let orig : Trial p c n → Fin n → Trial p c n := trialNext C
  have mean := controlled_attack_mean C (by omega) x hG
  have moment := moderate_from_fresh_dummy C hb ha x hG hphase
  refine ⟨?_,?_⟩
  · intro t
    let rel := fun (z : Trial p c n) (v : WindowScopedRace.State p c n) => trialHit z ∨ z.phys=v
    have J := RestartSerial.cost_dominated orig (controlled C) trialHit stop rel
      (by intro z v hz hv
          rcases hz with H|rfl
          · exact H
          · exact Or.inl hv)
      (by
        intro z v e hh hz _ 
        obtain rfl := hh.resolve_left hz
        have hf : z.phys.exited=false := Bool.eq_false_iff.mpr (fun hp => hz (Or.inl hp))
        have hd : z.leave=false := Bool.eq_false_iff.mpr (fun hp => hz (Or.inr hp))
        dsimp only [rel,orig]
        by_cases ha' : allowed (fun x => x.right.isReady) (liftedSite s (a+1)) z.phys e=true
        · right
          rw [controlled,effective_of_allowed s a z.phys e ha']
          simp [trialNext,hf,hd]
        · left
          have ha0 := Bool.eq_false_iff.mpr ha'
          simp [trialNext,hf,hd,ha0,trialHit])
      t ⟨x,false⟩ x (Or.inr rfl)
    exact Nat.le_trans J (mean t)
  · have hh : Paired x.ledger.config s a b x.left x.right :=
      (hG.resolve_left (by simp [hLive])).1.2.paired C.size
    have hdiff : liftedSite s a ≠ liftedSite s (a+1) := by
      intro he
      have eq := liftedSite_inj s (by have := hh.geom.at_least_two; omega)
        hh.geom.at_least_two he
      omega
    exact failure_bound (physicalStep C) (fun x => x.right.isReady)
      (liftedSite s a) (liftedSite s (a+1)) hdiff stop (Good C) orig trialHit
      (fun y => y.phys.exited=true) (fun x => ⟨x,false⟩) (agreement C)
      6 _ x hG mean moment

end L4.WindowScopedModerate
