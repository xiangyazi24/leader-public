import Leader.L4.WindowScopedRace

namespace L4.WindowScopedOneEdge
open WindowScopedRace TripleLongMonitor TriplePhase TripleVulnerable TripleControlled
open SevenTagCharge WindowLocal TripleBoundary

private def stop {p c n : Nat} (x : WindowScopedRace.State p c n) : Prop := x.exited=true

def value {p c n : Nat} (a : Nat) (x : WindowScopedRace.State p c n) : Nat :=
  if x.exited then 0 else if x.right=.forward .live 0 then 5*(a+1)-1
    else (coordinate x.left).value (a+1)

private theorem cap {p c n a : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} (C : Context initial group cert v a 0) (x : WindowScopedRace.State p c n)
    (h : C.Good x) : value a x≤5*(a+1)-1 := by
  by_cases hs : x.exited=true
  · simp [value,hs]
  · have hp := ((h.resolve_left hs).2.paired C.size).attacker
    have hv := Attack.value_le (a+1) _ (coordinate_valid _ v _ hp)
    by_cases hr : x.right=.forward .live 0 <;> simp [value,hs,hr] <;> omega

private theorem zero_forms (r : Phase) (h : PortValid 0 r) :
    r=.ready ∨ r=.forward .dummy 0 ∨ r=.forward .live 0 := by
  cases r with
  | ready => simp
  | forward k q =>
    have hh : q=0 := by simp [PortValid] at h; omega
    subst q
    cases k <;> simp
  | returning k q => simp [PortValid] at h

private theorem ordinary_target {n : Nat} (s : Fin n) (r : Phase)
    (h : r=.ready ∨ r=.forward .dummy 0) (e : Fin n) :
    r.tick s 0 e≠.forward .live 0 := by
  rcases h with rfl|rfl
  · by_cases he : e=s <;> by_cases hi : rightNeighbor e=s <;> simp [Phase.tick,he,hi]
  · by_cases he : e=s <;> simp [Phase.tick,liftedSite_zero,he]

private theorem pred_of {n : Nat} (v e : Fin n) :
    rightNeighbor e=v ↔ e=RearTrace.predecessor v := by
  constructor
  · intro h; rw [←h,RearTrace.predecessor_right]
  · intro h; rw [h,RearTrace.right_predecessor]

private theorem ready_adjacent_exit {p c n : Nat} {initial : Config p c n}
    {group cert : List (Fin n)} {v : Fin n}
    (C : Context initial group cert v 0 0) (x : WindowScopedRace.State p c n)
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

private theorem ordinary_next_value {p c n : Nat} {group cert : List (Fin n)} {v : Fin n}
    (a : Nat) (x : WindowScopedRace.State p c n) (e : Fin n)
    (h : x.right=.ready ∨ x.right=.forward .dummy 0)
    (hx : x.exited=false) :
    value a (WindowScopedRace.next group cert v a 0 x e) =
      if route group cert none x.ledger e=Event.keep then (coordinate (x.left.tick v a e)).value (a+1)
      else 0 := by
  by_cases he : route group cert none x.ledger e=Event.keep
  · simp [value,WindowScopedRace.next,hx,he,ordinary_target _ _ h e]
  · simp [value,WindowScopedRace.next,hx,he]

private theorem nonready_tick_pay {n : Nat} (v : Fin n) (a : Nat) (l : Phase)
    (h : PortValid a l) (hnr : l≠.ready)
    (hlive : ∀ q, l=.forward .live q → q<a) :
    (coordinate (l.tick v a (nominate v l))).value (a+1)+1 ≤ (coordinate l).value (a+1) := by
  cases l with
  | ready => contradiction
  | forward k q =>
    cases k
    · have hq : q≤a := h
      by_cases ht : q<a <;> by_cases ha : a=0 <;>
        simp [nominate,Phase.tick,coordinate,Attack.value,ht,ha] <;> omega
    · have hq := hlive q rfl
      simp [nominate,Phase.tick,coordinate,Attack.value,hq]
      omega
  | returning k q =>
    have hh : q+1≤a := h
    by_cases he : q=0 <;> simp [nominate,Phase.tick,coordinate,Attack.value,he] <;> omega

private theorem drift {p c n a : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} (C : Context initial group cert v a 0) (x : WindowScopedRace.State p c n)
    (hG : C.Good x) (hS : ¬stop x) :
    1≤BarrierIID.edgeSum (fun e => (value a x : Int)-
      (value a (WindowScopedRace.next group cert v a 0 x e) : Int)) := by
  have hx : x.exited=false := Bool.eq_false_iff.mpr hS
  have h := hG.resolve_left hS
  have hp := h.2.paired C.size
  let j := liftedSite v (a+1)
  let go := WindowScopedRace.next group cert v a 0 x
  by_cases hR : x.right=.forward .live 0
  · have hv : value a x=5*(a+1)-1 := by simp [value,hx,hR]
    rw [hv]
    apply progress_raw_drift _ j
    · have ht : (go j).right=.ready := by
        change x.right.tick j 0 j=.ready
        simp [hR,Phase.tick,liftedSite_zero]
      change value a (go j)+1≤5*(a+1)-1
      by_cases he : route group cert none x.ledger j=Event.keep
      · have hh := C.holds_keep x j h he
        have hv' := Attack.value_le (a+1) _
          (coordinate_valid _ v _ (hh.2.paired C.size).attacker)
        have hs : (go j).exited=false := by simp [go,WindowScopedRace.next,hx,he]
        simp [value,hs,ht]
        change (coordinate (go j).left).value (a+1)≤5*(a+1)-2 at hv'
        omega
      · have hs : (go j).exited=true := by simp [go,WindowScopedRace.next,he]
        simp [value,hs]; omega
    · exact fun e => cap C _ (C.good_step x e hG)
  · have ho : x.right=.ready ∨ x.right=.forward .dummy 0 := by
      rcases zero_forms x.right (portValid _ _ _ hp.target) with hr|hr|hr
      · exact .inl hr
      · exact .inr hr
      · exact (hR hr).elim
    have hd : DummyCycle x.right := by rcases ho with he|he <;> rw [he] <;> trivial
    have hV : value a x=(coordinate x.left).value (a+1) := by simp [value,hx,hR]
    rw [hV]
    by_cases hl : x.left=.ready
    · rw [hl]
      change 1≤BarrierIID.edgeSum (fun e => ((3*(a+1)-1 : Nat) : Int)-
        (value a (go e) : Int))
      have hN : RearTrace.predecessor v≠v := fun he =>
        in_out_distinct C.hn v ((pred_of v v).mpr he.symm)
      apply ready_raw_drift (a+1) (by omega) (RearTrace.predecessor v) v hN
      · rw [ordinary_next_value a x v ho hx]
        by_cases he : route group cert none x.ledger v=Event.keep
        · rw [if_pos he]
          by_cases ha : a=0
          · subst a; exact (ready_adjacent_exit C x h hl hd he).elim
          · simp [hl,Phase.tick,ha,coordinate,Attack.value]
            omega
        · simp [he]; omega
      · rw [ordinary_next_value a x (RearTrace.predecessor v) ho hx]
        simp [hl,Phase.tick,hN,RearTrace.right_predecessor,coordinate,Attack.value]
        split <;> omega
      · intro e hpre _
        rw [ordinary_next_value a x e ho hx]
        by_cases he : e=v
        · subst e
          by_cases ha : a=0 <;> by_cases he : route group cert none x.ledger v=Event.keep <;>
            simp [he,hl,Phase.tick,ha,coordinate,Attack.value] <;> omega
        · have hn : rightNeighbor e≠v := fun hh => hpre ((pred_of v e).mp hh)
          simp [hl,Phase.tick,he,hn,coordinate,Attack.value]
          split <;> omega
    · have hv := portValid _ _ _ hp.attacker
      have hlF : x.left.isReady=false := Bool.eq_false_iff.mpr (fun h => hl (isReady_eq _ h))
      let work := nominate v x.left
      have pay : value a (go work)+1≤(coordinate x.left).value (a+1) := by
        rw [ordinary_next_value a x work ho hx]
        by_cases he : route group cert none x.ledger work=Event.keep
        · rw [if_pos he]
          apply nonready_tick_pay v a x.left hv hl
          intro q hq
          have hB := hv
          rw [hq] at hB
          have hB' : q≤a := hB
          by_cases hh : q<a
          · exact hh
          · have hq' : q=a := by omega
            have hE : work=liftedSite v a := by simp [work,hq,hq',nominate]
            exact (live_no_impact C.hn initial group cert work q C.size h.1
              C.sub C.mid_mem h.2 he hq hd ⟨hq',hE⟩).elim
        · rw [if_neg he]
          have hh : (coordinate x.left).Valid (a+1) := coordinate_valid _ v _ hp.attacker
          cases hL : x.left with
          | ready => exact (hl hL).elim
          | forward k q =>
            rw [hL] at hh
            cases k <;> simp [coordinate,Attack.Valid,Attack.value] at hh ⊢ <;> omega
          | returning k q => simp [coordinate,Attack.value]; omega
      apply progress_raw_drift _ work _ pay
      intro e
      by_cases he : e=work
      · rw [he]; change value a (go work)≤_; omega
      · rw [ordinary_next_value a x e ho hx,idle_nonready v a x.left e hlF he]
        split <;> omega

/-- Scope-preserving adjacent-target clock, including an initially
live right phase. Exterior losses still update the actual tag ledger. -/
theorem mean {p c n a : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} (C : Context initial group cert v a 0)
    (z : Cursor p c n) (hz : C.Certified z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) Cursor.exit z (6*n*(a+1+1)) := by
  obtain ⟨l,r,h⟩ := hz
  let x : WindowScopedRace.State p c n := ⟨z.1,l,r,.seek,z.2⟩
  have H := mean_of_potential (WindowScopedRace.next group cert v a 0) stop C.Good (value a)
    (fun y e hy _ => C.good_step y e hy) (drift C) x (.inr h)
  intro t
  have hP := EntranceCover.iidHitCost_le_of_projection (cursorNext group cert)
    (WindowScopedRace.next group cert v a 0) Cursor.exit stop project
      (fun _ _ => rfl) (fun _ h => h) t x
  change iidHitCost (cursorNext group cert) Cursor.exit t z ≤ _
  refine Nat.le_trans (Nat.le_trans hP (H t)) ?_
  apply Nat.mul_le_mul_right
  calc
    _ ≤ n*(5*(a+1)-1) := Nat.mul_le_mul_left _ (cap C x (.inr h))
    _ ≤ n*(6*(a+1+1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ac_rfl

end L4.WindowScopedOneEdge

