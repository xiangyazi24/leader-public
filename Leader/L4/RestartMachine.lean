import Leader.L4.RestartRouting
import Leader.L4.RootedFresh

namespace L4.RestartMachine
open RankPhysical RankRootless RankSupplier TripleResidual RestartRouting Classical

/-- Each constructor carries the literal root geometry that its stage
needs. A protected push tracks the post-mark victim, not the old site. -/
inductive Mode {p c n : Nat} (r : Nat) (x : Config p c n) : Type where
  | search (h : NoLiving x)
  | first (v : Fin n) (d : Nat) (h : Live v (RankSupplier.init x d))
  | second (v : Fin n) (a d : Nat) (ha : a+1<n)
      (hv : (x v).leader=true) (hF : FirstMark x v a)
      (h : Live (liftedSite v (a+1)) (RankSupplier.init x d))
  | deletion (v : Fin n) (a b : Nat) (h : TripleResidual.Start x v a b)
  | protect (v : Fin n) (d : Nat) (h : Protected v (RankSupplier.init x d))
  | retired (h : rank x<r)
  | failed

def doneMode {p c n r : Nat} {x : Config p c n} :
    Mode r x → Bool
  | .retired _ | .failed => true
  | _ => false

def failedMode {p c n r : Nat} {x : Config p c n} :
    Mode r x → Bool
  | .failed => true
  | _ => false

def fromEntry {p c n r : Nat} {x : Config p c n} : NativeEntry x → Mode r x
  | .first v d h => .first v d h
  | .second v a d ha hv hF h => .second v a d ha hv hF h
  | .deletion v a b h => .deletion v a b h

structure State (p c n : Nat) (r : Nat) where
  config : Config p c n
  quiet : QuietEntrance config
  mode : Mode r config

structure Params (p c n r : Nat) : Prop where
  modulus : 2≤p
  calibration : 12≤c
  size : 4≤n
  initialRank : 2≤r

noncomputable def start {p c n : Nat} (x : Config p c n) (hq : QuietEntrance x)
    (hr : 2≤rank x) : State p c n (rank x) :=
  ⟨x,hq,if h : NoLiving x then .search h else fromEntry (afterActivation x hq.1 hr h)⟩

noncomputable def fromKill {p c n r : Nat} (hn : 4≤n)
    (x : Config p c n) (e : Fin n) (hq : QuietEntrance x)
    (hd : death x e=true) (hr : retirement x e=false) : Mode r (step x e) :=
  let ex := transition_after_kill hn x e hq hd hr
  let v := Classical.choose ex
  let exS := Classical.choose_spec ex
  let s := Classical.choose exS
  have hS := Classical.choose_spec exS
  .protect v s.donor (by
    have he : s=RankSupplier.init (step x e) s.donor := by
      have hconfig : s.config=step x e := hS.1
      have hs : s.stopped=false := hS.2.1.1.1
      revert hconfig hs
      generalize s = ss
      cases ss
      simp only [RankSupplier.init]
      intro h y
      cases h
      cases y
      rfl
    rw [←he]
    exact hS.2.1)

private theorem live_reset {p c n : Nat} (u : Fin n) (s : RankSupplier.Obs p c n)
    (y : Config p c n) (hS : s.config=y) (h : Live u s) :
    Live u (RankSupplier.init y s.donor) := by
  have hz : s=RankSupplier.init y s.donor := by
    cases s
    simp_all only [RankSupplier.Live,RankSupplier.init]
  simpa only [←hz] using h

theorem no_local_retirement {p c n r : Nat} (P : Params p c n r)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) (hx : rank x≤r)
    (hy : ¬rank (step x e)<r) : retirement x e=false := by
  cases h : retirement x e
  · rfl
  · have hh := rank_step P.size x e hm
    simp only [h,Bool.toNat_true] at hh
    omega

noncomputable def stepActive {p c n r : Nat} (P : Params p c n r)
    (x : Config p c n) (e : Fin n) (hq : QuietEntrance x)
    (hx : rank x≤r) (hy : ¬rank (step x e)<r)
    (mode : Mode r x) : Mode r (step x e) := by
  let y := step x e
  have hYr : 2≤rank y := by have := P.initialRank; change ¬rank y<r at hy; omega
  have hQ := RootedFresh.quiet_step x e P.modulus P.calibration P.size hq
  have hR := no_local_retirement P x e hq.1 hx hy
  cases mode with
  | retired hr => exact .retired (Nat.lt_of_le_of_lt (rank_step_le P.size x e hq.1) hr)
  | failed => exact .failed
  | search _ =>
      exact if h : NoLiving y then .search h else fromEntry (afterActivation y hQ.1 hYr h)
  | first v d h =>
      by_cases hd : death x e=true
      · exact fromKill P.size x e hq hd hR
      · have hd0 : death x e=false := Bool.eq_false_iff.mpr hd
        have he : event x e=false := by simp [event,hd0,hR]
        let s := RankSupplier.init x d
        let z := RankSupplier.advance v s e
        by_cases hz : z.stopped=false
        ·
          have hp := (RankSupplierPhysical.unstopped_fields v e s h.1 hz).1
          exact .first v z.donor (live_reset v z y hp (live_step P.size v e s h hz))
        · have hz : z.stopped=true := (by simpa using hz)
          have hv := no_event_preserves_leader P.size x e v hq.2.1 he h.2.2.1
          have hp := RestartAudit.supplier_birth_exit P.size v e s h hz hR hv
          exact fromEntry (afterFirst y v hQ.1 hYr hp.2.1 hv hp.1 hp.2.2)
  | second v a d ha hv hF h =>
      by_cases hd : death x e=true
      · exact fromKill P.size x e hq hd hR
      · have hd0 : death x e=false := Bool.eq_false_iff.mpr hd
        have he : event x e=false := by simp [event,hd0,hR]
        let u := liftedSite v (a+1)
        let s := RankSupplier.init x d
        let z := RankSupplier.advance u s e
        by_cases hz : z.stopped=false
        ·
          have hp := (RankSupplierPhysical.unstopped_fields u e s h.1 hz).1
          have K := second_keep_prefix P.size v e s h hq.2.1 hv hF ha he hz
          exact .second v a z.donor ha (hp ▸ K.1) (hp ▸ K.2.1)
            (live_reset u z y hp K.2.2)
        · have hz : z.stopped=true := (by simpa using hz)
          have ex := second_success_deletion P.size v e s h hq.2.1 hv hF ha he hz
          exact .deletion v a (Classical.choose ex) (Classical.choose_spec ex)
  | deletion v a b h =>
      by_cases hd : death x e=true
      · exact fromKill P.size x e hq hd hR
      · have hd0 : death x e=false := Bool.eq_false_iff.mpr hd
        exact .deletion v a b (no_event_preserves_start P.size x e v hq.1 hq.2.1
          (by simp [event,hd0,hR]) h)
  | protect v d h =>
      let s := RankSupplier.init x d
      let z := RankSupplier.advance v s e
      by_cases hz : z.stopped=false
      ·
        have hp := (RankSupplierPhysical.unstopped_fields v e s h.1.1 hz).1
        have ht := protected_step P.size v e s h hz
        exact .protect v z.donor ⟨live_reset v z y hp ht.1,hp ▸ ht.2⟩
      · exact .failed

/-- Physical steps continue through both sticky terminals. The auxiliary
observer itself does not freeze the actual configuration. -/
noncomputable def next {p c n r : Nat} (P : Params p c n r)
    (s : {s : State p c n r // rank s.config≤r}) (e : Fin n) :
    {s : State p c n r // rank s.config≤r} :=
  let x := s.val.config
  let y := step x e
  let hQ := RootedFresh.quiet_step x e P.modulus P.calibration P.size s.val.quiet
  let hRank := Nat.le_trans (rank_step_le P.size x e s.val.quiet.1) s.property
  ⟨⟨y,hQ,if failedMode s.val.mode then .failed
      else if h : rank y<r then .retired h
      else stepActive P x e s.val.quiet s.property h s.val.mode⟩,hRank⟩

theorem step_project {p c n r : Nat} (P : Params p c n r)
    (s : {s : State p c n r // rank s.config≤r}) (e : Fin n) :
    (next P s e).val.config=step s.val.config e := rfl

theorem terminals {p c n r : Nat} (s : State p c n r)
    (hd : doneMode s.mode=true) (hR : r≤rank s.config) :
    failedMode s.mode=true := by
  cases s with
  | mk x hq mode =>
    cases mode <;> simp [doneMode,failedMode] at *
    rename_i hr
    omega

theorem terminal_sticky {p c n r : Nat} (P : Params p c n r)
    (s : {s : State p c n r // rank s.config≤r}) (e : Fin n)
    (h : doneMode s.val.mode=true) : doneMode (next P s e).val.mode=true := by
  rcases s with ⟨⟨x,hq,mode⟩,hs⟩
  cases mode <;> simp only [doneMode,Bool.false_eq_true] at h
  · rename_i hr
    have hh := Nat.lt_of_le_of_lt (rank_step_le P.size x e hq.1) hr
    simp [next,failedMode,doneMode,hh]
  · simp [next,failedMode,doneMode]

end L4.RestartMachine
