import Leader.L4.WindowPlan
import Leader.L4.WindowProgressNormal
import Leader.L4.WindowOrdinaryHandoff
import Leader.L4.WindowTripleHandoff
import Leader.L4.WindowTripleWindow

namespace L4.WindowMiddle

open WindowPlan WindowOwnership WindowTransactions
open WindowProgressNormal WindowRosterTrace WindowA0Join
open SevenTagCharge WindowRoster WindowFiveStages RootedAssembly TripleRenewal

variable {p c n : Nat}
variable (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
variable (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))

private theorem current_append (w u : Word n) :
    current hp hc hn x hq i (w++u)=
      GGTiming.runMarks (WindowTripleHandoff.joined hp hc hn) (current hp hc hn x hq i w) u := by
  unfold current fold
  rw [WindowLatch.replay_append,replay_run]
  rfl

def Mid (j : Nat) (w : Word n) (h : Nat) : Prop :=
  done hp hc hn x hq i w ∨ physical x i w≤h ∧
    (atProtected hp hc hn x hq i w ∨ atOwned hp hc hn x hq i j w)

theorem midShape (j : Nat) (bound : 1≤j ∧ j≤3) (w : Word n) (h : Nat) :
    Allow hp hc hn x hq i (5-j) w h ↔ Mid hp hc hn x hq i j w h := by
  have Hj : j=1∨j=2∨j=3 := by omega
  rcases Hj with rfl|rfl|rfl <;> simp [Allow,Mid]

private theorem coordinates (w : Word n)
    (F : Front x (window7 (roster x) i)) (P : Progress F.ledger _)
    (hF : current hp hc hn x hq i w=.inl F) (hP : F.mode=.owned P) :
    (P.before.length=1 ∨ P.before.length=2) ∧ NoLivingTarget P ∧
      ∀ (j : Nat) (hj : j<P.cert.length),
        P.cert[j]=labels x i (P.before.length+j) :=
  owned_coordinates hq hp hc hn i (scope x i) rfl rfl w F P hF hP

private theorem protectedIndex (w : Word n)
    (F : Front x (window7 (roster x) i)) (P : Progress F.ledger _)
    (hF : current hp hc hn x hq i w=.inl F) (hP : F.mode=.owned P)
    (E : WindowProtectedOuter.Entry x (window7 (roster x) i))
    (hmem : E.victim∈P.cert) :
    ∃ d : Nat, 0<d ∧ d+2<7 ∧ E.victim=labels x i d := by
  obtain ⟨B,_,H⟩ := coordinates hp hc hn x hq i w F P hF hP
  obtain ⟨j,hj,Hj⟩ := List.mem_iff_getElem.mp hmem
  have cap := P.bounded
  refine ⟨P.before.length+j,?_,?_,Hj.symm.trans (H j hj)⟩ <;>
    rcases B with b|b <;> omega

private theorem wordMean {α : Type} (step : α → Fin n → α) (q : α) (stop : α → Prop)
    {B : Nat} (mean : IIDExpectedHittingTimeAtMost step stop q B) :
    IIDExpectedHittingTimeAtMost wordNext (fun v => stop (GGTiming.runMarks step q v)) [] B := by
  intro t
  have H := WindowA0Bridge.word_cost_le step stop _ (GGTiming.runMarks step q)
    (by intro u e; exact GGTiming.runMarks_append _ _ _ _)
    (fun _ h => h) t []
  exact Nat.le_trans H (mean t)

theorem ordinary_stage (h7 : 7≤RankPhysical.rank x) (k : Nat) (hK : 1≤k ∧ k≤2)
    (w : Word n) (h : Nat) (aw : Mid hp hc hn x hq i k w h)
    (nd : ¬done hp hc hn x hq i w) :
    Mid hp hc hn x hq i (k+1) w h ∨ ∃ T : Transaction (coefficient c) w h,
      ∀ u, FirstExit T.hit u → ¬done hp hc hn x hq i (w++u) →
        Mid hp hc hn x hq i (k+1) (w++u) (T.span u) := by
  obtain ⟨spanBound,prot|own⟩ := aw.resolve_left nd
  · exact .inl (.inr ⟨spanBound,.inl prot⟩)
  obtain ⟨F,P,hF,hP,len⟩ := own
  by_cases skipped : k+1≤P.cert.length
  · exact .inl (.inr ⟨spanBound,.inr ⟨F,P,hF,hP,skipped⟩⟩)
  have exactLen : P.cert.length=k := by omega
  have small : P.cert.length<3 := by omega
  have led : F.ledger=observe (initial x) w := by
    have L := fold_ledger hp hc hn hq (scope x i) w
    change WindowLatch.project Front.ledger (current hp hc hn x hq i w)=_ at L
    rw [hF] at L
    exact L
  have noLoss := WindowNoLoss.not_done_no_loss hp hc hn hq (scope x i) w nd
  have H := ordinary_cut_of_fold hq hp hc hn i h7 (scope x i) rfl rfl w F P hF hP small
    (by rw [led]; exact noLoss)
  let d := P.before.length+P.cert.length-1
  let a := labels x i (d+1)
  obtain ⟨dBound,T,_⟩ := H
  have ht : P.target=some a := T
  obtain ⟨_,ghost,coords⟩ := coordinates hp hc hn x hq i w F P hF hP
  have cert : labels x i d∈P.cert := by
    have pos := P.positive
    have j := coords (P.cert.length-1) (by omega)
    have E : P.before.length+(P.cert.length-1)=d := by dsimp [d]; omega
    rw [E] at j
    rw [←j]
    exact List.getElem_mem _
  have clock := WindowOrdinaryWindow.clock hp hc hn x hq i h7 w h spanBound noLoss
    F led P hP d (by change d≤3 at dBound; omega) cert ht (ghost _ ht)
  let q := WindowOrdinarySlot.Slot.active F P hP rfl ht
  let tick := WindowOrdinarySlot.next (x:=x) (g:=window7 (roster x) i) (cert:=P.cert) (a:=a) hp hc hn
  let hit := fun u => (GGTiming.runMarks tick q u).done
  have mean := wordMean tick q WindowOrdinarySlot.Slot.done clock
  let K := geometric x hn hq i h7 w spanBound hit mean
  refine .inr ⟨K,?_⟩
  intro u hu nd'
  have first : FirstExit hit u := hu
  have hspan : physical x i (w++u)≤K.span u :=
    Nat.le_of_eq (geometric_stamp x hn hq i h7 w spanBound hit mean u first).symm
  have R := WindowOrdinaryHandoff.word_handoff hp hc hn F P hP a ht u first
  change WindowOrdinaryHandoff.Handoff P.cert
    (GGTiming.runMarks (WindowTripleHandoff.joined hp hc hn) (.inl F) u) at R
  -- Use the same join equation in all three disjuncts, not a padded observer.
  have joined :
      current hp hc hn x hq i (w++u)=
        GGTiming.runMarks (WindowTripleHandoff.joined hp hc hn) (.inl F) u :=
    (current_append hp hc hn x hq i w u).trans (by rw [hF])
  rcases R with bad|⟨F',P',Q',m',len'⟩|⟨E,Q',mem⟩
  · have H : done hp hc hn x hq i (w++u) := by unfold done; rwa [joined]
    exact (nd' H).elim
  · exact .inr ⟨hspan,.inr ⟨F',P',joined.trans Q',m',by omega⟩⟩
  · obtain ⟨r,t,rt,eq⟩ := protectedIndex hp hc hn x hq i w F P hF hP E mem
    exact .inr ⟨hspan,.inl ⟨E,r,joined.trans Q',t,rt,eq⟩⟩

theorem singleton_slot (h7 : 7≤RankPhysical.rank x) :
    Slot hp hc hn x hq i 3 := by
  intro w h a nd
  obtain L|⟨T,H⟩ := ordinary_stage hp hc hn x hq i h7 1 (by omega) w h
    ((midShape hp hc hn x hq i 1 (by omega) w h).mp a) nd
  · exact .inl ((midShape hp hc hn x hq i 2 (by omega) w h).mpr L)
  · exact .inr ⟨T,fun u hu hd => (midShape hp hc hn x hq i 2 (by omega) (w++u) _).mpr (H u hu hd)⟩

theorem pair_slot (h7 : 7≤RankPhysical.rank x) :
    Slot hp hc hn x hq i 2 := by
  intro w h a nd
  obtain L|⟨T,H⟩ := ordinary_stage hp hc hn x hq i h7 2 (by omega) w h
    ((midShape hp hc hn x hq i 2 (by omega) w h).mp a) nd
  · exact .inl ((midShape hp hc hn x hq i 3 (by omega) w h).mpr L)
  · exact .inr ⟨T,fun u hu hd => (midShape hp hc hn x hq i 3 (by omega) (w++u) _).mpr (H u hu hd)⟩

theorem triple_slot (h7 : 7≤RankPhysical.rank x) :
    Slot hp hc hn x hq i 1 := by
  intro w h a nd
  have aw := (midShape hp hc hn x hq i 3 (by omega) w h).mp a
  obtain ⟨spanBound,prot|own⟩ := aw.resolve_left nd
  · exact .inl (.inr ⟨spanBound,.inl prot⟩)
  obtain ⟨F,P,hF,hP,ge⟩ := own
  have len : P.cert.length=3 := Nat.le_antisymm P.bounded ge
  have led : F.ledger=observe (initial x) w := by
    have L := fold_ledger hp hc hn hq (scope x i) w
    change WindowLatch.project Front.ledger (current hp hc hn x hq i w)=_ at L
    rw [hF] at L
    exact L
  have keep := WindowNoLoss.not_done_no_loss hp hc hn hq (scope x i) w nd
  obtain ⟨before,_,coord⟩ := coordinates hp hc hn x hq i w F P hF hP
  let d := P.before.length
  have cap : d+2<7 := by dsimp [d]; rcases before with B|B <;> omega
  have cert : P.cert=[labels x i d,labels x i (d+1),labels x i (d+2)] := by
    apply List.ext_getElem (by simpa using len)
    intro j hj _
    have E : j=0∨j=1∨j=2 := by omega
    rcases E with rfl|rfl|rfl
    · change P.cert[0]=labels x i d; simpa only [d,Nat.add_zero] using coord 0 (by omega)
    · exact coord 1 (by omega)
    · exact coord 2 (by omega)
  have clock := WindowTripleWindow.clock hn x hq i h7 w h spanBound keep F led P d cap cert
  let tick := WindowScopedRace.cursorNext (p:=p) (c:=c) (window7 (roster x) i) P.cert
  let hit := fun u => WindowScopedRace.Cursor.exit (GGTiming.runMarks tick (F.ledger,false) u)
  have mean := wordMean tick (F.ledger,false) WindowScopedRace.Cursor.exit clock
  let T := geometric x hn hq i h7 w spanBound hit mean
  refine .inr ⟨T,?_⟩
  intro u hu nd'
  have first : FirstExit hit u := hu
  have hspan : physical x i (w++u)≤T.span u :=
    Nat.le_of_eq (geometric_stamp x hn hq i h7 w spanBound hit mean u first).symm
  have R := WindowTripleHandoff.first_stop hp hc hn F ⟨P,hP,rfl,len⟩ u first
  have joined :
      current hp hc hn x hq i (w++u)=
        GGTiming.runMarks (WindowTripleHandoff.joined hp hc hn) (.inl F) u :=
    (current_append hp hc hn x hq i w u).trans (by rw [hF])
  obtain ⟨v,e,f,eq,prev,hprev,phase⟩ := R.2
  rcases phase with reward|death
  · obtain ⟨who,_,front,loss,Q,m⟩ := reward
    have H : done hp hc hn x hq i (w++u) := by
      unfold done
      rw [joined,Q]
      simp [WindowFrontDone.done,m]
    exact (nd' H).elim
  · obtain ⟨a,post,kn,route,who,_,Q⟩ := death
    let en := kn.entry hn
    have own : en.victim∈P.cert := by
      change kn.victim∈P.cert
      rw [who]
      exact (WindowNamedFront.death_inv f.ledger (window7 (roster x) i) P.cert none e a post route).2.2.1
    obtain ⟨r,rpos,rbound,rEq⟩ := protectedIndex hp hc hn x hq i w F P hF hP en own
    exact .inr ⟨hspan,.inl ⟨en,r,joined.trans Q,rpos,rbound,rEq⟩⟩

theorem concreteMiddle (h7 : 7≤RankPhysical.rank x) :
    Middle hp hc hn x hq i :=
  ⟨singleton_slot hp hc hn x hq i h7,pair_slot hp hc hn x hq i h7,
   triple_slot hp hc hn x hq i h7⟩

theorem physicalPlan : WindowFiveStages.PhysicalPlan :=
  physical_plan_of_middle (fun hp hc hn x hq h7 i _ => concreteMiddle hp hc hn x hq i h7)

theorem rooted_short_window : RootedWindows.RootedShortWindowReward :=
  WindowFiveStages.rooted_short_window_of_plan physicalPlan

#print axioms triple_slot
#print axioms physicalPlan
#print axioms rooted_short_window
#print axioms singleton_slot
#print axioms pair_slot

end L4.WindowMiddle
