import Leader.L4.WindowMiddle

namespace L4.WindowCappedOrdinaryClock

open SevenTagCharge WindowRoster WindowSpan WindowLocal WindowOwnership
open WindowOrdinarySlot WindowRosterTrace WindowTransactions
open WindowSpanTrace WindowPushEntry
open TripleRenewal WindowFiveStages RootedAssembly

private theorem lift_add {n : Nat} (a : Fin n) (d e : Nat) :
    liftedSite (liftedSite a d) e=liftedSite a (d+e) := by
  apply Fin.ext
  change ((a.val+d)%n+e)%n=(a.val+(d+e))%n
  simp [Nat.add_assoc]

theorem span_three {p c n : Nat} (x : Config p c n)
    (j : Fin (RankPhysical.rank x)) :
    spanK x j 3=gap x j+gap x (rightNeighbor j)+gap x (rightNeighbor (rightNeighbor j)) := by
  rw [show 3=2+1 by decide,spanK_succ,show 2=1+1 by decide,spanK_succ,
    show 1=0+1 by decide,spanK_succ]
  simp [spanK,liftedSite_succ,liftedSite_zero,TaggedTail.sumEdge]

private theorem push_arithmetic {n b c donor h C : Nat}
    (hs : donor+1+b+c≤h) (hC : 4096≤C) :
    4*n*(2*(2*b+c+1)+min (n-2) (max 2 (donor+(2*b+c+1)))+1)≤C*n*(h+1) := by
  let P := 2*b+c+1
  let m := min (n-2) (max 2 (donor+P))
  have hm : m≤2*h+2 := Nat.le_trans (Nat.min_le_right _ _)
    (Nat.max_le.mpr ⟨by omega,by dsimp [P]; omega⟩)
  have hsmall : 4*(2*P+m+1)≤4096*(h+1) := by dsimp [P] at *; omega
  have B := Nat.mul_le_mul_left n (Nat.le_trans hsmall (Nat.mul_le_mul_right (h+1) hC))
  simpa only [P,m,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using B

/-- Both ordinary stages share this exact raw-clock implementation.
The target slot's ghost bit is supplied by the front's normalization. -/
theorem clock {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (w : Word n) (h : Nat) (hbnd : physical x i w≤h)
    (keep : SevenTagCharge.hit (observe (initial x) w).losses (window7 (roster x) i)=false)
    (F : Front x (window7 (roster x) i)) (hL : F.ledger=observe (initial x) w)
    (P : Progress F.ledger (window7 (roster x) i)) (hm : F.mode=.owned P)
    (d : Nat) (dh : d+3<7) (hcert : labels x i d∈P.cert)
    (ht : P.target=some (labels x i (d+1)))
    (ghost : ∀ s, F.ledger.slots s=some (labels x i (d+1)) →
      (F.ledger.config (rightNeighbor s)).leader=false) :
    IIDExpectedHittingTimeAtMost (next hp hc hn) Slot.done (Slot.active F P hm rfl ht)
      (4096*n*(h+1)) := by
  let g := window7 (roster x) i
  have prj : (selected x i w).ledger=F.ledger :=
    (run_project g (init x (labels x i 0) (labels x i 6)) w).trans hL.symm
  have realRoster : ∃ j : Fin (RankPhysical.rank F.ledger.config),
      WindowSpan.span F.ledger.config j≤h ∧
      ∀ k : Fin 7, F.ledger.slots (labels F.ledger.config j k.val)=some (labels x i k.val) := by
    obtain ⟨j,_,s,K⟩ := selected_current x hn hq.1 hq.2.1 i h7 w keep
    have B : ∃ j : Fin (RankPhysical.rank (selected x i w).ledger.config),
        WindowSpan.span (selected x i w).ledger.config j≤h ∧
        ∀ k : Fin 7, (selected x i w).ledger.slots
          (labels (selected x i w).ledger.config j k.val)=some (labels x i k.val) :=
      ⟨j,s ▸ hbnd,K⟩
    rw [←prj]
    exact B
  obtain ⟨j,spanBound,edges⟩ := realRoster
  let y := F.ledger.config
  let a := labels x i (d+1)
  let b := labels x i (d+2)
  let k := labels x i (d+3)
  let r := liftedSite j d
  let r1 := rightNeighbor r
  let r2 := rightNeighbor r1
  let r3 := rightNeighbor r2
  have tagAt (m : Nat) (mh : m≤3) :
      F.ledger.slots (labels y r m)=some (labels x i (d+m)) := by
    rw [show labels y r m=labels y j (d+m) by unfold labels r; rw [lift_add]]
    exact edges ⟨d+m,by omega⟩
  have T0 : F.ledger.slots (roster y r)=some (labels x i d) := by
    simpa only [labels,liftedSite_zero,Nat.add_zero] using tagAt 0 (by decide)
  have T1 : F.ledger.slots (roster y r1)=some a := by
    simpa only [labels,liftedSite_succ,liftedSite_zero,r1,a] using tagAt 1 (by decide)
  have T2 : F.ledger.slots (roster y r2)=some b := by
    simpa only [labels,liftedSite_succ,liftedSite_zero,r2,r1,b] using tagAt 2 (by decide)
  have T3 : F.ledger.slots (roster y r3)=some k := by
    simpa only [labels,liftedSite_succ,liftedSite_zero,r3,r2,r1,k] using tagAt 3 (by decide)
  let s := P.owned.slot (labels x i d)
  have S := P.owned.live _ hcert
  have E : s=roster y r := F.valid.unique _ _ _ S.1 T0
  have TL : TaggedLeader F.ledger (roster y r) (labels x i d) := E ▸ S
  have dif (i₁ i₂ : Nat) (h₁ : i₁<7) (h₂ : i₂<7) (dif : i₁≠i₂) :
      labels x i i₁≠labels x i i₂ :=
    selected_distinct x i h7 ⟨i₁,h₁⟩ ⟨i₂,h₂⟩ (fun E => dif (congrArg Fin.val E))
  let q := WindowPushEntry.start F.ledger (roster y r1) (roster y r2) (roster y r3)
    (gap y r-1) (gap y r1-1) (gap y r2-1)
  have VC := ordinary_of_roster P.cert r (labels x i d) a b k F.valid TL hcert T1 T2 T3
    (dif d (d+1) (by omega) (by omega) (by omega))
    (dif (d+1) (d+2) (by omega) (by omega) (by omega))
    (dif (d+1) (d+3) (by omega) (by omega) (by omega)) (ghost _ T1)
  have p0 := gap_pos y r
  have p1 := gap_pos y r1
  have p2 := gap_pos y r2
  have bounds : gap y r+gap y r1+gap y r2≤h := by
    have L := subspan_le y j d 3 6 (by omega)
    rw [show liftedSite j d=r from rfl,span_three] at L
    exact Nat.le_trans L spanBound
  have hI : q.cursor.index+1=gap y r1 := by
    change gap y r1-1+1=gap y r1
    omega
  have hW : q.cursor.width+1=gap y r1+gap y r2 := by
    change (gap y r1-1)+1+(gap y r2-1)+1=_
    omega
  have M := ordinary_mean hp hc hn F P hm (rootSite y r) a b k ht
    (index_mem x i ⟨d+1,by omega⟩) (index_mem x i ⟨d+2,by omega⟩)
    (index_mem x i ⟨d+3,by omega⟩) (dif (d+1) (d+2) (by omega) (by omega) (by omega))
    q rfl rfl VC (gap y r1) (gap y r2) hI hW
  apply expected_mono M
  apply push_arithmetic
  · change (gap y r-1)+1+gap y r1+gap y r2≤h
    omega
  · exact Nat.le_refl _

#print axioms clock

end L4.WindowCappedOrdinaryClock

namespace L4.WindowCappedProtectedClock

open SevenTagCharge WindowRoster WindowSpan WindowSpanTrace WindowRosterTrace
open WindowTransactions WindowPushEntry WindowProtectedSlot WindowProtectedOuter
open TripleRenewal WindowFiveStages RootedAssembly

private theorem lift_add {n : Nat} (a : Fin n) (d e : Nat) :
    liftedSite (liftedSite a d) e=liftedSite a (d+e) := by
  apply Fin.ext
  change ((a.val+d)%n+e)%n=(a.val+(d+e))%n
  simp [Nat.add_assoc]

theorem clock {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (w : Word n) (h : Nat) (hbnd : physical x i w≤h)
    (keep : hit (observe (initial x) w).losses (window7 (roster x) i)=false)
    (E : Entry x (window7 (roster x) i)) (hL : E.ledger=observe (initial x) w)
    (heQ : QuietEntrance E.ledger.config) (d : Nat) (hd : 0<d) (hr : d+2<7)
    (victim : E.victim=labels x i d) :
    IIDExpectedHittingTimeAtMost pushNext
      (fun r : Running x (window7 (roster x) i) => r.q.terminal=true)
      (startRunning E) (4096*n*(h+1)) := by
  let g := window7 (roster x) i
  let y := E.ledger.config
  have prj : (selected x i w).ledger=E.ledger :=
    (run_project g (init x (labels x i 0) (labels x i 6)) w).trans hL.symm
  have realRoster : ∃ j : Fin (RankPhysical.rank y),
      WindowSpan.span y j≤h ∧
      ∀ k : Fin 7, E.ledger.slots (labels y j k.val)=some (labels x i k.val) := by
    obtain ⟨j,_,s,K⟩ := selected_current x hn hq.1 hq.2.1 i h7 w keep
    have B : ∃ j : Fin (RankPhysical.rank (selected x i w).ledger.config),
        WindowSpan.span (selected x i w).ledger.config j≤h ∧
        ∀ k : Fin 7, (selected x i w).ledger.slots
          (labels (selected x i w).ledger.config j k.val)=some (labels x i k.val) :=
      ⟨j,s ▸ hbnd,K⟩
    unfold y
    rw [←prj]
    exact B
  obtain ⟨j,spanBound,tags⟩ := realRoster
  let a := liftedSite j (d-1)
  let r := liftedSite j d
  let r1 := rightNeighbor r
  let r2 := rightNeighbor r1
  have rA : rightNeighbor a=r := by
    unfold a r
    rw [←liftedSite_succ,show d-1+1=d by omega]
  have T0 : E.ledger.slots (roster y a)=some (labels x i (d-1)) := tags ⟨d-1,by omega⟩
  have T1 : E.ledger.slots (roster y r)=some E.victim := by rw [victim]; exact tags ⟨d,by omega⟩
  have T2 : E.ledger.slots (roster y r1)=some (labels x i (d+1)) := by
    rw [show r1=liftedSite j (d+1) by exact (liftedSite_succ j d).symm]
    exact tags ⟨d+1,by omega⟩
  have T3 : E.ledger.slots (roster y r2)=some (labels x i (d+2)) := by
    rw [show r2=liftedSite j (d+2) by rw [liftedSite_succ,liftedSite_succ]]
    exact tags ⟨d+2,by omega⟩
  have SL : RankSupplier.Live E.supplier (RankSupplier.init y E.donor) := E.auth.2.1.1
  have M : (y (RearTrace.predecessor E.supplier)).mark=true := SL.2.1 _
    (.inl (by rw [RearTrace.right_predecessor]; exact SL.2.2.1))
  obtain ⟨s,hs⟩ := (roster_exact y _).mpr M
  have vs : rightNeighbor (roster y s)=E.supplier := by rw [hs,RearTrace.right_predecessor]
  have F := firstMark_after_roster y s
  rw [vs] at F
  have donorEq : gap y s-1=E.donor := F.unique SL.2.2.2.2.1
  have stepR : roster y (rightNeighbor s)=roster y r := by
    rw [←wall_at_gap y s]
    have T : liftedSite E.supplier E.donor=roster y r :=
      E.auth.1.unique _ _ _ E.auth.2.2.1 T1
    rw [←T,←donorEq,←vs,liftedSite_advance,
      show gap y s-1+1=gap y s by have := gap_pos y s; omega]
  have rs : rightNeighbor s=r := roster_injective y _ _ stepR
  have S0 : s=a := FreshSeparation.succ_inj (rs.trans rA.symm)
  have subCert : certified E ⊆ g := by
    unfold certified
    rw [←hs,S0,T0]
    rintro b hb
    have H : b=labels x i (d-1) := by simpa using hb
    subst b
    exact index_mem x i ⟨d-1,by omega⟩
  let b := labels x i (d+1)
  let k := labels x i (d+2)
  have V : ∀ m : Nat, d<m → m<7 → E.victim≠labels x i m := by
    intro m hm hh
    rw [victim]
    exact selected_distinct x i h7 ⟨d,by omega⟩ ⟨m,hh⟩ (fun C =>
      (by omega : d≠m) (congrArg Fin.val C))
  have S : E.donor+1+(gap y r-1+1)+(gap y r1-1+1)≤h := by
    have G := subspan_le y j (d-1) 3 6 (by omega)
    rw [WindowOrdinaryWindow.span_three,rA] at G
    have p0 := gap_pos y a
    have p1 := gap_pos y r
    have p2 := gap_pos y r1
    rw [S0] at donorEq
    change gap y a+gap y r+gap y r1≤WindowSpan.span y j at G
    omega
  exact protected_mean hp hc hn E (roster y r) (roster y r1) (roster y r2) b k
    (gap y r-1) (gap y r1-1) h (4096)
    (index_mem x i ⟨d+1,by omega⟩) (index_mem x i ⟨d+2,by omega⟩)
    (V _ (by omega) (by omega)) subCert (protected_of_roster E (certified E) r b k
      T1 T2 T3 (V _ (by omega) (by omega)) (V _ (by omega) (by omega))) heQ S (Nat.le_refl _)

#print axioms clock
end L4.WindowCappedProtectedClock

namespace L4.WindowCappedTripleClock
open SevenTagCharge WindowRoster WindowSpan WindowLocal WindowOwnership
open WindowRosterTrace WindowTransactions WindowSpanTrace
open WindowScopedRace WindowTripleEntry WindowScopedSealPrep WindowFiveStages TripleRenewal

theorem span_two {p c n : Nat} (x : Config p c n) (j : Fin (RankPhysical.rank x)) :
    spanK x j 2=gap x j+gap x (rightNeighbor j) := by
  rw [show 2=1+1 by decide,spanK_succ,show 1=0+1 by decide,spanK_succ]
  simp [spanK,liftedSite_succ,liftedSite_zero,TaggedTail.sumEdge]

theorem clock {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (w : Word n) (h : Nat) (hbnd : physical x i w≤h)
    (keep : SevenTagCharge.hit (observe (initial x) w).losses (window7 (roster x) i)=false)
    (F : Front x (window7 (roster x) i)) (hL : F.ledger=observe (initial x) w)
    (P : Progress F.ledger (window7 (roster x) i))
    (d : Nat) (dh : d+2<7)
    (hcert : P.cert=[labels x i d,labels x i (d+1),labels x i (d+2)]) :
    IIDExpectedHittingTimeAtMost (cursorNext (window7 (roster x) i) P.cert)
      WindowScopedRace.Cursor.exit (F.ledger,false) (4096*n*(h+1)) := by
  let g := window7 (roster x) i
  have prj : (selected x i w).ledger=F.ledger :=
    (run_project g (init x (labels x i 0) (labels x i 6)) w).trans hL.symm
  have realRoster : ∃ j : Fin (RankPhysical.rank F.ledger.config),
      WindowSpan.span F.ledger.config j≤h ∧
      ∀ k : Fin 7, F.ledger.slots (labels F.ledger.config j k.val)=some (labels x i k.val) := by
    obtain ⟨j,_,s,K⟩ := selected_current x hn hq.1 hq.2.1 i h7 w keep
    have B : ∃ j : Fin (RankPhysical.rank (selected x i w).ledger.config),
        WindowSpan.span (selected x i w).ledger.config j≤h ∧
        ∀ k : Fin 7, (selected x i w).ledger.slots
          (labels (selected x i w).ledger.config j k.val)=some (labels x i k.val) :=
      ⟨j,s ▸ hbnd,K⟩
    rw [←prj]
    exact B
  obtain ⟨j,spanBound,edges⟩ := realRoster
  let y := F.ledger.config
  let a := labels x i d
  let b := labels x i (d+1)
  let k := labels x i (d+2)
  let r := liftedSite j d
  let r1 := rightNeighbor r
  let r2 := rightNeighbor r1
  have tagAt (m : Nat) (mh : m≤2) :
      F.ledger.slots (labels y r m)=some (labels x i (d+m)) := by
    rw [show labels y r m=labels y j (d+m) by
      unfold labels r; rw [WindowPushEntry.lift_add]]
    exact edges ⟨d+m,by omega⟩
  have T0 : F.ledger.slots (roster y r)=some a := by
    simpa only [labels,liftedSite_zero,Nat.add_zero,a] using tagAt 0 (by decide)
  have T1 : F.ledger.slots (roster y r1)=some b := by
    simpa only [labels,liftedSite_succ,liftedSite_zero,r1,b] using tagAt 1 (by decide)
  have T2 : F.ledger.slots (roster y r2)=some k := by
    simpa only [labels,liftedSite_succ,liftedSite_zero,r2,r1,k] using tagAt 2 (by decide)
  have living (s id : Fin n) (hs : F.ledger.slots s=some id) (hmem : id∈P.cert) :
      (y (rightNeighbor s)).leader=true := by
    have S := P.owned.live _ hmem
    have E := F.valid.unique _ _ _ S.1 hs
    exact E ▸ S.2
  have L0 := living _ a T0 (by rw [hcert]; simp [a])
  have L1 := living _ b T1 (by rw [hcert]; simp [b])
  have L2 := living _ k T2 (by rw [hcert]; simp [k])
  have dif (i₁ i₂ : Nat) (h₁ : i₁<7) (h₂ : i₂<7) (dif : i₁≠i₂) :
      labels x i i₁≠labels x i i₂ :=
    selected_distinct x i h7 ⟨i₁,h₁⟩ ⟨i₂,h₂⟩ (fun E => dif (congrArg Fin.val E))
  obtain ⟨C,base,G⟩ := context_of_roster hn F.ledger g F.valid r a b k
    (index_mem x i ⟨d,by omega⟩) (index_mem x i ⟨d+1,by omega⟩)
    (index_mem x i ⟨d+2,by omega⟩)
    (dif d (d+1) (by omega) (by omega) (by omega))
    (dif d (d+2) (by omega) (by omega) (by omega))
    T0 T1 T2 L0 L1 L2
  have M := expected_scoped_deletion C base (F.ledger,false) G
  have g0 := gap_pos y r
  have g1 := gap_pos y r1
  have bounds : gap y r+gap y r1≤h := by
    have L := subspan_le y j d 2 6 (by omega)
    rw [show liftedSite j d=r from rfl,span_two] at L
    exact Nat.le_trans L spanBound
  rw [hcert]
  apply expected_mono M
  change 2564*n*((gap y r-1+1)+(gap y r1-1+1))≤4096*n*(h+1)
  rw [Nat.sub_add_cancel g0,Nat.sub_add_cancel g1]
  have coef : 2564≤4096 := by decide
  exact Nat.mul_le_mul (Nat.mul_le_mul_right n coef) (by omega)

#print axioms clock
end L4.WindowCappedTripleClock


namespace L4.WindowCappedPlan
open WindowPlan WindowFiveStages WindowOwnership WindowTransactions
open SevenTagCharge WindowLatch RootedAssembly WindowRoster WindowA0Join

variable {p c n : Nat}
variable (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
variable (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))

def SharpSlot (j : Nat) : Prop :=
  ∀ w h, Allow hp hc hn x hq i (j+1) w h → ¬done hp hc hn x hq i w →
    Allow hp hc hn x hq i j w h ∨ ∃ T : Transaction 4096 w h,
      ∀ u, FirstExit T.hit u → ¬done hp hc hn x hq i (w++u) →
        Allow hp hc hn x hq i j (w++u) (T.span u)
theorem protected_slot (h7 : 7≤RankPhysical.rank x) :
    SharpSlot hp hc hn x hq i 0 := by
  intro w h aw nd
  change done hp hc hn x hq i w ∨
    (physical x i w≤h ∧ (atProtected hp hc hn x hq i w ∨
      (2≤1 ∧ atOwned hp hc hn x hq i 4 w))) at aw
  obtain ⟨spanBound,E⟩ := aw.resolve_left nd
  have atLatch := E.resolve_right (by omega)
  obtain ⟨en,d,he,hd,hr,tag⟩ := atLatch
  have hL := fold_ledger hp hc hn hq (scope x i) w
  change WindowLatch.project Front.ledger (current hp hc hn x hq i w)=_ at hL
  rw [he] at hL
  change en.ledger=observe (initial x) w at hL
  have hQuiet : QuietEntrance en.ledger.config := by
    rw [hL,observe_config]
    exact RootedFresh.quiet_run x w hp hc hn hq
  have keep := WindowNoLoss.not_done_no_loss hp hc hn hq (scope x i) w nd
  have clock := WindowCappedProtectedClock.clock hp hc hn x hq i h7 w h spanBound keep en hL hQuiet d hd hr tag
  let T := WindowProtectedSlot.protected_transaction en w clock
  refine .inr ⟨T,?_⟩
  intro u hu nd'
  exfalso
  apply nd'
  unfold current fold at he
  rw [replay_run] at he
  have A := WindowProtectedSlot.joined_hit_after_latch
    (WindowLatch.front hn (decide hp hc hn)) (Front.initial x hq (scope x i)) en w u he
  unfold done current fold
  rw [replay_run,A]
  exact hu.2


end L4.WindowCappedPlan

namespace L4.WindowCappedMiddle

open WindowCappedPlan WindowPlan WindowOwnership WindowTransactions
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
    Mid hp hc hn x hq i (k+1) w h ∨ ∃ T : Transaction 4096 w h,
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
  have clock := WindowCappedOrdinaryClock.clock hp hc hn x hq i h7 w h spanBound noLoss
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
    SharpSlot hp hc hn x hq i 3 := by
  intro w h a nd
  obtain L|⟨T,H⟩ := ordinary_stage hp hc hn x hq i h7 1 (by omega) w h
    ((midShape hp hc hn x hq i 1 (by omega) w h).mp a) nd
  · exact .inl ((midShape hp hc hn x hq i 2 (by omega) w h).mpr L)
  · exact .inr ⟨T,fun u hu hd => (midShape hp hc hn x hq i 2 (by omega) (w++u) _).mpr (H u hu hd)⟩

theorem pair_slot (h7 : 7≤RankPhysical.rank x) :
    SharpSlot hp hc hn x hq i 2 := by
  intro w h a nd
  obtain L|⟨T,H⟩ := ordinary_stage hp hc hn x hq i h7 2 (by omega) w h
    ((midShape hp hc hn x hq i 2 (by omega) w h).mp a) nd
  · exact .inl ((midShape hp hc hn x hq i 3 (by omega) w h).mpr L)
  · exact .inr ⟨T,fun u hu hd => (midShape hp hc hn x hq i 3 (by omega) (w++u) _).mpr (H u hu hd)⟩

theorem triple_slot (h7 : 7≤RankPhysical.rank x) :
    SharpSlot hp hc hn x hq i 1 := by
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
  have clock := WindowCappedTripleClock.clock hn x hq i h7 w h spanBound keep F led P d cap cert
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


end L4.WindowCappedMiddle
