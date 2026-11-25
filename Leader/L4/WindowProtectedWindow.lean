import Leader.L4.WindowOrdinaryWindow

/-! Protected transaction initialization on the same seven-tag span
and exact named latch used by the protective probability monitor. -/
namespace L4.WindowProtectedWindow

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
      (startRunning E) (coefficient c*n*(h+1)) := by
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
    (gap y r-1) (gap y r1-1) h (coefficient c)
    (index_mem x i ⟨d+1,by omega⟩) (index_mem x i ⟨d+2,by omega⟩)
    (V _ (by omega) (by omega)) subCert (protected_of_roster E (certified E) r b k
      T1 T2 T3 (V _ (by omega) (by omega)) (V _ (by omega) (by omega))) heQ S (Nat.le_max_right _ _)

#print axioms clock
end L4.WindowProtectedWindow
