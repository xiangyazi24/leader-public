import Leader.L4.WindowTripleEntry
import Leader.L4.WindowTransactions

/-! The literal triple service cost is bounded by the current selected
window span, which is charged at the transaction's actual start. -/
namespace L4.WindowTripleWindow
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
      WindowScopedRace.Cursor.exit (F.ledger,false) (coefficient c*n*(h+1)) := by
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
  change 2564*n*((gap y r-1+1)+(gap y r1-1+1))≤coefficient c*n*(h+1)
  rw [Nat.sub_add_cancel g0,Nat.sub_add_cancel g1]
  have coef : 2564≤coefficient c := Nat.le_trans (by decide : 2564≤4096) (Nat.le_max_right _ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_right n coef) (by omega)

#print axioms clock
end L4.WindowTripleWindow
