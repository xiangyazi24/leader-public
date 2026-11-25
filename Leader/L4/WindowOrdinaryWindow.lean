import Leader.L4.WindowOrdinarySlot
import Leader.L4.WindowTransactions

/-! Install the literal ordinary push clock at an authenticated
active front and current original-roster cut. -/
namespace L4.WindowOrdinaryWindow

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
      (coefficient c*n*(h+1)) := by
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
  · exact Nat.le_max_right _ _

end L4.WindowOrdinaryWindow
