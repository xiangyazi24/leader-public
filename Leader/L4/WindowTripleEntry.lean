import Leader.L4.WindowRosterTrace
import Leader.L4.WindowScopedSealPrep

/-! At a real first certified triple, construct the scoped deletion
context directly from the tracked original labels and current roster.
Gap lengths are measured at the actual admission, not at time zero. -/
namespace L4.WindowTripleEntry
open SevenTagCharge WindowLocal WindowScopedRace WindowScopedSealPrep
open WindowRoster WindowSpan WindowRosterTrace

theorem context_of_roster {p c n : Nat} {x₀ : Config p c n} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (hl : Valid z x₀)
    (j : Fin (RankPhysical.rank z.config)) (l m r : Fin n)
    (ml : l∈g) (mm : m∈g) (mr : r∈g) (nm : l≠m) (nr : l≠r)
    (Sl : z.slots (roster z.config j)=some l)
    (Sm : z.slots (roster z.config (rightNeighbor j))=some m)
    (Sr : z.slots (roster z.config (rightNeighbor (rightNeighbor j)))=some r)
    (Ll : (z.config (rootSite z.config j)).leader=true)
    (Lm : (z.config (rootSite z.config (rightNeighbor j))).leader=true)
    (Lr : (z.config (rootSite z.config (rightNeighbor (rightNeighbor j)))).leader=true) :
    let a := gap z.config j-1
    let b := gap z.config (rightNeighbor j)-1
    ∃ C : Context x₀ g [l,m,r] (rootSite z.config j) a b,
      rightNeighbor C.s=rootSite z.config j ∧ PairGeom C (z,false) := by
  let s := roster z.config j
  let t := roster z.config (rightNeighbor j)
  let u := roster z.config (rightNeighbor (rightNeighbor j))
  let a := gap z.config j-1
  let b := gap z.config (rightNeighbor j)-1
  have K := WindowPushEntry.rear_of_roster j l m r Sl Sm Sr nm nr
  have size : a+b+2<n := by
    have H : a+1+b+1<n := K.noWrap
    omega
  let C : Context x₀ g [l,m,r] (rootSite z.config j) a b :=
    ⟨hn,size,l,m,r,s,t,u,by simpa using And.intro ml (And.intro mm mr),
      by simp,by simp,by simp⟩
  have SectL : CertifiedSector z l m s t a := by
    refine ⟨⟨Sl,Ll⟩,⟨Sm,Lm⟩,?_,K.firstW⟩
    rw [liftedSite_succ,K.wAt]
  have SectR : CertifiedSector z m r t u b := by
    refine ⟨⟨Sm,Lm⟩,⟨Sr,Lr⟩,?_,K.firstK⟩
    rw [liftedSite_succ,K.kAt]
  dsimp only
  refine ⟨C,?_,?_⟩
  · rfl
  · constructor
    · apply Or.inr
      exact ⟨hl,SectL⟩
    · apply Or.inr
      exact ⟨hl,SectR⟩

private theorem labels_append {p c n : Nat} (x : Config p c n)
    (a : Fin (RankPhysical.rank x)) (j k : Nat) :
    labels x (liftedSite a j) k = labels x a (j+k) := by
  unfold labels
  rw [WindowPushEntry.lift_add]

/-- Instantiate the triple's deletion clock on the literal endpoint of
a surviving original seven-window prefix. The offset chooses any
consecutive slice of three of its original labels. -/
theorem original_window_triple {p c n : Nat} (x : Config p c n) (hn : 4≤n)
    (hm : MCOV x) (hc : COV x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (w : List (Fin n))
    (alive : hit (observe (initial x) w).losses (window7 (roster x) i)=false)
    (o : Nat) (ho : o+2<7) :
    let z := observe (initial x) w
    let g := window7 (roster x) i
    let cert := [labels x i o, labels x i (o+1), labels x i (o+2)]
    ∃ j : Fin (RankPhysical.rank z.config),
      (∀ k : Fin 3, z.slots (labels z.config j k.val)=some (labels x i (o+k.val))) ∧
      ((∀ k : Fin 3, (z.config (rightNeighbor (labels z.config j k.val))).leader=true) →
        IIDExpectedHittingTimeAtMost (cursorNext g cert) Cursor.exit (z,false)
          (2564*n*(gap z.config j+gap z.config (rightNeighbor j)))) := by
  let z := observe (initial x) w
  let g := window7 (roster x) i
  obtain ⟨j₀,J⟩ := original_window x hn hm hc i h7 w alive
  let j := liftedSite j₀ o
  let l := labels x i o
  let m := labels x i (o+1)
  let r := labels x i (o+2)
  have T (k : Fin 3) : z.slots (labels z.config j k.val)=some (labels x i (o+k.val)) := by
    rw [show j=liftedSite j₀ o from rfl,labels_append]
    exact J ⟨o+k.val,by have := k.isLt; omega⟩
  have distinct {a b : Nat} (ha : a<7) (hb : b<7) (H : a≠b) :
      labels x i a≠labels x i b := by
    intro E
    exact H (liftedSite_inj i (by omega) (by omega) (roster_injective _ _ _ E))
  refine ⟨j,T,?_⟩
  intro lives
  have hv : Valid z x := valid_word hn (initial x) x w (valid_init x hm hc)
  have v₀ : (0 : Fin 3).val=0 := rfl
  have v₁ : (1 : Fin 3).val=1 := rfl
  have v₂ : (2 : Fin 3).val=2 := rfl
  obtain ⟨C,base,H⟩ := context_of_roster hn z g hv j l m r
    (index_mem x i ⟨o,by omega⟩) (index_mem x i ⟨o+1,by omega⟩)
    (index_mem x i ⟨o+2,by omega⟩) (distinct (by omega) (by omega) (by omega))
    (distinct (by omega) (by omega) (by omega))
    (by simpa only [labels,liftedSite_zero,Nat.add_zero,v₀,l] using T (0 : Fin 3))
    (by simpa only [labels,liftedSite_succ,liftedSite_zero,v₁,m] using T (1 : Fin 3))
    (by simpa only [labels,liftedSite_succ,liftedSite_zero,v₂,r] using T (2 : Fin 3))
    (by simpa only [rootSite,labels,liftedSite_zero,v₀] using lives (0 : Fin 3))
    (by simpa only [rootSite,labels,liftedSite_succ,liftedSite_zero,v₁] using lives (1 : Fin 3))
    (by simpa only [rootSite,labels,liftedSite_succ,liftedSite_zero,v₂] using lives (2 : Fin 3))
  have A := gap_pos z.config j
  have B := gap_pos z.config (rightNeighbor j)
  have F := expected_scoped_deletion C base (z,false) H
  simpa only [Nat.sub_add_cancel A,Nat.sub_add_cancel B] using F

end L4.WindowTripleEntry
