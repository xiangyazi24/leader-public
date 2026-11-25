import Leader.L4.WindowPushEntry

/-! Original designated neighboring tags remain physically consecutive on every no-selected-loss word. -/
namespace L4.WindowRosterTrace
open SevenTagCharge WindowFourHeadCut WindowFourHeadTrace WindowRoster WindowSpan

private theorem noLoss_step {p c n : Nat} (g : List (Fin n))
    (z : Ledger p c n) (e : Fin n) (w : List (Fin n))
    (h : hit (observe z (e::w)).losses g=false) :
    WindowLocal.selectedGroupLoss g z e=none := by
  cases hsel : WindowLocal.selectedGroupLoss g z e with
  | none => rfl
  | some a =>
    obtain ⟨hLost,hIn⟩ := (WindowLocal.selectedGroupLoss_iff g z e a).mp hsel
    have hNow : a∈(advance z e).losses := by simp [advance,hLost]
    have hAfter := loss_monotone (advance z e) w a hNow
    have hHit : hit (observe z (e::w)).losses g=true := by
      apply List.any_eq_true.mpr
      exact ⟨a,hAfter,by simpa using hIn⟩
    rw [h] at hHit
    cases hHit

/-- A surviving originally consecutive triple has consecutive actual
slots on the endpoint ledger, irrespective of exterior retirements. -/
theorem geometry_word {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (g : List (Fin n)) (a b cTag : Fin n) (ha : a∈g) (hb : b∈g) (hc : cTag∈g)
    (z : Ledger p c n) (j v k : Fin n) (bi di : Nat)
    (hz : Valid z initial) (hG : Geometry z j v k a b cTag bi di)
    (word : List (Fin n)) (h : hit (observe z word).losses g=false) :
    ∃ j' v' k' : Fin n, ∃ bi' di' : Nat,
      Geometry (observe z word) j' v' k' a b cTag bi' di' := by
  induction word generalizing z j v k bi di with
  | nil => exact ⟨j,v,k,bi,di,hG⟩
  | cons e w ih =>
    have hs := noLoss_step g z e w h
    have H := geom_step hn z g e j v k a b cTag bi di hG hz.markCover hz.covers ha hb hc hs
    exact ih _ _ _ _ _ _ (valid_step hn z initial e hz) H h

private theorem mark_of_slot {p c n : Nat} {z : Ledger p c n} {i a : Fin n}
    (h : Covers z.config z.slots) (ha : z.slots i=some a) : (z.config i).mark=true := by
  have H := h i
  rw [ha] at H
  exact H.symm

private theorem firstMark_index {p c n : Nat} {x : Config p c n}
    (i : Fin (RankPhysical.rank x)) (j : Fin n) (d : Nat)
    (h : FirstMark x (rightNeighbor (roster x i)) d)
    (he : liftedSite (rightNeighbor (roster x i)) d=j) :
    roster x (rightNeighbor i)=j := by
  have D := h.unique (firstMark_after_roster x i)
  rw [D,liftedSite_advance,show gap x i-1+1=gap x i by have := gap_pos x i; omega,
    wall_at_gap] at he
  exact he

/-- The lifted triple agrees with three consecutive entries of the
current canonical roster, not merely any order on surviving tags. -/
theorem roster_of_geometry {p c n : Nat} {z : Ledger p c n} (hcov : Covers z.config z.slots)
    {j v k a b cTag : Fin n} {bi di : Nat} (G : Geometry z j v k a b cTag bi di) :
    ∃ i : Fin (RankPhysical.rank z.config),
      roster z.config i=j ∧
      roster z.config (rightNeighbor i)=v ∧
      roster z.config (rightNeighbor (rightNeighbor i))=k := by
  obtain ⟨i,hi⟩ := (roster_exact z.config j).mpr (mark_of_slot hcov G.jTag)
  have fw : FirstMark z.config (rightNeighbor j) bi := by
    refine ⟨by have := G.width; have := G.wBefore; omega,?_,?_⟩
    · rw [G.wLift]
      exact mark_of_slot hcov G.wTag
    · intro l hl
      rw [G.noOther l (by have := G.wBefore; omega) (by omega)]
      decide
  have wloc : roster z.config (rightNeighbor i)=v := by
    apply firstMark_index i v bi
    · rwa [hi]
    · rw [hi]; exact G.wLift
  have nxt : liftedSite (rightNeighbor j) (bi+1)=rightNeighbor v := by
    rw [liftedSite_succ,G.wLift]
  have shift (l : Nat) : liftedSite (rightNeighbor v) l=
      liftedSite (rightNeighbor j) (bi+1+l) := by
    rw [←nxt,WindowPushEntry.lift_add]
  have fk : FirstMark z.config (rightNeighbor v) (di-(bi+1)) := by
    refine ⟨by have := G.width; omega,?_,?_⟩
    · rw [shift,Nat.add_sub_of_le (by have := G.wBefore; omega : bi+1≤di),G.kLift]
      exact mark_of_slot hcov G.kTag
    · intro l hl
      rw [shift,G.noOther _ (by omega) (by omega)]
      decide
  have kloc : roster z.config (rightNeighbor (rightNeighbor i))=k := by
    apply firstMark_index (rightNeighbor i) k (di-(bi+1))
    · rwa [wloc]
    · rw [wloc,shift,Nat.add_sub_of_le (by have := G.wBefore; omega : bi+1≤di)]
      exact G.kLift
  exact ⟨i,hi,wloc,kloc⟩

/-- Tag addresses at an index of the original clockwise roster. -/
def labels {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (d : Nat) : Fin n := roster x (liftedSite i d)

/-- A current roster anchor for any triple of original designated
successors. The three old positions remain consecutive on the
surviving raw word, even across residue zero. -/
theorem original_three {p c n : Nat} (x : Config p c n) (hn : 4≤n)
    (hm : MCOV x) (hcv : COV x) (g : List (Fin n)) (i : Fin (RankPhysical.rank x))
    (h0 : labels x i 0∈g) (h1 : labels x i 1∈g) (h2 : labels x i 2∈g)
    (hne1 : labels x i 0≠labels x i 1) (hne2 : labels x i 0≠labels x i 2)
    (w : List (Fin n)) (h : hit (observe (initial x) w).losses g=false) :
    let z := observe (initial x) w
    ∃ j : Fin (RankPhysical.rank z.config),
      ∀ d : Fin 3, z.slots (labels z.config j d.val)=some (labels x i d.val) := by
  let a := labels x i 0
  let b := labels x i 1
  let k := labels x i 2
  have initTag (d : Nat) : (initial x).slots (labels x i d)=some (labels x i d) := by
    have hh := (roster_exact x _).mp ⟨liftedSite i d,rfl⟩
    change (x (labels x i d)).mark=true at hh
    change initSlots x (labels x i d)=_
    simp [initSlots,hh]
  have hA : (initial x).slots (roster x i)=some a := by
    simpa only [a,labels,liftedSite_zero] using initTag 0
  have hB : (initial x).slots (roster x (rightNeighbor i))=some b := by
    simpa only [b,labels,liftedSite_succ,liftedSite_zero] using initTag 1
  have hK : (initial x).slots (roster x (rightNeighbor (rightNeighbor i)))=some k := by
    simpa only [k,labels,liftedSite_succ,liftedSite_zero] using initTag 2
  have R := WindowPushEntry.rear_of_roster (z:=initial x) i a b k hA hB hK hne1 hne2
  have V := valid_init x hm hcv
  obtain ⟨j',v',k',bi,di,G⟩ := geometry_word hn g a b k h0 h1 h2 _ _ _ _ _ _ V
    (WindowPushEntry.rear_geometry R) w h
  have V' := valid_word hn (initial x) x w V
  obtain ⟨r,hj,hv,hk⟩ := roster_of_geometry V'.covers G
  refine ⟨r,?_⟩
  intro d
  have hd : d.val=0 ∨ d.val=1 ∨ d.val=2 := by have := d.isLt; omega
  rcases hd with hd|hd|hd
  · simpa only [a,hd,labels,liftedSite_zero,hj] using G.jTag
  · simpa only [b,hd,labels,liftedSite_succ,liftedSite_zero,hv] using G.wTag
  · simpa only [k,hd,labels,liftedSite_succ,liftedSite_zero,hk] using G.kTag

private theorem labels_add {p c n : Nat} (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (a b : Nat) :
    labels x (liftedSite i a) b=labels x i (a+b) := by
  unfold labels
  rw [WindowPushEntry.lift_add]

/-- Stitch the overlapping triples (0,1,2) and (1,2,3) by uniqueness
of the shared surviving tag. This is the ordinary four-head input. -/
theorem original_four {p c n : Nat} (x : Config p c n) (hn : 4≤n)
    (hm : MCOV x) (hcv : COV x) (g : List (Fin n)) (i : Fin (RankPhysical.rank x))
    (all : ∀ d : Fin 4, labels x i d.val∈g)
    (distinct : ∀ a b : Fin 4, a≠b → labels x i a.val≠labels x i b.val)
    (w : List (Fin n)) (h : hit (observe (initial x) w).losses g=false) :
    let z := observe (initial x) w
    ∃ j : Fin (RankPhysical.rank z.config),
      ∀ d : Fin 4, z.slots (labels z.config j d.val)=some (labels x i d.val) := by
  let z := observe (initial x) w
  obtain ⟨j,A⟩ := original_three x hn hm hcv g i (all 0) (all 1) (all 2)
    (distinct 0 1 (by decide)) (distinct 0 2 (by decide)) w h
  obtain ⟨k,B⟩ := original_three x hn hm hcv g (liftedSite i 1)
    (by rw [labels_add]; exact all 1)
    (by rw [labels_add]; exact all 2)
    (by rw [labels_add]; exact all 3)
    (by rw [labels_add,labels_add]; exact distinct 1 2 (by decide))
    (by rw [labels_add,labels_add]; exact distinct 1 3 (by decide)) w h
  have V := valid_word hn (initial x) x w (valid_init x hm hcv)
  have Y := A 1
  have X := B 0
  change z.slots (labels z.config j 1)=some (labels x i 1) at Y
  change z.slots (labels z.config k 0)=some (labels x (liftedSite i 1) 0) at X
  rw [labels_add] at X
  have R := V.unique _ _ _ X Y
  have he : k=liftedSite j 1 := by
    apply roster_injective z.config
    simpa only [labels,liftedSite_zero] using R
  refine ⟨j,?_⟩
  intro d
  by_cases hd : d.val<3
  · exact A ⟨d.val,hd⟩
  · have h3 : d.val=3 := by have := d.isLt; omega
    have C := B 2
    change z.slots (labels z.config k 2)=some (labels x (liftedSite i 1) 2) at C
    rw [he,labels_add,labels_add] at C
    simpa only [h3] using C

/-- The exact roster of the seven original designated tags at every
no-selected-loss endpoint. All six ordinary neighbor pairs remain
adjacent in the canonical roster of the actual physical configuration. -/
theorem original_window {p c n : Nat} (x : Config p c n) (hn : 4≤n)
    (hm : MCOV x) (hcv : COV x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (w : List (Fin n))
    (h : hit (observe (initial x) w).losses (window7 (roster x) i)=false) :
    let z := observe (initial x) w
    ∃ j : Fin (RankPhysical.rank z.config),
      ∀ d : Fin 7, z.slots (labels z.config j d.val)=some (labels x i d.val) := by
  let z := observe (initial x) w
  let g := window7 (roster x) i
  have mem {d : Nat} (hd : d<7) : labels x i d∈g := by
    apply List.mem_map.mpr
    exact ⟨⟨d,hd⟩,List.mem_finRange _,rfl⟩
  have different {a b : Nat} (ha : a<7) (hb : b<7) (hab : a≠b) :
      labels x i a≠labels x i b := by
    intro he
    exact hab (liftedSite_inj i (by omega) (by omega) (roster_injective x _ _ he))
  obtain ⟨j,A⟩ := original_four x hn hm hcv g i
    (fun d => mem (by have := d.isLt; omega))
    (fun a b hab => different (by have := a.isLt; omega) (by have := b.isLt; omega)
      (fun he => hab (Fin.ext he))) w h
  obtain ⟨k,B⟩ := original_four x hn hm hcv g (liftedSite i 3)
    (fun d => by rw [labels_add]; exact mem (by have := d.isLt; omega))
    (fun a b hab => by
      rw [labels_add,labels_add]
      exact different (by have := a.isLt; omega) (by have := b.isLt; omega)
        (fun he => hab (Fin.ext (by omega)))) w h
  have V := valid_word hn (initial x) x w (valid_init x hm hcv)
  have Y := A 3
  have X := B 0
  change z.slots (labels z.config j 3)=some (labels x i 3) at Y
  change z.slots (labels z.config k 0)=some (labels x (liftedSite i 3) 0) at X
  rw [labels_add] at X
  have R := V.unique _ _ _ X Y
  have he : k=liftedSite j 3 := by
    apply roster_injective z.config
    simpa only [labels,liftedSite_zero] using R
  refine ⟨j,?_⟩
  intro d
  by_cases hd : d.val<4
  · exact A ⟨d.val,hd⟩
  · let t : Fin 4 := ⟨d.val-3,by have := d.isLt; omega⟩
    have C := B t
    change z.slots (labels z.config k t.val)=some (labels x (liftedSite i 3) t.val) at C
    rw [he,labels_add,labels_add,show 3+t.val=d.val by dsimp [t]; omega] at C
    exact C

/-- Membership for a literal original index of the seven window. -/
theorem index_mem {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (d : Fin 7) : labels x i d.val ∈ window7 (roster x) i :=
  List.mem_map.mpr ⟨d,List.mem_finRange _,rfl⟩

/-- Literal ordinary extension start from an original window offset
with three remaining successors. The supplier and the ghost target
are identified by their original tags, regardless of physical drift. -/
theorem ordinary_push_window {p c n : Nat} (x : Config p c n) (hn : 4≤n)
    (hm : MCOV x) (hcv : COV x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x)
    (w : List (Fin n)) (h : hit (observe (initial x) w).losses (window7 (roster x) i)=false)
    (d : Nat) (hd : d+3<7)
    (cert : List (Fin n)) (hc : labels x i d∈cert)
    (s t : Fin n)
    (hS : WindowLocal.TaggedLeader (observe (initial x) w) s (labels x i d))
    (hT : (observe (initial x) w).slots t=some (labels x i (d+1)))
    (hGhost : ((observe (initial x) w).config (rightNeighbor t)).leader=false) :
    ∃ q : WindowA0Push.State p c n,
      q.cursor.ledger=observe (initial x) w ∧ q.terminal=false ∧
      WindowA0Push.ValidCut x (rightNeighbor s) cert (labels x i (d+1))
        (labels x i (d+2)) (labels x i (d+3)) q := by
  let z := observe (initial x) w
  obtain ⟨j,A⟩ := original_window x hn hm hcv i h7 w h
  let r := liftedSite j d
  let v := z.config
  have V := valid_word hn (initial x) x w (valid_init x hm hcv)
  have P (k : Nat) (hk : k≤3) :
      z.slots (labels v r k)=some (labels x i (d+k)) := by
    rw [show labels v r k=labels v j (d+k) from labels_add v j d k]
    exact A ⟨d+k,by omega⟩
  have E : roster v r=s := by
    have R := P 0 (by decide)
    change z.slots (roster v (liftedSite r 0))=some (labels x i (d+0)) at R
    rw [liftedSite_zero,Nat.add_zero] at R
    exact V.unique _ _ _ R hS.1
  have E' : roster v (rightNeighbor r)=t := by
    have R := P 1 (by decide)
    change z.slots (roster v (liftedSite r 1))=some _ at R
    rw [liftedSite_succ,liftedSite_zero] at R
    exact V.unique _ _ _ R hT
  have PL : WindowLocal.TaggedLeader z (roster v r) (labels x i d) := by rwa [E]
  have P1 : z.slots (roster v (rightNeighbor r))=some (labels x i (d+1)) := by rwa [E']
  have P2 : z.slots (roster v (rightNeighbor (rightNeighbor r)))=some (labels x i (d+2)) := by
    have R := P 2 (by decide)
    simpa only [labels,liftedSite_succ,liftedSite_zero] using R
  have P3 : z.slots (roster v (rightNeighbor (rightNeighbor (rightNeighbor r))))=
      some (labels x i (d+3)) := by
    have R := P 3 (by decide)
    simpa only [labels,liftedSite_succ,liftedSite_zero] using R
  have nE (m l : Nat) (hm : m<7) (hl : l<7) (hne : m≠l) :
      labels x i m≠labels x i l := by
    intro E
    exact hne (liftedSite_inj i (by omega) (by omega) (roster_injective x _ _ E))
  have G : (z.config (rootSite v (rightNeighbor r))).leader=false := by
    change (z.config (rightNeighbor (roster v (rightNeighbor r)))).leader=false
    rwa [E']
  have Q := WindowPushEntry.ordinary_of_roster cert r
    (labels x i d) (labels x i (d+1)) (labels x i (d+2)) (labels x i (d+3)) V
    PL hc P1 P2 P3 (nE _ _ (by omega) (by omega) (by omega))
    (nE _ _ (by omega) (by omega) (by omega))
    (nE _ _ (by omega) (by omega) (by omega)) G
  refine ⟨WindowPushEntry.start z (roster v (rightNeighbor r))
    (roster v (rightNeighbor (rightNeighbor r)))
    (roster v (rightNeighbor (rightNeighbor (rightNeighbor r))))
    (gap v r-1) (gap v (rightNeighbor r)-1) (gap v (rightNeighbor (rightNeighbor r))-1),rfl,rfl,?_⟩
  rw [←E]
  exact Q

end L4.WindowRosterTrace
