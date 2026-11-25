import Leader.L4.WindowFourHeadShadow

namespace L4.WindowA0Push
open WindowFourHeadCut WindowFourHeadTrace WindowFourHeadCap WindowScopedSupplier
  RankSupplier SevenTagCharge GGTiming RankPhysical

/-- An uncensored four-head cursor and the old supplier's lifted donor. -/
structure State (p c n : Nat) where
  cursor : Cursor p c n
  donor : Nat
  terminal : Bool

/-- Every raw mark advances the real ledger.  Only the stop flag is absorbing. -/
def next {p c n : Nat} (v : Fin n) (group cert : List (Fin n))
    (a : Fin n) (s : State p c n) (e : Fin n) : State p c n :=
  let q := s.cursor
  ⟨tick q e, (follow v s.donor q.ledger.config e).donor,
   s.terminal || decide (WindowLocal.route group cert (some a) q.ledger e ≠ .keep)⟩

theorem stop_sticky {p c n : Nat} (v : Fin n) (g cert : List (Fin n))
    (a : Fin n) (s : State p c n) (e : Fin n) (h : s.terminal=true) :
    (next v g cert a s e).terminal=true := by simp [next,h]

/-- Physical motion of the J slot and the shadow donor use exactly the same old pair. -/
theorem follow_landing_charge {p c n : Nat} (v : Fin n) (q : Cursor p c n)
    (d : Nat) (e : Fin n) (hj : q.j=liftedSite v d) :
    (follow v d q.ledger.config e).donor = d+jCharge q e ∧
    (tick q e).j=liftedSite v (follow v d q.ledger.config e).donor := by
  by_cases he : e=liftedSite v d
  · subst e
    by_cases hpay : geometricPay (q.ledger.config (liftedSite v d)) (q.ledger.config (rightNeighbor (liftedSite v d)))=true
    · simp [follow,init,tick,jCharge,landing,moves,hj,hpay,liftedSite_succ]
    · have hp := Bool.eq_false_iff.mpr hpay
      simp [follow,init,tick,jCharge,landing,moves,hj,hp]
  · have hb : (e == liftedSite v d)=false := Bool.eq_false_iff.mpr
      (fun h => he (beq_iff_eq.mp h))
    simp [follow,init,tick,jCharge,landing,moves,hj,he,hb]

theorem route_noloss {p c n : Nat} (g cert : List (Fin n))
    (a : Fin n) (q : Cursor p c n) (e : Fin n)
    (h : WindowLocal.route g cert (some a) q.ledger e = .keep) :
    WindowLocal.selectedGroupLoss g q.ledger e=none := by
  unfold WindowLocal.route at h
  split at h
  · contradiction
  · assumption

/-- Joint induction through the raw word; no auxiliary independent scheduler. -/
theorem retained_count {p c n : Nat} (v : Fin n) (g cert : List (Fin n)) (a : Fin n)
    (I : State p c n → Prop)
    (retain : ∀ s, I s → s.terminal=false →
      s.cursor.j=liftedSite v s.donor)
    (preserve : ∀ s e, I s → (next v g cert a s e).terminal=false →
      I (next v g cert a s e) ∧
      ((tick s.cursor e).ledger.config (rightNeighbor (tick s.cursor e).j)).leader=false) :
    ∀ s w, I s → (runMarks (next v g cert a) s w).terminal=false →
      RetainedKeep g s.cursor w ∧
      (runMarks (next v g cert a) s w).donor = s.donor+totalJ s.cursor w ∧
      I (runMarks (next v g cert a) s w) := by
  have hs : ∀ (s : State p c n) w, s.terminal=true →
      (runMarks (next v g cert a) s w).terminal=true := by
    intro s w
    induction w generalizing s with
    | nil => simp [runMarks]
    | cons e w ih => intro h; exact ih _ (stop_sticky v g cert a s e h)
  intro s w
  induction w generalizing s with
  | nil => intro h _; exact ⟨.nil,by simp [runMarks,totalJ],h⟩
  | cons e w ih =>
    intro hi hf
    let y := next v g cert a s e
    change (runMarks (next v g cert a) y w).terminal=false at hf
    have hy : y.terminal=false := by
      cases ht : y.terminal
      · rfl
      · rw [hs y w ht] at hf
        contradiction
    have hsf : s.terminal=false := by
      cases ht : s.terminal
      · rfl
      · rw [stop_sticky v g cert a s e ht] at hy
        contradiction
    have hc : WindowLocal.route g cert (some a) s.cursor.ledger e = .keep := by
      have hh : (s.terminal || decide (WindowLocal.route g cert (some a) s.cursor.ledger e ≠ .keep)) = false := hy
      simpa [hsf] using hh
    obtain ⟨hiy,hghost⟩ := preserve s e hi hy
    obtain ⟨hk,hd,hfI⟩ := ih y hiy hf
    have hd' := (follow_landing_charge v s.cursor s.donor e (retain s hi hsf)).1
    refine ⟨.cons (route_noloss g cert a s.cursor e hc) hghost hk,?_,hfI⟩
    change (runMarks (next v g cert a) y w).donor =
      s.donor+(jCharge s.cursor e+totalJ (tick s.cursor e) w)
    rw [hd]
    change (follow v s.donor s.cursor.ledger.config e).donor + totalJ (tick s.cursor e) w = _
    change (follow v s.donor s.cursor.ledger.config e).donor + _ = _
    rw [hd',Nat.add_assoc]

/-- Any retained ordinary cut carries both physical follow conclusions and
the local no-retirement hypothesis needed by the same-word shadow. -/
theorem ordinary_step {p c n d : Nat} {initial : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n))
    (q : Cursor p c n) (e a sv label : Fin n)
    (hj : q.j=liftedSite v d) (hLive : Live v (init q.ledger.config d))
    (hv : Valid q.ledger initial)
    (hsub : cert ⊆ group) (hcert : label ∈ cert)
    (hsite : rightNeighbor sv=v) (hsupp : WindowLocal.TaggedLeader q.ledger sv label)
    (ha : a ∈ group) (hTag : q.ledger.slots q.j=some a)
    (hr : WindowLocal.route group cert (some a) q.ledger e=.keep) :
    let y := follow v d q.ledger.config e
    (e=liftedSite v d → retirement q.ledger.config e=false) ∧
      Live v y ∧ (tick q e).ledger.slots (tick q e).j=some a ∧
      ((tick q e).ledger.config (rightNeighbor (tick q e).j)).leader=false := by
  have htag : q.ledger.slots (liftedSite v d)=some a := by simpa only [←hj] using hTag
  obtain ⟨hret,hl,ht⟩ := WindowScopedFourHead.ordinary_follow_of_keep hn
    v group cert q.ledger e a hLive hv sv label hsub hcert hsite hsupp ha htag hr
  have hJ := (follow_landing_charge v q d e hj).2
  refine ⟨hret,hl,?_,?_⟩
  · rw [hJ]; exact ht
  · rw [hJ,←liftedSite_succ]; exact hl.2.2.2.1

/-- The analogous same-mark adapter for an already protected old supplier. -/
theorem protected_step {p c n d : Nat} {initial : Config p c n} (hn : 4≤n)
    (v : Fin n) (group cert : List (Fin n))
    (q : Cursor p c n) (e a : Fin n)
    (hj : q.j=liftedSite v d) (hLive : Protected v (init q.ledger.config d))
    (hv : Valid q.ledger initial)
    (ha : a ∈ group) (hTag : q.ledger.slots q.j=some a)
    (hr : WindowLocal.route group cert (some a) q.ledger e=.keep) :
    let y := follow v d q.ledger.config e
    (e=liftedSite v d → retirement q.ledger.config e=false) ∧
      Protected v y ∧ (tick q e).ledger.slots (tick q e).j=some a ∧
      ((tick q e).ledger.config (rightNeighbor (tick q e).j)).leader=false := by
  have htag : q.ledger.slots (liftedSite v d)=some a := by simpa only [←hj] using hTag
  obtain ⟨hret,hl,ht⟩ := WindowScopedRoute.follow_of_keep hn
    v group cert q.ledger e a hLive hv ha htag hr
  have hJ := (follow_landing_charge v q d e hj).2
  refine ⟨hret,hl,?_,?_⟩
  · rw [hJ]; exact ht
  · rw [hJ,←liftedSite_succ]; exact hl.1.2.2.2.1

/-- The local supplier has either an ordinary certified predecessor
or the authenticated protected corridor. Neither form filters raw marks. -/
def Supplier {p c n : Nat} (v : Fin n) (cert : List (Fin n))
    (s : State p c n) : Prop :=
  Live v (init s.cursor.ledger.config s.donor) ∧
    ((∃ sv label, rightNeighbor sv=v ∧ label∈cert ∧
      WindowLocal.TaggedLeader s.cursor.ledger sv label) ∨
      Protected v (init s.cursor.ledger.config s.donor))

structure ValidCut {p c n : Nat} (initial : Config p c n) (v : Fin n)
    (cert : List (Fin n)) (a b k : Fin n) (s : State p c n) : Prop where
  valid : Valid s.cursor.ledger initial
  geometry : Geometry s.cursor.ledger s.cursor.j s.cursor.w s.cursor.k a b k
    s.cursor.index s.cursor.width
  lift : s.cursor.j=liftedSite v s.donor
  supplier : Supplier v cert s

theorem kept_route {p c n : Nat} (v : Fin n) (g cert : List (Fin n))
    (a : Fin n) (s : State p c n) (e : Fin n)
    (h : (next v g cert a s e).terminal=false) :
    WindowLocal.route g cert (some a) s.cursor.ledger e=.keep := by
  have H : (s.terminal || decide (WindowLocal.route g cert (some a) s.cursor.ledger e ≠ .keep))=false := h
  exact Classical.byContradiction (fun H' => by simp [H'] at H)

theorem cut_step_on_keep {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (v : Fin n) (g cert : List (Fin n)) (a b k : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hsub : cert ⊆ g)
    (s : State p c n) (e : Fin n) (hc : ValidCut initial v cert a b k s)
    (hr : WindowLocal.route g cert (some a) s.cursor.ledger e=.keep) :
    ValidCut initial v cert a b k (next v g cert a s e) ∧
    (e=liftedSite v s.donor → retirement s.cursor.ledger.config e=false) ∧
    ((tick s.cursor e).ledger.config (rightNeighbor (tick s.cursor e).j)).leader=false := by
  let q := s.cursor
  have hv := hc.valid
  have hgeo := hc.geometry
  have hstep := geom_step hn q.ledger g e q.j q.w q.k a b k q.index q.width hgeo
    hv.markCover hv.covers ha hb hk (route_noloss g cert a q e hr)
  have hlift := (follow_landing_charge v q s.donor e hc.lift).2
  have hvalid := valid_step hn q.ledger initial e hv
  obtain ⟨hlive, hS | hP⟩ := hc.supplier
  · obtain ⟨sv,label,hsite,hlabel,hS⟩ := hS
    obtain ⟨hret,hL,_ht,hghost⟩ :=
      ordinary_step hn v g cert q e a sv label hc.lift hlive hv hsub hlabel hsite hS ha hgeo.jTag hr
    have hs := WindowLocal.certified_stationary_of_keep hn initial q.ledger g cert (some a)
      e sv label hv hsub hlabel hS hr
    exact ⟨⟨hvalid,hstep,hlift,⟨hL,.inl ⟨sv,label,hsite,hlabel,hs⟩⟩⟩,hret,hghost⟩
  · obtain ⟨hret,hP',_ht,hghost⟩ := protected_step hn v g cert q e a hc.lift hP hv ha hgeo.jTag hr
    exact ⟨⟨hvalid,hstep,hlift,⟨hP'.1,.inr hP'⟩⟩,hret,hghost⟩

theorem physical_retained_count {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (v : Fin n) (g cert : List (Fin n)) (a b k : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hsub : cert ⊆ g)
    (s : State p c n) (h : ValidCut initial v cert a b k s)
    (w : List (Fin n)) (hw : (runMarks (next v g cert a) s w).terminal=false) :
    RetainedKeep g s.cursor w ∧
      (runMarks (next v g cert a) s w).donor = s.donor+totalJ s.cursor w ∧
      ValidCut initial v cert a b k (runMarks (next v g cert a) s w) := by
  apply retained_count v g cert a (ValidCut initial v cert a b k)
    (fun _ H _ => H.lift) _ s w h hw
  intro y e hy he
  obtain ⟨hnext,_hret,hghost⟩ :=
    cut_step_on_keep hn v g cert a b k ha hb hk hsub y e hy (kept_route v g cert a y e he)
  exact ⟨hnext,hghost⟩

def append {n : Nat} (u : List (Fin n)) (e : Fin n) := u++[e]

theorem append_run {n : Nat} (u w : List (Fin n)) :
    runMarks append u w=u++w := by
  induction w generalizing u with
  | nil => simp [runMarks]
  | cons e w ih => simpa [runMarks,append,List.append_assoc] using ih (u++[e])

/-- Same-word push clock from a genuine geometric supplier cut.  This
does not construct the initial cut from the previous transaction's exit. -/
theorem push_mean {p c n : Nat} {initial : Config p c n}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (v : Fin n) (g cert : List (Fin n)) (a b k : Fin n)
    (ha : a∈g) (hb : b∈g) (hk : k∈g) (hab : a≠b) (hsub : cert ⊆ g)
    (s : State p c n) (h : ValidCut initial v cert a b k s)
    (hQ : QuietEntrance s.cursor.ledger.config)
    (b₀ c₀ : Nat) (hi : s.cursor.index+1=b₀) (hw : s.cursor.width+1=b₀+c₀) :
    let m := min (n-2) (max 2 (s.donor+(2*b₀+c₀+1)))
    IIDExpectedHittingTimeAtMost (next v g cert a) (fun y => y.terminal=true) s
      (4*n*(2*(2*b₀+c₀+1)+m+1)) := by
  let nstep : State p c n → Fin n → State p c n := next v g cert a
  let m := min (n-2) (max 2 (s.donor+(2*b₀+c₀+1)))
  let pstate := runMarks nstep s
  let cfg := fun u => (pstate u).cursor.ledger.config
  let donor := fun u => (pstate u).donor
  let done := fun u => (pstate u).terminal=true
  have hstep (u : List (Fin n)) (e : Fin n) : pstate (append u e)=nstep (pstate u) e := by
    simp [pstate,append,runMarks_append,runMarks]
  have hfalse (u : List (Fin n)) (hu : ¬done u) : (pstate u).terminal=false := by
    cases hb : (pstate u).terminal
    · rfl
    · exact False.elim (hu hb)
  have hJ : (s.cursor.ledger.config (rightNeighbor s.cursor.j)).leader=false := by
    rw [h.lift,←liftedSite_succ]
    exact h.supplier.1.2.2.2.1
  have hh (u : List (Fin n)) (hu : ¬done u) :=
    physical_retained_count hn v g cert a b k ha hb hk hsub s h u (hfalse u hu)
  have V : WindowFourHeadShadow.View cfg donor append done v s.donor m := by
    constructor
    · intro u e hu
      change (pstate (append u e)).terminal=true
      rw [hstep]
      exact stop_sticky v g cert a (pstate u) e hu
    · intro u hu
      obtain ⟨hkeep, hd, hvalid⟩ := hh u hu
      have H := four_head_payments hp hc hn g a b k ha hb hk hab s.cursor u hkeep
        h.valid hQ h.geometry hJ b₀ c₀ hi hw
      have hn' : donor u+1<n := hvalid.supplier.1.2.2.2.2.2
      change donor u=s.donor+totalJ s.cursor u at hd
      exact ⟨by omega, Nat.le_min.mpr ⟨by omega,by omega⟩⟩
    · intro u hu
      exact (hh u hu).2.2.supplier.1
    · intro u e he
      have hen := hfalse (append u e) he
      rw [hstep] at hen
      have hu : ¬done u := fun hu => by
        rw [stop_sticky v g cert a (pstate u) e hu] at hen
        contradiction
      have H := cut_step_on_keep hn v g cert a b k ha hb hk hsub (pstate u) e
        (hh u hu).2.2 (kept_route v g cert a (pstate u) e hen)
      refine ⟨H.2.1,H.1.supplier.1,?_,?_⟩
      · change (pstate (append u e)).cursor.ledger.config=_
        rw [hstep]
        rfl
      · change (pstate (append u e)).donor=_
        rw [hstep]
        rfl
  have hm : 2≤m := Nat.le_min.mpr ⟨by omega,Nat.le_max_left _ _⟩
  have hm' : m≤n-2 := Nat.min_le_left _ _
  have aux := WindowFourHeadShadow.mean_of_count hp hc hn hm hm' v cfg donor append done V
    [] s.cursor g a b k ha hb hk hab h.valid hQ h.geometry hJ b₀ c₀ hi hw
    (by
      intro w hdone
      have he : runMarks append ([] : List (Fin n)) w=w := by simp [append_run]
      rw [he] at hdone ⊢
      obtain ⟨hkeep,hd,_⟩ := hh w hdone
      change donor w = s.donor+totalJ s.cursor w at hd
      exact ⟨hkeep,by rw [hd]; omega⟩)
  change IIDExpectedHittingTimeAtMost nstep (fun y => y.terminal=true) s (4*n*(2*(2*b₀+c₀+1)+m+1))
  intro t
  exact Nat.le_trans (EntranceCover.iidHitCost_le_of_projection nstep append (fun y => y.terminal=true)
    done pstate hstep (fun _ hh => hh) t []) (aux t)

end L4.WindowA0Push
