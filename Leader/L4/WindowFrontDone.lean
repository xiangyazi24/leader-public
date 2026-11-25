import Leader.L4.WindowOwnership

namespace L4.WindowFrontDone
open SevenTagCharge WindowOwnership WindowProtectedOuter WindowLatch

def done {p c n} {x : Config p c n} {g : List (Fin n)} :
    Cursor (Front x g) x g → Prop
  | .inl s => match s.mode with
    | .reward _ _ => True
    | _ => False
  | .inr r => r.q.terminal=true

/-- Minimal projected invariant: the protected live corridor is carried
only before termination; after termination the ledger records reward
unless this is the exceptional target birth. -/
def Inv {p c n} {x : Config p c n} {g : List (Fin n)} :
    Cursor (Front x g) x g → Prop
  | .inl _ => True
  | .inr r =>
    Valid r.q.ledger x ∧
    (r.q.terminal=false →
      RankSupplier.Protected r.start.supplier (RankSupplier.init r.q.ledger.config r.q.donor) ∧
      r.q.ledger.slots (liftedSite r.start.supplier r.q.donor)=some r.start.victim ∧
      r.q.ledger.slots (RearTrace.predecessor r.start.supplier)=
        r.start.ledger.slots (RearTrace.predecessor r.start.supplier)) ∧
    (r.q.terminal=true → ¬WindowProtectedMass.failed r.q →
      WindowLocal.rewarded g r.q.ledger)

theorem start_inv {p c n} {x : Config p c n} {g : List (Fin n)} (a : Entry x g) :
    Inv (.inr (startRunning a) : Cursor (Front x g) x g) := by
  exact ⟨a.auth.1,fun _ => ⟨a.auth.2.1,a.auth.2.2.1,rfl⟩,fun h => by cases h⟩

private theorem no_supplier_death {p c n} {x : Config p c n} {g : List (Fin n)}
    (hn : 4≤n) (r : Running x g) (e : Fin n) (hv : Valid r.q.ledger x)
    (hl : RankSupplier.Protected r.start.supplier
      (RankSupplier.init r.q.ledger.config r.q.donor))
    (he : e=RearTrace.predecessor r.start.supplier) :
    WindowLocal.nativeDeath r.q.ledger.config e=false := by
  have hr : rightNeighbor e=r.start.supplier := he ▸ RearTrace.right_predecessor _
  have hne : rightNeighbor e≠e := by
    intro h
    have E : liftedSite e 1=liftedSite e 0 := by rw [liftedSite_succ,liftedSite_zero,h]
    have := liftedSite_inj e (show 1<n by omega) (show 0<n by omega) E
    omega
  apply Bool.eq_false_iff.mpr
  intro h
  have K := (WindowLocal.nativeDeath_iff r.q.ledger.config e).mp h
  have dead := (TenureOrigins.covered_ring_leader_loss_iff _ e hne hv.sourceCover K.1).mpr K
  have live := (RankSupplier.protected_supplier_on_mark hn r.start.supplier e _ hl).1
  change (step r.q.ledger.config e r.start.supplier).leader=true at live
  rw [hr,live] at dead
  contradiction

private theorem supplier_death_impossible {p c n} {x : Config p c n} {g : List (Fin n)}
    (hn : 4≤n) (r : Running x g) (e a pos : Fin n)
    (hv : Valid r.q.ledger x)
    (hl : RankSupplier.Protected r.start.supplier
      (RankSupplier.init r.q.ledger.config r.q.donor))
    (same : r.q.ledger.slots (RearTrace.predecessor r.start.supplier)=
      r.start.ledger.slots (RearTrace.predecessor r.start.supplier))
    (hr : WindowLocal.route g (pushNext.someSupplier r.start) (some r.start.victim)
      r.q.ledger e=.prefixDeath a pos) : False := by
  obtain ⟨_,hs,hcert,hd⟩ := WindowNamedFront.death_inv r.q.ledger g _
    (some r.start.victim) e a pos hr
  have hOldSlot : r.start.ledger.slots (RearTrace.predecessor r.start.supplier)=some a := by
    simpa [pushNext.someSupplier,Option.mem_toList] using hcert
  have ee := hv.unique e (RearTrace.predecessor r.start.supplier) a hs
    (same.trans hOldSlot)
  rw [no_supplier_death hn r e hv hl ee] at hd
  contradiction

private theorem push_inv {p c n} {x : Config p c n} {g : List (Fin n)}
    (hn : 4≤n) (r : Running x g) (e : Fin n)
    (old : Inv (.inr r : Cursor (Front x g) x g)) :
    Inv (.inr (pushNext r e) : Cursor (Front x g) x g) := by
  obtain ⟨hv,hL,hDone⟩ := old
  let v := r.start.supplier
  let a := r.start.victim
  let cert := pushNext.someSupplier r.start
  let q := r.q
  have newValid := valid_step hn q.ledger x e hv
  have proj : (pushNext r e).q.ledger=advance q.ledger e :=
    WindowProtectedMass.project_step v g cert a q e
  cases ht : r.q.terminal with
  | true =>
    refine ⟨proj ▸ newValid,?_,?_⟩
    · simp [pushNext,WindowProtectedMass.next,ht]
    · intro _ hb
      have oldB : ¬WindowProtectedMass.failed r.q := by
        simpa [pushNext,WindowProtectedMass.next,ht,WindowProtectedMass.failed] using hb
      rw [proj]
      exact WindowLocal.rewarded_sticky g r.q.ledger e (hDone ht oldB)
  | false =>
    obtain ⟨hP,hs,same⟩ := hL ht
    cases he : WindowLocal.route g cert (some a) q.ledger e with
    | keep =>
      have H := WindowScopedRoute.follow_of_keep hn v g cert q.ledger e a hP hv r.start.inGroup hs he
      have same' : (advance q.ledger e).slots (RearTrace.predecessor v)=
          r.start.ledger.slots (RearTrace.predecessor v) := by
        let j := RearTrace.predecessor v
        have lr : (q.ledger.config (rightNeighbor j)).leader=true := by
          rw [RearTrace.right_predecessor]
          exact hP.1.2.2.1
        have marked := hv.markCover j (.inl lr)
        have cover := hv.covers j
        change (q.ledger.slots j).isSome = _ at cover
        cases hj : q.ledger.slots j with
        | none => simp [hj,marked] at cover
        | some b =>
          have hold := (WindowLocal.living_tag_stays hn q.ledger j e b hv.sourceCover hj lr
            (fun h => no_supplier_death hn r e hv hP h.symm)).1
          exact hold.trans (hj.symm.trans same)
      change _ ∧ _ ∧ _ 
      have hQ : (pushNext r e).q=WindowProtectedMass.next v g cert a q e := rfl
      simp only [hQ,WindowProtectedMass.next,show q.terminal=false from ht,
        Bool.false_eq_true,if_false,he]
      exact ⟨newValid,fun _ => ⟨H.2.1,H.2.2,same'⟩,fun hh => by cases hh⟩
    | reward b =>
      have hl := (WindowLocal.reward_iff g cert (some a) q.ledger e b).mp he
      have loss : WindowLocal.rewarded g (advance q.ledger e) :=
        ⟨b,List.mem_append_left _ (by simp [hl.1]),hl.2⟩
      have hQ : (pushNext r e).q=WindowProtectedMass.next v g cert a q e := rfl
      change _ ∧ _ ∧ _
      simp only [hQ,WindowProtectedMass.next,show q.terminal=false from ht,
        Bool.false_eq_true,if_false,he]
      refine And.intro newValid (And.intro ?_ ?_)
      · intro h; cases h
      · intro _ _; exact loss
    | prefixDeath b pos =>
      exact (supplier_death_impossible hn r e b pos hv hP same he).elim
    | targetBirth b pos =>
      have hQ : (pushNext r e).q=WindowProtectedMass.next v g cert a q e := rfl
      change _ ∧ _ ∧ _
      simp only [hQ,WindowProtectedMass.next,show q.terminal=false from ht,
        Bool.false_eq_true,if_false,he]
      refine And.intro newValid (And.intro ?_ ?_)
      · intro h; cases h
      · intro _ bad; exact (bad (by rfl)).elim

noncomputable abbrev next {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} :
    Cursor (Front x g) x g → Fin n → Cursor (Front x g) x g :=
  joinedNext (front hn (decide hp hc hn))

theorem inv_step {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} (q : Cursor (Front x g) x g)
    (e : Fin n) (h : Inv q) : Inv (next hp hc hn q e) := by
  cases q with
  | inl s =>
    cases he : decide hp hc hn s e with
    | ordinary t ht => simp [next,joinedNext,front,he,Inv]
    | kill k => simpa [next,joinedNext,front,he] using start_inv (k.entry hn)
  | inr r => exact push_inv hn r e h

theorem done_sticky {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} (q : Cursor (Front x g) x g)
    (e : Fin n) (h : done q) : done (next hp hc hn q e) := by
  cases q with
  | inl s =>
    cases hm : s.mode with
    | entry A => simp [done,hm] at h
    | owned P => simp [done,hm] at h
    | reward a loss =>
      simp [next,joinedNext,front,WindowOwnership.decide,hm,done]
  | inr r =>
    have hT : r.q.terminal=true := h
    change (pushNext r e).q.terminal=true
    simp [pushNext,WindowProtectedMass.next,hT]

theorem replay_inv {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} (q : Cursor (Front x g) x g)
    (u : List (Fin n)) (h : Inv q) :
    Inv (replay (next hp hc hn) q u) := by
  induction u generalizing q with
  | nil => exact h
  | cons e u ih => exact ih _ (inv_step hp hc hn q e h)

theorem cursor_cover {p c n} {x : Config p c n} {g : List (Fin n)}
    (q : Cursor (Front x g) x g) (h : Inv q) (hd : done q) (hb : ¬bad q) :
    WindowLocal.rewarded g (project Front.ledger q) := by
  cases q with
  | inl s =>
    cases hm : s.mode with
    | entry A => simp [done,hm] at hd
    | owned P => simp [done,hm] at hd
    | reward a loss => exact ⟨a,loss.1,loss.2⟩
  | inr r => exact h.2.2 hd hb

theorem fold_closed {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (h : QuietEntrance x)
    {g : List (Fin n)} (A : EntryScope g) (w : List (Fin n)) (e : Fin n) :
    done (fold hp hc hn h A w) → done (fold hp hc hn h A (RootedAssembly.wordNext w e)) := by
  intro hd
  unfold fold
  rw [RootedAssembly.wordNext,replay_append]
  exact done_sticky hp hc hn _ e hd

theorem fold_cover {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (h : QuietEntrance x)
    {g : List (Fin n)} (A : EntryScope g) (w : List (Fin n))
    (hd : done (fold hp hc hn h A w)) (hb : ¬bad (fold hp hc hn h A w)) :
    WindowFiveStages.LedgerReward x g w := by
  have hI : Inv (fold hp hc hn h A w) :=
    replay_inv hp hc hn (.inl (Front.initial x h A)) w trivial
  obtain ⟨a,hm,hg⟩ := cursor_cover _ hI hd hb
  rw [fold_ledger hp hc hn h A w] at hm
  exact List.any_eq_true.mpr ⟨a,hm,by simpa using hg⟩

#print axioms fold_cover
#print axioms fold_closed

end L4.WindowFrontDone
