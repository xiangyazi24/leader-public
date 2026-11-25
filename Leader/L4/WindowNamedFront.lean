import Leader.L4.WindowLatch

namespace L4.WindowNamedFront
open SevenTagCharge WindowLatch

/-- Invert the actual first-priority router; in particular a target
birth or selected loss cannot be used as a protected kill. -/
theorem death_inv {p c n} (z : Ledger p c n)
    (group cert : List (Fin n)) (target : Option (Fin n)) (e a post : Fin n)
    (h : WindowLocal.route group cert target z e=.prefixDeath a post) :
    WindowLocal.selectedGroupLoss group z e=none ∧ z.slots e=some a ∧
      a∈cert ∧ WindowLocal.nativeDeath z.config e=true := by
  unfold WindowLocal.route at h
  cases hl : WindowLocal.selectedGroupLoss group z e with
  | some g => simp [hl] at h
  | none =>
    simp only [hl] at h
    cases hs : z.slots e with
    | none => simp [hs] at h
    | some id =>
      simp only [hs,WindowLocal.routeKnown] at h
      split at h
      · rename_i hd
        have hei : id=a := (WindowLocal.Event.prefixDeath.inj h).1
        subst id
        have ⟨hD,hC⟩ := Bool.and_eq_true_iff.mp hd
        exact ⟨rfl,rfl,by simpa using hC,hD⟩
      · split at h <;> cases h

/-- A living root cannot be struck by its own fully wrapped live
byte on a quiet tape. The required quiet-ray witness says that at
the root its shield is set and its old signal is zero. -/
private theorem no_wrap_kill {p c n} (hn : 4≤n) (x : Config p c n)
    (s e : Fin n) (d : Nat) (hd : d<n) (he : liftedSite (rightNeighbor s) d=e)
    (hD : WindowLocal.nativeDeath x e=true)
    (hKind : (d=0 ∧ tagOverwrite (x e)=true) ∨
      ((x (rightNeighbor s)).shield=true ∧
        ∀ j, j≤d → (x (liftedSite (rightNeighbor s) j)).signal=.zero)) :
    d+1<n := by
  apply Classical.byContradiction
  intro hh
  have dN : d+1=n := by omega
  have r : rightNeighbor e=rightNeighbor s := by
    rw [←he,←liftedSite_succ,dN,liftedSite_full]
  rcases hKind with ⟨h0,_⟩ | ⟨hS,hSignals⟩
  · omega
  · have zero := hSignals 0 (Nat.zero_le _)
    rw [liftedSite_zero] at zero
    have native := (WindowLocal.nativeDeath_iff x e).mp hD
    have hL := native.1
    have hf := native.2.2
    rw [r] at hL hf
    simp [fireResponder,hL,zero,hS] at hf

/-- Recover an authenticated named kill from the old *physical* word
and an actual certified death. No caller-supplied shooter, gap or
post-cut location is assumed. No lower bound on current rank is required. -/
theorem named_of_route {p c n} {z0 : Config p c n} (hn : 4≤n)
    (z : Ledger p c n) (group cert : List (Fin n)) (target : Option (Fin n))
    (e a post : Fin n) (hv : Valid z z0) (hq : QuietEntrance z.config)
    (hc : cert ⊆ group)
    (hr : WindowLocal.route group cert target z e=.prefixDeath a post) :
    Nonempty { k : Named z0 group z e // k.victim=a ∧ k.post=post } := by
  obtain ⟨_,hslot,hcert,hdeath⟩ := death_inv z group cert target e a post hr
  obtain ⟨s,id,d,hid,hl,hd,he,hgap,hKind⟩ :=
    WindowLocal.killing_shooter_pre_mark hn z e hq hv.covers hdeath
  have hM : (z.config s).mark=true := by simpa [hid] using (hv.covers s).symm
  exact ⟨⟨⟨cert,target,s,a,post,d,hv,hq,hc,hcert,hslot,hr,hdeath,hM,hl,he.symm,
    no_wrap_kill hn z.config s e d hd he hdeath hKind,hgap⟩,rfl,rfl⟩⟩

/-- The constructed left shooter agrees with the supplied original
predecessor cut when that cut is already known from a slot invariant. -/
theorem agrees_with_predecessor {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {z : Ledger p c n} {e : Fin n} (k : Named z0 group z e)
    (s : Fin n) (d : Nat) (hm : (z.config s).mark=true)
    (he : liftedSite (rightNeighbor s) d=e)
    (hg : ∀ j, j<d → (z.config (liftedSite (rightNeighbor s) j)).mark=false) :
    k.shooter=s ∧ k.oldDonor=d :=
  WindowLocal.nearest_shooting_root_unique z.config k.shooter s k.oldDonor d
    k.shooterMark hm (k.killAt.symm.trans he.symm) k.openSector hg

structure CertifiedScope {n} (g : List (Fin n)) where
  certified : List (Fin n)
  target : Option (Fin n)
  contained : certified ⊆ g

/-- Parameterizes only the ordinary five-stage mode update. The
kill dispatch and the raw ledger transition are not parameters. -/
structure FrontPolicy (α : Type) {p c n} (group : List (Fin n)) where
  routeAt : α → Option (CertifiedScope group)
  ordinary : α → Ledger p c n → WindowLocal.Event n → α

structure State (α : Type) {p c n} (z0 : Config p c n) where
  mode : α
  ledger : Ledger p c n
  valid : Valid ledger z0
  quiet : QuietEntrance ledger.config

def State.initial {α : Type} {p c n} (z0 : Config p c n)
    (hq : QuietEntrance z0) (a : α) : State α z0 :=
  ⟨a,SevenTagCharge.initial z0,valid_init z0 hq.1 hq.2.1,hq⟩

noncomputable def decision {α : Type} {p c n} {z0 : Config p c n}
    {group : List (Fin n)} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (P : FrontPolicy α (p:=p) (c:=c) group) (s : State α z0) (e : Fin n) :
    Decision z0 group State.ledger s e :=
  let ordinary (event : WindowLocal.Event n) : Decision z0 group State.ledger s e :=
    .ordinary ⟨P.ordinary s.mode (advance s.ledger e) event,advance s.ledger e,
      valid_step hn s.ledger z0 e s.valid,
      RootedFresh.quiet_step s.ledger.config e hp hc hn s.quiet⟩ rfl
  match P.routeAt s.mode with
  | none => ordinary .keep
  | some A =>
    match hr : WindowLocal.route group A.certified A.target s.ledger e with
    | .keep => ordinary .keep
    | .reward a => ordinary (.reward a)
    | .targetBirth a loc => ordinary (.targetBirth a loc)
    | .prefixDeath a loc =>
      .kill (Classical.choice (named_of_route hn s.ledger group A.certified
        A.target e a loc s.valid s.quiet A.contained hr)).val

/-- On the actual router death, the adapter chooses the right
injection automatically; capture both physical victim and post-site. -/
theorem chooses_kill {α : Type} {p c n} {z0 : Config p c n}
    {group : List (Fin n)} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (P : FrontPolicy α (p:=p) (c:=c) group) (s : State α z0) (e a loc : Fin n)
    (A : CertifiedScope group) (hs : P.routeAt s.mode=some A)
    (hr : WindowLocal.route group A.certified A.target s.ledger e=.prefixDeath a loc) :
    ∃ k : Named z0 group s.ledger e,
      decision hp hc hn P s e=.kill k ∧ k.victim=a ∧ k.post=loc := by
  let k := Classical.choice (named_of_route hn s.ledger group A.certified A.target
    e a loc s.valid s.quiet A.contained hr)
  refine ⟨k.val,?_, k.property⟩
  simp only [decision,hs,k]
  split
  · rename_i h; rw [hr] at h; contradiction
  · rename_i a h; rw [hr] at h; contradiction
  · rename_i a b h; rw [hr] at h; contradiction
  · rename_i a' loc' h
    have he := WindowLocal.Event.prefixDeath.inj (h.symm.trans hr)
    obtain ⟨rfl,rfl⟩ := he
    rfl

/-- Direct exact same-prefix bridge usable by a concrete five-slot
policy after its old-ledger route computation. -/
theorem policy_latch {α : Type} {p c n} {z0 : Config p c n}
    {group : List (Fin n)} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (P : FrontPolicy α (p:=p) (c:=c) group) (start s : State α z0)
    (w u : List (Fin n)) (e a loc : Fin n)
    (A : CertifiedScope group) (hs : P.routeAt s.mode=some A)
    (hr : WindowLocal.route group A.certified A.target s.ledger e=.prefixDeath a loc)
    (pre : replay (WindowProtectedOuter.joinedNext (front hn (decision hp hc hn P)))
      (.inl start) w=.inl s) :
    ∃ k : WindowProtectedOuter.Entry z0 group,
      HasLatch (WindowProtectedOuter.joinedNext (front hn (decision hp hc hn P))) start
        (w++e::u) k ∧ k.victim=a ∧ k.ledger=advance s.ledger e ∧
        loc=liftedSite k.supplier (k.donor+1) := by
  obtain ⟨k,hK,hA,hPost⟩ := chooses_kill hp hc hn P s e a loc A hs hr
  exact ⟨k.entry hn,latch_at_kill hn (decision hp hc hn P) start s w u e k pre hK,
    hA,rfl,hPost.symm.trans (k.post_eq hn)⟩

end L4.WindowNamedFront
