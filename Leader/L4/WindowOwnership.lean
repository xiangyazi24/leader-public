import Leader.L4.WindowNamedFront
import Leader.L4.WindowPushEntry
import Leader.L4.WindowA0Route

/-! Original certified IDs, not physical leader counts, are the ownership
witnesses passed through ordinary G7 transactions. -/
namespace L4.WindowOwnership
open SevenTagCharge WindowLocal

structure Owners {p c n} (z : Ledger p c n) (g cert : List (Fin n)) where
  contained : cert ⊆ g
  slot : Fin n → Fin n
  live : ∀ a, a∈cert → TaggedLeader z (slot a) a

def Owners.onKeep {p c n} {z0 : Config p c n}
    {z : Ledger p c n} {g cert : List (Fin n)} (h : Owners z g cert)
    (hn : 4≤n) (hv : Valid z z0) (target : Option (Fin n)) (e : Fin n)
    (hk : route g cert target z e=.keep) : Owners (advance z e) g cert :=
  ⟨h.contained,h.slot,fun a ha =>
    certified_stationary_of_keep hn z0 z g cert target e (h.slot a) a hv
      h.contained ha (h.live a ha) hk⟩

/-- A target birth detects the true old ghost; the original ID still
occupies its old slot on the birth mark. -/
theorem birth_inv {p c n} (z : Ledger p c n)
    (g cert : List (Fin n)) (target : Option (Fin n)) (e a site : Fin n)
    (h : route g cert target z e=.targetBirth a site) :
    selectedGroupLoss g z e=none ∧ z.slots e=some a ∧ target=some a ∧
      birthAt z.config e=true ∧ site=rightNeighbor e := by
  unfold route at h
  cases hl : selectedGroupLoss g z e with
  | some g => simp [hl] at h
  | none =>
    simp only [hl] at h
    cases hs : z.slots e with
    | none => simp [hs] at h
    | some id =>
      simp only [hs,routeKnown] at h
      split at h
      · cases h
      · split at h
        · rename_i hb
          obtain ⟨rfl,rfl⟩ := Event.targetBirth.inj h
          obtain ⟨ht,hB⟩ := Bool.and_eq_true_iff.mp hb
          exact ⟨rfl,rfl,beq_iff_eq.mp ht,hB,rfl⟩
        · cases h

/-- The designated new owner is attached on the same edge. All old
certified IDs keep their old slots, and this is not an existential
designation of any leader exposed later in that sector. -/
def Owners.onBirth {p c n} {z0 : Config p c n}
    {z : Ledger p c n} {g cert : List (Fin n)} (h : Owners z g cert)
    (hn : 4≤n) (hv : Valid z z0) (e a site : Fin n) (ha : a∈g)
    (hr : route g cert (some a) z e=.targetBirth a site) :
    Owners (advance z e) g (cert++[a]) := by
  obtain ⟨_,hs,_,hb,_⟩ := birth_inv z g cert (some a) e a site hr
  have born := (target_birth_result hn g cert z e a hv.markCover hv.sourceCover hs hb).2
  have noDeath : nativeDeath z.config e=false := by
    apply Bool.eq_false_iff.mpr
    intro hD
    have hTrue := ((nativeDeath_iff z.config e).mp hD).1
    have hFalse := (Bool.and_eq_true_iff.mp hb).1
    simp [hTrue] at hFalse
  refine ⟨?_,fun x => if x=a then e else h.slot x,?_⟩
  · intro b hmem
    rcases List.mem_append.mp hmem with hm|hm
    · exact h.contained hm
    · simpa using (List.mem_singleton.mp hm) ▸ ha
  · intro b hmem
    by_cases heq : b=a
    · subst b
      simpa only [if_true] using born
    · rcases List.mem_append.mp hmem with hm|hm
      · simp only [if_neg heq]
        obtain ⟨hh,hL⟩ := h.live b hm
        exact living_tag_stays hn z (h.slot b) e b hv.sourceCover hh hL (fun _ => noDeath)
      · exact (heq (List.mem_singleton.mp hm)).elim

/-- The same actual death edge preserves every other certified owner.
The victim is deliberately removed pending the protected latch. -/
def Owners.afterDeath {p c n} {z0 : Config p c n}
    {z : Ledger p c n} {g cert : List (Fin n)} (h : Owners z g cert)
    (hn : 4≤n) (hv : Valid z z0) (target : Option (Fin n)) (e a site : Fin n)
    (hr : route g cert target z e=.prefixDeath a site) :
    Owners (advance z e) g (cert.filter (· != a)) := by
  obtain ⟨_,hs,_,_⟩ := WindowNamedFront.death_inv z g cert target e a site hr
  refine ⟨fun b hb => h.contained (List.mem_filter.mp hb).1,h.slot,?_⟩
  intro b hb
  have hf := List.mem_filter.mp hb
  obtain ⟨hS,hL⟩ := h.live b hf.1
  apply living_tag_stays hn z (h.slot b) e b hv.sourceCover hS hL
  intro hEq
  have bad : b=a := by rw [hEq,hs] at hS; exact Option.some.inj hS.symm
  subst b
  simp at hf

/-- A certified consecutive slice of the original cyclic roster as
linearized at the start of the seven-root window.  The mode can never
substitute another living ID for the prescribed next original one. -/
structure Progress {p c n} (z : Ledger p c n) (g : List (Fin n)) where
  before : List (Fin n)
  cert : List (Fin n)
  after : List (Fin n)
  partition : g=before++cert++after
  owned : Owners z g cert
  positive : 0<cert.length
  bounded : cert.length≤3

def Progress.target {p c n} {z : Ledger p c n} {g : List (Fin n)}
    (P : Progress z g) : Option (Fin n) :=
  if P.cert.length<3 then P.after.head? else none

def Progress.onKeep {p c n} {z0 : Config p c n} {z : Ledger p c n} {g}
    (P : Progress z g) (hn : 4≤n) (hv : Valid z z0) (e : Fin n)
    (hr : route g P.cert P.target z e=.keep) :
    Progress (advance z e) g :=
  ⟨P.before,P.cert,P.after,P.partition,P.owned.onKeep hn hv P.target e hr,
    P.positive,P.bounded⟩

theorem Progress.target_head {p c n} {z : Ledger p c n} {g}
    (P : Progress z g) (a : Fin n) (h : P.target=some a) :
    P.cert.length<3 ∧ ∃ rest, P.after=a::rest := by
  unfold target at h
  split at h
  · rename_i H
    refine ⟨H,?_⟩
    cases hx : P.after with
    | nil => simp [hx] at h
    | cons b rest =>
      simp only [hx,List.head?_cons,Option.some.injEq] at h
      exact ⟨rest,by rw [h]⟩
  · contradiction

def Progress.extend {p c n} {z0 : Config p c n} {z : Ledger p c n} {g}
    (P : Progress z g) (hn : 4≤n) (hv : Valid z z0) (e a pos : Fin n)
    (hr : route g P.cert P.target z e=.targetBirth a pos) :
    Progress (advance z e) g := by
  have ht := (birth_inv z g P.cert P.target e a pos hr).2.2.1
  have advanceOwned (rest : List (Fin n)) (restEq : P.after=a::rest)
      (hBound : P.cert.length<3) : Progress (advance z e) g := by
    have hg : a∈g := by simp [P.partition,restEq]
    have own := P.owned.onBirth hn hv e a pos hg (by simpa only [ht] using hr)
    refine ⟨P.before,P.cert++[a],rest,?_,own,?_,?_⟩
    · simp [P.partition,restEq,List.append_assoc]
    · simp
    · simp; omega
  cases hA : P.after with
  | nil =>
    unfold Progress.target at ht
    simp [hA] at ht
  | cons b rest =>
    obtain ⟨hBound,_⟩ := P.target_head a ht
    have heq : b=a := by
      simpa [Progress.target,hBound,hA] using ht
    subst b
    exact advanceOwned rest hA hBound

/-- Attach an already living designated next original tag with no
physical step and no change in its ledger. -/
def Progress.attachLiving {p c n} {z : Ledger p c n} {g}
    (P : Progress z g) (a e : Fin n) (after : List (Fin n))
    (hA : P.after=a::after) (hB : P.cert.length<3)
    (hl : TaggedLeader z e a) : Progress z g := by
  refine ⟨P.before,P.cert++[a],after,?_,?_,by simp,by simp; omega⟩
  · simp [P.partition,hA,List.append_assoc]
  · have hg : a∈g := by simp [P.partition,hA]
    refine ⟨?_,fun b => if b=a then e else P.owned.slot b,?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with ho|hn
      · exact P.owned.contained ho
      · exact (List.mem_singleton.mp hn).symm ▸ hg
    · intro b hb
      by_cases hEq : b=a
      · subst b
        simpa only [if_true] using hl
      · rcases List.mem_append.mp hb with ho|hn
        · simpa only [if_neg hEq] using P.owned.live b ho
        · exact (hEq (List.mem_singleton.mp hn)).elim

noncomputable def Progress.skipOnce {p c n} {z : Ledger p c n} {g}
    (P : Progress z g) : Option (Progress z g) := by
  classical
  exact if hB : P.cert.length<3 then
    match hA : P.after with
    | [] => none
    | a::after => if hl : ∃ e, TaggedLeader z e a then
        some (P.attachLiving a (Classical.choose hl) after hA hB (Classical.choose_spec hl))
      else none
  else none

/-- At most two immediate tests can extend a nonempty certified
slice before the triple; both skips preserve the exact raw prefix. -/
noncomputable def Progress.normalize {p c n} {z : Ledger p c n} {g}
    (P : Progress z g) : Progress z g :=
  match P.skipOnce with
  | none => P
  | some R => R.skipOnce.getD R

/-- Existing A0 entry can create a singleton from either permitted
original candidate. This packages the exact same ledger of the birth,
with the relevant roster split still required from that entry cut. -/
def initialBirth {p c n} {z0 : Config p c n} {z : Ledger p c n}
    (hn : 4≤n) (hv : Valid z z0) (g before after : List (Fin n)) (e a : Fin n)
    (shape : g=before++[a]++after) (hs : z.slots e=some a)
    (hb : birthAt z.config e=true) : Progress (advance z e) g :=
  ⟨before,[a],after,shape,
    ⟨by intro b hB; simp only [List.mem_singleton] at hB; subst b; simp [shape],
      fun _ => e,by
        intro b hB
        have he : b=a := List.mem_singleton.mp hB
        subst b
        exact (target_birth_result hn g [] z e a hv.markCover hv.sourceCover hs hb).2⟩,
    by simp,by simp⟩

/-- Entry-phase two-target route inversion. No death branch is introduced
by either empty certified-list lookup. -/
theorem two_birth_inv {p c n} (z : Ledger p c n) (g : List (Fin n))
    (a b e victim pos : Fin n)
    (h : WindowA0Route.routeTwo g a b z e=.targetBirth victim pos) :
    (victim=a ∨ victim=b) ∧ z.slots e=some victim ∧ birthAt z.config e=true ∧
      pos=rightNeighbor e := by
  unfold WindowA0Route.routeTwo at h
  dsimp only at h
  split at h
  · obtain ⟨_,hs,ht,hB,hP⟩ := birth_inv z g [] (some b) e victim pos h
    exact ⟨.inr (Option.some.inj ht).symm,hs,hB,hP⟩
  · obtain ⟨_,hs,ht,hB,hP⟩ := birth_inv z g [] (some a) e victim pos h
    exact ⟨.inl (Option.some.inj ht).symm,hs,hB,hP⟩

structure EntryScope {n} (g : List (Fin n)) where
  first : Fin n
  second : Fin n
  firstBefore : List (Fin n)
  firstAfter : List (Fin n)
  secondBefore : List (Fin n)
  secondAfter : List (Fin n)
  firstShape : g=firstBefore++[first]++firstAfter
  secondShape : g=secondBefore++[second]++secondAfter

def initialLiving {p c n} {z : Ledger p c n} (g before after : List (Fin n))
    (a slot : Fin n) (shape : g=before++[a]++after) (hl : TaggedLeader z slot a) :
    Progress z g :=
  ⟨before,[a],after,shape,
    ⟨by intro b hm; have H := List.mem_singleton.mp hm; subst b; simp [shape],
      fun _ => slot,by intro b hm; have H := List.mem_singleton.mp hm; subst b; exact hl⟩,
    by simp,by simp⟩

/-- Ordered zero-time entry tests. The first candidate has priority;
the second is considered only if the first is not living. -/
noncomputable def startMode {p c n} {z : Ledger p c n} {g : List (Fin n)}
    (A : EntryScope g) : Option (Progress z g) := by
  classical
  exact if h₁ : ∃ s, TaggedLeader z s A.first then
    some (initialLiving g A.firstBefore A.firstAfter A.first (Classical.choose h₁)
      A.firstShape (Classical.choose_spec h₁))
  else if h₂ : ∃ s, TaggedLeader z s A.second then
    some (initialLiving g A.secondBefore A.secondAfter A.second (Classical.choose h₂)
      A.secondShape (Classical.choose_spec h₂))
  else none

theorem startMode_none {p c n} {z : Ledger p c n} {g : List (Fin n)} (A : EntryScope g) :
    startMode (z:=z) A=none ↔
      (¬∃ s, TaggedLeader z s A.first) ∧ (¬∃ s, TaggedLeader z s A.second) := by
  classical
  unfold startMode
  split
  · rename_i h
    simp [h]
  · rename_i h
    split <;> simp_all

/-- Entry can report a two-target birth, but it never reports a
certified death because each component has empty certification. -/
theorem no_entry_death {p c n} (z : Ledger p c n) (g : List (Fin n))
    (a b e v l : Fin n) :
    WindowA0Route.routeTwo g a b z e≠.prefixDeath v l := by
  intro h
  unfold WindowA0Route.routeTwo at h
  dsimp only at h
  split at h
  · have H := (WindowNamedFront.death_inv z g [] (some b) e v l h).2.2.1
    cases H
  · have H := (WindowNamedFront.death_inv z g [] (some a) e v l h).2.2.1
    cases H

def EntryScope.handoff {p c n} {z : Ledger p c n} {z0 : Config p c n} {g}
    (A : EntryScope g) (hn : 4≤n) (hv : Valid z z0) (e a site : Fin n)
    (h : WindowA0Route.routeTwo g A.first A.second z e=.targetBirth a site) :
    Progress (advance z e) g := by
  obtain ⟨_,hs,hb,_⟩ := two_birth_inv z g A.first A.second e a site h
  by_cases first : a=A.first
  · exact initialBirth hn hv g A.firstBefore A.firstAfter e a (first.symm ▸ A.firstShape) hs hb
  · have second := (two_birth_inv z g A.first A.second e a site h).1.resolve_left first
    exact initialBirth hn hv g A.secondBefore A.secondAfter e a (second.symm ▸ A.secondShape) hs hb

/-- Exact front states: entry, one/two/three certified original IDs,
or sticky selected loss (the protected phase is the right injection). -/
inductive Mode {p c n} (z : Ledger p c n) (g : List (Fin n)) where
  | entry (A : EntryScope g)
  | owned (P : Progress z g)
  | reward (a : Fin n) (certifiedLoss : a∈z.losses ∧ a∈g)

structure Front {p c n} (z0 : Config p c n) (g : List (Fin n)) where
  ledger : Ledger p c n
  valid : Valid ledger z0
  quiet : QuietEntrance ledger.config
  mode : Mode ledger g

noncomputable def Front.initial {p c n} (z : Config p c n) (h : QuietEntrance z)
    {g : List (Fin n)} (A : EntryScope g) : Front z g :=
  ⟨SevenTagCharge.initial z,valid_init z h.1 h.2.1,h,
    match startMode (z:=SevenTagCharge.initial z) A with
    | none => .entry A
    | some P => .owned P.normalize⟩

private theorem loss_of_route {p c n} (z : Ledger p c n)
    (g cert : List (Fin n)) (target : Option (Fin n)) (e a : Fin n)
    (hr : route g cert target z e=.reward a) :
    a∈(advance z e).losses ∧ a∈g := by
  obtain ⟨hh,hg⟩ := (reward_iff g cert target z e a).mp hr
  exact ⟨List.mem_append_left _ (by simp [hh]),hg⟩

private theorem entry_reward {p c n} (z : Ledger p c n) (g : List (Fin n))
    (i j e a : Fin n) (hr : WindowA0Route.routeTwo g i j z e=.reward a) :
    a∈(advance z e).losses ∧ a∈g := by
  unfold WindowA0Route.routeTwo at hr
  dsimp only at hr
  split at hr
  · exact loss_of_route z g [] (some j) e a hr
  · exact loss_of_route z g [] (some i) e a hr

noncomputable def decide {p c n} {z0 : Config p c n} {g : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (s : Front z0 g) (e : Fin n) :
    WindowLatch.Decision z0 g Front.ledger s e :=
  let y := advance s.ledger e
  let normal (m : Mode y g) : WindowLatch.Decision z0 g Front.ledger s e :=
    .ordinary ⟨y,valid_step hn s.ledger z0 e s.valid,
      RootedFresh.quiet_step s.ledger.config e hp hc hn s.quiet,m⟩ rfl
  match s.mode with
  | .reward a loss => normal (.reward a
      ⟨List.mem_append_right _ loss.1,loss.2⟩)
  | .entry A =>
    match hr : WindowA0Route.routeTwo g A.first A.second s.ledger e with
    | .keep => normal (.entry A)
    | .reward a => normal (.reward a (entry_reward s.ledger g A.first A.second e a hr))
    | .targetBirth a loc => normal (.owned (A.handoff hn s.valid e a loc hr).normalize)
    | .prefixDeath a loc => (no_entry_death s.ledger g A.first A.second e a loc hr).elim
  | .owned P =>
    match hr : route g P.cert P.target s.ledger e with
    | .keep => normal (.owned (P.onKeep hn s.valid e hr))
    | .reward a => normal (.reward a (loss_of_route s.ledger g P.cert P.target e a hr))
    | .targetBirth a loc => normal (.owned (P.extend hn s.valid e a loc hr).normalize)
    | .prefixDeath a loc =>
      .kill (Classical.choice (WindowNamedFront.named_of_route hn s.ledger g P.cert P.target
        e a loc s.valid s.quiet P.owned.contained hr)).val

/-- This is the exact fold to use for both the slot cut and bad mass.
Every raw suffix, including right-injected padding, uses physical
advance on the original initial ledger. -/
noncomputable def fold {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (h : QuietEntrance x)
    {g : List (Fin n)} (A : EntryScope g) (w : List (Fin n)) :
    WindowLatch.Cursor (Front x g) x g :=
  WindowLatch.replay
    (WindowProtectedOuter.joinedNext (WindowLatch.front hn (decide hp hc hn)))
    (.inl (Front.initial x h A)) w

theorem fold_ledger {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (h : QuietEntrance x)
    {g : List (Fin n)} (A : EntryScope g) (w : List (Fin n)) :
    WindowLatch.project Front.ledger (fold hp hc hn h A w)=observe (initial x) w :=
  WindowLatch.replay_projects hn (decide hp hc hn) (.inl (Front.initial x h A)) w

open Classical in
theorem fold_fresh_mass {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (h : QuietEntrance x) {g : List (Fin n)} (A : EntryScope g) (t : Nat) :
    1000*RankRenewal.endpointSum RootedAssembly.wordNext
      (fun w => if WindowProtectedOuter.bad (fold hp hc hn h A w) then 1 else 0) t []≤11*n^t :=
  WindowLatch.fresh_mass hn hc (decide hp hc hn) (Front.initial x h A) t

end L4.WindowOwnership
