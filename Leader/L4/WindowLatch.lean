import Leader.L4.WindowFiveStages
import Leader.L4.WindowProtectedOuter

namespace L4.WindowLatch
open SevenTagCharge WindowProtectedOuter WindowFiveStages

structure Named {p c n : Nat} (z0 : Config p c n) (group : List (Fin n))
    (z : Ledger p c n) (e : Fin n) where
  cert : List (Fin n)
  target : Option (Fin n)
  shooter : Fin n
  victim : Fin n
  post : Fin n
  oldDonor : Nat
  valid : Valid z z0
  quiet : QuietEntrance z.config
  subset : cert ⊆ group
  victimCertified : victim ∈ cert
  victimAt : z.slots e=some victim
  route : WindowLocal.route group cert target z e=.prefixDeath victim post
  native : WindowLocal.nativeDeath z.config e=true
  shooterMark : (z.config shooter).mark=true
  shooterLiving : (z.config (rightNeighbor shooter)).leader=true
  killAt : e=liftedSite (rightNeighbor shooter) oldDonor
  noWrap : oldDonor+1<n
  openSector : ∀ i, i<oldDonor → (z.config (liftedSite (rightNeighbor shooter) i)).mark=false

def Named.entry {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    {z : Ledger p c n} {e : Fin n} (hn : 4≤n) (k : Named z0 group z e) :
    Entry z0 group :=
  ⟨rightNeighbor k.shooter,k.victim,
    k.oldDonor+(geometricPay (z.config e) (z.config (rightNeighbor e))).toNat,
    advance z e,k.subset k.victimCertified,
    (WindowProtectedEntry.named_kill_entry hn z group k.cert k.target
      k.shooter k.victim e k.post k.valid k.quiet k.subset k.victimCertified k.victimAt
      k.route k.native k.shooterMark k.shooterLiving k.killAt k.noWrap k.openSector).1⟩

theorem Named.post_eq {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    {z : Ledger p c n} {e : Fin n} (hn : 4≤n) (k : Named z0 group z e) :
    k.post=liftedSite (k.entry hn).supplier ((k.entry hn).donor+1) :=
  (WindowProtectedEntry.named_kill_entry hn z group k.cert k.target
    k.shooter k.victim e k.post k.valid k.quiet k.subset k.victimCertified k.victimAt
    k.route k.native k.shooterMark k.shooterLiving k.killAt k.noWrap k.openSector).2

inductive Decision {α : Type} {p c n : Nat} (z0 : Config p c n)
    (group : List (Fin n)) (ledger : α → Ledger p c n) (s : α) (e : Fin n) where
  | ordinary (s' : α) (advance_eq : ledger s'=advance (ledger s) e)
  | kill (k : Named z0 group (ledger s) e)

def front {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n)
    (decideEdge : ∀ s e, Decision z0 group ledger s e) (s : α) (e : Fin n) :
    Sum α (Entry z0 group) :=
  match decideEdge s e with
  | .ordinary s' _ => .inl s'
  | .kill k => .inr (k.entry hn)

abbrev Cursor (α : Type) {p c n} (z0 : Config p c n) (group : List (Fin n)) :=
  Sum α (Running z0 group)

def project {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    (ledger : α → Ledger p c n) : Cursor α z0 group → Ledger p c n
  | .inl s => ledger s
  | .inr r => r.q.ledger

theorem step_projects {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n)
    (F : ∀ s e, Decision z0 group ledger s e) (q : Cursor α z0 group) (e : Fin n) :
    project ledger (joinedNext (front hn F) q e)=advance (project ledger q) e := by
  cases q with
  | inl s =>
    cases h : F s e with
    | ordinary t ht => simpa [joinedNext,front,h,project] using ht
    | kill k => simp [joinedNext,front,h,project,startRunning,Named.entry,WindowProtectedMass.initial]
  | inr r =>
    change (pushNext r e).q.ledger=advance r.q.ledger e
    unfold pushNext WindowProtectedMass.next
    dsimp only
    split
    · rfl
    · split <;> rfl

def replay {α : Type} {n : Nat} (next : α → Fin n → α) : α → Word n → α
  | x, [] => x
  | x, e::u => replay next (next x e) u

theorem replay_append {α : Type} {n} (next : α → Fin n → α)
    (s : α) (w u : Word n) :
    replay next s (w++u)=replay next (replay next s w) u := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => exact ih (next s e)

theorem replay_projects {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n)
    (F : ∀ s e, Decision z0 group ledger s e) (q : Cursor α z0 group) (w : Word n) :
    project ledger (replay (joinedNext (front hn F)) q w)=observe (project ledger q) w := by
  induction w generalizing q with
  | nil => rfl
  | cons e w ih =>
    change project ledger (replay (joinedNext (front hn F)) (joinedNext (front hn F) q e) w)
      = observe (advance (project ledger q) e) w
    rw [ih,step_projects]

def HasLatch {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    (next : Cursor α z0 group → Fin n → Cursor α z0 group)
    (start : α) (w : Word n) (k : Entry z0 group) : Prop :=
  ∃ r, replay next (.inl start) w=.inr r ∧ r.start=k

theorem follows_latch {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    (F : α → Fin n → Sum α (Entry z0 group)) (s : Running z0 group) (u : Word n) :
    ∃ r, replay (joinedNext F) (.inr s) u=.inr r ∧ r.start=s.start := by
  induction u generalizing s with
  | nil => exact ⟨s,rfl,rfl⟩
  | cons e u ih => exact ih (pushNext s e)

theorem latch_at_kill {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n)
    (F : ∀ s e, Decision z0 group ledger s e) (start s : α)
    (w u : Word n) (e : Fin n) (k : Named z0 group (ledger s) e)
    (pre : replay (joinedNext (front hn F)) (.inl start) w=.inl s)
    (kill : F s e=.kill k) :
    HasLatch (joinedNext (front hn F)) start (w++e::u) (k.entry hn) := by
  unfold HasLatch
  rw [replay_append,pre]
  have edge : joinedNext (front hn F) (.inl s) e=.inr (startRunning (k.entry hn)) := by
    simp [joinedNext,front,kill]
  change ∃ r, replay _ (joinedNext (front hn F) (.inl s) e) u=.inr r ∧
    r.start=k.entry hn
  rw [edge]
  exact follows_latch (front hn F) (startRunning (k.entry hn)) u

theorem latch_unique {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {F : Cursor α z0 group → Fin n → Cursor α z0 group} {s : α} {w : Word n}
    {a b : Entry z0 group} (ha : HasLatch F s w a) (hb : HasLatch F s w b) : a=b := by
  obtain ⟨x,hx,xa⟩ := ha
  obtain ⟨y,hy,yb⟩ := hb
  have h := Sum.inr.inj (hx.symm.trans hy)
  exact xa.symm.trans ((congrArg Running.start h).trans yb)

/-- Conversely a right injection can only come from a routed kill
on one physical edge of the same raw word, not a later re-entry. -/
theorem latch_has_kill {α : Type} {p c n} {z0 : Config p c n}
    {group : List (Fin n)} {ledger : α → Ledger p c n}
    (hn : 4≤n) (F : ∀ s e, Decision z0 group ledger s e)
    (start : α) (w : Word n) (a : Entry z0 group)
    (h : HasLatch (joinedNext (front hn F)) start w a) :
    ∃ pre post : Word n, ∃ e : Fin n, ∃ s : α,
      ∃ k : Named z0 group (ledger s) e,
      w=pre++e::post ∧
      replay (joinedNext (front hn F)) (.inl start) pre=.inl s ∧
      F s e=.kill k ∧ a=k.entry hn := by
  induction w generalizing start with
  | nil =>
    obtain ⟨r,h,_⟩ := h
    cases h
  | cons e w ih =>
    cases hD : F start e with
    | ordinary t ht =>
      have hstep : joinedNext (front hn F) (.inl start) e=.inl t := by
        simp [joinedNext,front,hD]
      have h' : HasLatch (joinedNext (front hn F)) t w a := by
        unfold HasLatch at *
        change (∃ r, replay _ (joinedNext (front hn F) (.inl start) e) w=.inr r ∧ r.start=a) at h
        rwa [hstep] at h
      obtain ⟨pre,post,f,s,k,hw,hpre,hkill,hentry⟩ := ih t h'
      refine ⟨e::pre,post,f,s,k,by simp [hw],?_,hkill,hentry⟩
      change replay _ (joinedNext (front hn F) (.inl start) e) pre=.inl s
      rwa [hstep]
    | kill k =>
      have hK := latch_at_kill hn F start start [] w e k rfl hD
      exact ⟨[],w,e,start,k,rfl,rfl,hD,latch_unique h hK⟩

/-- Exact endpoint mass transport for a raw word append, not a union
bound over possible first kill times or identities. -/
theorem endpoint_replay {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (start : α) (t : Nat) (w : Word n) :
    RankRenewal.endpointSum RootedAssembly.wordNext
      (fun u => f (replay next start u)) t w =
    RankRenewal.endpointSum next f t (replay next start w) := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    simp only [RankRenewal.endpointSum]
    apply congrArg TaggedTail.sumEdge
    funext e
    rw [ih,RootedAssembly.wordNext,replay_append]
    rfl

noncomputable def freshBad {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n)
    (F : ∀ s e, Decision z0 group ledger s e) (start : α) (w : Word n) : Prop :=
  bad (replay (joinedNext (front hn F)) (.inl start) w)

/-- Allows defining the protected branch of the final slot and freshBad
using the very same replay. Any independently supplied slot witness at
this word must equal its unique right injection. -/
theorem slot_bad_same_latch {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n)
    (F : ∀ s e, Decision z0 group ledger s e) (start : α) (w : Word n)
    (r : Running z0 group)
    (h : replay (joinedNext (front hn F)) (.inl start) w=.inr r) :
    freshBad hn F start w ↔ WindowProtectedMass.failed r.q := by
  simp only [freshBad,h,bad]

open Classical in
theorem fresh_mass {α : Type} {p c n} {z0 : Config p c n} {group : List (Fin n)}
    {ledger : α → Ledger p c n} (hn : 4≤n) (hc : 12≤c)
    (F : ∀ s e, Decision z0 group ledger s e) (start : α) (t : Nat) :
    1000*RankRenewal.endpointSum RootedAssembly.wordNext
      (fun w => if freshBad hn F start w then 1 else 0) t []≤11*n^t := by
  change 1000*RankRenewal.endpointSum RootedAssembly.wordNext
    (fun w => (fun q : Cursor α z0 group => if bad q then 1 else 0)
      (replay (joinedNext (front hn F)) (.inl start) w)) t []≤11*n^t
  rw [endpoint_replay (joinedNext (front hn F))
    (fun q : Cursor α z0 group => if bad q then 1 else 0) (.inl start) t []]
  exact outer_failure_mass hn hc (front hn F) t start

end L4.WindowLatch
