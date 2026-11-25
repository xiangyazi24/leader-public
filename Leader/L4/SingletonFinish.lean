import Leader.L4.RootlessFIFO
import Leader.L4.FixedResidual
import Leader.L4.Absorb

/-! Rank-one completion on the literal scheduler. Stock draining is
unconditional. The residual certificate is explicitly the aliased
top/door, not the distinct-endpoint fixed-corridor theorem. -/
namespace L4.SingletonFinish
open RankRootless RankPhysical FixedResidual
open Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    TaggedTail.sumEdge f = f 0 + TaggedTail.sumEdge (fun j : Fin n => f j.succ) := by
  simp [TaggedTail.sumEdge, List.ofFn_succ]
private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e ≤ g e) :
    TaggedTail.sumEdge f ≤ TaggedTail.sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [sSucc f, sSucc g]; exact Nat.add_le_add (h 0) (ih (fun e => h e.succ))
private theorem sConst (n b : Nat) : TaggedTail.sumEdge (fun _ : Fin n => b) = n*b := by
  induction n with
  | zero => simp [TaggedTail.sumEdge]
  | succ n ih => rw [sSucc, ih, Nat.succ_mul,Nat.add_comm]
private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    TaggedTail.sumEdge (fun e => f e + g e) = TaggedTail.sumEdge f + TaggedTail.sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega
private theorem sEntry {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    f i ≤ TaggedTail.sumEdge f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [sSucc]
    refine Fin.cases (Nat.le_add_right ..) (fun j => ?_) i
    exact Nat.le_trans (ih (fun e => f e.succ) j) (Nat.le_add_left ..)

private theorem mark_positive {p c n : Nat} (x : Config p c n)
    (h : ∃ i, (x i).mark = true) : 1 ≤ RankPhysical.rank x := by
  obtain ⟨i,hi⟩ := h
  simpa [hi,RankPhysical.rank] using sEntry (fun j => (x j).mark.toNat) i

/-- The rank-one quiet class is preserved on each actual mark, even on
the first canonical birth. Nondivisibility is used for the lower rank. -/
theorem singleton_step {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hp : 2 ≤ p) (hc : 12 ≤ c) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hQ : QuietEntrance x) (hR : RankPhysical.rank x = 1) :
    QuietEntrance (step x e) ∧ RankPhysical.rank (step x e) = 1 := by
  have hq := quiet_step x e hp hc hn hnd hQ
  have hl := mark_positive _ hq.2.2.1
  have hu := rank_step_le hn x e hQ.1
  exact ⟨hq,by omega⟩

/-- Generic same-scheduler two-stage composition. No independence after
an unverified conditioning event: the suffix estimate is required
uniformly at each actual cut in the intermediate target. -/
theorem expected_then {α : Type} {n : Nat} (next : α → Fin n → α)
    (good cut goal : α → Prop) (closed : ∀ x e, good x → good (next x e))
    (small : ∀ x, goal x → cut x) (B : Nat)
    (suffix : ∀ x, good x → cut x → IIDExpectedHittingTimeAtMost next goal x B)
    (x : α) (hx : good x) (A : Nat)
    (precost : IIDExpectedHittingTimeAtMost next cut x A) :
    IIDExpectedHittingTimeAtMost next goal x (A+B) := by
  have bound : ∀ t x, good x →
      iidHitCost next goal t x ≤ iidHitCost next cut t x + B*n^t := by
    intro t
    induction t with
    | zero => intro y _; simp [iidHitCost]
    | succ t ih =>
      intro y hy
      by_cases hcut : cut y
      · rw [iidHitCost_of_target next cut y hcut,Nat.zero_add]
        exact suffix y hy hcut (t+1)
      · have hg : ¬ goal y := fun h => hcut (small y h)
        simp only [iidHitCost, hg, hcut, if_false]
        change n^(t+1) + TaggedTail.sumEdge (fun e => iidHitCost next goal t (next y e)) ≤
          n^(t+1) + TaggedTail.sumEdge (fun e => iidHitCost next cut t (next y e)) + B*n^(t+1)
        have h := sMono (fun e => ih (next y e) (closed y e hy))
        rw [sAdd,sConst] at h
        have E : n * (B*n^t) = B*n^(t+1) := by rw [Nat.pow_succ]; ac_rfl
        rw [E] at h
        omega
  intro t
  rw [Nat.add_mul]
  exact Nat.le_trans (bound t x hx) (Nat.add_le_add_right (precost t) _)

/-- Target for the rank-one suffix on the original physical transition. -/
def LivingSingleton {p c n : Nat} (x : Config p c n) : Prop :=
  QuietEntrance x ∧ RankPhysical.rank x = 1 ∧ ¬ NoLiving x

/-- Only missing timer ingredient: the full-circuit aliased route with no
stock and no leaders. In particular this is not the distinct-endpoint
`ConcreteFixedResidualClock`, which requires a shorter gap. -/
def ConcreteSingletonTimer : Prop :=
  ∀ {p c n : Nat} (x : Config p c n),
    2 ≤ p → 12 ≤ c → 4 ≤ n → (¬ p ∣ n) →
    QuietEntrance x → RankPhysical.rank x = 1 →
    NoLiving x → NoStock x →
    ∃ clock : Countdown step (fun y => ¬ NoLiving y) x,
      clock.budget [] ≤ 32 * (2*c+1) * (n+1)

private theorem goal_cost_eq {α : Type} {n : Nat} (next : α → Fin n → α)
    (good P Q : α → Prop) (closed : ∀ x e, good x → good (next x e))
    (eq : ∀ x, good x → (P x ↔ Q x)) (t : Nat) (x : α) (hx : good x) :
    iidHitCost next P t x = iidHitCost next Q t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hq : Q x
    · rw [iidHitCost_of_target next P x ((eq x hx).mpr hq),
          iidHitCost_of_target next Q x hq]
    · have hp : ¬ P x := fun h => hq ((eq x hx).mp h)
      simp only [iidHitCost,hp,hq,if_false]
      rw [show (fun e => iidHitCost next P t (next x e)) =
               (fun e => iidHitCost next Q t (next x e)) from
        funext (fun e => ih _ (closed x e hx))]

/-- Exact bounded mean interface on the zero-stock, leaderless singleton. -/
def ZeroStockMean : Prop :=
  ∀ {p c n : Nat} (x : Config p c n),
    2 ≤ p → 12 ≤ c → 4 ≤ n → (¬ p ∣ n) →
    QuietEntrance x → RankPhysical.rank x = 1 → NoLiving x → NoStock x →
    IIDExpectedHittingTimeAtMost step (fun y => ¬ NoLiving y) x
      (n*(32*(2*c+1)*(n+1)))

/-- From any quiet rank-one state, obtain a live quiet singleton by exact
IID composition of literal rootless drainage and the aliased timer.
Already-living singleton cuts require zero further marks. -/
theorem singleton_expected_of_zero_mean (timer : ZeroStockMean)
    {p c n : Nat} (x : Config p c n)
    (hp : 2 ≤ p) (hc : 12 ≤ c) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hQ : QuietEntrance x) (hR : RankPhysical.rank x = 1) :
    IIDExpectedHittingTimeAtMost step LivingSingleton x
      (17*n^2 + n*(32*(2*c+1)*(n+1))) := by
  let good := fun y : Config p c n => QuietEntrance y ∧ RankPhysical.rank y = 1
  have closed : ∀ y e, good y → good (step y e) := fun y e h =>
    singleton_step y e hp hc hn hnd h.1 h.2
  refine expected_then step good RootlessFIFO.DrainTarget LivingSingleton closed
    (fun y h => .inl h.2.2) _ ?_ x ⟨hQ,hR⟩ _
    (RootlessFIFO.rootless_drain_mean_of_mcov hn x hQ.1 hnd)
  intro y hy cut
  by_cases hl : NoLiving y
  · have stock := cut.resolve_left (fun hh => hh hl)
    intro t
    rw [goal_cost_eq step good LivingSingleton (fun y => ¬ NoLiving y) closed
      (fun z hz => ⟨fun h => h.2.2, fun h => ⟨hz.1,hz.2,h⟩⟩) t y hy]
    exact timer y hp hc hn hnd hy.1 hy.2 hl stock t
  · intro t
    rw [iidHitCost_of_target step LivingSingleton y ⟨hy.1,hy.2,hl⟩]
    exact Nat.zero_le _

/-- A physical countdown remains one way to supply the smaller
zero-stock mean interface. -/
theorem singleton_expected_of_timer (timer : ConcreteSingletonTimer)
    {p c n : Nat} (x : Config p c n)
    (hp : 2 ≤ p) (hc : 12 ≤ c) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hQ : QuietEntrance x) (hR : RankPhysical.rank x = 1) :
    IIDExpectedHittingTimeAtMost step LivingSingleton x
      (17*n^2 + n*(32*(2*c+1)*(n+1))) := by
  apply singleton_expected_of_zero_mean _ x hp hc hn hnd hQ hR
  intro p' c' n' y hp' hc' hn' hnd' hq hr hl hs t
  obtain ⟨clock,hbudget⟩ := timer y hp' hc' hn' hnd' hq hr hl hs
  exact Nat.le_trans (expected_of_countdown _ _ _ clock t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbudget))

/-- Physical geometry stays fixed on each zero-stock rootless premark,
including the terminating birth mark. -/
theorem singleton_zero_stock_static {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hn : 4 ≤ n) (hm : MCOV x) (hl : NoLiving x) (hs : NoStock x) :
    NoStock (step x e) ∧
      ∀ i, (step x e i).mark = (x i).mark ∧ (step x e i).residue = (x i).residue :=
  ⟨zero_stock_preserved hn x e hl hs, zero_stock_static hn x e hm hl hs⟩

/-- Exact shared top/door patrol option at the singleton seam. The
seam sends neither port to a separate clock: both are applied to the
same old pair on each selected mark. -/
theorem alias_patrol_exact {Q : Nat} (s : Source Q) (a b : Rail) :
    patrol true true false s a b = { serviceDoor s a with right := topRail b } := by
  have hD := door_exact s a b
  have hT := top_exact true false s a b (.inl rfl)
  cases h : patrol true true false s a b
  cases h' : serviceDoor s a
  simp_all only

/-- On the covered zero-stock rootless seam the native/payment prefix
retains the marked ghost, so the complete patrol is the shared port
operation. The final leader bit is exactly its same-mark fire latch. -/
theorem alias_pair_exact {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hu : u.leader = false) (hv : v.leader = false)
    (hs : u.stock = false) :
    let door := serviceDoor v.source u.rail
    (pairStep u v).1.rail = door.left ∧
    (pairStep u v).2.rail = topRail v.rail ∧
    (pairStep u v).2.source = (if door.fire then .off else door.source) ∧
    (pairStep u v).2.leader = door.fire := by
  have hFields : (stepPrefix u v).1.mark = true ∧ (stepPrefix u v).2.leader = false := by
    cases hb : u.bullet <;> simp [stepPrefix,materialize,native,fireInitiator,fireResponder,
      impact,followerBullet,pinned,payment,payer,hm,hs,hu,hv,hb,
      show (Bullet.dummy == Bullet.none) = false from rfl,
      show (Bullet.live == Bullet.none) = false from rfl] <;> rfl
  have hPin : pinned (stepPrefix u v).1 (stepPrefix u v).2 = true := by
    simp [pinned,hFields.1,hFields.2]
  have hSelected : selectedPatrol u v = { serviceDoor v.source u.rail with right := topRail v.rail } := by
    simp [selectedPatrol,hFields.1,hFields.2,hPin,alias_patrol_exact]
  have hPorts := pair_ports u v
  simp only [hSelected,hPin,Bool.and_true] at hPorts
  refine ⟨hPorts.1,hPorts.2.1,hPorts.2.2,?_⟩
  have hP := prefix_ports u v
  unfold pairStep
  generalize hw : stepPrefix u v = w at *
  rcases w with ⟨a,b⟩
  dsimp only at hP hPin hFields ⊢
  rw [hP.1,hP.2.1,hP.2.2]
  simp only [hFields.1,hFields.2,hPin,Bool.false_or,alias_patrol_exact,patrolWrite]
  cases (serviceDoor v.source u.rail).fire
  all_goals rfl

/-- Away from the unique seam, literal zero-stock rootless updates are
body operations and cannot birth, regardless of native dummy traffic. -/
theorem alias_body_exact {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hu : u.leader = false) (hv : v.leader = false)
    (hr : v.residue = nextResidue u.residue) (hs : u.stock = false)
    (hO : v.source = .off) :
    let a := move false (⟨.off,u.rail,v.rail,false⟩ : Patrol (2*c))
    (pairStep u v).1.rail = a.left ∧ (pairStep u v).2.rail = a.right ∧
      (pairStep u v).2.leader = false := by
  have hDef : defect u v = false := by simp [defect,hr]
  have hBool (q : Bullet) : (q == .none) = false ∨ (q == .none) = true := by
    cases q <;> decide
  have hFields : (stepPrefix u v).1.mark = false ∧ (stepPrefix u v).2.leader = false := by
    rcases hBool u.bullet with hb|hb <;> rcases hBool v.bullet with hb'|hb' <;>
      simp [stepPrefix,materialize,native,fireInitiator,fireResponder,impact,
        followerBullet,pinned,payment,payer,hm,hs,hu,hv,hDef,hb,hb']
  have hPin : pinned (stepPrefix u v).1 (stepPrefix u v).2 = false := by
    simp [pinned,hFields.1,hFields.2]
  have hSelected : selectedPatrol u v = move false (⟨.off,u.rail,v.rail,false⟩ : Patrol (2*c)) := by
    simp [selectedPatrol,hFields.1,hFields.2,hPin,hO,body_exact]
  have hPorts := pair_ports u v
  simp only [hSelected] at hPorts
  refine ⟨hPorts.1,hPorts.2.1,?_⟩
  unfold pairStep
  generalize hw : stepPrefix u v = w at *
  rcases w with ⟨a,b⟩
  dsimp only at hFields ⊢
  have hl : pinned a b = false := hPin
  simp [finishBirth,patrolWrite,pinned,hFields.1,hFields.2]

/-- Rail/controller state of the literal aliased route; decoded directly
from the physical configuration rather than a replacement protocol. -/
structure AliasState (c n : Nat) where
  source : Source (2*c)
  rail : Fin n → Rail
  born : Bool

/-- Raw seam service occurs once even though it operates both ports. -/
def aliasStep {c n : Nat} (seam : Fin n) (s : AliasState c n) (e : Fin n) : AliasState c n :=
  if s.born then s else
  let r := rightNeighbor e
  let a := if e = seam then
    { serviceDoor s.source (s.rail e) with right := topRail (s.rail r) }
    else move false ⟨.off,s.rail e,s.rail r,false⟩
  ⟨if e = seam then (if a.fire then .off else a.source) else s.source,
    fun i => if i=e then a.left else if i=r then a.right else s.rail i,
    a.fire⟩

/-- Project all rails and the unique seam's controller. The target tests
the old ghost site: before lift-off it is the only possible birth site. -/
def aliasProject {p c n : Nat} (seam : Fin n) (x : Config p c n) : AliasState c n :=
  ⟨(x (rightNeighbor seam)).source, fun i => (x i).rail, (x (rightNeighbor seam)).leader⟩

private theorem pair_left_source {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.source = u.source := by
  have hM : (materialize u v).source = u.source := by unfold materialize; split <;> rfl
  have fire (a : Site p c) : (fireInitiator a).source = a.source := by
    unfold fireInitiator; split <;> rfl
  have imp (a b : Site p c) : (impact a b).1.source = a.source := by
    unfold impact; split <;> rfl
  have bullet (g : Bool) (a b : Site p c) : (followerBullet g a b).1.source = a.source := by
    unfold followerBullet; split <;> (first | rfl | split <;> rfl)
  have pay (a b : Site p c) : (payment a b).1.source = a.source := by
    unfold payment; split <;> (first | rfl | split <;> (first | rfl | split <;> rfl))
  have pre : (stepPrefix u v).1.source = u.source := by
    simp only [stepPrefix,native]
    rw [pay,bullet,imp,fire,hM]
  have birth (g : Bool) (a b : Site p c) : (finishBirth g a b).1.source = a.source := by
    unfold finishBirth; split <;> rfl
  simp only [pairStep,birth,patrolWrite]
  exact pre

private theorem right_ne_self {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have he' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

private theorem right_inj {n : Nat} {a b : Fin n} (h : rightNeighbor a = rightNeighbor b) : a = b := by
  simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor h

/-- The pure alias image commutes with the actual step at every rootless
zero-stock premark. Moreover its fire bit is exactly the actual first
leader, including the terminal mark itself. -/
theorem alias_commutes {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (seam e : Fin n)
    (hm : MCOV x) (hc : COV x) (hl : NoLiving x) (hs : NoStock x)
    (hseam : ∀ j, (x j).mark = true ↔ j = seam) :
    aliasProject seam (step x e) = aliasStep seam (aliasProject seam x) e ∧
      ((aliasProject seam (step x e)).born = false ↔ NoLiving (step x e)) := by
  have he := right_ne_self hn e
  let r := rightNeighbor e
  let top := rightNeighbor seam
  let pair := pairStep (x e) (x r)
  have ring := fun i => show step x e i = if i=e then pair.1 else if i=r then pair.2 else x i by
    rfl
  have h_left : pair.1.leader = false := (pair_geometric_fields _ _).2.1.trans (hl e)
  have h_rail (a b : Rail) (h : pair.1.rail = a ∧ pair.2.rail = b) :
      (fun i => (step x e i).rail) = fun i => if i=e then a else if i=r then b else (x i).rail := by
    funext i
    rw [ring i]
    by_cases hE : i=e
    · simp [hE,h.1]
    · by_cases hR : i=r
      · simp [hR,show r ≠ e from he,h.2]
      · simp [hE,hR]
  constructor
  · by_cases hev : e = seam
    · subst seam
      have H := alias_pair_exact (x e) (x r) ((hseam e).mpr rfl) (hl _) (hl _) (hs _)
      have h := ring r
      rw [if_neg he,if_pos rfl] at h
      have hrails := h_rail _ _ ⟨H.1,H.2.1⟩
      simp only [aliasStep,aliasProject,hl (rightNeighbor e), Bool.false_eq_true, if_false]
      change AliasState.mk _ _ _ = AliasState.mk _ _ _
      rw [h,hrails]
      rw [H.2.2.1,H.2.2.2]
      simp only [if_true]
      rfl
    · have hM : (x e).mark = false := Bool.eq_false_iff.mpr (fun h => hev ((hseam e).mp h))
      have hR : (x r).residue = nextResidue (x e).residue :=
        Classical.byContradiction (fun H => hev ((hseam e).mp (hm e (.inr H))))
      have hO : (x r).source = .off :=
        Classical.byContradiction (fun H => hev ((hseam e).mp (hc e H).2))
      have H := alias_body_exact (x e) (x r) hM (hl _) (hl _) hR (hs _) hO
      have htop : top ≠ r := fun H => hev (right_inj H.symm)
      have hsource : (step x e top).source = (x top).source := by
        rw [ring top]
        by_cases ht : top = e
        · subst e
          simpa using pair_left_source (x top) (x (rightNeighbor top))
        · simp [ht,htop]
      have hleader : (step x e top).leader = false := by
        rw [ring top]
        by_cases ht : top=e
        · simp [ht,h_left]
        · simp [ht,htop,hl top]
      have hrails := h_rail _ _ ⟨H.1,H.2.1⟩
      simp only [aliasProject,aliasStep,hl (rightNeighbor seam),Bool.false_eq_true,if_false,hev]
      change AliasState.mk (step x e top).source _ (step x e top).leader = _
      rw [hsource,hleader,hrails]
      cases (x e).rail <;> cases (x r).rail <;> rfl
  · constructor
    · intro hb i
      change (step x e top).leader = false at hb
      by_cases htop : i=top
      · simpa [htop] using hb
      · rw [ring i]
        by_cases hE : i=e
        · simpa [hE] using h_left
        · by_cases hR : i=r
          · subst i
            have hev : e ≠ seam := fun H => htop (congrArg rightNeighbor H)
            have hM : (x e).mark = false := Bool.eq_false_iff.mpr (fun h => hev ((hseam e).mp h))
            have hD : (x r).residue = nextResidue (x e).residue :=
              Classical.byContradiction (fun H => hev ((hseam e).mp (hm e (.inr H))))
            have hO : (x r).source = .off :=
              Classical.byContradiction (fun H => hev ((hseam e).mp (hc e H).2))
            have H := alias_body_exact (x e) (x r) hM (hl _) (hl _) hD (hs _) hO
            simpa [hE] using H.2.2
          · simp [hE,hR,hl i]
    · intro h; exact h top

/-- Pure rail/controller liveness certificate; all physical geometry,
native rows and scheduler-law transfer have been discharged. -/
def PureAliasClock : Prop :=
  ∀ {c n : Nat} (seam : Fin n) (s : AliasState c n),
    12 ≤ c → 4 ≤ n → s.born = false →
    ∃ clock : Countdown (aliasStep seam) (fun a => a.born = true) s,
      clock.budget [] ≤ 32*(2*c+1)*(n+1)

/-- Exact equality of first-birth cost numerators before any birth.
The folded projection may stop at birth; nothing is assumed of later
physical marks. -/
theorem alias_cost_eq {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (seam : Fin n)
    (hm : MCOV x) (hc : COV x) (hs : NoStock x)
    (hseam : ∀ j, (x j).mark = true ↔ j = seam) (hl : NoLiving x) (t : Nat) :
    iidHitCost step (fun y => ¬ NoLiving y) t x =
      iidHitCost (aliasStep seam) (fun a => a.born = true) t (aliasProject seam x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have ha : ¬ (aliasProject seam x).born = true := by
      change ¬ (x (rightNeighbor seam)).leader = true
      rw [hl (rightNeighbor seam)]
      decide
    have hp : ¬ (¬ NoLiving x) := fun h => h hl
    rw [iidHitCost, iidHitCost, if_neg hp, if_neg ha]
    have H (e : Fin n) :
        iidHitCost step (fun y => ¬ NoLiving y) t (step x e) =
        iidHitCost (aliasStep seam) (fun a => a.born = true) t
          (aliasStep seam (aliasProject seam x) e) := by
      have proj := alias_commutes hn x seam e hm hc hl hs hseam
      rw [← proj.1]
      by_cases hL : NoLiving (step x e)
      · have cover := EntranceCover.cover_closed hn x e ⟨hm,hc⟩
        have geo := singleton_zero_stock_static x e hn hm hl hs
        exact ih (step x e) cover.1 cover.2 geo.1 (fun j => (geo.2 j).1 ▸ hseam j) hL
      · have hB : (aliasProject seam (step x e)).born = true := by
          cases h : (aliasProject seam (step x e)).born
          · exact (hL (proj.2.mp h)).elim
          · rfl
        rw [iidHitCost_of_target step (fun y => ¬ NoLiving y) _ hL,
          iidHitCost_of_target (aliasStep seam) (fun a => a.born = true) _ hB]
    rw [show (fun e => iidHitCost step (fun y => ¬ NoLiving y) t (step x e)) =
      (fun e => iidHitCost (aliasStep seam) (fun a => a.born = true) t
          (aliasStep seam (aliasProject seam x) e)) from funext H]

/-- A pure rail/controller countdown supplies the physical zero-stock
mean on the original raw IID marks, with no thinning or separate seam clocks. -/
theorem zero_mean_of_alias (timer : PureAliasClock) : ZeroStockMean := by
  intro p c n x _ hc hn _ hq hr hl hs t
  obtain ⟨seam,hseam⟩ := Absorb.rank_one_unique_mark x hr
  obtain ⟨clock,hB⟩ := timer seam (aliasProject seam x) hc hn (hl (rightNeighbor seam))
  rw [alias_cost_eq hn x seam hq.1 hq.2.1 hs hseam hl t]
  exact Nat.le_trans (expected_of_countdown _ _ _ clock t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB))

#print axioms singleton_step
#print axioms expected_then
#print axioms singleton_expected_of_timer
#print axioms singleton_zero_stock_static
#print axioms alias_patrol_exact
#print axioms alias_pair_exact
#print axioms alias_body_exact
#print axioms alias_commutes
#print axioms alias_cost_eq
#print axioms zero_mean_of_alias

end L4.SingletonFinish
