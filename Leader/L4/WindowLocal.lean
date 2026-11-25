import Leader.L4.SevenTagCharge

/-! Local event router on the original physical scheduler.
Every mark advances the full ledger. The event output is a local witness,
never permission to suppress physical execution. -/
namespace L4.WindowLocal
open SevenTagCharge

inductive Event (n : Nat) where
  | keep
  | reward (tag : Fin n)
  | prefixDeath (tag : Fin n) (ghostSite : Fin n)
  | targetBirth (tag : Fin n) (leaderSite : Fin n)
  deriving DecidableEq

def nativeDeath {p c n : Nat} (x : Config p c n) (e : Fin n) : Bool :=
  let v := x (rightNeighbor e)
  v.leader && ((fireInitiator (x e)).bullet == .live) && !(fireResponder v).shield

theorem nativeDeath_iff {p c n : Nat} (x : Config p c n) (e : Fin n) :
    nativeDeath x e = true ↔ TenureOrigins.nativeKill (x e) (x (rightNeighbor e)) := by
  have h (b : Bullet) : (b == .live) = true ↔ b = .live := by cases b <;> decide
  simp [nativeDeath,TenureOrigins.nativeKill,Bool.and_eq_true,h,and_assoc]

def selectedGroupLoss {p c n : Nat} (group : List (Fin n)) (z : Ledger p c n) (e : Fin n) :
    Option (Fin n) := (lostStep z.config z.slots e).filter group.contains

def landingSlot {p c n : Nat} (x : Config p c n) (e : Fin n) : Fin n :=
  if geometricPay (x e) (x (rightNeighbor e)) then rightNeighbor e else e

def birthAt {p c n : Nat} (x : Config p c n) (e : Fin n) : Bool :=
  !(x (rightNeighbor e)).leader && ((step x e) (rightNeighbor e)).leader

def routeKnown {p c n : Nat} (certified : List (Fin n)) (target : Option (Fin n))
    (z : Ledger p c n) (e a : Fin n) : Event n :=
  if nativeDeath z.config e && certified.contains a then
    .prefixDeath a (rightNeighbor (landingSlot z.config e))
  else if (target == some a) && birthAt z.config e then
    .targetBirth a (rightNeighbor e)
  else .keep

def route {p c n : Nat} (group certified : List (Fin n)) (target : Option (Fin n))
    (z : Ledger p c n) (e : Fin n) : Event n :=
  match selectedGroupLoss group z e with
  | some a => .reward a
  | none =>
    match z.slots e with
    | none => .keep
    | some a => routeKnown certified target z e a

/-- Unconditional physical transition; the classification uses old
witnesses and the full next pair, with rewarding loss tested first. -/
def observedStep {p c n : Nat} (group certified : List (Fin n)) (target : Option (Fin n))
    (z : Ledger p c n) (e : Fin n) : Ledger p c n × Event n :=
  (SevenTagCharge.advance z e, route group certified target z e)

def rewarded {p c n : Nat} (group : List (Fin n)) (z : Ledger p c n) : Prop :=
  ∃ a, a ∈ z.losses ∧ a ∈ group

theorem observed_project {p c n : Nat} (group certified : List (Fin n)) (target : Option (Fin n))
    (z : Ledger p c n) (e : Fin n) :
    (observedStep group certified target z e).1.config = step z.config e := rfl

theorem selectedGroupLoss_iff {p c n : Nat} (group : List (Fin n))
    (z : Ledger p c n) (e a : Fin n) :
    selectedGroupLoss group z e = some a ↔ lostStep z.config z.slots e = some a ∧ a ∈ group := by
  unfold selectedGroupLoss
  cases h : lostStep z.config z.slots e with
  | none => simp [Option.filter]
  | some b =>
    by_cases hg : b ∈ group
    · simp [Option.filter,hg]
      exact fun he => he ▸ hg
    · simp [Option.filter,hg]
      intro he
      subst a
      exact hg

theorem reward_iff {p c n : Nat} (group certified : List (Fin n)) (target : Option (Fin n))
    (z : Ledger p c n) (e a : Fin n) :
    route group certified target z e = .reward a ↔ lostStep z.config z.slots e = some a ∧ a ∈ group := by
  rw [← selectedGroupLoss_iff group z e a]
  unfold route
  cases hh : selectedGroupLoss group z e
  · simp only
    cases z.slots e with
    | none => simp
    | some b =>
      simp only [reduceCtorEq,iff_false]
      change routeKnown certified target z e b ≠ .reward a
      unfold routeKnown
      split
      · simp
      · split <;> simp
  · simp

theorem rewarded_step_iff {p c n : Nat} (group : List (Fin n))
    (z : Ledger p c n) (e : Fin n) :
    rewarded group (SevenTagCharge.advance z e) ↔
      rewarded group z ∨ ∃ a, selectedGroupLoss group z e = some a := by
  constructor
  · rintro ⟨a,ha,hg⟩
    change a ∈ (lostStep z.config z.slots e).toList ++ z.losses at ha
    rcases List.mem_append.mp ha with hh | hh
    · exact .inr ⟨a,(selectedGroupLoss_iff group z e a).mpr
        ⟨by simpa using hh,hg⟩⟩
    · exact .inl ⟨a,hh,hg⟩
  · rintro (⟨a,ha,hg⟩ | ⟨a,hh⟩)
    · exact ⟨a,List.mem_append_right _ ha,hg⟩
    · have h := (selectedGroupLoss_iff group z e a).mp hh
      refine ⟨a,?_ ,h.2⟩
      change a ∈ (lostStep z.config z.slots e).toList ++ z.losses
      exact List.mem_append_left _ (by simp [h.1])

theorem rewarded_sticky {p c n : Nat} (group : List (Fin n))
    (z : Ledger p c n) (e : Fin n) (h : rewarded group z) :
    rewarded group (SevenTagCharge.advance z e) :=
  (rewarded_step_iff group z e).mpr (.inl h)

attribute [local irreducible] birthAt nativeDeath routeKnown selectedGroupLoss
/-- An exterior mark with no selected group event does not halt the local
trial, even when the physical global rank changes. -/
theorem route_keep_of_exterior {p c n : Nat} (group certified : List (Fin n))
    (target : Option (Fin n)) (z : Ledger p c n) (e : Fin n)
    (hLoss : selectedGroupLoss group z e = none)
    (hEvents : ∀ a, z.slots e = some a → routeKnown certified target z e a = Event.keep) :
    route group certified target z e = Event.keep := by
  unfold route
  rw [hLoss]
  change (match z.slots e with | none => Event.keep | some a => routeKnown certified target z e a) = Event.keep
  split
  · rfl
  · rename_i a ha
    exact hEvents a ha

theorem routeKnown_keep {p c n : Nat} (certified : List (Fin n)) (target : Option (Fin n))
    (z : Ledger p c n) (e a : Fin n)
    (hD : (nativeDeath z.config e && certified.contains a) = false)
    (hB : ((target == some a) && birthAt z.config e) = false) :
    routeKnown certified target z e a = Event.keep := by
  simp only [routeKnown,hD,hB,Bool.false_eq_true,if_false]


private theorem notLoop {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

/-- Certified death and group-loss ordering. A surviving victim is
looked up at its post-mark location, even when the N2 mark also pays
P3. If it coalesces with a resident the same mark instead rewards. -/
theorem prefix_death_result {p c n : Nat} (group certified : List (Fin n))
    (target : Option (Fin n)) (z : Ledger p c n) (e a : Fin n)
    (hn : 4 ≤ n) (hm : MCOV z.config) (hc : COV z.config)
    (ht : Covers z.config z.slots) (hu : Unique z.slots)
    (hSubset : certified ⊆ group)
    (ha : z.slots e = some a) (hC : a ∈ certified)
    (hD : nativeDeath z.config e = true) :
    (route group certified target z e = Event.reward a ∧
      lostStep z.config z.slots e = some a) ∨
    (let l := landingSlot z.config e
     route group certified target z e = Event.prefixDeath a (rightNeighbor l) ∧
      (SevenTagCharge.advance z e).slots l = some a ∧
      ((SevenTagCharge.advance z e).config (rightNeighbor l)).leader = false) := by
  have hk := (nativeDeath_iff z.config e).mp hD
  obtain ⟨a',ha',hDead,hOut⟩ := native_death_tag_outcome hn z.config z.slots e hm hc ht hu hk.1 hk
  have hh : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst a'
  by_cases hLost : lostStep z.config z.slots e = some a
  · exact .inl ⟨(reward_iff group certified target z e a).mpr ⟨hLost,hSubset hC⟩,hLost⟩
  · have hNo : lostStep z.config z.slots e = none := by
      unfold lostStep
      split
      · next h =>
        exfalso
        exact hLost (by simp [lostStep,h,ha])
      · rfl
    have hg : selectedGroupLoss group z e = none := by
      unfold selectedGroupLoss
      rw [hNo]
      rfl
    have hTrue : (nativeDeath z.config e && certified.contains a) = true :=
      Bool.and_eq_true_iff.mpr ⟨hD,List.contains_iff_mem.mpr hC⟩
    have hRoute : route group certified target z e =
        Event.prefixDeath a (rightNeighbor (landingSlot z.config e)) := by
      unfold route
      rw [hg]
      change (match z.slots e with | none => Event.keep | some b => routeKnown certified target z e b) = _
      rw [ha]
      change routeKnown certified target z e a = _
      unfold routeKnown
      rw [if_pos hTrue]
    apply Or.inr
    refine ⟨hRoute,?_⟩
    by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e)) = true
    · cases hOut with
      | inl h =>
        have hf : slotsStep z.config z.slots e e = none := by
          unfold slotsStep
          rw [if_pos hp]
          exact (paid_mover_or_resident hn z.slots e).1
        simp [hf] at h
      | inr h =>
        rcases h with h | h
        · simpa only [landingSlot,hp,if_true,SevenTagCharge.advance] using And.intro h.1 h.2.2
        · exact (hLost h.1).elim
    · have hF : geometricPay (z.config e) (z.config (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hp
      simp [landingSlot,hF,SevenTagCharge.advance,slotsStep,ha,hDead]

/-- A genuine target birth on the responding site keeps its original
identity. In particular the apparent target cannot already have paid
and been replaced by its adjacent resident in this mark. -/
theorem target_birth_at_same_slot {p c n : Nat} (hn : 4 ≤ n)
    (z : Ledger p c n) (e a : Fin n) (hm : MCOV z.config) (hc : COV z.config)
    (ha : z.slots e = some a) (hB : birthAt z.config e = true) :
    (SevenTagCharge.advance z e).slots e = some a ∧
      ((SevenTagCharge.advance z e).config (rightNeighbor e)).leader = true ∧
      lostStep z.config z.slots e = none := by
  unfold birthAt at hB
  have hPair := Bool.and_eq_true_iff.mp hB
  have hC := (EntranceCover.cover_closed hn z.config e ⟨hm,hc⟩).1 e (.inl hPair.2)
  have hMark := covered_step_mark hn z.config hm e e
  have hF : geometricPay (z.config e) (z.config (rightNeighbor e)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hp
    simp [hp] at hMark
    simp [hC] at hMark
  exact ⟨by simp [SevenTagCharge.advance, slotsStep,hF,ha],hPair.2,
    by simp [lostStep,RankPhysical.retirement,hF]⟩

#print axioms prefix_death_result
#print axioms target_birth_at_same_slot
#print axioms rewarded_step_iff

private theorem pay_cannot_land_from_living_responder {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hL : (step x e (rightNeighbor e)).leader = true) :
    geometricPay (x e) (x (rightNeighbor e)) = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have h := TaggedTrace.geometricPay_responder_nonleader _ _ hp
  have hPost : (step x e (rightNeighbor e)).leader = false := by
    simpa [step,notLoop hn e] using h
  rw [hL] at hPost
  contradiction

/-- Local repair of the global-stop geometry: both actual
endpoints survive, so their open sector remains root free. An exterior
retirement may occur on this very mark; no global rank condition is used. -/
theorem sector_persists_of_endpoints {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (s e : Fin n) (hm : MCOV x)
    (h : FirstMark x s d) (hS : (step x e s).leader = true)
    (hT : (step x e (liftedSite s (d+1))).leader = true) :
    FirstMark (step x e) s d := by
  have paid_from_mark (hp : geometricPay (x e) (x (rightNeighbor e)) = true) :
      (x e).mark = true := RearTrace.paid_was_marked hm e hp
  refine ⟨h.lt, ?_, ?_⟩
  · rw [covered_step_mark hn x hm]
    by_cases hP : geometricPay (x e) (x (rightNeighbor e)) = true
    · have he : liftedSite s d ≠ e := by
        intro hh
        have hh' : liftedSite s (d+1) = rightNeighbor e := by rw [liftedSite_succ,hh]
        rw [hh'] at hT
        exact (Bool.eq_false_iff.mp (pay_cannot_land_from_living_responder hn x e hT)) hP
      by_cases hr : liftedSite s d = rightNeighbor e <;> simp [hP,he,hr,h.marked,notLoop hn e]
    · have hF := Bool.eq_false_iff.mpr hP
      simp only [hF,Bool.false_eq_true,if_false]
      exact h.marked
  · intro j hj
    rw [covered_step_mark hn x hm]
    by_cases hP : geometricPay (x e) (x (rightNeighbor e)) = true
    · have he : liftedSite s j ≠ e := by
        intro hh
        apply h.before j hj
        rw [hh]
        exact paid_from_mark hP
      have hr : liftedSite s j ≠ rightNeighbor e := by
        intro hh
        cases j with
        | zero =>
          rw [liftedSite_zero] at hh
          rw [hh] at hS
          exact (Bool.eq_false_iff.mp (pay_cannot_land_from_living_responder hn x e hS)) hP
        | succ j =>
          rw [liftedSite_succ] at hh
          have he' := FreshSeparation.succ_inj hh
          apply h.before j (by omega)
          rw [he']
          exact paid_from_mark hP
      simpa only [hP,if_true,if_neg he,if_neg hr] using h.before j hj
    · have hF := Bool.eq_false_iff.mpr hP
      simpa only [hF,Bool.false_eq_true,if_false] using h.before j hj

/-- An existing living root which is not killed on this mark keeps its
old identity and physical site, including on an exterior merger into it. -/
theorem living_tag_stays {p c n : Nat} (hn : 4 ≤ n)
    (z : Ledger p c n) (s e a : Fin n) (hc : COV z.config)
    (ha : z.slots s = some a) (hL : (z.config (rightNeighbor s)).leader = true)
    (hNoDeath : s = e → nativeDeath z.config e = false) :
    (advance z e).slots s = some a ∧
      ((advance z e).config (rightNeighbor s)).leader = true := by
  have hpost : (step z.config e (rightNeighbor s)).leader = true := by
    by_cases hS : rightNeighbor s = e
    · rw [hS] at hL ⊢
      simpa [step] using (pair_geometric_fields (z.config e) (z.config (rightNeighbor e))).2.1.trans hL
    · by_cases hR : rightNeighbor s = rightNeighbor e
      · have he := FreshSeparation.succ_inj hR
        subst s
        cases h : (step z.config e (rightNeighbor e)).leader
        · have hk := (TenureOrigins.covered_ring_leader_loss_iff _ _ (notLoop hn e) hc hL).mp h
          have hD := (nativeDeath_iff z.config e).mpr hk
          rw [hNoDeath rfl] at hD
          contradiction
        · rfl
      · simpa [step,hS,hR] using hL
  refine ⟨?_,hpost⟩
  change slotsStep z.config z.slots e s = some a
  by_cases he : s = e
  · subst s
    have hN := pay_cannot_land_from_living_responder hn z.config e hpost
    simp only [slotsStep,hN,Bool.false_eq_true,if_false,ha]
  · unfold slotsStep
    split
    · unfold SevenTagCharge.move
      rw [if_neg he]
      split
      · simp [ha,Option.or]
      · exact ha
    · exact ha

#print axioms sector_persists_of_endpoints
#print axioms living_tag_stays

def TaggedLeader {p c n : Nat} (z : Ledger p c n) (s a : Fin n) : Prop :=
  z.slots s = some a ∧ (z.config (rightNeighbor s)).leader = true

/-- At a keep mark an actual certified leader survives at the same tag
and same site. The argument detects a kill before treating a simultaneous
target birth as an extension. -/
theorem certified_stationary_of_keep {p c n : Nat}
    (hn : 4 ≤ n) (x : Config p c n) (z : Ledger p c n)
    (group certified : List (Fin n)) (target : Option (Fin n)) (e s a : Fin n)
    (hValid : Valid z x) (hSubset : certified ⊆ group) (hC : a ∈ certified)
    (hL : TaggedLeader z s a) (hKeep : route group certified target z e = Event.keep) :
    TaggedLeader (advance z e) s a := by
  refine living_tag_stays hn z s e a hValid.sourceCover hL.1 hL.2 ?_
  intro h
  subst s
  apply Bool.eq_false_iff.mpr
  intro hd
  rcases prefix_death_result group certified target z e a hn hValid.markCover hValid.sourceCover
    hValid.covers hValid.unique hSubset hL.1 hC hd with hBad | hBad
  · rw [hKeep] at hBad
    cases hBad.1
  · dsimp only at hBad
    rw [hKeep] at hBad
    cases hBad.1

/-- Exact geometry object tracked by preparation and the sealed sector
phases. Its roots are the two named living tags at the indicated slots,
not merely two consecutive leaders in a filtered roster. -/
structure CertifiedSector {p c n : Nat} (z : Ledger p c n)
    (left right s t : Fin n) (d : Nat) : Prop where
  left_live : TaggedLeader z s left
  right_live : TaggedLeader z t right
  terminal_site : liftedSite (rightNeighbor s) (d+1) = rightNeighbor t
  gap : FirstMark z.config (rightNeighbor s) d

theorem certifiedSector_keep {p c n : Nat}
    (hn : 4 ≤ n) (x : Config p c n) (z : Ledger p c n)
    (group certified : List (Fin n)) (target : Option (Fin n))
    (e left right s t : Fin n) (d : Nat)
    (hValid : Valid z x) (hSubset : certified ⊆ group)
    (hLeft : left ∈ certified) (hRight : right ∈ certified)
    (hSector : CertifiedSector z left right s t d)
    (hKeep : route group certified target z e = Event.keep) :
    CertifiedSector (advance z e) left right s t d := by
  have hL := certified_stationary_of_keep hn x z group certified target e s left
    hValid hSubset hLeft hSector.left_live hKeep
  have hR := certified_stationary_of_keep hn x z group certified target e t right
    hValid hSubset hRight hSector.right_live hKeep
  have hT : (step z.config e (liftedSite (rightNeighbor s) (d+1))).leader = true := by
    rw [hSector.terminal_site]
    exact hR.2
  exact ⟨hL,hR,hSector.terminal_site,
    sector_persists_of_endpoints hn z.config (rightNeighbor s) e hValid.markCover hSector.gap hL.2 hT⟩

#print axioms certifiedSector_keep

/-- Only the named actual leader is used to rule out native death. No
conclusion about exterior kills is needed to run the native sector rows. -/
theorem certified_no_death_on_keep {p c n : Nat}
    (hn : 4 ≤ n) (x : Config p c n) (z : Ledger p c n)
    (group certified : List (Fin n)) (target : Option (Fin n)) (e s a : Fin n)
    (hValid : Valid z x) (hSubset : certified ⊆ group) (hA : a ∈ certified)
    (hL : TaggedLeader z s a) (hKeep : route group certified target z e = Event.keep)
    (hR : rightNeighbor e = rightNeighbor s) :
    nativeDeath z.config e = false := by
  have hs := FreshSeparation.succ_inj hR
  subst s
  have h := certified_stationary_of_keep hn x z group certified target e e a
    hValid hSubset hA hL hKeep
  apply Bool.eq_false_iff.mpr
  intro hd
  have hk := (nativeDeath_iff z.config e).mp hd
  have hf := (TenureOrigins.covered_ring_leader_loss_iff z.config e (notLoop hn e)
    hValid.sourceCover hL.2).mpr hk
  have hh : (step z.config e (rightNeighbor e)).leader = true := h.2
  rw [hh] at hf
  cases hf

#print axioms certified_no_death_on_keep

/-- Reconstruct the shooting root on the old tape: either this mark's
new N0 launch at its own distinct old incoming bond, or the quiet
nearest-upstream-root certificate of the genuine preexisting live byte. -/
theorem killing_shooter_pre_mark {p c n : Nat} (hn : 4 ≤ n)
    (z : Ledger p c n) (e : Fin n) (hq : QuietEntrance z.config)
    (ht : Covers z.config z.slots) (hD : nativeDeath z.config e = true) :
    ∃ incoming a d, z.slots incoming = some a ∧
      (z.config (rightNeighbor incoming)).leader = true ∧
      d < n ∧ liftedSite (rightNeighbor incoming) d = e ∧
      (∀ j, j < d → (z.config (liftedSite (rightNeighbor incoming) j)).mark = false) ∧
      ((d = 0 ∧ tagOverwrite (z.config e) = true) ∨
        ((z.config (rightNeighbor incoming)).shield = true ∧
          ∀ j, j ≤ d → (z.config (liftedSite (rightNeighbor incoming) j)).signal = .zero)) := by
  have tag_exists (i : Fin n) (hm : (z.config i).mark = true) : ∃ a, z.slots i = some a := by
    have hA := (ht i).trans hm
    cases h : z.slots i with
    | none => simp [h] at hA
    | some a => exact ⟨a,rfl⟩
  by_cases hShot : tagOverwrite (z.config e) = true
  · let i := liftedSite e (n-1)
    have hi : rightNeighbor i = e := by
      rw [show rightNeighbor i = liftedSite e (n-1+1) by rw [liftedSite_succ],show n-1+1=n by omega,
        liftedSite_full]
    have hLe : (z.config e).leader = true := by
      unfold tagOverwrite at hShot
      exact (Bool.and_eq_true_iff.mp hShot).1
    obtain ⟨a,ha⟩ := tag_exists i (hq.1 i (.inl (hi.symm ▸ hLe)))
    refine ⟨i,a,0,ha,hi.symm ▸ hLe,by omega,?_,?_,.inl ⟨rfl,hShot⟩⟩
    · rw [liftedSite_zero,hi]
    · intro j hj
      omega
  · have hb := TenureOrigins.killing_bullet_preexisting_if_no_refire
      ((nativeDeath_iff z.config e).mp hD) (Bool.eq_false_iff.mpr hShot)
    obtain ⟨i,d,hd,hm,hL,hS,he,hbefore,hzero⟩ := hq.2.2.2 e hb
    obtain ⟨a,ha⟩ := tag_exists i hm
    refine ⟨i,a,d,ha,hL,hd,he,?_,.inr ⟨hS,hzero⟩⟩
    intro j hj
    exact hbefore j hj

#print axioms killing_shooter_pre_mark

private theorem lift_add {n : Nat} (b : Fin n) (i j : Nat) :
    liftedSite (liftedSite b i) j = liftedSite b (i+j) := by
  apply Fin.ext
  simp [liftedSite,Nat.mod_add_mod,Nat.add_assoc]

private theorem lift_origin_inj {n : Nat} (d : Nat) {a b : Fin n}
    (h : liftedSite a d = liftedSite b d) : a = b := by
  induction d with
  | zero => simpa [liftedSite_zero] using h
  | succ d ih =>
    rw [liftedSite_succ,liftedSite_succ] at h
    exact ih (FreshSeparation.succ_inj h)

/-- Two purported nearest marked predecessors of the same donor are
identical. This needs no stability assumption about exterior roots. -/
theorem nearest_shooting_root_unique {p c n : Nat} (x : Config p c n)
    (a b : Fin n) (d f : Nat)
    (ha : (x a).mark = true) (hb : (x b).mark = true)
    (he : liftedSite (rightNeighbor a) d = liftedSite (rightNeighbor b) f)
    (hA : ∀ j, j < d → (x (liftedSite (rightNeighbor a) j)).mark = false)
    (hB : ∀ j, j < f → (x (liftedSite (rightNeighbor b) j)).mark = false) :
    a = b ∧ d = f := by
  have leq (i j : Fin n) (d f : Nat) (hI : (x i).mark = true)
      (he : liftedSite (rightNeighbor i) d = liftedSite (rightNeighbor j) f)
      (hj : ∀ m, m < f → (x (liftedSite (rightNeighbor j) m)).mark = false) : f ≤ d := by
    by_cases h : f≤d
    · exact h
    · let k := f-d-1
      have H : k+1+d=f := by dsimp [k]; omega
      have hSite : rightNeighbor i = liftedSite (rightNeighbor j) (k+1) := by
        apply lift_origin_inj d
        rw [lift_add,H]
        exact he
      rw [liftedSite_succ] at hSite
      have hI' := FreshSeparation.succ_inj hSite
      have hmark := hj k (by dsimp [k]; omega)
      rw [← hI',hI] at hmark
      cases hmark
  have h1 := leq a b d f ha he hB
  have h2 := leq b a f d hb he.symm hA
  have hd : d=f := by omega
  subst f
  exact ⟨FreshSeparation.succ_inj (lift_origin_inj d he),rfl⟩

/-- When a known consecutive tagged sector has a native kill at its
terminal, the recovered shooter is precisely that sector's left tag,
and not simply a nearby surviving leader. -/
theorem terminal_kill_named_shooter {p c n : Nat} (hn : 4 ≤ n)
    (z : Ledger p c n) (l r s t : Fin n) (d : Nat)
    (hq : QuietEntrance z.config) (ht : Covers z.config z.slots)
    (h : CertifiedSector z l r s t d) (hd : nativeDeath z.config t = true) :
    liftedSite (rightNeighbor s) d = t ∧
    ((d = 0 ∧ tagOverwrite (z.config t) = true) ∨
      ((z.config (rightNeighbor s)).shield = true ∧
        ∀ j, j ≤ d → (z.config (liftedSite (rightNeighbor s) j)).signal = .zero)) := by
  have hT : liftedSite (rightNeighbor s) d = t := by
    apply FreshSeparation.succ_inj
    rw [← liftedSite_succ]
    exact h.terminal_site
  refine ⟨hT,?_⟩
  obtain ⟨i,a,f,hi,hLeader,hf,hE,hB,hKind⟩ := killing_shooter_pre_mark hn z t hq ht hd
  have hA : (z.config s).mark = true := by simpa [h.left_live.1] using (ht s).symm
  have hMI : (z.config i).mark = true := by simpa [hi] using (ht i).symm
  have hh := nearest_shooting_root_unique z.config s i d f hA hMI (hT.trans hE.symm)
    (fun j hj => Bool.eq_false_iff.mpr (h.gap.before j hj)) hB
  rw [← hh.1,← hh.2] at hKind
  exact hKind

#print axioms nearest_shooting_root_unique
#print axioms terminal_kill_named_shooter

/-- Affirms the target-birth report, not just a raw leader bit change.
The same selected mark cannot instead route a certified native death:
there is one responding site and its old leader bit was false. -/
theorem target_birth_result {p c n : Nat} (hn : 4 ≤ n)
    (group cert : List (Fin n)) (z : Ledger p c n) (e a : Fin n)
    (hm : MCOV z.config) (hc : COV z.config)
    (ha : z.slots e = some a) (hB : birthAt z.config e = true) :
    route group cert (some a) z e = Event.targetBirth a (rightNeighbor e) ∧
    TaggedLeader (advance z e) e a := by
  have h := target_birth_at_same_slot hn z e a hm hc ha hB
  have hg : selectedGroupLoss group z e = none := by
    unfold selectedGroupLoss
    rw [h.2.2]
    rfl
  have hD : (nativeDeath z.config e && cert.contains a) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hl := ((nativeDeath_iff z.config e).mp ((Bool.and_eq_true_iff.mp hh).1)).1
    unfold birthAt at hB
    have hf := (Bool.and_eq_true_iff.mp hB).1
    simp only [hl,Bool.not_true,Bool.false_eq_true] at hf
  refine ⟨?_,h.1,h.2.1⟩
  unfold route
  rw [hg]
  change (match z.slots e with | none => Event.keep | some b => routeKnown cert (some a) z e b) = _
  rw [ha]
  change routeKnown cert (some a) z e a = _
  have hB' : ((some a == some a) && birthAt z.config e) = true := by
    simp only [beq_self_eq_true,Bool.true_and,hB]
  simp only [routeKnown,hD,hB',Bool.false_eq_true,if_false,if_true]

#print axioms target_birth_result
end L4.WindowLocal
