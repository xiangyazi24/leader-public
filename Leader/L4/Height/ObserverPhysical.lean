import Leader.L4.BStarJoinedLap
import Leader.L4.AllSizeS1Geometry
import Leader.L4.BStarResetSchedule
import Leader.L4.RearGeometry
import Leader.L4.RootedEntrance

/-! Physical observer projection and the public edge-cover latch. -/
namespace L4.Height.ObserverPhysical
open AllSizeProtocol
open BStarLapTransfer (decode get plan)
open BStarPublicCodec (readPub)
noncomputable section
variable {a : LargeParams} {n : Nat}
abbrev Ring (a : LargeParams) (n : Nat) := Fin n → LargeSite a
abbrev next (b : LargeRows a) := @AllSizeS1Geometry.step a n b
abbrev run (b : LargeRows a) := @BStarResetSchedule.run (Ring a n) n (next b)
def pub (hp : 0<a.p) (x : Ring a n) : Config a.p a.c1 n :=
  fun i => readPub hp (x i).publicRow
def slots (x : Ring a n) (i : Fin n) := decode (get (x i).guard)
def refBit (b : LargeRows a) (x : Ring a n) (i : Fin n) :=
  H5.seesReference (reference b (x i))
def Fixed (b : LargeRows a) (x : Ring a n) (root : Fin n) : Prop :=
  ∀ w i, refBit b (run b x w) i = true ↔ i = root
def pulse (b : LargeRows a) (hp : 0<a.p) (x : Ring a n) (e : Fin n) : Bool :=
  let j := rightNeighbor e
  let old := (reference b (x e), reference b (x j))
  let y := next b x e
  let newRef := (reference b (y e), reference b (y j))
  let u := pub hp x e
  let v := pub hp x j
  let p := pairStep u v
  (H5.row ((x e).guard,(x j).guard) old newRef (u.mark,v.mark) (p.1.mark,p.2.mark)).seed.1

theorem fixed_step {b : LargeRows a} {x : Ring a n} {root : Fin n}
    (fix : Fixed b x root) (e : Fin n) : Fixed b (next b x e) root :=
  fun w i => fix (e::w) i

theorem fixed_run {b : LargeRows a} {x : Ring a n} {root : Fin n}
    (fix : Fixed b x root) (w : List (Fin n)) : Fixed b (run b x w) root := by
  intro v i
  simpa only [run,BStarResetSchedule.run_append] using fix (w++v) i

theorem incoming_pulse (b : LargeRows a) (hp : 0<a.p) {x : Ring a n} {root : Fin n}
    (fix : Fixed b x root) (e : Fin n) :
    pulse b hp x e = true ↔ rightNeighbor e = root ∧ (slots x root).pc = 2 := by
  change (refBit b x (rightNeighbor e) && refBit b (next b x e) (rightNeighbor e) &&
    ((slots x (rightNeighbor e)).pc == 2)) = true ↔ _
  have old := fix [] (rightNeighbor e)
  have newRef := (fixed_step fix e) [] (rightNeighbor e)
  change refBit b x _ = true ↔ _ at old
  change refBit b (next b x e) _ = true ↔ _ at newRef
  simp only [Bool.and_eq_true, beq_iff_eq, old, newRef]
  constructor
  · rintro ⟨⟨h,_⟩, hpc⟩
    exact ⟨h,h ▸ hpc⟩
  · rintro ⟨h,hpc⟩
    exact ⟨⟨h,h⟩,h.symm ▸ hpc⟩

theorem no_seed_iff_no_pending (b : LargeRows a) (hp : 0<a.p) {x : Ring a n}
    {root : Fin n} (fix : Fixed b x root) :
    (∀ w e, pulse b hp (run b x w) e = false) ↔
      ∀ w, (slots (run b x w) root).pc ≠ 2 := by
  constructor
  · intro h w pending
    have hit := (incoming_pulse b hp (fixed_run fix w) (RearTrace.predecessor root)).2
      ⟨RearTrace.right_predecessor root,pending⟩
    rw [h] at hit
    contradiction
  · intro h w e
    apply Bool.eq_false_iff.mpr
    intro hit
    exact h w ((incoming_pulse b hp (fixed_run fix w) e).1 hit).2

theorem endpoints_ne (hn : 4≤n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val+1)%n=e.val at hv
  have bound := e.isLt
  by_cases cut : e.val+1<n
  · rw [Nat.mod_eq_of_lt cut] at hv; omega
  · rw [show e.val+1=n by omega, Nat.mod_self] at hv; omega

def seeded {p c : Nat} (x : Config p c n) (e : Fin n) (bit : Bool) : Config p c n :=
  fun i => if i=e then {x i with mark := (x i).mark || bit} else x i
def ordinaryMarks (hp : 0<a.p) (x : Ring a n) (e : Fin n) : Pair Bool :=
  let p := pairStep (pub hp x e) (pub hp x (rightNeighbor e))
  (p.1.mark,p.2.mark)
def crosses (hp : 0<a.p) (x : Ring a n) (e : Fin n) :=
  (pub hp x e).mark && !(ordinaryMarks hp x e).1 && (ordinaryMarks hp x e).2

theorem joined_step (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Ring a n) (e : Fin n) :
    let j := rightNeighbor e
    let y := next b x e
    let old := (slots x e,slots x j)
    let p := plan old.1 old.2 (refBit b x e) (refBit b x j) (refBit b y e) (refBit b y j)
      ((pub hp x e).mark,(pub hp x j).mark) (ordinaryMarks hp x e)
    (slots y e,slots y j) = (p.1.1.site old.1,p.1.2.site old.2) ∧
    pub hp y = seeded (step (pub hp x) e) e (pulse b hp x e) := by
  dsimp only
  let j := rightNeighbor e
  let out := largePair b (x e,x j)
  have hL : next b x e e=out.1 := if_pos rfl
  have hR : next b x e j=out.2 := by
    change (if j=e then out.1 else if j=j then out.2 else x j)=_
    rw [if_neg (endpoints_ne hn e),if_pos rfl]
  have pair := BStarJoinedLap.joined_lap_public b hp bind (x e,x j)
  constructor
  · change (decode (get (next b x e e).guard),decode (get (next b x e j).guard)) = _
    unfold refBit
    change _ = ((plan _ _ _ _ (H5.seesReference (reference b (next b x e e)))
      (H5.seesReference (reference b (next b x e j))) _ _).1.1.site _,
      (plan _ _ _ _ (H5.seesReference (reference b (next b x e e)))
      (H5.seesReference (reference b (next b x e j))) _ _).1.2.site _)
    rw [hL,hR]
    exact pair.1
  · have L := congrArg Prod.fst pair.2
    have R := congrArg Prod.snd pair.2
    have seedEq : pulse b hp x e =
        (H5.seesReference (reference b (x j)) && H5.seesReference (reference b out.2) &&
        ((slots x j).pc == 2)) := by
      change (refBit b x j && H5.seesReference (reference b (next b x e j)) && _) = _
      rw [hR]
      rfl
    funext i
    by_cases he : i=e
    · subst i
      change readPub hp (next b x e e).publicRow = _
      rw [hL]
      simp only [seeded,L4.step,if_pos rfl,seedEq]
      exact L
    · by_cases hj : i=j
      · subst i
        change readPub hp (next b x e j).publicRow = _
        rw [hR]
        simp [seeded,L4.step,j,endpoints_ne hn e]
        exact R
      · simp only [pub,next,AllSizeS1Geometry.step,seeded,L4.step,if_neg he,
          if_neg (show i≠rightNeighbor e from hj)]

theorem extra_cover {p c : Nat} (x : Config p c n) (e i : Fin n) (bit : Bool)
    (h : EntranceCover.BondCovered (x i) (x (rightNeighbor i))) :
    EntranceCover.BondCovered (seeded x e bit i) (seeded x e bit (rightNeighbor i)) := by
  let y := seeded x e bit
  have geom (j : Fin n) : (y j).residue=(x j).residue ∧ (y j).leader=(x j).leader ∧
      (y j).source=(x j).source := by
    by_cases z : j=e <;> simp [y,seeded,z]
  have mark (hm : (x i).mark=true) : (y i).mark=true := by
    by_cases z : i=e
    · subst e; simp [y,seeded,hm]
    · simpa [y,seeded,z] using hm
  change EntranceCover.BondCovered (y i) (y (rightNeighbor i))
  unfold EntranceCover.BondCovered
  rw [(geom _).2.1,(geom _).1,(geom i).1,(geom _).2.2]
  exact ⟨fun a => mark (h.1 a), fun a => ⟨(h.2 a).1, mark (h.2 a).2⟩⟩

theorem cover_step (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Ring a n) (e i : Fin n)
    (h : i=e ∨ EntranceCover.BondCovered (pub hp x i) (pub hp x (rightNeighbor i))) :
    EntranceCover.BondCovered (pub hp (next b x e) i) (pub hp (next b x e) (rightNeighbor i)) := by
  rw [(joined_step hn b hp bind x e).2]
  exact extra_cover _ _ _ _ (EntranceCover.bondCovered_step hn _ e i h)

theorem cover_monitor_step (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Ring a n) (e : Fin n) (todo : List (Fin n))
    (h : EntranceCover.coverInvariant (todo,pub hp x)) :
    EntranceCover.coverInvariant (EntranceCover.advance todo e,pub hp (next b x e)) := by
  intro i hi
  apply cover_step hn b hp bind
  by_cases he : i=e
  · exact Or.inl he
  · apply Or.inr
    apply h
    cases todo with
    | nil => simp
    | cons a tail =>
      change i ∉ EntranceCover.advance (a::tail) e at hi
      by_cases ha : e=a
      · subst a; simpa [EntranceCover.advance,he] using hi
      · simpa [EntranceCover.advance,ha] using hi

theorem cover_cost (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Ring a n) :
    L4.IIDExpectedHittingTimeAtMost (next b)
      (fun y => MCOV (pub hp y) ∧ COV (pub hp y)) x (n*n) := by
  let good := fun y : List (Fin n) × Ring a n => EntranceCover.coverInvariant (y.1,pub hp y.2)
  have H := EntranceCover.orderedAllEdges_then_physical (next b)
    (fun y => MCOV (pub hp y) ∧ COV (pub hp y)) good 0
    (fun y e hy => cover_monitor_step hn b hp bind y.2 e y.1 hy)
    (by
      intro y hy t
      have covered := (EntranceCover.coverInvariant_endpoint _).1 hy
      rw [L4.iidHitCost_of_target (next b) (fun z => MCOV (pub hp z) ∧ COV (pub hp z)) y covered]; simp)
    x (by
      intro i hi
      exact (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim)
  simpa using H

/-- The only disappearing old carrier crosses precisely the selected physical bond. -/
theorem carrier_step (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Ring a n) (e i : Fin n) (old : (pub hp x i).mark = true) :
    (pub hp (next b x e) i).mark = true ∨
      (i=e ∧ (pub hp (next b x e) (rightNeighbor e)).mark=true ∧ crosses hp x e=true) := by
  rw [(joined_step hn b hp bind x e).2]
  let y := pub hp x
  let j := rightNeighbor e
  let u := y e
  let v := y j
  have pair := RootedEntrance.raw_pair_marks u v
  by_cases pay : geometricPay u v=true
  · rw [if_pos pay] at pair
    by_cases left : i=e
    · right
      subst i
      refine ⟨rfl,?_,?_⟩
      · simpa [seeded,L4.step,j,endpoints_ne hn e] using pair.2
      · change ((pub hp x e).mark && !(pairStep u v).1.mark && (pairStep u v).2.mark)=true
        rw [old,pair.1,pair.2]; rfl
    · left
      by_cases right : i=j
      · subst i
        simpa [seeded,L4.step,j,endpoints_ne hn e] using pair.2
      · simpa [seeded,L4.step,left,(show i ≠ rightNeighbor e from right)] using old
  · rw [if_neg pay] at pair
    left
    by_cases left : i=e
    · subst i
      have hm : (materialize u v).mark=true := by simp [materialize,u,y,old]
      change (seeded (step y e) e _ e).mark=true
      simp only [seeded,step,if_pos rfl]
      change ((pairStep u v).1.mark || _) = true
      simp [pair.1,hm]
    · by_cases right : i=j
      · subst i
        simpa [seeded,L4.step,j,endpoints_ne hn e] using pair.2.trans old
      · simpa [seeded,L4.step,left,(show i ≠ rightNeighbor e from right)] using old

def Marked (b : LargeRows a) (hp : 0<a.p) (x : Ring a n) : Prop :=
  (∃ root, Fixed b x root) ∧ (∀ w e, pulse b hp (run b x w) e=false) ∧
  RootedEntrance.MarkNonempty (pub hp x) ∧ MCOV (pub hp x) ∧ COV (pub hp x)

theorem marked_projects (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    {x : Ring a n} (e : Fin n) (h : Marked b hp x) :
    pub hp (next b x e)=step (pub hp x) e := by
  rw [(joined_step hn b hp bind x e).2, (show pulse b hp x e=false from h.2.1 [] e)]
  funext i
  by_cases he : i=e
  · simp [seeded,he]
  · simp [seeded,he]

theorem marked_closed (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic = BStarPublic.publicWork (c₁:=a.c1) hp)
    {x : Ring a n} (e : Fin n) (h : Marked b hp x) : Marked b hp (next b x e) := by
  obtain ⟨r,hr⟩ := h.1
  refine ⟨⟨r,fixed_step hr e⟩,fun w f => h.2.1 (e::w) f,?_⟩
  rw [marked_projects hn b hp bind e h]
  exact ⟨RootedEntrance.mark_nonempty_step hn _ _ h.2.2.1,
    EntranceCover.cover_closed hn _ _ h.2.2.2⟩

end
end L4.Height.ObserverPhysical
