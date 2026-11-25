import Leader.L4.RankBlockContraction
import Leader.L4.TenureOrigins
import Leader.L4.FreshSeparation

/-! Literal physical root-identity ledger of the last-two argument. The
slot of a tag is the marked incoming bond of its current root. -/
namespace L4.SevenTagCharge
open RankPhysical

abbrev Slots (n : Nat) := Fin n → Option (Fin n)

def initSlots {p c n : Nat} (x : Config p c n) : Slots n :=
  fun i => if (x i).mark then some i else none

def occupied {n : Nat} (t : Slots n) (a : Fin n) : Prop :=
  ∃ i, t i = some a

def Unique {n : Nat} (t : Slots n) : Prop :=
  ∀ i j a, t i = some a → t j = some a → i = j

def Covers {p c n : Nat} (x : Config p c n) (t : Slots n) : Prop :=
  ∀ i, (t i).isSome = (x i).mark

def move {n : Nat} (t : Slots n) (e : Fin n) : Slots n :=
  fun i => if i = e then none else
    if i = rightNeighbor e then (t i).or (t e) else t i

def slotsStep {p c n : Nat} (x : Config p c n) (t : Slots n) (e : Fin n) : Slots n :=
  if geometricPay (x e) (x (rightNeighbor e)) then move t e else t

def lostStep {p c n : Nat} (x : Config p c n) (t : Slots n) (e : Fin n) : Option (Fin n) :=
  if retirement x e then t e else none

private theorem notLoop {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

theorem init_covers {p c n : Nat} (x : Config p c n) : Covers x (initSlots x) := by
  intro i
  cases h : (x i).mark <;> simp [initSlots,h]

theorem init_unique {p c n : Nat} (x : Config p c n) : Unique (initSlots x) := by
  intro i j a hi hj
  unfold initSlots at hi hj
  split at hi <;> split at hj <;> simp_all

/-- This equation uses the real paid row, including its having tested
post-native leader. Type changes alone never touch a slot. -/
theorem physical_slots {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (t : Slots n) (e : Fin n) (hm : MCOV x) (ht : Covers x t) :
    Covers (step x e) (slotsStep x t e) := by
  intro i
  rw [covered_step_mark hn x hm]
  by_cases h : geometricPay (x e) (x (rightNeighbor e)) = true
  · simp only [slotsStep,h,if_true]
    have hE : (t e).isSome = true := (ht e).trans (RearTrace.paid_was_marked hm e h)
    cases hh : t e with
    | none => simp [hh] at hE
    | some a =>
      by_cases hi : i = e
      · simp [move,hi]
      · by_cases hj : i = rightNeighbor e
        · subst i
          cases hk : t (rightNeighbor e) <;> simp [move,hi,hh,hk]
        · simp [move,hi,hj,ht i]
  · have hh : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr h
    simp [slotsStep,hh,ht i]

private theorem move_origin {n : Nat} (t : Slots n) (e i a : Fin n)
    (h : move t e i = some a) :
    (i ≠ e ∧ t i = some a) ∨
      (i = rightNeighbor e ∧ t (rightNeighbor e) = none ∧ t e = some a) := by
  unfold move at h
  split at h
  · simp at h
  · rename_i he
    split at h
    · rename_i hh
      subst i
      cases hR : t (rightNeighbor e) with
      | none => exact .inr ⟨rfl,rfl,by simpa [hR,Option.or] using h⟩
      | some b => exact .inl ⟨he,by simpa [hR,Option.or] using h⟩
    · exact .inl ⟨he,h⟩

theorem step_unique {p c n : Nat} (x : Config p c n) (t : Slots n) (e : Fin n)
    (h : Unique t) : Unique (slotsStep x t e) := by
  unfold slotsStep
  split
  · intro i j a hi hj
    rcases move_origin t e i a hi with ⟨hiE,hi⟩ | ⟨hiR,_,hi⟩ <;>
      rcases move_origin t e j a hj with ⟨hjE,hj⟩ | ⟨hjR,_,hj⟩
    · exact h _ _ _ hi hj
    · exact (hiE (h _ _ _ hi hj)).elim
    · exact (hjE (h _ _ _ hj hi)).elim
    · exact hiR.trans hjR.symm
  · exact h

/-- A tag survives the mark exactly when it was present and is not the
lost mover. A resident remains even on a type change or a merger. -/
theorem occupied_step {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (t : Slots n)
    (e a : Fin n) (ht : Covers x t) (hu : Unique t) :
    occupied (slotsStep x t e) a ↔ occupied t a ∧ lostStep x t e ≠ some a := by
  let r := rightNeighbor e
  have hr : r ≠ e := notLoop hn e
  by_cases hP : geometricPay (x e) (x r) = true
  · cases hR : t r with
    | none =>
      have hmr : (x r).mark = false := by simpa [hR] using (ht r).symm
      have hl : lostStep x t e = none := by simp [lostStep,retirement,hP,hmr,r]
      rw [show slotsStep x t e = move t e by simp [slotsStep,hP,r],hl]
      constructor
      · rintro ⟨i,hi⟩
        rcases move_origin t e i a hi with ⟨_,h⟩ | ⟨_,_,h⟩
        · exact ⟨⟨i,h⟩,by simp⟩
        · exact ⟨⟨e,h⟩,by simp⟩
      · rintro ⟨⟨i,hi⟩,_⟩
        by_cases hiE : i = e
        · subst i
          exact ⟨r,by simpa [move,hr,r,hR,Option.or] using hi⟩
        · have hiR : i ≠ r := by intro h; subst i; simp [hR] at hi
          exact ⟨i,by simpa [move,hiE,hiR,r] using hi⟩
    | some b =>
      have hmr : (x r).mark = true := by simpa [hR] using (ht r).symm
      have hl : lostStep x t e = t e := by simp [lostStep,retirement,hP,hmr,r]
      rw [show slotsStep x t e = move t e by simp [slotsStep,hP,r],hl]
      constructor
      · rintro ⟨i,hi⟩
        rcases move_origin t e i a hi with ⟨hiE,h⟩ | ⟨_,heem,_⟩
        · exact ⟨⟨i,h⟩,fun he => hiE (hu _ _ _ h he)⟩
        · simp [r,hR] at heem
      · rintro ⟨⟨i,hi⟩,he⟩
        have hiE : i ≠ e := by intro hh; subst i; exact he hi
        by_cases hiR : i = r
        · subst i
          exact ⟨r,by simpa [move,hr,r,hR,Option.or] using hi⟩
        · exact ⟨i,by simpa [move,hiE,hiR,r] using hi⟩
  · have hF : geometricPay (x e) (x r) = false := Bool.eq_false_iff.mpr hP
    simp [slotsStep,lostStep,retirement,hF,r]

/-- A nonretiring root keeps its tag on N2/P5 type changes. On a
paid native death its old tag is looked up *after* movement; the
foreign resident is never mistaken for the deceased mover. -/
theorem paid_mover_or_resident {n : Nat} (hn : 4 ≤ n) (t : Slots n) (e : Fin n) :
    move t e e = none ∧
      move t e (rightNeighbor e) = (t (rightNeighbor e)).or (t e) := by
  simp [move,notLoop hn e]


structure Ledger (p c n : Nat) where
  config : Config p c n
  slots : Slots n
  losses : List (Fin n)

def initial {p c n : Nat} (x : Config p c n) : Ledger p c n := ⟨x,initSlots x,[]⟩

def advance {p c n : Nat} (z : Ledger p c n) (e : Fin n) : Ledger p c n :=
  ⟨step z.config e, slotsStep z.config z.slots e, (lostStep z.config z.slots e).toList ++ z.losses⟩

def observe {p c n : Nat} (z : Ledger p c n) (w : List (Fin n)) : Ledger p c n :=
  w.foldl advance z

theorem observe_config {p c n : Nat} (z : Ledger p c n) (w : List (Fin n)) :
    (observe z w).config = run z.config w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    change (observe (advance z e) w).config = run (step z.config e) w
    exact ih _

theorem retire_count {p c n : Nat} (x : Config p c n) (t : Slots n)
    (e : Fin n) (hm : MCOV x) (ht : Covers x t) :
    (lostStep x t e).toList.length = (retirement x e).toNat := by
  by_cases h : retirement x e = true
  · have hp : geometricPay (x e) (x (rightNeighbor e)) = true :=
      (Bool.and_eq_true_iff.mp h).1
    have hE : (t e).isSome = true := (ht e).trans (RearTrace.paid_was_marked hm e hp)
    cases hse : t e with
    | none => simp [hse] at hE
    | some a => simp [lostStep,h,hse]
  · have hR : retirement x e = false := Bool.eq_false_iff.mpr h
    simp [lostStep,hR]

structure Valid {p c n : Nat} (z : Ledger p c n) (x : Config p c n) : Prop where
  markCover : MCOV z.config
  sourceCover : COV z.config
  covers : Covers z.config z.slots
  unique : Unique z.slots
  inventory : ∀ a, occupied z.slots a ↔ (x a).mark = true ∧ a ∉ z.losses
  no_repeat : z.losses.Nodup
  count : rank z.config + z.losses.length = rank x

theorem valid_init {p c n : Nat} (x : Config p c n) (hm : MCOV x) (hc : COV x) :
    Valid (initial x) x := by
  refine ⟨hm,hc,init_covers x,init_unique x,?_,by simp [initial],by simp [initial]⟩
  intro a
  constructor
  · rintro ⟨i,hi⟩
    unfold initial initSlots at hi
    simp only at hi
    split at hi <;> simp_all [initial]
  · intro h
    exact ⟨a,by simp [initial,initSlots,h.1]⟩

theorem valid_step {p c n : Nat} (hn : 4 ≤ n) (z : Ledger p c n) (x : Config p c n)
    (e : Fin n) (hz : Valid z x) : Valid (advance z e) x := by
  let gone := lostStep z.config z.slots e
  have hCov := EntranceCover.cover_closed hn z.config e ⟨hz.markCover,hz.sourceCover⟩
  refine ⟨hCov.1,hCov.2,physical_slots hn _ _ _ hz.markCover hz.covers,
    step_unique _ _ _ hz.unique,?_,?_,?_⟩
  · intro a
    change occupied (slotsStep z.config z.slots e) a ↔ (x a).mark = true ∧ a ∉ gone.toList ++ z.losses
    rw [occupied_step hn _ _ _ _ hz.covers hz.unique,hz.inventory]
    change (((x a).mark = true ∧ a ∉ z.losses) ∧ gone ≠ some a) ↔ _
    cases gone with
    | none => simp
    | some b =>
      simp only [Option.toList,List.singleton_append,List.mem_cons,not_or]
      constructor
      · rintro ⟨⟨hm,hn⟩,hh⟩
        exact ⟨hm,fun h => hh (congrArg some h.symm),hn⟩
      · rintro ⟨hm,hh,hn⟩
        exact ⟨⟨hm,hn⟩,fun h => hh ((Option.some.inj h).symm)⟩
  · change (gone.toList ++ z.losses).Nodup
    cases h : gone with
    | none => simpa [h] using hz.no_repeat
    | some a =>
      have he : retirement z.config e = true := by
        cases hc : retirement z.config e
        · exfalso; simp [gone,lostStep,hc] at h
        · rfl
      have ha : z.slots e = some a := by simpa [gone,lostStep,he] using h
      have hv := (hz.inventory a).mp ⟨e,ha⟩
      simpa [h] using And.intro hv.2 hz.no_repeat
  · have r := rank_step hn z.config e hz.markCover
    have hlen := retire_count z.config z.slots e hz.markCover hz.covers
    have hcount := hz.count
    change rank (step z.config e) + (gone.toList ++ z.losses).length = rank x
    rw [List.length_append,show gone.toList.length = _ from hlen]
    omega

theorem valid_word {p c n : Nat} (hn : 4 ≤ n) (z : Ledger p c n) (x : Config p c n)
    (w : List (Fin n)) (h : Valid z x) : Valid (observe z w) x := by
  induction w generalizing z with
  | nil => exact h
  | cons e w ih =>
    exact ih _ (valid_step hn z x e h)

theorem loss_monotone {p c n : Nat} (z : Ledger p c n) (w : List (Fin n)) (a : Fin n) :
    a ∈ z.losses → a ∈ (observe z w).losses := by
  induction w generalizing z with
  | nil => exact id
  | cons e w ih => intro ha; exact ih (advance z e) (List.mem_append_right _ ha)

def hit {n : Nat} (lost group : List (Fin n)) : Bool :=
  lost.any (fun a => group.contains a)

def hits {n : Nat} (lost : List (Fin n)) (groups : List (List (Fin n))) : Nat :=
  (groups.map (fun g => (hit lost g).toNat)).sum

private theorem hits_cons_loss {n : Nat} (a : Fin n) (losses : List (Fin n))
    (groups : List (List (Fin n))) :
    hits (a::losses) groups ≤ hits [a] groups + hits losses groups := by
  induction groups with
  | nil => simp [hits]
  | cons g gs ih =>
    have h : (g.contains a || hit losses g).toNat ≤ (g.contains a).toNat + (hit losses g).toNat := by
      cases g.contains a <;> cases hit losses g <;> decide
    simp only [hits,List.map_cons,List.sum_cons] at *
    have h1 : hit [a] g = g.contains a := by simp [hit]
    have h2 : hit (a::losses) g = (g.contains a || hit losses g) := by simp [hit]
    rw [h1,h2]
    omega

/-- Pointwise incidence (including overlapping windows). The only
combinatorial premise is the multiplicity bound for each original id;
the schedule need not be independent between the windows. -/
theorem hits_le_seven_losses {n : Nat} (losses : List (Fin n))
    (groups : List (List (Fin n))) (h7 : ∀ a, hits [a] groups ≤ 7) :
    hits losses groups ≤ 7*losses.length := by
  induction losses with
  | nil =>
    have hh : (groups.map fun g => (hit [] g).toNat) = groups.map (fun _ => 0) := by rfl
    unfold hits
    rw [hh]
    clear h7 hh
    induction groups with
    | nil => simp
    | cons _ gs ih => simpa using ih
  | cons a losses ih =>
    have h := hits_cons_loss a losses groups
    have ha := h7 a
    simp only [List.length_cons]
    omega

/-- Actual incidence inequality on the literal raw word. Birth/kill
without geometric coalescence do not count as losses, and a merger
outside a group cannot make its indicator fire. -/
theorem physical_incidence {p c n : Nat} (x : Config p c n)
    (hn : 4 ≤ n) (hm : MCOV x) (hc : COV x) (w : List (Fin n))
    (groups : List (List (Fin n))) (h7 : ∀ a, hits [a] groups ≤ 7) :
    7 * rank (run x w) + hits (observe (initial x) w).losses groups ≤ 7 * rank x := by
  have hv := valid_word hn (initial x) x w (valid_init x hm hc)
  have hr := hv.count
  rw [observe_config] at hr
  have h := hits_le_seven_losses (observe (initial x) w).losses groups h7
  change 7 * rank (run x w) + hits (observe (initial x) w).losses groups ≤ _
  have he : (initial x).config = x := rfl
  rw [he] at hr
  omega

#print axioms physical_slots
#print axioms occupied_step
#print axioms valid_word
#print axioms physical_incidence


def window7 {n k : Nat} (roster : Fin k → Fin n) (i : Fin k) : List (Fin n) :=
  (List.finRange 7).map fun j => roster (liftedSite i j.val)

private theorem translate_injective {k : Nat} (j : Nat) {u v : Fin k}
    (h : liftedSite u j = liftedSite v j) : u = v := by
  induction j with
  | zero => simpa [liftedSite_zero] using h
  | succ j ih =>
    rw [liftedSite_succ,liftedSite_succ] at h
    exact ih (FreshSeparation.succ_inj h)

private theorem hits_filtered_starts {n k : Nat} (roster : Fin k → Fin n)
    (starts : List (Fin k)) (a : Fin n) :
    hits [a] (starts.map (window7 roster)) =
      (starts.filter (fun i => (window7 roster i).contains a)).length := by
  induction starts with
  | nil => rfl
  | cons i starts ih =>
    change (hit [a] (window7 roster i)).toNat + hits [a] (starts.map (window7 roster)) = _
    rw [ih,show hit [a] (window7 roster i) = (window7 roster i).contains a by simp [hit],List.filter_cons]
    cases (window7 roster i).contains a <;> simp only [Bool.false_eq_true,if_false,if_true,
      Bool.toNat_false,Bool.toNat_true,List.length_cons] <;> omega

/-- Among any nonduplicated collection of cyclic starts, an original
tag can occur in at most seven seven-windows. No regular-gap premise;
filtering for short spans is allowed. This uses exactly seven offsets
even when all seven windows have the same membership at rank seven. -/
theorem windows7_multiplicity {n k : Nat} (roster : Fin k → Fin n)
    (inj : ∀ i j, roster i = roster j → i = j)
    (starts : List (Fin k)) (hs : starts.Nodup) (a : Fin n) :
    hits [a] (starts.map (window7 roster)) ≤ 7 := by
  classical
  let findStart : Fin 7 → Option (Fin k) := fun j =>
    if hh : ∃ i : Fin k, roster (liftedSite i j.val) = a
    then some (Classical.choose hh) else none
  let possibles := (List.finRange 7).filterMap findStart
  have hi : (starts.filter (fun i => (window7 roster i).contains a)) ⊆ possibles := by
    intro i hi
    have hg : a ∈ window7 roster i := List.contains_iff_mem.mp (List.mem_filter.mp hi).2
    obtain ⟨j,hj,hEq⟩ := List.mem_map.mp hg
    apply List.mem_filterMap.mpr
    refine ⟨j,hj,?_⟩
    have h : ∃ i : Fin k, roster (liftedSite i j.val) = a := ⟨i,hEq⟩
    dsimp only [findStart]
    rw [dif_pos h]
    congr 1
    exact translate_injective j.val (inj _ _ ((Classical.choose_spec h).trans hEq.symm))
  rw [hits_filtered_starts]
  exact Nat.le_trans ((List.Nodup.sublist List.filter_sublist hs).length_le_of_subset hi)
    (by simpa [possibles] using List.length_filterMap_le findStart (List.finRange 7))

theorem physical_windows7_incidence {p c n k : Nat} (x : Config p c n)
    (hn : 4 ≤ n) (hm : MCOV x) (hc : COV x) (w : List (Fin n))
    (roster : Fin k → Fin n) (inj : ∀ i j, roster i = roster j → i = j)
    (starts : List (Fin k)) (hs : starts.Nodup) :
    7 * rank (run x w) +
      hits (observe (initial x) w).losses (starts.map (window7 roster)) ≤ 7 * rank x :=
  physical_incidence x hn hm hc w _ (windows7_multiplicity roster inj starts hs)

#print axioms windows7_multiplicity
#print axioms physical_windows7_incidence

/-- A native death is charged from the old responder slot. If P3 runs
on the same mark, the victim is either the moved ghost at the next site,
or the lost mover; it is never the surviving resident at the landing site. -/
theorem native_death_tag_outcome {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (t : Slots n) (e : Fin n) (hm : MCOV x) (hc : COV x)
    (ht : Covers x t) (hu : Unique t)
    (hL : (x (rightNeighbor e)).leader = true)
    (hd : TenureOrigins.nativeKill (x e) (x (rightNeighbor e))) :
    ∃ a, t e = some a ∧ (step x e (rightNeighbor e)).leader = false ∧
      ((slotsStep x t e e = some a ∧ lostStep x t e = none) ∨
       (slotsStep x t e (rightNeighbor e) = some a ∧ lostStep x t e = none ∧
         (step x e (rightNeighbor (rightNeighbor e))).leader = false) ∨
       (lostStep x t e = some a ∧ ¬ occupied (slotsStep x t e) a)) := by
  let r := rightNeighbor e
  have hr : r ≠ e := notLoop hn e
  have he' := (ht e).trans (hm e (.inl hL))
  have hDead := (TenureOrigins.covered_ring_leader_loss_iff x e hr hc hL).mpr hd
  cases ha : t e with
  | none => simp [ha] at he'
  | some a =>
    refine ⟨a,rfl,hDead,?_⟩
    by_cases hp : geometricPay (x e) (x r) = true
    · cases hz : t r with
      | none =>
        have hM : (x r).mark = false := by simpa [hz] using (ht r).symm
        have hNL : (x (rightNeighbor r)).leader = false := by
          cases h : (x (rightNeighbor r)).leader
          · rfl
          · have h' := hm r (.inl h)
            simp [hM] at h'
        have hN1 : rightNeighbor r ≠ r := notLoop hn r
        have hN0 : rightNeighbor r ≠ e := by
          intro he
          have h : liftedSite e 2 = liftedSite e 0 := by
            simpa [liftedSite_succ,liftedSite_zero,r] using he
          have hh := liftedSite_inj e (by omega : 2<n) (by omega : 0<n) h
          omega
        apply Or.inr; apply Or.inl
        refine ⟨?_,?_,?_⟩
        · simpa [slotsStep,hp,r] using
            (show move t e r = some a by simp [move,hr,r,hz,ha,Option.or])
        · simp [lostStep,retirement,hp,r,hM]
        · simpa [step,r,hN0,hN1] using hNL
      | some b =>
        have hM : (x r).mark = true := by simpa [hz] using (ht r).symm
        have hGone : lostStep x t e = some a := by simp [lostStep,retirement,hp,r,hM,ha]
        exact .inr (.inr ⟨hGone,fun h =>
          ((occupied_step hn x t e a ht hu).mp h).2 hGone⟩)
    · have hF : geometricPay (x e) (x r) = false := Bool.eq_false_iff.mpr hp
      exact .inl ⟨by simp [slotsStep,hF,r,ha],by simp [lostStep,retirement,hF,r]⟩

#print axioms native_death_tag_outcome
end L4.SevenTagCharge
