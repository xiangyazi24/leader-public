import Leader.L4.FreshTimerEpoch

/-! The fixed ghost's upstream rail (top at slot 0, door at slot h−1).
The proof-side phase is not part of a protocol state. -/
namespace L4.FreshEpochAuthentication
open FreshTimerEpoch

def Clean (a : Rail) : Prop := a = .e ∨ a = .t ∨ a = .x

macro "proveClean" : tactic => `(tactic| first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))

def Outbound {h : Nat} (r : Fin h → Rail) (p : Fin h) : Prop :=
  r p = .ui ∧ ∀ i : Fin h, p.val < i.val → Clean (r i)

def Inbound {h : Nat} (r : Fin h → Rail) (p : Fin h) : Prop :=
  r p = .di ∧ (∀ i : Fin h, i.val < p.val → r i = .e) ∧
    (∀ i : Fin h, p.val < i.val → Clean (r i))

def Lost {h : Nat} (r : Fin h → Rail) : Prop := ∀ i, Clean (r i)

abbrev Piece {Q : Nat} (a b : Rail) := patrol false false false (.off : Source Q) a b

theorem clean_pair {Q : Nat} (a b : Rail) (ha : Clean a) (hb : Clean b) :
    Clean (Piece (Q := Q) a b).left ∧ Clean (Piece (Q := Q) a b).right := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> constructor <;> proveClean

theorem empty_pair {Q : Nat} :
    (Piece (Q := Q) .e .e).left = .e ∧ (Piece (Q := Q) .e .e).right = .e := ⟨rfl,rfl⟩

/-- An edge on the door-side of an outward front cannot move it
inward or introduce a return there, even if that suffix contains X. -/
theorem ui_waits_on_right {Q : Nat} (r : Rail) (h : Clean r) :
    (Piece (Q := Q) .ui r).left = .ui ∧ Clean (Piece (Q := Q) .ui r).right := by
  rcases h with rfl | rfl | rfl <;> refine ⟨rfl,?_⟩ <;> proveClean

/-- There is no returning-particle movement across the back of a
genuine return. Its top-side empty sheet stays empty. -/
theorem di_waits_on_left {Q : Nat} :
    (Piece (Q := Q) .e .di).left = .e ∧ (Piece (Q := Q) .e .di).right = .di :=
  ⟨rfl,rfl⟩

/-- The old pair right boundary is the fixed supplier/turn. It cannot
create Ui or Di in an already empty slot. -/
theorem top_empty {Q : Nat} (l : Rail) :
    (patrol true false true (.off : Source Q) l .e).right = .e := by
  cases l <;> rfl

theorem top_clean {Q : Nat} (l r : Rail) (h : Clean r) :
    Clean (patrol true false true (.off : Source Q) l r).right := by
  rcases h with rfl | rfl | rfl <;> cases l <;> proveClean

/-- Door I1 on E or X relaunches initialization. On T it waits.
None of these suffix letters can authorize A1. -/
theorem door_clean {Q : Nat} (l r : Rail) (hl : Clean l) :
    let out := patrol true true false (.i1 : Source Q) l r
    out.source = .i1 ∧ out.fire = false ∧
      (out.left = .ui ∨ Clean out.left) := by
  rcases hl with rfl | rfl | rfl <;> cases r <;> refine ⟨rfl,rfl,?_⟩ <;> first | exact Or.inl rfl | apply Or.inr; proveClean

theorem door_front_holds {Q : Nat} (r : Rail) :
    let out := patrol true true false (.i1 : Source Q) .ui r
    out.source = .i1 ∧ out.left = .ui ∧ out.fire = false := by
  cases r <;> exact ⟨rfl,rfl,rfl⟩

#print axioms clean_pair
#print axioms ui_waits_on_right
#print axioms top_clean
#print axioms door_clean


inductive Auth {h : Nat} (r : Fin h → Rail) : Prop where
  | out (p : Fin h) : Outbound r p → Auth r
  | back (p : Fin h) : Inbound r p → Auth r
  | lost : Lost r → Auth r

def put {h : Nat} (r : Fin h → Rail) (p : Fin h) (v : Rail) : Fin h → Rail :=
  fun i => if i=p then v else r i

def body {Q h : Nat} (r : Fin h → Rail) (a b : Fin h) : Fin h → Rail :=
  let o := Piece (Q := Q) (r a) (r b)
  put (put r a o.left) b o.right

private theorem clean_ui_tail (l : Rail) : Clean (if l == .x then .x else .t) := by
  cases l <;> proveClean

/-- Every ordinary selected bond preserves the proof-side
authentication state. A broken return enters the clean failed state;
its next door launch is a fresh epoch of the same fixed gap. -/
theorem body_preserves {Q h : Nat} (r : Fin h → Rail) (a b : Fin h)
    (adj : a.val+1=b.val) (H : Auth r) : Auth (body (Q := Q) r a b) := by
  have hab : a ≠ b := by
    intro he
    have hh := congrArg Fin.val he
    omega
  let o := Piece (Q := Q) (r a) (r b)
  let r' := body (Q := Q) r a b
  have hA : r' a = o.left := by simp [r',body,put,hab,o]
  have hB : r' b = o.right := by simp [r',body,put,o]
  have hOff (i : Fin h) (ha : i ≠ a) (hb : i ≠ b) : r' i = r i := by
    simp [r',body,put,ha,hb]
  have fixed_side (p : Fin h) (g : ∀ i : Fin h, p.val < i.val → Clean (r i))
      (h0 : p.val < a.val) :
      ∀ i : Fin h, p.val < i.val → Clean (r' i) := by
    have hh := clean_pair (Q := Q) (r a) (r b) (g a h0) (g b (by omega))
    intro i hi
    by_cases ha : i=a
    · subst i; rw [hA]; exact hh.1
    · by_cases hb : i=b
      · subst i; rw [hB]; exact hh.2
      · rw [hOff i ha hb]; exact g i hi
  change Auth r'
  cases H with
  | lost hall =>
    apply Auth.lost
    have hh := clean_pair (Q := Q) (r a) (r b) (hall a) (hall b)
    intro i
    by_cases ha : i=a
    · subst i; rw [hA]; exact hh.1
    · by_cases hb : i=b
      · subst i; rw [hB]; exact hh.2
      · rw [hOff _ ha hb]; exact hall i
  | out p hP =>
    obtain ⟨hp,hTail⟩ := hP
    by_cases ha : a=p
    · subst a
      have ho : o.left = .ui ∧ Clean o.right := by
        simpa [o,hp] using ui_waits_on_right (Q := Q) (r b) (hTail b (by omega))
      refine Auth.out p ⟨hA.trans ho.1,?_⟩
      intro i hi
      by_cases hb : i=b
      · subst i; rw [hB]; exact ho.2
      · rw [hOff i (fun h => by subst i; omega) hb]; exact hTail i hi
    · by_cases hb : b=p
      · subst b
        have ho := ui_crosses_dirty (Q := Q) (r a)
        have ho' : o.left = .ui ∧ Clean o.right := by
          simpa [o,hp,ho.1,ho.2.1] using clean_ui_tail (r a)
        refine Auth.out a ⟨hA.trans ho'.1,?_⟩
        intro i hi
        by_cases hb : i=p
        · subst i; rw [hB]; exact ho'.2
        · rw [hOff i (fun ha => by subst i; omega) hb]
          have hn : i.val ≠ p.val := fun he => hb (Fin.ext he)
          exact hTail i (by omega)
      · have hP' : r' p = .ui := (hOff _ (Ne.symm ha) (Ne.symm hb)).trans hp
        refine Auth.out p ⟨hP',?_⟩
        by_cases h0 : p.val < a.val
        · exact fixed_side p hTail h0
        · intro i hi
          have hp0 : p.val ≠ a.val := fun he => ha (Fin.ext he.symm)
          have hp1 : p.val ≠ b.val := fun he => hb (Fin.ext he.symm)
          rw [hOff i (fun he => by subst i; omega) (fun he => by subst i; omega)]
          exact hTail i hi
  | back p hP =>
    obtain ⟨hp,hPre,hTail⟩ := hP
    by_cases ha : a=p
    · subst a
      have hc := hTail b (by omega)
      rcases hc with hh | hh | hh
      · have ho := di_clean_return (Q := Q) (r b) (Or.inl hh)
        have ho' : o.left = .e ∧ o.right = .di := by simpa [o,hp] using And.intro ho.1 ho.2.1
        refine Auth.back b ⟨hB.trans ho'.2,?_,?_⟩
        · intro i hi
          by_cases hEq : i=p
          · subst i; exact hA.trans ho'.1
          · have hn : i.val ≠ p.val := fun he => hEq (Fin.ext he)
            rw [hOff i hEq (fun he => by subst i; omega)]
            exact hPre i (by omega)
        · intro i hi
          rw [hOff i (fun he => by subst i; omega) (fun he => by subst i; omega)]
          exact hTail i (by omega)
      · have ho := di_clean_return (Q := Q) (r b) (Or.inr hh)
        have ho' : o.left = .e ∧ o.right = .di := by simpa [o,hp] using And.intro ho.1 ho.2.1
        refine Auth.back b ⟨hB.trans ho'.2,?_,?_⟩
        · intro i hi
          by_cases hEq : i=p
          · subst i; exact hA.trans ho'.1
          · have hn : i.val ≠ p.val := fun he => hEq (Fin.ext he)
            rw [hOff i hEq (fun he => by subst i; omega)]
            exact hPre i (by omega)
        · intro i hi
          rw [hOff i (fun he => by subst i; omega) (fun he => by subst i; omega)]
          exact hTail i (by omega)
      · have ho : o.left = .e ∧ o.right = .x := by simp [o,hp,hh,di_meets_break.1,di_meets_break.2.1]
        apply Auth.lost
        intro i
        by_cases h1 : i=p
        · subst i; exact Or.inl (hA.trans ho.1)
        · by_cases h2 : i=b
          · subst i; exact Or.inr (Or.inr (hB.trans ho.2))
          · rw [hOff i h1 h2]
            by_cases h3 : i.val < p.val
            · exact Or.inl (hPre i h3)
            · have hn : i.val ≠ p.val := fun he => h1 (Fin.ext he)
              exact hTail i (by omega)
    · by_cases hb : b=p
      · subst b
        have hf : r a = .e := hPre a (by omega)
        have ho : o.left = .e ∧ o.right = .di := by
          simpa [o,hf,hp] using di_waits_on_left (Q := Q)
        refine Auth.back p ⟨hB.trans ho.2,?_,?_⟩
        · intro i hi
          by_cases h1 : i=a
          · subst i; exact hA.trans ho.1
          · rw [hOff i h1 (fun h => by subst i; omega)]; exact hPre i hi
        · intro i hi
          rw [hOff i (fun h => by subst i; omega) (fun h => by subst i; omega)]
          exact hTail i hi
      · refine Auth.back p ⟨(hOff _ (Ne.symm ha) (Ne.symm hb)).trans hp,?_,?_⟩
        have h0 : a.val ≠ p.val := fun he => ha (Fin.ext he)
        have h1 : b.val ≠ p.val := fun he => hb (Fin.ext he)
        · intro i hi
          by_cases ha' : i=a
          · subst i
            have ho : o.left = .e := by simp [o,hPre a hi,hPre b (by omega),empty_pair.1]
            exact hA.trans ho
          · by_cases hb' : i=b
            · subst i
              have ho : o.right = .e := by simp [o,hPre a (by omega),hPre b hi,empty_pair.2]
              exact hB.trans ho
            · rw [hOff i ha' hb']; exact hPre i hi
        · by_cases ht : p.val < a.val
          · exact fixed_side p hTail ht
          · intro i hi
            rw [hOff i (fun h => by subst i; omega) (fun h => by subst i; omega)]
            exact hTail i hi

#print axioms body_preserves


def top {Q h : Nat} (r : Fin h → Rail) (z : Fin h) (l : Rail) : Fin h → Rail :=
  put r z (patrol true false true (.off : Source Q) l (r z)).right

/-- The fixed supplier's incoming service turns only the front at the
top. The exterior slot is arbitrary and cannot inject a return. -/
theorem top_preserves {Q h : Nat} (r : Fin h → Rail) (z : Fin h)
    (hz : z.val=0) (l : Rail) (H : Auth r) : Auth (top (Q := Q) r z l) := by
  let r' := top (Q := Q) r z l
  let o := patrol true false true (.off : Source Q) l (r z)
  have hZ : r' z = o.right := by simp [r',o,top,put]
  have hOff (i : Fin h) (hi : i ≠ z) : r' i = r i := by simp [r',top,put,hi]
  change Auth r'
  cases H with
  | lost H =>
    apply Auth.lost
    intro i
    by_cases hi : i=z
    · subst i; rw [hZ]; exact top_clean l (r z) (H z)
    · rw [hOff i hi]; exact H i
  | out p H =>
    obtain ⟨hf,hT⟩ := H
    by_cases hp : p=z
    · subst p
      have hturn : o.right = .di := by
        change (patrol true false true (.off : Source Q) l (r z)).right = .di
        rw [hf]
        exact (ui_turns_at_root l).1
      refine Auth.back z ⟨hZ.trans hturn,?_,?_⟩
      · intro i hi; omega
      · intro i hi
        rw [hOff i (fun hh => by subst i; omega)]
        exact hT i hi
    · refine Auth.out p ⟨(hOff p hp).trans hf,?_⟩
      intro i hi
      rw [hOff i (fun hh => by subst i; omega)]
      exact hT i hi
  | back p H =>
    obtain ⟨hf,hP,hT⟩ := H
    have hTopKeep (q : Rail) (hx : q = .e ∨ q = .di) :
        (patrol true false true (.off : Source Q) l q).right = q := by
      rcases hx with rfl|rfl <;> cases l <;> rfl
    by_cases hp : p=z
    · subst p
      have ho : o.right = .di := (hTopKeep _ (Or.inr hf)).trans hf
      refine Auth.back z ⟨hZ.trans ho,?_,?_⟩
      · intro i hi; omega
      · intro i hi
        rw [hOff i (fun hh => by subst i; omega)]
        exact hT i hi
    · have hp' : p.val ≠ z.val := fun he => hp (Fin.ext he)
      have ho : o.right = .e := (hTopKeep _ (Or.inl (hP z (by omega)))).trans (hP z (by omega))
      refine Auth.back p ⟨(hOff p hp).trans hf,?_,?_⟩
      · intro i hi
        by_cases hz' : i=z
        · subst i; exact hZ.trans ho
        · rw [hOff i hz']; exact hP i hi
      · intro i hi
        rw [hOff i (fun he => by subst i; omega)]
        exact hT i hi

/-- A true A1 is characterized by the owned return at the last slot,
and all prior slots are then empty. No old Di can satisfy this guard. -/
theorem door_di_authenticated {h : Nat} (r : Fin h → Rail) (d : Fin h)
    (hd : d.val+1=h) (H : Auth r) (hdi : r d = .di) :
    Inbound r d := by
  cases H with
  | lost h =>
    specialize h d
    simp [Clean,hdi] at h
  | out p H =>
    obtain ⟨hp,hT⟩ := H
    by_cases he : d=p
    · rw [he,hp] at hdi
      contradiction
    · have hn : d.val ≠ p.val := fun he' => he (Fin.ext he')
      have hC := hT d (by have := p.isLt; omega)
      simp [Clean,hdi] at hC
  | back p H =>
    by_cases he : d=p
    · simpa [he] using H
    · have hn : d.val ≠ p.val := fun he' => he (Fin.ext he')
      have hC := H.2.2 d (by have := p.isLt; omega)
      simp [Clean,hdi] at hC

#print axioms top_preserves
#print axioms door_di_authenticated


/-- After entering I1 by the real L1 row, the door slot contains Ui
and there is no door-side suffix to confirm. -/
theorem launch_authenticated {h : Nat} (r : Fin h → Rail) (d : Fin h)
    (hd : d.val+1=h) (hL : r d = .ui) : Auth r := by
  refine Auth.out d ⟨hL,?_⟩
  intro i hi
  have := i.isLt
  omega

def door {Q h : Nat} (r : Fin h → Rail) (d : Fin h) (exterior : Rail) : Patrol Q :=
  patrol true true false .i1 (r d) exterior

/-- Literal door step. It either waits/relaunches without accepting A1,
or consumes the matching Di and immediately installs count-zero Uc.
A successful A1 has an entirely empty earlier path. -/
theorem door_transition {Q h : Nat} (hQ : 0<Q) (r : Fin h → Rail) (d : Fin h)
    (hd : d.val+1=h) (exterior : Rail) (H : Auth r) :
    let o := door (Q := Q) r d exterior
    let r' := put r d o.left
    (o.source = .i1 ∧ o.fire = false ∧ Auth r') ∨
      (Inbound r d ∧ o.source = .await ⟨0,hQ⟩ ∧
        o.fire = false ∧ r' d = .uc ∧
        ∀ i : Fin h, i.val < d.val → r' i = .e) := by
  let o := door (Q := Q) r d exterior
  let r' := put r d o.left
  have hD : r' d = o.left := by simp [r',put]
  have hStay (i : Fin h) (hi : i ≠ d) : r' i = r i := by simp [r',put,hi]
  change (o.source = .i1 ∧ o.fire = false ∧ Auth r') ∨ _
  by_cases hDi : r d = .di
  · have hAuth := door_di_authenticated r d hd H hDi
    have hP := a1_accepts_and_launches (Q := Q) hQ exterior
    have hLift : o.source = .await ⟨0,hQ⟩ ∧ o.left = .uc ∧ o.fire = false := by
      simpa [o,door,hDi] using hP
    refine Or.inr ⟨hAuth,hLift.1,hLift.2.2,hD.trans hLift.2.1,?_⟩
    intro i hi
    change r' i = .e
    rw [hStay i (fun he => by subst i; omega)]
    exact hAuth.2.1 i hi
  · have hLift : o.source = .i1 ∧ o.fire = false ∧
        (o.left = .ui ∨ Clean o.left) := by
      by_cases hUi : r d = .ui
      · have hP := door_front_holds (Q := Q) exterior
        have hZ : o.source = .i1 ∧ o.left = .ui ∧ o.fire = false := by
          simpa [o,door,hUi] using hP
        exact ⟨hZ.1,hZ.2.2,Or.inl hZ.2.1⟩
      · have hC : Clean (r d) := by
          cases H with
          | lost H => exact H d
          | out p H =>
            have hn : d ≠ p := fun he => hUi (he.symm ▸ H.1)
            have hn' : d.val ≠ p.val := fun he => hn (Fin.ext he)
            exact H.2 d (by have := p.isLt; omega)
          | back p H =>
            have hn : d ≠ p := fun he => hDi (he.symm ▸ H.1)
            have hn' : d.val ≠ p.val := fun he => hn (Fin.ext he)
            exact H.2.2 d (by have := p.isLt; omega)
        exact door_clean _ _ hC
    refine Or.inl ⟨hLift.1,hLift.2.1,?_⟩
    rcases hLift.2.2 with hUi | hClean
    · exact launch_authenticated r' d hd (hD.trans hUi)
    · have hClean' : Clean (r' d) := hD.symm ▸ hClean
      have forward_tail (p : Fin h) (HP : ∀ i : Fin h, p.val<i.val → Clean (r i)) :
          ∀ i : Fin h, p.val<i.val → Clean (r' i) := by
        intro i hi
        by_cases he : i=d
        · subst i; exact hClean'
        · rw [hStay i he]; exact HP i hi
      cases H with
      | lost H =>
        apply Auth.lost
        intro i
        by_cases he : i=d
        · subst i; exact hClean'
        · rw [hStay i he]; exact H i
      | out p H =>
        have hne : p ≠ d := by
          intro he
          subst p
          have hP := door_front_holds (Q := Q) exterior
          have hz : o.left = .ui := by simpa [o,door,H.1] using hP.2.1
          simp [Clean,hz] at hClean
        exact Auth.out p ⟨(hStay p hne).trans H.1,forward_tail p H.2⟩
      | back p H =>
        have hne : p ≠ d := fun he => hDi (he ▸ H.1)
        refine Auth.back p ⟨(hStay p hne).trans H.1,?_,forward_tail p H.2.2⟩
        intro i hi
        have hn : i ≠ d := by
          intro he
          subst i
          have := p.isLt
          omega
        rw [hStay i hn]
        exact H.2.1 i hi

#print axioms launch_authenticated
#print axioms door_transition


theorem prefix_payload {p c : Nat} (u v : Site p c) :
    (stepPrefix u v).1.rail = u.rail ∧ (stepPrefix u v).2.rail = v.rail ∧
      (stepPrefix u v).2.source = v.source := by
  have hp (a b : Site p c) :
      (payment a b).1.rail = a.rail ∧ (payment a b).2.rail = b.rail ∧
        (payment a b).2.source = b.source := by
    unfold payment
    split
    · exact ⟨rfl,rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl,rfl⟩
  have hm : (materialize u v).rail = u.rail := by unfold materialize; split <;> rfl
  have hi : (fireInitiator (materialize u v)).rail = u.rail := by
    unfold fireInitiator; split <;> exact hm
  have hr : (fireResponder v).rail = v.rail ∧ (fireResponder v).source = v.source := by
    unfold fireResponder
    split
    · cases v.signal <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  unfold stepPrefix native
  generalize fireInitiator (materialize u v) = a at hi ⊢
  generalize fireResponder v = b at hr ⊢
  have hI : (impact a b).1.rail = a.rail ∧ (impact a b).2.rail = b.rail ∧
      (impact a b).2.source = b.source := by
    unfold impact
    split
    · split <;> exact ⟨rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl⟩
  generalize impact a b = ab at hI ⊢
  rcases ab with ⟨a',b'⟩
  dsimp only at hI ⊢
  have hF (g : Bool) : (followerBullet g a' b').1.rail = a'.rail ∧
      (followerBullet g a' b').2.rail = b'.rail ∧ (followerBullet g a' b').2.source = b'.source := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl⟩
  have hh := hF (pinned a' b')
  generalize followerBullet (pinned a' b') a' b' = uv at hh ⊢
  rcases uv with ⟨u',v'⟩
  dsimp only at hh ⊢
  obtain ⟨h1,h2,h3⟩ := hh
  obtain ⟨hh1,hh2,hh3⟩ := hp
    {u' with signal := (Signal.max u'.signal
      (if v'.leader then .one else if pinned a' b' then .two else v'.signal))} v'
  exact ⟨hh1.trans (h1.trans (hI.1.trans hi)),
    hh2.trans (h2.trans (hI.2.1.trans hr.1)),
    hh3.trans (h3.trans (hI.2.2.trans hr.2))⟩

/-- Exact body R0/N/P pre-patrol geometry for an unmarked, coherent
bond into an ordinary responder. Its literal controller is OFF by COV. -/
theorem ordinary_prefix_flags {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) :
    (stepPrefix u v).1.mark = false ∧ (stepPrefix u v).2.leader = false := by
  have hma : materialize u v = u := by simp [materialize,defect,hm,hr,hl]
  have hI : (fireInitiator u).mark = false := by unfold fireInitiator; split <;> exact hm
  have hR : fireResponder v = v := by simp [fireResponder,hl]
  unfold stepPrefix native
  rw [hma,hR]
  generalize fireInitiator u = a at hI ⊢
  have hZ : impact a v = (a,v) := by simp [impact,hl]
  rw [hZ]
  dsimp only
  have hF (g : Bool) : (followerBullet g a v).1.mark = false ∧
      (followerBullet g a v).2.leader = false := by
    unfold followerBullet
    split
    · split <;> exact ⟨hI,hl⟩
    · exact ⟨hI,hl⟩
  have hh := hF (pinned a v)
  generalize followerBullet (pinned a v) a v = uv at hh ⊢
  rcases uv with ⟨a',b'⟩
  obtain ⟨ha,hb⟩ := hh
  dsimp only at ha hb ⊢
  simp only [payment,hb,ha,Bool.false_eq_true,if_false,Bool.not_false,Bool.true_and,
    Bool.false_and]
  split <;> split <;> exact ⟨rfl,by first | rfl | exact hb⟩

/-- Pairwise projection into the exact old-pair timer, on marks where no
P5 fires. Endpoint flags refer to the actual post-native/P3 stage. -/
theorem pair_projects_rails {p c : Nat} (u v : Site p c)
    (m l : Bool)
    (hm : (stepPrefix u v).1.mark = m) (hl : (stepPrefix u v).2.leader = l)
    (hF : (patrol (l || m) (!l && m) l v.source u.rail v.rail).fire = false) :
    let t := patrol (l || m) (!l && m) l v.source u.rail v.rail
    (pairStep u v).1.rail = t.left ∧ (pairStep u v).2.rail = t.right ∧
      (pairStep u v).2.source = t.source := by
  have hp := prefix_payload u v
  unfold pairStep
  generalize stepPrefix u v = uv at hp hm hl ⊢
  rcases uv with ⟨a,b⟩
  dsimp only at hp hm hl ⊢
  simp [patrolWrite,finishBirth,pinned,hp.1,hp.2.1,hp.2.2,hm,hl,hF]

/-- Body service has exactly the ordinary E/T/X–Ui/Di row used by the
array invariant, on every native/stock/patrol filler assignment. -/
theorem ordinary_pair_projects {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) (ho : v.source = .off) :
    let t := Piece (Q := 2*c) u.rail v.rail
    (pairStep u v).1.rail = t.left ∧ (pairStep u v).2.rail = t.right ∧
      (pairStep u v).2.source = t.source := by
  obtain ⟨hM,hL⟩ := ordinary_prefix_flags u v hm hr hl
  have hF : (patrol (false || false) (!false && false) false v.source u.rail v.rail).fire = false := by
    rw [ho]
    exact (patrol_unpinned_source_fire _ _ _ _ _).2
  have hh := pair_projects_rails u v false false hM hL hF
  simpa [ho] using hh

#print axioms pair_projects_rails
#print axioms ordinary_pair_projects


theorem top_pair_projects {p c : Nat} (u v : Site p c)
    (hl : v.leader = true) (ho : v.source = .off)
    (hn : ¬ TenureOrigins.nativeKill u v) :
    let t := patrol true false true (.off : Source (2*c)) u.rail v.rail
    (pairStep u v).1.rail = t.left ∧ (pairStep u v).2.rail = t.right ∧
      (pairStep u v).2.source = t.source := by
  let a := native (materialize u v) v
  have hL : a.2.leader = true := by
    cases hL : a.2.leader
    · exact False.elim (hn ((TenureOrigins.native_loses_leader_iff u v hl).mp hL))
    · rfl
  have hm : (stepPrefix u v).1.mark = true := by
    change (payment a.1 a.2).1.mark = true
    simp [payment,hL]
  have hL' : (stepPrefix u v).2.leader = true := by
    change (payment a.1 a.2).2.leader = true
    simp [payment,hL]
  have hF : (patrol (true || true) (!true && true) true v.source u.rail v.rail).fire = false :=
    (patrol_unpinned_source_fire _ _ _ _ _).2
  have hh := pair_projects_rails u v true true hm hL' hF
  simpa [ho] using hh

theorem native_preserves_mark {p c : Nat} (u v : Site p c) :
    (native u v).1.mark = u.mark := by
  have ha : (fireInitiator u).mark = u.mark := by unfold fireInitiator; split <;> rfl
  unfold native
  generalize fireInitiator u = a at ha ⊢
  generalize fireResponder v = b
  have hi : (impact a b).1.mark = a.mark := by unfold impact; split <;> rfl
  generalize impact a b = ab at hi ⊢
  rcases ab with ⟨l,r⟩
  have hf (g : Bool) : (followerBullet g l r).1.mark = l.mark := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  exact (hf _).trans (hi.trans ha)

theorem old_follower_native {p c : Nat} (u v : Site p c) (hl : v.leader=false) :
    (native u v).2.leader = false := by
  have hf : fireResponder v = v := by simp [fireResponder,hl]
  unfold native
  rw [hf]
  generalize fireInitiator u = a
  have hi : impact a v = (a,v) := by simp [impact,hl]
  rw [hi]
  dsimp only
  unfold followerBullet
  split
  · split <;> exact hl
  · exact hl

/-- Selected fixed-head door service under I1 and no P3 payment
is exactly the finite-array door step whenever authentication holds. -/
theorem unpaid_door_projects {p c h : Nat} (hQ : 0 < 2*c)
    (u v : Site p c) (r : Fin h → Rail) (d : Fin h)
    (hd : d.val+1=h) (hR : r d = u.rail) (hAuth : Auth r)
    (hm : u.mark = true) (hl : v.leader = false) (hs : v.source = .i1)
    (hp : geometricPay u v = false) :
    let t := door (Q := 2*c) r d v.rail
    (pairStep u v).1.rail = t.left ∧ (pairStep u v).2.rail = t.right ∧
      (pairStep u v).2.source = t.source := by
  let a := native (materialize u v) v
  have hmat : (materialize u v).mark = true := by simp [materialize,hm]
  have hM : a.1.mark = true := (native_preserves_mark _ _).trans hmat
  have hL : a.2.leader = false := old_follower_native _ _ hl
  have hP : payer a.1 = false := by
    change (!a.2.leader && a.1.mark && payer a.1) = false at hp
    simpa [hM,hL] using hp
  have hm' : (stepPrefix u v).1.mark = true := by
    change (payment a.1 a.2).1.mark = true
    simp [payment,hM,hL,hP]
  have hl' : (stepPrefix u v).2.leader = false := by
    change (payment a.1 a.2).2.leader = false
    simp [payment,hM,hL,hP]
  have ht := door_transition (Q := 2*c) hQ r d hd v.rail hAuth
  have hNoFire : (door (Q := 2*c) r d v.rail).fire = false := by
    rcases ht with hh | hh
    · exact hh.2.1
    · exact hh.2.2.1
  have hf : (patrol (false || true) (!false && true) false v.source u.rail v.rail).fire = false := by
    simpa [door,hR,hs] using hNoFire
  have hh := pair_projects_rails u v true false hm' hl' hf
  simpa [door,hR,hs] using hh

#print axioms top_pair_projects
#print axioms unpaid_door_projects


theorem pair_left_source {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.source = u.source := by
  have hMat : (materialize u v).source = u.source := by unfold materialize; split <;> rfl
  have hI : (fireInitiator (materialize u v)).source = u.source := by
    unfold fireInitiator
    split <;> exact hMat
  have hImpact (a b : Site p c) : (impact a b).1.source = a.source := by
    unfold impact; split <;> rfl
  have hFollow (g : Bool) (a b : Site p c) : (followerBullet g a b).1.source = a.source := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  have hPay (a b : Site p c) : (payment a b).1.source = a.source := by
    unfold payment
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  have hPre : (stepPrefix u v).1.source = u.source := by
    unfold stepPrefix native
    generalize fireInitiator (materialize u v) = a at hI ⊢
    generalize fireResponder v = b
    have hHit := (hImpact a b).trans hI
    generalize impact a b = w at hHit ⊢
    rcases w with ⟨l,r⟩
    let w := followerBullet (pinned l r) l r
    let q := {w.1 with signal := (Signal.max w.1.signal
      (if w.2.leader then .one else if pinned l r then .two else w.2.signal))}
    change (payment q w.2).1.source = u.source
    exact (hPay _ _).trans ((hFollow _ _ _).trans hHit)
  unfold pairStep
  generalize stepPrefix u v = pp at hPre ⊢
  rcases pp with ⟨a,b⟩
  have hs : a.source = u.source := hPre
  have hf (b : Bool) (a z : Site p c) : (finishBirth b a z).1.source = a.source := by
    unfold finishBirth; split <;> rfl
  exact (hf _ _ _).trans hs

def railsAt {p c n : Nat} (x : Config p c n) (y : Fin n) (d : Nat) :
    Fin (d+1) → Rail := fun i => (x (liftedSite y i.val)).rail

/-- Finite word interface for the actual physical ring. The premise only
labels which certified local operation the selected physical edge
projects to; the authentication proof never assumes a matching Di. -/
inductive LocalProjection {Q h : Nat} (r r' : Fin h → Rail)
    (count : Source Q) : Prop
  | unchanged : r'=r → count=.i1 → LocalProjection r r' count
  | body (a b : Fin h) (adj : a.val+1=b.val) :
      r'=body (Q:=Q) r a b → count=.i1 → LocalProjection r r' count
  | top (slot : Fin h) (atStart : slot.val=0) (outside : Rail) :
      r'=top (Q:=Q) r slot outside → count=.i1 → LocalProjection r r' count
  | door (slot : Fin h) (atEnd : slot.val+1=h) (outside : Rail) :
      r'=put r slot (door (Q:=Q) r slot outside).left →
      count=(door (Q:=Q) r slot outside).source → LocalProjection r r' count

/-- The literal rail monitor recognizes a clean A1 or stays in the
initialization invariant. Here earlier emptiness is in the actual
post-patrol array, not a hypothetical reset of stale storage. -/
theorem projected_auth_step {Q h : Nat} (hQ : 0<Q) (r r' : Fin h → Rail)
    (count : Source Q) (H : Auth r) (hp : LocalProjection r r' count) :
    (count = .i1 ∧ Auth r') ∨
      ∃ d : Fin h, d.val+1=h ∧ Inbound r d ∧ count=.await ⟨0,hQ⟩ ∧
        r' d = .uc ∧ ∀ i : Fin h, i.val < d.val → r' i = .e := by
  cases hp with
  | unchanged hR hC => exact Or.inl ⟨hC,hR.symm ▸ H⟩
  | body a b adj hR hC =>
    rw [hR]; exact Or.inl ⟨hC,body_preserves r a b adj H⟩
  | top a ha outside hR hC =>
    rw [hR]; exact Or.inl ⟨hC,top_preserves r a ha outside H⟩
  | door d hd l hR hC =>
    rw [hR,hC]
    rcases door_transition (Q:=Q) hQ r d hd l H with hh|hh
    · exact Or.inl ⟨hh.1,hh.2.2⟩
    · exact Or.inr ⟨d,hd,hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

#print axioms pair_left_source
#print axioms projected_auth_step


private theorem ring_no_self {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro he
  have hh : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using he
  have hh' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) hh
  omega

/-- Every physical raw mark of the fixed unpaid epoch projects to
exactly one of the tested body, top, door or irrelevant operations.
Supplier protection is obtained from the literal corridor theorem. -/
theorem ring_projection {p c n d : Nat} (hn : 4 ≤ n) (hQ : 0<2*c)
    (x : Config p c n) (y e : Fin n) (hm : MCOV x) (hc : COV x)
    (H : RankFresh.Corridor x y d)
    (hS : (x (liftedSite y (d+1))).source = .i1)
    (hPay : e = liftedSite y d →
      geometricPay (x e) (x (rightNeighbor e)) = false)
    (hAuth : Auth (railsAt x y d)) :
    LocalProjection (railsAt x y d) (railsAt (step x e) y d)
      ((step x e) (liftedSite y (d+1))).source := by
  obtain ⟨k,hkn,hke⟩ := liftedSite_of_site y e
  subst e
  let e := liftedSite y k
  let b := rightNeighbor e
  let z := liftedSite y (d+1)
  have hRe : liftedSite y (k+1) = b := liftedSite_succ _ _
  have hne := ring_no_self hn e
  have stepL : step x e e = (pairStep (x e) (x b)).1 := by simp [step,b]
  have stepR : step x e b = (pairStep (x e) (x b)).2 := by simp [step,b,hne]
  have stepO (i) (ha : i ≠ e) (hb : i ≠ b) : step x e i = x i := by simp [step,b,ha,hb]
  have hGap := H.gap
  have siteNe (a b : Nat) (ha : a<n) (hb : b<n) (hh : a≠b) :
      liftedSite y a ≠ liftedSite y b := fun he => hh (liftedSite_inj y ha hb he)
  have hKeep (hK : k≠d) : (step x e z).source = .i1 := by
    have hz : z ≠ b := by
      intro hz
      have hh : rightNeighbor (liftedSite y d) = rightNeighbor e :=
        (liftedSite_succ y d).symm.trans hz
      have hf := congrArg RearTrace.predecessor hh
      simp only [RearTrace.predecessor_right] at hf
      exact hK (liftedSite_inj y (by omega) hkn hf).symm
    by_cases hz' : z=e
    · rw [hz',stepL,pair_left_source,← hz']; exact hS
    · rw [stepO _ hz' hz]; exact hS
  by_cases hk : k<d
  · have hM : (x e).mark = false := Bool.eq_false_iff.mpr (H.first.before k hk)
    have hL : (x b).leader = false := Bool.eq_false_iff.mpr (fun hh => H.first.before k hk (hm e (Or.inl hh)))
    have hR : (x b).residue = nextResidue (x e).residue := by
      by_cases h : (x b).residue = nextResidue (x e).residue
      · exact h
      · exact False.elim (H.first.before k hk (hm e (Or.inr h)))
    have hOff : (x b).source = .off := by
      by_cases h : (x b).source = .off
      · exact h
      · exact False.elim (H.first.before k hk (hc e h).2)
    obtain ⟨hu,hv,_⟩ := ordinary_pair_projects (x e) (x b) hM hR hL hOff
    let a₀ : Fin (d+1) := ⟨k,by omega⟩
    let b₀ : Fin (d+1) := ⟨k+1,by omega⟩
    refine LocalProjection.body a₀ b₀ rfl ?_ (hKeep (by omega))
    funext i
    have hv' : liftedSite y b₀.val = b := hRe
    change (step x e (liftedSite y i.val)).rail =
      put (put (railsAt x y d) a₀ (Piece (Q:=2*c)
        (x e).rail (x (liftedSite y (k+1))).rail).left)
        b₀ (Piece (Q:=2*c) (x e).rail (x (liftedSite y (k+1))).rail).right i
    rw [hRe]
    by_cases hi : i=b₀
    · subst i
      rw [hv',stepR,hv]
      simp [put]
    · by_cases hj : i=a₀
      · subst i
        rw [show liftedSite y a₀.val=e from rfl,stepL,hu]
        simp [put,hi]
      · have hia : i.val≠k := fun hh => hj (Fin.ext hh)
        have hib : i.val≠k+1 := fun hh => hi (Fin.ext hh)
        have hI := i.isLt
        have h1 := siteNe i.val k (by omega) hkn hia
        have h2 := siteNe i.val (k+1) (by omega) (by omega) hib
        rw [hRe] at h2
        rw [stepO _ h1 h2]
        simp [put,hi,hj,railsAt]
  · by_cases hd : k=d
    · let slot : Fin (d+1) := ⟨d,by omega⟩
      have hEb : e=liftedSite y d := by exact congrArg (liftedSite y) hd
      have hzb : z=b := by rw [← hRe,hd]
      have hProj := unpaid_door_projects hQ (x e) (x b) (railsAt x y d) slot rfl
        (congrArg (fun i => (x i).rail) hEb.symm) hAuth
        (hEb.symm ▸ H.first.marked)
        (hzb ▸ H.ghost) (hzb ▸ hS) (hPay hEb)
      refine LocalProjection.door slot rfl (x b).rail ?_ ?_
      · funext i
        by_cases hi : i=slot
        · subst i
          change (step x e (liftedSite y d)).rail = _
          rw [← hEb,stepL,hProj.1]
          simp [put]
        · have hI := i.isLt
          have hni : i.val≠d := fun hh => hi (Fin.ext hh)
          have h1 := siteNe i.val k (by omega) hkn (by omega)
          have h2 := siteNe i.val (d+1) (by omega) (by omega) (by omega)
          change liftedSite y i.val ≠ z at h2
          rw [hzb] at h2
          change (step x e (liftedSite y i.val)).rail = _
          rw [stepO _ h1 h2]
          simp [put,hi,railsAt]
      · change (step x e z).source = _
        rw [hzb,stepR]
        exact hProj.2.2
    · by_cases htop : k+1=n
      · let slot : Fin (d+1) := ⟨0,by omega⟩
        have hby : b=y := by rw [← hRe,htop,liftedSite_full]
        have hO : (x b).source = .off := by
          by_cases hs : (x b).source = .off
          · exact hs
          · have hl := (hc e hs).1
            change (x b).leader = false at hl
            rw [hby,H.leader] at hl
            contradiction
        have hK : ¬ TenureOrigins.nativeKill (x e) (x b) := by
          intro hKill
          have hl : (x b).leader = true := hby.symm ▸ H.leader
          have he := (TenureOrigins.covered_leader_loss_iff (x e) (x b) hl hO).mpr hKill
          have hAlive := (RankFresh.corridor_supplier_step hn x y e hm H).1
          rw [← hby,stepR,he] at hAlive
          contradiction
        have hP := top_pair_projects (x e) (x b) (hby.symm ▸ H.leader) hO hK
        refine LocalProjection.top slot rfl (x e).rail ?_ (hKeep hd)
        funext i
        by_cases hi : i=slot
        · subst i
          change (step x e (liftedSite y 0)).rail = _
          rw [liftedSite_zero,← hby,stepR,hP.2.1]
          simp [top,put,railsAt,slot,liftedSite_zero,hby]
        · have hI := i.isLt
          have hi0 : i.val≠0 := fun hh => hi (Fin.ext hh)
          have h1 := siteNe i.val k (by omega) hkn (by omega)
          have h2 := siteNe i.val 0 (by omega) (by omega) hi0
          rw [liftedSite_zero] at h2
          have h2' : liftedSite y i.val ≠ b := fun hh => h2 (hh.trans hby)
          change (step x e (liftedSite y i.val)).rail = _
          rw [stepO _ h1 h2']
          simp [top,put,hi,railsAt]
      · refine LocalProjection.unchanged ?_ (hKeep hd)
        funext i
        have hI := i.isLt
        have h1 := siteNe i.val k (by omega) hkn (by omega)
        have h2 := siteNe i.val (k+1) (by omega) (by omega) (by omega)
        rw [hRe] at h2
        change (step x e (liftedSite y i.val)).rail = _
        rw [stepO _ h1 h2]
        rfl

#print axioms ring_projection


/-- Checked physical initialization step. On any first transition out of
I1 within the still-unpaid fixed corridor, the old return is authentic
and COUNT zero is launched on an empty earlier sheet. -/
theorem ring_auth_step {p c n d : Nat} (hn : 4 ≤ n) (hQ : 0<2*c)
    (x : Config p c n) (y e : Fin n) (hm : MCOV x) (hc : COV x)
    (H : RankFresh.Corridor x y d)
    (hS : (x (liftedSite y (d+1))).source = .i1)
    (hPay : e = liftedSite y d →
      geometricPay (x e) (x (rightNeighbor e)) = false)
    (hAuth : Auth (railsAt x y d)) :
    let x' := step x e
    let r := railsAt x y d
    let r' := railsAt x' y d
    let count := (x' (liftedSite y (d+1))).source
    (count = .i1 ∧ Auth r') ∨
      ∃ j : Fin (d+1), j.val+1=d+1 ∧ Inbound r j ∧ count=.await ⟨0,hQ⟩ ∧
        r' j = .uc ∧ ∀ i : Fin (d+1), i.val < j.val → r' i = .e :=
  projected_auth_step hQ _ _ _ hAuth (ring_projection hn hQ x y e hm hc H hS hPay hAuth)

def FixedUnpaidWord {p c n : Nat} (x : Config p c n) (y : Fin n) (d : Nat) :
    List (Fin n) → Prop
  | [] => True
  | e::w => MCOV x ∧ COV x ∧ RankFresh.Corridor x y d ∧
      (e = liftedSite y d → geometricPay (x e) (x (rightNeighbor e)) = false) ∧
      (step x e (liftedSite y (d+1))).source = .i1 ∧ FixedUnpaidWord (step x e) y d w

/-- Through any still-I1 prefix of the fixed unpaid epoch, including
failed or relaunched initialization fronts, the physical slots satisfy
the authenticated rail invariant. -/
theorem ring_auth_word {p c n d : Nat} (hn : 4 ≤ n) (hQ : 0<2*c)
    (x : Config p c n) (y : Fin n) (w : List (Fin n))
    (hS : (x (liftedSite y (d+1))).source = .i1)
    (hAuth : Auth (railsAt x y d)) (hp : FixedUnpaidWord x y d w) :
    ((run x w) (liftedSite y (d+1))).source = .i1 ∧ Auth (railsAt (run x w) y d) := by
  induction w generalizing x with
  | nil => exact ⟨hS,hAuth⟩
  | cons e w ih =>
    obtain ⟨hm,hc,hCor,hPay,hSrc,hTail⟩ := hp
    have ha := ring_auth_step hn hQ x y e hm hc hCor hS hPay hAuth
    rcases ha with H | ⟨_,_,_,hA,_,_⟩
    · exact ih (step x e) H.1 H.2 hTail
    · change (step x e (liftedSite y (d+1))).source = Source.await ⟨0,hQ⟩ at hA
      rw [hSrc] at hA
      contradiction

#print axioms ring_auth_step
#print axioms ring_auth_word

end L4.FreshEpochAuthentication
