import Leader.L4.BStarClearanceStopped

/-! Mixed-radix rank for the four clearance coordinates. Caps are fixed
for the entire stopped experiment, not recomputed after a mark. -/
namespace L4.BStarClearanceLex

structure Four where
  forward : Nat
  mobile : Nat
  reply : Nat
  trail : Nat

def Bounded (cap a : Four) : Prop :=
  a.forward≤cap.forward ∧ a.mobile≤cap.mobile ∧ a.reply≤cap.reply ∧ a.trail≤cap.trail

def join (base hi lo : Nat) := hi*(base+1)+lo

def scalar (cap a : Four) :=
  join cap.trail (join cap.reply (join cap.mobile a.forward a.mobile) a.reply) a.trail

def Falls (a b : Four) : Prop :=
  a.forward<b.forward ∨
  a.forward=b.forward ∧ (a.mobile<b.mobile ∨
  a.mobile=b.mobile ∧ (a.reply<b.reply ∨
  a.reply=b.reply ∧ a.trail<b.trail))

def Weak (a b : Four) : Prop :=
  a.forward<b.forward ∨
  a.forward=b.forward ∧ (a.mobile<b.mobile ∨
  a.mobile=b.mobile ∧ (a.reply<b.reply ∨
  a.reply=b.reply ∧ a.trail≤b.trail))

theorem join_lt {base a b l r : Nat} (hl : l≤base) (hr : r≤base) :
    join base a l < join base b r ↔ a<b ∨ a=b ∧ l<r := by
  have H : ∀ {i j x y : Nat}, x≤base → i<j → join base i x < join base j y := by
    intro i j x y hx hij
    have M := Nat.mul_le_mul_right (base+1) (show i+1≤j by omega)
    rw [Nat.add_mul] at M
    simp only [Nat.one_mul] at M
    unfold join
    omega
  constructor
  · intro e
    rcases Nat.lt_trichotomy a b with h|h|h
    · exact .inl h
    · subst b
      right
      exact ⟨rfl,by unfold join at e; omega⟩
    · exact (Nat.not_lt_of_ge (Nat.le_of_lt (H hr h)) e).elim
  · rintro (h|⟨h,k⟩)
    · exact H hl h
    · subst b
      unfold join
      omega

theorem join_le {base a b l r : Nat} (hl : l≤base) (hr : r≤base) :
    join base a l ≤ join base b r ↔ a<b ∨ a=b ∧ l≤r := by
  rw [← Nat.not_lt,join_lt hr hl]
  rcases Nat.lt_trichotomy a b with H|H|H <;> omega

theorem join_eq {base a b l r : Nat} (hl : l≤base) (hr : r≤base) :
    join base a l = join base b r ↔ a=b ∧ l=r := by
  rw [Nat.le_antisymm_iff,join_le hl hr,join_le hr hl]
  omega

theorem scalar_lt {cap a b : Four} (ha : Bounded cap a) (hb : Bounded cap b) :
    scalar cap a<scalar cap b ↔ Falls a b := by
  unfold scalar Falls
  simp only [join_lt ha.2.2.2 hb.2.2.2,join_lt ha.2.2.1 hb.2.2.1,join_lt ha.2.1 hb.2.1,
    join_eq ha.2.2.1 hb.2.2.1,join_eq ha.2.1 hb.2.1]
  omega

theorem scalar_le {cap a b : Four} (ha : Bounded cap a) (hb : Bounded cap b) :
    scalar cap a≤scalar cap b ↔ Weak a b := by
  unfold scalar Weak
  simp only [join_le ha.2.2.2 hb.2.2.2,join_lt ha.2.2.1 hb.2.2.1,join_lt ha.2.1 hb.2.1,
    join_eq ha.2.2.1 hb.2.2.1,join_eq ha.2.1 hb.2.1]
  omega

/-- A convenient ordered-discharge rule: check each coordinate only
when all higher-priority coordinates tie. -/
theorem weak_of_conditional {a b : Four}
    (f : a.forward≤b.forward)
    (m : a.forward=b.forward → a.mobile≤b.mobile)
    (d : a.forward=b.forward → a.mobile=b.mobile → a.reply≤b.reply)
    (t : a.forward=b.forward → a.mobile=b.mobile → a.reply=b.reply → a.trail≤b.trail) :
    Weak a b := by
  by_cases F : a.forward=b.forward
  · by_cases M : a.mobile=b.mobile
    · by_cases D : a.reply=b.reply
      · exact .inr ⟨F,.inr ⟨M,.inr ⟨D,t F M D⟩⟩⟩
      · exact .inr ⟨F,.inr ⟨M,.inl (by have := d F M; omega)⟩⟩
    · exact .inr ⟨F,.inl (by have := m F; omega)⟩
  · exact .inl (by omega)

theorem bounded_scalar {cap a : Four} (h : Bounded cap a) :
    scalar cap a≤scalar cap cap := by
  obtain ⟨F,M,D,T⟩ := h
  have H : Bounded cap cap := ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩
  exact (scalar_le ⟨F,M,D,T⟩ H).mpr (weak_of_conditional F (fun _ => M) (fun _ _ => D) (fun _ _ _ => T))

theorem falls_of_weak_ne {a b : Four} (W : Weak a b)
    (N : a.forward≠b.forward ∨ a.mobile≠b.mobile ∨ a.reply≠b.reply ∨ a.trail≠b.trail) :
    Falls a b := by
  unfold Weak at W
  unfold Falls
  omega

/-- Apply the scalar stopped theorem to any four finite sums once
the actual local accounting and bounded service witness are proved. -/
theorem certificate {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} (cap : Four) (coord : X → Four) (budget : Nat)
    (bounded : ∀ x, Inv x → Bounded cap (coord x))
    (closed : ∀ x e, Inv x → ¬Ready x → Inv (step x e))
    (weak : ∀ x e, Inv x → ¬Ready x → Weak (coord (step x e)) (coord x))
    (serve : ∀ x, Inv x → ¬Ready x → ∃ w : List (Fin n), w.length≤budget ∧
      (Ready (BStarResetSchedule.run step x w) ∨
        Bounded cap (coord (BStarResetSchedule.run step x w)) ∧
        Falls (coord (BStarResetSchedule.run step x w)) (coord x))) :
    BStarClearanceStopped.Certificate step Inv Ready (fun x => scalar cap (coord x)) budget := by
  refine ⟨closed,?_,?_⟩
  · intro x e I R
    exact (scalar_le (bounded _ (closed x e I R)) (bounded _ I)).mpr (weak x e I R)
  · intro x I R
    obtain ⟨w,L,H⟩ := serve x I R
    refine ⟨w,L,H.imp_right ?_⟩
    rintro ⟨B,F⟩
    exact (scalar_lt B (bounded _ I)).mpr F

/-- The deterministic existence half needs no assertion about ranks
on other marks. Caps still refer to the pre-fixed chart, not old
arbitrary offset bytes or field multiplicities recomputed after a mark. -/
theorem ready_word_of_lex_service {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} (cap : Four) (coord : X → Four) (budget : Nat)
    (bounded : ∀ x, Inv x → Bounded cap (coord x))
    (closed : ∀ x e, Inv x → ¬Ready x → Inv (step x e))
    (serve : ∀ x, Inv x → ¬Ready x → ∃ w : List (Fin n), w.length≤budget ∧
      (Ready (BStarResetSchedule.run step x w) ∨
        Bounded cap (coord (BStarResetSchedule.run step x w)) ∧
        Falls (coord (BStarResetSchedule.run step x w)) (coord x)))
    (x : X) (I : Inv x) :
    ∃ w : List (Fin n), w.length≤budget*(scalar cap (coord x)+1) ∧
      BStarClearanceStopped.Before step Ready x w ∧ Inv (BStarResetSchedule.run step x w) ∧
      Ready (BStarResetSchedule.run step x w) := by
  apply BStarClearanceStopped.ready_word_of_service (rank:=fun x => scalar cap (coord x)) closed _ x I
  intro y J N
  obtain ⟨w,L,H⟩ := serve y J N
  refine ⟨w,L,H.imp_right ?_⟩
  rintro ⟨B,F⟩
  exact (scalar_lt B (bounded y J)).mpr F

private abbrev ordinalRank : WellFoundedRelation (Nat × Nat × Nat × Nat) :=
  Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))

private def packRank (a : Four) : Nat × Nat × Nat × Nat :=
  (a.forward,a.mobile,a.reply,a.trail)

private theorem falls_ord {a b : Four} (F : Falls a b) :
    ordinalRank.rel (packRank a) (packRank b) := by
  change Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
    (packRank a) (packRank b)
  simpa only [packRank,Prod.lex_def,Falls] using F

/-- The existence of the finite historical cuts needs no numeric cap.
For a one-mark service nomination choose only from the strictly
decreasing labels. The history stops before source service at Ready. -/
theorem nominated_ready_word {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv Ready : X → Prop} (coord : X → Four)
    (closed : ∀ x e, Inv x → ¬Ready x → Inv (step x e))
    (nominate : ∀ x, Inv x → ¬Ready x → ∃ e, Ready (step x e) ∨
      Falls (coord (step x e)) (coord x)) (x : X) (I : Inv x) :
    ∃ w, BStarClearanceStopped.Before step Ready x w ∧
      Inv (BStarResetSchedule.run step x w) ∧ Ready (BStarResetSchedule.run step x w) := by
  classical
  let rel := invImage (fun y => packRank (coord y)) ordinalRank
  induction x using rel.wf.induction with
  | h x ih =>
    by_cases R : Ready x
    · refine ⟨[],?_,I,R⟩
      intro u e v E
      cases u <;> contradiction
    obtain ⟨e,P⟩ := nominate x I R
    have J := closed x e I R
    obtain ⟨w,W,A,Z⟩ : ∃ w, BStarClearanceStopped.Before step Ready (step x e) w ∧
        Inv (BStarResetSchedule.run step (step x e) w) ∧
        Ready (BStarResetSchedule.run step (step x e) w) := by
      rcases P with P|F
      · refine ⟨[],?_,J,P⟩
        intro u a v E
        cases u <;> contradiction
      · exact ih _ (falls_ord F) J
    refine ⟨e::w,?_,A,Z⟩
    intro u a v E
    cases u with
    | nil => exact R
    | cons b u =>
      obtain ⟨h,j⟩ := List.cons.inj E
      subst b
      exact W u a v j

#print axioms nominated_ready_word
#print axioms ready_word_of_lex_service
#print axioms scalar_lt
#print axioms scalar_le
#print axioms certificate
end L4.BStarClearanceLex
