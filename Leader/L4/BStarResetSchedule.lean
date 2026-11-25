import Leader.L4.BStarSeparatingProgress
import Leader.L4.AllSizeS1Geometry

/-! Consecutive covering blocks of actual directed ring marks suffice
once each nominated old service row and its chart are certified.
The old-door handling mark is separate from the clean return cut. -/
namespace L4.BStarResetSchedule
open BStarSeparatingRail BStarSeparatingProgress BStarLongToken

abbrev Track := BStarSeparatingRail.Rail

def run {X : Type} {n : Nat} (step : X → Fin n → X) : X → List (Fin n) → X
  | x, [] => x
  | x, e::w => run step (step x e) w

theorem run_append {X : Type} {n : Nat} (step : X → Fin n → X) (x : X)
    (u v : List (Fin n)) : run step x (u++v)=run step (run step x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- The geometric service label function is fixed during this rail
experiment. Service and closure are all-label facts only before return;
requiring the service frame at a returned old D would exclude its
literal door consumption. -/
structure Adapter {X : Type} {n : Nat} (step : X → Fin n → X) (track : X → Track)
    (tag : Tag) (len : Nat) (Inv : X → Prop) (edgeOf : Label → Fin n) : Prop where
  sane : Sane tag
  closed : ∀ x e c, Inv x → c≠.back 0 → Good tag len (track x) c → Inv (step x e)
  service : ∀ x e c, Inv x → c≠.back 0 → Good tag len (track x) c →
    ∃ s : Service tag len (track x) (track (step x e)),
      e=edgeOf (nomination len c) → nomination len c∈s.labels

def Clean {X : Type} (track : X → Track) (tag : Tag) (len : Nat) (x : X) : Prop :=
  tag.D (track x 0) ∧ ∀ i, 0<i → i≤len → track x i=.empty

/-- Guided path of the cursor on the very same physical word of marks,
ending when a tagged response reaches zero. -/
inductive Seen {X : Type} {n : Nat} (step : X → Fin n → X) (track : X → Track)
    (tag : Tag) (len : Nat) : X → Cursor → List (Fin n) → Cursor → Prop
  | nil (x c) : Seen step track tag len x c [] c
  | cons {x e w c d f} (l : c≠.back 0)
      (m : Mark tag len (track x) (track (step x e)))
      (a : Advance len c d) (g : Good tag len (track (step x e)) d)
      (t : Seen step track tag len (step x e) d w f) : Seen step track tag len x c (e::w) f

theorem Seen.append {X : Type} {n : Nat} {step : X → Fin n → X} {track : X → Track}
    {tag : Tag} {len : Nat} {x : X} {c d f : Cursor} {u v : List (Fin n)}
    (a : Seen step track tag len x c u d)
    (b : Seen step track tag len (run step x u) d v f) :
    Seen step track tag len x c (u++v) f := by
  induction a with
  | nil _ _ => exact b
  | cons l m a g _ ih => exact .cons l m a g (ih b)

def Stopped {X : Type} {n : Nat} (step : X → Fin n → X) (track : X → Track)
    (tag : Tag) (len : Nat) (Inv : X → Prop) (x : X) (c : Cursor)
    (w : List (Fin n)) : Prop :=
  ∃ pre post, w=pre++post ∧ Seen step track tag len x c pre (.back 0) ∧
    Inv (run step x pre) ∧ Clean track tag len (run step x pre)

private theorem zero_of_good {X : Type} {track : X → Track} {tag : Tag}
    {len : Nat} {x : X} (g : Good tag len (track x) (.back 0)) : Clean track tag len x :=
  ⟨g.2.1,g.2.2.2⟩

theorem word_progress {X : Type} {n : Nat} {step : X → Fin n → X} {track : X → Track}
    {tag : Tag} {len : Nat} {Inv : X → Prop} {edgeOf : Label → Fin n}
    (A : Adapter step track tag len Inv edgeOf) (w : List (Fin n))
    (x : X) (c : Cursor) (hx : Inv x) (gc : Good tag len (track x) c) :
    Stopped step track tag len Inv x c w ∨
    ∃ d, Seen step track tag len x c w d ∧ Inv (run step x w) ∧
      Good tag len (track (run step x w)) d ∧ d≠.back 0 ∧ rank len d≤rank len c ∧
      (edgeOf (nomination len c)∈w → rank len d<rank len c) := by
  induction w generalizing x c with
  | nil =>
    by_cases h : c=.back 0
    · subst c
      exact .inl ⟨[],[],rfl,.nil _ _,hx,zero_of_good gc⟩
    · exact .inr ⟨c,.nil _ _,hx,gc,h,Nat.le_refl _,fun h => (List.not_mem_nil h).elim⟩
  | cons e w ih =>
    by_cases L : c=.back 0
    · subst c
      exact .inl ⟨[],e::w,rfl,.nil _ _,hx,zero_of_good gc⟩
    obtain ⟨s,H⟩ := A.service x e c hx L gc
    obtain ⟨d,J,G⟩ := lift_mark s.mark c L gc
    rcases ih (step x e) d (A.closed x e c hx L gc) G with
      C|⟨f,t,hf,F,live,mono,strict⟩
    · obtain ⟨pre,post,W,t,I,Q⟩ := C
      exact .inl ⟨e::pre,post,congrArg (List.cons e) W,.cons L s.mark J G t,I,Q⟩
    · refine .inr ⟨f,.cons L s.mark J G t,hf,F,live,
        Nat.le_trans mono (rank_mono gc J),?_⟩
      intro E
      by_cases B : c=d
      · subst d
        rcases List.mem_cons.mp E with h|h
        · exact (mandatory A.sane s L gc G (H h.symm) rfl).elim
        · exact strict h
      · exact Nat.lt_of_le_of_lt mono (rank_strict gc J B)

def sweeps (n : Nat) : Nat → List (Fin n)
  | 0 => []
  | k+1 => List.finRange n ++ sweeps n k

theorem sweeps_length (n k : Nat) : (sweeps n k).length=n*k := by
  induction k with
  | zero => simp [sweeps]
  | succ k ih => simp [sweeps,ih,Nat.mul_succ,Nat.add_comm]

theorem stop_by_sweeps {X : Type} {n : Nat} {step : X → Fin n → X} {track : X → Track}
    {tag : Tag} {len : Nat} {Inv : X → Prop} {edgeOf : Label → Fin n}
    (A : Adapter step track tag len Inv edgeOf) (k : Nat)
    (x : X) (c : Cursor) (hx : Inv x) (gc : Good tag len (track x) c)
    (budget : rank len c≤k) : Stopped step track tag len Inv x c (sweeps n k) := by
  induction k generalizing x c with
  | zero =>
    have H : c=.back 0 := by
      apply Classical.not_not.mp
      intro l
      have P := rank_nonzero gc l
      omega
    subst c
    exact ⟨[],[],rfl,.nil _ _,hx,zero_of_good gc⟩
  | succ k ih =>
    rcases word_progress A (List.finRange n) x c hx gc with
      C|⟨d,F,I,G,_,_,strict⟩
    · obtain ⟨pre,post,E,T,J,Q⟩ := C
      refine ⟨pre,post++sweeps n k,?_,T,J,Q⟩
      rw [sweeps,E,List.append_assoc]
    · have R := strict (List.mem_finRange _)
      obtain ⟨pre,post,E,T,J,Q⟩ :=
        ih (run step x (List.finRange n)) d I G (by omega)
      refine ⟨List.finRange n++pre,post,?_,Seen.append F T,?_,?_⟩
      · rw [sweeps,E,List.append_assoc]
      · rw [run_append]; exact J
      · rw [run_append]; exact Q

/-- The clean return exists within exactly the prefix budget obtained by
taking 2*len+1 rounds of every directed label, from any issued suffix. -/
theorem reset_prefix {X : Type} {n : Nat} {step : X → Fin n → X} {track : X → Track}
    {tag : Tag} {len : Nat} {Inv : X → Prop} {edgeOf : Label → Fin n}
    (A : Adapter step track tag len Inv edgeOf) (x : X) (hx : Inv x) (F : tag.F (track x 0)) :
    ∃ pre post,
      sweeps n (2*len+1)=pre++post ∧ pre.length≤n*(2*len+1) ∧
      Seen step track tag len x (.out 0) pre (.back 0) ∧
      Inv (run step x pre) ∧ Clean track tag len (run step x pre) := by
  have H : Good tag len (track x) (.out 0) :=
    ⟨Nat.zero_le _,F,fun j h => (Nat.not_lt_zero j h).elim⟩
  obtain ⟨pre,post,W,T,I,C⟩ :=
    stop_by_sweeps A (2*len+1) x (.out 0) hx H (by simp [rank])
  refine ⟨pre,post,W,?_,T,I,C⟩
  have L := congrArg List.length W
  rw [sweeps_length,List.length_append] at L
  omega

/-- The additional source mark is applied *after* the exhibited clean
prefix, not counted as its final hop. The endpoint theorem may record a
successful receipt or a literal fault restart, as appropriate. -/
theorem reset_prefix_then_door {X : Type} {n : Nat} {step : X → Fin n → X} {track : X → Track}
    {tag : Tag} {len : Nat} {Inv : X → Prop} {edgeOf : Label → Fin n}
    (A : Adapter step track tag len Inv edgeOf) (x : X) (hx : Inv x) (F : tag.F (track x 0))
    (door : Fin n) (Handled : X → X → Prop)
    (handle : ∀ y, Inv y → Clean track tag len y → Handled y (step y door)) :
    ∃ pre post,
      sweeps n (2*len+1)=pre++post ∧ (pre++[door]).length≤n*(2*len+1)+1 ∧
      Seen step track tag len x (.out 0) pre (.back 0) ∧ Clean track tag len (run step x pre) ∧
      Handled (run step x pre) (run step x (pre++[door])) := by
  obtain ⟨pre,post,W,L,V,I,C⟩ := reset_prefix A x hx F
  refine ⟨pre,post,W,?_,V,C,?_⟩
  · simp [List.length_append]; omega
  · rw [run_append]
    exact handle _ I C

/-- Decode the chart's actual packed command occurrence at each
ordinal. The chart adapter, not this function, proves injectivity and
the consistency of its nominations with the literal claim table. -/
def ringTrack {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (chart : Nat → Fin n × Fin 11)
    (x : Fin n → AllSizeProtocol.LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)) : Track :=
  fun j => atSite (x (chart j).1).long (chart j).2

theorem ring_reset_then_door {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (b : AllSizeProtocol.LargeRows (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)) (chart : Nat → Fin n × Fin 11)
    (tag : Tag) (len : Nat) (Inv : (Fin n → AllSizeProtocol.LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)) → Prop)
    (edgeOf : Label → Fin n) (door : Fin n)
    (A : Adapter (AllSizeS1Geometry.step b) (ringTrack chart) tag len Inv edgeOf)
    (x : Fin n → AllSizeProtocol.LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)) (hx : Inv x) (F : tag.F (ringTrack chart x 0))
    (Handled : (Fin n → AllSizeProtocol.LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)) → (Fin n → AllSizeProtocol.LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁)) → Prop)
    (handle : ∀ y, Inv y → Clean (ringTrack chart) tag len y →
      Handled y (AllSizeS1Geometry.step b y door)) :
    ∃ pre post,
      sweeps n (2*len+1)=pre++post ∧ (pre++[door]).length≤n*(2*len+1)+1 ∧
      Seen (AllSizeS1Geometry.step b) (ringTrack chart) tag len x (.out 0) pre (.back 0) ∧
      Clean (ringTrack chart) tag len (run (AllSizeS1Geometry.step b) x pre) ∧
      Handled (run (AllSizeS1Geometry.step b) x pre)
        (run (AllSizeS1Geometry.step b) x (pre++[door])) :=
  reset_prefix_then_door A x hx F door Handled handle

#print axioms reset_prefix
#print axioms reset_prefix_then_door
#print axioms ring_reset_then_door
end L4.BStarResetSchedule
