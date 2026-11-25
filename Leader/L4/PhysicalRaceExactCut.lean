import Leader.L4.OrderedRaceTape

namespace L4.PhysicalRaceExactCut
open StoppedDoorRaceIID PhysicalDoorRace PhysicalRacePrefixes PhysicalCustody

/-- Exact successful stopping: an extending word has not been sampled
past the first accepted decision. -/
def Exact {n : Nat} (d : Fin n) (k : Nat) (w : List (Fin n)) : Prop :=
  accepted d k w=1 ∧ ∀ pre rest,w=pre++rest→rest≠[]→accepted d k pre≠1

theorem exact_of_tick {n : Nat} (d : Fin n) {k j : Nat} (hk : 0<k)
    (v : List (Fin n)) (e : Fin n)
    (R : BStarResetSchedule.run (next d) (.live k) v=.live j)
    (paid : next d (.live j) e=.accept) : Exact d k (v++[e]) := by
  have final : BStarResetSchedule.run (next d) (.live k) (v++[e])=.accept := by
    rw [BStarResetSchedule.run_append,R]
    exact paid
  refine ⟨(reaches_accept_iff d k hk _).mp final,?_⟩
  intro pre rest E N hit
  have earlier : ∃ rem,v=pre++rem := by
    rcases List.append_eq_append_iff.mp E with ⟨a,A,B⟩|⟨a,A,_⟩
    · have L := congrArg List.length B
      have h := List.length_pos_iff.mpr N
      simp only [List.length_append,List.length_cons,List.length_nil] at L
      have Z := List.length_eq_zero_iff.mp (show a.length=0 by omega)
      exact ⟨[],by simpa [Z] using A.symm⟩
    · exact ⟨a,A⟩
  obtain ⟨rem,eq⟩ := earlier
  have old := (reaches_accept_iff d k hk _).mpr hit
  have absorb (l : List (Fin n)) : BStarResetSchedule.run (next d) .accept l=.accept := by
    induction l with
    | nil => rfl
    | cons e l ih => exact ih
  rw [eq,BStarResetSchedule.run_append,old,absorb] at R
  cases R

theorem exact_racing_tick {n : Nat} (A : List (Fin n)→Prop) (d : Fin n)
    (k j : Nat) (hk : 0<k) (w v : List (Fin n)) (e : Fin n)
    (V : OrderedRaceTape.valid A d k (.racing w v (.live j)))
    (paid : next d (.live j) e=.accept) :
    Exact d k (ResetReturnIID.appendTape v e) :=
  exact_of_tick d hk v e V.2.symm paid

private theorem accepted_skip {n : Nat} (d : Fin n) (k : Nat)
    (gap t : List (Fin n)) (D : ∀ e∈gap,DisjointMarks e d)
    (A : AcceptedPrefix d (k+1) t) : AcceptedPrefix d (k+1) (gap++t) := by
  induction gap with
  | nil => exact A
  | cons e rest ih =>
    exact .disjoint (D _ List.mem_cons_self) (ih (fun f h=>D f (List.mem_cons_of_mem _ h)))

theorem single_tail_nil {n : Nat} {d : Fin n} {w g t : List (Fin n)}
    (H : Exact d 1 w) (E : w=g++d::t) (D : ∀ e∈g,DisjointMarks e d) : t=[] := by
  have S : AcceptedPrefix d 1 (g++[d]) := accepted_skip d 0 g [d] D (.door (.done []))
  by_cases Z : t=[]
  · exact Z
  · exfalso
    exact H.2 _ _ (by simpa only [List.append_assoc,List.singleton_append] using E) Z
      ((accepted_iff _ _ _).mpr S)

theorem double_tail_nil {n : Nat} {d : Fin n} {w a b t : List (Fin n)}
    (H : Exact d 2 w) (E : w=a++d::(b++d::t))
    (D : ∀ e∈a,DisjointMarks e d) (V : ∀ e∈b,DisjointMarks e d) : t=[] := by
  have S : AcceptedPrefix d 2 (a++d::(b++[d])) :=
    accepted_skip d 1 a _ D (.door (accepted_skip d 0 b [d] V (.door (.done []))))
  by_cases Z : t=[]
  · exact Z
  · exfalso
    exact H.2 _ _ (by simpa only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using E) Z
      ((accepted_iff _ _ _).mpr S)

theorem exact_single_split {n : Nat} {d : Fin n} {w : List (Fin n)}
    (H : Exact d 1 w) : ∃ gap,w=gap++[d] ∧ ∀ e∈gap,DisjointMarks e d := by
  obtain ⟨g,t,E,D⟩ := one_gap ((accepted_iff d 1 w).mp H.1)
  have Z := single_tail_nil H E D
  subst t
  exact ⟨g,E,D⟩

theorem exact_double_split {n : Nat} {d : Fin n} {w : List (Fin n)}
    (H : Exact d 2 w) : ∃ a b,w=a++d::(b++[d]) ∧
      (∀ e∈a,DisjointMarks e d) ∧ (∀ e∈b,DisjointMarks e d) := by
  obtain ⟨a,b,t,E,D,V⟩ := two_gaps ((accepted_iff d 2 w).mp H.1)
  have Z := double_tail_nil H E D V
  subst t
  exact ⟨a,b,E,D,V⟩

/-- In addition to the ordinary observer consistency, no race mark has
yet been sampled after the first accepting or rejecting decision. -/
def ValidFirst {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat)
    (z : OrderedRaceTape.State n) : Prop :=
  OrderedRaceTape.valid A d k z ∧
    match z with
    | .waiting _ => True
    | .racing _ v _ =>
      ∀ pre rest,v=pre++rest→rest≠[]→
        ¬target (BStarResetSchedule.run (next d) (.live k) pre)

theorem validFirst_start {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) :
    ValidFirst A d k (OrderedRaceTape.enter A k []) := by
  refine ⟨OrderedRaceTape.valid_start A d k,?_⟩
  classical
  by_cases H : A []
  · rw [show OrderedRaceTape.enter A k []=.racing [] [] (.live k) by simp [OrderedRaceTape.enter,H]]
    intro pre rest E N
    have L := congrArg List.length E
    simp only [List.length_nil,List.length_append] at L
    exact (N (List.length_eq_zero_iff.mp (by omega))).elim
  · rw [show OrderedRaceTape.enter A k []=.waiting [] by simp [OrderedRaceTape.enter,H]]
    trivial

private theorem terminal_absorb {n : Nat} (d : Fin n) (q : Decision)
    (h : target q) (v : List (Fin n)) : BStarResetSchedule.run (next d) q v=q := by
  induction v with
  | nil => rfl
  | cons e v ih =>
    cases q with
    | live j => cases h
    | accept => exact ih
    | reject => exact ih

theorem validFirst_step {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat)
    (z : OrderedRaceTape.State n) (e : Fin n) (V : ValidFirst A d k z)
    (L : ¬OrderedRaceTape.done z) :
    ValidFirst A d k (OrderedRaceTape.tick A d k z e) := by
  refine ⟨OrderedRaceTape.valid_step A d k z e V.1,?_⟩
  cases z with
  | waiting w =>
    classical
    change match OrderedRaceTape.enter A k (ResetReturnIID.appendTape w e) with
    | .waiting _ => True
    | .racing _ v _ => ∀ pre rest,v=pre++rest→rest≠[]→¬target (BStarResetSchedule.run (next d) (.live k) pre)
    by_cases H : A (ResetReturnIID.appendTape w e)
    · rw [show OrderedRaceTape.enter A k (ResetReturnIID.appendTape w e)=.racing (ResetReturnIID.appendTape w e) [] (.live k) by simp [OrderedRaceTape.enter,H]]
      intro pre rest E N
      have l := congrArg List.length E
      simp only [List.length_nil,List.length_append] at l
      exact (N (List.length_eq_zero_iff.mp (by omega))).elim
    · rw [show OrderedRaceTape.enter A k (ResetReturnIID.appendTape w e)=.waiting (ResetReturnIID.appendTape w e) by simp [OrderedRaceTape.enter,H]]
      trivial
  | racing a v q =>
    intro pre rest E N hit
    change v++[e]=pre++rest at E
    have earlier : ∃ rem,v=pre++rem := by
      rcases List.append_eq_append_iff.mp E with ⟨b,M,B⟩|⟨b,M,_⟩
      · have l := congrArg List.length B
        have h := List.length_pos_iff.mpr N
        simp only [List.length_cons,List.length_nil,List.length_append] at l
        have Z := List.length_eq_zero_iff.mp (show b.length=0 by omega)
        exact ⟨[],by simpa [Z] using M.symm⟩
      · exact ⟨b,M⟩
    obtain ⟨rem,M⟩ := earlier
    have R := V.1.2
    rw [M,BStarResetSchedule.run_append,terminal_absorb d _ hit] at R
    exact L (show target q from R.symm ▸ hit)

theorem exact_of_validFirst_accept {n : Nat} (A : List (Fin n)→Prop) (d : Fin n)
    (k : Nat) (K : 0<k) (pre v : List (Fin n))
    (V : ValidFirst A d k (.racing pre v .accept)) :
    OrderedRaceTape.cut A pre ∧ Exact d k v := by
  obtain ⟨cut,accept⟩ := OrderedRaceTape.accepted_split A d k K pre v V.1
  refine ⟨cut,accept,?_⟩
  intro u rest E N old
  exact V.2 _ _ E N (by rw [(reaches_accept_iff d k K _).mpr old]; trivial)

end L4.PhysicalRaceExactCut
