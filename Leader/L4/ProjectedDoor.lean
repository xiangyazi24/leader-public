import Leader.L4.PhysicalCustodyCommutation
import Leader.L4.Height.LeaderBridge
import Leader.L4.RearGeometry
import Leader.L4.Barrier

namespace L4.ProjectedDoor
open PhysicalCustody RearTrace Height

variable {n : Nat}
instance (d e : Fin n) : Decidable (DisjointMarks d e) := by
  unfold DisjointMarks
  infer_instance

private theorem disjoint_iff (d e : Fin n) :
    DisjointMarks d e ↔ e≠d ∧ e≠predecessor d ∧ e≠rightNeighbor d := by
  constructor
  · rintro ⟨a,b,c,_⟩
    refine ⟨Ne.symm a,fun H=>b ?_,Ne.symm c⟩
    rw [H,right_predecessor]
  · rintro ⟨a,b,c⟩
    refine ⟨Ne.symm a,?_,Ne.symm c,?_⟩
    · intro H
      apply b
      simpa only [predecessor_right] using (congrArg predecessor H).symm
    · intro H
      apply a
      simpa only [predecessor_right] using (congrArg predecessor H).symm

private theorem triple_ne (hn : 4≤n) (d : Fin n) :
    predecessor d≠d ∧ predecessor d≠rightNeighbor d ∧ d≠rightNeighbor d := by
  simpa only [right_predecessor] using barrierBondsDistinct hn (predecessor d)

private theorem filter_nodup {α : Type} (p : α → Bool) {xs : List α} (h : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨N,H⟩ := List.nodup_cons.mp h
    cases C : p a
    · simpa [C] using ih H
    · simp only [List.filter_cons,C,if_true]
      exact List.nodup_cons.mpr ⟨fun M=>N (List.mem_filter.mp M).1,ih H⟩

/-- Exactly three scheduler labels meet the endpoints of the door. -/
theorem door_incident_labels_three (hn : 4≤n) (d : Fin n) :
    ((List.finRange n).filter (fun e => decide (¬DisjointMarks d e))).length=3 := by
  obtain ⟨a,b,c⟩ := triple_ne hn d
  let f := fun e => decide (¬DisjointMarks d e)
  have T : [d,predecessor d,rightNeighbor d].Nodup := by
    simp [Ne.symm a,b,c]
  have P : ((List.finRange n).filter f).Perm [d,predecessor d,rightNeighbor d] := by
    apply (List.perm_ext_iff_of_nodup (filter_nodup f (List.nodup_finRange _)) T).mpr
    intro e
    simp [f,List.mem_filter,List.mem_finRange,disjoint_iff]
  exact P.length_eq

inductive State where
  | idle | armed | done
  deriving DecidableEq

def next (d : Fin n) : State → Fin n → State
  | .idle,e => if e=d then .armed else .idle
  | .armed,e => if e=d then .done else if DisjointMarks d e then .armed else .idle
  | .done,_ => .done

def potential (n : Nat) : State → Nat
  | .idle => 4*n
  | .armed => 3*n
  | .done => 0

private def sum {m : Nat} (f : Fin m → Nat) : Nat := (List.ofFn f).sum

private theorem sum_succ {m : Nat} (f : Fin (m+1) → Nat) :
    sum f = f 0+sum (fun i : Fin m => f i.succ) := by simp [sum,List.ofFn_succ]

private theorem sum_const (m a : Nat) : sum (fun _ : Fin m => a)=m*a := by
  induction m with
  | zero => simp [sum]
  | succ m ih => rw [sum_succ,ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_add {m : Nat} (f g : Fin m → Nat) :
    sum (fun i=>f i+g i)=sum f+sum g := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sum_succ,sum_succ f,sum_succ g,ih]; omega

private theorem sum_single {m : Nat} (e : Fin m) (a : Nat) : sum (fun i => if i=e then a else 0)=a := by
  induction m with
  | zero => exact Fin.elim0 e
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) e
    · rw [sum_succ]
      simp [show (fun i : Fin m => if i.succ=(0 : Fin (m+1)) then a else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sum_const]
    · rw [sum_succ,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

/-- The unnormalized single-mark Bellman equation is exact at both
active states. Its finite-horizon consequence below is an upper bound. -/
theorem door_pair_drift (hn : 4≤n) (d : Fin n) (q : State) (active : q≠.done) :
    n + (List.ofFn (fun e : Fin n => potential n (next d q e))).sum=n*potential n q := by
  cases q with
  | done => exact (active rfl).elim
  | idle =>
    let f := fun e => potential n (next d .idle e)
    let charge := fun e : Fin n => if e=d then n else 0
    have E : (fun e=>f e+charge e)=(fun _ : Fin n=>4*n) := by
      funext e
      by_cases H : e=d <;> simp [f,charge,next,potential,H] <;> omega
    have B := congrArg sum E
    rw [sum_add,sum_const,show sum charge=n from sum_single d n] at B
    change n+sum f=n*(4*n)
    omega
  | armed =>
    let f := fun e => potential n (next d .armed e)
    let charge := fun e : Fin n => if e=d then 3*n else 0
    let left := fun e : Fin n => if e=predecessor d then n else 0
    let right := fun e : Fin n => if e=rightNeighbor d then n else 0
    obtain ⟨a,b,c⟩ := triple_ne hn d
    have E : (fun e=>f e+charge e)=(fun e=>3*n+left e+right e) := by
      funext e
      by_cases H : e=d
      · subst e; simp [f,charge,next,potential,left,right,Ne.symm a,c]
      by_cases L : e=predecessor d
      · subst e; simp [f,charge,next,potential,left,right,disjoint_iff,a,b]; omega
      by_cases R : e=rightNeighbor d
      · subst e; simp [f,charge,next,potential,left,right,disjoint_iff,Ne.symm b,Ne.symm c]; omega
      · simp [f,charge,next,potential,left,right,disjoint_iff,H,L,R]
    have B := congrArg sum E
    rw [sum_add,sum_add _ right,sum_add _ left,sum_const,
      show sum charge=3*n from sum_single d (3*n), show sum left=n from sum_single _ _,
      show sum right=n from sum_single _ _] at B
    change n+sum f=n*(3*n)
    omega

theorem projected_doublet_expected (hn : 4≤n) (d : Fin n) :
    Height.IIDExpectedHittingTimeAtMost (next d) (· = State.done) .idle (4*n) :=
  iid_potential_le (next d) _ (potential n)
    (fun q active => Nat.le_of_eq (door_pair_drift hn d q active)) .idle

/-- The witness carries the exact intervening raw marks, not a bound
on raw adjacency or a claim of controller eligibility. -/
def Doublet (d : Fin n) (w : List (Fin n)) : Prop :=
  ∃ pre gap tail, w=pre++d::(gap++d::tail) ∧ ∀ e∈gap,DisjointMarks d e

private def Witness (d : Fin n) (w : List (Fin n)) : State → Prop
  | .idle => True
  | .armed => ∃ pre gap,w=pre++d::gap ∧ ∀ e∈gap,DisjointMarks d e
  | .done => Doublet d w

private theorem witness_snoc (d e : Fin n) (w : List (Fin n)) (q : State)
    (W : Witness d w q) : Witness d (w++[e]) (next d q e) := by
  cases q with
  | idle =>
    by_cases H : e=d
    · subst e
      rw [next,if_pos rfl]
      exact ⟨w,[],rfl,by simp⟩
    · simp [next,H,Witness]
  | armed =>
    obtain ⟨pre,gap,E,G⟩ := W
    by_cases H : e=d
    · subst e
      rw [next,if_pos rfl]
      exact ⟨pre,gap,[],by rw [E,List.append_assoc,List.cons_append],G⟩
    · rw [next,if_neg H]
      by_cases D : DisjointMarks d e
      · rw [if_pos D]
        refine ⟨pre,gap++[e],by rw [E,List.append_assoc,List.cons_append],?_⟩
        intro f F
        rcases List.mem_append.mp F with I|I
        · exact G f I
        · exact (List.mem_singleton.mp I).symm ▸ D
      · simp [D,Witness]
  | done =>
    obtain ⟨pre,gap,tail,E,G⟩ := W
    exact ⟨pre,gap,tail++[e],by rw [E,List.append_assoc,List.cons_append,List.append_assoc,
      List.cons_append],G⟩

theorem observed_doublet (d : Fin n) (w : List (Fin n))
    (done : BStarResetSchedule.run (next d) .idle w=.done) : Doublet d w := by
  have every : ∀ v : List (Fin n), Witness d v.reverse
      (BStarResetSchedule.run (next d) .idle v.reverse) := by
    intro v
    induction v with
    | nil => trivial
    | cons e v ih =>
      rw [List.reverse_cons,BStarResetSchedule.run_append]
      exact witness_snoc d e _ _ ih
  have W := every w.reverse
  rw [List.reverse_reverse,done] at W
  exact W

private theorem flip_disjoint {d e : Fin n} (H : DisjointMarks d e) : DisjointMarks e d :=
  ⟨Ne.symm H.1,Ne.symm H.2.2.1,Ne.symm H.2.1,Ne.symm H.2.2.2⟩

/-- Bubble only the second door mark across endpoint-disjoint marks.
The exact commuted word is independent of the physical initial state. -/
theorem observed_doublet_commuted (d : Fin n) (w : List (Fin n))
    (done : BStarResetSchedule.run (next d) .idle w=.done) :
    ∃ pre gap tail,
      w=pre++d::(gap++d::tail) ∧ (∀ e∈gap,DisjointMarks d e) ∧
      Commuted w (pre++d::d::(gap++tail)) := by
  obtain ⟨pre,gap,tail,E,D⟩ := observed_doublet d w done
  refine ⟨pre,gap,tail,E,D,?_⟩
  rw [E]
  simpa only [List.append_assoc,List.singleton_append] using
    commute_prefix (pre++[d]) (bubble_door gap tail d (fun e M=>flip_disjoint (D e M)))

end L4.ProjectedDoor
