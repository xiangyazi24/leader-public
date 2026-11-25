import Leader.L4.BStarPaceBetweenCharge
import Leader.L4.BStarGeneratedTapeCuts

namespace L4.Height.ProductionAdmissions
open AllSizeProtocol BStarLongCommand BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongLayout
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarClearanceSource BStarRepeatedPace
open BStarLongFixedRouting BStarPaceCount BStarPaceLedger BStarPaceChartLedger BStarPaceBetweenCharge
open Classical
noncomputable section

private theorem first_true {n : Nat} (test : List (Fin n) → Fin n → Prop) (a w : List (Fin n)) :
    let f := fun p e => if test p e then 1 else 0
    charges f a w=0 ∨ ∃ u e v, w=u++e::v ∧ test (a++u) e ∧
      charges f a w=1+charges f ((a++u)++[e]) v := by
  dsimp only
  induction w generalizing a with
  | nil => exact .inl rfl
  | cons b w ih =>
    by_cases h : test a b
    · exact .inr ⟨[],b,w,rfl,by simpa using h,by simp [charges,h]⟩
    · rcases ih (a++[b]) with zero|⟨u,e,v,eq,yes,num⟩
      · exact .inl (by simp [charges,h,zero])
      · refine .inr ⟨b::u,e,v,congrArg (List.cons b) eq,?_,?_⟩
        · simpa only [List.append_assoc,List.singleton_append] using yes
        · simp only [charges,if_neg h,Nat.zero_add]
          simpa only [List.append_assoc,List.singleton_append] using num

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

def issues (ini : X) (root : Fin n) (a : List (Fin n)) (e : Fin n) : Prop :=
  let x := run ini a
  e=RearTrace.predecessor root ∧ Launch (x root).long (step x e root).long ∧
    (ctrlOp.read (x root).long).toNat=admit

def count (ini : X) (root : Fin n) (a w : List (Fin n)) :=
  charges (fun b e => if issues hp ini root b e then 1 else 0) a w

private theorem split_issue {base ini : X} {addr : Nat → Pos n} {len : Nat}
    {a u v : List (Fin n)} {e : Fin n} {m d : Mode}
    (G : GeneratedOwner hp base addr len (run ini a) m (u++e::v) d)
    (hit : issues hp ini (addr 0).1 (a++u) e) :
    GeneratedOwner hp base addr len (run ini a) m u .idle ∧
    Ready4 addr (run ini (a++u)) .idle ∧
    GeneratedOwner hp base addr len (run ini ((a++u)++[e])) (.busy admit (.out 0)) v d := by
  obtain ⟨mode,head,tail⟩ := BStarGeneratedTapeCuts.split hp u (e::v) G
  obtain ⟨door,L,pc⟩ := hit
  rw [BStarResetSchedule.run_append] at L pc
  cases tail with
  | next cur ev rest =>
    have oldIdle := idle_of_issue hp cur L.1
    subst mode
    refine ⟨head,⟨rfl,by rwa [BStarResetSchedule.run_append]⟩,?_⟩
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    change GeneratedOwner hp base addr len (step (run (run ini a) u) e) (.busy admit (.out 0)) v d
    cases ev with
    | idle_hold bad => exact (bad door).elim
    | bad_issue _ bad =>
      obtain ⟨b,ib,_⟩ := L.2
      rw [bad] at ib
      contradiction
    | launch _ _ => exact pc ▸ rest

private theorem prepend_gap {base ini : X} {addr : Nat → Pos n} {len k : Nat} {b w : List (Fin n)}
    (I : PaidIntervals hp base ini addr len b w k) (a gap : List (Fin n)) (eq : b=a++gap) :
    PaidIntervals hp base ini addr len a (gap++w) k := by
  cases I with
  | nil => exact .nil _ _
  | @cons b skip tour rest k trail ready tail =>
    subst b
    have out := PaidIntervals.cons (hp:=hp) (base:=base) (initial:=ini) (addr:=addr) (len:=len)
      (a:=a) (gap:=gap++skip) (tour:=tour) (rest:=rest) (k:=k)
      (by simpa only [List.append_assoc] using trail)
      (by simpa only [List.append_assoc] using ready)
      (by simpa only [List.append_assoc] using tail)
    simpa only [List.append_assoc] using out

private theorem paid_bounded {base ini : X} {addr : Nat → Pos n} {len : Nat} (fuel : Nat) :
    ∀ (a w : List (Fin n)),w.length≤fuel → ∀ {d : Mode},
      GeneratedOwner hp base addr len (run ini a) (.busy admit (.out 0)) w d →
      PaidIntervals hp base ini addr len a w (count hp ini (addr 0).1 a w) := by
  induction fuel with
  | zero =>
    intro a w within d G
    have empty : w=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero within)
    subst w
    exact .nil _ _
  | succ fuel ih =>
    intro a w within d G
    let root := (addr 0).1
    rcases first_true (issues hp ini root) a w with zero|⟨u,e,v,eq,yes,num⟩
    · change count hp ini (addr 0).1 a w=0 at zero
      rw [zero]
      exact .nil _ _
    · have smaller : v.length≤fuel := by
        rw [eq,List.length_append,List.length_cons] at within
        omega
      subst w
      obtain ⟨previous,ready,tail⟩ := split_issue hp G yes
      have nextPaid := ih ((a++u)++[e]) v smaller tail
      have joined := prepend_gap hp nextPaid (a++u) [e] rfl
      change count hp ini (addr 0).1 a (u++e::v)=1+count hp ini (addr 0).1 ((a++u)++[e]) v at num
      rw [num,Nat.add_comm 1]
      apply PaidIntervals.cons (gap:=[]) (tour:=u) (rest:=e::v)
      · simpa only [List.append_nil] using previous
      · simpa only [List.append_nil] using ready
      · simpa only [List.append_nil,List.singleton_append] using joined

/-- Each genuine launch closes one disjoint, generated interval at ready ISSUE4. -/
theorem paid_after_launch {base ini : X} {addr : Nat → Pos n} {len : Nat}
    (a w : List (Fin n)) {d : Mode}
    (G : GeneratedOwner hp base addr len (run ini a) (.busy admit (.out 0)) w d) :
    PaidIntervals hp base ini addr len a w (count hp ini (addr 0).1 a w) :=
  paid_bounded hp w.length a w (Nat.le_refl _) G

/-- The first new issue on an arbitrary suffix is free. Every further launch
has PaidIntervals evidence on the actual tape. -/
theorem all_launch_intervals {base ini : X} {addr : Nat → Pos n} {len : Nat}
    (a w : List (Fin n)) {m d : Mode} (G : GeneratedOwner hp base addr len (run ini a) m w d) :
    PaidIntervals hp base ini addr len a w (count hp ini (addr 0).1 a w-1) := by
  let root := (addr 0).1
  rcases first_true (issues hp ini root) a w with zero|⟨u,e,v,eq,yes,num⟩
  · change count hp ini (addr 0).1 a w=0 at zero
    rw [zero]
    exact .nil _ _
  · subst w
    obtain ⟨_,_,tail⟩ := split_issue hp G yes
    have tailPaid := paid_after_launch hp ((a++u)++[e]) v tail
    change count hp ini (addr 0).1 a (u++e::v)=1+count hp ini (addr 0).1 ((a++u)++[e]) v at num
    rw [num,Nat.add_comm 1,Nat.add_sub_cancel]
    simpa only [List.append_assoc,List.singleton_append] using
      prepend_gap hp tailPaid a (u++[e]) (List.append_assoc ..)

/-- The first ADMIT of an arbitrary observed suffix needs no charge. Every
later launch has a disjoint paid traversal on that same suffix. -/
theorem all_launch_excess {base ini : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ b j, Layout B base j=Layout B (run ini b) j)
    (a w : List (Fin n)) {m d : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len (run ini a) m w d) :
    len*(count hp ini (S.getD 0 fall).1 a w-1) ≤
      charges (rawCharge hp base ini (fun j=>S.getD j fall) len) a w :=
  intervals_charge hp C sep layout (all_launch_intervals hp a w G)

#print axioms all_launch_intervals
#print axioms all_launch_excess
end
end L4.Height.ProductionAdmissions

