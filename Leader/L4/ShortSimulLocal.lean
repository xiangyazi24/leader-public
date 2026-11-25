import Leader.L4.ShortActualIssueClock
import Leader.L4.ShortLeastForward
import Leader.L4.ShortClearLaunch

namespace L4.ShortSimulLocal
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetChart ShortResetCycle
open ShortClearLaunch
open ShortResetWatch ShortPhaseRank ShortInheritedRank ShortActualIssueClock

def Fiber {s n : Nat} (h : Fin n → Bool) (x : Raw s n) : Prop :=
  H2Ready x ∧ ∀ q,header x q=h q

def modeNext {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Option Stage) (e : Fin n) : Option Stage :=
  match st with
  | none =>
      if Issuable C x ∧ e=RearTrace.predecessor C.root then some (.fwd 0) else none
  | some u => some (nextStage C e u)

def Valid {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) : Option Stage → Prop
  | none => True
  | some u => u≠.done ∧ Active C x u

def Done {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Option Stage) : Prop := st=some .done ∧ Complete C x

def seeking {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Nat :=
  2*C.L+1 + if Issuable C x then 0 else chartRank C 505 (rail C) (projection C x)

def score {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) : Option Stage → Nat
  | none => seeking C x
  | some u => debt C.L u

theorem door_mem {n : Nat} {h : Fin n → Bool} (C : Chart h) :
    RearTrace.predecessor C.root∈watch C :=
  (watch_incident C _).mpr ⟨0,C.positive,.inr (RearTrace.right_predecessor C.root).symm⟩

private theorem edge_mem {n : Nat} {h : Fin n → Bool} (C : Chart h) (i : Nat)
    (I : i<C.L) : nextAt C.root i ∈ watch C :=
  (mem_watch C _).mpr (.inr ⟨i,I,rfl⟩)

theorem next_valid {s n : Nat} {h : Fin n → Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (y : Option Stage) (e : Fin n) (F : Fiber h x) (V : Valid C x y) :
    Done C (rawNext s x e) (modeNext C x y e) ∨ Valid C (rawNext s x e) (modeNext C x y e) := by
  cases y with
  | none =>
    simp only [modeNext]
    by_cases E : Issuable C x ∧ e=RearTrace.predecessor C.root
    · rw [if_pos E]
      apply Or.inr
      have A := (actual_issue C N x F.2 E.1).2
      rw [E.2]
      exact ⟨by decide,A⟩
    · rw [if_neg E]
      exact .inr trivial
  | some st =>
    have G := active_step C x e (by omega) F.2 st V.1 V.2
    by_cases D : nextStage C e st=.done
    · rw [D] at G
      exact .inl ⟨congrArg some D,G⟩
    · exact .inr ⟨D,G⟩

theorem score_bounds {s n : Nat} {h : Fin n → Bool} (C : Chart h) (S : C.L≤9)
    (x : Raw s n) (y : Option Stage) (V : Valid C x y) :
    0<score C x y ∧ score C x y<8115 := by
  cases y with
  | none =>
    have B := chartRank_cap C 505 (rail C) (projection C x) (rail_cap C S _)
    change 0<seeking C x ∧ seeking C x<8115
    unfold seeking
    split <;> omega
  | some st =>
    cases st with
    | done => exact False.elim (V.1 rfl)
    | fwd i =>
      have I := V.2.1
      change 0<2*C.L-i ∧ 2*C.L-i<8115
      omega
    | rev i =>
      have I := V.2.1
      change 0<i+1 ∧ i+1<8115
      omega

private theorem forwardNominate {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (S : C.L≤9) (N : 5≤n) (Nom : ForwardNomination (s:=s) C)
    (x : Raw s n) (A : Fiber h x) (notIssue : ¬Issuable C x) :
    ∃ e∈watch C, seeking C (rawNext s x e)<seeking C x := by
  obtain ⟨e,W,drop⟩ := chart_nominate C N x ((A.2 _).trans C.rootHeader) notIssue
    505 (rail C) (fun _=>rail_cap C S _)
    (fun _ _ _ Held=>rail_nominate_held C S N Nom x A.1 A.2 Held)
  refine ⟨e,W,?_⟩
  unfold seeking
  rw [if_neg notIssue]
  split <;> omega

private theorem stage_drop {n : Nat} {h : Fin n → Bool} (C : Chart h) (st : Stage)
    (valid : match st with | .done => False | .fwd k | .rev k => k<C.L) :
    ∃ e∈watch C, debt C.L (nextStage C e st)<debt C.L st := by
  cases st with
  | done => exact False.elim valid
  | fwd i =>
    change i<C.L at valid
    refine ⟨nextAt C.root i,edge_mem C i valid,?_⟩
    by_cases H : i+1<C.L
    · simp only [nextStage,if_true,if_pos H,debt]; omega
    · simp only [nextStage,if_true,if_neg H,debt]; omega
  | rev i =>
    cases i with
    | zero => exact ⟨RearTrace.predecessor C.root,door_mem C,by simp [nextStage,debt,RearTrace.right_predecessor]⟩
    | succ j =>
      change j+1<C.L at valid
      exact ⟨nextAt C.root j,edge_mem C j (by omega),by simp [nextStage,debt]⟩

private def stageValid (L : Nat) : Stage → Prop
  | .done => False
  | .fwd k | .rev k => k<L

private theorem stage_valid {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Stage) (V : Valid C x (some st)) : stageValid C.L st := by
  cases st
  · exact V.2.1
  · exact V.2.1
  · exact V.1 rfl

theorem nominate {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (S : C.L≤9) (N : 5≤n) (Nom : ForwardNomination (s:=s) C)
    (x : Raw s n) (y : Option Stage) (A : Fiber h x) (V : Valid C x y) :
    ∃ e∈watch C, score C (rawNext s x e) (modeNext C x y e)<score C x y := by
  cases y with
  | none =>
    by_cases E : Issuable C x
    · let d := RearTrace.predecessor C.root
      refine ⟨d,door_mem C,?_⟩
      have Q : modeNext C x none d=some (.fwd 0) := if_pos ⟨E,rfl⟩
      rw [Q]
      change 2*C.L-0 < seeking C x
      unfold seeking
      rw [if_pos E]
      omega
    · obtain ⟨e,W,D⟩ := forwardNominate C S N Nom x A E
      exact ⟨e,W,by simpa only [modeNext,E,false_and,if_false,score] using D⟩
  | some st =>
    have L := stage_valid C x st V
    exact stage_drop C st L

private theorem stage_idle {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (e : Fin n) (E : e∉watch C) (st : Stage) (V : stageValid C.L st) :
    nextStage C e st=st := by
  cases st with
  | done => rfl
  | fwd i =>
    have X : e≠nextAt C.root i := fun h=>E (h.symm ▸ edge_mem C i V)
    simp [nextStage,X]
  | rev i =>
    cases i with
    | zero =>
      have X : rightNeighbor e≠C.root := fun h=>E ((watch_incident C e).mpr
        ⟨0,C.positive,.inr h.symm⟩)
      simp [nextStage,X]
    | succ j =>
      have B : j+1<C.L := V
      have X : e≠nextAt C.root j := fun h=>E (h.symm ▸ edge_mem C j (by omega))
      simp [nextStage,X]

theorem idle {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (y : Option Stage) (e : Fin n) (V : Valid C x y) (E : e∉watch C) :
    ¬Done C (rawNext s x e) (modeNext C x y e) ∧
      score C (rawNext s x e) (modeNext C x y e)=score C x y := by
  cases y with
  | none =>
    have d : e≠RearTrace.predecessor C.root := fun h=>E (h.symm ▸ door_mem C)
    have R := outside_root C x e E
    have Z := outside_projection C x e E
    have eq : modeNext C x none e=none := by simp [modeNext,d]
    rw [eq]
    constructor
    · simp [Done]
    · simp [score,seeking,Issuable,R,Z]
  | some u =>
    have L := stage_idle C e E u (stage_valid C x u V)
    simp only [modeNext,L,score]
    exact ⟨fun d=>V.1 (Option.some.inj d.1),trivial⟩

/-- Earlier completed charts stay complete on any word not selecting
their own door, even when another owner has overlapping physical sites. -/
theorem complete_nondoor {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ q,header x q=h q) (e : Fin n)
    (A : Complete C x) (E : e≠RearTrace.predecessor C.root) :
    Complete C (rawNext s x e) := by
  have G : ClearIssue C x 1 := ⟨by decide,A.1,A.2.1,A.2.2⟩
  have L := clear_issue_nondoor C x heads 1 G e E
  exact ⟨L.2.1,L.2.2.1,L.2.2.2⟩

theorem complete_can_redirty {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ q,header x q=h q) (A : Complete C x) :
    ¬Complete C (rawNext s x (RearTrace.predecessor C.root)) := by
  have G : ClearIssue C x 1 := ⟨by decide,A.1,A.2.1,A.2.2⟩
  have L := clean_launch C x heads 1 G
  intro P
  have S := L.1.symm.trans P.2.1
  contradiction

end L4.ShortSimulLocal
