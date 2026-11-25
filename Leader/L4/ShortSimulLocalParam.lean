import Leader.L4.ShortInheritedRankParam
import Leader.L4.ShortSimulLocal

namespace L4.ShortSimulLocalParam
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetChart ShortResetCycle
open ShortClearLaunch
open ShortResetWatch ShortPhaseRank ShortActualIssueClock
open ShortInheritedRank (ForwardNomination)
open ShortInheritedRankParam
open ShortSimulLocal (Fiber modeNext Valid Done door_mem)

def phaseCap (limit : Nat) : Nat :=
  2*limit+2 + (15*(railCap limit+1)+railCap limit)

def seeking {s n : Nat} {h : Fin n → Bool} (C : Chart h) (limit : Nat) (x : Raw s n) : Nat :=
  2*C.L+1 + if Issuable C x then 0 else chartRank C (railCap limit) (rail C limit) (projection C x)

def score {s n : Nat} {h : Fin n → Bool} (C : Chart h) (limit : Nat)
    (x : Raw s n) : Option Stage → Nat
  | none => seeking C limit x
  | some u => debt C.L u

private theorem edge_mem {n : Nat} {h : Fin n → Bool} (C : Chart h) (i : Nat)
    (I : i<C.L) : nextAt C.root i ∈ watch C :=
  (mem_watch C _).mpr (.inr ⟨i,I,rfl⟩)

theorem score_bounds {s n : Nat} {h : Fin n → Bool} (C : Chart h) (limit : Nat) (S : C.L≤limit)
    (x : Raw s n) (y : Option Stage) (V : Valid C x y) :
    0<score C limit x y ∧ score C limit x y<phaseCap limit := by
  cases y with
  | none =>
    have B := chartRank_cap C (railCap limit) (rail C limit) (projection C x) (rail_cap C limit S _)
    change 0<seeking C limit x ∧ seeking C limit x<phaseCap limit
    unfold seeking phaseCap
    split <;> omega
  | some st =>
    cases st with
    | done => exact False.elim (V.1 rfl)
    | fwd i =>
      have I := V.2.1
      change 0<2*C.L-i ∧ 2*C.L-i<phaseCap limit
      unfold phaseCap
      omega
    | rev i =>
      have I := V.2.1
      change 0<i+1 ∧ i+1<phaseCap limit
      unfold phaseCap
      omega

private theorem forwardNominate {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (limit : Nat) (S : C.L≤limit) (N : 5≤n) (Nom : ForwardNomination (s:=s) C)
    (x : Raw s n) (A : Fiber h x) (notIssue : ¬Issuable C x) :
    ∃ e∈watch C, seeking C limit (rawNext s x e)<seeking C limit x := by
  obtain ⟨e,W,drop⟩ := chart_nominate C N x ((A.2 _).trans C.rootHeader) notIssue
    (railCap limit) (rail C limit) (fun _=>rail_cap C limit S _)
    (fun _ _ _ Held=>rail_nominate_held C limit S N Nom x A.1 A.2 Held)
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
    (limit : Nat) (S : C.L≤limit) (N : 5≤n) (Nom : ForwardNomination (s:=s) C)
    (x : Raw s n) (y : Option Stage) (A : Fiber h x) (V : Valid C x y) :
    ∃ e∈watch C, score C limit (rawNext s x e) (modeNext C x y e)<score C limit x y := by
  cases y with
  | none =>
    by_cases E : Issuable C x
    · let d := RearTrace.predecessor C.root
      refine ⟨d,door_mem C,?_⟩
      have Q : modeNext C x none d=some (.fwd 0) := if_pos ⟨E,rfl⟩
      rw [Q]
      change 2*C.L-0 < seeking C limit x
      unfold seeking
      rw [if_pos E]
      omega
    · obtain ⟨e,W,D⟩ := forwardNominate C limit S N Nom x A E
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

theorem idle {s n : Nat} {h : Fin n → Bool} (C : Chart h) (limit : Nat)
    (x : Raw s n) (y : Option Stage) (e : Fin n) (V : Valid C x y) (E : e∉watch C) :
    ¬Done C (rawNext s x e) (modeNext C x y e) ∧
      score C limit (rawNext s x e) (modeNext C x y e)=score C limit x y := by
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

#print axioms score_bounds
#print axioms nominate
#print axioms idle
end L4.ShortSimulLocalParam
