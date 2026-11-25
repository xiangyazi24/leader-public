import Leader.L4.ShortInheritedRank

namespace L4.ShortActualIssueClock
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetCycle ShortResetMIS1Ring ShortPhaseRank ShortControllerEntrance
open ShortForwardRank

abbrev Issuable {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Prop :=
  pc (x C.root).mis1=8

theorem issuable_fields {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (I : Issuable C x) :
    get (x C.root).mis1 81 2 (by decide)=1 ∧ get (x C.root).mis1 78 3 (by decide)=0 := by
  have H := pc_fields (x C.root).mis1
  have O : get (x C.root).mis1 78 3 (by decide)<8 :=
    ((lane 78 3 (by decide)).read (x C.root).mis1).isLt
  unfold Issuable at I
  omega

/-- ISSUE0 remains literal at the physical root until the actual incoming
owner door is marked, even if a nondoor mark changes the packet bytes. -/
theorem issuable_nondoor {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (headerTrue : header x C.root=true) (I : Issuable C x) (e : Fin n)
    (NE : e≠RearTrace.predecessor C.root) : Issuable C (rawNext s x e) := by
  unfold Issuable at I ⊢
  by_cases E : e=C.root
  · subst e
    have F := reset_controller_outgoing_raw x C.root headerTrue
    rw [pc_fields,F.1,F.2,←pc_fields]
    exact I
  · have R : C.root≠rightNeighbor e := by
      intro B
      apply NE
      rw [B,RearTrace.predecessor_right]
    rw [reset_remote_frame_raw _ _ _ (Ne.symm E) R]
    exact I

/-- The observer bit is set only by an actual owner-door interaction from
the literal old ISSUE0. It never changes any physical transition. -/
def step {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (z : Raw s n × Bool) (e : Fin n) : Raw s n × Bool :=
  (rawNext s z.1 e,z.2 || decide (Issuable C z.1 ∧ e=RearTrace.predecessor C.root))

def Goal {s n : Nat} {h : Fin n → Bool} (C : Chart h) (z : Raw s n × Bool) : Prop :=
  z.2=true ∧ Complete C z.1

theorem actual_issue {s n : Nat} {h : Fin n → Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (heads : ∀ j,header x j=h j) (I : Issuable C x) :
    let d := RearTrace.predecessor C.root
    let z := step C (x,false) d
    z.2=true ∧ Active C z.1 (.fwd 0) := by
  let d := RearTrace.predecessor C.root
  have R : rightNeighbor d=C.root := RearTrace.right_predecessor C.root
  obtain ⟨P,O⟩ := issuable_fields C x I
  have B := begin_reset C x d (edge_sep (by omega) d) R ((heads _).trans C.rootHeader) P O
  refine ⟨by simpa [step] using I,C.positive,B.1,?_,B.2⟩
  intro i J
  omega

theorem post_cost {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (t : Nat) (x : Raw s n) :
    Height.iidHitCost (step C) (Goal C) t (x,true)=
      Height.iidHitCost (rawNext s) (Complete C) t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t IH =>
    by_cases H : Complete C x
    · rw [Height.iidHitCost_of_target _ _ _ (show Goal C (x,true) from ⟨rfl,H⟩),
          Height.iidHitCost_of_target _ _ _ H]
    · have Z : ¬Goal C (x,true) := fun A=>H A.2
      simp only [Height.iidHitCost,if_neg Z,if_neg H]
      congr 1
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      exact IH _

theorem clean_expected_from_issue0 {s n : Nat} {h : Fin n → Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (Q : H2Ready x) (heads : ∀ j,header x j=h j) (I : Issuable C x) :
    Height.IIDExpectedHittingTimeAtMost (step C) (Goal C) (x,false) ((2*C.L+1)*n) := by
  let B := (2*C.L+1)*n
  let d := RearTrace.predecessor C.root
  intro t
  induction t generalizing x with
  | zero => simp [Height.iidHitCost]
  | succ t IH =>
    have G : ¬Goal C (x,false) := by simp [Goal]
    simp only [Height.iidHitCost,if_neg G]
    let f := fun e : Fin n => Height.iidHitCost (step C) (Goal C) t (step C (x,false) e)
    let g := fun e : Fin n => if e=d then 2*C.L*n*n^t else B*n^t
    have P : (List.ofFn f).sum≤(List.ofFn g).sum := by
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      by_cases E : e=d
      · subst e
        have X : step C (x,false) d=(rawNext s x d,true) := by simpa [step,d] using I
        obtain ⟨F,O⟩ := issuable_fields C x I
        have M := completed_reset_mean_of_issue C N x d Q heads
          (RearTrace.right_predecessor C.root) F O t
        simpa [f,g,X,post_cost] using M
      · have X : step C (x,false) e=(rawNext s x e,false) := by simp [step,show e≠RearTrace.predecessor C.root from E]
        have J := issuable_nondoor C x ((heads _).trans C.rootHeader) I e E
        have H : ∀ q,header (rawNext s x e) q=h q :=
          fun q=>(PhysicalCustody.H1.raw_h1_selected_frozen N x e q Q.1).trans (heads q)
        simpa [f,g,X,E,B] using IH _ (h2_ready_closed N x e Q) H J
    have sumG := PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const d g (B*n^t)
      (fun e E=>if_neg E)
    rw [sumG] at P
    simp only [g,if_true] at P
    change n^(t+1)+(List.ofFn f).sum≤B*n^(t+1)
    have npos : 0<n := by omega
    have Eq : n + 2*C.L*n + (n-1)*B = n*B := by
      have H : n + 2*C.L*n = B := by simp [B,Nat.add_mul,Nat.add_comm]
      rw [H]
      calc
        B+(n-1)*B=(1+(n-1))*B := by rw [Nat.add_mul,Nat.one_mul]
        _=n*B := by rw [show 1+(n-1)=n by omega]
    calc
      _ ≤ n^(t+1)+(2*C.L*n*n^t+(n-1)*(B*n^t)) := Nat.add_le_add_left P _
      _ = B*n^(t+1) := by
        rw [Nat.pow_succ]
        calc
          _ = n*n^t + (2*C.L*n*n^t+(n-1)*(B*n^t)) := by rw [Nat.mul_comm (n^t) n]
          _ = (n*B)*n^t := by
            rw [←Nat.mul_assoc (n-1) B (n^t), ←Nat.add_mul, ←Nat.add_mul, ←Nat.add_assoc, Eq]
          _ = _ := by ac_rfl

/-- The scheduler-tree formulations in the L4 statement and Height
layers agree pointwise, including the time-zero target check. -/
private theorem hitCost_eq {X : Type} {n : Nat} (next : X→Fin n→X) (P : X→Prop)
    (t : Nat) (x : X) : Height.iidHitCost next P t x=L4.iidHitCost next P t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t IH =>
    by_cases H : P x
    · simp [Height.iidHitCost,L4.iidHitCost,H]
    · simp only [Height.iidHitCost,L4.iidHitCost,if_neg H]
      congr 1
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      exact fun e=>IH (next x e)

/-- A history-safe Bellman composition: before the first ISSUE0 prefix
the observer remains false and the exact raw cost plus the later clean
budget bounds its completion cost. -/
theorem clean_cost_via_issue0 {s n : Nat} {h : Fin n → Bool} (C : Chart h) (N : 5≤n)
    (t : Nat) (x : Raw s n) (Q : H2Ready x) (heads : ∀ j,header x j=h j) :
    Height.iidHitCost (step C) (Goal C) t (x,false) ≤
      Height.iidHitCost (rawNext s) (Issuable C) t x + ((2*C.L+1)*n)*n^t := by
  let B := (2*C.L+1)*n
  induction t generalizing x with
  | zero => simp [Height.iidHitCost]
  | succ t IH =>
    by_cases I : Issuable C x
    · rw [Height.iidHitCost_of_target _ _ _ I,Nat.zero_add]
      exact clean_expected_from_issue0 C N x Q heads I _
    · have G : ¬Goal C (x,false) := by simp [Goal]
      simp only [Height.iidHitCost,if_neg G,if_neg I]
      let f := fun e : Fin n=>Height.iidHitCost (rawNext s) (Issuable C) t (rawNext s x e)
      have P : (List.ofFn (fun e : Fin n=>
          Height.iidHitCost (step C) (Goal C) t (step C (x,false) e))).sum ≤
          (List.ofFn (fun e : Fin n=>f e+B*n^t)).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_le
        intro e
        have Y : step C (x,false) e=(rawNext s x e,false) := by simp [step,I]
        have H : ∀ q,header (rawNext s x e) q=h q :=
          fun q=>(PhysicalCustody.H1.raw_h1_selected_frozen N x e q Q.1).trans (heads q)
        rw [Y]
        exact IH _ (h2_ready_closed N x e Q) H
      rw [FiniteUniformStoppingTree.ofFn_sum_add,FiniteUniformStoppingTree.ofFn_sum_const] at P
      have E : n*(B*n^t)=B*n^(t+1) := by rw [Nat.pow_succ]; ac_rfl
      rw [E] at P
      apply Nat.le_trans (Nat.add_le_add_left P _)
      rw [Nat.add_assoc]
      exact Nat.le_refl _

/-- The genuinely issued and physically completed owner reset, on the
same raw tape, conditional solely on the arbitrary-forward nomination. -/
theorem from_inherited_expected {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (small : C.L≤9) (N : 5≤n) (Nom : ShortInheritedRank.ForwardNomination (s := s) C)
    (x : Raw s n) (Q : H2Ready x) (heads : ∀ j,header x j=h j) :
    Height.IIDExpectedHittingTimeAtMost (step C) (Goal C) (x,false)
      ((10^8095+19)*n) := by
  intro t
  have B := ShortInheritedRank.issue0_expected C small N Nom x Q heads t
  change L4.iidHitCost (rawNext s) (Issuable C) t x≤_ at B
  rw [←hitCost_eq] at B
  have D : ((2*C.L+1)*n)*n^t ≤ (19*n)*n^t :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have E' (k : Nat) : (n*k)*n^t + (19*n)*n^t = ((k+19)*n)*n^t := by
    rw [←Nat.add_mul,Nat.add_mul k 19 n,Nat.mul_comm n k]
  have E := E' (10^8095)
  rw [←E]
  exact Nat.le_trans (clean_cost_via_issue0 C N t x Q heads) (Nat.add_le_add B D)

end L4.ShortActualIssueClock
