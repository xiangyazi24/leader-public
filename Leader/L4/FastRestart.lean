import Leader.L4.RankAttempt

/-! Property P3 on exact finite IID raw-edge words. All probabilities are
cross-multiplied. The repeated restart uses a bound from every starting
state in a forward-closed domain. -/
namespace L4.FastRestart
open TaggedTail Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f=f 0+sumEdge (fun i : Fin n => f i.succ) := by simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih fun i => h i.succ)

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e)=a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

private theorem block_comp {α : Type} {n : Nat} (next : α → Fin n → α)
    (live : α → Prop) (b u : Nat) (x : α) :
    survival next live (b+u) x=weightedSurvival next live (survival next live u) b x := by
  induction b generalizing x with
  | zero =>
    by_cases h : live x
    · simp [weightedSurvival,h]
    · cases u <;> simp [survival,weightedSurvival,h]
  | succ b ih =>
    rw [show b+1+u=b+u+1 by omega]
    by_cases h : live x
    · simp only [survival,weightedSurvival,h,if_true]
      exact congrArg sumEdge (funext (fun e => ih (next x e)))
    · simp [survival,weightedSurvival,h]

private theorem scaled_mass {α : Type} {n : Nat} (next : α → Fin n → α)
    (I live : α → Prop) (closed : ∀ x e, I x → I (next x e))
    (w : α → Nat) (a c b : Nat) (h : ∀ x, I x → a*w x≤c) (x : α) (hx : I x) :
    a*weightedSurvival next live w b x≤c*survival next live b x := by
  induction b generalizing x with
  | zero => by_cases hl : live x <;> simp [survival,weightedSurvival,hl,h x hx]
  | succ b ih =>
    by_cases hl : live x
    · simp only [survival,weightedSurvival,hl,if_true,←sScale]
      exact sMono (fun e => ih (next x e) (closed x e hx))
    · simp [survival,weightedSurvival,hl]

/-- One Markov block: positive mu suffices for cancellation. An empty
edge alphabet still satisfies the integer inequality, but does not
define the intended probability law. -/
theorem half_block {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : α → Prop) (μ : Nat) (hμ : 0<μ) (x : α)
    (mean : IIDExpectedHittingTimeAtMost next D x μ) :
    2*survival next (fun y => ¬D y) (2*μ) x≤n^(2*μ) := by
  have h := Nat.le_trans (RankPhysical.horizon_mul_survival_le_cost next D (2*μ) x)
    (mean (2*μ))
  apply Nat.le_of_mul_le_mul_left _ hμ
  have hh : μ*(2*survival next (fun y => ¬D y) (2*μ) x) =
      (2*μ)*survival next (fun y => ¬D y) (2*μ) x := by ac_rfl
  rwa [hh]

/-- P3 repeated restart. No target closure is required to count words
that never enter the target, since that statistic is killed at first hit. -/
theorem restart_tail {α : Type} {n : Nat} (next : α → Fin n → α)
    (I D : α → Prop) (closed : ∀ x e, I x → I (next x e))
    (μ : Nat) (hμ : 0<μ)
    (mean : ∀ x, I x → IIDExpectedHittingTimeAtMost next D x μ)
    (j : Nat) (x : α) (hx : I x) :
    2^j*survival next (fun y => ¬D y) (j*(2*μ)) x≤n^(j*(2*μ)) := by
  induction j generalizing x with
  | zero => by_cases h : D x <;> simp [survival,weightedSurvival,h]
  | succ j ih =>
    let b := 2*μ
    let l := fun y => ¬D y
    have hM := scaled_mass next I l closed (survival next l (j*b))
      (2^j) (n^(j*b)) b (fun y hy => ih y hy) x hx
    rw [←block_comp] at hM
    have hH := half_block next D μ hμ x (mean x hx)
    calc
      _ = 2*(2^j*survival next l (b+j*b) x) := by
        rw [Nat.succ_mul,Nat.pow_succ]
        have hh : j*(2*μ)+2*μ=b+j*b := by dsimp [b]; ac_rfl
        rw [hh]
        ac_rfl
      _ ≤ 2*(n^(j*b)*survival next l b x) := Nat.mul_le_mul_left _ hM
      _ = n^(j*b)*(2*survival next l b x) := by ac_rfl
      _ ≤ n^(j*b)*n^b := Nat.mul_le_mul_left _ hH
      _ = _ := by rw [Nat.succ_mul,Nat.pow_add]

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem cost_split {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : α → Prop) (B t : Nat) (x : α) :
    iidHitCost next D (B+t) x≤B*n^(B+t) +
      weightedSurvival next (fun y => ¬D y) (iidHitCost next D t) B x := by
  induction B generalizing x with
  | zero =>
    by_cases h : D x
    · rw [show 0+t=t by omega,iidHitCost_of_target next D x h]
      exact Nat.zero_le _
    · simp [weightedSurvival,h]
  | succ B ih =>
    rw [show B+1+t=B+t+1 by omega]
    by_cases h : D x
    · rw [iidHitCost_of_target next D x h]
      exact Nat.zero_le _
    · simp only [iidHitCost,weightedSurvival,h,not_false_eq_true,if_true,if_false]
      apply Nat.le_trans (Nat.add_le_add_left (sMono fun e => ih (next x e)) _) ?_
      rw [sAdd,sConst,Nat.add_mul,Nat.one_mul]
      have hh : n*(B*n^(B+t))=B*n^(B+t+1) := by rw [Nat.pow_succ]; ac_rfl
      rw [hh]
      omega

/-- A half-survival block, uniform on a closed domain, integrates to
mean at most twice the block length. No target closure is needed:
continuations are charged only on words that have not hit yet. -/
theorem mean_of_half_block {α : Type} {n : Nat} (next : α → Fin n → α)
    (I D : α → Prop) (closed : ∀ x e, I x → I (next x e))
    (B : Nat) (hB : 0<B)
    (half : ∀ x, I x → 2*survival next (fun y => ¬D y) B x≤n^B)
    (x : α) (hx : I x) :
    IIDExpectedHittingTimeAtMost next D x (2*B) := by
  intro t
  revert x
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro x hx
    by_cases ht : t<B
    · exact Nat.le_trans (iidHitCost_le_horizon next D t x)
        (Nat.mul_le_mul_right _ (by omega))
    · obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le (show B≤t by omega)
      have hu : u<B+u := by omega
      have he := scaled_mass next I (fun y => ¬D y) closed (iidHitCost next D u)
        1 ((2*B)*n^u) B (fun y hy => by simpa only [Nat.one_mul] using ih u hu y hy) x hx
      rw [Nat.one_mul] at he
      have hb : (2*B)*n^u*survival next (fun y => ¬D y) B x≤B*n^(B+u) := by
        calc
          _ = (B*n^u)*(2*survival next (fun y => ¬D y) B x) := by ac_rfl
          _ ≤ (B*n^u)*n^B := Nat.mul_le_mul_left _ (half x hx)
          _ = _ := by rw [Nat.pow_add]; ac_rfl
      refine Nat.le_trans (cost_split next D B u x) (Nat.le_trans
        (Nat.add_le_add_left (Nat.le_trans he hb) _) ?_)
      rw [Nat.mul_assoc,Nat.two_mul]
      exact Nat.le_refl _

/-- On a closed domain, previously attained closed targets are never
lost. The miss count of their intersection admits the finite union
bound, even though target events use the same overlapping raw marks. -/
theorem intersection_survival_le {α : Type} {n K : Nat} (next : α → Fin n → α)
    (I : α → Prop) (D : Fin K → α → Prop)
    (closed : ∀ x e, I x → I (next x e))
    (keep : ∀ i x e, I x → D i x → D i (next x e))
    (t : Nat) (x : α) (hx : I x) :
    survival next (fun y => ¬∀ i, D i y) t x ≤
      sumEdge (fun i => survival next (fun y => ¬D i y) t x) := by
  let A := {y : α // I y}
  let move (y : A) (e : Fin n) : A := ⟨next y.val e,closed y.val e y.property⟩
  let l (i : Fin K) (y : A) := ¬ D i y.val
  let z : A := ⟨x,hx⟩
  have hp := RankPhysical.equal_survival_of_projection next move
    (fun y => ¬∀ i, D i y) Subtype.val (fun _ _ => rfl) t z
  have he : (fun y : A => ¬∀ i, D i y.val) = fun y => ∃ i, l i y := by
    funext y
    exact propext not_forall
  rw [he] at hp
  rw [←hp]
  apply Nat.le_trans (survival_union move l (fun i y e h hd => h (keep i y.val e y.property hd)) t z)
  apply Nat.le_of_eq
  apply congrArg sumEdge
  funext i
  exact RankPhysical.equal_survival_of_projection next move (fun y => ¬D i y)
    Subtype.val (fun _ _ => rfl) t z

/-- Explicit logarithmic horizon interface: if 2K≤2^j, the joint
miss mass at j double-mean blocks is at most one half. -/
theorem intersection_half_block {α : Type} {n K : Nat} (next : α → Fin n → α)
    (I : α → Prop) (D : Fin K → α → Prop)
    (closed : ∀ x e, I x → I (next x e))
    (keep : ∀ i x e, I x → D i x → D i (next x e))
    (μ : Nat) (hμ : 0<μ)
    (mean : ∀ i x, I x → IIDExpectedHittingTimeAtMost next (D i) x μ)
    (j : Nat) (hlog : 2*K≤2^j) (x : α) (hx : I x) :
    2*survival next (fun y => ¬∀ i, D i y) (j*(2*μ)) x ≤ n^(j*(2*μ)) := by
  let T := j*(2*μ)
  let S := survival next (fun y => ¬∀ i, D i y) T x
  have hu := intersection_survival_le next I D closed keep T x hx
  have hMass : 2^j*S≤K*n^T := by
    refine Nat.le_trans (Nat.mul_le_mul_left _ hu) ?_
    rw [←sScale]
    exact Nat.le_trans
      (sMono (g:=fun _ : Fin K => n^T)
        (fun i => restart_tail next I (D i) closed μ hμ (mean i) j x hx))
      (Nat.le_of_eq (sConst K (n^T)))
  have hp : 0 < (2:Nat)^j := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_left _ hp
  calc
    2^j*(2*S) = 2*(2^j*S) := by ac_rfl
    _ ≤ 2*(K*n^T) := Nat.mul_le_mul_left _ hMass
    _ = (2*K)*n^T := (Nat.mul_assoc ..).symm
    _ ≤ 2^j*n^T := Nat.mul_le_mul_right _ hlog

/-- For K>0 this is the least j with 2K≤2^j, i.e. ceil(log₂(2K)).
For an empty family the joint target holds immediately. -/
def intersectionExponent (K : Nat) : Nat :=
  if K=0 then 0 else (2*K-1).log2+1

theorem intersectionExponent_covers (K : Nat) : 2*K≤2^intersectionExponent K := by
  by_cases h : K=0
  · simp [h]
  · have hh := Nat.lt_log2_self (n:=2*K-1)
    simpa only [intersectionExponent,h,if_false] using
      (show 2*K≤2^((2*K-1).log2+1) by omega)

private theorem iid_zero_alphabet {α : Type} (next : α → Fin 0 → α)
    (D : α → Prop) (t : Nat) (x : α) : iidHitCost next D t x=0 := by
  cases t with
  | zero => rfl
  | succ t =>
    by_cases h : D x
    · exact iidHitCost_of_target next D x h _
    · simp [iidHitCost,h]

/-- All-of-K mean bound with the sharp stated P3 convention
4*mu*ceil(log₂(2K)); budgets and probability checks are Nat. Empty
families and zero means are handled without a spurious restart. -/
theorem intersection_mean {α : Type} {n K : Nat} (next : α → Fin n → α)
    (I : α → Prop) (D : Fin K → α → Prop)
    (closed : ∀ x e, I x → I (next x e))
    (keep : ∀ i x e, I x → D i x → D i (next x e))
    (μ : Nat) (mean : ∀ i x, I x → IIDExpectedHittingTimeAtMost next (D i) x μ)
    (x : α) (hx : I x) :
    IIDExpectedHittingTimeAtMost next (fun y => ∀ i, D i y) x
      (4*μ*intersectionExponent K) := by
  by_cases hK : K=0
  · subst K
    intro t
    rw [iidHitCost_of_target next _ x (fun i => Fin.elim0 i)]
    exact Nat.zero_le _
  by_cases hμ : μ=0
  · subst μ
    by_cases hn : n=0
    · subst n
      intro t
      rw [iid_zero_alphabet]
      exact Nat.zero_le _
    · have all : ∀ i,D i x := by
        intro i
        by_cases h : D i x
        · exact h
        · have hh := mean i x hx 1
          simp [iidHitCost,h] at hh
          omega
      intro t
      rw [iidHitCost_of_target next _ x all]
      exact Nat.zero_le _
  · let j := intersectionExponent K
    have hj : 0<j := by simp [j,intersectionExponent,hK]
    have hb : 0<j*(2*μ) := Nat.mul_pos hj (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hμ))
    have hM := mean_of_half_block next I (fun y => ∀ i,D i y) closed _ hb
      (intersection_half_block next I D closed keep μ (Nat.pos_of_ne_zero hμ) mean
        j (intersectionExponent_covers K)) x hx
    have he : 2*(j*(2*μ))=4*μ*intersectionExponent K := by
      dsimp only [j]
      calc
        _ = (2*2)*μ*intersectionExponent K := by ac_rfl
        _ = _ := rfl
    rwa [he] at hM

end L4.FastRestart

#print axioms L4.FastRestart.restart_tail
#print axioms L4.FastRestart.mean_of_half_block
#print axioms L4.FastRestart.intersection_half_block
#print axioms L4.FastRestart.intersection_mean
