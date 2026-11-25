import Leader.L4.TripleRenewal

/-! The qualitative G9 composition on one fixed finite joined raw-mark
system. No quotient, lifting, access, or asymptotic FAST claim is
inferred for any specific stratum. -/
namespace L4.AllSizeComposition
open TaggedTail RankRenewal Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f=f 0+sumEdge (fun i : Fin n => f i.succ) := by simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih fun i => h i.succ)

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun i => f i+g i)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e)=a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem eMono {α : Type} {n : Nat} (next : α → Fin n → α)
    {f g : α → Nat} (h : ∀ x, f x≤g x) (t : Nat) (x : α) :
    endpointSum next f t x≤endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h x
  | succ t ih => exact sMono (fun _ => ih _)

private theorem eAdd {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => f y+g y) t x=endpointSum next f t x+endpointSum next g t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sAdd]

private theorem eScale {α : Type} {n : Nat} (next : α → Fin n → α)
    (a : Nat) (f : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => a*f y) t x=a*endpointSum next f t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sScale]

private theorem eConst {α : Type} {n : Nat} (next : α → Fin n → α)
    (a t : Nat) (x : α) : endpointSum next (fun _ => a) t x=a*n^t := by
  induction t generalizing x with
  | zero => simp [endpointSum]
  | succ t ih => simp only [endpointSum,ih,sConst,Nat.pow_succ]; ac_rfl

/-- Closure under each actual mark, including marks after target entry. -/
def Closed {α : Type} {n : Nat} (next : α → Fin n → α) (D : α → Prop) : Prop :=
  ∀ x e, D x → D (next x e)

/-- Run the actual joined raw-mark map, in the prescribed order. -/
def runWord {α : Type} {n : Nat} (next : α → Fin n → α)
    (x : α) : List (Fin n) → α
  | [] => x
  | e::w => runWord next (next x e) w

theorem closed_run {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : α → Prop) (hD : Closed next D) (x : α) (w : List (Fin n)) (hx : D x) :
    D (runWord next x w) := by
  induction w generalizing x with
  | nil => exact hx
  | cons e w ih => exact ih _ (hD _ _ hx)

noncomputable def indicator {α : Type} (D : α → Prop) (x : α) : Nat :=
  if D x then 1 else 0

private theorem term_le_sum {n : Nat} (f : Fin n → Nat) (i : Fin n) : f i≤sumEdge f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [sSucc]
    refine Fin.cases (Nat.le_add_right _ _) (fun j => ?_) i
    exact Nat.le_trans (ih (fun i => f i.succ) j) (Nat.le_add_left _ _)

private theorem endpoint_exact_word {α : Type} {n : Nat}
    (next : α → Fin n → α) (D : α → Prop)
    (x : α) (w : List (Fin n)) (hx : D (runWord next x w)) :
    1≤endpointSum next (indicator D) w.length x := by
  induction w generalizing x with
  | nil => simp_all [runWord,endpointSum,indicator]
  | cons e w ih =>
    change 1≤sumEdge (fun i => endpointSum next (indicator D) w.length (next x i))
    exact Nat.le_trans (ih _ hx) (term_le_sum (fun i => endpointSum next (indicator D) w.length (next x i)) e)

/-- A witness of length at most d gives at least one successful
length-d word. Dividing by n^d yields the paper's raw-block probability. -/
theorem block_success_of_word {α : Type} {n : Nat} (hn : 0<n)
    (next : α → Fin n → α) (D : α → Prop) (hD : Closed next D)
    (x : α) (w : List (Fin n)) (d : Nat) (hw : w.length≤d)
    (hx : D (runWord next x w)) :
    1≤endpointSum next (indicator D) d x := by
  have happ (z : α) (a b : List (Fin n)) :
      runWord next z (a++b)=runWord next (runWord next z a) b := by
    induction a generalizing z with
    | nil => rfl
    | cons e a ih => exact ih _
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hw
  have hab : (w++List.replicate k (⟨0,hn⟩ : Fin n)).length=d := by
    simp [hk]
  rw [←hab]
  apply endpoint_exact_word
  rw [happ]
  exact closed_run next D hD _ _ hx

private theorem eMono_closed {α : Type} {n : Nat} (next : α → Fin n → α)
    (A : α → Prop) (hA : Closed next A)
    {f g : α → Nat} (h : ∀ x, A x → f x≤g x)
    (t : Nat) (x : α) (hx : A x) : endpointSum next f t x≤endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h x hx
  | succ t ih => exact sMono (fun e => ih _ (hA _ e hx))

private theorem split_cost {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : α → Prop) (b t : Nat) (x : α) :
    iidHitCost next D (b+t) x ≤ b*n^(b+t)+endpointSum next (iidHitCost next D t) b x := by
  induction b generalizing x with
  | zero => simp [endpointSum]
  | succ b ih =>
    rw [show b+1+t=b+t+1 by omega]
    by_cases hx : D x
    · simp [iidHitCost,hx]
    · rw [iidHitCost,if_neg hx]
      apply Nat.le_trans (Nat.add_le_add_left (sMono fun e => ih (next x e)) _) ?_
      simp only [sAdd,sConst,endpointSum]
      rw [Nat.add_mul,Nat.one_mul]
      have hh : n*(b*n^(b+t))=b*n^(b+t+1) := by rw [Nat.pow_succ]; ac_rfl
      rw [hh]
      omega

/-- A uniform witness length on a closed lower domain gives the
qualitative expected mark budget d*n^d, including the case d=0. -/
theorem expected_of_uniform_words {α : Type} {n : Nat} (hn : 0<n)
    (next : α → Fin n → α) (A D : α → Prop)
    (hA : Closed next A) (hD : Closed next D) (d : Nat)
    (access : ∀ x, A x → ∃ w, w.length≤d ∧ D (runWord next x w))
    (x : α) (hx : A x) : IIDExpectedHittingTimeAtMost next D x (d*n^d) := by
  let B := d*n^d
  intro t
  change iidHitCost next D t x ≤ B*n^t
  revert x
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro x hx
    by_cases hd : d=0
    · obtain ⟨w,hw,hW⟩ := access x hx
      have he : w=[] := List.length_eq_zero_iff.mp (by omega)
      rw [he] at hW
      exact Nat.le_trans (Nat.le_of_eq (iidHitCost_of_target next D x hW t)) (Nat.zero_le _)
    · by_cases ht : t<d
      · apply Nat.le_trans (iidHitCost_le_horizon next D t x)
        have hh : d≤B := by
          simpa [B] using Nat.mul_le_mul_left d (show 1≤n^d by exact Nat.pow_pos hn)
        exact Nat.mul_le_mul_right _ (Nat.le_trans (Nat.le_of_lt ht) hh)
      · have hdt : d≤t := by omega
        obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hdt
        have hu : u<d+u := by omega
        obtain ⟨w,hw,hW⟩ := access x hx
        have hHit := block_success_of_word hn next D hD x w d hw hW
        have hMass : endpointSum next (indicator D) d x +
            endpointSum next (indicator (fun y => ¬D y)) d x=n^d := by
          rw [←eAdd]
          have hh : (fun y => indicator D y+indicator (fun y => ¬D y) y)=(fun _ => 1) := by
            funext y
            by_cases h : D y <;> simp [indicator,h]
          rw [hh,eConst,Nat.one_mul]
        let M := endpointSum next (indicator (fun y => ¬D y)) d x
        have hM : M+1≤n^d := by dsimp only [M]; omega
        have he := eMono_closed next A hA
          (f := iidHitCost next D u)
          (g := fun y => (B*n^u)*indicator (fun z => ¬D z) y) ?_ d x hx
        · rw [eScale] at he
          change endpointSum next (iidHitCost next D u) d x ≤ (B*n^u)*M at he
          apply Nat.le_trans (split_cost next D d u x)
          have hC : (B*n^u)*(M+1)≤(B*n^u)*n^d := Nat.mul_le_mul_left _ hM
          calc
            _ ≤ d*n^(d+u)+(B*n^u)*M := Nat.add_le_add_left he _
            _ = (B*n^u)*(M+1) := by
              rw [Nat.pow_add,Nat.mul_add,Nat.mul_one]
              unfold B
              rw [← Nat.mul_assoc d (n^d) (n^u)]
              ac_rfl
            _ ≤ (B*n^u)*n^d := hC
            _ = _ := by rw [Nat.pow_add]; ac_rfl
        · intro y hy
          by_cases hDy : D y
          · simp [iidHitCost_of_target next D y hDy u]
          · simpa [indicator,hDy] using ih u hu y hy

/-- Finiteness may be supplied by any exhaustive list, without assuming
decidable equality on the full joined state or its targets. -/
theorem uniform_words_of_finite_cover {α : Type} {n : Nat} (next : α → Fin n → α)
    (A D : α → Prop) (states : List α) (cover : ∀ x, A x → x∈states)
    (access : ∀ x, A x → ∃ w, D (runWord next x w)) :
    ∃ d : Nat, ∀ x, A x → ∃ w, w.length≤d ∧ D (runWord next x w) := by
  have finite : ∀ l : List α, ∃ d : Nat, ∀ x, x∈l → A x →
      ∃ w, w.length≤d ∧ D (runWord next x w) := by
    intro l
    induction l with
    | nil => exact ⟨0, fun _ h => False.elim (List.not_mem_nil h)⟩
    | cons a l ih =>
      obtain ⟨d,hd⟩ := ih
      by_cases ha : A a
      · obtain ⟨w,hw⟩ := access a ha
        refine ⟨max d w.length, ?_⟩
        intro x hm hx
        rcases List.mem_cons.mp hm with rfl|hm
        · exact ⟨w,Nat.le_max_right _ _,hw⟩
        · obtain ⟨v,hv,hD⟩ := hd x hm hx
          exact ⟨v,Nat.le_trans hv (Nat.le_max_left _ _),hD⟩
      · refine ⟨d,?_⟩
        intro x hm hx
        rcases List.mem_cons.mp hm with rfl|hm
        · exact False.elim (ha hx)
        · exact hd x hm hx
  obtain ⟨d,hd⟩ := finite states
  exact ⟨d,fun x hx => hd x (cover x hx) hx⟩

/-- Add the conditional mean of the next stage to the preceding mean.
The continuation is charged at the first lower-target hit, not at a
deterministic time or under an independence assumption on the cut. -/
theorem additive_stage {α : Type} {n : Nat} (next : α → Fin n → α)
    (A D : α → Prop) (a b : Nat) (x : α)
    (prep : IIDExpectedHittingTimeAtMost next A x a)
    (after : ∀ y, A y → IIDExpectedHittingTimeAtMost next D y b) :
    IIDExpectedHittingTimeAtMost next D x (a+b) := by
  intro t
  have h := TripleRenewal.glue_until_stop next next id (fun _ _ => rfl)
    D A (fun _ => True) (fun _ _ _ => trivial) b t
    (fun y u _ hA _ _ => after y hA u) t (Nat.le_refl _) x trivial
  have h' := TripleRenewal.terminalMass_le_total next A (fun y => ¬ D y) t x
  change iidHitCost next D t x ≤ (a+b)*n^t
  rw [Nat.add_mul]
  exact Nat.le_trans h (Nat.add_le_add (prep t) (Nat.mul_le_mul_left _ h'))

/-- Closed-target and mean-witness ledger. A stage may supply a FAST
budget directly, independently of the qualitative finite-cover proof. -/
structure MeanChain {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : Nat → α → Prop) (cost : Nat → Nat) (h : Nat) : Prop where
  initial : ∀ x, D 0 x
  nested : ∀ j, j<h → ∀ x, D (j+1) x → D j x
  closed : ∀ j, j≤h → Closed next (D j)
  mean : ∀ j, j<h → ∀ x, D j x →
    IIDExpectedHittingTimeAtMost next (D (j+1)) x (cost j)

/-- Sum the first h conditional stage budgets without a uniformity
claim in the system size. The final target is closed separately. -/
theorem compose_means {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : Nat → α → Prop) (cost : Nat → Nat) (h : Nat)
    (chain : MeanChain next D cost h) (x : α) :
    Closed next (D h) ∧
      IIDExpectedHittingTimeAtMost next (D h) x
        (((List.range h).map cost).sum) := by
  refine ⟨chain.closed h (Nat.le_refl _),?_⟩
  have aux : ∀ j, j≤h → IIDExpectedHittingTimeAtMost next (D j) x
      (((List.range j).map cost).sum) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact fun t => Nat.le_trans (Nat.le_of_eq (iidHitCost_of_target next (D 0) x (chain.initial x) t)) (Nat.zero_le _)
    | succ j ih =>
      intro hj
      rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      exact additive_stage next (D j) (D (j+1)) _ _ x
        (ih (by omega)) (chain.mean j (by omega))
  exact aux _ (Nat.le_refl _)

/-- Paper G9 hypotheses on the actual joined pair map. The predicate
should carry any lower interface description that needs to survive. -/
structure WordChain {α : Type} {n : Nat} (next : α → Fin n → α)
    (D : Nat → α → Prop) (h : Nat) : Prop where
  initial : ∀ x, D 0 x
  nested : ∀ j, j<h → ∀ x, D (j+1) x → D j x
  closed : ∀ j, j≤h → Closed next (D j)
  access : ∀ j, j<h → ∀ x, D j x → ∃ w, D (j+1) (runWord next x w)

/-- Uniform success numerators from each lower-target state, additive
expected entrance in raw marks, and post-hit closure. A list of actual
states is used only to bound witness lengths. No numerical or
polynomial estimate on d is asserted. -/
theorem compose_finite_words {α : Type} {n : Nat} (hn : 0<n)
    (next : α → Fin n → α) (D : Nat → α → Prop) (h : Nat)
    (states : List α) (cover : ∀ x, x∈states)
    (chain : WordChain next D h) :
    ∃ d : Nat → Nat,
      (∀ j, j<h → ∀ x, D j x → 1≤endpointSum next (indicator (D (j+1))) (d j) x) ∧
      Closed next (D h) ∧
      (∀ x, IIDExpectedHittingTimeAtMost next (D h) x
        (((List.range h).map (fun j => d j*n^(d j))).sum)) := by
  have stepWords : ∀ j, j<h → ∃ d : Nat, ∀ x, D j x →
      ∃ w, w.length≤d ∧ D (j+1) (runWord next x w) := by
    intro j hj
    exact uniform_words_of_finite_cover next (D j) (D (j+1)) states
      (fun x _ => cover x) (chain.access j hj)
  let d : Nat → Nat := fun j => if hj : j<h then choose (stepWords j hj) else 0
  have dSpec (j : Nat) (hj : j<h) (x : α) (hx : D j x) :
      ∃ w, w.length≤d j ∧ D (j+1) (runWord next x w) := by
    simpa only [d,dif_pos hj] using choose_spec (stepWords j hj) x hx
  have hm : MeanChain next D (fun j => d j*n^(d j)) h :=
    ⟨chain.initial,chain.nested,chain.closed,fun j hj x hx =>
      expected_of_uniform_words hn next (D j) (D (j+1))
        (chain.closed j (by omega)) (chain.closed (j+1) (by omega))
        (d j) (dSpec j hj) x hx⟩
  refine ⟨d,?_,chain.closed h (Nat.le_refl _),fun x => (compose_means next D _ h hm x).2⟩
  intro j hj x hx
  obtain ⟨w,hw,hW⟩ := dSpec j hj x hx
  exact block_success_of_word hn next _ (chain.closed (j+1) (by omega)) x w _ hw hW

end L4.AllSizeComposition

#print axioms L4.AllSizeComposition.block_success_of_word
#print axioms L4.AllSizeComposition.expected_of_uniform_words
#print axioms L4.AllSizeComposition.compose_means
#print axioms L4.AllSizeComposition.compose_finite_words
