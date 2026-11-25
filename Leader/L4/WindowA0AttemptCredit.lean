import Leader.L4.WindowA0Restart

/-! Exact adapted first-terminal failure products on the same labeled
raw word. Unfinished stages are not failures and require no deadline. -/
namespace L4.WindowA0AttemptCredit
open TripleRenewal TaggedTail Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f=f 0+sumEdge (fun i : Fin n => f i.succ) := by simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i,f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih fun i => h i.succ)

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e)=a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

/-- A single local attempt sees the same transitions as the eventual
trial. Its failure mass counts only its own first stop. The live
invariant is needed only through that first stop, so an entered
continuation need not leave the old phase monitor valid. -/
structure Layer {α : Type} {n : Nat} (next : α → Fin n → α)
    (done : α → Prop) (entry handoff : α → Prop) (d : Nat) where
  localDone : α → Prop
  localBad : α → Prop
  live : α → Prop
  enter : ∀ x, entry x → live x
  keep : ∀ x e, live x → ¬localDone x → live (next x e)
  notEarly : ∀ x, live x → done x → localDone x
  pass : ∀ x, live x → localDone x → ¬localBad x → handoff x
  budget : ∀ x, entry x → ∀ t,
    d*terminalMass next localDone localBad t x≤(d-1)*n^t

/-- Keep exact continuation credit at a good local stop, and charge
at most the local first-failure numerator for the bad stops. -/
theorem glue_failure {α : Type} {n : Nat} (next : α → Fin n → α)
    (done bad entry handoff : α → Prop) {d : Nat}
    (L : Layer next done entry handoff d) (D : Nat) (hD : 0<D)
    (suffix : ∀ x, handoff x → ∀ t,
      D*terminalMass next done bad t x≤(D-1)*n^t)
    (t : Nat) (x : α) (hx : L.live x) :
    D*terminalMass next done bad t x≤(D-1)*n^t+
      terminalMass next L.localDone L.localBad t x := by
  have atStop (u : Nat) (y : α) (hy : L.live y) (h : L.localDone y) :
      D*terminalMass next done bad u y≤(D-1)*n^u+
        terminalMass next L.localDone L.localBad u y := by
    by_cases hb : L.localBad y
    · have H := Nat.mul_le_mul_left D (terminalMass_le_total next done bad u y)
      have H1 : terminalMass next L.localDone L.localBad u y=n^u := by
        cases u <;> simp [terminalMass,h,hb]
      rw [H1]
      have E : D*n^u=(D-1)*n^u+n^u := by
        calc
          _ = (D-1+1)*n^u := congrArg (fun k => k*n^u) (by omega)
          _ = _ := by rw [Nat.add_mul,Nat.one_mul]
      rwa [←E]
    · exact Nat.le_trans (suffix y (L.pass y hy h hb) u) (Nat.le_add_right ..)
  induction t generalizing x with
  | zero =>
    by_cases h : L.localDone x
    · exact atStop 0 x hx h
    · have hd : ¬done x := fun hd => h (L.notEarly x hx hd)
      simp [terminalMass,hd]
  | succ t ih =>
    by_cases h : L.localDone x
    · exact atStop (t+1) x hx h
    · have hd : ¬done x := fun hd => h (L.notEarly x hx hd)
      have H := sMono (fun e => ih (next x e) (L.keep x e hx h))
      rw [sScale,sAdd,sConst] at H
      simp only [terminalMass,h,hd,if_false,Nat.pow_succ']
      simpa only [Nat.mul_left_comm n (D-1)] using H

theorem product_failure {α : Type} {n : Nat} (next : α → Fin n → α)
    (done bad entry handoff : α → Prop) {d : Nat}
    (L : Layer next done entry handoff d) (D : Nat) (hd : 0<d) (hD : 0<D)
    (suffix : ∀ x, handoff x → ∀ t,
      D*terminalMass next done bad t x≤(D-1)*n^t)
    (t : Nat) (x : α) (hx : entry x) :
    (d*D)*terminalMass next done bad t x≤(d*D-1)*n^t := by
  have H := Nat.mul_le_mul_left d (glue_failure next done bad entry handoff L D hD suffix
     t x (L.enter x hx))
  rw [←Nat.mul_assoc,Nat.mul_add,←Nat.mul_assoc] at H
  have E : d*(D-1)+(d-1)=d*D-1 := by
    have e : d*(D-1)+d=d*D := by
      calc
        _ = d*(D-1+1) := by rw [Nat.mul_add,Nat.mul_one]
        _ = _ := by rw [show D-1+1=D by omega]
    omega
  calc
    _ ≤ d*(D-1)*n^t+d*terminalMass next L.localDone L.localBad t x := H
    _ ≤ d*(D-1)*n^t+(d-1)*n^t := Nat.add_le_add_left (L.budget x hx t) _
    _ = _ := by rw [←Nat.add_mul,E]

/-- An early physical exit can be carried through remaining layers as
an immediately favorable final terminal. -/
def Final {α : Type} (done bad : α → Prop) (x : α) := done x ∧ ¬bad x

/-- Sequence of adaptive cuts on the same raw map. -/
inductive Chain {α : Type} {n : Nat} (next : α → Fin n → α)
    (done bad : α → Prop) : (α → Prop) → List Nat → Type where
  | done {entry : α → Prop} (finish : ∀ x, entry x → Final done bad x) :
      Chain next done bad entry []
  | next {entry handoff : α → Prop} {d : Nat} {ds : List Nat}
      (hd : 0<d) (L : Layer next done entry handoff d)
      (tail : Chain next done bad handoff ds) :
      Chain next done bad entry (d::ds)

/-- Multiply continuation probabilities, without independence. -/
theorem chain_failure {α : Type} {n : Nat} {next : α → Fin n → α}
    {done bad entry : α → Prop} {ds : List Nat}
    (C : Chain next done bad entry ds) :
    0<ds.prod ∧ ∀ x, entry x → ∀ t,
      ds.prod*terminalMass next done bad t x≤(ds.prod-1)*n^t := by
  induction C with
  | done finish =>
    refine ⟨by decide,?_⟩
    intro x hx t
    have h := finish x hx
    cases t <;> simp [terminalMass,h.1,h.2]
  | next hd L _ ih =>
    refine ⟨Nat.mul_pos hd ih.1,?_⟩
    intro x hx t
    exact product_failure next done bad _ _ L _ hd ih.1 ih.2 t x hx

/-- k guarded legs on the full ledger: release denominator 216,
then return denominator 3 up to the next actual acceptance. -/
structure GuardedLegs {α : Type} {n : Nat} (next : α → Fin n → α)
    (done bad : α → Prop) (k : Nat) (start : Nat → α → Prop) where
  released : Nat → α → Prop
  release : ∀ j, j<k → Layer next done (start j) (released j) 216
  ret : ∀ j, j<k → Layer next done (released j) (start (j+1)) 3
  final : ∀ x, start k x → Final done bad x

/-- Compose 216*3=648 at each leg. The argument charges no unfinished
leaf as failure and tests each bounded horizon separately. -/
theorem guarded_failure {α : Type} {n : Nat} {next : α → Fin n → α}
    {done bad : α → Prop} {k : Nat} {start : Nat → α → Prop}
    (L : GuardedLegs next done bad k start) (j : Nat) (hj : j≤k)
    (x : α) (hx : start j x) (t : Nat) :
    648^(k-j)*terminalMass next done bad t x≤(648^(k-j)-1)*n^t := by
  have H : ∀ q j, j+q=k → ∀ x, start j x → ∀ t,
      648^q*terminalMass next done bad t x≤(648^q-1)*n^t := by
    intro q
    induction q with
    | zero =>
      intro j he x hx t
      have hj' : j=k := by omega
      subst j
      have h := L.final x hx
      cases t <;> simp [terminalMass,h.1,h.2]
    | succ q ih =>
      intro j he x hx t
      have hj' : j<k := by omega
      have hQ : 0<(648:Nat)^q := Nat.pow_pos (by decide)
      have hR : ∀ y, L.released j y → ∀ u,
          (3*648^q)*terminalMass next done bad u y≤(3*648^q-1)*n^u := by
        intro y hy u
        exact product_failure next done bad _ _ (L.ret j hj') _ (by decide) hQ
          (ih (j+1) (by omega)) u y hy
      have h := product_failure next done bad _ _ (L.release j hj')
        (3*648^q) (by decide) (Nat.mul_pos (by decide) hQ) hR t x hx
      rwa [←Nat.mul_assoc,show 216*3=648 by decide,←Nat.pow_succ'] at h
  exact H (k-j) j (by omega) x hx t

/-- A0's exact denominator for Q+1 count legs. A failure-free cleanup
stage can be prepended with denominator one via product_failure. -/
theorem a0_guarded_failure {α : Type} {n : Nat} {next : α → Fin n → α}
    {done bad : α → Prop} {start : Nat → α → Prop} (c : Nat)
    (L : GuardedLegs next done bad (2*c+1) start)
    (x : α) (hx : start 0 x) (t : Nat) :
    WindowA0Restart.attempts c*terminalMass next done bad t x≤
      (WindowA0Restart.attempts c-1)*n^t := by
  simpa only [Nat.sub_zero,WindowA0Restart.attempts] using
    guarded_failure L 0 (Nat.zero_le _) x hx t

/-- Attach the failure product to a literal stage projection. No
premise freezes the physical process after an auxiliary decision:
stage.projStep already requires every padded raw mark to project. -/
def assemble_attempt {α : Type} {n : Nat} {step : α → Fin n → α} {x : α}
    (goal admissible : α → Prop) (c H : Nat) (stage : Stage step x)
    (proper : ¬stage.ready stage.start)
    (restart : ∀ y, stage.reachable y → stage.ready y → ¬goal (stage.project y) →
      admissible (stage.project y))
    (mean : IIDExpectedHittingTimeAtMost stage.next stage.ready stage.start
      (WindowA0Restart.attemptCost c n H))
    (entry : stage.State → Prop) {start : Nat → stage.State → Prop}
    (cleanup : Layer stage.next stage.ready entry (start 0) 1)
    (legs : GuardedLegs stage.next stage.ready (fun y => ¬goal (stage.project y))
      (2*c+1) start)
    (hx : entry stage.start) :
    UniformAttempt step goal admissible (WindowA0Restart.attemptCost c n H)
      (WindowA0Restart.attempts c) x where
  stage := stage
  properStart := proper
  restart := restart
  mean := mean
  failBound := fun t => by
    have bound := product_failure stage.next stage.ready (fun y => ¬goal (stage.project y))
      entry (start 0) cleanup (WindowA0Restart.attempts c)
      (by decide) (Nat.pow_pos (by decide))
      (fun y hy u => a0_guarded_failure c legs y hy u) t stage.start hx
    simpa only [Nat.one_mul] using bound

end L4.WindowA0AttemptCredit

