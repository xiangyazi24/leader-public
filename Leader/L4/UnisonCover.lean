import Leader.L4.FastParallel
import Leader.L4.TripleRenewal

/-! The serial unison cover lemmas have a raw IID interpretation only
after a physical same-mark projection and uniform service estimates
have been supplied. This module derives the cover and iteration costs. -/
namespace L4.UnisonCover
open FastExpEvent FastParallel TripleRenewal Classical

/-- A finite list of serial centre publications covers every centre,
with repetitions and arbitrary order allowed. -/
def Covers {m : Nat} (w : List (Fin m)) : Prop := ∀ i, i∈w

/-- Execute serial publications, one at a time. -/
def runAtomic {β : Type} {m : Nat} (atomic : β → Fin m → β)
    (x : β) : List (Fin m) → β
  | [] => x
  | e::w => runAtomic atomic (atomic x e) w

theorem runAtomic_push {β : Type} {m : Nat} (atomic : β → Fin m → β)
    (x : β) (w : List (Fin m)) (e : Fin m) :
    runAtomic atomic x (w++[e])=atomic (runAtomic atomic x w) e := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => exact ih (atomic x i)

/-- A raw mark can stutter or publish one uniquely named centre.
Identity native updates must still be recorded as publications
whenever they give actual service. -/
structure SerialProjection {α β : Type} {n m : Nat}
    (next : α → Fin n → α) (atomic : β → Fin m → β) (I : α → Prop) where
  project : α → β
  pub : α → Fin n → Option (Fin m)
  closed : ∀ x e, I x → I (next x e)
  row : ∀ x e, I x → project (next x e) =
    match pub x e with | none => project x | some i => atomic (project x) i

private def pushed {m : Nat} (w : List (Fin m)) (e : Option (Fin m)) :
    List (Fin m) := match e with | none => w | some i => w++[i]

private theorem coverClock_step {α β : Type} {n m : Nat}
    {next : α → Fin n → α} {atomic : β → Fin m → β} {I : α → Prop}
    (S : SerialProjection next atomic I)
    (z : α × (Fin m → Nat)) (w : List (Fin m)) (e : Fin n)
    (hcap : ∀ i, z.2 i≤1) (hc : ∀ i, z.2 i=0 ↔ i∈w) :
    ∀ i, (stepAll next (fun i _ x e => S.pub x e=some i) z e).2 i=0 ↔
      i∈pushed w (S.pub z.1 e) := by
  intro i
  have hh := hc i
  have hk := hcap i
  cases hz : S.pub z.1 e with
  | none => by_cases h : z.2 i=0 <;> simp_all [stepAll,sequenceNext,pushed]
  | some j =>
    by_cases hij : i=j
    · subst j
      by_cases h : z.2 i=0
      · simp [stepAll,sequenceNext,pushed,h,hz]
      · have he : z.2 i=1 := by omega
        simp [stepAll,sequenceNext,pushed,he,hz]
    · by_cases h : z.2 i=0 <;> simp_all [stepAll,sequenceNext,pushed,Ne.symm hij]

/-- One complete serial cover costs at most the sharp cover bound for
the joint first-publication target. This is the associated mean bound
for moving between any two native cover stages. -/
theorem phase_mean {α β : Type} {n m : Nat} {next : α → Fin n → α}
    {atomic : β → Fin m → β} {I : α → Prop}
    (S : SerialProjection next atomic I) (A B : β → Prop)
    (round : ∀ y w, A y → Covers w → B (runAtomic atomic y w))
    (μ c : Nat) (hμ : 0<μ) (hn : 0<n) (hg : 2*m≤2^c)
    (service : ∀ i x, I x → IIDExpectedHittingTimeAtMost
      (flagNext next (fun y e => S.pub y e=some i)) (fun z => z.2=true) (x,false) μ)
    (x : α) (hx : I x) (hA : A (S.project x)) :
    IIDExpectedHittingTimeAtMost next (fun y => B (S.project y)) x ((2*μ)*(c+1)) := by
  let ev := fun (i : Fin m) (_ : Nat) y e => S.pub y e=some i
  let start : α × (Fin m → Nat) := (x,fun _ => 1)
  let reached := fun (z : α × (Fin m → Nat)) =>
    Domain I 1 z ∧ ∃ w : List (Fin m), S.project z.1=runAtomic atomic (S.project x) w ∧
      ∀ i,z.2 i=0 ↔ i∈w
  have hR : reached start := by exact ⟨⟨hx,fun _ => Nat.le_refl _⟩,[],rfl,fun _ => by simp [start]⟩
  have keep (z : α × (Fin m → Nat)) (e : Fin n) (hz : reached z) :
      reached (stepAll next ev z e) := by
    obtain ⟨hz, w, hw, hcount⟩ := hz
    refine ⟨domain_closed next I ev 1 S.closed z e hz,pushed w (S.pub z.1 e),?_,?_⟩
    · change S.project (next z.1 e)=_
      rw [S.row z.1 e hz.1]
      cases S.pub z.1 e with
      | none => exact hw
      | some i => rw [pushed,runAtomic_push,hw]
    · exact coverClock_step S z w e hz.2 hcount
  let P : Stage next x :=
    ⟨α × (Fin m → Nat),start,stepAll next ev,Prod.fst,
      fun z => ∀ i,z.2 i=0,reached,rfl,fun _ _ => rfl,hR,keep⟩
  have hmean := all_paths_mean next I ev 1 μ c hμ hn (by simpa [Nat.mul_comm] using hg)
    S.closed (fun i _ y hy => service i y hy) start hR.1
  have h := expected_with_preparation P (fun y => B (S.project y)) _ 0 hmean (by
    intro z hz done fail
    obtain ⟨_,w,hw,hc⟩ := hz
    change ¬B (S.project z.1) at fail
    rw [hw] at fail
    exact False.elim (fail (round _ _ hA (fun i => (hc i).mp (done i)))))
  simpa only [Nat.add_zero] using h

/-- Iterate an arbitrary finite list of cover stages, restarting the
observer at each actual entrance. All times are raw marks; one cover
is not assumed to be one deterministic block. -/
theorem phases_mean {α β : Type} {n m : Nat} {next : α → Fin n → α}
    {atomic : β → Fin m → β} {I : α → Prop}
    (S : SerialProjection next atomic I) (D : Nat → β → Prop) (k : Nat)
    (round : ∀ j, j<k → ∀ y w, D j y → Covers w → D (j+1) (runAtomic atomic y w))
    (μ c : Nat) (hμ : 0<μ) (hn : 0<n) (hg : 2*m≤2^c)
    (service : ∀ i x, I x → IIDExpectedHittingTimeAtMost
      (flagNext next (fun y e => S.pub y e=some i)) (fun z => z.2=true) (x,false) μ)
    (x : α) (hx : I x) (hD : D 0 (S.project x)) :
    IIDExpectedHittingTimeAtMost next (fun y => D k (S.project y)) x
      (k*((2*μ)*(c+1))) := by
  let U := (2*μ)*(c+1)
  have go : ∀ j, j≤k → IIDExpectedHittingTimeAtMost next (fun y => D j (S.project y)) x (j*U) := by
    intro j
    induction j with
    | zero =>
      intro _ t
      rw [iidHitCost_of_target next _ x hD]
      exact Nat.zero_le _
    | succ j ih =>
      intro hj
      let P : Stage next x :=
        ⟨α,x,next,id,fun y => D j (S.project y),I,rfl,fun _ _ => rfl,hx,S.closed⟩
      have h := expected_with_preparation P (fun y => D (j+1) (S.project y)) _ U
        (ih (by omega)) (fun y hy hdy _ =>
          phase_mean S (D j) (D (j+1)) (round j (by omega)) μ c hμ hn hg service y hy hdy)
      simpa only [Nat.succ_mul] using h
  exact go k (Nat.le_refl _)

end L4.UnisonCover

