import Leader.L4.FastExp

namespace L4.FastExpEvent
open TaggedTail FastExp Classical

/-- Event certificate, evaluated before a raw mark. Normalize
by scale*n^t. On a successful mark the child value is exactly one. -/
structure EventCert {α : Type} {n : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : α → Fin n → Prop) (rate gain scale : Nat) where
  scalePositive : 0<scale
  ratePositive : 0<rate
  gainPositive : 0<gain
  pot : Nat → α → Nat
  lo : ∀ t x, I x → scale*n^t≤pot t x
  hi : ∀ t x, I x → pot t x≤gain*(scale*n^t)
  drift : ∀ t x, I x →
    rate*sumEdge (fun e => if ev x e then scale*n^t else pot t (next x e))≤
      (rate-1)*pot (t+1) x

noncomputable def flagNext {α : Type} {n : Nat} (next : α → Fin n → α)
    (ev : α → Fin n → Prop) (z : α × Bool) (e : Fin n) : α × Bool :=
  (next z.1 e,if ev z.1 e then true else z.2)

/-- Uniform first-service mean yields an event certificate via the
normalized truncated-cost potential; rate 2μ, gain 2. -/
noncomputable def service_of_mean {α : Type} {n : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : α → Fin n → Prop) (μ : Nat) (hμ : 0<μ)
    (mean : ∀ x, I x → IIDExpectedHittingTimeAtMost (flagNext next ev)
      (fun z => z.2=true) (x,false) μ)
    (keep : ∀ x e, I x → I (next x e)) : EventCert next I ev (2*μ) 2 μ := by
  let good := fun z : α × Bool => I z.1
  let done := fun z : α × Bool => z.2=true
  have h (z : α × Bool) (hz : good z) :
      IIDExpectedHittingTimeAtMost (flagNext next ev) done z μ := by
    rcases z with ⟨x,b⟩
    cases b
    · exact mean x hz
    · intro t
      rw [iidHitCost_of_target _ _ _ (show done (x,true) from rfl)]
      exact Nat.zero_le _
  let cert := fromMean (flagNext next ev) good done μ hμ h
  refine ⟨hμ,Nat.mul_pos (by decide) hμ,by decide,fun t x => cert.pot t (x,false),?_,?_,?_⟩
  · exact fun t x hx => cert.lo t (x,false) hx
  · exact fun t x hx => cert.hi t (x,false) hx
  · intro t x hx
    have hh := cert.drift t (x,false) hx (show ¬false=true by decide)
    change 2*μ*sumEdge (fun e => cert.pot t (flagNext next ev (x,false) e)) ≤ _ at hh
    have eq (e : Fin n) : cert.pot t (flagNext next ev (x,false) e) =
        if ev x e then μ*n^t else cert.pot t (next x e,false) := by
      by_cases he : ev x e
      · rw [if_pos he,show flagNext next ev (x,false) e=(next x e,true) by simp [flagNext,he]]
        exact cert.terminal t _ (keep x e hx) rfl
      · simp [flagNext,he]
    simpa only [eq] using hh

/-- One event per physical mark, selected by the remaining budget. -/
noncomputable def sequenceNext {α : Type} {n : Nat} (next : α → Fin n → α)
    (ev : Nat → α → Fin n → Prop) (z : α × Nat) (e : Fin n) : α × Nat :=
  (next z.1 e,if z.2=0 then 0 else if ev z.2 z.1 e then z.2-1 else z.2)

private theorem sum_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem sum_scale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e)=a*sumEdge f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.mul_add]

theorem sequence_closed {α : Type} {n : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : Nat → α → Fin n → Prop) (H : Nat)
    (keep : ∀ x e, I x → I (next x e)) (z : α × Nat) (e : Fin n)
    (hz : I z.1 ∧ z.2≤H) :
    I (sequenceNext next ev z e).1 ∧ (sequenceNext next ev z e).2≤H := by
  refine ⟨keep _ e hz.1,?_⟩
  unfold sequenceNext
  dsimp only
  split
  · omega
  · split <;> omega

/-- Sequential law. Gain is G^H with no change in rate L. -/
noncomputable def sequence {α : Type} {n : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : Nat → α → Fin n → Prop) (rate G S H : Nat)
    (hr : 0<rate) (hg : 0<G) (hs : 0<S)
    (stage : ∀ k, EventCert next I (ev k) rate G S)
    (keep : ∀ x e, I x → I (next x e)) :
    ExpCert (sequenceNext next ev) (fun z => I z.1 ∧ z.2≤H) (fun z => z.2=0)
      rate (G^H) := by
  let val : Nat → α × Nat → Nat := fun t z =>
    match z.2 with
    | 0 => S*n^t
    | k+1 => G^k*(stage (k+1)).pot t z.1
  refine ⟨S,hs,hr,Nat.pow_pos hg,val,?_,?_,?_,?_⟩
  · intro t z hz
    rcases z with ⟨x,k⟩
    cases k with
    | zero => exact Nat.le_refl _
    | succ k =>
      change S*n^t≤G^k*(stage (k+1)).pot t x
      apply Nat.le_trans ((stage (k+1)).lo t x hz.1)
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right ((stage (k+1)).pot t x) (Nat.pow_pos hg : 1≤G^k)
  · intro t z hz
    rcases z with ⟨x,k⟩
    cases k with
    | zero =>
      change S*n^t≤G^H*(S*n^t)
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (S*n^t) (Nat.pow_pos hg : 1≤G^H)
    | succ k =>
      change G^k*(stage (k+1)).pot t x≤G^H*(S*n^t)
      calc
        _ ≤ G^k*(G*(S*n^t)) := Nat.mul_le_mul_left _ ((stage (k+1)).hi t x hz.1)
        _ = G^(k+1)*(S*n^t) := by rw [Nat.pow_succ,Nat.mul_assoc]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hg hz.2)
  · rintro t ⟨x,k⟩ _ h
    change k=0 at h
    subst k
    rfl
  · rintro t ⟨x,k⟩ hx hk
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      have hEach (e : Fin n) : val t (sequenceNext next ev (x,k+1) e) ≤
          G^k*(if ev (k+1) x e then S*n^t else (stage (k+1)).pot t (next x e)) := by
        by_cases he : ev (k+1) x e
        · rw [if_pos he,show sequenceNext next ev (x,k+1) e=(next x e,k) by simp [sequenceNext,he]]
          cases k with
          | zero => simp [val]
          | succ k =>
            change G^k*(stage (k+1)).pot t (next x e)≤G^(k+1)*(S*n^t)
            rw [Nat.pow_succ,Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ ((stage (k+1)).hi t _ (keep x e hx.1))
        · simp [if_neg he,sequenceNext,val]
      change rate*sumEdge (fun e => val t (sequenceNext next ev (x,k+1) e)) ≤
        (rate-1)*(G^k*(stage (k+1)).pot (t+1) x)
      calc
        _ ≤ rate*sumEdge (fun e => G^k*(if ev (k+1) x e then S*n^t else
            (stage (k+1)).pot t (next x e))) := Nat.mul_le_mul_left _ (sum_mono hEach)
        _ = G^k*(rate*sumEdge (fun e => if ev (k+1) x e then S*n^t else
            (stage (k+1)).pot t (next x e))) := by rw [sum_scale]; ac_rfl
        _ ≤ G^k*((rate-1)*(stage (k+1)).pot (t+1) x) :=
          Nat.mul_le_mul_left _ ((stage (k+1)).drift t x hx.1)
        _ = _ := by ac_rfl

end L4.FastExpEvent
