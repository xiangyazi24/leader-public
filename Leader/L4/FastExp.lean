import Leader.L4.RankRenewal
import Leader.L4.FastRestart

namespace L4.FastExp
open TaggedTail RankRenewal Classical

private theorem smono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem smul {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun i => a*f i)=a*sumEdge f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.mul_add]

private theorem sadd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun i => f i+g i)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih]
    omega

private theorem sconst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.succ_mul,Nat.add_comm]

/-- A terminal-one exponential certificate. At remaining horizon t, the
normalizing denominator is scale*n^t. Scaling by this denominator makes
the finite-horizon mean potential integral without changing its gain.
Drift is required on live states only; target states have value one. -/
structure ExpCert {α : Type} {n : Nat} (next : α → Fin n → α)
    (I D : α → Prop) (rate gain : Nat) where
  scale : Nat
  positive : 0<scale
  ratePositive : 0<rate
  gainPositive : 0<gain
  pot : Nat → α → Nat
  lo : ∀ t x, I x → scale*n^t≤pot t x
  hi : ∀ t x, I x → pot t x≤gain*(scale*n^t)
  terminal : ∀ t x, I x → D x → pot t x=scale*n^t
  drift : ∀ t x, I x → ¬D x →
    rate*sumEdge (fun e => pot t (next x e))≤(rate-1)*pot (t+1) x

/-- Nat-only terminal-one potential 1 + truncated mean / μ.
No infinite expectation or independence of restarted histories. -/
noncomputable def fromMean {α : Type} {n : Nat} (next : α → Fin n → α)
    (I D : α → Prop) (μ : Nat) (hμ : 0<μ)
    (mean : ∀ x, I x → IIDExpectedHittingTimeAtMost next D x μ) :
    ExpCert next I D (2*μ) 2 where
  scale := μ
  positive := hμ
  ratePositive := Nat.mul_pos (by decide) hμ
  gainPositive := by decide
  pot := fun t x => μ*n^t+iidHitCost next D t x
  lo := fun _ _ _ => Nat.le_add_right _ _
  hi := fun t x hx => by have h := mean x hx t; omega
  terminal := fun t x _ hx => by rw [iidHitCost_of_target _ _ _ hx,Nat.add_zero]
  drift := by
    intro t x hx hd
    let W := n^(t+1)
    let S := sumEdge (fun e => iidHitCost next D t (next x e))
    have hM := mean x hx (t+1)
    rw [iidHitCost,if_neg hd] at hM
    change W+S≤μ*W at hM
    rw [sadd,sconst,show n*(μ*n^t)=μ*n^(t+1) by rw [Nat.pow_succ]; ac_rfl]
    rw [iidHitCost,if_neg hd]
    change (2*μ)*(μ*W+S)≤(2*μ-1)*(μ*W+(W+S))
    have hA : 1+(2*μ-1)=2*μ := by omega
    have hA' : (2*μ)*(μ*W+S)=(μ*W+S)+(2*μ-1)*(μ*W+S) := by
      calc
        _ = (1+(2*μ-1))*(μ*W+S) := congrArg (fun a => a*(μ*W+S)) hA.symm
        _ = _ := by rw [Nat.add_mul,Nat.one_mul]
    rw [hA']
    have hD : (2*μ-1)*(μ*W+(W+S)) =
        (2*μ-1)*(μ*W+S)+(2*μ-1)*W := by
      rw [show μ*W+(W+S)=(μ*W+S)+W by omega]
      exact Nat.mul_add .. 
    rw [hD]
    have hB : (2*μ-1)*W + W = (2*μ)*W := by
      calc
        _ = (1+(2*μ-1))*W := by rw [Nat.add_mul,Nat.one_mul]; omega
        _ = _ := congrArg (fun a => a*W) hA
    have hC : (2*μ)*W=2*(μ*W) := Nat.mul_assoc .. 
    omega

/-- Every raw word still alive contributes at least one. The canceled
form below retains only the exact finite-word probability denominator. -/
theorem tail {α : Type} {n : Nat} {next : α → Fin n → α} {I D : α → Prop}
    {rate gain : Nat} (C : ExpCert next I D rate gain) (hn : 0<n)
    (keep : ∀ x e, I x → I (next x e)) (t : Nat) (x : α) (hx : I x) :
    rate^t*survival next (fun y => ¬D y) t x≤gain*(n*(rate-1))^t := by
  have core : ∀ t x, I x →
      (rate^t*(C.scale*n^t))*survival next (fun y => ¬D y) t x≤
      (n*(rate-1))^t*C.pot t x := by
    intro t
    induction t with
    | zero =>
      intro x h
      by_cases hd : D x
      · simp [survival,weightedSurvival,hd]
      · simpa [survival,weightedSurvival,hd] using C.lo 0 x h
    | succ t ih =>
      intro x h
      by_cases hd : D x
      · simp [survival,weightedSurvival,hd]
      simp only [survival,weightedSurvival,hd,not_false_eq_true,if_true]
      calc
        _ = (rate*n)*sumEdge (fun e =>
          (rate^t*(C.scale*n^t))*survival next (fun y => ¬D y) t (next x e)) := by
          rw [smul,Nat.pow_succ rate,Nat.pow_succ n]; ac_rfl
        _ ≤ (rate*n)*sumEdge (fun e => (n*(rate-1))^t*C.pot t (next x e)) :=
          Nat.mul_le_mul_left _ (smono (fun e => ih (next x e) (keep x e h)))
        _ = (n*(n*(rate-1))^t)*(rate*sumEdge (fun e => C.pot t (next x e))) := by rw [smul]; ac_rfl
        _ ≤ (n*(n*(rate-1))^t)*((rate-1)*C.pot (t+1) x) :=
          Nat.mul_le_mul_left _ (C.drift t x h hd)
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have H := Nat.le_trans (core t x hx) (Nat.mul_le_mul_left _ (C.hi t x hx))
  have hpos : 0<C.scale*n^t := Nat.mul_pos C.positive (Nat.pow_pos hn)
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc
    (C.scale*n^t)*(rate^t*survival next (fun y => ¬D y) t x) =
        (rate^t*(C.scale*n^t))*survival next (fun y => ¬D y) t x := by ac_rfl
    _ ≤ (n*(rate-1))^t*(gain*(C.scale*n^t)) := H
    _ = _ := by ac_rfl

/-- At the first stage handoff the old certificate is worth exactly
one. The new start is worth at most its gain; this is exactly the
reserve carried by every old live state. Both stages use the same
actual raw words, including the mark on which the handoff occurs. -/
noncomputable def sequential {α : Type} {n : Nat} {next : α → Fin n → α}
    {I D E : α → Prop} {rate G H : Nat}
    (A : ExpCert next I D rate G)
    (B : ExpCert next (fun x => I x ∧ D x) E rate H)
    (keep : ∀ x e, I x → I (next x e))
    (sticky : ∀ x e, I x → D x → D (next x e))
    (nested : ∀ x, I x → E x → D x) : ExpCert next I E rate (G*H) := by
  let pot := fun (t : Nat) (x : α) =>
    if D x then A.scale*B.pot t x else (H*B.scale)*A.pot t x
  refine ⟨A.scale*B.scale,Nat.mul_pos A.positive B.positive,
    A.ratePositive,Nat.mul_pos A.gainPositive B.gainPositive,pot,?_,?_,?_,?_⟩
  · intro t x hx
    by_cases h : D x
    · simp only [pot,if_pos h]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left A.scale (B.lo t x ⟨hx,h⟩)
    · simp only [pot,if_neg h]
      calc
        _ = B.scale*(A.scale*n^t) := by ac_rfl
        _ ≤ B.scale*A.pot t x := Nat.mul_le_mul_left _ (A.lo t x hx)
        _ = 1*(B.scale*A.pot t x) := (Nat.one_mul _).symm
        _ ≤ H*(B.scale*A.pot t x) := Nat.mul_le_mul_right _ B.gainPositive
        _ = _ := by ac_rfl
  · intro t x hx
    by_cases h : D x
    · simp only [pot,if_pos h]
      calc
        _ ≤ A.scale*(H*(B.scale*n^t)) := Nat.mul_le_mul_left _ (B.hi t x ⟨hx,h⟩)
        _ = 1*(H*(A.scale*B.scale*n^t)) := by rw [Nat.one_mul]; ac_rfl
        _ ≤ G*(H*(A.scale*B.scale*n^t)) := Nat.mul_le_mul_right _ A.gainPositive
        _ = _ := by ac_rfl
    · simp only [pot,if_neg h]
      calc
        _ ≤ (H*B.scale)*(G*(A.scale*n^t)) := Nat.mul_le_mul_left _ (A.hi t x hx)
        _ = _ := by ac_rfl
  · intro t x hx he
    have h := nested x hx he
    simp only [pot,if_pos h,B.terminal t x ⟨hx,h⟩ he]
    ac_rfl
  · intro t x hx he
    by_cases hd : D x
    · have hp : (fun e => pot t (next x e)) = (fun e => A.scale*B.pot t (next x e)) :=
        funext fun e => if_pos (sticky x e hx hd)
      rw [hp,smul,show pot (t+1) x=A.scale*B.pot (t+1) x from if_pos hd]
      calc
        _ = A.scale*(rate*sumEdge (fun e => B.pot t (next x e))) := by ac_rfl
        _ ≤ A.scale*((rate-1)*B.pot (t+1) x) := Nat.mul_le_mul_left _ (B.drift t x ⟨hx,hd⟩ he)
        _ = _ := by ac_rfl
    · have hp : ∀ e, pot t (next x e) ≤ (H*B.scale)*A.pot t (next x e) := by
        intro e
        have hj := keep x e hx
        by_cases h : D (next x e)
        · simp only [pot,if_pos h,A.terminal t _ hj h]
          calc
            _ ≤ A.scale*(H*(B.scale*n^t)) := Nat.mul_le_mul_left _ (B.hi t _ ⟨hj,h⟩)
            _ = _ := by ac_rfl
        · exact Nat.le_of_eq (if_neg h)
      calc
        _ ≤ rate*sumEdge (fun e => (H*B.scale)*A.pot t (next x e)) :=
          Nat.mul_le_mul_left _ (smono hp)
        _ = (H*B.scale)*(rate*sumEdge (fun e => A.pot t (next x e))) := by rw [smul]; ac_rfl
        _ ≤ (H*B.scale)*((rate-1)*A.pot (t+1) x) :=
          Nat.mul_le_mul_left _ (A.drift t x hx hd)
        _ = _ := by rw [show pot (t+1) x=(H*B.scale)*A.pot (t+1) x from if_neg hd]; ac_rfl

/-- A finite union of failures (closed or sticky individual targets).
The gain is the sum of individual gains; the rate and raw labels do not
change. No independence is used. -/
theorem union_tail {α : Type} {n K : Nat} {next : α → Fin n → α}
    {I : α → Prop} {D : Fin K → α → Prop} {rate : Nat} (gain : Fin K → Nat)
    (C : ∀ i, ExpCert next I (D i) rate (gain i)) (hn : 0<n)
    (keep : ∀ x e, I x → I (next x e))
    (sticky : ∀ i x e, D i x → D i (next x e)) (t : Nat) (x : α) (hx : I x) :
    rate^t*survival next (fun y => ∃ i, ¬D i y) t x≤
      sumEdge gain*(n*(rate-1))^t := by
  have hU := survival_union next (fun i y => ¬D i y)
    (fun i y e h hd => h (sticky i y e hd)) t x
  calc
    _ ≤ rate^t*sumEdge (fun i => survival next (fun y => ¬D i y) t x) :=
      Nat.mul_le_mul_left _ hU
    _ = sumEdge (fun i => rate^t*survival next (fun y => ¬D i y) t x) := (smul _ _).symm
    _ ≤ sumEdge (fun i => gain i*(n*(rate-1))^t) := smono (fun i => tail (C i) hn keep t x hx)
    _ = _ := by
      simp only [Nat.mul_comm (gain _) ((n*(rate-1))^t),smul]
      exact Nat.mul_comm .. 

theorem rate_pow_half (r : Nat) (hr : 0<r) :
    2*(r-1)^r ≤ r^r := by
  have hr' : r-1+1=r := by omega
  have hb (t : Nat) : (r-1)*(r+t+1)≤r*(r+t) := by
    have a : (r-1)*(r+t+1)=(r-1)*(r+t)+(r-1) := by rw [Nat.mul_add,Nat.mul_one]
    have b : r*(r+t)=(r-1)*(r+t)+(r+t) := by
      calc
        _ = (r-1+1)*(r+t) := congrArg (fun z => z*(r+t)) hr'.symm
        _ = _ := by rw [Nat.add_mul,Nat.one_mul]
    omega
  have H (t : Nat) : (r-1)^t*(r+t)≤r^(t+1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      calc
        _ = (r-1)^t*((r-1)*(r+t+1)) := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ (r-1)^t*(r*(r+t)) := Nat.mul_le_mul_left _ (hb t)
        _ = r*((r-1)^t*(r+t)) := by ac_rfl
        _ ≤ r*r^(t+1) := Nat.mul_le_mul_left _ ih
        _ = _ := (show r^(t+1+1)=r*r^(t+1) from Nat.pow_succ').symm
  have ht := H r
  rw [show r+r=2*r by omega,Nat.pow_succ] at ht
  apply Nat.le_of_mul_le_mul_left _ hr
  calc
    _ = (r-1)^r*(2*r) := by ac_rfl
    _ ≤ r^r*r := ht
    _ = _ := Nat.mul_comm ..

/-- Choose a half-survival block without a real logarithm. In particular
j = ceil(log₂(2*gain)) suffices. -/
theorem half_of_tail {n rate gain j : Nat} (_hn : 0<n) (hr : 0<rate)
    (hj : 2*gain≤2^j) (s : Nat)
    (h : rate^(rate*j)*s≤gain*(n*(rate-1))^(rate*j)) :
    2*s≤n^(rate*j) := by
  let b := rate*j
  have hPos : 0<rate^b := Nat.pow_pos hr
  refine Nat.le_of_mul_le_mul_left ?_ hPos
  calc
    _ = 2*(rate^b*s) := by ac_rfl
    _ ≤ 2*(gain*(n*(rate-1))^b) := Nat.mul_le_mul_left _ h
    _ = (2*gain)*(n^b*(rate-1)^b) := by rw [Nat.mul_pow]; ac_rfl
    _ ≤ 2^j*(n^b*(rate-1)^b) := Nat.mul_le_mul_right _ hj
    _ = n^b*(2*(rate-1)^rate)^j := by
      rw [Nat.mul_pow,← Nat.pow_mul]
      change 2^j*(n^b*(rate-1)^b)=_
      ac_rfl
    _ ≤ n^b*(rate^rate)^j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (rate_pow_half rate hr) _)
    _ = _ := by rw [←Nat.pow_mul]; ac_rfl

theorem mean {α : Type} {n : Nat} {next : α → Fin n → α}
    {I D : α → Prop} {rate gain : Nat} (C : ExpCert next I D rate gain)
    (hn : 0<n) (keep : ∀ x e, I x → I (next x e))
    (x : α) (hx : I x) :
    IIDExpectedHittingTimeAtMost next D x (2*rate*FastRestart.intersectionExponent gain) := by
  let j := FastRestart.intersectionExponent gain
  have hj : 2*gain≤2^j := FastRestart.intersectionExponent_covers gain
  have hjP : 0<j := by
    by_cases hz : j=0
    · simp [hz] at hj; have := C.gainPositive; omega
    · omega
  have h := FastRestart.mean_of_half_block next I D keep (rate*j)
    (Nat.mul_pos C.ratePositive hjP)
    (fun y hy => half_of_tail hn C.ratePositive hj _ (tail C hn keep _ y hy)) x hx
  simpa only [Nat.mul_assoc] using h

/-- Same closure rule for finitely many composed paths: a sum of gains,
not a sum of rates or a logarithm per stage. -/
theorem union_mean {α : Type} {n K : Nat} {next : α → Fin n → α}
    {I : α → Prop} {D : Fin K → α → Prop} {rate : Nat} (gain : Fin K → Nat)
    (C : ∀ i, ExpCert next I (D i) rate (gain i)) (hn : 0<n)
    (keep : ∀ x e, I x → I (next x e))
    (sticky : ∀ i x e, D i x → D i (next x e))
    (j : Nat) (hB : 0<rate*j) (hj : 2*sumEdge gain≤2^j) (x : α) (hx : I x) :
    IIDExpectedHittingTimeAtMost next (fun y => ∀ i, D i y) x (2*rate*j) := by
  have hr : 0<rate := by
    cases rate
    · simp at hB
    · omega
  have equiv : (fun y => ¬ ∀ i, D i y) = (fun y => ∃ i, ¬D i y) := by
    funext y
    exact propext not_forall
  have h := FastRestart.mean_of_half_block next I (fun y => ∀ i, D i y) keep (rate*j)
    hB (fun y hy => by rw [equiv]; exact half_of_tail hn hr hj _ (union_tail gain C hn keep sticky _ y hy)) x hx
  simpa only [Nat.mul_assoc] using h

/-- A finite chain of terminal-one certificates on the same augmented
raw state. Downstream stages are required only after their handoff. -/
inductive Chain {α : Type} {n : Nat} (next : α → Fin n → α)
    (rate gain : Nat) : (α → Prop) → (α → Prop) → Nat → Type where
  | done {I E : α → Prop} (all : ∀ x, I x → E x) : Chain next rate gain I E 0
  | more {I D E : α → Prop} {k : Nat} (first : ExpCert next I D rate gain)
      (sticky : ∀ x e, I x → D x → D (next x e))
      (nested : ∀ x, I x → E x → D x)
      (rest : Chain next rate gain (fun x => I x ∧ D x) E k) :
      Chain next rate gain I E (k+1)

/-- Unchanged rate and a product gain for a finite sequence. -/
noncomputable def ofChain {α : Type} {n : Nat} {next : α → Fin n → α}
    {I E : α → Prop} {rate gain k : Nat} (C : Chain next rate gain I E k)
    (hr : 0<rate) (keep : ∀ x e, I x → I (next x e)) :
    ExpCert next I E rate (gain^k) := by
  induction C with
  | done all =>
    refine ⟨1,by decide,hr,by simp,fun t _ => n^t,?_,?_,?_,?_⟩
    · intros; simp
    · intros; simp
    · intros; simp
    · intro _ x hx hz; exact (hz (all x hx)).elim
  | more first sticky nested rest ih =>
    have B := ih (fun x e hx => ⟨keep x e hx.1,sticky x e hx.1 hx.2⟩)
    rw [Nat.pow_succ']
    exact sequential first B keep sticky nested

private theorem sselector {n : Nat} (i : Fin n) (w : Nat) :
    sumEdge (fun e => if e=i then w else 0)=w := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : (fun e : Fin n => if e.succ=(0:Fin (n+1)) then w else 0) = fun _ => 0 :=
        funext fun e => by simp [Fin.succ_ne_zero]
      simp [sumEdge,List.ofFn_succ,h,show (List.ofFn (fun _ : Fin n => 0)).sum=0 by
        exact (sconst n 0).trans (Nat.mul_zero n)]
    · have h : (fun e : Fin n => if e.succ=j.succ then w else 0) = fun e => if e=j then w else 0 :=
        funext fun _ => by simp
      simpa [sumEdge,List.ofFn_succ,Ne.symm (Fin.succ_ne_zero j),h] using ih j

/-- Direct countdown certificate, with the terminal value normalized
to one.  State may retain the entire raw history or adaptive monitor. -/
noncomputable def fromCountdown {α : Type} {n : Nat} (next : α → Fin n → α)
    (I D : α → Prop) (budget : α → Nat) (nom : α → Fin n) (U : Nat) (hn : 0<n)
    (cap : ∀ x, I x → budget x≤U)
    (_keep : ∀ x e, I x → I (next x e))
    (decr : ∀ x e, I x → ¬D x →
      budget (next x e)+(if e=nom x then 1 else 0)≤budget x) :
    ExpCert next I D (2*n) (2^U) := by
  let B := fun x => if D x then 0 else budget x
  refine ⟨1,by decide,by omega,Nat.pow_pos (by decide),fun t x => 2^(B x)*n^t,?_,?_,?_,?_⟩
  · intro t x _
    have h : 1≤(2:Nat)^(B x) := Nat.pow_pos (by decide)
    exact Nat.mul_le_mul_right _ h
  · intro t x hx
    have h : B x≤U := by
      dsimp only [B]
      split
      · omega
      · exact cap x hx
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n^t)
      (Nat.pow_le_pow_right (by decide : 0<2) h)
  · intro t x _ hx
    simp [B,hx]
  · intro t x hx hd
    have hB (y : α) : B y≤budget y := by dsimp only [B]; split <;> omega
    have hb : 0<budget x := by
      have h := decr x (nom x) hx hd
      simp at h; omega
    let k := budget x-1
    have hxk : budget x=k+1 := by omega
    let W := 2^k*n^t
    have hW : 2^(B x)*n^t = 2*W := by
      rw [show B x=budget x from if_neg hd,hxk,Nat.pow_succ',Nat.mul_assoc]
    have hPt : 2^(B x)*n^(t+1)=2*W*n := by
      rw [Nat.pow_succ,← Nat.mul_assoc,hW]
    have child (e : Fin n) :
        2^(B (next x e))*n^t+(if e=nom x then W else 0)≤2*W := by
      by_cases he : e=nom x
      · have h := decr x e hx hd
        simp only [he,if_true] at h ⊢
        have h' : B (next x (nom x))≤k := by
          have h'' := hB (next x (nom x)); omega
        have hM := Nat.mul_le_mul_right (n^t) (Nat.pow_le_pow_right (by decide : 0<2) h')
        change _ ≤ W at hM
        omega
      · have h := decr x e hx hd
        simp only [he,if_false,Nat.add_zero] at h ⊢
        rw [←hW]
        have h' : B (next x e)≤B x := by
          rw [show B x=budget x from if_neg hd]
          exact Nat.le_trans (hB _) h
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h')
    have hS := smono child
    rw [sadd,sselector,sconst] at hS
    rw [hPt]
    let X := sumEdge (fun e => 2^(B (next x e))*n^t)
    change X+W≤n*(2*W) at hS
    change (2*n)*X≤(2*n-1)*(2*W*n)
    have hm := Nat.mul_le_mul_left (2*n) hS
    rw [Nat.mul_add] at hm
    have hEq : (2*n)*(n*(2*W))=(2*n-1)*(2*W*n)+(2*n)*W := by
      calc
        _ = (2*n)*(2*W*n) := by ac_rfl
        _ = ((2*n-1)+1)*(2*W*n) := congrArg (fun m => m*(2*W*n)) (by omega)
        _ = _ := by
          rw [Nat.add_mul,Nat.one_mul]
          congr 1
          ac_rfl
    omega

end L4.FastExp
