import Leader.L4.WindowA0Guard
import Leader.L4.TripleRenewal

/-! A0: finite-word 6-label release credit under a supplied frame. -/
namespace L4.WindowA0ReleaseCredit
open TaggedTail TripleRenewal Classical

inductive Phase where
  | waiting (progress : Fin 3)
  | success
  | failed
  deriving DecidableEq

def score : Phase → Nat
  | .waiting k => 6^k.val
  | .success => 216
  | .failed => 0

def done : Phase → Prop
  | .waiting _ => False
  | _ => True

def mask {n : Nat} (labels : List (Fin n)) (e : Fin n) : Nat :=
  if e ∈ labels then 1 else 0

private theorem mono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    exact Nat.add_le_add (h 0) (ih (fun e => h e.succ))

private theorem plus {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih]; omega

private theorem mul {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e) = a*sumEdge f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.mul_add]

private theorem const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem selector {n : Nat} (r : Fin n) (a : Nat) :
    sumEdge (fun e => if e=r then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) r
    · have Z : (fun e : Fin n => if e.succ=(0:Fin (n+1)) then a else 0) = fun _ => 0 :=
        funext fun e => by simp [Fin.succ_ne_zero]
      simp [sumEdge,List.ofFn_succ,Z,show (List.ofFn (fun _ : Fin n => 0)).sum=0 by
        exact (const n 0).trans (Nat.mul_zero n)]
    · have E : (fun e : Fin n => if e.succ=j.succ then a else 0) =
          fun e => if e=j then a else 0 := funext fun _ => by simp
      simpa [sumEdge,List.ofFn_succ,Ne.symm (Fin.succ_ne_zero j),E] using ih j

/-- The cardinal bound counts each physical edge at most once; duplicate
indices in the cyclic list never increase the size of the race. -/
theorem mask_sum {n : Nat} (labels : List (Fin n)) :
    sumEdge (mask labels) ≤ labels.length := by
  induction labels with
  | nil =>
    have Z : (mask ([] : List (Fin n))) = fun _ => 0 := funext fun e => by simp [mask]
    rw [Z,const,Nat.mul_zero]
    exact Nat.le_refl _
  | cons a more ih =>
    have h : ∀ e : Fin n, mask (a::more) e ≤ (if e=a then 1 else 0) + mask more e := by
      intro e
      by_cases he : e=a <;> simp [mask,he]
    have H := mono h
    rw [plus,selector] at H
    simp only [List.length_cons]
    omega

/-- The six consecutive physical initiator labels i−2 through i+3,
written clockwise from the admitted top i (for n ≥ 4). -/
def labelsAt {n : Nat} (i : Fin n) : List (Fin n) :=
  List.ofFn fun j : Fin 6 => liftedSite i (n-2+j.val)

@[simp] theorem labelsAt_length {n : Nat} (i : Fin n) :
    (labelsAt i).length = 6 := by simp [labelsAt]

/-- All three possible requested bonds in the paid/unpaid scripts
are in the fixed list, also when circular aliases deduplicate it. -/
theorem script_labels_mem {n : Nat} (hn : 4≤n) (i : Fin n) :
    GGStage.incoming i 0 ∈ labelsAt i ∧ i ∈ labelsAt i ∧
      rightNeighbor i ∈ labelsAt i := by
  refine ⟨?_,?_,?_⟩ <;> unfold labelsAt <;> apply List.mem_ofFn.mpr
  · refine ⟨(1 : Fin 6),?_⟩
    unfold GGStage.incoming
    change liftedSite i (n-2+1)=liftedSite i (0+n-1)
    congr 1; omega
  · refine ⟨(2 : Fin 6),?_⟩
    change liftedSite i (n-2+2)=i
    rw [show n-2+2=n by omega,liftedSite_full]
  · refine ⟨(3 : Fin 6),?_⟩
    change liftedSite i (n-2+3)=rightNeighbor i
    rw [show n-2+3=n+1 by omega,liftedSite_succ,liftedSite_full]

/-- Local submartingale arithmetic. Unspecified competitors may have
zero credit. Outside the fixed list a step stutters in stage or makes
an earlier favorable exit; we only use that credit does not decrease. -/
theorem drift {n : Nat} (labels : List (Fin n)) (hl : labels.length ≤ 6)
    (r : Fin n) (hr : r ∈ labels) (w : Nat) (f : Fin n → Nat)
    (hwin : 6*w ≤ f r) (hout : ∀ e, e ∉ labels → w ≤ f e) :
    n*w ≤ sumEdge f := by
  have H : ∀ e, w+(if e=r then 6*w else 0) ≤ f e+w*mask labels e := by
    intro e
    by_cases he : e=r
    · subst e; simp [mask,hr]; omega
    · rw [if_neg he,Nat.add_zero]
      by_cases h : e ∈ labels
      · simp [mask,h]
      · simpa [mask,h] using hout e h
  have h := mono H
  rw [plus,const,selector,plus,mul] at h
  have hL := Nat.mul_le_mul_left w (Nat.le_trans (mask_sum labels) hl)
  have E : w*6=6*w := Nat.mul_comm ..
  omega

/-- Context at a continuing admission prefix. The label list is fixed
for the entire experiment; the advancing nominated label is adapted. -/
structure Frame {α : Type} {n : Nat} (next : α → Fin n → α)
    (phase : α → Phase) (labels : List (Fin n)) (x : α) (k : Fin 3) where
  requested : Fin n
  inside : requested ∈ labels
  onRequest : 6*score (.waiting k) ≤ score (phase (next x requested))
  outside : ∀ e, e ∉ labels → phase (next x e)=.waiting k ∨ phase (next x e)=.success

private theorem score_le (p : Phase) : score p ≤ 216 := by
  cases p with
  | success | failed => decide
  | waiting k =>
    apply Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<6) (show k.val≤3 by omega))
    decide

/-- At every horizon, terminal failure on the original raw scheduler
plus the live or successful initial credit is bounded by the total.
A successful physical stop is represented by Phase.success. -/
theorem finite_credit {α : Type} {n : Nat} (next : α → Fin n → α)
    (phase : α → Phase) (labels : List (Fin n)) (hl : labels.length ≤ 6)
    (good : α → Prop)
    (keep : ∀ x e k, good x → phase x=.waiting k → good (next x e))
    (frame : ∀ x k, good x → phase x=.waiting k → Frame next phase labels x k) :
    ∀ t x, good x →
      216*terminalMass next (fun y => done (phase y)) (fun y => phase y=.failed) t x
        + score (phase x)*n^t ≤ 216*n^t := by
  intro t
  induction t with
  | zero =>
    intro x hx
    cases h : phase x with
    | waiting k => simpa [terminalMass,h,done] using score_le (.waiting k)
    | success | failed => simp [terminalMass,h,done,score]
  | succ t ih =>
    intro x hx
    cases h : phase x with
    | success | failed => simp [terminalMass,h,done,score]
    | waiting k =>
      let F := frame x k hx h
      let bad (y : α) := terminalMass next (fun z => done (phase z)) (fun z => phase z=.failed) t y
      let f (e : Fin n) := score (phase (next x e))
      have d : n*score (.waiting k) ≤ sumEdge f := by
        refine drift labels hl F.requested F.inside _ f F.onRequest ?_
        intro e he
        rcases F.outside e he with hs|hs
        · simp [f,hs]
        · simpa [f,hs,score] using score_le (.waiting k)
      have hC := mono (fun e => ih (next x e) (keep x e k hx h))
      change sumEdge (fun e => 216*bad (next x e)+f e*n^t) ≤
         sumEdge (fun _ : Fin n => 216*n^t) at hC
      rw [plus,mul,const] at hC
      rw [show (fun e => f e*n^t)=(fun e => n^t*f e) from
        funext (fun _ => Nat.mul_comm _ _),mul] at hC
      simp only [terminalMass,h,done,if_false]
      change 216*sumEdge (fun e => bad (next x e))+score (.waiting k)*n^(t+1) ≤ 216*n^(t+1)
      rw [Nat.pow_succ]
      have hD := Nat.mul_le_mul_left (n^t) d
      calc
        _ ≤ 216*sumEdge (fun e => bad (next x e))+n^t*sumEdge f := by
          apply Nat.add_le_add_left
          simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hD
        _ ≤ n*(216*n^t) := hC
        _ = _ := by ac_rfl

theorem release_failure_bound {α : Type} {n : Nat} (next : α → Fin n → α)
    (phase : α → Phase) (i : Fin n) (good : α → Prop)
    (keep : ∀ x e k, good x → phase x=.waiting k → good (next x e))
    (frame : ∀ x k, good x → phase x=.waiting k → Frame next phase (labelsAt i) x k)
    (t : Nat) (x : α) (hx : good x) (h0 : phase x=.waiting 0) :
    216*terminalMass next (fun y => done (phase y)) (fun y => phase y=.failed) t x ≤ 215*n^t := by
  have h := finite_credit next phase (labelsAt i) (by simp) good keep frame t x hx
  simp only [h0,score,Fin.val_zero,Nat.pow_zero,Nat.one_mul] at h
  have hEq : 216*n^t = 215*n^t+n^t := by
    rw [show (216:Nat)=215+1 by decide,Nat.add_mul,Nat.one_mul]
  omega

end L4.WindowA0ReleaseCredit
