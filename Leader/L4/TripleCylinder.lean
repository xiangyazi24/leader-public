import Leader.L4.TripleControlled
import Leader.L4.TripleRenewal

/-! Enumeration of first-stop effective cylinders by their charges.
This connects the controlled scheduler's finite expectation to renewal. -/
namespace L4.TripleCylinder
open TripleControlled TripleRenewal TripleResidual BarrierIID Classical

private theorem ss {n : Nat} (f : Fin (n+1) → Nat) :
    TaggedTail.sumEdge f = f 0 + TaggedTail.sumEdge (fun e => f e.succ) := by
  simp [TaggedTail.sumEdge,List.ofFn_succ]

private theorem ns_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e≤g e) :
    TaggedTail.sumEdge f ≤ TaggedTail.sumEdge g := by
  induction n with
  | zero => simp [TaggedTail.sumEdge]
  | succ n ih => rw [ss,ss]; exact Nat.add_le_add (h _) (ih (fun e => h e.succ))

private theorem ns_add {n : Nat} (f g : Fin n → Nat) :
    TaggedTail.sumEdge (fun e => f e+g e) = TaggedTail.sumEdge f+TaggedTail.sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ss,ss f,ss g,ih]; omega

private theorem ns_cast {n : Nat} (f : Fin n → Nat) :
    (TaggedTail.sumEdge f : Int) = edgeSum (fun e => (f e : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ss,Int.natCast_add,ih]
    simp [edgeSum,List.ofFn_succ]

private theorem edge_add {n : Nat} (f g : Fin n → Int) :
    edgeSum (fun e => f e+g e) = edgeSum f+edgeSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons] at ih ⊢
    rw [ih]; omega

private theorem edge_mono {n : Nat} {f g : Fin n → Int} (hh : ∀ e,f e≤g e) :
    edgeSum f≤edgeSum g := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons] at *
    exact Int.add_le_add (hh 0) (ih (fun e => hh e.succ))

private theorem edge_scale {n : Nat} (a : Int) (f : Fin n → Int) :
    edgeSum (fun e => a*f e) = a*edgeSum f := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Int.mul_add]

private theorem remap_sum {n : Nat} (b : Bool) (l r : Fin n) (h : l≠r) (f : Fin n → Int) :
    edgeSum (fun e => f (controlledEdge b l r e)) =
      edgeSum (fun e => if b && e == r then 0 else if b && e == l then 2*f e else f e) := by
  cases b
  · simp [controlledEdge]
  · have h₁ (e : Fin n) : f (controlledEdge true l r e) =
          f e + (if e=r then f l-f r else 0) := by
      by_cases he : e=r
      · subst e; simp [controlledEdge]; omega
      · simp [controlledEdge,he]
    have h₂ (e : Fin n) : (if true && e == r then 0 else if true && e == l then 2*f e else f e) =
          f e + ((if e=r then -f r else 0) + (if e=l then f l else 0)) := by
      by_cases he : e=r
      · subst e; simp [Ne.symm h]; omega
      · by_cases he' : e=l
        · subst e; simp [h]; omega
        · simp [he,he']
    simp only [h₁,h₂,edge_add,edgeSum_selector]
    omega

/-- An effective word can be followed unless it uses the suppressed
outgoing orientation at readiness. -/
def allowed {α : Type} {n : Nat} (ready : α → Bool) (r : Fin n) (x : α) (e : Fin n) : Bool :=
  !(ready x && e == r)

/-- Unit cost at every effective ready-time incoming mark. -/
def chargeUnit {α : Type} {n : Nat} (ready : α → Bool) (l : Fin n) (x : α) (e : Fin n) : Nat :=
  (ready x && e == l).toNat

/-- Charge of an actual raw service after predictably redirecting it. -/
def rawCharge {α : Type} {n : Nat} (ready : α → Bool) (l r : Fin n) (x : α) (e : Fin n) : Int :=
  (chargeUnit ready l x (controlledEdge (ready x) l r e) : Int)

/-- Enumerate charges on all stopped successful effective words of
exact length t, in lexicographic raw-label order. Once stopped, append
arbitrary suffix labels at unit weight and no further charge. -/
noncomputable def terminalCharges {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (stop : α → Prop) : Nat → α → List Nat
  | 0, x => if stop x then [0] else []
  | t+1, x => if stop x then List.replicate (n^(t+1)) 0 else
      (List.ofFn (fun e : Fin n =>
        if allowed ready r x e then
          (terminalCharges next ready l r stop t (next x e)).map
            (fun q => chargeUnit ready l x e + q)
        else [])).flatten

private theorem flat_len {n : Nat} (f : Fin n → List Nat) :
    (List.ofFn f).flatten.length = TaggedTail.sumEdge (fun e => (f e).length) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ,ss,ih]

private theorem lm_add (a b : List Nat) :
    likelihoodMass (a++b) = likelihoodMass a+likelihoodMass b := by
  simp [likelihoodMass]

private theorem cm_add (a b : List Nat) :
    chargeMass (a++b) = chargeMass a+chargeMass b := by
  simp [chargeMass]

private theorem flat_lm {n : Nat} (f : Fin n → List Nat) :
    likelihoodMass (List.ofFn f).flatten = TaggedTail.sumEdge (fun e => likelihoodMass (f e)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ,ss,ih,lm_add]

private theorem flat_cm {n : Nat} (f : Fin n → List Nat) :
    chargeMass (List.ofFn f).flatten = TaggedTail.sumEdge (fun e => chargeMass (f e)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ,ss,ih,cm_add]

private theorem shift_lm (u : Nat) (q : List Nat) :
    likelihoodMass (q.map (fun x => u+x)) = 2^u*likelihoodMass q := by
  induction q with
  | nil => simp [likelihoodMass]
  | cons x q ih =>
    change 2^(u+x)+likelihoodMass (q.map (fun x => u+x)) = 2^u*(2^x+likelihoodMass q)
    rw [ih,Nat.pow_add,Nat.mul_add]

private theorem shift_cm (u : Nat) (q : List Nat) :
    chargeMass (q.map (fun x => u+x)) = 2^u*(u*likelihoodMass q+chargeMass q) := by
  induction q with
  | nil => simp [likelihoodMass,chargeMass]
  | cons x q ih =>
    change (u+x)*2^(u+x)+chargeMass (q.map (fun x => u+x)) =
      2^u*(u*(2^x+likelihoodMass q)+(x*2^x+chargeMass q))
    rw [ih,Nat.pow_add]
    simp only [Nat.add_mul,Nat.mul_add]
    ac_rfl

private theorem lm_replicate (u : Nat) :
    likelihoodMass (List.replicate u 0) = u := by
  induction u with
  | zero => rfl
  | succ u ih => simpa [List.replicate_succ,likelihoodMass] using (congrArg (fun v => 1+v) ih).trans (Nat.add_comm 1 u)

private theorem cm_replicate (u : Nat) :
    chargeMass (List.replicate u 0) = 0 := by
  induction u with
  | zero => rfl
  | succ u ih => simp [List.replicate_succ,chargeMass] at *

private theorem masked_remap {α : Type} {n : Nat} (ready : α → Bool)
    (l r : Fin n) (h : l≠r) (x : α) (f : Fin n → Int) :
    edgeSum (fun e => if allowed ready r x e then
      (2:Int)^(chargeUnit ready l x e)*f e else 0) =
      edgeSum (fun e => f (controlledEdge (ready x) l r e)) := by
  rw [remap_sum _ l r h]
  apply congrArg edgeSum
  funext e
  simp only [allowed,chargeUnit]
  by_cases hb : ready x = true
  · by_cases hL : e=l
    · subst e; simp [hb,h,Int.pow_one]
    · have hEL : (e == l) = false := by simpa using hL
      by_cases hR : e=r <;> simp [hb,hEL,hR]
  · have hb' : ready x = false := Bool.eq_false_iff.mpr hb
    simp [hb']

/-- The list's likelihood mass is exactly the number of raw controlled
words reaching the first stop by the horizon. -/
theorem terminalCharges_mass {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (h : l≠r) (stop : α → Prop)
    (t : Nat) (x : α) :
    likelihoodMass (terminalCharges next ready l r stop t x) =
      terminalMass (controlledNext next ready l r) stop (fun _ => True) t x := by
  induction t generalizing x with
  | zero => by_cases hs : stop x <;> simp [terminalCharges,terminalMass,hs,likelihoodMass]
  | succ t ih =>
    by_cases hs : stop x
    · simp [terminalCharges,terminalMass,hs,lm_replicate]
    · simp only [terminalCharges,terminalMass,hs,if_false,flat_lm]
      apply Int.ofNat.inj
      change (↑(TaggedTail.sumEdge _) : Int) = (↑(TaggedTail.sumEdge _) : Int)
      rw [ns_cast,ns_cast]
      let f := fun e => (terminalMass (controlledNext next ready l r) stop
        (fun _ => True) t (next x e) : Int)
      change _ = edgeSum (fun e => f (controlledEdge (ready x) l r e))
      rw [←masked_remap ready l r h x f]
      apply congrArg edgeSum
      funext e
      by_cases ha : allowed ready r x e
      · simp [ha,shift_lm,ih,Int.natCast_mul,Int.natCast_pow,f]
      · simp [ha,likelihoodMass]

private theorem rawCharge_nonnegative {α : Type} {n : Nat} (ready : α → Bool)
    (l r : Fin n) (x : α) (e : Fin n) : 0≤rawCharge ready l r x e :=
  Int.natCast_nonneg _

/-- Charge of complete effective words is bounded by the stopped raw
charge expectation, which also accounts for the unfinished words. -/
theorem terminalCharges_firstMoment {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (h : l≠r) (stop : α → Prop)
    (t : Nat) (x : α) :
    (chargeMass (terminalCharges next ready l r stop t x) : Int) ≤
      stoppedDriftNumerator (controlledNext next ready l r) stop (rawCharge ready l r) t x := by
  let cnext := controlledNext next ready l r
  induction t generalizing x with
  | zero => by_cases hs : stop x <;> simp [terminalCharges,stoppedDriftNumerator,hs,chargeMass]
  | succ t ih =>
    by_cases hs : stop x
    · simp [terminalCharges,stoppedDriftNumerator,hs,cm_replicate]
    · simp only [terminalCharges,stoppedDriftNumerator,hs,if_false,flat_cm]
      rw [ns_cast]
      let f := fun e => (chargeUnit ready l x e : Int) *
          likelihoodMass (terminalCharges next ready l r stop t (next x e)) +
          (chargeMass (terminalCharges next ready l r stop t (next x e)) : Int)
      have he (e : Fin n) :
          (↑(chargeMass (if allowed ready r x e then
            List.map (fun q => chargeUnit ready l x e + q)
              (terminalCharges next ready l r stop t (next x e)) else [])) : Int) =
          if allowed ready r x e then (2:Int)^(chargeUnit ready l x e)*f e else 0 := by
        by_cases ha : allowed ready r x e
        · simp [ha,shift_cm,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,f]
        · simp [ha,chargeMass]
      simp only [he]
      rw [masked_remap ready l r h x]
      have bound (e : Fin n) :
          f (controlledEdge (ready x) l r e) ≤ (n:Int)^t*rawCharge ready l r x e +
            stoppedDriftNumerator cnext stop (rawCharge ready l r) t (cnext x e) := by
        let j := controlledEdge (ready x) l r e
        have hb := Nat.mul_le_mul_left (chargeUnit ready l x j)
          (terminalMass_le_total cnext stop (fun _ => True) t (cnext x e))
        rw [← terminalCharges_mass next ready l r h] at hb
        have hh : (chargeUnit ready l x j : Int) *
            (likelihoodMass (terminalCharges next ready l r stop t (next x j)) : Int) ≤
            (n:Int)^t*rawCharge ready l r x e := by
          simpa [Int.natCast_mul,Int.natCast_pow,Nat.mul_comm,j,cnext,controlledNext,rawCharge]
            using (show ((chargeUnit ready l x j *
              likelihoodMass (terminalCharges next ready l r stop t (next x j)) : Nat) : Int) ≤
              ((chargeUnit ready l x j*n^t : Nat) : Int) from Int.ofNat_le.mpr hb)
        exact Int.add_le_add hh (ih (next x j))
      have H := edge_mono bound
      rw [edge_add (fun e : Fin n => (n:Int)^t*rawCharge ready l r x e)
        (fun e => stoppedDriftNumerator cnext stop (rawCharge ready l r) t (cnext x e)),edge_scale] at H
      exact H

/-- Along allowed effective labels the original attempt and the
controlled attempt have the same projected physical state; the original
can end early on a suppressed label which never occurs in this list. -/
structure Agreement {α β : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (r : Fin n) (stop good : α → Prop)
    (orig : β → Fin n → β) (origDone origGoal : β → Prop) (project : α → β) : Prop where
  keep : ∀ x e, good x → ¬stop x → allowed ready r x e → good (next x e)
  step : ∀ x e, good x → ¬stop x → allowed ready r x e →
    project (next x e) = orig (project x) e
  before : ∀ x, good x → ¬stop x → ¬origDone (project x)
  success : ∀ x, good x → stop x → origDone (project x) ∧ origGoal (project x)

/-- The charge list indexes distinct successful cylinders in the
original scheduler; its length is therefore at most original success. -/
theorem terminalCharges_injection {α β : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (stop good : α → Prop)
    (orig : β → Fin n → β) (origDone origGoal : β → Prop) (project : α → β)
    (agree : Agreement next ready r stop good orig origDone origGoal project)
    (t : Nat) (x : α) (hx : good x) :
    (terminalCharges next ready l r stop t x).length ≤
      terminalMass orig origDone origGoal t (project x) := by
  induction t generalizing x with
  | zero =>
    by_cases hs : stop x
    · obtain ⟨hd,hg⟩ := agree.success x hx hs
      simp [terminalCharges,terminalMass,hs,hd,hg]
    · simp [terminalCharges,hs]
  | succ t ih =>
    by_cases hs : stop x
    · obtain ⟨hd,hg⟩ := agree.success x hx hs
      simp [terminalCharges,terminalMass,hs,hd,hg]
    · simp only [terminalCharges,terminalMass,hs,if_false,flat_len,agree.before x hx hs]
      apply ns_mono
      intro e
      by_cases ha : allowed ready r x e
      · simp only [ha,if_true,List.length_map]
        rw [←agree.step x e hx hs ha]
        exact ih _ (agree.keep x e hx hs ha)
      · simp [ha]

private theorem ns_zero (n : Nat) : TaggedTail.sumEdge (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ss,ih]

private theorem terminalMass_false {α : Type} {n : Nat} (next : α → Fin n → α)
    (done : α → Prop) (t : Nat) (x : α) :
    terminalMass next done (fun _ => False) t x = 0 := by
  induction t generalizing x with
  | zero => simp [terminalMass]
  | succ t ih =>
    by_cases h : done x
    · simp [terminalMass,h]
    · simp [terminalMass,h,ih,ns_zero]

/-- Terminal failed-word bound for the original attempt from the exact
controlled-scheduler charge moment, controlled mean and projection
on admissible labels. The shift/enumeration and likelihood are derived. -/
theorem failure_bound {α β : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (hlr : l≠r) (stop good : α → Prop)
    (orig : β → Fin n → β) (origDone origGoal : β → Prop) (project : α → β)
    (agree : Agreement next ready r stop good orig origDone origGoal project)
    (m B : Nat) (x : α) (hx : good x)
    (mean : IIDExpectedHittingTimeAtMost (controlledNext next ready l r) stop x B)
    (moment : ∀ t, stoppedDriftNumerator (controlledNext next ready l r) stop
      (rawCharge ready l r) t x ≤ (m : Int)*(n : Int)^t) :
    ∀ t, 2^m * terminalMass orig origDone (fun y => ¬ origGoal y) t (project x) ≤
      (2^m-1)*n^t := by
  have hn : 0<n := Nat.zero_lt_of_lt l.isLt
  apply failure_of_controlled_words orig origDone origGoal (project x)
    (controlledNext next ready l r) stop x hn m B mean
  intro t
  let qs := terminalCharges next ready l r stop t x
  refine ⟨qs, ?_, ?_, terminalCharges_injection next ready l r stop good orig origDone
    origGoal project agree t x hx⟩
  · have h := partition_terminalMass (controlledNext next ready l r) stop
      (fun _ => True) x t
    have hfalse : (fun _ : α => ¬ True) = fun _ => False := by funext y; simp
    rw [hfalse,terminalMass_false,Nat.add_zero,←terminalCharges_mass next ready l r hlr] at h
    exact Nat.le_of_eq h.symm
  · apply Int.ofNat_le.mp
    rw [Int.natCast_mul,Int.natCast_pow]
    exact Int.le_trans (terminalCharges_firstMoment next ready l r hlr stop t x) (moment t)

/-- Starting immediately after the incoming dummy earns no initial
charge credit. Divide d668's finite compensator estimate by n*d to get
the exact moment premise of `failure_bound`. -/
theorem moment_of_zero_credit {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop : α → Prop) (charge : α → Fin n → Int)
    (d m B : Nat) (x : α) (hn : 0<n) (hd : 0<d)
    (cost : IIDExpectedHittingTimeAtMost next stop x B)
    (budget : B≤n*d*m)
    (compensator : ∀ t, (n:Int)*(d:Int)*stoppedDriftNumerator next stop charge t x ≤
      (iidHitCost next stop t x : Int)) :
    ∀ t, stoppedDriftNumerator next stop charge t x ≤ (m:Int)*(n:Int)^t := by
  intro t
  have h := Nat.le_trans (cost t) (Nat.mul_le_mul_right (n^t) budget)
  have hi : (iidHitCost next stop t x : Int) ≤
      ((n:Int)*(d:Int)*(m:Int))*(n:Int)^t := by
    simpa only [Int.natCast_mul,Int.natCast_pow] using (Int.ofNat_le.mpr h)
  have hh := Int.le_trans (compensator t) hi
  have hpos : 0 < (n:Int)*(d:Int) :=
    Int.mul_pos (by omega) (by omega)
  apply Int.le_of_mul_le_mul_left _ hpos
  rw [←Int.mul_assoc]
  exact hh

/-- The moderate-sector constants fit the integer tangent at m=6. -/
theorem moderate_charge_budget (a b n : Nat) (hb : 2≤b) (ha : a≤2*b) :
    n*(5*a-2) ≤ n*(2*b-1)*6 := by
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  omega

end L4.TripleCylinder

#print axioms L4.TripleCylinder.terminalCharges_mass
#print axioms L4.TripleCylinder.terminalCharges_firstMoment
#print axioms L4.TripleCylinder.terminalCharges_injection
#print axioms L4.TripleCylinder.failure_bound

#print axioms L4.TripleCylinder.moment_of_zero_credit
