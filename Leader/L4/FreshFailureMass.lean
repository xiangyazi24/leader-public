import Leader.L4.FreshGapAssembly

/-! Fixed-cutoff and distinct-gap arithmetic for the fresh-birth trial.
All counts are exact numerators on the common original raw scheduler. -/
namespace L4.FreshFailureMass
open RankRenewal TaggedTail RankRace Classical

private theorem sSucc {n : Nat} (f : Fin (n+1)→Nat) :
    sumEdge f=f 0+sumEdge (fun i => f i.succ) := by simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n→Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

private theorem sAdd {n : Nat} (f g : Fin n→Nat) :
    sumEdge (fun i => f i+g i)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem sMul {n : Nat} (a : Nat) (f : Fin n→Nat) :
    sumEdge (fun i => a*f i)=a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

private theorem eMono {α : Type} {n : Nat} (next : α→Fin n→α)
    (f g : α→Nat) (good : α→Prop) (keep : ∀ x e, good x → good (next x e))
    (h : ∀ x, good x → f x≤g x) (t : Nat) (x : α) (hx : good x) :
    endpointSum next f t x≤endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h _ hx
  | succ t ih => exact sMono (fun e => ih _ (keep _ _ hx))

private theorem eAdd {α : Type} {n : Nat} (next : α→Fin n→α)
    (f g : α→Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => f y+g y) t x=endpointSum next f t x+endpointSum next g t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sAdd]

private theorem eMul {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : α→Nat) (a t : Nat) (x : α) :
    endpointSum next (fun y => a*f y) t x=a*endpointSum next f t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sMul]

private theorem eComp {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : α→Nat) (T U : Nat) (x : α) :
    endpointSum next f (T+U) x =
      endpointSum next (fun y => endpointSum next f U y) T x := by
  induction T generalizing x with
  | zero => simp [endpointSum]
  | succ T ih =>
    rw [show T+1+U=(T+U)+1 by omega]
    simp only [endpointSum,ih]

private theorem gap_sum_congr (f g : Nat→Nat) (b k : Nat)
    (h : ∀ i, b≤i → i<b+k → f i=g i) : gapSum f b k=gapSum g b k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    change f b+gapSum f (b+1) k = g b+gapSum g (b+1) k
    rw [h _ (by omega) (by omega),ih _ (fun i hi hj => h i (by omega) (by omega))]

private theorem eGap {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : Nat→α→Nat) (b k T : Nat) (x : α) :
    endpointSum next (fun y => gapSum (fun h => f h y) b k) T x=
      gapSum (fun h => endpointSum next (f h) T x) b k := by
  induction k generalizing b with
  | zero =>
    change endpointSum next (fun _ => 0) T x=0
    induction T generalizing x with
    | zero => rfl
    | succ T ih => simp [endpointSum,ih,sConst]
  | succ k ih =>
    simp only [gapSum,eAdd,ih]

/-- Shift the raw horizon from the true first epoch entry without a
factor for the number of possible entry times. The invariant is needed
only until entry and on the entering mark; it need not survive after. -/
theorem scaled_bound_of_first_entry {α : Type} {n : Nat}
    (next : α→Fin n→α) (entered before : α→Prop) (score : α→Nat) (C : Nat)
    (keep : ∀ x e, before x → ¬entered x → before (next x e))
    (absent : ∀ x, before x → ¬entered x → score x=0)
    (entryBound : ∀ x, before x → entered x → ∀ t, C*endpointSum next score t x≤n^t)
    (t : Nat) (x : α) (hx : before x) :
    C*endpointSum next score t x≤n^t := by
  induction t generalizing x with
  | zero =>
    by_cases h : entered x
    · exact entryBound x hx h 0
    · simp [endpointSum,absent x hx h]
  | succ t ih =>
    by_cases h : entered x
    · exact entryBound x hx h (t+1)
    · rw [endpointSum,←sMul]
      calc
        _ ≤ sumEdge (fun _ : Fin n => n^t) := sMono (fun e => ih _ (keep x e hx h))
        _ = _ := by rw [sConst,Nat.pow_succ']

private theorem ePad_low {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : α→Nat) (mono : ∀ y e, f y≤f (next y e)) (U : Nat) (x : α) :
    n^U*f x≤endpointSum next f U x := by
  induction U generalizing x with
  | zero => simp [endpointSum]
  | succ U ih =>
    calc
      _ = sumEdge (fun _ : Fin n => n^U*f x) := by rw [sConst,Nat.pow_succ',Nat.mul_assoc]
      _ ≤ sumEdge (fun e => n^U*f (next x e)) :=
        sMono (fun e => Nat.mul_le_mul_left _ (mono x e))
      _ ≤ _ := sMono (fun e => ih (next x e))

/-- Prefix padding inequality for an already-recorded flag. -/
theorem sticky_pad_lower {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : α→Nat) (mono : ∀ y e, f y≤f (next y e)) (T U : Nat) (x : α) :
    n^U*endpointSum next f T x≤endpointSum next f (T+U) x := by
  rw [eComp,←eMul]
  exact eMono next _ _ (fun _ => True) (fun _ _ _ => trivial)
    (fun z _ => ePad_low next f mono U z) T x trivial

private theorem late_constant {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : α→Nat) (age : α→Nat) (D U : Nat)
    (inc : ∀ y e, age y+1=age (next y e))
    (freeze : ∀ y e, D≤age y → f (next y e)=f y)
    (x : α) (hx : D≤age x) :
    endpointSum next f U x=n^U*f x := by
  induction U generalizing x with
  | zero => simp [endpointSum]
  | succ U ih =>
    have h (e : Fin n) : endpointSum next f U (next x e)=n^U*f x := by
      rw [ih (next x e) (by rw [←inc]; omega),freeze _ _ hx]
    simp only [endpointSum,h,sConst,Nat.pow_succ',Nat.mul_assoc]

private theorem eAgeCongr {α : Type} {n : Nat} (next : α→Fin n→α)
    (f g : α→Nat) (age : α→Nat) (D : Nat)
    (inc : ∀ y e, age y+1=age (next y e))
    (h : ∀ y, D≤age y → f y=g y) (T : Nat) (x : α) (hx : D≤age x+T) :
    endpointSum next f T x=endpointSum next g T x := by
  induction T generalizing x with
  | zero => exact h _ (by omega)
  | succ T ih =>
    simp only [endpointSum]
    apply congrArg sumEdge
    funext e
    exact ih _ (by rw [←inc]; omega)

/-- Convert an exact local bound checked at the inclusive deadline
D to all remaining raw horizons. Before D, use monotonicity of stored
event evidence; after D, the observer must freeze that evidence. -/
theorem all_horizons_of_fixed_cutoff {α : Type} {n : Nat} (next : α→Fin n→α)
    (f : α→Nat) (age : α→Nat) (D C : Nat) (x : α) (hn : 0<n)
    (inc : ∀ y e, age y+1=age (next y e))
    (sticky : ∀ y e, f y≤f (next y e))
    (freeze : ∀ y e, D≤age y → f (next y e)=f y)
    (fixed : C*endpointSum next f D x≤n^D) :
    ∀ T, C*endpointSum next f T x≤n^T := by
  intro T
  by_cases h : T≤D
  · let V := D-T
    have ht : T+V=D := by dsimp [V]; omega
    have hpos : 0<n^V := Nat.pow_pos hn
    apply Nat.le_of_mul_le_mul_left _ hpos
    calc
      _ = C*(n^V*endpointSum next f T x) := by ac_rfl
      _ ≤ C*endpointSum next f (T+V) x := Nat.mul_le_mul_left _ (sticky_pad_lower next f sticky T V x)
      _ ≤ n^D := by rw [ht]; exact fixed
      _ = _ := by rw [←Nat.pow_add,show V+T=D by omega]
  · let U := T-D
    have ht : D+U=T := by dsimp [U]; omega
    have he : endpointSum next f (D+U) x=n^U*endpointSum next f D x := by
      rw [eComp,←eMul]
      exact eAgeCongr next _ _ age D inc (fun y hy => late_constant next f age D U inc freeze y hy)
        D x (by omega)
    rw [←ht,he,Nat.pow_add]
    calc
      _ = n^U*(C*endpointSum next f D x) := by ac_rfl
      _ ≤ n^U*n^D := Nat.mul_le_mul_left _ fixed
      _ = _ := by ac_rfl

/-- The finite sum really includes each gap with index in its range. -/
theorem gap_entry_le_sum (f : Nat→Nat) (b k h : Nat) (hb : b≤h) (hk : h<b+k) :
    f h≤gapSum f b k := by
  induction k generalizing b with
  | zero => omega
  | succ k ih =>
    by_cases hh : h=b
    · subst h; exact Nat.le_add_right ..
    · exact Nat.le_trans (ih (b+1) (by omega) (by omega)) (Nat.le_add_left ..)

/-- Multiplicity-free gap union. Early and late event numerators may use
different induction/coupling arguments; only deterministic coverage on
a single observer and uniform bounds for positive distinct gaps are used. -/
theorem failure_mass_of_gap_partition {α : Type} {n : Nat}
    (next : α→Fin n→α) (x : α) (t K : Nat) (failed : α→Nat)
    (early late : Nat→α→Nat) (good : α→Prop) (hx : good x)
    (keep : ∀ z e, good z → good (next z e))
    (cover : ∀ z, good z → failed z≤gapSum (fun h => early h z+late h z) 1 K)
    (earlyBound : ∀ h, 0<h → h≤K → 256^h*endpointSum next (early h) t x≤n^t)
    (lateBound : ∀ h, 0<h → h≤K → 256^h*endpointSum next (late h) t x≤n^t) :
    1000*endpointSum next failed t x≤11*n^t := by
  let a (h : Nat) := if h≤K then endpointSum next (early h) t x else 0
  let b (h : Nat) := if h≤K then endpointSum next (late h) t x else 0
  have ha (h : Nat) (hh : 0<h) : 256^h*a h≤n^t := by
    by_cases hk : h≤K
    · simpa [a,hk] using earlyBound h hh hk
    · simp [a,hk]
  have hb (h : Nat) (hh : 0<h) : 256^h*b h≤n^t := by
    by_cases hk : h≤K
    · simpa [b,hk] using lateBound h hh hk
    · simp [b,hk]
  have hg := eMono next failed _ good keep cover t x hx
  rw [eGap] at hg
  have he : gapSum (fun h => endpointSum next (fun z => early h z+late h z) t x) 1 K=
      gapSum (fun h => a h+b h) 1 K := by
    apply gap_sum_congr
    intro i hi hiK
    have hK : i≤K := by omega
    simp [eAdd,a,b,hK]
  rw [he] at hg
  exact Nat.le_trans (Nat.mul_le_mul_left _ hg)
    (elevenPerThousand_of_distinct_gap_masses (n^t) K a b ha hb)

/-- Any endpoint failure assigned to one positive gap contributes a
unit to the finite gap union. Attribution need not choose a random gap. -/
theorem attributed_failure_le_gap_sum {α : Type} (failure : α→Prop)
    (early late : Nat→α→Nat) (K : Nat) (z : α)
    (cover : failure z → ∃ h, 0<h ∧ h≤K ∧ 1≤early h z+late h z) :
    (if failure z then 1 else 0)≤gapSum (fun h => early h z+late h z) 1 K := by
  by_cases h : failure z
  · obtain ⟨g,hg,hK,hPos⟩ := cover h
    rw [if_pos h]
    exact Nat.le_trans hPos (gap_entry_le_sum (fun h => early h z+late h z) 1 K g (by omega) (by omega))
  · simp [h]

/-- E.g. weaken the 2048⁻ʰ slow-payment budget to the common 256⁻ʰ
gap budget without changing either event or raw scheduler horizon. -/
theorem relax_scaled_budget (small large h mass total : Nat) (hl : small≤large)
    (bound : large^h*mass≤total) : small^h*mass≤total :=
  Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hl h)) bound

/-- Direct first-entry assembly for separate early and late risks.
This leaves exactly the local entry bounds and the pointwise attribution
as obligations. Early and late are allowed to overlap. -/
theorem failure_mass_by_first_entries {α : Type} {n : Nat}
    (next : α→Fin n→α) (x : α) (t K : Nat) (failure : α→Prop)
    (early late : Nat→α→Nat) (good : α→Prop) (hx : good x)
    (keep : ∀ z e, good z → good (next z e))
    (credit : ∀ z, good z → failure z → ∃ h, 0<h ∧ h≤K ∧ 1≤early h z+late h z)
    (entry before : Nat→α→Prop)
    (starts : ∀ h, 0<h → h≤K → before h x)
    (pre : ∀ h z e, 0<h → h≤K → before h z → ¬entry h z → before h (next z e))
    (absent : ∀ h z, 0<h → h≤K → before h z → ¬entry h z → early h z=0 ∧ late h z=0)
    (entryBound : ∀ h z, 0<h → h≤K → before h z → entry h z →
      ∀ u, 256^h*endpointSum next (early h) u z≤n^u ∧
        256^h*endpointSum next (late h) u z≤n^u) :
    1000*endpointSum next (fun z => if failure z then 1 else 0) t x≤11*n^t := by
  refine failure_mass_of_gap_partition next x t K _ early late good hx keep
    (fun z hz => attributed_failure_le_gap_sum failure early late K z (credit z hz)) ?_ ?_
  · intro h hh hK
    exact scaled_bound_of_first_entry next (entry h) (before h) (early h) (256^h)
      (fun z e => pre h z e hh hK)
      (fun z hz he => (absent h z hh hK hz he).1)
      (fun z hz he u => (entryBound h z hh hK hz he u).1)
      t x (starts h hh hK)
  · intro h hh hK
    exact scaled_bound_of_first_entry next (entry h) (before h) (late h) (256^h)
      (fun z e => pre h z e hh hK)
      (fun z hz he => (absent h z hh hK hz he).2)
      (fun z hz he u => (entryBound h z hh hK hz he u).2)
      t x (starts h hh hK)

/-- The checked fresh-failure bound is stronger than the quarter
budget required by the outer RestartTrial interface. -/
theorem quarter_of_elevenPerThousand (mass total : Nat) (hh : 1000*mass≤11*total) :
    4*mass≤total := by omega

end L4.FreshFailureMass

