import Leader.L4.PhysicalCustody
import Leader.L4.Height.LeaderBridge
import Leader.Core.PredictableTwoTargetFiniteTree
import Leader.L4.RearGeometry

namespace L4.ReportCacheWindow
open AllSizeProtocol BStarH6Ordinal Height

variable {X : Type} {n : Nat}

/-- Literal cache projections on a closed fixed-header raw region.
A receiver write clips the old, not the new, initiator offset. -/
structure Frame (step : X → Fin n → X) (Q : X → Prop)
    (h : Fin n → Bool) (cap : Nat) (off : X → Fin n → Nat)
    (successor : X → Fin n → Bool) : Prop where
  closed : ∀ x e, Q x → Q (step x e)
  respond : ∀ x e, Q x → off (step x e) (rightNeighbor e)=
    if h (rightNeighbor e) then 0 else min cap ((if h e then 0 else min cap (off x e))+1)
  hold : ∀ x e i, Q x → i≠rightNeighbor e → off (step x e) i=off x i
  writeSucc : ∀ x e, Q x → successor (step x e) e=h (rightNeighbor e)
  holdSucc : ∀ x e i, Q x → i≠e → successor (step x e) i=successor x i

/-- A dependency cone of precision k at this site, precision k-1 at
its predecessor, and so on. No global cover is required. -/
def Precision (h : Fin n → Bool) (hh : ∃ i,h i=true) (off : X → Fin n → Nat)
    (x : X) : Nat → Fin n → Prop
  | 0, _ => True
  | k+1, i => min (k+1) (off x i)=min (k+1) (ordinal h hh i) ∧
      Precision h hh off x k (RearTrace.predecessor i)

private theorem rhs_precision (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (cap k : Nat) (K : k+1≤cap) (e : Fin n) (o : Nat)
    (P : min k o=min k (ordinal h hh e)) :
    min (k+1) (if h (rightNeighbor e) then 0 else min cap ((if h e then 0 else min cap o)+1)) =
      min (k+1) (ordinal h hh (rightNeighbor e)) := by
  rw [ordinal_right]
  by_cases A : h (rightNeighbor e)=true
  · rw [if_pos A,if_pos A]
  · rw [if_neg A,if_neg A]
    by_cases B : h e=true
    · rw [if_pos B,(ordinal_zero h hh e).mpr B]
      omega
    · rw [if_neg B]
      omega

theorem precision_closed {step : X → Fin n → X} {Q : X → Prop}
    {h : Fin n → Bool} (hh : ∃ i,h i=true) {cap : Nat}
    {off : X → Fin n → Nat} {successor : X → Fin n → Bool}
    (F : Frame step Q h cap off successor) (k : Nat) (K : k≤cap)
    (i : Fin n) (x : X) (e : Fin n) (A : Q x) (P : Precision h hh off x k i) :
    Precision h hh off (step x e) k i := by
  induction k generalizing i with
  | zero => trivial
  | succ k ih =>
    change _ ∧ _ at P ⊢
    refine ⟨?_,ih (by omega) _ P.2⟩
    by_cases I : i=rightNeighbor e
    · subst i
      have G : Precision h hh off x k e := by
        simpa only [RearTrace.predecessor_right] using P.2
      have H : min k (off x e)=min k (ordinal h hh e) := by
        cases k
        · rfl
        · exact G.1
      rw [F.respond x e A]
      exact rhs_precision h hh cap k K e _ H
    · rw [F.hold x e i A I]
      exact P.1

theorem predecessor_earns {step : X → Fin n → X} {Q : X → Prop}
    {h : Fin n → Bool} (hh : ∃ i,h i=true) {cap : Nat}
    {off : X → Fin n → Nat} {successor : X → Fin n → Bool}
    (F : Frame step Q h cap off successor) (k : Nat) (K : k+1≤cap)
    (i : Fin n) (x : X) (A : Q x)
    (P : Precision h hh off x k (RearTrace.predecessor i)) :
    Precision h hh off (step x (RearTrace.predecessor i)) (k+1) i := by
  let e := RearTrace.predecessor i
  have E : rightNeighbor e=i := RearTrace.right_predecessor i
  have H : min k (off x e)=min k (ordinal h hh e) := by
    cases k
    · rfl
    · exact P.1
  change _ ∧ _
  refine ⟨?_,precision_closed hh F k (by omega) e x e A P⟩
  change min (k+1) (off (step x e) i)=min (k+1) (ordinal h hh i)
  rw [←E,F.respond x e A]
  exact rhs_precision h hh cap k K e _ H

/-- Once this site has full precision and the raw cache is bounded by
cap, the actual stored bits encode the exact clipped physical ordinal. -/
theorem precision_raw_offset (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (off : X → Fin n → Nat) (cap : Nat) (x : X) (i : Fin n)
    (K : 0<cap) (D : off x i≤cap) (P : Precision h hh off x cap i) :
    off x i=min cap (ordinal h hh i) := by
  cases cap with
  | zero => omega
  | succ cap =>
    have E := P.1
    rwa [Nat.min_eq_right D] at E

private theorem hit_weaken {step : X → Fin n → X} {P T : X → Prop}
    (sub : ∀ x, P x → T x) (x : X) (k : Nat) :
    Height.iidHitCost step T k x≤Height.iidHitCost step P k x := by
  induction k generalizing x with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    by_cases H : T x
    · simp [Height.iidHitCost,H]
    have G : ¬P x := fun g=>H (sub x g)
    simp only [Height.iidHitCost,if_neg H,if_neg G]
    exact Nat.add_le_add_left (FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun e=>ih (step x e))) _

private theorem marked_expected {step : X → Fin n → X} {region target : X → Prop}
    (a : Fin n) (safe : ∀ x e, region x → region (step x e))
    (success : ∀ x, region x → target (step x a)) (x : X) (A : region x) :
    Height.IIDExpectedHittingTimeAtMost step target x n := by
  intro t
  induction t generalizing x with
  | zero => simp [Height.iidHitCost]
  | succ t ih =>
    by_cases H : target x
    · simp [Height.iidHitCost,H]
    simp only [Height.iidHitCost,if_neg H]
    let f := fun e : Fin n=>if e=a then 0 else n*n^t
    have L : (List.ofFn (fun e=>Height.iidHitCost step target t (step x e))).sum ≤ (List.ofFn f).sum := by
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      by_cases E : e=a
      · subst e
        rw [Height.iidHitCost_of_target _ _ _ (success x A)]
        exact Nat.zero_le _
      · simpa only [f,if_neg E] using ih (step x e) (safe x e A)
    rw [PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const a f (n*n^t)
      (fun e E=>if_neg E)] at L
    simp only [f,if_true,Nat.zero_add] at L
    calc
      _ ≤ n^(t+1) + (n-1)*(n*n^t) := Nat.add_le_add_left L _
      _ = n*n^(t+1) := by
        have N : 1+(n-1)=n := by have := a.isLt; omega
        rw [Nat.pow_succ,Nat.mul_comm (n^t) n]
        calc
          _ = (1+(n-1))*(n*n^t) := by rw [Nat.add_mul,Nat.one_mul]
          _ = _ := by rw [N]

/-- Each added link of a localized dependency cone waits for just its
predecessor's next physical mark, which costs n in expectation. -/
theorem precision_expected {step : X → Fin n → X} {Q : X → Prop}
    {h : Fin n → Bool} (hh : ∃ i,h i=true) {cap : Nat}
    {off : X → Fin n → Nat} {successor : X → Fin n → Bool}
    (F : Frame step Q h cap off successor) (k : Nat) (K : k≤cap)
    (i : Fin n) (x : X) (A : Q x) :
    Height.IIDExpectedHittingTimeAtMost step (fun z=>Q z ∧ Precision h hh off z k i) x (k*n) := by
  induction k generalizing i x with
  | zero =>
    intro t
    rw [Height.iidHitCost_of_target step (fun z=>Q z ∧ Precision h hh off z 0 i) x ⟨A,trivial⟩]
    exact Nat.zero_le _
  | succ k ih =>
    let L := fun z=>Q z ∧ Precision h hh off z k (RearTrace.predecessor i)
    let T := fun z=>Q z ∧ Precision h hh off z (k+1) i
    have first : Height.IIDExpectedHittingTimeAtMost step (fun z=>L z ∨ T z) x (k*n) :=
      fun t=>Nat.le_trans (hit_weaken (fun _=>Or.inl) x t)
        (ih (by omega) (RearTrace.predecessor i) x A t)
    have next : ∀ z, L z → Height.IIDExpectedHittingTimeAtMost step T z n := by
      intro z Z
      exact marked_expected (RearTrace.predecessor i)
        (fun y e Y=>⟨F.closed y e Y.1,precision_closed hh F k (by omega) _ y e Y.1 Y.2⟩)
        (fun y Y=>⟨F.closed y _ Y.1,predecessor_earns hh F k K i y Y.1 Y.2⟩) z Z
    rw [Nat.succ_mul]
    exact iid_stage_le step (by have := i.isLt; omega) x L T (k*n) n first next

/-- Site certificate with both cache fields. The last mark writes the
successor field; since its endpoints are distinct, it cannot clobber
the already-certified raw offset at the initiator. -/
def SiteCorrect (Q : X → Prop) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (cap : Nat) (off : X → Fin n → Nat) (successor : X → Fin n → Bool)
    (i : Fin n) (x : X) : Prop :=
  Q x ∧ Precision h hh off x cap i ∧ off x i≤cap ∧ successor x i=h (rightNeighbor i)

private theorem offBound_mark {step : X → Fin n → X} {Q : X → Prop}
    {h : Fin n → Bool} {cap : Nat} {off : X → Fin n → Nat} {succ : X → Fin n → Bool}
    (F : Frame step Q h cap off succ) (x : X) (e : Fin n) (A : Q x) :
    off (step x e) (rightNeighbor e)≤cap := by
  rw [F.respond x e A]
  split
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

theorem site_correct_closed {step : X → Fin n → X} {Q : X → Prop}
    {h : Fin n → Bool} (hh : ∃ i,h i=true) {cap : Nat}
    {off : X → Fin n → Nat} {succ : X → Fin n → Bool}
    (F : Frame step Q h cap off succ) (i : Fin n) (x : X) (e : Fin n)
    (A : SiteCorrect Q h hh cap off succ i x) :
    SiteCorrect Q h hh cap off succ i (step x e) := by
  refine ⟨F.closed x e A.1, precision_closed hh F cap (Nat.le_refl _) i x e A.1 A.2.1,?_,?_⟩
  · by_cases E : i=rightNeighbor e
    · subst i
      exact offBound_mark F x e A.1
    · rw [F.hold x e i A.1 E]
      exact A.2.2.1
  · by_cases E : i=e
    · subst i
      exact F.writeSucc x e A.1
    · rw [F.holdSucc x e i A.1 E]
      exact A.2.2.2

/-- The site certificate is reached in at most cap predecessor
marks and one writer mark, each costing n expected raw marks. -/
theorem site_correct_expected {step : X → Fin n → X} {Q : X → Prop}
    {h : Fin n → Bool} (hh : ∃ i,h i=true) {cap : Nat}
    {off : X → Fin n → Nat} {succ : X → Fin n → Bool}
    (F : Frame step Q h cap off succ) (C : 0<cap)
    (i : Fin n) (x : X) (A : Q x) :
    Height.IIDExpectedHittingTimeAtMost step (SiteCorrect Q h hh cap off succ i) x ((cap+1)*n) := by
  let e := RearTrace.predecessor i
  have ei : rightNeighbor e=i := RearTrace.right_predecessor _
  let k := cap-1
  have KC : k+1=cap := by dsimp [k]; omega
  let L := fun z=>Q z ∧ Precision h hh off z k e
  let M := fun z=>Q z ∧ Precision h hh off z cap i ∧ off z i≤cap
  let T := SiteCorrect Q h hh cap off succ i
  have D : ∀ y f, M y → M (step y f) := by
    intro y f Y
    refine ⟨F.closed y f Y.1,precision_closed hh F cap (Nat.le_refl _) i y f Y.1 Y.2.1,?_⟩
    by_cases E : i=rightNeighbor f
    · rw [E]
      exact offBound_mark F y f Y.1
    · rw [F.hold y f i Y.1 E]
      exact Y.2.2
  have H1 : Height.IIDExpectedHittingTimeAtMost step (fun z=>L z ∨ M z) x (k*n) :=
    fun t=>Nat.le_trans (hit_weaken (fun _=>Or.inl) x t) (precision_expected hh F k (by omega) e x A t)
  have H2 : ∀ y, L y → Height.IIDExpectedHittingTimeAtMost step M y n := by
    intro y Y
    refine marked_expected e
      (fun z f Z=>⟨F.closed z f Z.1, precision_closed hh F k (by omega) e z f Z.1 Z.2⟩)
      (fun z Z=>⟨F.closed z e Z.1,?_,?_⟩) y Y
    · rw [←KC]
      exact predecessor_earns hh F k (by omega) i z Z.1 Z.2
    · rw [←ei]
      exact offBound_mark F z e Z.1
  have HP := iid_stage_le step (by have := i.isLt; omega) x L M (k*n) n H1 H2
  have H3 : Height.IIDExpectedHittingTimeAtMost step (fun z=>M z ∨ T z) x (cap*n) := by
    have U : k*n+n=cap*n := by rw [←Nat.succ_mul]; exact congrArg (fun c=>c*n) KC
    rw [U] at HP
    exact fun t=>Nat.le_trans (hit_weaken (fun _=>Or.inl) x t) (HP t)
  have H4 : ∀ y, M y → Height.IIDExpectedHittingTimeAtMost step T y n := by
    intro y Y
    exact marked_expected i D (fun z Z=>⟨(D z i Z).1,(D z i Z).2.1,
      (D z i Z).2.2,F.writeSucc z i Z.1⟩) y Y
  rw [Nat.succ_mul]
  exact iid_stage_le step (by have := i.isLt; omega) x M T (cap*n) n H3 H4

section Literal
variable {a : LargeParams} {w k : Nat}

private theorem frame_of_refresh (b : LargeRows a) (G : ShortGeo w k)
    (read : LargeSite a → BitVec w) (low : Headers → Bool)
    (h : Fin n → Bool) (cap : Nat) (Q : (Fin n → LargeSite a) → Prop)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (size : cap<2^k)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,low (oldHeaders b (x i))=h i)
    (refresh : ∀ old : Pair (LargeSite a),
      G.Refresh cap (Pair.map (fun y=>low (oldHeaders b y)) old)
        (Pair.map read old) (Pair.map read (largePair b old))) :
    Frame (AllSizeS1Geometry.step b) Q h cap
      (fun x i=>(G.off.read (read (x i))).toNat)
      (fun x i=>(G.successor.read (read (x i))).getLsbD 0) := by
  have R (x : Fin n → LargeSite a) (e : Fin n) (A : Q x) :
      let r := rightNeighbor e
      let y := AllSizeS1Geometry.step b x e
      G.Refresh cap (h e,h r) (read (x e),read (x r)) (read (y e),read (y r)) := by
    dsimp only
    have f := refresh (x e,x (rightNeighbor e))
    change G.Refresh cap (low (oldHeaders b (x e)),low (oldHeaders b (x (rightNeighbor e))))
      (read (x e),read (x (rightNeighbor e)))
      (read (largePair b (x e,x (rightNeighbor e))).1,
        read (largePair b (x e,x (rightNeighbor e))).2) at f
    rw [mask x A e,mask x A (rightNeighbor e)] at f
    simpa only [AllSizeS1Geometry.step,if_true,if_pos rfl,if_neg (Ne.symm (sep e))] using f
  refine ⟨closed,?_,?_,?_,?_⟩
  · intro x e A
    have E := congrArg BitVec.toNat (R x e A).2.1
    rw [G.nextOff_nat _ _ _ size] at E
    exact E
  · intro x e i A I
    by_cases E : i=e
    · subst i
      exact congrArg BitVec.toNat (R x e A).2.2.1
    · simp only [AllSizeS1Geometry.step,if_neg E,if_neg I]
  · intro x e A
    have E := congrArg (fun b : BitVec 1=>b.getLsbD 0) (R x e A).1
    cases T : h (rightNeighbor e)
    · simpa [ShortGeo.nextSuccessor,T] using E
    · simpa [ShortGeo.nextSuccessor,T] using E
  · intro x e i A I
    by_cases E : i=rightNeighbor e
    · subst i
      exact congrArg (fun b : BitVec 1=>b.getLsbD 0) (R x e A).2.2.2
    · simp only [AllSizeS1Geometry.step,if_neg I,if_neg E]

/-- Every lower-layer-stable region of the actual report1 row
satisfies the per-site clock interface, with cap 3. -/
theorem report1_frame (b : LargeRows a) (h : Fin n → Bool)
    (Q : (Fin n → LargeSite a) → Prop)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders b (x i)).h4=h i) :
    let G := ShortGeo.report (a.k1+1) 1 a.J1
    Frame (AllSizeS1Geometry.step b) Q h 3
      (fun x i=>(G.off.read (x i).report1).toNat)
      (fun x i=>(G.successor.read (x i).report1).getLsbD 0) :=
  frame_of_refresh b (ShortGeo.report (a.k1+1) 1 a.J1)
    LargeSite.report1 Headers.h4 h 3 Q sep (ShortGeo.ell_cap 3) closed mask
    (fun x=>(largePair_short_geometry b x).2.2.2.1)

/-- Report2 uses cap max 3 t2. It is not silently clipped to
three as in the short MIS sheets. -/
theorem report2_frame (b : LargeRows a) (h : Fin n → Bool)
    (Q : (Fin n → LargeSite a) → Prop)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders b (x i)).h5=h i) :
    let G := ShortGeo.report 2 a.t2 a.J2
    Frame (AllSizeS1Geometry.step b) Q h (max 3 a.t2)
      (fun x i=>(G.off.read (x i).report2).toNat)
      (fun x i=>(G.successor.read (x i).report2).getLsbD 0) :=
  frame_of_refresh b (ShortGeo.report 2 a.t2 a.J2)
    LargeSite.report2 Headers.h5 h (max 3 a.t2) Q sep (ShortGeo.ell_cap _) closed mask
    (fun x=>(largePair_short_geometry b x).2.2.2.2.1)

end Literal

end L4.ReportCacheWindow
