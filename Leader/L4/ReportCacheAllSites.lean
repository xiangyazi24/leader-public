import Leader.L4.ReportCacheWindow
import Leader.L4.ShortResetCycle

namespace L4.ReportCacheAllSites

open AllSizeProtocol BStarH6Ordinal Height ReportCacheWindow

variable {X : Type} {n : Nat}

/-- The invariant includes the dependency cone, and not just a coincidentally
correct raw field. This is what permits the earlier sites to remain complete. -/
def AllCorrect (Q : X → Prop) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (cap : Nat) (off : X → Fin n → Nat) (successor : X → Fin n → Bool)
    (x : X) : Prop :=
  Q x ∧ ∀ i, SiteCorrect Q h hh cap off successor i x

private def PrefixCorrect (Q : X → Prop) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (cap : Nat) (off : X → Fin n → Nat) (successor : X → Fin n → Bool)
    (k : Nat) (x : X) : Prop :=
  Q x ∧ ∀ i : Fin n, i.val<k → SiteCorrect Q h hh cap off successor i x

private theorem cost_eq_under {step : X → Fin n → X} (A P T : X → Prop)
    (stay : ∀ z e, A z → A (step z e))
    (same : ∀ z, A z → (P z ↔ T z)) (x : X) (hx : A x) (t : Nat) :
    Height.iidHitCost step P t x=Height.iidHitCost step T t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : P x
    · simp [Height.iidHitCost,H,(same x hx).mp H]
    · have K : ¬T x := fun a=>H ((same x hx).mpr a)
      simp only [Height.iidHitCost,if_neg H,if_neg K]
      congr 2
      apply congrArg List.ofFn
      funext e
      exact ih _ (stay x e hx)

private theorem cost_weaken {step : X → Fin n → X} {P T : X → Prop}
    (sub : ∀ z, P z → T z) (x : X) (t : Nat) :
    Height.iidHitCost step T t x≤Height.iidHitCost step P t x := by
  induction t generalizing x with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases H : T x
    · simp [Height.iidHitCost,H]
    · have J : ¬P x := fun h=>H (sub x h)
      simp only [Height.iidHitCost,if_neg H,if_neg J]
      exact Nat.add_le_add_left (FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun e=>ih (step x e))) _

theorem all_closed {step : X → Fin n → X} {Q : X → Prop} {h : Fin n → Bool}
    (hh : ∃ i,h i=true) {cap : Nat} {off : X → Fin n → Nat} {succ : X → Fin n → Bool}
    (F : Frame step Q h cap off succ) (x : X) (e : Fin n)
    (A : AllCorrect Q h hh cap off succ x) :
    AllCorrect Q h hh cap off succ (step x e) :=
  ⟨F.closed x e A.1,fun i=>site_correct_closed hh F i x e (A.2 i)⟩

theorem raw_fields_correct {Q : X → Prop} {h : Fin n → Bool} (hh : ∃ i,h i=true)
    {cap : Nat} {off : X → Fin n → Nat} {succ : X → Fin n → Bool}
    (C : 0<cap) (x : X) (A : AllCorrect Q h hh cap off succ x) (i : Fin n) :
    off x i=min cap (ordinal h hh i) ∧ succ x i=h (rightNeighbor i) :=
  let B := A.2 i
  ⟨precision_raw_offset h hh off cap x i C B.2.2.1 B.2.1,B.2.2.2⟩

/-- Enumerate sites, not sampled labels. Each stage stops on its first
certificate on the original alphabet; earlier certificates remain true. -/
theorem all_expected {step : X → Fin n → X} {Q : X → Prop} {h : Fin n → Bool}
    (hh : ∃ i,h i=true) {cap : Nat} {off : X → Fin n → Nat} {succ : X → Fin n → Bool}
    (F : Frame step Q h cap off succ) (C : 0<cap) (x : X) (XQ : Q x) :
    Height.IIDExpectedHittingTimeAtMost step (AllCorrect Q h hh cap off succ) x ((cap+1)*n^2) := by
  let S := PrefixCorrect Q h hh cap off succ
  let K := (cap+1)*n
  have HN : 0<n := by obtain ⟨i,_⟩ := hh; exact Nat.zero_lt_of_lt i.isLt
  have stable (k : Nat) (z : X) (e : Fin n) (A : S k z) : S k (step z e) :=
    ⟨F.closed z e A.1,fun i I=>site_correct_closed hh F i z e (A.2 i I)⟩
  have H (k : Nat) (kn : k≤n) : Height.IIDExpectedHittingTimeAtMost step (S k) x (k*K) := by
    induction k with
    | zero =>
      intro t
      rw [Height.iidHitCost_of_target step (S 0) x ⟨XQ,fun i I=>False.elim (Nat.not_lt_zero _ I)⟩]
      exact Nat.zero_le _
    | succ k ih =>
      let i : Fin n := ⟨k,by omega⟩
      have one (z : X) (A : S k z) :
          Height.IIDExpectedHittingTimeAtMost step (S (k+1)) z K := by
        have A' (y : X) (Y : S k y) :
            S (k+1) y ↔ SiteCorrect Q h hh cap off succ i y := by
          constructor
          · intro L
            exact L.2 i (Nat.lt_succ_self k)
          · intro L
            refine ⟨Y.1,fun j J=>?_⟩
            by_cases E : j.val=k
            · have T : j=i := Fin.ext E
              subst j
              exact L
            · exact Y.2 j (by omega)
        intro t
        rw [cost_eq_under (S k) (S (k+1)) (SiteCorrect Q h hh cap off succ i) (stable k) A' z A t]
        exact site_correct_expected hh F C i z A.1 t
      have L := ih (by omega)
      have first : Height.IIDExpectedHittingTimeAtMost step (fun z=>S k z ∨ S (k+1) z) x (k*K) :=
        fun t=>Nat.le_trans (cost_weaken (fun z H=>Or.inl H) x t) (L t)
      rw [show (k+1)*K=k*K+K by rw [Nat.succ_mul]]
      exact iid_stage_le step HN x (S k) (S (k+1)) (k*K) K first one
  have EQ : S n=AllCorrect Q h hh cap off succ := by
    funext z
    apply propext
    exact ⟨fun A=>⟨A.1,fun i=>A.2 i i.isLt⟩,fun A=>⟨A.1,fun i _=>A.2 i⟩⟩
  have B := H n (Nat.le_refl _)
  rw [EQ,show n*K=(cap+1)*n^2 by dsimp [K]; rw [Nat.pow_two]; ac_rfl] at B
  exact B

section Literal
variable {a : LargeParams}

abbrev Report1Correct (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : (Fin n → LargeSite a) → Prop) (x : Fin n → LargeSite a) : Prop :=
  let G := ShortGeo.report (a.k1+1) 1 a.J1
  AllCorrect Q h hh 3 (fun y i=>(G.off.read (y i).report1).toNat)
    (fun y i=>(G.successor.read (y i).report1).getLsbD 0) x

abbrev Report2Correct (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : (Fin n → LargeSite a) → Prop) (x : Fin n → LargeSite a) : Prop :=
  let G := ShortGeo.report 2 a.t2 a.J2
  AllCorrect Q h hh (max 3 a.t2) (fun y i=>(G.off.read (y i).report2).toNat)
    (fun y i=>(G.successor.read (y i).report2).getLsbD 0) x

theorem report1_all_sites (b : LargeRows a) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : (Fin n → LargeSite a) → Prop)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders b (x i)).h4=h i)
    (x : Fin n → LargeSite a) (A : Q x) :
    (∀ y e, Report1Correct h hh Q y → Report1Correct h hh Q (AllSizeS1Geometry.step b y e)) ∧
    Height.IIDExpectedHittingTimeAtMost (AllSizeS1Geometry.step b) (Report1Correct h hh Q) x (4*n^2) := by
  have F := report1_frame b h Q sep closed mask
  exact ⟨all_closed hh F,all_expected hh F (by decide) x A⟩

theorem report2_all_sites (b : LargeRows a) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : (Fin n → LargeSite a) → Prop)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (closed : ∀ x e,Q x→Q (AllSizeS1Geometry.step b x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders b (x i)).h5=h i)
    (x : Fin n → LargeSite a) (A : Q x) :
    (∀ y e, Report2Correct h hh Q y → Report2Correct h hh Q (AllSizeS1Geometry.step b y e)) ∧
    Height.IIDExpectedHittingTimeAtMost (AllSizeS1Geometry.step b) (Report2Correct h hh Q) x
      ((max 3 a.t2+1)*n^2) := by
  have F := report2_frame b h Q sep closed mask
  exact ⟨all_closed hh F,all_expected hh F (by omega) x A⟩

end Literal

section Production
open PhysicalCustody

theorem report1_raw {s n : Nat} (N : 1<n) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop)
    (closed : ∀ x e,Q x→Q (rawNext s x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders (rows s) (x i)).h4=h i)
    (x : Raw s n) (A : Q x) :
    (∀ y e, Report1Correct h hh Q y → Report1Correct h hh Q (rawNext s y e)) ∧
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (Report1Correct h hh Q) x (4*n^2) :=
  report1_all_sites (rows s) h hh Q (ShortResetCycle.edge_sep N) closed mask x A

theorem report2_raw {s n : Nat} (N : 1<n) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop)
    (closed : ∀ x e,Q x→Q (rawNext s x e))
    (mask : ∀ x,Q x→∀ i,(oldHeaders (rows s) (x i)).h5=h i)
    (x : Raw s n) (A : Q x) :
    (∀ y e, Report2Correct h hh Q y → Report2Correct h hh Q (rawNext s y e)) ∧
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (Report2Correct h hh Q) x
      ((max 3 (ell (radiusTwo s+1))+1)*n^2) :=
  report2_all_sites (rows s) h hh Q (ShortResetCycle.edge_sep N) closed mask x A

end Production

#print axioms all_closed
#print axioms raw_fields_correct
#print axioms all_expected
#print axioms report1_all_sites
#print axioms report2_all_sites
#print axioms report1_raw
#print axioms report2_raw
end L4.ReportCacheAllSites
