import Leader.L4.BStarResetReleaseAuthority
import Leader.L4.BStarResetSchedule

/-! The exact local boundary used to distinguish inherited authority
from a post-reset acquisition. A raw zero bit can become nonzero only
by a winning request at that same intrinsic incidence. -/
namespace L4.BStarGrantBirth
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongGrant BStarLongCommandData
open BStarLongGrantProjection BStarLongLayout

private theorem canonical_false (old : Ports) (j : Fin 3) (H : old j=false) :
    canonical old j=false := by
  unfold canonical
  by_cases V : old 1=true
  · have N : j≠1 := by intro E; subst j; exact Bool.noConfusion (V.symm.trans H)
    simp [V,show (j==1)=false from Bool.eq_false_iff.mpr (fun E => N (beq_iff_eq.mp E))]
  · simp [Bool.eq_false_iff.mpr V,H]

theorem result_birth (old rel ask : Ports) (j : Fin 3) (H : old j=false)
    (G : result old rel ask j=true) : win old rel ask j=true ∧ ask j=true := by
  have W : win old rel ask j=true := by simpa [result,canonical_false old j H] using G
  refine ⟨W,?_⟩
  unfold win at W
  by_cases I : j=1
  · subst j
    simp only [if_true, Bool.and_eq_true] at W
    exact W.1.2
  · simp only [if_neg I, Bool.and_eq_true] at W
    exact W.1.1.2

/-- The actual packed long pair. Both request and winner use the old
normalized grant semantics, so a same-mark release cannot create a
spurious acquisition story for a surviving grant. -/
theorem joined_birth (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side) (j : Fin 3) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let o := (round g raw).offered
    let old := original (BStarLongGrant.atOld raw s)
    let rel := fun k => requested o s k releaseOp
    let ask := fun k => requested o s k acquire
    read raw s j=0 →
      read (Pair.map LargeSite.long (largePair b x)) s j≠0 →
      (geometry g s).axes.h6=true ∧ win old rel ask j=true ∧ ask j=true := by
  dsimp only
  intro Z N
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw := Pair.map LargeSite.long x
  let o := (round g raw).offered
  have R : grants g raw o s j=true := by
    have E := joined_grants k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x s j
    cases V : grants g raw o s j
    · exact (N (E.trans (congrArg BitVec.ofBool V))).elim
    · rfl
  have Orig : original (BStarLongGrant.atOld raw s) j=false := by
    change (read raw s j).getLsbD 0=false
    rw [Z]
    rfl
  obtain ⟨header,G⟩ := Bool.and_eq_true_iff.mp R
  exact ⟨header,result_birth _ _ _ j Orig G⟩

#print axioms joined_birth

open BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

def bit (x : X) (i : Fin n) (j : Fin 3) := (grant j).read (x i).long

/-- Pre-update evidence at a physical grant incidence. This records
a successful old-pair arbitration, not a receipt-byte match. -/
def WonAt (x : X) (e i : Fin n) (j : Fin 3) : Prop :=
  ∃ s : Side, site e s=i ∧
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let o := (round g raw).offered
    (geometry g s).axes.h6=true ∧
      win (original (BStarLongGrant.atOld raw s))
        (fun k => requested o s k releaseOp) (fun k => requested o s k acquire) j=true ∧
      ∃ C q, (C,.advance q)∈o ∧ C.source.side=s ∧ C.source.occurrence.val=j.val ∧
        q.fault=0 ∧ q.opcode.toNat=acquire

private theorem req_of_win (x : X) (e : Fin n) (j : Fin 3) (s : Side)
    (Z : read ((x e).long,(x (rightNeighbor e)).long) s j=0)
    (N : read (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s j≠0) :
    WonAt hp x e (site e s) j := by
  have ⟨H,W,A⟩ := joined_birth k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) s j Z N
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  change requested (round g raw).offered s j acquire=true at A
  obtain ⟨⟨C,a⟩,P,Q⟩ := List.any_eq_true.mp A
  have L := Bool.and_eq_true_iff.mp Q
  cases a <;> try (simp at L)
  rename_i q
  exact ⟨s,rfl,H,W,C,q,P,L.1.1,L.1.2,L.2.1,L.2.2⟩

theorem mark_birth (x : X) (e i : Fin n) (j : Fin 3)
    (he : e≠rightNeighbor e) (Z : bit x i j=0) (N : bit (step x e) i j≠0) :
    WonAt hp x e i j := by
  by_cases E : i=e
  · subst i
    have H : step x e e=(largePair B (x e,x (rightNeighbor e))).1 := by
      simp only [AllSizeS1Geometry.step,if_true]
    have Z' : read ((x e).long,(x (rightNeighbor e)).long) .left j=0 := Z
    have N' : read (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) .left j≠0 := by
      change (grant j).read (largePair B (x e,x (rightNeighbor e))).1.long≠0
      rw [←H]
      exact N
    exact req_of_win hp x e j .left Z' N'
  · by_cases R : i=rightNeighbor e
    · subst i
      have H : step x e (rightNeighbor e)=(largePair B (x e,x (rightNeighbor e))).2 := by
        simp only [AllSizeS1Geometry.step,if_neg (Ne.symm he),if_true]
      have Z' : read ((x e).long,(x (rightNeighbor e)).long) .right j=0 := Z
      have N' : read (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) .right j≠0 := by
        change (grant j).read (largePair B (x e,x (rightNeighbor e))).2.long≠0
        rw [←H]
        exact N
      exact req_of_win hp x e j .right Z' N'
    · have H : step x e i=x i := by
        simp only [AllSizeS1Geometry.step,if_neg E,if_neg R]
      exact (N (by unfold bit; rw [H]; exact Z)).elim

#print axioms mark_birth

local notation "run" => BStarResetSchedule.run step

def Continuous (x : X) (i : Fin n) (j : Fin 3) (w : List (Fin n)) : Prop :=
  ∀ u v, w=u++v → bit (run x u) i j≠0

/-- The last rising grant has winning old-pair evidence and survives
each prefix of the remaining physical word. A later release followed
by reacquisition therefore cannot be mistaken for uninterrupted custody. -/
theorem continuous_or_birth (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (i : Fin n) (j : Fin 3) (w : List (Fin n))
    (H : bit (run x w) i j≠0) :
    Continuous hp x i j w ∨
    ∃ pre e suf, w=pre++e::suf ∧ bit (run x pre) i j=0 ∧
      WonAt hp (run x pre) e i j ∧ Continuous hp (step (run x pre) e) i j suf := by
  induction w generalizing x with
  | nil =>
    refine .inl ?_
    intro u v eq
    cases u with
    | nil => exact H
    | cons a u => contradiction
  | cons e w ih =>
    have HH : bit (run (step x e) w) i j≠0 := H
    rcases ih (step x e) HH with A|⟨u,f,v,E,Z,W,F⟩
    · by_cases Z : bit x i j=0
      · exact .inr ⟨[],e,w,rfl,Z,mark_birth hp x e i j (sep e) Z (A [] _ rfl),A⟩
      · refine .inl ?_
        intro u v eq
        cases u with
        | nil => exact Z
        | cons f u =>
          obtain ⟨R,E⟩ := List.cons.inj eq
          subst f
          exact A u v E
    · exact .inr ⟨e::u,f,v,congrArg (List.cons e) E,Z,W,F⟩

theorem born_after_zero (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (i : Fin n) (j : Fin 3) (w : List (Fin n))
    (Z : bit x i j=0) (H : bit (run x w) i j≠0) :
    ∃ pre e suf, w=pre++e::suf ∧ bit (run x pre) i j=0 ∧
      WonAt hp (run x pre) e i j ∧ Continuous hp (step (run x pre) e) i j suf :=
  (continuous_or_birth hp sep x i j w H).resolve_left (fun A => A [] w rfl Z)

#print axioms born_after_zero

/-- After a reset service, no marked old win at that same physical
incidence suffices to keep its cleared bit zero through the tape. -/
theorem zero_along (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (i : Fin n) (j : Fin 3) (w : List (Fin n))
    (Z : bit x i j=0)
    (none : ∀ pre e tail,w=pre++e::tail → ¬WonAt hp (run x pre) e i j) :
    bit (run x w) i j=0 := by
  apply Classical.byContradiction
  intro N
  obtain ⟨u,e,v,E,_,W,_⟩ := born_after_zero hp sep x i j w Z N
  exact none u e v E W

#print axioms zero_along
end L4.BStarGrantBirth
