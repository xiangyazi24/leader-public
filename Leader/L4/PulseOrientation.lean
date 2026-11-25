import Lean

namespace L4.PulseOrientation

variable {B k n : Nat} {S : Type}

abbrev Word (n B : Nat) := Fin B → Fin n

/-- The key of a recoded tape records its completion skeleton. A warm
credit supplies a deterministic, distinct list of 2J starting slots
from that key; each slot's two literal labels are distinguishable. -/
structure Model (n B k : Nat) (S : Type) where
  key : Word n B → S
  start : S → Fin k → Fin B
  side : S → Fin k → Bool → Fin n
  start_inj : ∀ z, Function.Injective (start z)
  side_inj : ∀ z i, Function.Injective (side z i)

noncomputable def overwrite (M : Model n B k S) (w : Word n B) (bits : Fin k → Bool) : Word n B := by
  classical
  exact fun j => if H : ∃ i,M.start (M.key w) i=j then
    M.side (M.key w) (Classical.choose H) (bits (Classical.choose H)) else w j

theorem overwrite_hit (M : Model n B k S) (w : Word n B) (bits : Fin k→Bool) (i : Fin k) :
    overwrite M w bits (M.start (M.key w) i)=M.side (M.key w) i (bits i) := by
  classical
  unfold overwrite
  have H : ∃ j,M.start (M.key w) j=M.start (M.key w) i := ⟨i,rfl⟩
  rw [dif_pos H,M.start_inj _ (Classical.choose_spec H)]

theorem overwrite_off (M : Model n B k S) (w : Word n B) (bits : Fin k→Bool)
    (j : Fin B) (H : ∀ i,M.start (M.key w) i≠j) :
    overwrite M w bits j=w j := by
  classical
  unfold overwrite
  rw [dif_neg (fun A=>let ⟨i,E⟩:=A; H i E)]

/-- Inputs carry the old outgoing-first orientations; gap/packet
projection must prove that overwriting cannot alter the skeleton
extracting their selected starts. No distributional premise. -/
def Original (M : Model n B k S) (w : Word n B) : Prop :=
  ∀ i,w (M.start (M.key w) i)=M.side (M.key w) i true

theorem inject_overwrite (M : Model n B k S)
    (A : Word n B→Prop)
    (orig : ∀ w,A w→Original M w)
    (stable : ∀ w,A w→∀ bits,M.key (overwrite M w bits)=M.key w) :
    Function.Injective (fun z : {w // A w} × (Fin k→Bool) =>
      overwrite M z.1.val z.2) := by
  classical
  rintro ⟨⟨w,H⟩,bits⟩ ⟨⟨v,I⟩,other⟩ Eq
  have E : M.key w=M.key v :=
    (stable w H bits).symm.trans ((congrArg M.key Eq).trans (stable v I other))
  have P : bits=other := by
    funext i
    apply M.side_inj (M.key w) i
    have K := congrFun Eq (M.start (M.key w) i)
    change overwrite M w bits (M.start (M.key w) i)=
      overwrite M v other (M.start (M.key w) i) at K
    rw [overwrite_hit,show M.start (M.key w) i=M.start (M.key v) i from congrArg (fun z=>M.start z i) E,
      overwrite_hit,←E] at K
    exact K
  have V : w=v := by
    funext j
    by_cases J : ∃ i,M.start (M.key w) i=j
    · obtain ⟨i,K⟩ := J
      rw [←K,orig w H i,E,orig v I i]
    · have R : ∀ i,M.start (M.key w) i≠j := fun i K=>J ⟨i,K⟩
      have T : ∀ i,M.start (M.key v) i≠j := by rw [←E]; exact R
      have K := congrFun Eq j
      change overwrite M w bits j=overwrite M v other j at K
      rwa [overwrite_off M w bits j R,overwrite_off M v other j T] at K
  exact Prod.ext (Subtype.ext V) P

/-- Same skeleton, and neither pinned completion is a start of a
selected round. Thus the injection lands in the two-pinned words. -/
theorem into_pinned (M : Model n B k S) (A : Word n B→Prop)
    (p q : Fin B) (u v : Fin n)
    (orig : ∀ w,A w→Original M w)
    (stable : ∀ w,A w→∀ bits,M.key (overwrite M w bits)=M.key w)
    (pins : ∀ w,A w→w p=u ∧ w q=v)
    (avoid : ∀ w,A w→∀ i,M.start (M.key w) i≠p ∧ M.start (M.key w) i≠q) :
    ∃ f : ({w // A w} × (Fin k→Bool)) → {w : Word n B // w p=u ∧ w q=v},
      Function.Injective f := by
  refine ⟨fun z=>⟨overwrite M z.1.val z.2,?_,?_⟩,?_⟩
  · rw [overwrite_off M _ _ _ (fun i=>(avoid _ z.1.property i).1)]
    exact (pins _ z.1.property).1
  · rw [overwrite_off M _ _ _ (fun i=>(avoid _ z.1.property i).2)]
    exact (pins _ z.1.property).2
  · intro a b H
    exact inject_overwrite M A orig stable (congrArg Subtype.val H)

#print axioms inject_overwrite
#print axioms into_pinned
end L4.PulseOrientation
