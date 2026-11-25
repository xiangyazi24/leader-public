import Leader.L4.BStarNativeOffsetTrace
import Leader.L4.BStarFenceReceiverChart

namespace L4.BStarNativeOffsetSweep
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarClearanceOffset BStarFenceReceiverChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

def PrefixOK (h : Fin n→Bool) (head : Fin n) (j : Nat) (x : X) : Prop :=
  ∀ t≤j, eff h x (digitFrom head t)=min 5 t

theorem advance (h : Fin n→Bool) (head : Fin n) (j : Nat) (x : X) (e : Fin n)
    (sep : e≠rightNeighbor e) (fixed : oldH6 B x=h)
    (h0 : h head=true) (body : ∀ t,0<t → t≤j → h (digitFrom head t)=false)
    (P : PrefixOK h head j x) :
    PrefixOK h head j (step x e) ∧
      (e=digitFrom head j → h (digitFrom head (j+1))=false → PrefixOK h head (j+1) (step x e)) := by
  have kept : PrefixOK h head j (step x e) := by
    intro t upper
    cases t with
    | zero => simp [eff,digitFrom,h0]
    | succ u =>
      by_cases hit : digitFrom head (u+1)=rightNeighbor e
      · have eq : e=digitFrom head u := by
          change rightNeighbor (digitFrom head u)=rightNeighbor e at hit
          rw [←RearTrace.predecessor_right e,←RearTrace.predecessor_right (digitFrom head u),hit]
        rw [hit,responder hp h x e sep (congrFun fixed),←hit,body _ (by omega) (by omega)]
        simp only [Bool.false_eq_true,if_false,eq,P u (by omega)]
        omega
      · exact (elsewhere hp h x e _ (BStarClearanceOffsetMask.leftFrame hp x e) hit).trans
          (P (u+1) upper)
  refine ⟨kept,?_⟩
  intro H next t ht
  by_cases cut : t≤j
  · exact kept t cut
  · have T : t=j+1 := by omega
    subst t
    have S : digitFrom head (j+1)=rightNeighbor e := by rw [H]; rfl
    rw [S,responder hp h x e sep (congrFun fixed),←S,next]
    simp only [Bool.false_eq_true,if_false,H,P j (Nat.le_refl _)]
    omega

/-- Every selected mark in the supplied physical prefix may be separated
by arbitrary intervening marks. They need not only avoid the strip:
already repaired cells remain repaired on any fixed-layout mark. -/
theorem replay (h : Fin n→Bool) (head : Fin n) (bound : Nat) (x : X)
    (h0 : h head=true) (body : ∀ t,0<t → t≤bound → h (digitFrom head t)=false)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n))
    (fixed : ∀ u v,w=u++v → oldH6 B (run x u)=h)
    (visit : ((List.range bound).map (digitFrom head)).Sublist w) :
    PrefixOK h head bound (run x w) := by
  have generic : ∀ (j k : Nat) (x : X) (w : List (Fin n)), j+k≤bound →
      (∀ u v,w=u++v → oldH6 B (run x u)=h) →
      ((List.range' j k).map (digitFrom head)).Sublist w →
      PrefixOK h head j x → PrefixOK h head (j+k) (run x w) := by
    intro j k x w
    induction w generalizing j k x with
    | nil =>
      intro lim F S P
      have Z := S.length_le
      simp at Z
      simpa [Z,BStarResetSchedule.run] using P
    | cons e w ih =>
      intro lim F S P
      have Fw : ∀ u v,w=u++v→oldH6 B (run (step x e) u)=h :=
        fun u v E => F (e::u) v (congrArg (List.cons e) E)
      have cur : oldH6 B x=h := F [] (e::w) rfl
      have keep := (advance hp h head j x e (sep e) cur h0
        (fun u pos up => body u pos (by omega)) P).1
      cases k with
      | zero =>
        exact ih j 0 (step x e) (by omega) Fw (by simp) keep
      | succ k =>
        simp only [List.range'_succ,List.map_cons] at S
        cases S with
        | cons _ rest => exact ih j (k+1) (step x e) lim Fw (by simpa [List.range'_succ] using rest) keep
        | cons_cons _ rest =>
          have Q := (advance hp h head j x _ (sep _) cur h0
            (fun u pos up => body u pos (by omega)) P).2 rfl (body _ (by omega) (by omega))
          simpa [BStarResetSchedule.run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
            ih (j+1) k (step x (digitFrom head j)) (by omega) Fw rest Q
  simpa only [Nat.zero_add] using generic 0 bound x w (by simp) fixed (by simpa [List.range_eq_range'] using visit)
    (by
      intro t T
      have Z : t=0 := by omega
      subst t
      simp [eff,digitFrom,h0])

#print axioms replay
end L4.BStarNativeOffsetSweep
