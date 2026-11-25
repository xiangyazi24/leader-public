import Leader.L4.BStarCycleCosetInit
import Leader.L4.BStarCycleGeometry
import Leader.L4.BStarPhysicalCoset

namespace L4.BStarPhysicalCosetStart
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarAcquireAnchors BStarH6WordChart BStarNativePortGeometry BStarNativePointwise
open BStarCycleGeometry BStarBiasedLift BStarPhysicalLegitimate
open BStarPhysicalLiftAlignment BStarPhysicalCoset L4.Compiler.Native
set_option maxRecDepth 4096

private theorem succ_int_mod (P x : Nat) (pos : 0<P) :
    (successor (2*P) x : Int)%(P:Int)=((x:Int)+1)%(P:Int) := by
  exact_mod_cast successor_mod P x pos

theorem signed_edge (P a b : Nat) (pos : 0<P) (A : Adjacent (2*P) a b) :
    ∃ d : Int, -1≤d ∧ d≤1 ∧ ((a:Int)+d)%(P:Int)=(b:Int)%(P:Int) := by
  rcases A with E|E|E
  · exact ⟨0, by decide, by decide, by simp [E]⟩
  · exact ⟨1, by decide, by decide, by rw [←succ_int_mod P a pos,E]⟩
  · refine ⟨-1, by decide, by decide, ?_⟩
    have H := (succ_int_mod P b pos).symm
    rw [E] at H
    simpa only [show (b:Int)+1+(-1)=(b:Int) by omega] using
      (show ((a:Int)+(-1))%(P:Int)=((b:Int)+1+(-1))%(P:Int) by
        rw [Int.add_emod (a:Int), Int.add_emod ((b:Int)+1), H])

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- The actual closed word cycle always supplies a coherent phase-coset
initializer at a legitimate cut, provided there are fewer words than the half-period.
There is no exact-representative or uniform-sign premise. -/
theorem physical_coset_start {base old : X} (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (small : total (oldH6 B base)<P)
    (L : ClockLegit hp base hh old) :
    ∃ time : Fin n→Nat, RepresentsCoset hp base old P time ∧ Coherent hh time := by
  classical
  let h := oldH6 B base
  have hm : 0<total h := total_pos h hh
  let tick (i : Fin (total h)) := (readRecord (r:=r) old (atIndex hh i).val).tick
  have edges (i : Fin (total h)) :
      ∃ d : Int, -1≤d ∧ d≤1 ∧ ((tick i : Int)+d)%(P:Int)=
        (tick (BStarCycleCosetInit.next i):Int)%(P:Int) := by
    change ∃ d : Int, -1≤d ∧ d≤1 ∧ ((tick i : Int)+d)%(P:Int)=
      (tick (BStarCycleGeometry.next i):Int)%(P:Int)
    unfold tick
    rw [atIndex_next]
    have H := L.2 (atIndex hh i) 2
    rw [M] at H
    exact signed_edge _ _ _ (by omega) H
  obtain ⟨u, Ru, Cu⟩ := BStarCycleCosetInit.exists_coherent _ P hm small tick edges
  let time (i : Fin n) : Nat := if hi : h i=true then u (index hh ⟨i,hi⟩) else 0
  have F (i : Header h) : time i.val=u (index hh i) :=
    dif_pos i.property
  refine ⟨time, ?_, ?_⟩
  · intro i
    refine ⟨L.1 i, ?_⟩
    rw [F]
    have H := Ru (index hh i)
    simpa [tick] using H.symm
  · intro i q
    rw [F, F]
    have cases : q=0 ∨ q=1 ∨ q=2 := by
      have C := q.isLt
      have H : q.val=0 ∨ q.val=1 ∨ q.val=2 := by omega
      exact H.imp Fin.ext (fun h=>h.imp Fin.ext Fin.ext)
    rcases cases with E|E|E
    · subst q
      have H := Cu (index hh (neighborHeader hh i 0))
      change u (index hh (neighborHeader hh i 0))≤u (BStarCycleGeometry.next (index hh (neighborHeader hh i 0)))+1 ∧
        u (BStarCycleGeometry.next (index hh (neighborHeader hh i 0)))≤u (index hh (neighborHeader hh i 0))+1 at H
      rw [next_index_left] at H
      exact ⟨H.2,H.1⟩
    · subst q
      rw [index_self]
      omega
    · subst q
      rw [index_right]
      exact Cu (index hh i)

#print axioms signed_edge
#print axioms physical_coset_start
end L4.BStarPhysicalCosetStart
