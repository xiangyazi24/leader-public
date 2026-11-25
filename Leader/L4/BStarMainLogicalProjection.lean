import Leader.L4.BStarWarmupMainCoverage

namespace L4.BStarMainLogicalProjection
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarWarmupKeys BStarWarmupReceiptChoice BStarWarmupMainCoverage
open BStarPhysicalLiftAlignment BStarEpochLift

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n m Q : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def logicalKey (hm : 0<m) (physical : Fin m→Fin n) (opening : Nat)
    (j : Fin (Q*m)) : Key n :=
  (physical ⟨j.val%m,Nat.mod_lt _ hm⟩, opening+32*(j.val/m)+1)

theorem logicalKey_injective (hm : 0<m) (physical : Fin m→Fin n)
    (phys : Function.Injective physical) (opening : Nat) :
    Function.Injective (logicalKey (Q:=Q) hm physical opening) := by
  intro a b same
  have H := congrArg Prod.fst same
  have I := congrArg Fin.val (phys H)
  change a.val%m=b.val%m at I
  have J := congrArg Prod.snd same
  change opening+32*(a.val/m)+1=opening+32*(b.val/m)+1 at J
  have quot : a.val/m=b.val/m := by omega
  have E := Nat.mod_add_div a.val m
  rw [I,quot,Nat.mod_add_div] at E
  exact Fin.ext E.symm

/-- Embed exactly the round-major logical BIT keys in the main
coordinates. This requires no physical reveal at unused coordinates. -/
theorem logical_projection (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (lo opening cap G : Nat)
    (upper : ∀ i,traceCount hp base initial hh start history i≤G)
    (align : frontier G≤opening) (phase : opening%32=0) (room : opening+32*Q≤cap)
    (hm : 0<m) (physical : Fin m→Fin n) (phys : Function.Injective physical) :
    let reserve := reserveMap hp base initial hh start history
    ∃ f : Fin (Q*m)→Fin (keys reserve opening cap).length,
      Function.Injective f ∧ ∀ j,
      sumCoordinate reserve lo opening cap (logicalKey hm physical opening j)=
        some ((f j).natAdd (keys reserve lo opening).length) := by
  classical
  dsimp only
  let reserve := reserveMap hp base initial hh start history
  have there (j : Fin (Q*m)) :
      ∃ a : Fin (keys reserve opening cap).length,
      sumCoordinate reserve lo opening cap (logicalKey hm physical opening j)=
        some (a.natAdd (keys reserve lo opening).length) := by
    have round : j.val/m<Q := (Nat.div_lt_iff_lt_mul hm).mpr j.isLt
    have phase1 : (opening+32*(j.val/m)+1)%32=1 := by
      rw [Nat.add_mod,Nat.add_mod opening,phase]
      simp
    exact main_coordinate hp base initial hh start history _ _ lo opening cap G (upper _) align
      (by omega) (by omega) phase1
  let f := fun j=>Classical.choose (there j)
  have I (j : Fin (Q*m)) := Classical.choose_spec (there j)
  refine ⟨f,?_,I⟩
  intro a b E
  apply logicalKey_injective hm physical phys opening
  exact ((sum_fiber reserve lo opening cap _ _).mp (I a)).trans
    (((sum_fiber reserve lo opening cap _ _).mp (I b)).symm ▸
      congrArg (fun j=>sumKey reserve lo opening cap (j.natAdd (keys reserve lo opening).length)) E)

#print axioms logical_projection
end L4.BStarMainLogicalProjection
