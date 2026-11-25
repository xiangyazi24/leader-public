import Leader.L4.BStarParkedSteering
import Leader.L4.BStarPaceSteeredCharge

namespace L4.BStarFiveClientBudget
open Height Classical BStarRawBlockDrift
open BStarSteeredLikelihood BStarPaceCount

def clientTotal {n : Nat} (c : Fin 5 → Word n → Nat) (v : Word n) : Nat :=
  c 0 v + c 1 v + c 2 v + c 3 v + c 4 v

/-- If each of the five owners pays for all but its first fresh
decision, the aggregate prescribed-decision overflow is below the
budget even without independence between owners or between attempts. -/
theorem overflow_of_excess {n : Nat} (t : Nat) (c : Fin 5 → Word n → Nat)
    (mass : ∀ i, wordSum (c i) t ≤ (81*2^20)*n^t)
    (paid : Word n → Nat)
    (each : ∀ v, paid v≤5+clientTotal c v) :
    8*wordSum (massInd (fun v => 5*2^32<paid v)) t ≤ n^t := by
  have M : wordSum (clientTotal c) t ≤ (5*81*2^20)*n^t := by
    unfold clientTotal
    simp only [wordSum_add_fun]
    have M0 := mass 0
    have M1 := mass 1
    have M2 := mass 2
    have M3 := mass 3
    have M4 := mass 4
    omega
  have T := five_overflow t (clientTotal c) M
  refine Nat.le_trans (Nat.mul_le_mul_left 8 (wordSum_mono _ _ (fun v=>?_ ) t)) T
  by_cases F : 5*2^32<paid v
  · have P : 2^32-1 ≤ clientTotal c v := by have H := each v; omega
    simp [massInd,F,P]
  · simp [massInd,F]

end L4.BStarFiveClientBudget
