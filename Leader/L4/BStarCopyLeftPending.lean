import Leader.L4.BStarCopyLeftReleaseOrder

namespace L4.BStarCopyLeftPending
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyLeftStrip BStarCopyLeftReleaseOrder BStarCopyMarkedLedger
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarCopyRightStrip (addr)
open BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Final K5 at ordinal zero fixes the exact entire descending tour. -/
theorem affine_chart {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (a : Fin n) (seam width end5 : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (last : end5<len) (atLast : S.getD end5 fall=(addr a 0,5)) :
    ∀ i<seam, i≤end5 ∧ S.getD (end5-i) fall=(addr a i,5) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨Nat.zero_le _,by simpa using atLast⟩
  | succ i ih =>
    intro hi
    obtain ⟨le,old⟩ := ih (by omega)
    obtain ⟨k,kl,ptr⟩ := k5_ordinal hp C a seam width (i+1) strip root hi
    have ⟨_,H⟩ := k5_chart_successor hp C a seam width i k strip hi (by omega) ptr
    have lenS := C.length
    have E : k+1=end5-i := (List.getD_inj (by omega) (by omega) C.nodup).mp (H.trans old.symm)
    have M : end5-(i+1)=k := by omega
    exact ⟨by omega,M.symm ▸ ptr⟩

/-- Number of original inside source digits still unvisited at the old
PC10 cursor. All OUT addresses, foreign waits and returns cost zero. -/
def remaining (end5 width : Nat) : Cursor → Nat
  | .out k => min width (end5+1-k)
  | .back _ => 0

def pending {Tag : Type} (atDigit : Nat→Tag) (m : Nat) : List Tag :=
  (List.range m).reverse.map atDigit

theorem pending_succ {Tag : Type} (atDigit : Nat→Tag) (i : Nat) :
    pending atDigit (i+1)=atDigit i::pending atDigit i := by
  simp [pending,List.range_succ]

theorem remaining_forward (end5 width k : Nat) :
    (∃ i, i<width ∧ i≤end5 ∧ k=end5-i ∧
      remaining end5 width (.out k)=i+1 ∧ remaining end5 width (.out (k+1))=i) ∨
    remaining end5 width (.out (k+1))=remaining end5 width (.out k) := by
  simp only [remaining]
  by_cases H : k≤end5 ∧ end5-k<width
  · left
    refine ⟨end5-k,H.2,by omega,by omega,?_,?_⟩
    · rw [Nat.min_eq_right (by omega)]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  · right
    by_cases G : end5<k
    · rw [show end5+1-(k+1)=0 by omega,show end5+1-k=0 by omega]
    · rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]

theorem remaining_at_actual_k5 (end5 width i : Nat) (H : i<width) (K : i≤end5) :
    remaining end5 width (.out (end5-i))=i+1 ∧
      remaining end5 width (.out (end5-i+1))=i := by
  simp only [remaining]
  constructor <;> rw [Nat.min_eq_right (by omega)] <;> omega

/-- For a proper complete LOAD/ENABLE start, this identifies the
exact plan remaining term at the old source and its literal tail
after consuming that source. No per-visit data identities enter. -/
theorem release_pending {Tag : Type} (atDigit : Nat→Tag) (end5 width i : Nat)
    (H : i<width) (K : i≤end5) :
    pending atDigit (remaining end5 width (.out (end5-i)))=
      atDigit i::pending atDigit (remaining end5 width (.out (end5-i+1))) := by
  obtain ⟨A,B0⟩ := remaining_at_actual_k5 end5 width i H K
  rw [A,B0,pending_succ]

end L4.BStarCopyLeftPending
