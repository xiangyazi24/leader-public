import Leader.L4.BStarCopySetupFinalCut
import Leader.L4.BStarCopyCleanupOriginal

namespace L4.BStarCopyLastCut
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarGeneratedOwner
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedBandScan BStarNativeReceiptTape BStarCopyFenceCuts

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarCopySetupFinalCut

/-- Two certified final ACK11 cuts on one original raw tape coincide,
even if its early failed attempts visited PC11. -/
theorem unique {x : X} (root : Fin n) (w l r ls rs : List (Fin n)) (e f : Fin n)
    (L : w=(l++[e])++ls) (R : w=(r++[f])++rs)
    (pcL : pc (play x l) root=11) (pcR : pc (play x r) root=11)
    (floorL : Floor hp root (play x (l++[e])) ls)
    (floorR : Floor hp root (play x (r++[f])) rs) :
    l=r ∧ e=f ∧ ls=rs := by
  have noEarlier (a b v u : List (Fin n)) (i j : Fin n)
      (W : w=(a++[i])++v) (Y : w=b++j::u)
      (pcAt : pc (play x b) root=11) (F : Floor hp root (play x (a++[i])) v) :
      ¬a.length<b.length := by
    intro lt
    rcases List.append_eq_append_iff.mp (W.symm.trans Y) with ⟨q,Q,E⟩|⟨q,Q,E⟩
    · have h := F q j u E
      rw [←BStarResetSchedule.run_append step x (a++[i]) q,←Q,pcAt] at h
      omega
    · have k := congrArg List.length Q
      simp only [List.length_append,List.length_cons,List.length_nil] at k
      have eq : q=[] := List.length_eq_zero_iff.mp (show q.length=0 by omega)
      subst q
      simp only [List.append_nil] at Q
      have h := F [] j u (by simpa using E.symm)
      change 12≤pc (play x (a++[i])) root at h
      rw [Q,pcAt] at h
      omega
  have consL : w=l++e::ls := by rw [L,List.append_assoc]; rfl
  have consR : w=r++f::rs := by rw [R,List.append_assoc]; rfl
  have le := Nat.le_of_not_gt (noEarlier r l rs ls f e R consL pcL floorR)
  have ge := Nat.le_of_not_gt (noEarlier l r ls rs e f L consR pcR floorL)
  have E := congrArg (List.take l.length) (consL.symm.trans consR)
  rw [List.take_append_of_le_length (Nat.le_refl l.length),List.take_length,
      List.take_append_of_le_length le,List.take_of_length_le ge] at E
  subst r
  have tails : e::ls=f::rs := by simpa only [List.append_right_inj] using consL.symm.trans consR
  exact ⟨rfl,List.cons.inj tails⟩

end L4.BStarCopyLastCut
