import Leader.L4.BStarCopySetupFinalCut
import Leader.L4.BStarCopyCleanupOriginal

namespace L4.BStarAttemptLastCut
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarGeneratedOwner
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedBandScan BStarNativeReceiptTape BStarCopyFenceCuts

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every selected mark in this suffix sees a source PC at least the given floor. -/
def AtLeast (b : Nat) (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∀ a e t,w=a++e::t → b≤pc (play x a) i

/-- Two certified final receipt cuts on one original raw tape coincide,
even if its early failed attempts visited the same PC. -/
theorem unique {x : X} (k : Nat) (root : Fin n) (w l r ls rs : List (Fin n)) (e f : Fin n)
    (L : w=(l++[e])++ls) (R : w=(r++[f])++rs)
    (pcL : pc (play x l) root=k) (pcR : pc (play x r) root=k)
    (floorL : AtLeast hp (k+1) root (play x (l++[e])) ls)
    (floorR : AtLeast hp (k+1) root (play x (r++[f])) rs) :
    l=r ∧ e=f ∧ ls=rs := by
  have noEarlier (a b v u : List (Fin n)) (i j : Fin n)
      (W : w=(a++[i])++v) (Y : w=b++j::u)
      (pcAt : pc (play x b) root=k) (F : AtLeast hp (k+1) root (play x (a++[i])) v) :
      ¬a.length<b.length := by
    intro lt
    rcases List.append_eq_append_iff.mp (W.symm.trans Y) with ⟨q,Q,E⟩|⟨q,Q,E⟩
    · have h := F q j u E
      rw [←BStarResetSchedule.run_append step x (a++[i]) q,←Q,pcAt] at h
      omega
    · have lengths := congrArg List.length Q
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      have eq : q=[] := List.length_eq_zero_iff.mp (show q.length=0 by omega)
      subst q
      simp only [List.append_nil] at Q
      have h := F [] j u (by simpa using E.symm)
      change k+1≤pc (play x (a++[i])) root at h
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

theorem append_mark (D : X → Prop) (x : X) (u v : List (Fin n))
    (A : ∀ p e t,u=p++e::t → D (play x p))
    (B0 : ∀ p e t,v=p++e::t → D (play (play x u) p)) :
    ∀ p e t,u++v=p++e::t → D (play x p) := by
  intro p e t E
  rcases List.append_eq_append_iff.mp E with ⟨q,P,F⟩|⟨q,P,F⟩
  · rw [P,BStarResetSchedule.run_append]
    exact B0 q e t F
  · cases q with
    | nil =>
      simp only [List.append_nil] at P
      rw [←P]
      exact B0 [] e t F.symm
    | cons m q =>
      have G : e::t=m::(q++v) := F
      have E := (List.cons.inj G).1
      subst m
      exact A p e q P

end L4.BStarAttemptLastCut
