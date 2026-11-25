import Leader.L4.BStarResetCycle
import Leader.L4.DirtyFencePrep

namespace L4.DirtyFenceOccurrence
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetChartNomination BStarResetCycle BStarResetMarkAdapter
open BStarClearanceIndexedSum BStarLongCommandData
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

theorem chart_occurrence_mono {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    {i j : Nat} (ij : i≤j) (bound : j≤len) :
    (S.getD i fall).2.val≤(S.getD j fall).2.val := by
  obtain ⟨edge,link,_⟩ := fixed_nominations hp C head cont
  have adjacent (k : Nat) (K : k<len) :
      (S.getD k fall).2.val≤(S.getD (k+1) fall).2.val := by
    obtain ⟨cc,d,hc,hd,hs,ht⟩ := link base (fun _=>rfl) k K
    exact (index_step (show Edge B base (S.getD k fall) (S.getD (k+1) fall) from
      ⟨edge (.link k),cc,d,hc,hd,hs,ht⟩)).1
  induction j with
  | zero =>
    have e : i=0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases e : i=j+1
    · subst i; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (adjacent j (by omega))

theorem fence_occurrence_ge_six (g : LongGeometry) (k : Fin 11) {a : Sheet}
    (F : fenceSheet g k=some a) : 6≤k.val := by
  by_cases ok : 6≤k.val
  · exact ok
  exfalso
  have K : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 := by omega
  rcases K with h|h|h|h|h|h <;> simp [fenceSheet,h] at F

/-- At a real FENCE chart address, every possible prep position of the
same owner is strictly earlier. This proves the geometric cutoff needed
by the no-reservation theorem; it asserts no dynamic packet frame. -/
theorem prep_before_fence {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    {j : Nat} (J : j≤len) {s : Sheet}
    (F : fenceSheet (longGeometry B (base (S.getD j fall).1)) (S.getD j fall).2=some s)
    {u : Pos n} (U : u∈S) {op : Prep} {target : Sheet}
    (P : target∈prepSites (longGeometry B (base u.1)) u.2 op) :
    distance S (S.getD j fall)<distance S u := by
  have lenS := C.length
  obtain ⟨i,hi,E⟩ := List.mem_iff_getElem.mp U
  let ip : i<S.length := hi
  change S[i]'ip=u at E
  have G := fence_occurrence_ge_six _ _ F
  have K := (DirtyFencePrep.prep_cut _ _ _ _ P).1
  have hId : S.getD i fall=u := (List.getElem_eq_getD (h:=hi) fall).symm.trans E
  have lt : i<j := by
    by_cases H : i<j
    · exact H
    have W := chart_occurrence_mono hp C head cont (by omega : j≤i) (by omega : i≤len)
    rw [hId] at W
    omega
  have jl : j<S.length := by omega
  rw [←List.getElem_eq_getD (h:=jl) fall,←E,distance_idx C.nodup jl,distance_idx C.nodup hi]
  omega

end L4.DirtyFenceOccurrence
