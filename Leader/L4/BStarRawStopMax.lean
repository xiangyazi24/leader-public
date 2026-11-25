import Leader.L4.BStarRawStopCut
import Leader.L4.Height.Trial

namespace L4.BStarRawStopMax
open BStarRawStopCut BStarRawStopMoment Height

def threeReady {n : Nat} (a b c : List (Fin n)→Bool) (h : List (Fin n)) : Bool :=
  (a h && b h) && c h

/-- Three monotone tests first hold together at the maximum of their
individual truncated first-hit times. In particular this remains true
if one or more tests have not yet held by the finite horizon. -/
theorem firstTime_threeReady {n : Nat} (a b c : List (Fin n)→Bool)
    (ma : ∀ h v,a h=true→a (h++v)=true)
    (mb : ∀ h v,b h=true→b (h++v)=true)
    (mc : ∀ h v,c h=true→c (h++v)=true)
    (h w : List (Fin n)) :
    firstTime (threeReady a b c) h w =
      max (firstTime a h w) (max (firstTime b h w) (firstTime c h w)) := by
  let j := max (firstTime a h w) (max (firstTime b h w) (firstTime c h w))
  let k := firstTime (threeReady a b c) h w
  have A : firstTime a h w≤j := Nat.le_max_left _ _
  have B : firstTime b h w≤j := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have C : firstTime c h w≤j := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have incl : ∀ l : Nat, threeReady a b c (h++w.take l)=true →
      firstTime a h w≤l ∧ firstTime b h w≤l ∧ firstTime c h w≤l := by
    intro l T
    obtain ⟨⟨ha,hb⟩,hc⟩ := Bool.and_eq_true_iff.mp T |>.imp_left Bool.and_eq_true_iff.mp
    exact ⟨firstTime_le a h w l ha,firstTime_le b h w l hb,firstTime_le c h w l hc⟩
  show k=j
  apply Nat.le_antisymm
  · by_cases jFull : w.length≤j
    · exact Nat.le_trans (firstTime_length _ h w) jFull
    · have jl : j<w.length := Nat.lt_of_not_ge jFull
      apply firstTime_le
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨true_after_time a ma h w j (Nat.lt_of_le_of_lt A jl) A,
         true_after_time b mb h w j (Nat.lt_of_le_of_lt B jl) B⟩,
         true_after_time c mc h w j (Nat.lt_of_le_of_lt C jl) C⟩
  · by_cases kFull : w.length≤k
    · exact Nat.le_trans (Nat.max_le.mpr ⟨firstTime_length a h w,
        Nat.max_le.mpr ⟨firstTime_length b h w,firstTime_length c h w⟩⟩) kFull
    · have monot : ∀ x y, threeReady a b c x=true→threeReady a b c (x++y)=true := by
        intro x y T
        have H := Bool.and_eq_true_iff.mp T
        have G := Bool.and_eq_true_iff.mp H.1
        exact Bool.and_eq_true_iff.mpr
          ⟨Bool.and_eq_true_iff.mpr ⟨ma x y G.1,mb x y G.2⟩,mc x y H.2⟩
      have trueK := true_after_time (threeReady a b c) monot h w k
        (Nat.lt_of_not_ge kFull) (Nat.le_refl _)
      obtain ⟨ak,bk,ck⟩ := incl k trueK
      exact Nat.max_le.mpr ⟨ak,Nat.max_le.mpr ⟨bk,ck⟩⟩

/-- The elapsed value of the adapted scanner equals the three-way
first-hit maximum on the exact same raw word. -/
theorem atStop_threeReady {n : Nat} (a b c : List (Fin n)→Bool)
    (ma : ∀ h v,a h=true→a (h++v)=true)
    (mb : ∀ h v,b h=true→b (h++v)=true)
    (mc : ∀ h v,c h=true→c (h++v)=true)
    (h w : List (Fin n)) :
    atStop (threeReady a b c) (fun _ t _=>t) h 0 w =
      max (firstTime a h w) (max (firstTime b h w) (firstTime c h w)) := by
  rw [atStop_eq_split,Nat.zero_add]
  exact firstTime_threeReady a b c ma mb mc h w

/-- Apply the factor-four stopped service estimate to a single
causal child, under the three exact monotone predecessor tests. -/
theorem child_moment {n : Nat}
    (a b c : List (Fin n)→Bool)
    (ma : ∀ h v,a h=true→a (h++v)=true)
    (mb : ∀ h v,b h=true→b (h++v)=true)
    (mc : ∀ h v,c h=true→c (h++v)=true)
    (wait : List (Fin n)→List (Fin n)→Nat) (L D : Nat) (pos : 0<L)
    (slice : ∀ h K, threeReady a b c h=true →
      wordSum (fun w=>2^(wait h w/L)) K≤2*n^K)
    (empty : ∀ h,wait h []=0)
    (child : List (Fin n)→Nat)
    (causal : ∀ w, w.length=D →
      child w≤atStop (threeReady a b c) (fun h t v=>t+wait h v) [] 0 w) :
    wordSum (fun w=>2^(child w/L)) D ≤
      4*wordSum (fun w=>2^(max (firstTime a [] w)
        (max (firstTime b [] w) (firstTime c [] w))/L)) D := by
  have left := wordSum_mono_on_length (fun w=>2^(child w/L))
    (atStop (threeReady a b c) (fun h t v=>2^((t+wait h v)/L)) [] 0) D (fun w W=>by
      have H := causal w W
      rw [atStop_eq_split] at H ⊢
      exact Nat.pow_le_pow_right (by decide : 0<2) (Nat.div_le_div_right H))
  have factor := stopped_service_moment (threeReady a b c) wait L pos slice empty D [] 0
  apply Nat.le_trans left
  apply Nat.le_trans factor
  apply Nat.mul_le_mul_left
  apply wordSum_mono
  intro w
  have E := atStop_threeReady a b c ma mb mc [] w
  rw [atStop_eq_split] at E ⊢
  rw [E]
  exact Nat.le_refl _

#print axioms child_moment

#print axioms firstTime_threeReady
#print axioms atStop_threeReady
end L4.BStarRawStopMax
