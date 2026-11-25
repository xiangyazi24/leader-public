import Leader.L4.RankSupplier

/-! Cumulative-cut formulation of FIFO matching. Slot zero is the source;
the sink is at width, and slots used by the comparison are 1 through width−1. -/
namespace L4.FIFOCompare

/-- Number of occupied slots from k through width−1. -/
def tailSlots (width : Nat) (stock : Nat → Bool) (k : Nat) : Nat :=
  if k < width then (stock k).toNat + tailSlots width stock (k+1) else 0
termination_by width-k
decreasing_by omega

/-- Number of ordinals that have already crossed a cut; departed particles
are counted at all cuts, even when the real absorbing head is earlier. -/
def cuts (width : Nat) (stock : Nat → Bool) (departed k : Nat) : Nat :=
  departed + tailSlots width stock k

theorem cuts_far (width : Nat) (stock : Nat → Bool) (dep k : Nat) (h : width ≤ k) :
    cuts width stock dep k = dep := by
  unfold cuts
  rw [tailSlots,if_neg (by omega : ¬ k<width),Nat.add_zero]

theorem cuts_adjacent (width : Nat) (stock : Nat → Bool) (dep k : Nat) (h : k < width) :
    cuts width stock dep k = (stock k).toNat + cuts width stock dep (k+1) := by
  unfold cuts
  rw [tailSlots,if_pos h]
  omega

theorem cuts_adjacent_all (width : Nat) (stock : Nat → Bool) (dep k : Nat) :
    cuts width stock dep k =
      (if k < width then (stock k).toNat else 0) + cuts width stock dep (k+1) := by
  by_cases hh : k < width
  · rw [if_pos hh,cuts_adjacent _ _ _ _ hh]
  · rw [if_neg hh,cuts_far _ _ _ _ (by omega),cuts_far _ _ _ _ (by omega),Nat.zero_add]

/-- Setting one empty/occupied slot changes exactly the cuts at or below
its coordinate. This handles raw width and does not presume a moving head. -/
def setStock (stock : Nat → Bool) (j : Nat) (b : Bool) : Nat → Bool :=
  fun k => if k = j then b else stock k

theorem tailSlots_set (width : Nat) (stock : Nat → Bool) (j : Nat) (b : Bool) (k : Nat) :
    tailSlots width (setStock stock j b) k +
      (if k ≤ j ∧ j < width then (stock j).toNat else 0) =
    tailSlots width stock k + (if k ≤ j ∧ j < width then b.toNat else 0) := by
  rw [tailSlots.eq_1 width (setStock stock j b) k,tailSlots.eq_1 width stock k]
  by_cases hw : k<width
  · rw [if_pos hw,if_pos hw]
    have ih := tailSlots_set width stock j b (k+1)
    by_cases he : k = j
    · subst j
      simp [setStock,hw,show ¬ k+1 ≤ k by omega] at ih ⊢
      omega
    · have hh : (k ≤ j ∧ j < width) ↔ (k+1 ≤ j ∧ j < width) := by omega
      simp only [hh]
      simp [setStock,he]
      omega
  · rw [if_neg hw,if_neg hw]
    simp [show ¬ (k ≤ j ∧ j < width) by omega]
termination_by width-k
decreasing_by omega

theorem cuts_set (width : Nat) (stock : Nat → Bool) (dep j : Nat) (b : Bool) (k : Nat) :
    cuts width (setStock stock j b) dep k + (if k ≤ j ∧ j < width then (stock j).toNat else 0) =
      cuts width stock dep k + (if k ≤ j ∧ j < width then b.toNat else 0) := by
  have h := tailSlots_set width stock j b k
  unfold cuts
  omega

theorem cuts_inject (width : Nat) (stock : Nat → Bool) (dep j : Nat)
    (h : stock j = false) (hj : j < width) (k : Nat) :
    cuts width (setStock stock j true) dep k = cuts width stock dep k + (if k ≤ j then 1 else 0) := by
  simpa [h,hj] using cuts_set width stock dep j true k

theorem cuts_move (width : Nat) (stock : Nat → Bool) (dep j : Nat)
    (h : stock j = true) (hv : stock (j+1) = false) (hj : j+1 < width) (k : Nat) :
    cuts width (setStock (setStock stock j false) (j+1) true) dep k =
      cuts width stock dep k + (if k = j+1 then 1 else 0) := by
  have h₁ := cuts_set width stock dep j false k
  have h₂ := cuts_inject width (setStock stock j false) dep (j+1)
    (by simp [setStock,hv]) hj k
  simp only [h, show j < width by omega, and_true,
    Bool.toNat_true,Bool.toNat_false] at h₁
  by_cases hk : k ≤ j
  · have hk' : k ≤ j+1 := by omega
    have hk'' : k ≠ j+1 := by omega
    simp [hk,hk',hk''] at h₁ h₂ ⊢
    omega
  · by_cases he : k = j+1
    · subst k; simp [hk] at h₁ h₂ ⊢; omega
    · have he' : ¬ k ≤ j+1 := by omega
      simp [hk,he,he'] at h₁ h₂ ⊢
      omega

theorem cuts_absorb (width : Nat) (stock : Nat → Bool) (dep j : Nat)
    (h : stock j = true) (hj : j < width) (k : Nat) :
    cuts width (setStock stock j false) (dep+1) k =
      cuts width stock dep k + (if j < k then 1 else 0) := by
  have h₁ := cuts_set width stock dep j false k
  simp only [h,hj,and_true,Bool.toNat_true,Bool.toNat_false] at h₁
  unfold cuts at h₁ ⊢
  by_cases hk : k ≤ j
  · simp [hk,show ¬ j<k by omega] at h₁ ⊢; omega
  · simp [hk,show j<k by omega] at h₁ ⊢; omega

/-- In particular, an outlet at the last usable cell changes exactly
cut width among the cuts from 1 through width. -/
theorem cuts_outlet (width : Nat) (stock : Nat → Bool) (dep j : Nat)
    (h : stock j = true) (hj : j+1=width) (k : Nat) (hk : k ≤ width) :
    cuts width (setStock stock j false) (dep+1) k =
      cuts width stock dep k + (if k=width then 1 else 0) := by
  rw [cuts_absorb _ _ _ _ h (by omega)]
  by_cases h' : k=width <;> simp [h',show j<k ↔ k=width by omega,show j<width by omega]

end L4.FIFOCompare

namespace L4.FIFOCompare

/-- For every physical service real cumulative crossings are monotone.
On the unpaused nominated entrance or next vacant slot, the tracked
particle crosses that cut (or has instead been consumed at the head). -/
structure RealStep (width i : Nat) (r : Nat → Bool) (R R' : Nat → Nat) : Prop where
  monotone : ∀ k, 0 < k → k ≤ width → R k ≤ R' k
  source : i = 0 → r 1 = false → R 1 + 1 ≤ R' 1
  crossing : 0 < i → i < width → r i = true → r (i+1) = false →
    R (i+1)+1 ≤ R' (i+1)

/-- Precise changes in the fixed virtual queue on a single selected bond. -/
inductive VirtualDelta (width i : Nat) (s : Nat → Bool) (V V' : Nat → Nat) : Prop
  | idle (eq : ∀ k, 0 < k → k ≤ width → V' k = V k)
  | inject (hz : i = 0) (vacant : s 1 = false)
      (eq : ∀ k, 0 < k → k ≤ width → V' k = V k + if k=1 then 1 else 0)
  | move (hi : 0 < i) (hW : i+1 < width) (donor : s i = true) (vacant : s (i+1) = false)
      (eq : ∀ k, 0 < k → k ≤ width → V' k = V k + if k=i+1 then 1 else 0)
  | outlet (hi : 0 < i) (hW : i+1 = width) (donor : s i = true)
      (eq : ∀ k, 0 < k → k ≤ width → V' k = V k + if k=i+1 then 1 else 0)

/-- FIFO comparison from adjacent cut constraints. If the real count
at the virtual crossing is already greater, the virtual move consumes
one slack unit. At equality the neighboring cuts force the resulting
real vacancy and, except at source, a real donor. No independence or
relationship between raw labels on different marks is assumed. -/
theorem compare_single_step (width i : Nat) (hw : 2 ≤ width)
    (r s : Nat → Bool) (dr ds : Nat) (R' V' : Nat → Nat)
    (hV : VirtualDelta width i s (cuts width s ds) V')
    (hR : RealStep width i r (cuts width r dr) R')
    (hrOut : r width = false)
    (hOld : ∀ k, 0 < k → k ≤ width → cuts width s ds k ≤ cuts width r dr k) :
    ∀ k, 0 < k → k ≤ width → V' k ≤ R' k := by
  let V := cuts width s ds
  let R := cuts width r dr
  have hRmono (k : Nat) (hk : 0<k) (hkw : k≤width) : R k ≤ R' k := hR.monotone k hk hkw
  have hle (k : Nat) (hk : 0<k) (hkw : k≤width) : V k ≤ R k := hOld k hk hkw
  have hVac (j : Nat) (hj : 0<j) (hW : j<width) (hs : s j = false)
      (eq : R j = V j) : r j = false := by
    have h1 := cuts_adjacent width r dr j hW
    have h2 := cuts_adjacent width s ds j hW
    change R j = (r j).toNat + R (j+1) at h1
    change V j = (s j).toNat + V (j+1) at h2
    have hh := hle (j+1) (by omega) (by omega)
    rw [hs] at h2
    cases h : r j
    · rfl
    · rw [h] at h1
      change R j = 1 + R (j+1) at h1
      change V j = 0 + V (j+1) at h2
      omega
  have hDonor (j : Nat) (hj : 0<j) (hW : j<width) (hs : s j = true)
      (eq : R (j+1) = V (j+1)) : r j = true := by
    have h1 := cuts_adjacent width r dr j hW
    have h2 := cuts_adjacent width s ds j hW
    change R j = (r j).toNat + R (j+1) at h1
    change V j = (s j).toNat + V (j+1) at h2
    have hh := hle j hj (by omega)
    rw [hs] at h2
    cases h : r j
    · rw [h] at h1
      change R j = 0 + R (j+1) at h1
      change V j = 1 + V (j+1) at h2
      omega
    · rfl
  have bump (j : Nat) (hj : 0<j) (hW : j≤width)
      (hc : R j = V j → R j+1 ≤ R' j) :
      ∀ k, 0<k → k≤width → V k + (if k=j then 1 else 0) ≤ R' k := by
    intro k hk hkw
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl]
      by_cases he : R j = V j
      · have hh := hc he
        omega
      · have hA := hle j hj hW
        have hB := hRmono j hj hW
        omega
    · rw [if_neg hkj,Nat.add_zero]
      exact Nat.le_trans (hle k hk hkw) (hRmono k hk hkw)
  intro k hk hkw
  cases hV with
  | idle eq => rw [eq k hk hkw]; exact Nat.le_trans (hle k hk hkw) (hRmono k hk hkw)
  | inject hz hS eq =>
    rw [eq k hk hkw]
    exact bump 1 (by omega) (by omega) (fun h => hR.source hz (hVac 1 (by omega) (by omega) hS h)) k hk hkw
  | move hi hW hS hv eq =>
    rw [eq k hk hkw]
    exact bump (i+1) (by omega) (by omega)
      (fun h => hR.crossing hi (by omega) (hDonor i hi (by omega) hS h)
        (hVac (i+1) (by omega) hW hv h)) k hk hkw
  | outlet hi hW hS eq =>
    rw [eq k hk hkw]
    exact bump (i+1) (by omega) (by omega)
      (fun h => hR.crossing hi (by omega) (hDonor i hi (by omega) hS h) (hW ▸ hrOut)) k hk hkw

/-- Paused comparisons keep the same virtual queue, while real ordinal
crossings may increase: outside activity need not be frozen. -/
theorem compare_paused (width : Nat) (R R' V : Nat → Nat)
    (hR : ∀ k, 0<k → k≤width → R k ≤ R' k)
    (hV : ∀ k, 0<k → k≤width → V k ≤ R k) :
    ∀ k, 0<k → k≤width → V k ≤ R' k :=
  fun k hk hW => Nat.le_trans (hV k hk hW) (hR k hk hW)

/-- At the final cut only departed ordinals count on either side. -/
theorem departures_le (width : Nat) (hW : 0<width)
    (r s : Nat → Bool) (actual virtual : Nat)
    (h : ∀ k, 0 < k → k ≤ width → cuts width s virtual k ≤ cuts width r actual k) :
    virtual ≤ actual := by
  have hh := h width hW (Nat.le_refl _)
  simpa [cuts_far width _ _ width (Nat.le_refl _)] using hh

end L4.FIFOCompare

#print axioms L4.FIFOCompare.compare_single_step
#print axioms L4.FIFOCompare.departures_le

namespace L4.FIFOCompare
open RankSupplier

/-- Finite stock array extended by false outside its physical coordinates. -/
def asNatStock {n : Nat} (s : Fin n → Bool) (k : Nat) : Bool :=
  if h : k<n then s ⟨k,h⟩ else false

theorem asNatStock_val {n : Nat} (s : Fin n → Bool) (i : Fin n) :
    asNatStock s i.val = s i := by
  simp [asNatStock,i.isLt]

theorem asNatStock_set {n : Nat} (s : Fin n → Bool) (j : Fin n) (b : Bool) :
    asNatStock (fun r => if r=j then b else s r) = setStock (asNatStock s) j.val b := by
  funext k
  by_cases hk : k<n
  · by_cases he : k=j.val
    · subst k; simp [setStock,asNatStock,j.isLt]
    · have hf : (⟨k,hk⟩ : Fin n) ≠ j := fun hh => he (congrArg Fin.val hh)
      simp [asNatStock,hk,hf,setStock,he]
  · have hf : k ≠ j.val := by have := j.isLt; omega
    simp [asNatStock,hk,setStock,hf]

theorem setStock_same (s : Nat → Bool) (j : Nat) :
    setStock s j (s j) = s := by
  funext k
  by_cases h : k=j <;> simp [setStock,h]

theorem setStock_comm (s : Nat → Bool) (i j : Nat) (b c : Bool) (h : i ≠ j) :
    setStock (setStock s i b) j c = setStock (setStock s j c) i b := by
  funext k
  by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [setStock]

private theorem find_lifted {n : Nat} (v i : Fin n) :
    ((List.finRange n).find? (fun r => liftedSite v r.val == liftedSite v i.val)) = some i := by
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp,i.val,by simp,?_,?_⟩
  · simp
  · intro j hj
    simp only [List.getElem_finRange,Fin.val_cast]
    change (!(liftedSite v j == liftedSite v i.val)) = true
    have hNe : liftedSite v j ≠ liftedSite v i.val := by
      intro h
      have hEq := liftedSite_inj v (by omega : j<n) i.isLt h
      omega
    simp [hNe]

/-- The virtual delta is an exact characterization of the virtual
transition on its actual raw mark, not a replacement queue. -/
theorem literal_virtual_delta {n : Nat} (hn : 4 ≤ n) (v i : Fin n) (q : Virtual n) :
    VirtualDelta (n-1) i.val (asNatStock q.stock)
      (cuts (n-1) (asNatStock q.stock) q.departures)
      (cuts (n-1) (asNatStock (virtualStep v q (liftedSite v i.val)).stock)
        (virtualStep v q (liftedSite v i.val)).departures) := by
  unfold virtualStep
  rw [find_lifted]
  dsimp only
  by_cases hi : i.val+1<n
  · rw [dif_pos hi]
    let j : Fin n := ⟨i.val+1,hi⟩
    by_cases hz : i.val=0
    · simp only [if_pos hz]
      have hj : j.val=1 := by simp [j,hz]
      have hW : j.val<n-1 := by omega
      change VirtualDelta _ _ _ _
        (cuts (n-1) (asNatStock (fun r => if r=j then true else q.stock r)) q.departures)
      rw [asNatStock_set]
      cases hs : q.stock j
      · have hS : asNatStock q.stock 1 = false := by rwa [← hj,asNatStock_val]
        refine .inject hz hS (fun k hk hkw => ?_)
        rw [cuts_inject _ _ _ _ (by rwa [asNatStock_val]) hW]
        simp [hj,show k≤1 ↔ k=1 by omega]
      · rw [show true = asNatStock q.stock j.val by rw [asNatStock_val,hs],setStock_same]
        exact .idle (fun _ _ _ => rfl)
    · simp only [if_neg hz]
      cases hs : q.stock i
      · exact .idle (fun _ _ _ => rfl)
      · simp only [Bool.not_true,Bool.false_eq_true,if_false]
        by_cases ho : j.val+1=n
        · have ho' : i.val+1=n-1 := by have hj : j.val=i.val+1 := rfl; omega
          have ho'': (⟨i.val+1,hi⟩ : Fin n).val+1 = n := ho
          rw [if_pos ho'']
          dsimp only
          rw [asNatStock_set]
          refine .outlet (by omega) ho' (by rwa [asNatStock_val]) (fun k hk hkw => ?_)
          rw [cuts_outlet _ _ _ _ (by rwa [asNatStock_val]) ho' k hkw]
          rw [ho']
        · have hW : i.val+1 < n-1 := by have hj : j.val=i.val+1 := rfl; omega
          have ho' : (⟨i.val+1,hi⟩ : Fin n).val+1 ≠ n := ho
          rw [if_neg ho']
          cases hc : q.stock j
          · have hj : (⟨i.val+1,hi⟩ : Fin n) = j := rfl
            rw [hj]
            simp only [Bool.false_eq_true,if_false]
            rw [asNatStock_set,asNatStock_set]
            have hnij : i.val ≠ j.val := by have hj : j.val=i.val+1 := rfl; omega
            rw [setStock_comm _ _ _ _ _ hnij.symm]
            refine .move (by omega) hW (by rwa [asNatStock_val]) (by
              change asNatStock q.stock j.val = false; rwa [asNatStock_val]) (fun k hk hw => ?_)
            exact cuts_move _ _ _ _ (by rwa [asNatStock_val])
              (by change asNatStock q.stock j.val = false; rwa [asNatStock_val]) hW k
          · exact .idle (fun _ _ _ => rfl)
  · rw [dif_neg hi]
    exact .idle (fun _ _ _ => rfl)

end L4.FIFOCompare

#print axioms L4.FIFOCompare.literal_virtual_delta

namespace L4.FIFOCompare
open RankSupplier

/-- The initial physical strict corridor and the exact virtual initial
array have the same stock at every usable slot. -/
theorem pointwise_cuts_of_realStep {p c n : Nat} (hn : 4 ≤ n)
    (v : Fin n) (s₀ : Obs p c n) (hStart : Live v s₀)
    (real : Obs p c n → Nat → Bool)
    (hInit : real s₀ = asNatStock (virtualInit v s₀).stock)
    (hOut : ∀ s, Live v s → real s (n-1) = false)
    (hReal : ∀ (s : Obs p c n) (i : Fin n), Live v s → s₀.donor ≤ s.donor →
      (advance v s (liftedSite v i.val)).stopped = false →
      RealStep (n-1) i.val (real s) (cuts (n-1) (real s) (s.donor-s₀.donor))
        (cuts (n-1) (real (advance v s (liftedSite v i.val)))
          ((advance v s (liftedSite v i.val)).donor-s₀.donor))) :
    ∀ w, (track v s₀ w).stopped = false → ∀ k, 0<k → k≤n-1 →
      cuts (n-1) (asNatStock (GGTiming.runMarks (virtualStep v) (virtualInit v s₀) w).stock)
        (GGTiming.runMarks (virtualStep v) (virtualInit v s₀) w).departures k ≤
      cuts (n-1) (real (track v s₀ w)) ((track v s₀ w).donor-s₀.donor) k := by
  have coupled (w : List (Fin n)) (s : Obs p c n) (q : Virtual n)
      (hs : Live v s) (hLag : s₀.donor ≤ s.donor)
      (hD : ∀ k, 0<k → k≤n-1 →
        cuts (n-1) (asNatStock q.stock) q.departures k ≤ cuts (n-1) (real s) (s.donor-s₀.donor) k)
      (hLive : (track v s w).stopped = false) :
      ∀ k, 0<k → k≤n-1 →
        cuts (n-1) (asNatStock (GGTiming.runMarks (virtualStep v) q w).stock)
          (GGTiming.runMarks (virtualStep v) q w).departures k ≤
          cuts (n-1) (real (track v s w)) ((track v s w).donor-s₀.donor) k := by
    induction w generalizing s q with
    | nil => exact hD
    | cons e w ih =>
      let t := advance v s e
      have hT : t.stopped = false := by
        cases hSt : t.stopped
        · rfl
        · change (track v t w).stopped = false at hLive
          rw [stopped_stays v t w hSt,hSt] at hLive
          contradiction
      have hTLive : Live v t := live_step hn v e s hs hT
      obtain ⟨j,hj,he⟩ := liftedSite_of_site v e
      let i : Fin n := ⟨j,hj⟩
      have hei : liftedSite v i.val = e := he
      have hS := hReal s i hs hLag (hei.symm ▸ hT)
      have hV := literal_virtual_delta hn v i q
      rw [hei] at hS hV
      have hn' := compare_single_step (n-1) i.val (by omega)
        (real s) (asNatStock q.stock) (s.donor-s₀.donor) q.departures
        _ _ hV hS (hOut s hs) hD
      have htm : s₀.donor ≤ t.donor := Nat.le_trans hLag (donor_mono_step v e s)
      exact ih t (virtualStep v q e) hTLive htm hn' hLive
  intro w hw
  exact coupled w s₀ (virtualInit v s₀) hStart (Nat.le_refl _)
    (fun k _ _ => by simp [hInit,virtualInit]) hw

theorem projection_of_realStep {p c n : Nat} (hn : 4 ≤ n)
    (v : Fin n) (s₀ : Obs p c n) (hStart : Live v s₀)
    (real : Obs p c n → Nat → Bool)
    (hInit : real s₀ = asNatStock (virtualInit v s₀).stock)
    (hOut : ∀ s, Live v s → real s (n-1) = false)
    (hReal : ∀ (s : Obs p c n) (i : Fin n), Live v s → s₀.donor ≤ s.donor →
      (advance v s (liftedSite v i.val)).stopped = false →
      RealStep (n-1) i.val (real s) (cuts (n-1) (real s) (s.donor-s₀.donor))
        (cuts (n-1) (real (advance v s (liftedSite v i.val)))
          ((advance v s (liftedSite v i.val)).donor-s₀.donor))) :
    DepartureProjection v s₀
      (fun w => (GGTiming.runMarks (virtualStep v) (virtualInit v s₀) w).departures) := by
  intro w hw
  have hh := pointwise_cuts_of_realStep hn v s₀ hStart real hInit hOut hReal w hw
  exact departures_le (n-1) (by omega) _ _ _ _ hh

end L4.FIFOCompare

#print axioms L4.FIFOCompare.pointwise_cuts_of_realStep
#print axioms L4.FIFOCompare.projection_of_realStep

namespace L4.FIFOCompare
open RankSupplier

/-- Convenient projection for the physical offset-mask used by the
real lane. At both source and sink the queue resident bit is false. -/
theorem asNatStock_virtualInit {p c n : Nat}
    (v : Fin n) (s : Obs p c n) (h : Live v s) :
    asNatStock (virtualInit v s).stock =
      fun k => if 0<k ∧ k≤s.donor then (s.config (liftedSite v k)).stock else false := by
  funext k
  have hcap := h.2.2.2.2.2
  by_cases hk : k<n
  · simp [asNatStock,virtualInit,hk]
  · have hOut : ¬ (0<k ∧ k≤s.donor) := by omega
    simp [asNatStock,hk,hOut]

/-- An ordinal observed at the virtual outlet is already an actual paid
ordinal on the same raw prefix, unless the physical observer stopped.
The map is the identity on ordinal numbers, so distinct virtual
departures certify distinct paid events without selecting stock labels. -/
theorem matched_departure_ordinal {p c n : Nat}
    {v : Fin n} {s : Obs p c n} {departures : List (Fin n) → Nat}
    (h : DepartureProjection v s departures) (w : List (Fin n))
    (hLive : (track v s w).stopped = false) (j : Fin (departures w)) :
    ∃ k : Fin ((track v s w).donor-s.donor), k.val=j.val := by
  exact ⟨⟨j.val,Nat.lt_of_lt_of_le j.isLt (h w hLive)⟩,rfl⟩

end L4.FIFOCompare

#print axioms L4.FIFOCompare.asNatStock_virtualInit
#print axioms L4.FIFOCompare.matched_departure_ordinal
