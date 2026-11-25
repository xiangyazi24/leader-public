import Leader.L4.WindowA0StockCap
import Leader.L4.WindowA0Drained

/-! Actual local exclusion rows for the paused A0 fixed-sink comparison.
The label ordering facts are separate from physical stock observations. -/
namespace L4.WindowA0FixedSink
open GGStage

/-- This is the interior A0 row, not the living-supplier injection row.
Covered unmarked service merely moves a resident byte to a vacancy. -/
theorem interior_exclusion {p c n : Nat} (hn : 4≤n) (x : Config p c n)
    (e : Fin n) (hm : MCOV x) (hM : (x e).mark=false)
    (hL : (x e).leader=false) :
    ((step x e e).stock,(step x e (rightNeighbor e)).stock) =
      if (x e).stock && !(x (rightNeighbor e)).stock then (false,true)
      else ((x e).stock,(x (rightNeighbor e)).stock) := by
  obtain ⟨hr,hv⟩ : (x (rightNeighbor e)).residue=nextResidue (x e).residue ∧
      (x (rightNeighbor e)).leader=false := by
    constructor
    · by_cases hh : (x (rightNeighbor e)).residue=nextResidue (x e).residue
      · exact hh
      · have H := hm e (.inr hh)
        rw [hM] at H
        cases H
    · apply Bool.eq_false_iff.mpr
      intro hh
      have H := hm e (.inl hh)
      rw [hM] at H
      cases H
  have hne : rightNeighbor e≠e := by
    intro h
    have H : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
    have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) H
    omega
  simpa [step,hne,payer,hL] using ordinary_pair_stock (x e) (x (rightNeighbor e)) hM hr hv

/-- At the ghost J door with an empty old-head socket, a retained paid
step consumes rather than transports the entering label. No new
untracked resident appears at the old head. The donor is stocked and hence the
actual A0 monitor is paused on this service. -/
theorem empty_old_head_j_absorbs {p c n : Nat} (hn : 4≤n) (x : Config p c n)
    (e : Fin n) (hm : (x e).mark=true)
    (hL : (x (rightNeighbor e)).leader=false)
    (hd : (x e).stock=true) (hr : (x (rightNeighbor e)).stock=false) :
    geometricPay (x e) (x (rightNeighbor e))=true ∧
      (step x e e).stock=false ∧ (step x e (rightNeighbor e)).stock=false := by
  have hp := WindowA0StockDrain.marked_ghost_stock_pays _ _ hm hL hd
  have hne : rightNeighbor e≠e := by
    intro h
    have H : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
    have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) H
    omega
  have h := GGStockPhysical.marked_stock_consumed (x e) (x (rightNeighbor e)) hm hd
  exact ⟨hp,by simpa [step] using h.1,by simpa [step,hne,hr] using h.2⟩

/-- Incoming service into I never transports upstream stock into the
retained interval, including a surviving paid I mark. -/
theorem top_no_import {p c n : Nat} (hn : 4≤n) (x : Config p c n)
    (e : Fin n) (hm : (x e).mark=true) :
    (step x e (rightNeighbor e)).stock=(x (rightNeighbor e)).stock := by
  have hne : rightNeighbor e≠e := by
    intro h
    have H : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
    have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) H
    omega
  simpa [step,hne] using RearFrontStock.marked_right_stock (x e) (x (rightNeighbor e)) hm

/-- Ordered label comparison: if a virtual token at k sees a vacancy
and its paired real token is tied at k, no real tracked token can
occupy k+1. Removed real tokens need not map to live virtual tokens;
only a surviving real blocker needs a still-live virtual counterpart. -/
theorem tied_receiver_empty {m : Nat} (virtual real : Fin m → Option Nat)
    (k : Nat) (a : Fin m) (hv : virtual a=some k) (hr : real a=some k)
    (vac : ∀ i, virtual i≠some (k+1))
    (realOrder : ∀ i j u v, i.val≤j.val → real i=some u → real j=some v → u≤v)
    (virtualOrder : ∀ i j u v, i.val<j.val → virtual i=some u → virtual j=some v → u<v)
    (ahead : ∀ i u, real i=some u → ∃ v, virtual i=some v ∧ v≤u) :
    ∀ j, real j≠some (k+1) := by
  intro j hR
  have hA : a.val<j.val := by
    by_cases hj : a.val<j.val
    · exact hj
    · have H := realOrder j a (k+1) k (by omega) hR hr
      omega
  obtain ⟨v,hv',hb⟩ := ahead j (k+1) hR
  have hLt := virtualOrder a j k v hA hv hv'
  have he : v=k+1 := by omega
  exact vac j (he ▸ hv')

#print axioms interior_exclusion
#print axioms empty_old_head_j_absorbs
#print axioms tied_receiver_empty

/-- The implemented pause is deliberately stronger than a test for an
untracked old-head resident: it tests any stock at J's incoming bond.
On an unpaused mark the ghost J cannot pay, even if its own stock bit
(which is still outside the retained interval) is true. -/
theorem unpaused_no_j_move {p c n : Nat} {z : SevenTagCharge.Ledger p c n}
    {i j k a b cTag : Fin n} {idx d : Nat}
    (h : WindowFourHeadTrace.Cut z i j k a b cTag idx d)
    (mc : MCOV z.config) (vac : (z.config j).stock=false) (e : Fin n) :
    ¬WindowFourHeadTrace.moves z e j := by
  rintro ⟨he,hp⟩
  subst e
  have hL := h.nonliving mc j ⟨idx, Nat.le_of_lt h.wBefore,h.wLift⟩
  have hz := RearTrace.geometricPay_ready _ _ hp
  simp [payer,hL,vac] at hz

/-- A virtual move onto k+1 never breaks pointwise lead at another
label. If its real counterpart is still present, either it was already
strictly ahead or the literal tied service must move or remove it.
This packages the nonpositive case without requiring an after-state
constraint for labels already removed by the real observer. -/
theorem progress_at_requested_label {m : Nat} (virtual real : Fin m → Option Nat)
    (a : Fin m) (k : Nat)
    (hAhead : ∀ i u, real i=some u → ∃ v, virtual i=some v ∧ v≤u)
    (hV : virtual a=some k)
    (real' : Fin m → Option Nat)
    (moved : ∀ i u, real' i=some u → ∃ old, real i=some old ∧ old≤u)
    (tied : real a=some k → ∀ u, real' a=some u → k+1≤u) :
    ∀ i u, real' i=some u →
      ∃ v, (if i=a then some (k+1) else virtual i)=some v ∧ v≤u := by
  intro i u hu
  obtain ⟨v,hv,hvu⟩ := moved i u hu
  by_cases he : i=a
  · subst i
    refine ⟨k+1, by simp, ?_⟩
    obtain ⟨vv,hvv,hle⟩ := hAhead a v hv
    rw [hV] at hvv
    have hh := Option.some.inj hvv
    by_cases hEq : v=k
    · exact tied (by simpa [hEq] using hv) u hu
    · omega
  · obtain ⟨vv,hvv,hle⟩ := hAhead i v hv
    exact ⟨vv,by simpa [he] using hvv, Nat.le_trans hle hvu⟩

#print axioms unpaused_no_j_move
#print axioms progress_at_requested_label

/-- Fixed-sink dependency commit for the non-injecting stock-height
proof. Cut 0 holds all P original bytes. On an unpaused mark there is
no tracked byte at the last fixed buffer: if J is at the fixed
boundary, its incoming buffer is empty; if J is earlier the buffer
is already outside the real support. -/
theorem closed_cut_commit (m P i k spent : Nat) (s : Nat → Bool)
    (hi : i≤m) (hk : 0<k) (hP : k≤P)
    (source : P ≤ FIFOCompare.cuts (m+1) s spent 1)
    (sink : s m=false)
    (left : 0<i → k≤FIFOCompare.cuts (m+1) s spent (i-1+1))
    (right : i<m → k-1≤FIFOCompare.cuts (m+1) s spent (i+1+1))
    (H : Nat)
    (mono : FIFOCompare.cuts (m+1) s spent (i+1)≤H)
    (move : 0<i → i<m → s i=true → s (i+1)=false →
      FIFOCompare.cuts (m+1) s spent (i+1)+1≤H) :
    k≤H := by
  let C := FIFOCompare.cuts (m+1) s spent
  by_cases h0 : i=0
  · subst i
    simp only [Nat.zero_add] at mono
    omega
  by_cases hcut : k≤C (i+1)
  · exact Nat.le_trans hcut mono
  have hNear : C i = (s i).toNat+C (i+1) :=
    FIFOCompare.cuts_adjacent (m+1) s spent i (by omega)
  have hp : k≤C i := by simpa [show i-1+1=i by omega] using left (by omega)
  have hOcc : s i=true := by
    cases hh : s i
    · rw [hh] at hNear
      change C i = 0+C (i+1) at hNear
      omega
    · rfl
  have hm : i<m := by
    by_cases hm : i=m
    · rw [hm,sink] at hOcc
      cases hOcc
    · omega
  have hVac : s (i+1)=false := by
    have hN : C (i+1)=(s (i+1)).toNat + C (i+1+1) :=
      FIFOCompare.cuts_adjacent (m+1) s spent (i+1) (by omega)
    have hr : k-1≤C (i+1+1) := right hm
    cases hh : s (i+1)
    · rfl
    · rw [hh] at hN
      change C (i+1)=1+C (i+1+1) at hN
      omega
  have hh : C (i+1)+1≤H := move (by omega) hm hOcc hVac
  rw [hOcc] at hNear
  change C i=1+C (i+1) at hNear
  omega

#print axioms closed_cut_commit

open FIFOCompare in
/-- Possible changes to tracked original stock, after excluding a newly
exposed J byte from the mask. Removing such an extra byte is idle
for this state. Physically a top overtake and a J payment use distinct
edges; both are the same abstract absorb row. -/
inductive MaskedRow (width : Nat) (s : Nat → Bool) (spent : Nat) :
    (Nat → Bool) → Nat → Prop where
  | idle : MaskedRow width s spent s spent
  | transfer (i : Nat) (hi : 0<i) (hj : i+1<width)
      (occ : s i=true) (vac : s (i+1)=false) :
      MaskedRow width s spent (setStock (setStock s i false) (i+1) true) spent
  | absorb (i : Nat) (hi : 0<i) (hj : i<width) (occ : s i=true) :
      MaskedRow width s spent (setStock s i false) (spent+1)

open FIFOCompare in
theorem MaskedRow.heights {width spent spent' : Nat} {s s' : Nat → Bool}
    (h : MaskedRow width s spent s' spent') :
    cuts width s spent 1 = cuts width s' spent' 1 ∧
    ∀ k, cuts width s spent k ≤ cuts width s' spent' k := by
  cases h with
  | idle => exact ⟨rfl,fun _ => Nat.le_refl _⟩
  | transfer i hi hj occ vac =>
    refine ⟨?_,?_⟩
    · rw [cuts_move width s spent i occ vac hj]
      simp [show i≠0 by omega]
    · intro k
      rw [cuts_move width s spent i occ vac hj]
      exact Nat.le_add_right _ _
  | absorb i hi hj occ =>
    refine ⟨?_,?_⟩
    · rw [cuts_absorb width s spent i occ hj]
      simp [show ¬i<1 by omega]
    · intro k
      rw [cuts_absorb width s spent i occ hj]
      exact Nat.le_add_right _ _

#print axioms MaskedRow.heights
end L4.WindowA0FixedSink
