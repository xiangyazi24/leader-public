import Leader.AAFJ.OneBarrier.DirtyTail


set_option autoImplicit false


namespace AAFJPK
namespace SingleBarrierSanitation
namespace DirtyTailBellman


open BarrierAlgebra


/-- The exact physical unique-barrier tail after one original-Protocol6 step. -/
def postTail
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b e : Fin n) : Fin n :=
  if AdvanceReady hk ring C e then ring.rightNeighbor b else b


/-- Four-valued dirty-tail control debt.


It is zero once the current tail bullet is clear.  While the bullet is present,
one unit pays for the bullet itself and separate units pay for a tail leader
and a tail probe. -/
def dirtyCtl
    {n k : Nat} (C : Fin n → State k) (b : Fin n) : Nat :=
  if (C b).bullet then
    1 +
      (if (C b).leader then 1 else 0) +
      (if (C b).probe then 1 else 0)
  else
    0


def dirtyChild
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b e : Fin n) : Nat :=
  let D := (protocol k hk).step ring C e
  dirtyCtl D (postTail hk ring C b e)


private theorem dirtyCtl_le_three
    {n k : Nat} (C : Fin n → State k) (b : Fin n) :
    dirtyCtl C b ≤ 3 := by
  cases hb : (C b).bullet <;>
    cases hl : (C b).leader <;>
    cases hp : (C b).probe <;>
    simp [dirtyCtl, hb, hl, hp]


private theorem incoming_ne_tail_dt
    {n : Nat} (ring : DirectedRing n) (hn2 : 1 < n) (b : Fin n) :
    ring.leftNeighbor b ≠ b := by
  intro h
  have hr := rightNeighbor_leftNeighbor_clean ring b
  rw [h] at hr
  exact (BarrierAlgebra.rightNeighbor_ne_self ring hn2 b) hr


private theorem incoming_nonbarrier_dt
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b) :
    ¬ IsBarrier hk
      (C (ring.leftNeighbor b))
      (C (ring.rightNeighbor (ring.leftNeighbor b))) := by
  let p := ring.leftNeighbor b
  have hpne : p ≠ b := by
    simpa [p] using incoming_ne_tail_dt ring hn2 b
  intro hbar
  have hphys : BarrierAt hk ring (labelsOf C) p := by
    exact (barrierAt_labelsOf_iff hk ring C p).2 hbar
  exact hpne ((hone p).1 hphys)


/-- The four-valued debt is nonincreasing under every scheduler edge.


The child is measured at the literal unique-barrier successor cut:
the tail moves to `b⁺` exactly when the source `AdvanceReady` gate is true. -/
private theorem dirtyChild_le
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b e : Fin n)
    (hone : OneBarrierAt hk ring C b) :
    dirtyChild hk ring C b e ≤ dirtyCtl C b := by
  have hn2 : 1 < n := by omega
  by_cases heb : e = b
  · subst e
    have hbarAt : BarrierAt hk ring (labelsOf C) b :=
      oneBarrierAt_barrier hk ring C b hone
    have hbar :
        IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
      (barrierAt_labelsOf_iff hk ring C b).1 hbarAt
    have hre : ring.rightNeighbor b ≠ b :=
      BarrierAlgebra.rightNeighbor_ne_self ring hn2 b
    cases hbu : (C b).bullet <;>
      cases hle : (C b).leader <;>
      cases hpr : (C b).probe <;>
      cases hph : (C b).phase <;>
      cases hhp : (C (ring.rightNeighbor b)).probe <;>
      simp [dirtyChild, postTail, dirtyCtl,
        AdvanceReady, PairAdvanceReady,
        PopulationProtocol.step, protocol, transition,
        hbar, barrierStep, probeHitsBarrier, hre,
        hbu, hle, hpr, hph, hhp]
  · have hnon :
        ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
      intro hbar
      have hphys : BarrierAt hk ring (labelsOf C) e :=
        (barrierAt_labelsOf_iff hk ring C e).2 hbar
      exact heb ((hone e).1 hphys)
    have hnotReady : ¬ AdvanceReady hk ring C e := by
      intro hready
      exact hnon hready.1
    by_cases hresp : ring.rightNeighbor e = b
    · have hbe : b ≠ e := Ne.symm heb
      have hnon' : ¬ IsBarrier hk (C e) (C b) := by
        simpa [hresp] using hnon
      cases hbu : (C b).bullet <;>
        cases hle : (C b).leader <;>
        cases hpr : (C b).probe <;>
        cases hep : (C e).probe <;>
        simp [dirtyChild, postTail, dirtyCtl,
          hnotReady, PopulationProtocol.step, protocol,
          transition, hnon, nonBarrierStep,
          heb, hbe, hresp, hnon', hbu, hle, hpr, hep]
    · have hbe : b ≠ e := Ne.symm heb
      have hbr : b ≠ ring.rightNeighbor e := Ne.symm hresp
      simp [dirtyChild, postTail, dirtyCtl, hnotReady,
        PopulationProtocol.step, hbe, hbr]


/-- The unique incoming edge strictly decreases the debt whenever the
current unique barrier tail carries a bullet. -/
private theorem dirtyChild_incoming_lt
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hbullet : (C b).bullet = true) :
    dirtyChild hk ring C b (ring.leftNeighbor b) < dirtyCtl C b := by
  have hn2 : 1 < n := by omega
  let p := ring.leftNeighbor b
  have hpne : p ≠ b := by
    simpa [p] using incoming_ne_tail_dt ring hn2 b
  have hr : ring.rightNeighbor p = b := by
    simpa [p] using rightNeighbor_leftNeighbor_clean ring b
  have hnon :
      ¬ IsBarrier hk (C p) (C (ring.rightNeighbor p)) := by
    simpa [p] using incoming_nonbarrier_dt hk ring hn2 C b hone
  have hnon' :
      ¬ IsBarrier hk (C (ring.leftNeighbor b)) (C b) := by
    simpa [p, hr] using hnon
  have hnotReady : ¬ AdvanceReady hk ring C p := by
    intro hready
    exact hnon hready.1
  have hbp : b ≠ p := Ne.symm hpne
  cases hle : (C b).leader <;>
    cases hpr : (C b).probe <;>
    cases hep : (C p).probe <;>
    simp [dirtyChild, postTail, dirtyCtl, p,
      hnotReady, PopulationProtocol.step, protocol,
      transition, hnon, nonBarrierStep,
      hnon', hpne, hbp, hr, hbullet, hle, hpr, hep]


/-- One-barrier and `PhiAt = 1` are preserved on the exact physical child cut.
This is separate from the dirty-tail control accounting. -/
theorem dirtyTail_child_frame
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b e : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphi : PhiAt ring b C = 1) :
    let D := (protocol k hk).step ring C e
    let b' :=
      if AdvanceReady hk ring C e then ring.rightNeighbor b else b
    OneBarrierAt hk ring D b' ∧
      PhiAt ring b' D = 1 := by
  have hframe :=
    oneBarrier_phi_step_le hk ring hn3 C b e hndvd hone
  dsimp only at hframe ⊢
  refine ⟨hframe.1, ?_⟩
  apply Nat.le_antisymm
  · simpa [hphi] using hframe.2
  · unfold PhiAt Phi
    exact Nat.le_max_left _ _


private theorem ofFn_sum_le
    {m : Nat} (f g : Fin m → Nat)
    (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))


private theorem ofFn_sum_const (m c : Nat) :
    (List.ofFn (fun _ : Fin m => c)).sum = m * c := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _


/-- Pointwise `f ≤ g` off one index gives the one-index exchange inequality. -/
private theorem ofFn_sum_split
    {m : Nat} (f g : Fin m → Nat) (a : Fin m)
    (hle : ∀ i, i ≠ a → f i ≤ g i) :
    (List.ofFn f).sum + g a ≤
      (List.ofFn g).sum + f a := by
  induction m with
  | zero =>
      exact Fin.elim0 a
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hz : a = 0
      · subst hz
        have ht := ofFn_sum_le
          (fun i : Fin m => f i.succ)
          (fun i : Fin m => g i.succ)
          (fun i => hle i.succ (Fin.succ_ne_zero i))
        omega
      · have hz' : a.val ≠ 0 := fun h => hz (Fin.ext h)
        let p : Fin m := ⟨a.val - 1, by
          have hc := a.isLt
          omega⟩
        have hs : p.succ = a := Fin.ext (by simp [p]; omega)
        have ht := ih
          (fun i : Fin m => f i.succ)
          (fun i : Fin m => g i.succ) p
          (fun i hi =>
            hle i.succ
              (fun h => hi (by
                rw [← hs] at h
                exact Fin.succ_inj.mp h)))
        have h0 := hle 0 (Ne.symm hz)
        simp only [hs] at ht
        omega


/-- Concrete one-step dirty-tail Bellman row.


The public hypotheses are exactly the requested one-barrier `PhiAt=1`,
non-clean, dirty-tail slice.  `hnotclean` is logically redundant once the
tail bullet is true (a clean cut has a mark-free tail), but it is retained here
so this theorem plugs directly into that branch decomposition.


The first conjunct keeps the exact moving barrier witness and `PhiAt=1`
for every scheduler child.  The second conjunct is the scale-1 Bellman row. -/
theorem dirtyTail_bellman_row
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphi : PhiAt ring b C = 1)
    (hnotclean : ¬ Clean hk ring C)
    (hbullet : (C b).bullet = true) :
    (∀ e : Fin n,
      let D := (protocol k hk).step ring C e
      let b' :=
        if AdvanceReady hk ring C e then ring.rightNeighbor b else b
      OneBarrierAt hk ring D b' ∧
        PhiAt ring b' D = 1) ∧
    (List.ofFn
      (fun e : Fin n => dirtyChild hk ring C b e)).sum + 1 ≤
        n * dirtyCtl C b := by
  constructor
  · intro e
    exact dirtyTail_child_frame
      hk ring hn3 hndvd C b e hone hphi
  · let p := ring.leftNeighbor b
    have hall :
        ∀ e : Fin n,
          dirtyChild hk ring C b e ≤ dirtyCtl C b := by
      intro e
      exact dirtyChild_le hk ring hn3 C b e hone
    have hp :
        dirtyChild hk ring C b p < dirtyCtl C b := by
      simpa [p] using
        dirtyChild_incoming_lt
          hk ring hn3 C b hone hbullet
    have hs := ofFn_sum_split
      (fun e : Fin n => dirtyChild hk ring C b e)
      (fun _ : Fin n => dirtyCtl C b) p
      (fun e _ => hall e)
    rw [ofFn_sum_const] at hs
    omega


#print axioms dirtyTail_child_frame
#print axioms dirtyTail_bellman_row


end DirtyTailBellman
end SingleBarrierSanitation
end AAFJPK
