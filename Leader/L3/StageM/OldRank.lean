import Leader.L3.StageM.OldCells

/-!
# Stage M (R10c, Lemma e-max): the inherited-work rank with old pending packets

The Q7 rank
(`L3.MarkedCells.rank`) is blind to an inherited pending packet that has no obstacle before it:
at rank zero such a packet can still sit in the window, and then the aligned queue of the attempt
class fails. This module adds the missing ghost datum and the missing rank term.

* `OCell`: a window register (`Inp`, `Car`) with a proof-only flag `o`: the register holds a
  pending packet that was present at the Stage M entrance (an *old* pending packet).
* `opair`, `oterm`, `oclean`, `oaccept`: the Q7 rows (`pair`, `portClean`, `portAccept`) with
  the flag moved along with its packet; it is cleared when the packet settles, retires or is
  erased, and a packet accepted at the port is never old. The `Cell` part is the Q7 row itself
  (`ocellApply`).
* `oviol`, `owt`, `orank`: the Q7 rank in which a pending input is a violator also when it is old
  or when a violator was seen before it. Every other weight is the Q7 weight.

Proved for every window, with no invariant:
* `orankMoveLe`: no window move raises the rank;
* `orankProgress`: off rank zero some window edge strictly lowers it;
* `orankZeroNoOld`, `rankLeOrank`: at rank zero there is no old pending packet and the Q7 rank is
  zero (so `rank_zero_barrier`, `rank_zero_gap` apply);
* `orankLe`: the rank is at most `r (4 r + 4) = 4 r (r + 1)`, the paper's Stage M budget.

Exhaustive checks before the proof (scratch script, R = 2, 3, 4 on every window and flag pattern;
single check): no move raises the rank, some edge lowers it off zero, and rank zero has no old
pending packet. With the violator test of Q7 alone (without `vb`) the rank can rise when a
non-old packet right of an old one settles; adding `vb` to the test removes that case.

Consumer: `L3.StageMGhostLane` (the Stage M potential on the ghost lane chain).
-/

namespace L3.StageMOldRank

set_option autoImplicit false

open L3.MarkedCells
open L3.PacketMomentWindow

/-! ### Registers with the old-pending flag -/

/-- Replace one register. Consumer: `oedge`, `oApply`. -/
def osetOne (G : Nat → OCell) (p : Nat) (a : OCell) : Nat → OCell :=
  fun j => if j = p then a else G j

/-- Replace two adjacent registers. Consumer: `oedge`. -/
def osetTwo (G : Nat → OCell) (p : Nat) (a b : OCell) : Nat → OCell :=
  fun j => if j = p then a else if j = p + 1 then b else G j

/-- The window edge at register `p` (terminal when `p` is last). Consumer: `oApply`,
`orankProgress`. -/
def oedge (r : Nat) (G : Nat → OCell) (p : Nat) : Nat → OCell :=
  if p + 1 < r then
    osetTwo G p (opair (decide (p = 0)) (G p) (G (p + 1))).1
      (opair (decide (p = 0)) (G p) (G (p + 1))).2
  else osetOne G (r - 1) (oterm (G (r - 1)))

/-- **A window move with flags.** Consumer: `L3.StageMGhostLane`. -/
def oApply (r : Nat) (G : Nat → OCell) : WMove → Nat → OCell
  | .frame => G
  | .edge p => oedge r G p
  | .clean => osetOne G 0 (oclean (G 0))
  | .accept t => osetOne G 0 (oaccept t (G 0))

/-- The Q7 window of a flagged window. Consumer: `ocellApply`. -/
def cellsOf (G : Nat → OCell) : Nat → Cell := fun j => (G j).cell

/-- **The `Cell` part of a flagged move is the Q7 move.** Consumer: the fresh-carry invariants
on the ghost window (`L3.StageMGhostLane`). -/
theorem ocellApply (r : Nat) (G : Nat → OCell) (m : WMove) :
    cellsOf (oApply r G m) = wApply r (cellsOf G) m := by
  funext j
  cases m with
  | frame => rfl
  | edge p =>
      show (oedge r G p j).cell = edgeStep r (cellsOf G) p j
      unfold oedge edgeStep
      by_cases h : p + 1 < r
      · rw [if_pos h, if_pos h]
        unfold osetTwo setTwo
        by_cases h1 : j = p
        · rw [if_pos h1, if_pos h1]; rfl
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : j = p + 1
          · rw [if_pos h2, if_pos h2]; rfl
          · rw [if_neg h2, if_neg h2]; rfl
      · rw [if_neg h, if_neg h]
        unfold osetOne setOne
        by_cases h1 : j = r - 1
        · rw [if_pos h1, if_pos h1]; rfl
        · rw [if_neg h1, if_neg h1]; rfl
  | clean =>
      show (osetOne G 0 (oclean (G 0)) j).cell = setOne (cellsOf G) 0 (portClean (cellsOf G 0)) j
      unfold osetOne setOne
      by_cases h1 : j = 0
      · rw [if_pos h1, if_pos h1]; rfl
      · rw [if_neg h1, if_neg h1]; rfl
  | accept t =>
      show (osetOne G 0 (oaccept t (G 0)) j).cell =
        setOne (cellsOf G) 0 (portAccept t (cellsOf G 0)) j
      unfold osetOne setOne
      by_cases h1 : j = 0
      · rw [if_pos h1, if_pos h1]; rfl
      · rw [if_neg h1, if_neg h1]; rfl

/-! ### The rank -/

/-- Left-to-right weighted scan of `k` registers from register `j`. Consumer: `orank`. -/
def oscan (r : Nat) (G : Nat → OCell) : Nat → Nat → Bool → Bool → Nat
  | 0, _, _, _ => 0
  | k + 1, j, ob, vb => owt r j ob vb (G j) + oscan r G k (j + 1) (onob ob (G j)) (onvb ob vb (G j))

/-- Scan flags after `k` registers from register `j`. Consumer: the patch lemmas. -/
def oflags (G : Nat → OCell) : Nat → Nat → Bool → Bool → Bool × Bool
  | 0, _, ob, vb => (ob, vb)
  | k + 1, j, ob, vb => oflags G k (j + 1) (onob ob (G j)) (onvb ob vb (G j))

/-- **The inherited-work rank** of a window of `r` registers. Consumer: `L3.StageMGhostLane`. -/
def orank (r : Nat) (G : Nat → OCell) : Nat := oscan r G r 0 false false

/-! ### Scan algebra -/

/-- The scan is monotone in the entering flags. Consumer: the patch lemmas. -/
theorem oscanMono (r : Nat) (G : Nat → OCell) :
    ∀ k j ob ob' vb vb', (ob = true → ob' = true) → (vb = true → vb' = true) →
      oscan r G k j ob vb ≤ oscan r G k j ob' vb' := by
  intro k
  induction k with
  | zero => intros; exact Nat.le_refl _
  | succ k ih =>
      intro j ob ob' vb vb' h1 h2
      exact Nat.add_le_add (owtMono r j ob ob' vb vb' (G j) h1 h2)
        (ih (j + 1) _ _ _ _ (onobMono ob ob' (G j) h1) (onvbMono ob ob' vb vb' (G j) h1 h2))

/-- Splitting a scan. Consumer: the patch lemmas. -/
theorem oscanAdd (r : Nat) (G : Nat → OCell) :
    ∀ k1 k2 j ob vb, oscan r G (k1 + k2) j ob vb =
      oscan r G k1 j ob vb + oscan r G k2 (j + k1) (oflags G k1 j ob vb).1
        (oflags G k1 j ob vb).2 := by
  intro k1
  induction k1 with
  | zero => intro k2 j ob vb; simp [oscan, oflags]
  | succ k1 ih =>
      intro k2 j ob vb
      have h : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
      rw [h]
      simp only [oscan, oflags]
      rw [ih k2 (j + 1) _ _]
      have h2 : j + 1 + k1 = j + (k1 + 1) := by omega
      rw [h2, Nat.add_assoc]

/-- A scan reads only its registers. Consumer: the patch lemmas. -/
theorem oscanCongr (r : Nat) (G G' : Nat → OCell) :
    ∀ k j ob vb, (∀ i, j ≤ i → i < j + k → G' i = G i) →
      oscan r G' k j ob vb = oscan r G k j ob vb ∧ oflags G' k j ob vb = oflags G k j ob vb := by
  intro k
  induction k with
  | zero => intros; exact ⟨rfl, rfl⟩
  | succ k ih =>
      intro j ob vb h
      have h0 : G' j = G j := h j (Nat.le_refl _) (by omega)
      have hr := ih (j + 1) (onob ob (G j)) (onvb ob vb (G j))
        (fun i hi hi' => h i (by omega) (by omega))
      simp only [oscan, oflags, h0]
      exact ⟨by rw [hr.1], hr.2⟩

/-- The rank split at register `p`: prefix, then `m` registers. Consumer: the patch lemmas. -/
theorem orankSplit (r p m : Nat) (hm : r = p + m) (G : Nat → OCell) :
    orank r G = oscan r G p 0 false false +
      oscan r G m p (oflags G p 0 false false).1 (oflags G p 0 false false).2 := by
  unfold orank
  have h := oscanAdd r G p m 0 false false
  rw [← hm, Nat.zero_add] at h
  exact h

/-- **Patch of two adjacent registers.** Consumer: `orankMoveLe`, `orankProgress`. -/
theorem opatchTwo (r p d : Nat) (hp : p + 1 < r) (G G' : Nat → OCell)
    (hout : ∀ i, i ≠ p → i ≠ p + 1 → G' i = G i)
    (hloc : ∀ ob vb, oflags G p 0 false false = (ob, vb) →
      owt r p ob vb (G' p) + owt r (p + 1) (onob ob (G' p)) (onvb ob vb (G' p)) (G' (p + 1)) + d ≤
        owt r p ob vb (G p) + owt r (p + 1) (onob ob (G p)) (onvb ob vb (G p)) (G (p + 1)) ∧
      (onob (onob ob (G' p)) (G' (p + 1)) = true → onob (onob ob (G p)) (G (p + 1)) = true) ∧
      (onvb (onob ob (G' p)) (onvb ob vb (G' p)) (G' (p + 1)) = true →
        onvb (onob ob (G p)) (onvb ob vb (G p)) (G (p + 1)) = true)) :
    orank r G' + d ≤ orank r G := by
  obtain ⟨m, hm⟩ : ∃ m, r = p + (m + 2) := ⟨r - p - 2, by omega⟩
  have hpre := oscanCongr r G G' p 0 false false (fun i _ hi => hout i (by omega) (by omega))
  rw [orankSplit r p (m + 2) hm G', orankSplit r p (m + 2) hm G, hpre.1, hpre.2]
  generalize hf : oflags G p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl
  have hsuf := oscanCongr r G G' m (p + 2) (onob (onob ob (G' p)) (G' (p + 1)))
    (onvb (onob ob (G' p)) (onvb ob vb (G' p)) (G' (p + 1)))
    (fun i h1 h2 => hout i (by omega) (by omega))
  have hmono := oscanMono r G m (p + 2)
    (onob (onob ob (G' p)) (G' (p + 1))) (onob (onob ob (G p)) (G (p + 1)))
    (onvb (onob ob (G' p)) (onvb ob vb (G' p)) (G' (p + 1)))
    (onvb (onob ob (G p)) (onvb ob vb (G p)) (G (p + 1))) hloc'.2.1 hloc'.2.2
  have e2 : ∀ cs : Nat → OCell, oscan r cs (m + 2) p ob vb =
      owt r p ob vb (cs p) +
        (owt r (p + 1) (onob ob (cs p)) (onvb ob vb (cs p)) (cs (p + 1)) +
          oscan r cs m (p + 2) (onob (onob ob (cs p)) (cs (p + 1)))
            (onvb (onob ob (cs p)) (onvb ob vb (cs p)) (cs (p + 1)))) := fun _ => rfl
  rw [e2 G', e2 G, hsuf.1]
  have := hloc'.1
  omega

/-- **Patch of one register with a suffix.** Consumer: `orankMoveLe`. -/
theorem opatchOne (r p d : Nat) (hp : p < r) (G G' : Nat → OCell)
    (hout : ∀ i, i ≠ p → G' i = G i)
    (hloc : ∀ ob vb, oflags G p 0 false false = (ob, vb) →
      owt r p ob vb (G' p) + d ≤ owt r p ob vb (G p) ∧
      (onob ob (G' p) = true → onob ob (G p) = true) ∧
      (onvb ob vb (G' p) = true → onvb ob vb (G p) = true)) :
    orank r G' + d ≤ orank r G := by
  obtain ⟨m, hm⟩ : ∃ m, r = p + (m + 1) := ⟨r - p - 1, by omega⟩
  have hpre := oscanCongr r G G' p 0 false false (fun i _ hi => hout i (by omega))
  rw [orankSplit r p (m + 1) hm G', orankSplit r p (m + 1) hm G, hpre.1, hpre.2]
  generalize hf : oflags G p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl
  have hsuf := oscanCongr r G G' m (p + 1) (onob ob (G' p)) (onvb ob vb (G' p))
    (fun i h1 h2 => hout i (by omega))
  have hmono := oscanMono r G m (p + 1) (onob ob (G' p)) (onob ob (G p))
    (onvb ob vb (G' p)) (onvb ob vb (G p)) hloc'.2.1 hloc'.2.2
  have e2 : ∀ cs : Nat → OCell, oscan r cs (m + 1) p ob vb =
      owt r p ob vb (cs p) + oscan r cs m (p + 1) (onob ob (cs p)) (onvb ob vb (cs p)) :=
    fun _ => rfl
  rw [e2 G', e2 G, hsuf.1]
  have := hloc'.1
  omega

/-- **Patch of the last register.** Consumer: `orankMoveLe`, `orankProgress`. -/
theorem opatchLast (r p d : Nat) (hp : p + 1 = r) (G G' : Nat → OCell)
    (hout : ∀ i, i ≠ p → G' i = G i)
    (hloc : ∀ ob vb, oflags G p 0 false false = (ob, vb) →
      owt r p ob vb (G' p) + d ≤ owt r p ob vb (G p)) :
    orank r G' + d ≤ orank r G := by
  have hpre := oscanCongr r G G' p 0 false false (fun i _ hi => hout i (by omega))
  rw [orankSplit r p 1 hp.symm G', orankSplit r p 1 hp.symm G, hpre.1, hpre.2]
  generalize hf : oflags G p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl
  have e2 : ∀ cs : Nat → OCell, oscan r cs 1 p ob vb = owt r p ob vb (cs p) := by
    intro cs; simp [oscan]
  rw [e2 G', e2 G]
  omega

/-! ### No move raises the rank -/

/-- **No window move raises the inherited-work rank** (every window, no invariant).
Consumer: `L3.StageMGhostLane` (nonincrease on every lane letter). -/
theorem orankMoveLe (r : Nat) (hr : 2 ≤ r) (G : Nat → OCell) (m : WMove) (hm : m.Ok r) :
    orank r (oApply r G m) ≤ orank r G := by
  cases m with
  | frame => exact Nat.le_refl _
  | edge p =>
      have hp : p < r := hm
      show orank r (oedge r G p) ≤ orank r G
      unfold oedge
      by_cases h : p + 1 < r
      · rw [if_pos h]
        have := opatchTwo r p 0 h G
          (osetTwo G p (opair (decide (p = 0)) (G p) (G (p + 1))).1
            (opair (decide (p = 0)) (G p) (G (p + 1))).2)
          (fun i h1 h2 => by simp [osetTwo, h1, h2])
          (fun ob vb _ => by
            have := opairLocal r p h (decide (p = 0)) (G p) (G (p + 1)) ob vb
            simpa [osetTwo] using this)
        omega
      · rw [if_neg h]
        have := opatchLast r (r - 1) 0 (by omega) G (osetOne G (r - 1) (oterm (G (r - 1))))
          (fun i h1 => by simp [osetOne, h1])
          (fun ob vb _ => by
            have := otermLocal r (r - 1) (by omega) (G (r - 1)) ob vb
            simpa [osetOne] using this)
        omega
  | clean =>
      have := opatchOne r 0 0 (by omega) G (osetOne G 0 (oclean (G 0)))
        (fun i h1 => by simp [osetOne, h1])
        (fun ob vb hf => by
          have hf' : oflags G 0 0 false false = (false, false) := rfl
          rw [hf'] at hf
          cases hf
          simpa [osetOne] using ocleanLocal r (by omega) (G 0))
      exact this
  | accept t =>
      have := opatchOne r 0 0 (by omega) G (osetOne G 0 (oaccept t (G 0)))
        (fun i h1 => by simp [osetOne, h1])
        (fun ob vb hf => by
          have hf' : oflags G 0 0 false false = (false, false) := rfl
          rw [hf'] at hf
          cases hf
          simpa [osetOne] using oacceptLocal r (by omega) t (G 0))
      exact this

/-! ### Strict progress off rank zero -/

/-- Register `p` is selected. Consumer: `oedgeLt`. -/
def OSelAt (r : Nat) (G : Nat → OCell) (p : Nat) : Prop :=
  if p + 1 < r then
    OSel (oflags G p 0 false false).1 (oflags G p 0 false false).2 (G p) (G (p + 1))
  else OSelT (oflags G p 0 false false).1 (oflags G p 0 false false).2 (G p)

/-- The edge of a selected register strictly lowers the rank. Consumer: `orankProgress`. -/
theorem oedgeLt (r p : Nat) (hp : p < r) (G : Nat → OCell) (hsel : OSelAt r G p) :
    orank r (oedge r G p) + 1 ≤ orank r G := by
  unfold oedge
  unfold OSelAt at hsel
  by_cases h : p + 1 < r
  · rw [if_pos h] at hsel ⊢
    apply opatchTwo r p 1 h
    · intro i h1 h2; simp [osetTwo, h1, h2]
    · intro ob vb hf
      rw [hf] at hsel
      have h1 := opairStrict r p h (decide (p = 0)) (G p) (G (p + 1)) ob vb hsel
      have h2 := opairLocal r p h (decide (p = 0)) (G p) (G (p + 1)) ob vb
      simpa [osetTwo] using ⟨h1, h2.2.1, h2.2.2⟩
  · rw [if_neg h] at hsel ⊢
    apply opatchLast r (r - 1) 1 (by omega)
    · intro i h1; simp [osetOne, h1]
    · intro ob vb hf
      have hp' : p = r - 1 := by omega
      subst hp'
      rw [hf] at hsel
      have := otermStrict r (r - 1) (by omega) (G (r - 1)) ob vb hsel
      simpa [osetOne] using this

/-- Scan flags after one more register. Consumer: `orankProgress`. -/
theorem oflagsSucc (G : Nat → OCell) :
    ∀ k j ob vb, oflags G (k + 1) j ob vb =
      (onob (oflags G k j ob vb).1 (G (j + k)),
        onvb (oflags G k j ob vb).1 (oflags G k j ob vb).2 (G (j + k))) := by
  intro k
  induction k with
  | zero => intro j ob vb; simp [oflags]
  | succ k ih =>
      intro j ob vb
      have h1 : oflags G (k + 1 + 1) j ob vb =
          oflags G (k + 1) (j + 1) (onob ob (G j)) (onvb ob vb (G j)) := rfl
      have h2 : oflags G (k + 1) j ob vb = oflags G k (j + 1) (onob ob (G j)) (onvb ob vb (G j)) :=
        rfl
      rw [h1, ih (j + 1), h2]
      have e : j + 1 + k = j + (k + 1) := by omega
      rw [e]

/-- Without violators and inherited carries the scan is zero. Consumer: `orankProgress`. -/
theorem oscanZeroClean (r : Nat) (G : Nat → OCell) :
    ∀ k j ob vb, vb = false →
      (∀ i, i < k → oviol (oflags G i j ob vb).1 (oflags G i j ob vb).2 (G (j + i)) = false ∧
        (G (j + i)).c ≠ .inh) →
      oscan r G k j ob vb = 0 := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro j ob vb hvb h
      have h0 := h 0 (by omega)
      simp only [oflags, Nat.add_zero] at h0
      subst hvb
      have hw : owt r j ob false (G j) = 0 := owtZeroClean r j ob (G j) h0.1 h0.2
      have hv' : onvb ob false (G j) = false := by simp [onvb, h0.1]
      simp only [oscan, hw, Nat.zero_add]
      apply ih (j + 1) _ _ hv'
      intro i hi
      have := h (i + 1) (by omega)
      have e : j + (i + 1) = j + 1 + i := by omega
      simp only [oflags, e] at this
      exact this

/-- **Off rank zero some window edge strictly lowers the inherited-work rank** (every window,
no invariant). Consumer: `L3.StageMGhostLane` (the nominated edge of the Stage M moment). -/
theorem orankProgress (r : Nat) (hr : 2 ≤ r) (G : Nat → OCell) (hpos : 0 < orank r G) :
    ∃ p, p < r ∧ orank r (oedge r G p) + 1 ≤ orank r G := by
  by_cases hv : ∃ i, i < r ∧
      oviol (oflags G i 0 false false).1 (oflags G i 0 false false).2 (G i) = true
  · obtain ⟨i, hi, hviol, hmax⟩ := exists_max r _ hv
    have hflag := oflagsSucc G i 0 false false
    simp only [Nat.zero_add] at hflag
    have hvb : (oflags G (i + 1) 0 false false).2 = true := by
      rw [hflag]; simp [onvb, hviol]
    rcases hxc : G i with ⟨xi, xc, xo⟩
    rw [hxc] at hviol
    have hxP : xi.isP = true := by
      simp only [oviol, Bool.and_eq_true] at hviol; exact hviol.1
    by_cases hcar : xc = .off
    · subst hcar
      have hwhy : (oflags G i 0 false false).1 = true ∨ (oflags G i 0 false false).2 = true ∨
          xo = true := by
        simp [oviol] at hviol
        rcases hviol.2 with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      by_cases hlast : i + 1 < r
      · rcases hy : G (i + 1) with ⟨yi, yc, yo⟩
        by_cases hyc : yc = .off
        · subst hyc
          have hselP : (yi = .e ∨ yi.isS = true) → ∃ p, p < r ∧ OSelAt r G p := by
            intro hy'
            refine ⟨i, hi, ?_⟩
            unfold OSelAt
            rw [if_pos hlast, hxc, hy]
            refine Or.inr (Or.inr (Or.inl ⟨hxP, rfl, hwhy, ?_⟩))
            rcases hy' with h | h
            · exact Or.inl ⟨h, rfl⟩
            · exact Or.inr ⟨h, rfl⟩
          cases yi with
          | e => obtain ⟨p, hp, hs⟩ := hselP (Or.inl rfl); exact ⟨p, hp, oedgeLt r p hp G hs⟩
          | st => obtain ⟨p, hp, hs⟩ := hselP (Or.inr rfl); exact ⟨p, hp, oedgeLt r p hp G hs⟩
          | sn => obtain ⟨p, hp, hs⟩ := hselP (Or.inr rfl); exact ⟨p, hp, oedgeLt r p hp G hs⟩
          | x =>
              refine ⟨i + 1, hlast, oedgeLt r (i + 1) hlast G ?_⟩
              unfold OSelAt
              by_cases h2 : i + 1 + 1 < r
              · rw [if_pos h2, hy]; exact Or.inr (Or.inl ⟨rfl, rfl, hvb⟩)
              · rw [if_neg h2, hy]; exact Or.inr (Or.inl ⟨rfl, rfl, hvb⟩)
          | pt =>
              exfalso
              apply hmax (i + 1) (by omega) hlast
              rw [hy]; simp [oviol, hvb, Inp.isP]
          | pn =>
              exfalso
              apply hmax (i + 1) (by omega) hlast
              rw [hy]; simp [oviol, hvb, Inp.isP]
        · refine ⟨i + 1, hlast, oedgeLt r (i + 1) hlast G ?_⟩
          unfold OSelAt
          by_cases h2 : i + 1 + 1 < r
          · rw [if_pos h2, hy]; exact Or.inl ⟨hyc, Or.inr hvb⟩
          · rw [if_neg h2, hy]; exact Or.inl ⟨hyc, Or.inr hvb⟩
      · refine ⟨i, hi, oedgeLt r i hi G ?_⟩
        unfold OSelAt
        rw [if_neg hlast, hxc]
        exact Or.inr (Or.inr (Or.inl ⟨hxP, rfl, hwhy⟩))
    · refine ⟨i, hi, oedgeLt r i hi G ?_⟩
      unfold OSelAt
      by_cases h2 : i + 1 < r
      · rw [if_pos h2, hxc]; exact Or.inl ⟨hcar, Or.inl hviol⟩
      · rw [if_neg h2, hxc]; exact Or.inl ⟨hcar, Or.inl hviol⟩
  · by_cases hinh : ∃ j, j < r ∧ (G j).c = .inh
    · obtain ⟨j, hj, hc⟩ := hinh
      refine ⟨j, hj, oedgeLt r j hj G ?_⟩
      unfold OSelAt
      by_cases h2 : j + 1 < r
      · rw [if_pos h2]; exact Or.inr (Or.inr (Or.inr hc))
      · rw [if_neg h2]; exact Or.inr (Or.inr (Or.inr hc))
    · exfalso
      have hzero : orank r G = 0 := by
        unfold orank
        apply oscanZeroClean r G r 0 false false rfl
        intro i hi
        refine ⟨?_, ?_⟩
        · cases h : oviol (oflags G i 0 false false).1 (oflags G i 0 false false).2 (G (0 + i))
          · rfl
          · exact absurd ⟨i, hi, by simpa using h⟩ hv
        · intro h
          exact hinh ⟨0 + i, by omega, h⟩
      omega

/-! ### Rank zero and the bound -/

/-- The Q7 scan is at most the inherited-work scan. Consumer: `rankLeOrank`. -/
theorem scanLeOscan (r : Nat) (G : Nat → OCell) :
    ∀ k j ob vb vb', (vb = true → vb' = true) →
      scan r (cellsOf G) k j ob vb ≤ oscan r G k j ob vb' := by
  intro k
  induction k with
  | zero => intros; exact Nat.le_refl _
  | succ k ih =>
      intro j ob vb vb' h
      have hw := wtLeOwt r j ob vb vb' (G j) h
      exact Nat.add_le_add hw.1 (ih (j + 1) _ _ _ hw.2)

/-- **The Q7 rank of the window is at most the inherited-work rank.** Consumer: the stop facts
(`rank_zero_barrier`, `rank_zero_gap` at inherited-work rank zero). -/
theorem rankLeOrank (r : Nat) (G : Nat → OCell) : rank r (cellsOf G) ≤ orank r G :=
  scanLeOscan r G r 0 false false false (fun h => h)

/-- A zero scan has zero register weights. Consumer: `orankZeroNoOld`. -/
theorem oscanZeroWt (r : Nat) (G : Nat → OCell) :
    ∀ k j ob vb, oscan r G k j ob vb = 0 → ∀ i, i < k →
      owt r (j + i) (oflags G i j ob vb).1 (oflags G i j ob vb).2 (G (j + i)) = 0 := by
  intro k
  induction k with
  | zero => intro j ob vb _ i hi; omega
  | succ k ih =>
      intro j ob vb h i hi
      simp only [oscan] at h
      cases i with
      | zero => simpa [oflags] using (show owt r j ob vb (G j) = 0 by omega)
      | succ i =>
          have := ih (j + 1) (onob ob (G j)) (onvb ob vb (G j)) (by omega) i (by omega)
          have e : j + (i + 1) = j + 1 + i := by omega
          simp only [oflags, e]
          exact this

/-- **At rank zero no old pending packet is left.** Consumer: the stop of Stage M (the old
pending packets are resolved, so the aligned queue is the queue of post-entrance exports). -/
theorem orankZeroNoOld (r : Nat) (G : Nat → OCell) (h : orank r G = 0) (j : Nat) (hj : j < r) :
    oP (G j) = false := by
  have hz := oscanZeroWt r G r 0 false false h j hj
  simp only [Nat.zero_add] at hz
  revert hz
  generalize (oflags G j 0 false false).1 = ob
  generalize (oflags G j 0 false false).2 = vb
  rcases G j with ⟨ci, cc, co⟩
  cases co <;> cases ci <;> cases cc <;> cases ob <;> cases vb <;>
    simp (config := { decide := true }) [owt, oviol, oP, gateW, Inp.isP] <;> omega

/-- The scan of `k` registers is at most `k (4 r + 4)`. Consumer: `orankLe`. -/
theorem oscanLe (r : Nat) (G : Nat → OCell) :
    ∀ k j ob vb, oscan r G k j ob vb ≤ k * (4 * r + 4) := by
  intro k
  induction k with
  | zero => intros; simp [oscan]
  | succ k ih =>
      intro j ob vb
      have h1 := owtLe r j ob vb (G j)
      have h2 := ih (j + 1) (onob ob (G j)) (onvb ob vb (G j))
      simp only [oscan]
      rw [Nat.succ_mul]
      omega

/-- **The inherited-work rank is at most `4 r (r + 1)`** (the paper's Stage M term
`r(r+2) + r(r+1) + r^2 + r(r+1)`). Consumer: the Stage M budget. -/
theorem orankLe (r : Nat) (G : Nat → OCell) : orank r G ≤ r * (4 * r + 4) :=
  oscanLe r G r 0 false false

end L3.StageMOldRank

#print axioms L3.StageMOldRank.ocellApply
#print axioms L3.StageMOldRank.orankMoveLe
#print axioms L3.StageMOldRank.orankProgress
#print axioms L3.StageMOldRank.rankLeOrank
#print axioms L3.StageMOldRank.orankZeroNoOld
#print axioms L3.StageMOldRank.orankLe
