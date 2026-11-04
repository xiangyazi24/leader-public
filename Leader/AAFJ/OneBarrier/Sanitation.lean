import Leader.AAFJ.BarrierAlgebra

/-!
# Deterministic single-barrier sanitation for generalized AAFJ `P_k`

This module supplies the deterministic foundation of the one-barrier argument.
It uses the literal transition from `AAFJProtocol6`; no scheduler, probability,
or convergence hypothesis is introduced here.

The ring is cut immediately after its unique barrier.  Cut coordinate zero is
the barrier head and coordinate `n-1` is its tail.  A probe is dangerous when
no leader occurs at a strictly larger cut coordinate.  The potential is
`max 1 (leaders + dangerousBit)`.
-/

namespace AAFJPK
namespace SingleBarrierSanitation

open BarrierAlgebra

set_option autoImplicit false

/-! ## Clockwise cut coordinates -/

/-- Position reached after `t` clockwise edges from `i`. -/
def cwPos {n : Nat} (ring : DirectedRing n) (i : Fin n) (t : Nat) : Fin n :=
  ⟨(i.val + t) % n, Nat.mod_lt _ ring.hn⟩

/-- Canonical clockwise distance in `[0,n)`. -/
def cwDist {n : Nat} (_ring : DirectedRing n) (i j : Fin n) : Nat :=
  (j.val + n - i.val) % n

@[simp] theorem cwPos_zero {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    cwPos ring i 0 = i := by
  apply Fin.ext
  simp [cwPos, Nat.mod_eq_of_lt i.isLt]

theorem cwDist_lt {n : Nat} (ring : DirectedRing n) (i j : Fin n) :
    cwDist ring i j < n := by
  exact Nat.mod_lt _ ring.hn

theorem cwPos_cwDist {n : Nat} (ring : DirectedRing n) (i j : Fin n) :
    cwPos ring i (cwDist ring i j) = j := by
  apply Fin.ext
  unfold cwPos cwDist
  dsimp only
  rw [Nat.add_mod_mod]
  have hsum : i.val + (j.val + n - i.val) = j.val + n := by omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt j.isLt]

theorem cwPos_bounded_unique {n : Nat} (ring : DirectedRing n)
    (i j : Fin n) (d : Nat) (hd : d < n) (hpos : cwPos ring i d = j) :
    d = cwDist ring i j := by
  have hv := congrArg Fin.val hpos
  have hc := congrArg Fin.val (cwPos_cwDist ring i j)
  unfold cwPos at hv hc
  dsimp only at hv hc
  have hmod : (i.val + d) % n =
      (i.val + cwDist ring i j) % n := hv.trans hc.symm
  have hdist := cwDist_lt ring i j
  by_cases hdWrap : i.val + d < n
  · rw [Nat.mod_eq_of_lt hdWrap] at hmod
    by_cases hcWrap : i.val + cwDist ring i j < n
    · rw [Nat.mod_eq_of_lt hcWrap] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  · rw [Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)] at hmod
    by_cases hcWrap : i.val + cwDist ring i j < n
    · rw [Nat.mod_eq_of_lt hcWrap] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hmod
      omega

@[simp] theorem cwPos_period {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    cwPos ring i n = i := by
  apply Fin.ext
  simp [cwPos, Nat.mod_eq_of_lt i.isLt]

theorem cwPos_rightNeighbor {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (t : Nat) :
    cwPos ring (ring.rightNeighbor i) t = cwPos ring i (t + 1) := by
  apply Fin.ext
  unfold cwPos DirectedRing.rightNeighbor
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

@[simp] theorem cwPos_succ {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (t : Nat) :
    cwPos ring i (t + 1) = ring.rightNeighbor (cwPos ring i t) := by
  apply Fin.ext
  unfold cwPos DirectedRing.rightNeighbor
  dsimp only
  rw [mod_succ_eq]
  congr 1

/-- Physical site at cut coordinate `i`, where the cut is the edge `barrier`. -/
def cutPos {n : Nat} (ring : DirectedRing n) (barrier i : Fin n) : Fin n :=
  cwPos ring (ring.rightNeighbor barrier) i.val

/-- Cut coordinate of a physical site. -/
def cutCoord {n : Nat} (ring : DirectedRing n) (barrier i : Fin n) : Fin n :=
  ⟨cwDist ring (ring.rightNeighbor barrier) i,
    cwDist_lt ring (ring.rightNeighbor barrier) i⟩

@[simp] theorem cutPos_cutCoord {n : Nat} (ring : DirectedRing n)
    (barrier i : Fin n) :
    cutPos ring barrier (cutCoord ring barrier i) = i := by
  exact cwPos_cwDist ring (ring.rightNeighbor barrier) i

@[simp] theorem cutCoord_cutPos {n : Nat} (ring : DirectedRing n)
    (barrier i : Fin n) :
    cutCoord ring barrier (cutPos ring barrier i) = i := by
  apply Fin.ext
  exact (cwPos_bounded_unique ring (ring.rightNeighbor barrier)
    (cutPos ring barrier i) i.val i.isLt rfl).symm

theorem cutPos_injective {n : Nat} (ring : DirectedRing n)
    (barrier : Fin n) : Function.Injective (cutPos ring barrier) := by
  intro i j hij
  have h := congrArg (cutCoord ring barrier) hij
  simpa using h

theorem cutPos_surjective {n : Nat} (ring : DirectedRing n)
    (barrier : Fin n) : Function.Surjective (cutPos ring barrier) := by
  intro i
  exact ⟨cutCoord ring barrier i, cutPos_cutCoord ring barrier i⟩

@[simp] theorem cutPos_zero {n : Nat} (ring : DirectedRing n)
    (barrier : Fin n) :
    cutPos ring barrier ⟨0, ring.hn⟩ = ring.rightNeighbor barrier := by
  simp [cutPos]

theorem cutPos_rightNeighbor {n : Nat} (ring : DirectedRing n)
    (barrier i : Fin n) :
    cutPos ring barrier (ring.rightNeighbor i) =
      ring.rightNeighbor (cutPos ring barrier i) := by
  apply Fin.ext
  unfold cutPos cwPos DirectedRing.rightNeighbor
  dsimp only
  rw [Nat.add_mod_mod, mod_succ_eq]
  congr 1

/-- Last cut coordinate, i.e. the physical barrier tail. -/
def tailCoord {n : Nat} (ring : DirectedRing n) : Fin n :=
  ⟨n - 1, by
    have hn : 0 < n := ring.hn
    omega⟩

@[simp] theorem rightNeighbor_tailCoord {n : Nat} (ring : DirectedRing n) :
    ring.rightNeighbor (tailCoord ring) = ⟨0, ring.hn⟩ := by
  apply Fin.ext
  have hnpos : 0 < n := ring.hn
  have hn : n - 1 + 1 = n := by omega
  simp [tailCoord, DirectedRing.rightNeighbor, hn]

@[simp] theorem cutPos_tailCoord {n : Nat} (ring : DirectedRing n)
    (barrier : Fin n) : cutPos ring barrier (tailCoord ring) = barrier := by
  rw [cutPos]
  rw [cwPos_rightNeighbor]
  have hnpos : 0 < n := ring.hn
  have h : n - 1 + 1 = n := by omega
  change cwPos ring barrier (n - 1 + 1) = barrier
  rw [h, cwPos_period]

/-- Reindex a physical configuration in barrier-cut coordinates. -/
def cutView {n k : Nat} (ring : DirectedRing n) (barrier : Fin n)
    (C : Fin n → State k) : Fin n → State k :=
  fun i => C (cutPos ring barrier i)

/-- Exact equivariance of the literal packaged protocol step under a cut
rotation. -/
theorem cutView_step_at_cutPos {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (barrier : Fin n)
    (C : Fin n → State k) (e : Fin n) :
    cutView ring barrier
        ((protocol k hk).step ring C (cutPos ring barrier e)) =
      (protocol k hk).step ring (cutView ring barrier C) e := by
  funext i
  have hinj := cutPos_injective ring barrier
  simp only [cutView, PopulationProtocol.step, protocol]
  rw [cutPos_rightNeighbor]
  by_cases hie : i = e
  · subst i
    simp
  · have hpos : cutPos ring barrier i ≠ cutPos ring barrier e := by
      intro h
      exact hie (hinj h)
    by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hphys : ring.rightNeighbor (cutPos ring barrier e) ≠
          cutPos ring barrier e := by
        intro h
        apply hie
        apply hinj
        rw [cutPos_rightNeighbor]
        exact h
      simp [hie, hphys, cutPos_rightNeighbor]
    · have hposr : cutPos ring barrier i ≠
          ring.rightNeighbor (cutPos ring barrier e) := by
        rw [← cutPos_rightNeighbor]
        intro h
        exact hir (hinj h)
      simp [hie, hir, hpos, hposr]

/-! ## The cut potential -/

/-- Left rotation of cut coordinates after the barrier advances one edge. -/
def rotateCut {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k) : Fin n → State k :=
  fun i => X (ring.rightNeighbor i)

theorem cutPos_nextBarrier {n : Nat} (ring : DirectedRing n)
    (barrier i : Fin n) :
    cutPos ring (ring.rightNeighbor barrier) i =
      cutPos ring barrier (ring.rightNeighbor i) := by
  apply Fin.ext
  unfold cutPos cwPos DirectedRing.rightNeighbor
  dsimp only
  rw [Nat.mod_add_mod, Nat.add_mod_mod]
  congr 1
  omega

/-- Changing the cut from a barrier to its successor is exactly one left
rotation of the old cut view. -/
theorem cutView_nextBarrier {n k : Nat} (ring : DirectedRing n)
    (barrier : Fin n) (C : Fin n → State k) :
    cutView ring (ring.rightNeighbor barrier) C =
      rotateCut ring (cutView ring barrier C) := by
  funext i
  exact congrArg C (cutPos_nextBarrier ring barrier i)

/-- Count the true bits of a finite Boolean family. -/
def bitCount {n : Nat} (bits : Fin n → Bool) : Nat :=
  (List.ofFn (fun i => if bits i then 1 else 0)).sum

theorem bitCount_succ {n : Nat} (bits : Fin (n + 1) → Bool) :
    bitCount bits =
      (if bits 0 then 1 else 0) +
        bitCount (fun i : Fin n => bits i.succ) := by
  unfold bitCount
  rw [List.ofFn_succ, List.sum_cons]

theorem bitCount_congr {n : Nat} {a b : Fin n → Bool}
    (h : ∀ i, a i = b i) : bitCount a = bitCount b := by
  congr 1
  funext i
  rw [h i]

theorem bitCount_single_drop {n : Nat}
    (before after : Fin n → Bool) (victim : Fin n)
    (hbefore : before victim = true)
    (hafter : after victim = false)
    (hother : ∀ i, i ≠ victim → after i = before i) :
    bitCount after + 1 = bitCount before := by
  induction n with
  | zero => exact Fin.elim0 victim
  | succ n ih =>
      rw [bitCount_succ, bitCount_succ]
      cases victim using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin n => after i.succ) =
                fun i : Fin n => before i.succ := by
            funext i
            exact hother i.succ (Fin.succ_ne_zero i)
          rw [hbefore, hafter, htail]
          simp only [Bool.false_eq_true, eq_self, if_false, if_true,
            Nat.zero_add]
          omega
      | succ victim =>
          have hhead : after 0 = before 0 :=
            hother 0 (fun h => Fin.succ_ne_zero victim h.symm)
          have htail := ih
            (fun i : Fin n => before i.succ)
            (fun i : Fin n => after i.succ)
            victim hbefore hafter
            (fun i hi => hother i.succ (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

theorem bitCount_single_birth {n : Nat}
    (before after : Fin n → Bool) (born : Fin n)
    (hbefore : before born = false)
    (hafter : after born = true)
    (hother : ∀ i, i ≠ born → after i = before i) :
    bitCount after = bitCount before + 1 := by
  induction n with
  | zero => exact Fin.elim0 born
  | succ n ih =>
      rw [bitCount_succ, bitCount_succ]
      cases born using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin n => after i.succ) =
                fun i : Fin n => before i.succ := by
            funext i
            exact hother i.succ (Fin.succ_ne_zero i)
          rw [hbefore, hafter, htail]
          simp only [Bool.false_eq_true, eq_self, if_false, if_true,
            Nat.zero_add]
          omega
      | succ born =>
          have hhead : after 0 = before 0 :=
            hother 0 (fun h => Fin.succ_ne_zero born h.symm)
          have htail := ih
            (fun i : Fin n => before i.succ)
            (fun i : Fin n => after i.succ)
            born hbefore hafter
            (fun i hi => hother i.succ (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

theorem bitCount_single_birth_le {n : Nat}
    (before after : Fin n → Bool) (born : Fin n)
    (hafter : after born = true)
    (hother : ∀ i, i ≠ born → after i = before i) :
    bitCount after ≤ bitCount before + 1 := by
  cases hbefore : before born
  · have h := bitCount_single_birth before after born
      hbefore hafter hother
    omega
  · have heq : after = before := by
      funext i
      by_cases hi : i = born
      · subst i
        rw [hafter, hbefore]
      · exact hother i hi
    rw [heq]
    omega

private theorem sum_ofFn_rightNeighbor {n : Nat} (ring : DirectedRing n)
    (f : Fin n → Nat) :
    (List.ofFn (fun i => f (ring.rightNeighbor i))).sum =
      (List.ofFn f).sum := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun i : Fin (m + 1) => f (ring.rightNeighbor i)) =
    (List.ofFn (fun i : Fin m =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last m))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last m) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin m,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin m => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin m => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

/-- Number of current leaders. -/
def leaderCount {n k : Nat} (X : Fin n → State k) : Nat :=
  bitCount (fun i => (X i).leader)

/-- A probe is shielded when a leader occurs strictly ahead in the cut order. -/
def Shielded {n k : Nat} (X : Fin n → State k) (p : Fin n) : Prop :=
  ∃ ell : Fin n, p.val < ell.val ∧ (X ell).leader = true

/-- Some probe has no strictly-ahead leader. -/
def Dangerous {n k : Nat} (X : Fin n → State k) : Prop :=
  ∃ p : Fin n, (X p).probe = true ∧ ¬ Shielded X p

instance instDecidableShielded {n k : Nat} (X : Fin n → State k)
    (p : Fin n) : Decidable (Shielded X p) := by
  unfold Shielded
  infer_instance

instance instDecidableDangerous {n k : Nat} (X : Fin n → State k) :
    Decidable (Dangerous X) := by
  unfold Dangerous
  infer_instance

/-- Boolean-sized dangerousness charge. -/
def dangerBit {n k : Nat} (X : Fin n → State k) : Nat :=
  if Dangerous X then 1 else 0

/-- Single-barrier sanitation potential in cut coordinates. -/
def Phi {n k : Nat} (X : Fin n → State k) : Nat :=
  max 1 (leaderCount X + dangerBit X)

@[simp] theorem leaderCount_rotateCut {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k) :
    leaderCount (rotateCut ring X) = leaderCount X := by
  unfold leaderCount bitCount rotateCut
  simpa using sum_ofFn_rightNeighbor ring
    (fun i => if (X i).leader then 1 else 0)

theorem dangerBit_le_one {n k : Nat} (X : Fin n → State k) :
    dangerBit X ≤ 1 := by
  unfold dangerBit
  split <;> omega

theorem dangerous_of_tail_probe {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k)
    (hprobe : (X (tailCoord ring)).probe = true) : Dangerous X := by
  refine ⟨tailCoord ring, hprobe, ?_⟩
  rintro ⟨ell, hell, _⟩
  change n - 1 < ell.val at hell
  have hn : ell.val < n := ell.isLt
  omega

theorem not_dangerous_of_tail_leader {n k : Nat}
    (ring : DirectedRing n) (X : Fin n → State k)
    (hleader : (X (tailCoord ring)).leader = true)
    (hprobe : (X (tailCoord ring)).probe = false) : ¬ Dangerous X := by
  rintro ⟨p, hp, hnot⟩
  apply hnot
  by_cases hpt : p = tailCoord ring
  · subst p
    simp [hprobe] at hp
  · refine ⟨tailCoord ring, ?_, hleader⟩
    change p.val < n - 1
    have hpLt : p.val < n := p.isLt
    have hpne : p.val ≠ n - 1 := by
      intro h
      apply hpt
      apply Fin.ext
      exact h
    omega

/-- The potential attached to a physical one-barrier cut. -/
def PhiAt {n k : Nat} (ring : DirectedRing n) (barrier : Fin n)
    (C : Fin n → State k) : Nat :=
  Phi (cutView ring barrier C)

/-! ### Finite-order helper lemmas -/

theorem rightNeighbor_val_of_ne_tail {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (hi : i ≠ tailCoord ring) :
    (ring.rightNeighbor i).val = i.val + 1 := by
  by_cases hlt : i.val + 1 < n
  · simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hlt]
  · exfalso
    have hval : i.val = n - 1 := by
      have hiLt := i.isLt
      omega
    apply hi
    apply Fin.ext
    exact hval

theorem rightNeighbor_lt_iff_of_ne_tail {n : Nat}
    (ring : DirectedRing n) (i ell : Fin n) (hi : i ≠ tailCoord ring) :
    (ring.rightNeighbor i).val < ell.val ↔ i.val + 1 < ell.val := by
  rw [rightNeighbor_val_of_ne_tail ring i hi]

/-- Predecessor coordinate of a positive coordinate. -/
def predCoord {n : Nat} (i : Fin n) (hi : 0 < i.val) : Fin n :=
  ⟨i.val - 1, by omega⟩

@[simp] theorem rightNeighbor_predCoord {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (hi : 0 < i.val) :
    ring.rightNeighbor (predCoord i hi) = i := by
  apply Fin.ext
  have hlt : i.val - 1 + 1 < n := by omega
  have heq : i.val - 1 + 1 = i.val := by omega
  simp [predCoord, DirectedRing.rightNeighbor, heq,
    Nat.mod_eq_of_lt i.isLt]

theorem not_dangerous_iff {n k : Nat} (X : Fin n → State k) :
    ¬ Dangerous X ↔
      ∀ p : Fin n, (X p).probe = true → Shielded X p := by
  constructor
  · intro h p hp
    apply Classical.byContradiction
    intro hs
    exact h ⟨p, hp, hs⟩
  · intro h
    rintro ⟨p, hp, hs⟩
    exact hs (h p hp)

theorem not_dangerous_of_leaders_eq_probes_subset {n k : Nat}
    (X Y : Fin n → State k)
    (hleaders : ∀ i, (Y i).leader = (X i).leader)
    (hprobes : ∀ i, (Y i).probe = true → (X i).probe = true)
    (hX : ¬ Dangerous X) : ¬ Dangerous Y := by
  rw [not_dangerous_iff] at hX ⊢
  intro p hp
  obtain ⟨ell, hlt, hell⟩ := hX p (hprobes p hp)
  exact ⟨ell, hlt, by rw [hleaders]; exact hell⟩

theorem leaderCount_eq_of_leaders_eq {n k : Nat}
    (X Y : Fin n → State k)
    (h : ∀ i, (Y i).leader = (X i).leader) :
    leaderCount Y = leaderCount X := by
  apply bitCount_congr
  exact h

theorem leaderCount_eq_zero_of_all_false {n k : Nat}
    (X : Fin n → State k)
    (h : ∀ i, (X i).leader = false) : leaderCount X = 0 := by
  unfold leaderCount
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [bitCount_succ, h 0]
      simp only [Bool.false_eq_true, if_false, Nat.zero_add]
      exact ih (X := fun i : Fin n => X i.succ) (fun i => h i.succ)

theorem phi_mono_of_same_leaders {n k : Nat}
    (X Y : Fin n → State k)
    (hleaders : ∀ i, (Y i).leader = (X i).leader)
    (hsafe : ¬ Dangerous X → ¬ Dangerous Y) :
    Phi Y ≤ Phi X := by
  have hcount := leaderCount_eq_of_leaders_eq X Y hleaders
  by_cases hX : Dangerous X
  · have hdy := dangerBit_le_one Y
    simp [Phi, dangerBit, hX] at *
    omega
  · have hY := hsafe hX
    simp [Phi, dangerBit, hX, hY, hcount]

theorem phi_mono_of_same_leaderCount {n k : Nat}
    (X Y : Fin n → State k)
    (hcount : leaderCount Y = leaderCount X)
    (hsafe : ¬ Dangerous X → ¬ Dangerous Y) :
    Phi Y ≤ Phi X := by
  by_cases hX : Dangerous X
  · have hdy := dangerBit_le_one Y
    simp [Phi, dangerBit, hX] at *
    omega
  · have hY := hsafe hX
    simp [Phi, dangerBit, hX, hY, hcount]

theorem phi_mono_of_single_leader_drop {n k : Nat}
    (X Y : Fin n → State k)
    (hdrop : leaderCount Y + 1 = leaderCount X) :
    Phi Y ≤ Phi X := by
  have hdy := dangerBit_le_one Y
  unfold Phi
  omega

theorem phi_mono_of_birth_consumes_danger {n k : Nat}
    (X Y : Fin n → State k)
    (hcount : leaderCount Y ≤ leaderCount X + 1)
    (hX : Dangerous X) (hY : ¬ Dangerous Y) :
    Phi Y ≤ Phi X := by
  simp [Phi, dangerBit, hX, hY] at *
  omega

theorem phi_eq_one_of_no_leaders {n k : Nat}
    (X : Fin n → State k)
    (h : ∀ i, (X i).leader = false) : Phi X = 1 := by
  have hc := leaderCount_eq_zero_of_all_false X h
  have hd := dangerBit_le_one X
  unfold Phi
  omega

/-! ### Dangerousness under the only nontrivial probe motions -/

theorem not_dangerous_after_forward_probe {n k : Nat}
    (ring : DirectedRing n) (X Y : Fin n → State k)
    (i : Fin n) (hi : i ≠ tailCoord ring)
    (hfollower : (X (ring.rightNeighbor i)).leader = false)
    (hleaders : ∀ j, (Y j).leader = (X j).leader)
    (hprobes : ∀ j, (Y j).probe = true →
      (X j).probe = true ∨
        (j = ring.rightNeighbor i ∧ (X i).probe = true))
    (hX : ¬ Dangerous X) : ¬ Dangerous Y := by
  rw [not_dangerous_iff] at hX ⊢
  intro p hp
  rcases hprobes p hp with hold | ⟨rfl, hsource⟩
  · obtain ⟨ell, hlt, hell⟩ := hX p hold
    exact ⟨ell, hlt, by rw [hleaders]; exact hell⟩
  · obtain ⟨ell, hlt, hell⟩ := hX i hsource
    have hne : ell ≠ ring.rightNeighbor i := by
      intro h
      subst ell
      simp [hfollower] at hell
    refine ⟨ell, ?_, by rw [hleaders]; exact hell⟩
    rw [rightNeighbor_val_of_ne_tail ring i hi]
    have hle : i.val + 1 ≤ ell.val := by omega
    have hvalne : i.val + 1 ≠ ell.val := by
      intro hval
      apply hne
      apply Fin.ext
      rw [rightNeighbor_val_of_ne_tail ring i hi]
      exact hval.symm
    omega

theorem not_dangerous_after_head_probe {n k : Nat}
    (ring : DirectedRing n) (X Y : Fin n → State k)
    (hheadFollower : (X ⟨0, ring.hn⟩).leader = false)
    (hleaders : ∀ j, (Y j).leader = (X j).leader)
    (hprobes : ∀ j, (Y j).probe = true →
      (X j).probe = true ∨ j = ⟨0, ring.hn⟩)
    (hhasLeader : ∃ ell, (X ell).leader = true)
    (hX : ¬ Dangerous X) : ¬ Dangerous Y := by
  rw [not_dangerous_iff] at hX ⊢
  intro p hp
  rcases hprobes p hp with hold | rfl
  · obtain ⟨ell, hlt, hell⟩ := hX p hold
    exact ⟨ell, hlt, by rw [hleaders]; exact hell⟩
  · obtain ⟨ell, hell⟩ := hhasLeader
    have hellne : ell ≠ ⟨0, ring.hn⟩ := by
      intro h
      subst ell
      simp [hheadFollower] at hell
    refine ⟨ell, ?_, by rw [hleaders]; exact hell⟩
    have hvalne : ell.val ≠ 0 := by
      intro h
      apply hellne
      apply Fin.ext
      exact h
    dsimp only
    omega

theorem phi_mono_of_head_probe_only {n k : Nat}
    (ring : DirectedRing n) (X Y : Fin n → State k)
    (hheadFollower : (X ⟨0, ring.hn⟩).leader = false)
    (hleaders : ∀ j, (Y j).leader = (X j).leader)
    (hprobes : ∀ j, (Y j).probe = true →
      (X j).probe = true ∨ j = ⟨0, ring.hn⟩) :
    Phi Y ≤ Phi X := by
  by_cases hX : Dangerous X
  · apply phi_mono_of_same_leaders X Y hleaders
    intro hn
    exact (hn hX).elim
  · by_cases hleader : ∃ ell, (X ell).leader = true
    · apply phi_mono_of_same_leaders X Y hleaders
      intro _
      exact not_dangerous_after_head_probe ring X Y hheadFollower
        hleaders hprobes hleader hX
    · have hallX : ∀ i, (X i).leader = false := by
        intro i
        cases hi : (X i).leader
        · rfl
        · exact False.elim (hleader ⟨i, hi⟩)
      have hallY : ∀ i, (Y i).leader = false := by
        intro i
        rw [hleaders, hallX]
      rw [phi_eq_one_of_no_leaders X hallX,
        phi_eq_one_of_no_leaders Y hallY]
      exact Nat.le_refl 1

theorem not_dangerous_rotate_of_head_probe_free {n k : Nat}
    (ring : DirectedRing n) (X : Fin n → State k)
    (hhead : (X ⟨0, ring.hn⟩).probe = false)
    (hX : ¬ Dangerous X) : ¬ Dangerous (rotateCut ring X) := by
  rw [not_dangerous_iff] at hX ⊢
  intro p hp
  change (X (ring.rightNeighbor p)).probe = true at hp
  have hrne : ring.rightNeighbor p ≠ ⟨0, ring.hn⟩ := by
    intro h
    rw [h, hhead] at hp
    contradiction
  have hrpos : 0 < (ring.rightNeighbor p).val := by
    have hrlt := (ring.rightNeighbor p).isLt
    have hrvalne : (ring.rightNeighbor p).val ≠ 0 := by
      intro hval
      apply hrne
      apply Fin.ext
      exact hval
    omega
  obtain ⟨ell, hlt, hell⟩ := hX (ring.rightNeighbor p) hp
  have helpos : 0 < ell.val := by omega
  let ell' := predCoord ell helpos
  refine ⟨ell', ?_, ?_⟩
  · have hpnot : p ≠ tailCoord ring := by
      intro h
      subst p
      simp at hrne
    have hpval := rightNeighbor_val_of_ne_tail ring p hpnot
    change p.val < ell.val - 1
    omega
  · change (X (ring.rightNeighbor ell')).leader = true
    simpa [ell'] using hell

theorem not_dangerous_rotate_of_tail_birth {n k : Nat}
    (ring : DirectedRing n) (X : Fin n → State k)
    (htailLeader : (X (tailCoord ring)).leader = true)
    (htailProbe : (X (tailCoord ring)).probe = false)
    (hheadProbe : (X ⟨0, ring.hn⟩).probe = false) :
    ¬ Dangerous (rotateCut ring X) := by
  apply not_dangerous_rotate_of_head_probe_free ring X hheadProbe
  exact not_dangerous_of_tail_leader ring X htailLeader htailProbe

/-! ### Relevant-field projection of one literal local step -/

theorem step_leaders_eq_of_local {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (e : Fin n)
    (hl : (transition hk (X e) (X (ring.rightNeighbor e))).1.leader =
      (X e).leader)
    (hr : (transition hk (X e) (X (ring.rightNeighbor e))).2.leader =
      (X (ring.rightNeighbor e)).leader) :
    ∀ i, (((protocol k hk).step ring X e) i).leader = (X i).leader := by
  intro i
  have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
  by_cases hie : i = e
  · subst i
    simpa [PopulationProtocol.step, protocol, hre] using hl
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, protocol, hre, hie] using hr
    · simp [PopulationProtocol.step, protocol, hie, hir]

theorem step_probes_subset_of_local {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (e : Fin n)
    (hl : (transition hk (X e) (X (ring.rightNeighbor e))).1.probe = true →
      (X e).probe = true)
    (hr : (transition hk (X e) (X (ring.rightNeighbor e))).2.probe = true →
      (X (ring.rightNeighbor e)).probe = true) :
    ∀ i, (((protocol k hk).step ring X e) i).probe = true →
      (X i).probe = true := by
  intro i hi
  have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
  by_cases hie : i = e
  · subst i
    apply hl
    simpa [PopulationProtocol.step, protocol, hre] using hi
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      apply hr
      simpa [PopulationProtocol.step, protocol, hre, hie] using hi
    · simpa [PopulationProtocol.step, protocol, hie, hir] using hi

theorem step_probes_forward_of_local {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (e : Fin n)
    (hl : (transition hk (X e) (X (ring.rightNeighbor e))).1.probe = true →
      (X e).probe = true)
    (hr : (transition hk (X e) (X (ring.rightNeighbor e))).2.probe = true →
      (X (ring.rightNeighbor e)).probe = true ∨ (X e).probe = true) :
    ∀ i, (((protocol k hk).step ring X e) i).probe = true →
      (X i).probe = true ∨
        (i = ring.rightNeighbor e ∧ (X e).probe = true) := by
  intro i hi
  have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
  by_cases hie : i = e
  · left
    subst i
    apply hl
    simpa [PopulationProtocol.step, protocol, hre] using hi
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rcases hr (by simpa [PopulationProtocol.step, protocol, hre, hie]
        using hi) with hold | hmoved
      · exact Or.inl hold
      · exact Or.inr ⟨rfl, hmoved⟩
    · left
      simpa [PopulationProtocol.step, protocol, hie, hir] using hi

theorem step_leaderCount_single_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (e : Fin n)
    (hl : (transition hk (X e) (X (ring.rightNeighbor e))).1.leader =
      (X e).leader)
    (hbefore : (X (ring.rightNeighbor e)).leader = true)
    (hafter :
      (transition hk (X e) (X (ring.rightNeighbor e))).2.leader = false) :
    leaderCount ((protocol k hk).step ring X e) + 1 = leaderCount X := by
  apply bitCount_single_drop
    (fun i => (X i).leader)
    (fun i => (((protocol k hk).step ring X e) i).leader)
    (ring.rightNeighbor e) hbefore
  · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    simpa [PopulationProtocol.step, protocol, hre] using hafter
  · intro i hir
    have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    by_cases hie : i = e
    · subst i
      simpa [PopulationProtocol.step, protocol, hre] using hl
    · simp [PopulationProtocol.step, protocol, hie, hir]

theorem step_leaderCount_birth_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (e : Fin n)
    (hborn :
      (transition hk (X e) (X (ring.rightNeighbor e))).1.leader = true)
    (hr : (transition hk (X e) (X (ring.rightNeighbor e))).2.leader =
      (X (ring.rightNeighbor e)).leader) :
    leaderCount ((protocol k hk).step ring X e) ≤ leaderCount X + 1 := by
  apply bitCount_single_birth_le
    (fun i => (X i).leader)
    (fun i => (((protocol k hk).step ring X e) i).leader) e
  · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    simpa [PopulationProtocol.step, protocol, hre] using hborn
  · intro i hie
    have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, protocol, hre, hie] using hr
    · simp [PopulationProtocol.step, protocol, hie, hir]

/-! ## Full literal one-step monotonicity in canonical cut coordinates -/

/-- Exactly one barrier, at the wrap edge from coordinate `n-1` to zero. -/
def CanonicalOneBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k) : Prop :=
  ∀ i : Fin n,
    IsBarrier hk (X i) (X (ring.rightNeighbor i)) ↔ i = tailCoord ring

instance instDecidableAdvanceReady {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k) (e : Fin n) :
    Decidable (AdvanceReady hk ring X e) := by
  unfold AdvanceReady PairAdvanceReady
  infer_instance

/-- A label write moves the cut one edge clockwise; every other branch keeps
the current cut. -/
def cutSuccessor {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (e : Fin n) : Fin n → State k :=
  let D : Fin n → State k :=
    fun j => ((protocol k hk).step ring X e) j
  if AdvanceReady hk ring X e then rotateCut ring D else D

/-- Full pathwise monotonicity of `Phi` for the exact Protocol-6 transition.

The label-write branch is included: its post-state is viewed after rotating
the cut to the successor barrier. -/
theorem canonical_phi_step_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (hbar : CanonicalOneBarrier hk ring X)
    (e : Fin n) : Phi (cutSuccessor hk ring X e) ≤ Phi X := by
  have hn2 : 1 < n := by omega
  let t := tailCoord ring
  let r := ring.rightNeighbor e
  let D := (protocol k hk).step ring X e
  unfold cutSuccessor
  by_cases het : e = t
  · subst e
    have htailEq : tailCoord ring = t := rfl
    have hzeroTail : (⟨0, ring.hn⟩ : Fin n) ≠ t := by
      intro h
      have hv := congrArg Fin.val h
      change 0 = n - 1 at hv
      omega
    have hBarrier : IsBarrier hk (X t) (X (ring.rightNeighbor t)) :=
      (hbar t).2 rfl
    have hrt : ring.rightNeighbor t = ⟨0, ring.hn⟩ := by
      simpa [t] using rightNeighbor_tailCoord ring
    have hBarrier0 : IsBarrier hk (X t) (X ⟨0, ring.hn⟩) := by
      simpa [hrt] using hBarrier
    cases htailProbe : (X t).probe with
    | false =>
      cases hphase : (X t).phase with
      | false =>
        have hready : ¬ AdvanceReady hk ring X t := by
          intro h
          exact Bool.noConfusion (h.2.1.symm.trans hphase)
        simp only [hready, if_false]
        cases hheadLeader : (X (ring.rightNeighbor t)).leader with
        | false =>
          have hleaders := step_leaders_eq_of_local hk ring hn2 X t
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase])
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadLeader])
          apply phi_mono_of_head_probe_only ring X
            ((protocol k hk).step ring X t) (by simpa [hrt] using hheadLeader)
            hleaders
          intro i hi
          have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
          by_cases hit : i = t
          · subst i
            simp [PopulationProtocol.step, protocol, transition, hBarrier,
              barrierStep, probeHitsBarrier, htailProbe, hphase, hre] at hi
          · by_cases hir : i = ring.rightNeighbor t
            · exact Or.inr (by simpa [hir, hrt])
            · exact Or.inl (by simpa [PopulationProtocol.step, protocol,
                hit, hir] using hi)
        | true =>
          have hleaders := step_leaders_eq_of_local hk ring hn2 X t
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase])
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadLeader])
          apply phi_mono_of_same_leaders X
            ((protocol k hk).step ring X t) hleaders
          intro hsafe
          apply not_dangerous_of_leaders_eq_probes_subset X
            ((protocol k hk).step ring X t) hleaders
          · apply step_probes_subset_of_local hk ring hn2 X t
            · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
                htailProbe, hphase]
            · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
                htailProbe, hphase, hheadLeader]
          · exact hsafe
      | true =>
        cases hheadProbe : (X (ring.rightNeighbor t)).probe with
        | false =>
          have hready : AdvanceReady hk ring X t :=
            ⟨hBarrier, hphase, hheadProbe⟩
          simp only [hready, if_true]
          have hleadersD := step_leaders_eq_of_local hk ring hn2 X t
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
          apply phi_mono_of_same_leaderCount X
            (rotateCut ring ((protocol k hk).step ring X t))
          · calc
              leaderCount
                  (rotateCut ring ((protocol k hk).step ring X t)) =
                  leaderCount ((protocol k hk).step ring X t) := by
                    exact leaderCount_rotateCut ring
                      (fun i => ((protocol k hk).step ring X t) i)
              _ = leaderCount X :=
                leaderCount_eq_of_leaders_eq X _ hleadersD
          · intro hsafe
            apply not_dangerous_rotate_of_head_probe_free ring
            · have hheadProbe0 : (X ⟨0, ring.hn⟩).probe = false := by
                simpa [hrt] using hheadProbe
              have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
              simp [PopulationProtocol.step, protocol, transition, hBarrier,
                hBarrier0,
                barrierStep, probeHitsBarrier, htailProbe, hphase,
                hheadProbe, hheadProbe0, hrt, hre, hzeroTail]
            · apply not_dangerous_of_leaders_eq_probes_subset X _ hleadersD
              · apply step_probes_subset_of_local hk ring hn2 X t
                · simp [transition, hBarrier, barrierStep,
                    probeHitsBarrier, htailProbe, hphase, hheadProbe]
                · simp [transition, hBarrier, barrierStep,
                    probeHitsBarrier, htailProbe, hphase, hheadProbe]
              · exact hsafe
        | true =>
          have hready : ¬ AdvanceReady hk ring X t := by
            intro h
            exact Bool.noConfusion (h.2.2.symm.trans hheadProbe)
          simp only [hready, if_false]
          have hleaders := step_leaders_eq_of_local hk ring hn2 X t
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
          apply phi_mono_of_same_leaders X _ hleaders
          intro hsafe
          apply not_dangerous_of_leaders_eq_probes_subset X _ hleaders
          · apply step_probes_subset_of_local hk ring hn2 X t
            · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
                htailProbe, hphase, hheadProbe]
            · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
                htailProbe, hphase, hheadProbe]
          · exact hsafe
    | true =>
      have hOldDanger := dangerous_of_tail_probe ring X htailProbe
      cases hphase : (X t).phase with
      | false =>
        have hready : ¬ AdvanceReady hk ring X t := by
          intro h
          exact Bool.noConfusion (h.2.1.symm.trans hphase)
        simp only [hready, if_false]
        have hcount := step_leaderCount_birth_le hk ring hn2 X t
          (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase])
          (by
            simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase]
            split <;> rfl)
        apply phi_mono_of_birth_consumes_danger X _ hcount hOldDanger
        apply not_dangerous_of_tail_leader ring
        · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
          simp [PopulationProtocol.step, protocol, transition, hBarrier,
            barrierStep, probeHitsBarrier, htailProbe, hphase, hre, htailEq]
        · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
          simp [PopulationProtocol.step, protocol, transition, hBarrier,
            barrierStep, probeHitsBarrier, htailProbe, hphase, hre, htailEq]
      | true =>
        cases hheadProbe : (X (ring.rightNeighbor t)).probe with
        | false =>
          have hready : AdvanceReady hk ring X t :=
            ⟨hBarrier, hphase, hheadProbe⟩
          simp only [hready, if_true]
          have hcountD := step_leaderCount_birth_le hk ring hn2 X t
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
          have hcount : leaderCount
              (rotateCut ring ((protocol k hk).step ring X t)) ≤
              leaderCount X + 1 := by
            calc
              leaderCount
                  (rotateCut ring ((protocol k hk).step ring X t)) =
                  leaderCount ((protocol k hk).step ring X t) := by
                    exact leaderCount_rotateCut ring
                      (fun i => ((protocol k hk).step ring X t) i)
              _ ≤ leaderCount X + 1 := hcountD
          apply phi_mono_of_birth_consumes_danger X _ hcount hOldDanger
          apply not_dangerous_rotate_of_tail_birth ring
          · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
            simp [PopulationProtocol.step, protocol, transition, hBarrier,
              barrierStep, probeHitsBarrier, htailProbe, hphase,
              hheadProbe, hre, htailEq]
          · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
            simp [PopulationProtocol.step, protocol, transition, hBarrier,
              barrierStep, probeHitsBarrier, htailProbe, hphase,
              hheadProbe, hre, htailEq]
          · have hheadProbe0 : (X ⟨0, ring.hn⟩).probe = false := by
              simpa [hrt] using hheadProbe
            have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
            simp [PopulationProtocol.step, protocol, transition, hBarrier,
              hBarrier0,
              barrierStep, probeHitsBarrier, htailProbe, hphase,
              hheadProbe, hheadProbe0, hrt, hre, hzeroTail]
        | true =>
          have hready : ¬ AdvanceReady hk ring X t := by
            intro h
            exact Bool.noConfusion (h.2.2.symm.trans hheadProbe)
          simp only [hready, if_false]
          have hcount := step_leaderCount_birth_le hk ring hn2 X t
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
            (by simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe])
          apply phi_mono_of_birth_consumes_danger X _ hcount hOldDanger
          apply not_dangerous_of_tail_leader ring
          · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
            simp [PopulationProtocol.step, protocol, transition, hBarrier,
              barrierStep, probeHitsBarrier, htailProbe, hphase,
              hheadProbe, hre, htailEq]
          · have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
            simp [PopulationProtocol.step, protocol, transition, hBarrier,
              barrierStep, probeHitsBarrier, htailProbe, hphase,
              hheadProbe, hre, htailEq]
  · have hNonBarrier :
        ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
      intro h
      exact het ((hbar e).1 h)
    have hready : ¬ AdvanceReady hk ring X e := by
      intro h
      exact hNonBarrier h.1
    simp only [hready, if_false]
    cases hrespLeader : (X (ring.rightNeighbor e)).leader with
    | false =>
      cases hrespBullet : (X (ring.rightNeighbor e)).bullet with
      | false =>
        cases hinitProbe : (X e).probe with
        | false =>
          have hleaders := step_leaders_eq_of_local hk ring hn2 X e
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
          apply phi_mono_of_same_leaders X _ hleaders
          intro hsafe
          apply not_dangerous_of_leaders_eq_probes_subset X _ hleaders
          · apply step_probes_subset_of_local hk ring hn2 X e
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
          · exact hsafe
        | true =>
          have hleaders := step_leaders_eq_of_local hk ring hn2 X e
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
          apply phi_mono_of_same_leaders X _ hleaders
          intro hsafe
          apply not_dangerous_after_forward_probe ring X _ e het hrespLeader
            hleaders
          · apply step_probes_forward_of_local hk ring hn2 X e
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
          · exact hsafe
      | true =>
        cases hinitProbe : (X e).probe with
        | false =>
          have hleaders := step_leaders_eq_of_local hk ring hn2 X e
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
          apply phi_mono_of_same_leaders X _ hleaders
          intro hsafe
          apply not_dangerous_of_leaders_eq_probes_subset X _ hleaders
          · apply step_probes_subset_of_local hk ring hn2 X e
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
          · exact hsafe
        | true =>
          have hleaders := step_leaders_eq_of_local hk ring hn2 X e
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
            (by simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe])
          apply phi_mono_of_same_leaders X _ hleaders
          intro hsafe
          apply not_dangerous_after_forward_probe ring X _ e het hrespLeader
            hleaders
          · apply step_probes_forward_of_local hk ring hn2 X e
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
            · simp [transition, hNonBarrier, nonBarrierStep,
                hrespLeader, hrespBullet, hinitProbe]
          · exact hsafe
    | true =>
      cases hrespBullet : (X (ring.rightNeighbor e)).bullet with
      | false =>
        have hleaders := step_leaders_eq_of_local hk ring hn2 X e
          (by simp [transition, hNonBarrier, nonBarrierStep,
            hrespLeader, hrespBullet])
          (by simp [transition, hNonBarrier, nonBarrierStep,
            hrespLeader, hrespBullet])
        apply phi_mono_of_same_leaders X _ hleaders
        intro hsafe
        apply not_dangerous_of_leaders_eq_probes_subset X _ hleaders
        · apply step_probes_subset_of_local hk ring hn2 X e
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet]
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet]
        · exact hsafe
      | true =>
        have hdrop := step_leaderCount_single_drop hk ring hn2 X e
          (by simp [transition, hNonBarrier, nonBarrierStep,
            hrespLeader, hrespBullet]) hrespLeader
          (by simp [transition, hNonBarrier, nonBarrierStep,
            hrespLeader, hrespBullet])
        exact phi_mono_of_single_leader_drop X _ hdrop

/-! ## Physical one-barrier frames and the lifted `Phi` theorem -/

/-- The full configuration has exactly one barrier, at physical edge `b`. -/
def OneBarrierAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Prop :=
  ∀ e : Fin n,
    BarrierAt hk ring (labelsOf C) e ↔ e = b

instance instDecidableOneBarrierAt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n) :
    Decidable (OneBarrierAt hk ring C b) := by
  unfold OneBarrierAt BarrierAt
  infer_instance

/-- Existential one-barrier predicate, with `OneBarrierAt` retaining the cut
witness needed by `PhiAt`. -/
def OneBarrier {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) : Prop :=
  ∃ b : Fin n, OneBarrierAt hk ring C b

theorem oneBarrierAt_barrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (h : OneBarrierAt hk ring C b) :
    BarrierAt hk ring (labelsOf C) b := (h b).2 rfl

theorem oneBarrierAt_barrierCount_eq_one {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (h : OneBarrierAt hk ring C b) :
    barrierCount hk ring (labelsOf C) = 1 := by
  let S := barrierSupport hk ring (labelsOf C)
  have hb : b ∈ S := by
    exact (mem_barrierSupport_iff hk ring (labelsOf C) b).2
      (oneBarrierAt_barrier hk ring C b h)
  have hn := barrierSupport_nodup hk ring (labelsOf C)
  change S.Nodup at hn
  have hall : ∀ e, e ∈ S → e = b := by
    intro e he
    apply (h e).1
    exact (mem_barrierSupport_iff hk ring (labelsOf C) e).1 he
  cases hs : S with
  | nil => simp [hs] at hb
  | cons a rest =>
      have ha : a = b := hall a (by simp [hs])
      cases hr : rest with
      | nil =>
          change S.length = 1
          rw [hs, hr]
          rfl
      | cons c rest' =>
          have hc : c = b := hall c (by simp [hs, hr])
          rw [hs, List.nodup_cons] at hn
          exact False.elim (hn.1 (by simp [hr, ha, hc]))

theorem exists_barrier_of_barrierCount_eq_one {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (hcount : barrierCount hk ring (labelsOf C) = 1) :
    ∃ b, BarrierAt hk ring (labelsOf C) b := by
  unfold barrierCount at hcount
  rw [List.length_eq_one_iff] at hcount
  obtain ⟨b, hb⟩ := hcount
  refine ⟨b, ?_⟩
  apply (mem_barrierSupport_iff hk ring (labelsOf C) b).1
  simp [hb]

theorem oneBarrierAt_of_count_one_of_unique {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (hcount : barrierCount hk ring (labelsOf C) = 1)
    (hunique : ∀ e, BarrierAt hk ring (labelsOf C) e → e = b) :
    OneBarrierAt hk ring C b := by
  obtain ⟨q, hq⟩ := exists_barrier_of_barrierCount_eq_one
    hk ring C hcount
  have hqb : q = b := hunique q hq
  intro e
  constructor
  · exact hunique e
  · intro heb
    subst e
    simpa [hqb] using hq

theorem canonicalOneBarrier_cutView {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (h : OneBarrierAt hk ring C b) :
    CanonicalOneBarrier hk ring (cutView ring b C) := by
  intro i
  have hgeom := cutPos_rightNeighbor ring b i
  have hjournal := barrierAt_labelsOf_iff hk ring C (cutPos ring b i)
  constructor
  · intro hi
    have hp : BarrierAt hk ring (labelsOf C) (cutPos ring b i) := by
      apply hjournal.2
      simpa [cutView, hgeom] using hi
    have hpos : cutPos ring b i = b := (h (cutPos ring b i)).1 hp
    apply cutPos_injective ring b
    rw [hpos, cutPos_tailCoord]
  · intro hi
    subst i
    have hp : BarrierAt hk ring (labelsOf C)
        (cutPos ring b (tailCoord ring)) := by
      apply (h (cutPos ring b (tailCoord ring))).2
      exact cutPos_tailCoord ring b
    have hj := hjournal.1 hp
    simpa [cutView, hgeom] using hj

theorem advanceReady_cutView_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b i : Fin n) :
    AdvanceReady hk ring (cutView ring b C) i ↔
      AdvanceReady hk ring C (cutPos ring b i) := by
  simp only [AdvanceReady, PairAdvanceReady, cutView,
    cutPos_rightNeighbor]

/-- The exact next barrier location: unchanged outside the label-write branch,
and advanced one physical edge by a label write.  The count-one conclusion is
obtained from `protocol_step_preserves_oneBarrier`; the rest identifies that
unique support element. -/
theorem oneBarrierAt_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let D := (protocol k hk).step ring C e
    OneBarrierAt hk ring D
      (if AdvanceReady hk ring C e then ring.rightNeighbor b else b) := by
  let D : Fin n → State k :=
    fun j => ((protocol k hk).step ring C e) j
  have hcountC := oneBarrierAt_barrierCount_eq_one hk ring C b hone
  have hcountD := protocol_step_preserves_oneBarrier hk ring hn2 C e
    hndvd hcountC
  by_cases hready : AdvanceReady hk ring C e
  · have heb : e = b := by
      apply (hone e).1
      exact (barrierAt_labelsOf_iff hk ring C e).2 hready.1
    subst e
    simp only [hready, if_true]
    apply oneBarrierAt_of_count_one_of_unique hk ring D
      (ring.rightNeighbor b) hcountD
    intro j hj
    by_cases hjb : j = b
    · subst j
      exact False.elim
        ((protocol_advance_repairs_edge hk ring hn2 C b hready) hj)
    by_cases hjr : j = ring.rightNeighbor b
    · exact hjr
    · have hlabels := labelsOf_step_eq_advance_of_ready
          hk ring hn2 C b hready
      have hsame := defect_advance_other hk ring (labelsOf C) b j hjb hjr
      have hnew : defect hk ring (labelsOf D) j ≠ zeroResidue hk := hj
      have hold : defect hk ring (labelsOf C) j ≠ zeroResidue hk := by
        intro hz
        apply hnew
        rw [hlabels, hsame, hz]
      have holdBarrier : BarrierAt hk ring (labelsOf C) j := hold
      exact False.elim (hjb ((hone j).1 holdBarrier))
  · simp only [hready, if_false]
    have hlabels := labelsOf_step_eq_self_of_not_ready hk ring C e hready
    intro j
    rw [← hone j]
    unfold BarrierAt
    rw [hlabels]

/-- Physical form of full one-step `Phi` monotonicity.  It returns the exact
successor cut together with the preserved one-barrier frame. -/
theorem oneBarrier_phi_step_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b e : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let D := (protocol k hk).step ring C e
    let b' := if AdvanceReady hk ring C e then ring.rightNeighbor b else b
    OneBarrierAt hk ring D b' ∧ PhiAt ring b' D ≤ PhiAt ring b C := by
  let D := (protocol k hk).step ring C e
  let b' := if AdvanceReady hk ring C e then ring.rightNeighbor b else b
  have hn2 : 1 < n := by omega
  have hnext : OneBarrierAt hk ring D b' := by
    dsimp only [D, b']
    exact oneBarrierAt_step hk ring hn2 C b e hndvd hone
  refine ⟨hnext, ?_⟩
  let i := cutCoord ring b e
  let X := cutView ring b C
  have hpos : cutPos ring b i = e := by
    simp [i]
  have hview : cutView ring b D = (protocol k hk).step ring X i := by
    dsimp only [D, X]
    simpa [hpos] using cutView_step_at_cutPos hk ring b C i
  have hcanon : CanonicalOneBarrier hk ring X := by
    exact canonicalOneBarrier_cutView hk ring C b hone
  have hreadyIff : AdvanceReady hk ring X i ↔ AdvanceReady hk ring C e := by
    simpa [hpos] using advanceReady_cutView_iff hk ring C b i
  have hmono := canonical_phi_step_le hk ring hn3 X hcanon i
  by_cases hready : AdvanceReady hk ring C e
  · have hreadyX : AdvanceReady hk ring X i := hreadyIff.2 hready
    dsimp only [b', PhiAt]
    simp only [hready, if_true]
    change Phi (cutView ring (ring.rightNeighbor b) D) ≤ Phi X
    have hrotateView :
        cutView ring (ring.rightNeighbor b) D =
          rotateCut ring (cutView ring b D) := by
      exact cutView_nextBarrier ring b (fun j => D j)
    rw [hrotateView, hview]
    unfold cutSuccessor at hmono
    simp only [hreadyX, if_true] at hmono
    exact hmono
  · have hreadyX : ¬ AdvanceReady hk ring X i := by
      exact fun h => hready (hreadyIff.1 h)
    dsimp only [b', PhiAt]
    simp only [hready, if_false]
    rw [hview]
    unfold cutSuccessor at hmono
    simp only [hreadyX, if_false] at hmono
    exact hmono

/-! ## Exact clean region -/

/-- A mark is either of the two mobile control tokens. -/
def Marked {k : Nat} (q : State k) : Prop :=
  q.bullet = true ∨ q.probe = true

instance instDecidableMarked {k : Nat} (q : State k) :
    Decidable (Marked q) := by
  unfold Marked
  infer_instance

/-- The leader and mark part of AAFJ cleanliness in canonical barrier-cut
coordinates.  Every mark is strictly between the barrier head and the unique
leader; consequently both the leader endpoint and the barrier tail are
mark-free. -/
def CleanData {n k : Nat} (X : Fin n → State k) (ell : Fin n) : Prop :=
  (X ell).leader = true ∧
    (∀ i : Fin n, (X i).leader = true → i = ell) ∧
    ∀ i : Fin n, Marked (X i) → i.val < ell.val

instance instDecidableCleanData {n k : Nat} (X : Fin n → State k)
    (ell : Fin n) : Decidable (CleanData X ell) := by
  unfold CleanData
  infer_instance

/-- Syntactic AAFJ clean region in the canonical unique-barrier cut. -/
def CanonicalClean {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (ell : Fin n) : Prop :=
  CanonicalOneBarrier hk ring X ∧ CleanData X ell

instance instDecidableCanonicalClean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k) (ell : Fin n) :
    Decidable (CanonicalClean hk ring X ell) := by
  unfold CanonicalClean CanonicalOneBarrier
  infer_instance

theorem cleanData_leader_false_of_ne {n k : Nat}
    {X : Fin n → State k} {ell i : Fin n}
    (hclean : CleanData X ell) (hi : i ≠ ell) :
    (X i).leader = false := by
  cases hbit : (X i).leader with
  | false => rfl
  | true => exact False.elim (hi (hclean.2.1 i hbit))

theorem cleanData_markFree_of_not_lt {n k : Nat}
    {X : Fin n → State k} {ell i : Fin n}
    (hclean : CleanData X ell) (hi : ¬ i.val < ell.val) :
    (X i).bullet = false ∧ (X i).probe = false := by
  constructor
  · cases hb : (X i).bullet with
    | false => rfl
    | true => exact False.elim (hi (hclean.2.2 i (Or.inl hb)))
  · cases hp : (X i).probe with
    | false => rfl
    | true => exact False.elim (hi (hclean.2.2 i (Or.inr hp)))

theorem cleanData_leader_markFree {n k : Nat}
    {X : Fin n → State k} {ell : Fin n}
    (hclean : CleanData X ell) :
    (X ell).bullet = false ∧ (X ell).probe = false := by
  exact cleanData_markFree_of_not_lt hclean (by omega)

theorem cleanData_tail_markFree {n k : Nat} (ring : DirectedRing n)
    {X : Fin n → State k} {ell : Fin n}
    (hclean : CleanData X ell) :
    (X (tailCoord ring)).bullet = false ∧
      (X (tailCoord ring)).probe = false := by
  apply cleanData_markFree_of_not_lt hclean
  change ¬ n - 1 < ell.val
  have hell := ell.isLt
  omega

/-- Local state conditions sufficient to preserve `CleanData` across a
packaged protocol step whose cut does not rotate. -/
theorem cleanData_step_of_local {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (ell e : Fin n) (hclean : CleanData X ell)
    (hl : (transition hk (X e) (X (ring.rightNeighbor e))).1.leader =
      (X e).leader)
    (hr : (transition hk (X e) (X (ring.rightNeighbor e))).2.leader =
      (X (ring.rightNeighbor e)).leader)
    (hmarkL : Marked
        (transition hk (X e) (X (ring.rightNeighbor e))).1 →
      e.val < ell.val)
    (hmarkR : Marked
        (transition hk (X e) (X (ring.rightNeighbor e))).2 →
      (ring.rightNeighbor e).val < ell.val) :
    CleanData ((protocol k hk).step ring X e) ell := by
  have hleaders := step_leaders_eq_of_local hk ring hn2 X e hl hr
  refine ⟨?_, ?_, ?_⟩
  · rw [hleaders]
    exact hclean.1
  · intro i hi
    apply hclean.2.1 i
    rw [← hleaders i]
    exact hi
  · intro i hi
    have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    by_cases hie : i = e
    · subst i
      apply hmarkL
      simpa [PopulationProtocol.step, protocol, hre] using hi
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        apply hmarkR
        simpa [PopulationProtocol.step, protocol, hre, hie] using hi
      · apply hclean.2.2 i
        simpa [PopulationProtocol.step, protocol, hie, hir] using hi

theorem rightNeighbor_leftNeighbor_clean {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

theorem leftNeighbor_rightNeighbor_clean {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

theorem leftNeighbor_val_of_pos {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (hi : 0 < i.val) :
    (ring.leftNeighbor i).val = i.val - 1 := by
  simp only [DirectedRing.leftNeighbor]
  have heq : i.val + n - 1 = n + (i.val - 1) := by omega
  rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]

/-- Rotating the cut preserves clean confinement provided the old head, which
becomes the new tail, is mark-free.  The same physical leader moves to its
predecessor coordinate. -/
theorem cleanData_rotateCut {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k) (ell : Fin n) (hclean : CleanData X ell)
    (hhead : (X ⟨0, ring.hn⟩).bullet = false ∧
      (X ⟨0, ring.hn⟩).probe = false) :
    CleanData (rotateCut ring X) (ring.leftNeighbor ell) := by
  refine ⟨?_, ?_, ?_⟩
  · change (X (ring.rightNeighbor (ring.leftNeighbor ell))).leader = true
    rw [rightNeighbor_leftNeighbor_clean]
    exact hclean.1
  · intro i hi
    change (X (ring.rightNeighbor i)).leader = true at hi
    have hri : ring.rightNeighbor i = ell := hclean.2.1 _ hi
    apply Fin.ext
    have h := congrArg Fin.val
      (congrArg (ring.leftNeighbor) hri)
    simpa [leftNeighbor_rightNeighbor_clean] using h
  · intro i hi
    change Marked (X (ring.rightNeighbor i)) at hi
    have hbefore := hclean.2.2 (ring.rightNeighbor i) hi
    by_cases hell0 : ell.val = 0
    · omega
    have hellpos : 0 < ell.val := by omega
    have hleft := leftNeighbor_val_of_pos ring ell hellpos
    by_cases hit : i = tailCoord ring
    · subst i
      have hz : ring.rightNeighbor (tailCoord ring) = ⟨0, ring.hn⟩ :=
        rightNeighbor_tailCoord ring
      rw [hz] at hi
      rcases hi with hb | hp
      · rw [hhead.1] at hb
        contradiction
      · rw [hhead.2] at hp
        contradiction
    · have hright := rightNeighbor_val_of_ne_tail ring i hit
      rw [hleft]
      rw [hright] at hbefore
      omega

theorem cutCoord_nextBarrier {n : Nat} (ring : DirectedRing n)
    (barrier p : Fin n) :
    cutCoord ring (ring.rightNeighbor barrier) p =
      ring.leftNeighbor (cutCoord ring barrier p) := by
  apply Fin.ext
  have hpos :
      cutPos ring barrier
          (ring.rightNeighbor
            (cutCoord ring (ring.rightNeighbor barrier) p)) = p := by
    rw [← cutPos_nextBarrier]
    exact cutPos_cutCoord ring (ring.rightNeighbor barrier) p
  have hcoord :
      ring.rightNeighbor
          (cutCoord ring (ring.rightNeighbor barrier) p) =
        cutCoord ring barrier p := by
    apply cutPos_injective ring barrier
    rw [hpos, cutPos_cutCoord]
  have hleft := congrArg (ring.leftNeighbor) hcoord
  simpa only [leftNeighbor_rightNeighbor_clean] using congrArg Fin.val hleft

/-- Branch-complete preservation of clean leader/mark data for the literal
transition.  In the label-write branch both the configuration and the leader
coordinate are rotated to the new barrier cut. -/
theorem canonical_cleanData_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (hbar : CanonicalOneBarrier hk ring X)
    (ell e : Fin n) (hclean : CleanData X ell) :
    CleanData (cutSuccessor hk ring X e)
      (if AdvanceReady hk ring X e then ring.leftNeighbor ell else ell) := by
  have hn2 : 1 < n := by omega
  let t := tailCoord ring
  unfold cutSuccessor
  by_cases het : e = t
  · subst e
    have hzeroTail : (⟨0, ring.hn⟩ : Fin n) ≠ t := by
      intro h
      have hv := congrArg Fin.val h
      change 0 = n - 1 at hv
      omega
    have hBarrier : IsBarrier hk (X t) (X (ring.rightNeighbor t)) :=
      (hbar t).2 rfl
    have hrt : ring.rightNeighbor t = ⟨0, ring.hn⟩ := by
      simpa [t] using rightNeighbor_tailCoord ring
    have hBarrier0 : IsBarrier hk (X t) (X ⟨0, ring.hn⟩) := by
      simpa [hrt] using hBarrier
    have htailFree := cleanData_tail_markFree ring hclean
    have htailBullet : (X t).bullet = false := by
      simpa [t] using htailFree.1
    have htailProbe : (X t).probe = false := by
      simpa [t] using htailFree.2
    cases hphase : (X t).phase with
    | false =>
      have hready : ¬ AdvanceReady hk ring X t := by
        intro h
        exact Bool.noConfusion (h.2.1.symm.trans hphase)
      simp only [hready, if_false]
      cases hheadLeader : (X (ring.rightNeighbor t)).leader with
      | false =>
        have hheadNe : (ring.rightNeighbor t) ≠ ell := by
          intro h
          rw [h, hclean.1] at hheadLeader
          contradiction
        have hheadLt : (ring.rightNeighbor t).val < ell.val := by
          rw [hrt]
          have hval : ell.val ≠ 0 := by
            intro hv
            apply hheadNe
            apply Fin.ext
            simpa [hrt] using hv.symm
          change 0 < ell.val
          omega
        apply cleanData_step_of_local hk ring hn2 X ell t hclean
        · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase]
        · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase, hheadLeader]
        · intro hm
          apply hclean.2.2 t
          simpa [Marked, transition, hBarrier, barrierStep,
            probeHitsBarrier, htailProbe, hphase] using hm
        · intro _
          exact hheadLt
      | true =>
        apply cleanData_step_of_local hk ring hn2 X ell t hclean
        · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase]
        · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase, hheadLeader]
        · intro hm
          apply hclean.2.2 t
          simpa [Marked, transition, hBarrier, barrierStep,
            probeHitsBarrier, htailProbe, hphase] using hm
        · intro hm
          apply hclean.2.2 (ring.rightNeighbor t)
          simpa [Marked, transition, hBarrier, barrierStep,
            probeHitsBarrier, htailProbe, hphase, hheadLeader] using hm
    | true =>
      cases hheadProbe : (X (ring.rightNeighbor t)).probe with
      | false =>
        have hready : AdvanceReady hk ring X t :=
          ⟨hBarrier, hphase, hheadProbe⟩
        simp only [hready, if_true]
        have hD : CleanData ((protocol k hk).step ring X t) ell := by
          apply cleanData_step_of_local hk ring hn2 X ell t hclean
          · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe]
          · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
              htailProbe, hphase, hheadProbe]
          · intro hm
            apply hclean.2.2 t
            simpa [Marked, transition, hBarrier, barrierStep,
              probeHitsBarrier, htailProbe, hphase, hheadProbe] using hm
          · intro hm
            simp [Marked, transition, hBarrier, barrierStep,
              probeHitsBarrier, htailProbe, hphase, hheadProbe] at hm
        apply cleanData_rotateCut ring
          ((protocol k hk).step ring X t) ell hD
        have hheadProbe0 : (X ⟨0, ring.hn⟩).probe = false := by
          simpa [hrt] using hheadProbe
        have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 t
        constructor <;>
          simp [PopulationProtocol.step, protocol, transition, hBarrier,
            hBarrier0, barrierStep, probeHitsBarrier, htailProbe, hphase,
            hheadProbe, hheadProbe0, hrt, hre, hzeroTail]
      | true =>
        have hready : ¬ AdvanceReady hk ring X t := by
          intro h
          exact Bool.noConfusion (h.2.2.symm.trans hheadProbe)
        simp only [hready, if_false]
        apply cleanData_step_of_local hk ring hn2 X ell t hclean
        · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase, hheadProbe]
        · simp [transition, hBarrier, barrierStep, probeHitsBarrier,
            htailProbe, hphase, hheadProbe]
        · intro hm
          apply hclean.2.2 t
          simpa [Marked, transition, hBarrier, barrierStep,
            probeHitsBarrier, htailProbe, hphase, hheadProbe] using hm
        · intro hm
          apply hclean.2.2 (ring.rightNeighbor t)
          simpa [Marked, transition, hBarrier, barrierStep,
            probeHitsBarrier, htailProbe, hphase, hheadProbe] using hm
  · have hNonBarrier :
        ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
      intro h
      exact het ((hbar e).1 h)
    have hready : ¬ AdvanceReady hk ring X e := by
      intro h
      exact hNonBarrier h.1
    simp only [hready, if_false]
    have heTail : e ≠ tailCoord ring := by simpa [t] using het
    have hrval := rightNeighbor_val_of_ne_tail ring e heTail
    cases hrespLeader : (X (ring.rightNeighbor e)).leader with
    | true =>
      have hrEll : ring.rightNeighbor e = ell :=
        hclean.2.1 (ring.rightNeighbor e) hrespLeader
      have hleaderFree := cleanData_leader_markFree hclean
      have hrespBullet : (X (ring.rightNeighbor e)).bullet = false := by
        simpa [hrEll] using hleaderFree.1
      have heLt : e.val < ell.val := by
        have hval := congrArg Fin.val hrEll
        rw [hrval] at hval
        omega
      apply cleanData_step_of_local hk ring hn2 X ell e hclean
      · simp [transition, hNonBarrier, nonBarrierStep,
          hrespLeader, hrespBullet]
      · simp [transition, hNonBarrier, nonBarrierStep,
          hrespLeader, hrespBullet]
      · intro _
        exact heLt
      · intro hm
        apply hclean.2.2 (ring.rightNeighbor e)
        simpa [Marked, transition, hNonBarrier, nonBarrierStep,
          hrespLeader, hrespBullet] using hm
    | false =>
      have hrNe : ring.rightNeighbor e ≠ ell := by
        intro h
        rw [h, hclean.1] at hrespLeader
        contradiction
      have hforward (heLt : e.val < ell.val) :
          (ring.rightNeighbor e).val < ell.val := by
        rw [hrval]
        have hneVal : e.val + 1 ≠ ell.val := by
          intro hval
          apply hrNe
          apply Fin.ext
          rw [hrval]
          exact hval
        omega
      cases hrespBullet : (X (ring.rightNeighbor e)).bullet with
      | false =>
        cases hinitProbe : (X e).probe with
        | false =>
          apply cleanData_step_of_local hk ring hn2 X ell e hclean
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · intro hm
            apply hclean.2.2 e
            simpa [Marked, transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe] using hm
          · intro hm
            apply hclean.2.2 (ring.rightNeighbor e)
            simpa [Marked, transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe] using hm
        | true =>
          have heLt := hclean.2.2 e (Or.inr hinitProbe)
          have hrLt := hforward heLt
          apply cleanData_step_of_local hk ring hn2 X ell e hclean
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · intro _
            exact heLt
          · intro _
            exact hrLt
      | true =>
        have hrLt := hclean.2.2 (ring.rightNeighbor e)
          (Or.inl hrespBullet)
        have heLt : e.val < ell.val := by
          rw [hrval] at hrLt
          omega
        cases hinitProbe : (X e).probe with
        | false =>
          apply cleanData_step_of_local hk ring hn2 X ell e hclean
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · intro _
            exact heLt
          · intro _
            exact hrLt
        | true =>
          apply cleanData_step_of_local hk ring hn2 X ell e hclean
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · simp [transition, hNonBarrier, nonBarrierStep,
              hrespLeader, hrespBullet, hinitProbe]
          · intro _
            exact heLt
          · intro _
            exact hrLt

@[simp] theorem cutPos_tailCoord_identity {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    cutPos ring (tailCoord ring) i = i := by
  apply Fin.ext
  simp [cutPos, cwPos, rightNeighbor_tailCoord,
    Nat.mod_eq_of_lt i.isLt]

@[simp] theorem cutView_tailCoord_identity {n k : Nat}
    (ring : DirectedRing n) (X : Fin n → State k) :
    cutView ring (tailCoord ring) X = X := by
  funext i
  simp [cutView]

theorem canonicalOneBarrier_oneBarrierAt_tail {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k)
    (hbar : CanonicalOneBarrier hk ring X) :
    OneBarrierAt hk ring X (tailCoord ring) := by
  intro i
  rw [barrierAt_labelsOf_iff]
  exact hbar i

/-- Full canonical `Clean` closure.  The theorem includes the unique-barrier
component, while `canonical_cleanData_step` supplies the exact same-leader and
mark-confinement component. -/
theorem canonical_clean_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (ell e : Fin n)
    (hndvd : ¬ k ∣ n) (hclean : CanonicalClean hk ring X ell) :
    CanonicalClean hk ring (cutSuccessor hk ring X e)
      (if AdvanceReady hk ring X e then ring.leftNeighbor ell else ell) := by
  have hn2 : 1 < n := by omega
  let D : Fin n → State k :=
    fun j => ((protocol k hk).step ring X e) j
  have honeX : OneBarrierAt hk ring X (tailCoord ring) :=
    canonicalOneBarrier_oneBarrierAt_tail hk ring X hclean.1
  have honeD := oneBarrierAt_step hk ring hn2 X (tailCoord ring) e
    hndvd honeX
  refine ⟨?_, canonical_cleanData_step hk ring hn3 X hclean.1 ell e hclean.2⟩
  by_cases hready : AdvanceReady hk ring X e
  · have honeReady : OneBarrierAt hk ring D
        (ring.rightNeighbor (tailCoord ring)) := by
      simpa [D, hready] using honeD
    have hcanon := canonicalOneBarrier_cutView hk ring D
      (ring.rightNeighbor (tailCoord ring)) honeReady
    have hview : cutView ring (ring.rightNeighbor (tailCoord ring)) D =
        rotateCut ring D := by
      rw [cutView_nextBarrier, cutView_tailCoord_identity]
    unfold cutSuccessor
    simp only [hready, if_true]
    rw [← hview]
    exact hcanon
  · have honeFixed : OneBarrierAt hk ring D (tailCoord ring) := by
      simpa [D, hready] using honeD
    have hcanon := canonicalOneBarrier_cutView hk ring D
      (tailCoord ring) honeFixed
    unfold cutSuccessor
    simp only [hready, if_false]
    simpa using hcanon

/-- Physical clean configuration, retaining both the unique barrier and the
physical leader witnesses. -/
def CleanAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (barrier leader : Fin n) : Prop :=
  OneBarrierAt hk ring C barrier ∧
    CleanData (cutView ring barrier C) (cutCoord ring barrier leader)

instance instDecidableCleanAt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b ell : Fin n) :
    Decidable (CleanAt hk ring C b ell) := by
  unfold CleanAt
  infer_instance

/-- Clean configurations with a fixed physical leader and a moving unique
barrier. -/
def CleanForLeader {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (leader : Fin n) (C : Fin n → State k) : Prop :=
  ∃ barrier : Fin n, CleanAt hk ring C barrier leader

/-- Existential clean region.  `CleanAt` and `CleanForLeader` expose the
witnesses needed by same-physical-leader consumers. -/
def Clean {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) : Prop :=
  ∃ leader : Fin n, CleanForLeader hk ring leader C

theorem cleanAt_physical_leader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b ell : Fin n)
    (hclean : CleanAt hk ring C b ell) : (C ell).leader = true := by
  have h := hclean.2.1
  simpa [cutView] using h

theorem cleanAt_unique_physical_leader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b ell i : Fin n)
    (hclean : CleanAt hk ring C b ell)
    (hi : (C i).leader = true) : i = ell := by
  have hviewLeader :
      ((cutView ring b C) (cutCoord ring b i)).leader = true := by
    simpa [cutView] using hi
  have hcoord := hclean.2.2.1 (cutCoord ring b i) hviewLeader
  have hpos := congrArg (cutPos ring b) hcoord
  simpa using hpos

theorem cleanAt_physical_follower_of_ne {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b ell i : Fin n)
    (hclean : CleanAt hk ring C b ell) (hi : i ≠ ell) :
    (C i).leader = false := by
  cases hbit : (C i).leader with
  | false => rfl
  | true => exact False.elim (hi
      (cleanAt_unique_physical_leader hk ring C b ell i hclean hbit))

/-- Two clean witnesses indexed by the same physical leader have pointwise
equal protocol outputs, independently of their barrier positions. -/
theorem cleanAt_output_eq_of_sameLeader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C C' : Fin n → State k)
    (b b' ell : Fin n) (hC : CleanAt hk ring C b ell)
    (hC' : CleanAt hk ring C' b' ell) :
    ∀ i : Fin n,
      (protocol k hk).output (C' i) = (protocol k hk).output (C i) := by
  intro i
  change (C' i).leader = (C i).leader
  by_cases hi : i = ell
  · subst i
    rw [cleanAt_physical_leader hk ring C' b' ell hC',
      cleanAt_physical_leader hk ring C b ell hC]
  · rw [cleanAt_physical_follower_of_ne hk ring C' b' ell i hC' hi,
      cleanAt_physical_follower_of_ne hk ring C b ell i hC hi]

/-- Exact physical clean closure with the same physical leader.  The barrier
witness advances iff the literal transition writes the responder label. -/
theorem cleanAt_step_sameLeader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b ell e : Fin n)
    (hndvd : ¬ k ∣ n) (hclean : CleanAt hk ring C b ell) :
    let D := (protocol k hk).step ring C e
    let b' := if AdvanceReady hk ring C e then ring.rightNeighbor b else b
    CleanAt hk ring D b' ell := by
  let D : Fin n → State k :=
    fun j => ((protocol k hk).step ring C e) j
  let b' := if AdvanceReady hk ring C e then ring.rightNeighbor b else b
  have hn2 : 1 < n := by omega
  have honeD : OneBarrierAt hk ring D b' := by
    dsimp only [D, b']
    exact oneBarrierAt_step hk ring hn2 C b e hndvd hclean.1
  refine ⟨honeD, ?_⟩
  let X := cutView ring b C
  let i := cutCoord ring b e
  let ellX := cutCoord ring b ell
  have hpos : cutPos ring b i = e := by simp [i]
  have hview : cutView ring b D = (protocol k hk).step ring X i := by
    dsimp only [D, X]
    simpa [hpos] using cutView_step_at_cutPos hk ring b C i
  have hcanon : CanonicalOneBarrier hk ring X :=
    canonicalOneBarrier_cutView hk ring C b hclean.1
  have hdata : CleanData X ellX := by
    simpa [X, ellX] using hclean.2
  have hreadyIff : AdvanceReady hk ring X i ↔
      AdvanceReady hk ring C e := by
    simpa [hpos] using advanceReady_cutView_iff hk ring C b i
  have hstep := canonical_cleanData_step hk ring hn3 X hcanon ellX i hdata
  by_cases hready : AdvanceReady hk ring C e
  · have hreadyX : AdvanceReady hk ring X i := hreadyIff.2 hready
    simp only [hready, if_true]
    rw [cutCoord_nextBarrier]
    have hrotateView :
        cutView ring (ring.rightNeighbor b) D =
          rotateCut ring (cutView ring b D) :=
      cutView_nextBarrier ring b (fun j => D j)
    rw [hrotateView, hview]
    unfold cutSuccessor at hstep
    simp only [hreadyX, if_true] at hstep
    exact hstep
  · have hreadyX : ¬ AdvanceReady hk ring X i := by
      exact fun h => hready (hreadyIff.1 h)
    simp only [hready, if_false]
    rw [hview]
    unfold cutSuccessor at hstep
    simp only [hreadyX, if_false] at hstep
    exact hstep

/-- The fixed-physical-leader clean slice is one-step closed. -/
theorem cleanForLeader_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (ell : Fin n) (C : Fin n → State k)
    (hclean : CleanForLeader hk ring ell C) (e : Fin n) :
    CleanForLeader hk ring ell ((protocol k hk).step ring C e) := by
  obtain ⟨b, hb⟩ := hclean
  refine ⟨if AdvanceReady hk ring C e then ring.rightNeighbor b else b, ?_⟩
  simpa using cleanAt_step_sameLeader hk ring hn3 C b ell e hndvd hb

/-- Existential clean configurations are one-step closed. -/
theorem clean_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (hclean : Clean hk ring C) (e : Fin n) :
    Clean hk ring ((protocol k hk).step ring C e) := by
  obtain ⟨ell, hell⟩ := hclean
  exact ⟨ell, cleanForLeader_step hk ring hn3 hndvd ell C hell e⟩

theorem cleanForLeader_closed {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (ell : Fin n) :
    PopulationProtocol.ClosedPred (protocol k hk) ring
      (CleanForLeader hk ring ell) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact cleanForLeader_step hk ring hn3 hndvd ell C hC e

theorem clean_closed {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n) :
    PopulationProtocol.ClosedPred (protocol k hk) ring (Clean hk ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact clean_step hk ring hn3 hndvd C hC e

/-- Reachability consumer: every continuation stays clean with the same
physical leader, although the barrier witness may move. -/
theorem cleanForLeader_reachable {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (ell : Fin n) {C C' : Fin n → State k}
    (hC : CleanForLeader hk ring ell C)
    (hr : PopulationProtocol.Reachable (protocol k hk) ring C C') :
    CleanForLeader hk ring ell C' := by
  exact (cleanForLeader_closed hk ring hn3 hndvd ell).reachable hC hr

/-- Semantic consumer boundary: a physical clean witness already satisfies
the repository's fixed-output safety predicate. -/
theorem cleanAt_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b ell : Fin n)
    (hclean : CleanAt hk ring C b ell) :
    PopulationProtocol.IsSafe (protocol k hk) ring C (fun bit => bit) := by
  constructor
  · refine ⟨ell, cleanAt_physical_leader hk ring C b ell hclean, ?_⟩
    intro i hi
    exact cleanAt_unique_physical_leader hk ring C b ell i hclean hi
  · intro C' hr i
    obtain ⟨b', hclean'⟩ := cleanForLeader_reachable hk ring hn3 hndvd
      ell ⟨b, hclean⟩ hr
    exact cleanAt_output_eq_of_sameLeader hk ring C C' b b' ell
      hclean hclean' i

theorem cleanForLeader_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (ell : Fin n)
    (hclean : CleanForLeader hk ring ell C) :
    PopulationProtocol.IsSafe (protocol k hk) ring C (fun bit => bit) := by
  obtain ⟨b, hb⟩ := hclean
  exact cleanAt_isSafe hk ring hn3 hndvd C b ell hb

/-! ## Literal `n = 3` regression witness -/

/-- The smallest state witnessing that a statically selected tail leader can
die before the barrier crosses it without decreasing `Phi`. -/
def staticGoodLeaderCounterexampleConfig (i : Fin 3) : State 2 where
  bullet := if i.val = 2 then true else false
  leader := if i.val = 0 then false else true
  label := if i.val = 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  probe := if i.val = 1 then true else false
  phase := false

/-- Exact successor after activating the ordinary edge `1 → 2` in the
regression state. -/
def staticGoodLeaderCounterexampleAfter : Fin 3 → State 2 :=
  (protocol 2 (by decide)).step ⟨by decide⟩
    staticGoodLeaderCounterexampleConfig ⟨1, by decide⟩

/-- Executable certificate for the false static-good-leader premise.

The cut is the identity cut at the unique barrier `2 → 0`.  Initially the
leaders are `1,2`, the probe is at `1`, and the bullet is at `2`.  The ordinary
edge `1 → 2` kills the tail leader, changes `(L,D)` from `(2,0)` to `(1,1)`,
and leaves `Phi = 2`. -/
theorem staticGoodLeaderCounterexample :
    let ring : DirectedRing 3 := ⟨by decide⟩
    let C := staticGoodLeaderCounterexampleConfig
    let D := staticGoodLeaderCounterexampleAfter
    OneBarrierAt (by decide) ring C ⟨2, by decide⟩ ∧
      (C ⟨1, by decide⟩).leader = true ∧
      (C ⟨2, by decide⟩).leader = true ∧
      (C ⟨1, by decide⟩).probe = true ∧
      (C ⟨2, by decide⟩).bullet = true ∧
      leaderCount (cutView ring ⟨2, by decide⟩ C) = 2 ∧
      ¬ Dangerous (cutView ring ⟨2, by decide⟩ C) ∧
      PhiAt ring ⟨2, by decide⟩ C = 2 ∧
      (D ⟨2, by decide⟩).leader = false ∧
      (D ⟨1, by decide⟩).leader = true ∧
      leaderCount (cutView ring ⟨2, by decide⟩ D) = 1 ∧
      Dangerous (cutView ring ⟨2, by decide⟩ D) ∧
      PhiAt ring ⟨2, by decide⟩ D = 2 := by
  decide

/-! The clean predicate is not an empty contract: this concrete state has the
same unique barrier `2 → 0`, its sole leader at `1`, and no mobile marks. -/
def cleanSatisfiabilityWitness (i : Fin 3) : State 2 where
  bullet := false
  leader := if i.val = 1 then true else false
  label := if i.val = 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  probe := false
  phase := false

theorem cleanAt_satisfiable :
    CleanAt (by decide) (⟨by decide⟩ : DirectedRing 3)
      cleanSatisfiabilityWitness ⟨2, by decide⟩ ⟨1, by decide⟩ := by
  decide

end SingleBarrierSanitation
end AAFJPK
