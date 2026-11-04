import Leader.PPL.SPLEntry.DistanceSweepPhase
import Leader.PPL.SPLEntry.RootResetPhase
import Leader.PPL.SPLEntry.CPBUniqueStepRow
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
Lemma 18 last-sweep phase.

The fixed word is

  seqL(root,n) =
    [shiftLeft root 1, ..., shiftLeft root n].

For 0 < d <= n, the edge shiftLeft root d has clockwise offset n-d,
and its responder is shiftLeft root (d-1).  Hence the first letter writes
the offset n-1 site from the root, while the last letter is the root edge
and writes offset 0 from the offset-1 responder.  In particular, for n=3
the literal edge word is [root-1, root-2, root]; the wrap edge is neither
duplicated nor omitted.

The proof keeps the explicit prefix invariant:
after k letters, every site whose clockwise offset is at least n-k already
has the canonical last value.  The other sites are irrelevant until their
letter is consumed.  Canonical distances, CPB, and the unique root are
preserved at every step.
-/

/-! -------------------------------------------------------------------------
    Geometry of the counterclockwise sweep
------------------------------------------------------------------------- -/

theorem l18LastCyclicOffsetLt
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    PPL.cyclicOffset ring root i < n := by
  unfold PPL.cyclicOffset
  exact Nat.mod_lt _ ring.hn

theorem l18LastCyclicOffsetSelf
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    PPL.cyclicOffset ring root root = 0 := by
  unfold PPL.cyclicOffset
  have hsum :
      root.val + n - root.val = n := by
    omega
  rw [hsum, Nat.mod_self]

theorem l18LastShiftRightZero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    PPL.shiftRight ring root 0 = root := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt root.isLt]

theorem l18LastShiftRightAdd
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (a b : Nat) :
    PPL.shiftRight ring
        (PPL.shiftRight ring root a) b =
      PPL.shiftRight ring root (a + b) := by
  apply Fin.ext
  change
    (((root.val + a) % n + b) % n) =
      (root.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem l18LastRightNeighborShiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat) :
    ring.rightNeighbor
        (PPL.shiftRight ring root d) =
      PPL.shiftRight ring root (d + 1) := by
  change
    PPL.shiftRight ring
        (PPL.shiftRight ring root d) 1 =
      PPL.shiftRight ring root (d + 1)
  rw [l18LastShiftRightAdd]

theorem l18LastCyclicOffsetShiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hd : d < n) :
    PPL.cyclicOffset ring root
        (PPL.shiftRight ring root d) = d := by
  unfold PPL.cyclicOffset
  change
    (((root.val + d) % n + n - root.val) % n) = d
  by_cases hs : root.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        root.val + d + n - root.val =
          n + d := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt hd]
  · have hge : n <= root.val + d := by
      omega
    have hlt : root.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        root.val + d - n + n - root.val = d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]

theorem l18LastShiftRightCyclicOffset
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    PPL.shiftRight ring root
        (PPL.cyclicOffset ring root i) =
      i := by
  apply Fin.ext
  change
    (root.val +
        ((i.val + n - root.val) % n)) % n =
      i.val
  by_cases hri : root.val <= i.val
  · have heq :
        i.val + n - root.val =
          n + (i.val - root.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt
        (by omega : i.val - root.val < n)]
    have hsum :
        root.val + (i.val - root.val) =
          i.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt i.isLt]
  · have hlt :
        i.val + n - root.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        root.val + (i.val + n - root.val) =
          i.val + n := by
      omega
    rw [hsum, Nat.add_mod_right,
      Nat.mod_eq_of_lt i.isLt]

theorem l18LastCyclicOffsetInjective
    {n : Nat}
    (ring : DirectedRing n)
    (root i j : Fin n)
    (h :
      PPL.cyclicOffset ring root i =
        PPL.cyclicOffset ring root j) :
    i = j := by
  have hs :=
    congrArg
      (fun d : Nat => PPL.shiftRight ring root d) h
  rw [l18LastShiftRightCyclicOffset,
      l18LastShiftRightCyclicOffset] at hs
  exact hs

theorem l18LastShiftLeftZero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    PPL.shiftLeft ring root 0 = root := by
  apply Fin.ext
  simp [PPL.shiftLeft,
    Nat.mod_eq_of_lt root.isLt]

theorem l18LastShiftLeftN
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    PPL.shiftLeft ring root n = root := by
  apply Fin.ext
  simp [PPL.shiftLeft,
    Nat.mod_eq_of_lt root.isLt]

theorem l18LastShiftLeftEqShiftRightSub
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hdle : d <= n) :
    PPL.shiftLeft ring root d =
      PPL.shiftRight ring root (n - d) := by
  by_cases hdn : d = n
  · subst d
    rw [l18LastShiftLeftN, Nat.sub_self,
      l18LastShiftRightZero]
  · have hdlt : d < n := by
      omega
    apply Fin.ext
    simp only [PPL.shiftLeft, PPL.shiftRight,
      Fin.val_mk]
    rw [Nat.mod_eq_of_lt hdlt]
    have heq :
        root.val + n - d =
          root.val + (n - d) := by
      omega
    rw [heq]

theorem l18LastCyclicOffsetShiftLeftPos
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hdpos : 0 < d)
    (hdle : d <= n) :
    PPL.cyclicOffset ring root
        (PPL.shiftLeft ring root d) =
      n - d := by
  rw [l18LastShiftLeftEqShiftRightSub
    ring root d hdle]
  exact
    l18LastCyclicOffsetShiftRight
      ring root (n - d) (by omega)

theorem l18LastRightShiftLeftPred
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hd1 : 1 <= d)
    (hdn : d <= n) :
    ring.rightNeighbor
        (PPL.shiftLeft ring root d) =
      PPL.shiftLeft ring root (d - 1) := by
  by_cases heq : d = n
  · subst d
    rw [l18LastShiftLeftN ring root]
    apply Fin.ext
    simp only
      [DirectedRing.rightNeighbor,
        PPL.shiftLeft]
    have hpred :
        n - 1 < n := by
      omega
    rw [Nat.mod_eq_of_lt hpred]
    congr 1
    omega
  · have hdlt : d < n := by
      omega
    have hpred :
        d - 1 < n := by
      omega
    apply Fin.ext
    simp only
      [DirectedRing.rightNeighbor,
        PPL.shiftLeft]
    rw [Nat.mod_eq_of_lt hdlt,
      Nat.mod_eq_of_lt hpred]
    rw [Nat.mod_add_mod]
    congr 1
    omega

theorem l18LastRightNeighborShiftLeftSucc
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (hk : k < n) :
    ring.rightNeighbor
        (PPL.shiftLeft ring root (k + 1)) =
      PPL.shiftLeft ring root k := by
  have h :=
    l18LastRightShiftLeftPred
      ring root (k + 1)
      (by omega) (by omega)
  have hs : k + 1 - 1 = k := by
    omega
  rw [hs] at h
  exact h

theorem l18LastSeqLSucc
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat) :
    PPL.seqL ring root (k + 1) =
      PPL.seqL ring root k ++
        [PPL.shiftLeft ring root (k + 1)] := by
  unfold PPL.seqL
  rw [List.ofFn_succ_last]
  rfl

/-! -------------------------------------------------------------------------
    Arithmetic of the final segment
------------------------------------------------------------------------- -/

def l18LastThreshold
    (n psi : Nat) : Nat :=
  psi * (PPL.segmentCount n psi - 1)

theorem l18LastSegmentCountPos
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi) :
    0 < PPL.segmentCount n psi := by
  unfold PPL.segmentCount
  have hle :
      1 <= (n + psi - 1) / psi := by
    apply (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).2
    simp only [Nat.one_mul]
    omega
  omega

theorem l18LastThresholdLt
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi) :
    l18LastThreshold n psi < n := by
  let z := PPL.segmentCount n psi
  have hzpos : 0 < z := by
    dsimp only [z]
    exact l18LastSegmentCountPos hn3 hpsi
  have hmul :
      z * psi <= n + psi - 1 := by
    dsimp only [z]
    unfold PPL.segmentCount
    exact Nat.div_mul_le_self (n + psi - 1) psi
  have hzsplit :
      z = (z - 1) + 1 := by
    omega
  rw [hzsplit, Nat.add_mul] at hmul
  simp only [Nat.one_mul] at hmul
  have hsum :
      n + psi - 1 = (n - 1) + psi := by
    omega
  rw [hsum] at hmul
  have hsmall :
      (z - 1) * psi <= n - 1 := by
    omega
  unfold l18LastThreshold
  dsimp only [z] at hsmall
  have hsmall' :
      psi * (PPL.segmentCount n psi - 1) <=
        n - 1 := by
    simpa only [Nat.mul_comm] using hsmall
  omega

theorem l18LastThresholdUpper
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi) :
    n <= l18LastThreshold n psi + psi := by
  let z := PPL.segmentCount n psi
  have hzpos : 0 < z := by
    dsimp only [z]
    exact l18LastSegmentCountPos hn3 hpsi
  have hrem :
      (n + psi - 1) % psi < psi :=
    Nat.mod_lt _ (by omega)
  have hdec :=
    Nat.mod_add_div (n + psi - 1) psi
  have hceil :
      n <=
        psi * ((n + psi - 1) / psi) := by
    omega
  have hzsplit :
      z = (z - 1) + 1 := by
    omega
  unfold l18LastThreshold
  dsimp only [z] at hzsplit
  calc
    n <=
        psi * PPL.segmentCount n psi := by
      simpa only [PPL.segmentCount] using hceil
    _ =
        psi * (PPL.segmentCount n psi - 1) +
          psi := by
      rw [hzsplit, Nat.mul_add]
      simp

theorem l18LastModSucc
    (a m : Nat)
    (hm : 1 < m) :
    ((a % m) + 1) % m =
      (a + 1) % m := by
  calc
    ((a % m) + 1) % m =
        ((a % m) + (1 % m)) % m := by
      rw [Nat.mod_eq_of_lt hm]
    _ = (a + 1) % m :=
      (Nat.add_mod a 1 m).symm

theorem l18LastPsiMultipleIsTwoPsiBorder
    (psi t : Nat)
    (hpsi : 0 < psi) :
    Or
      ((psi * t) % (2 * psi) = 0)
      ((psi * t) % (2 * psi) = psi) := by
  have hdec := Nat.mod_add_div t 2
  rcases Nat.mod_two_eq_zero_or_one t with hzero | hone
  · rw [hzero, Nat.zero_add] at hdec
    have ht :
        t = 2 * (t / 2) := by
      omega
    have heq :
        psi * (2 * (t / 2)) =
          (2 * psi) * (t / 2) := by
      ac_rfl
    exact Or.inl (by
      rw [ht, heq]
      simp)
  · rw [hone] at hdec
    have ht :
        t = 1 + 2 * (t / 2) := by
      omega
    have heq :
        psi * (1 + 2 * (t / 2)) =
          psi + (2 * psi) * (t / 2) := by
      rw [Nat.mul_add, Nat.mul_one]
      congr 1
      ac_rfl
    have hsmall :
        psi % (2 * psi) = psi :=
      Nat.mod_eq_of_lt (by omega)
    exact Or.inr (by
      rw [ht, heq]
      calc
        (psi + (2 * psi) * (t / 2)) %
            (2 * psi) =
          psi % (2 * psi) := by
            exact
              Nat.add_mul_mod_self_left
                psi (2 * psi) (t / 2)
        _ = psi := hsmall)

theorem l18LastBorderModPsiZero
    (psi b : Nat)
    (hpsi : 0 < psi)
    (hborder :
      Or
        (b % (2 * psi) = 0)
        (b % (2 * psi) = psi)) :
    b % psi = 0 := by
  have hdec := Nat.mod_add_div b (2 * psi)
  rcases hborder with hzero | hpsiRem
  · rw [hzero, Nat.zero_add] at hdec
    have hb :
        b = (2 * psi) * (b / (2 * psi)) :=
      hdec.symm
    have heq :
        (2 * psi) * (b / (2 * psi)) =
          psi * (2 * (b / (2 * psi))) := by
      ac_rfl
    rw [hb, heq]
    simp
  · rw [hpsiRem] at hdec
    have hb :
        b =
          psi +
            (2 * psi) * (b / (2 * psi)) :=
      hdec.symm
    have heq :
        (2 * psi) * (b / (2 * psi)) =
          psi * (2 * (b / (2 * psi))) := by
      ac_rfl
    rw [hb, heq, Nat.add_mod]
    simp

theorem l18LastBorderEqThreshold
    {n psi b : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hborder :
      Or
        (b % (2 * psi) = 0)
        (b % (2 * psi) = psi))
    (hge : l18LastThreshold n psi <= b)
    (hlt : b < n) :
    b = l18LastThreshold n psi := by
  let t := PPL.segmentCount n psi - 1
  let q := b / psi
  have hbUpper :
      b < l18LastThreshold n psi + psi :=
    Nat.lt_of_lt_of_le hlt
      (l18LastThresholdUpper hn3 hpsi)
  have hmod :
      b % psi = 0 :=
    l18LastBorderModPsiZero
      psi b (by omega) hborder
  have hdec := Nat.mod_add_div b psi
  rw [hmod, Nat.zero_add] at hdec
  have hbq :
      b = psi * q := by
    dsimp only [q]
    exact hdec.symm
  have hleMul :
      psi * t <= psi * q := by
    simpa only [l18LastThreshold, t, hbq] using hge
  have htq :
      t <= q :=
    Nat.le_of_mul_le_mul_left hleMul (by omega)
  have hltMul :
      psi * q < psi * (t + 1) := by
    calc
      psi * q = b := hbq.symm
      _ < l18LastThreshold n psi + psi := hbUpper
      _ = psi * (t + 1) := by
        dsimp only [t]
        rw [Nat.mul_add]
        simp [l18LastThreshold]
  have hqt :
      q < t + 1 :=
    (Nat.mul_lt_mul_left (by omega : 0 < psi)).mp
      hltMul
  have hqeq : q = t := by
    omega
  rw [hbq, hqeq]
  rfl

theorem l18LastBorderForcesBelowThreshold
    {n psi a : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ha : a + 1 < n)
    (hborder :
      Or
        ((a + 1) % (2 * psi) = 0)
        ((a + 1) % (2 * psi) = psi)) :
    Not (l18LastThreshold n psi <= a) := by
  intro hta
  have heq :=
    l18LastBorderEqThreshold
      hn3 hpsi hborder
      (by omega)
      ha
  omega

theorem l18LastNonborderThresholdStep
    {n psi a : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ha : a + 1 < n)
    (hnot :
      Not
        (Or
          ((a + 1) % (2 * psi) = 0)
          ((a + 1) % (2 * psi) = psi))) :
    Iff
      (l18LastThreshold n psi <= a + 1)
      (l18LastThreshold n psi <= a) := by
  constructor
  · intro hnext
    by_cases hcur :
        l18LastThreshold n psi <= a
    · exact hcur
    · have heq :
          l18LastThreshold n psi = a + 1 := by
        omega
      have hborder :
          Or
            ((l18LastThreshold n psi) %
                (2 * psi) = 0)
            ((l18LastThreshold n psi) %
                (2 * psi) = psi) := by
        unfold l18LastThreshold
        exact
          l18LastPsiMultipleIsTwoPsiBorder
            psi
            (PPL.segmentCount n psi - 1)
            (by omega)
      rw [heq] at hborder
      exact False.elim (hnot hborder)
  · intro hcur
    omega

/-! -------------------------------------------------------------------------
    Pair-level dist/last row for P_PL-prime
------------------------------------------------------------------------- -/

theorem l18LastDetermineModeFields
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    And (d.1.dist = l.dist)
      (And (d.1.last = l.last)
        (And (d.1.leader = l.leader)
          (And (d.2.dist = r.dist)
            (And (d.2.last = r.last)
              (d.2.leader = r.leader))))) := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact
      And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl
              (And.intro rfl rfl))))

def l18LastLine4Value
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) : Nat :=
  if r.leader = true then
    0
  else
    (l.dist.val + 1) % (2 * psi)

def l18LastPreTokenPair
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    Prod (PPL.State psi kappa)
      (PPL.State psi kappa) :=
  let d := PPL.determineMode l r
  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      Fin.mk 0 (by omega)
    else
      Fin.mk
        ((d.1.dist.val + 1) % (2 * psi))
        (Nat.mod_lt _ (by omega))
  let r1 : PPL.State psi kappa := { d.2 with dist := tmp }
  let l1 : PPL.State psi kappa :=
    if r1.leader = true then
      { d.1 with last := true }
    else if
        Or (r1.dist.val = 0)
          (r1.dist.val = psi) then
      { d.1 with last := false }
    else
      { d.1 with last := r1.last }
  (l1, r1)

theorem l18LastPreTokenPairFields
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let p := l18LastPreTokenPair hpsi l r
    And (p.1.dist = l.dist)
      (And
        (p.2.dist.val =
          l18LastLine4Value l r)
        (And (p.2.last = r.last)
          (p.1.last =
            if r.leader = true then
              true
            else if
                Or
                  (l18LastLine4Value l r = 0)
                  (l18LastLine4Value l r = psi) then
              false
            else
              r.last))) := by
  let d := PPL.determineMode l r
  have hd0 := l18LastDetermineModeFields l r
  have hd :
      And (d.1.dist = l.dist)
        (And (d.1.last = l.last)
          (And (d.1.leader = l.leader)
            (And (d.2.dist = r.dist)
              (And (d.2.last = r.last)
                (d.2.leader = r.leader))))) := by
    simpa [d] using hd0

  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      Fin.mk 0 (by omega)
    else
      Fin.mk
        ((d.1.dist.val + 1) % (2 * psi))
        (Nat.mod_lt _ (by omega))

  have htmp :
      tmp.val = l18LastLine4Value l r := by
    unfold l18LastLine4Value
    dsimp only [tmp]
    rw [hd.2.2.2.2.2, hd.1]
    by_cases hq : r.leader = true <;> simp [hq]

  let r1 : PPL.State psi kappa :=
    { d.2 with dist := tmp }

  have hr1dist :
      r1.dist.val = l18LastLine4Value l r := by
    dsimp only [r1]
    exact htmp

  have hr1last : r1.last = r.last := by
    dsimp only [r1]
    exact hd.2.2.2.2.1

  have hr1leader : r1.leader = r.leader := by
    dsimp only [r1]
    exact hd.2.2.2.2.2

  let l1 : PPL.State psi kappa :=
    if r1.leader = true then
      { d.1 with last := true }
    else if
        Or (r1.dist.val = 0)
          (r1.dist.val = psi) then
      { d.1 with last := false }
    else
      { d.1 with last := r1.last }

  have hl1dist : l1.dist = l.dist := by
    dsimp only [l1]
    split
    · exact hd.1
    · split
      · exact hd.1
      · exact hd.1

  have hl1last :
      l1.last =
        if r.leader = true then
          true
        else if
            Or
              (l18LastLine4Value l r = 0)
              (l18LastLine4Value l r = psi) then
          false
        else
          r.last := by
    dsimp only [l1]
    rw [hr1leader, hr1dist, hr1last]
    by_cases hleader : r.leader = true
    · simp only [if_pos hleader]
    · simp only [if_neg hleader]
      by_cases hborder :
          Or
            (l18LastLine4Value l r = 0)
            (l18LastLine4Value l r = psi)
      · simp only [if_pos hborder]
      · simp only [if_neg hborder]

  have hpdef :
      l18LastPreTokenPair hpsi l r = (l1, r1) := by
    rfl

  rw [hpdef]
  exact
    And.intro hl1dist
      (And.intro hr1dist
        (And.intro hr1last hl1last))

theorem l18LastMoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (And (q.1.last = l.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l r with
    hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId,
          PPL.birthFields]

theorem l18LastPPrimeMoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := pprimeMoveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (And (q.1.last = l.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  unfold pprimeMoveToken
  dsimp only
  have h :=
    l18LastMoveTokenDistLast
      hpsi kind l { r with mode := false }
  dsimp only at h
  simpa using h

theorem l18LastEliminateDistLast
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    And (q.1.dist = l.dist)
      (And (q.1.last = l.last)
        (And (q.2.dist = r.dist)
          (q.2.last = r.last))) := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    And.intro
      (congrArg
        (fun z :
          PPL.Elim.OtherFields psi kappa =>
            z.dist) hl)
      (And.intro
        (congrArg
          (fun z :
            PPL.Elim.OtherFields psi kappa =>
              z.last) hl)
        (And.intro
          (congrArg
            (fun z :
              PPL.Elim.OtherFields psi kappa =>
                z.dist) hr)
          (congrArg
            (fun z :
              PPL.Elim.OtherFields psi kappa =>
                z.last) hr)))

private def l18LastCreateMirror
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let p := l18LastPreTokenPair hpsi l r
  let b :=
    pprimeMoveToken hpsi PPL.TokenKind.black
      p.1 p.2
  pprimeMoveToken hpsi PPL.TokenKind.white
    b.1 b.2

private theorem l18LastCreateMirror_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    l18LastCreateMirror hpsi l r =
      pprimeCreateLeader hpsi l r := by
  unfold l18LastCreateMirror
    l18LastPreTokenPair
    pprimeCreateLeader
  rfl

theorem l18LastPPrimeCreateLeaderFields
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let q := pprimeCreateLeader hpsi l r
    And (q.1.dist = l.dist)
      (And
        (q.2.dist.val =
          l18LastLine4Value l r)
        (And (q.2.last = r.last)
          (q.1.last =
            if r.leader = true then
              true
            else if
                Or
                  (l18LastLine4Value l r = 0)
                  (l18LastLine4Value l r = psi) then
              false
            else
              r.last))) := by
  let p := l18LastPreTokenPair hpsi l r
  let b :=
    pprimeMoveToken hpsi PPL.TokenKind.black
      p.1 p.2
  let w :=
    pprimeMoveToken hpsi PPL.TokenKind.white
      b.1 b.2
  have hp :=
    l18LastPreTokenPairFields hpsi l r
  have hb :=
    l18LastPPrimeMoveTokenDistLast
      hpsi PPL.TokenKind.black p.1 p.2
  have hw :=
    l18LastPPrimeMoveTokenDistLast
      hpsi PPL.TokenKind.white b.1 b.2
  dsimp only at hp hb hw

  have hq1dist :
      w.1.dist = p.1.dist :=
    hw.1.trans hb.1
  have hq1last :
      w.1.last = p.1.last :=
    hw.2.1.trans hb.2.1
  have hq2dist :
      w.2.dist = p.2.dist :=
    hw.2.2.1.trans hb.2.2.1
  have hq2last :
      w.2.last = p.2.last :=
    hw.2.2.2.trans hb.2.2.2

  have hresult :
      And (w.1.dist = l.dist)
        (And
          (w.2.dist.val =
            l18LastLine4Value l r)
          (And (w.2.last = r.last)
            (w.1.last =
              if r.leader = true then
                true
              else if
                  Or
                    (l18LastLine4Value l r = 0)
                    (l18LastLine4Value l r = psi) then
                false
              else
                r.last))) :=
    And.intro
      (hq1dist.trans hp.1)
      (And.intro
        ((congrArg
          (fun d : Fin (2 * psi) => d.val)
          hq2dist).trans hp.2.1)
        (And.intro
          (hq2last.trans hp.2.2.1)
          (hq1last.trans hp.2.2.2)))

  have hmirror :
      l18LastCreateMirror hpsi l r = w := by
    rfl
  have hdef :
      pprimeCreateLeader hpsi l r = w :=
    (l18LastCreateMirror_eq hpsi l r).symm.trans
      hmirror
  rw [hdef]
  exact hresult

theorem l18LastPPrimePplFields
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let q := pprimePpl hpsi l r
    And (q.1.dist = l.dist)
      (And
        (q.2.dist.val =
          l18LastLine4Value l r)
        (And (q.2.last = r.last)
          (q.1.last =
            if r.leader = true then
              true
            else if
                Or
                  (l18LastLine4Value l r = 0)
                  (l18LastLine4Value l r = psi) then
              false
            else
              r.last))) := by
  let c := pprimeCreateLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc :=
    l18LastPPrimeCreateLeaderFields hpsi l r
  have he :=
    l18LastEliminateDistLast c.1 c.2
  dsimp only at hc he
  have hdef :
      pprimePpl hpsi l r = q := by
    rfl
  rw [hdef]
  exact
    And.intro
      (he.1.trans hc.1)
      (And.intro
        ((congrArg
          (fun d : Fin (2 * psi) => d.val)
          he.2.2.1).trans hc.2.1)
        (And.intro
          (he.2.2.2.trans hc.2.2.1)
          (he.2.1.trans hc.2.2.2)))

/-! -------------------------------------------------------------------------
    Configuration-level single-letter row and untouched frame
------------------------------------------------------------------------- -/

/-- Named frame row: a site outside the scheduled pair
is literally unchanged by one P_PL-prime letter. -/
theorem l18LastUntouchedFrame
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : Ne i e)
    (hir : Ne i (ring.rightNeighbor e)) :
    pprimeStep ring C e i = C i := by
  simp
    [pprimeStep,
      pprimeProtocol,
      PopulationProtocol.step,
      hie, hir]

theorem l18LastPPrimeTransition_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    pprimeTransition psi kappa l r =
      pprimePpl hpsi l r := by
  unfold pprimeTransition
  split
  · rfl
  · omega

theorem l18LastPPrimeStepLeft
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    pprimeStep ring C e e =
      (pprimePpl hpsi
        (C e)
        (C (ring.rightNeighbor e))).1 := by
  unfold pprimeStep PopulationProtocol.step
  dsimp only [pprimeProtocol]
  rw [l18LastPPrimeTransition_eq
    hpsi (C e) (C (ring.rightNeighbor e))]
  simp
  all_goals rfl

theorem l18LastPPrimeStepRight
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    pprimeStep ring C e
        (ring.rightNeighbor e) =
      (pprimePpl hpsi
        (C e)
        (C (ring.rightNeighbor e))).2 := by
  have hne :
      Ne (ring.rightNeighbor e) e :=
    PPL.Convergence.L18Bridge.l18RightNeighbor_ne_self
      hn3 ring e
  unfold pprimeStep PopulationProtocol.step
  dsimp only [pprimeProtocol]
  rw [l18LastPPrimeTransition_eq
    hpsi (C e) (C (ring.rightNeighbor e))]
  simp [hne]
  all_goals rfl

/-- Named single-letter write row.

Assume the first k counterclockwise sites have already acquired their
canonical last values.  The next selected edge writes exactly the next
canonical value, preserves every canonical distance, and leaves every
already-written site other than the new initiator's last bit unchanged.
-/
theorem l18LastSingleLetterWrite
    {n psi kappa k : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hk : k < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hUnique : L18UniqueLeaderAt C root)
    (hDist : L18CanonicalDistanceAt ring root C)
    (hPrefix :
      forall i : Fin n,
        n - k <= PPL.cyclicOffset ring root i ->
        Iff
          ((C i).last = true)
          (l18LastThreshold n psi <=
            PPL.cyclicOffset ring root i)) :
    let e := PPL.shiftLeft ring root (k + 1)
    let D := pprimeStep ring C e
    And
      (L18CanonicalDistanceAt ring root D)
      (And
        (Iff
          ((D e).last = true)
          (l18LastThreshold n psi <=
            PPL.cyclicOffset ring root e))
        (forall i : Fin n,
          Ne i e ->
            (D i).last = (C i).last)) := by
  let e := PPL.shiftLeft ring root (k + 1)
  let r := ring.rightNeighbor e
  let D := pprimeStep ring C e

  have hne : Ne r e := by
    dsimp only [r]
    exact
      PPL.Convergence.L18Bridge.l18RightNeighbor_ne_self
        hn3 ring e

  have heoff :
      PPL.cyclicOffset ring root e =
        n - (k + 1) := by
    dsimp only [e]
    exact
      l18LastCyclicOffsetShiftLeftPos
        ring root (k + 1)
        (by omega) (by omega)

  have hrsite :
      r = PPL.shiftLeft ring root k := by
    dsimp only [r, e]
    exact
      l18LastRightNeighborShiftLeftSucc
        ring root k hk

  have hp :=
    l18LastPPrimePplFields
      hpsi (C e) (C r)
  dsimp only at hp

  have hleft :
      D e =
        (pprimePpl hpsi (C e) (C r)).1 := by
    dsimp only [D, r]
    exact
      l18LastPPrimeStepLeft hpsi ring C e

  have hright :
      D r =
        (pprimePpl hpsi (C e) (C r)).2 := by
    dsimp only [D, r]
    exact
      l18LastPPrimeStepRight
        hn3 hpsi ring C e

  have htmp :
      l18LastLine4Value (C e) (C r) =
        (C r).dist.val := by
    by_cases hk0 : k = 0
    · subst k
      have hr0 : r = root := by
        rw [hrsite]
        exact l18LastShiftLeftZero ring root
      have hleader :
          (C r).leader = true := by
        rw [hr0]
        exact (hUnique root).mpr rfl
      have hdr := hDist r
      unfold l18LastLine4Value
      rw [hleader]
      rw [hdr, hr0, l18LastCyclicOffsetSelf]
      simp
    · have hkpos : 0 < k := by
        omega
      have hroff :
          PPL.cyclicOffset ring root r =
            n - k := by
        rw [hrsite]
        exact
          l18LastCyclicOffsetShiftLeftPos
            ring root k hkpos (by omega)
      have hrnot : Ne r root := by
        intro hrroot
        have hoff0 :
            PPL.cyclicOffset ring root r = 0 := by
          rw [hrroot, l18LastCyclicOffsetSelf]
        rw [hroff] at hoff0
        omega
      have hleader :
          (C r).leader = false := by
        cases hl : (C r).leader with
        | false =>
            rfl
        | true =>
            have hre : r = root :=
              (hUnique r).mp hl
            exact False.elim (hrnot hre)
      have hde := hDist e
      have hdr := hDist r
      unfold l18LastLine4Value
      simp [hleader]
      rw [hde, hdr, heoff, hroff]
      have hs :
          n - k =
            (n - (k + 1)) + 1 := by
        omega
      rw [hs]
      exact
        l18LastModSucc
          (n - (k + 1))
          (2 * psi)
          (by omega)

  have hCanonicalD :
      L18CanonicalDistanceAt ring root D := by
    intro i
    by_cases hie : i = e
    · subst i
      calc
        (D e).dist.val =
            (C e).dist.val := by
          rw [hleft]
          exact
            congrArg
              (fun d : Fin (2 * psi) => d.val)
              hp.1
        _ =
            PPL.cyclicOffset ring root e %
              (2 * psi) :=
          hDist e
    · by_cases hir : i = r
      · subst i
        calc
          (D r).dist.val =
              l18LastLine4Value (C e) (C r) := by
            rw [hright]
            exact hp.2.1
          _ = (C r).dist.val := htmp
          _ =
              PPL.cyclicOffset ring root r %
                (2 * psi) :=
            hDist r
      · have hf :
            D i = C i := by
          dsimp only [D, r]
          exact
            l18LastUntouchedFrame
              ring C e i hie hir
        rw [hf]
        exact hDist i

  have hInit :
      (D e).last =
        if (C r).leader = true then
          true
        else if
            Or
              (l18LastLine4Value (C e) (C r) = 0)
              (l18LastLine4Value (C e) (C r) = psi) then
          false
        else
          (C r).last := by
    rw [hleft]
    exact hp.2.2.2

  have hSelected :
      Iff
        ((D e).last = true)
        (l18LastThreshold n psi <=
          PPL.cyclicOffset ring root e) := by
    by_cases hk0 : k = 0
    · subst k
      have hr0 : r = root := by
        rw [hrsite]
        exact l18LastShiftLeftZero ring root
      have hleader :
          (C r).leader = true := by
        rw [hr0]
        exact (hUnique root).mpr rfl
      have hlast :
          (D e).last = true := by
        simpa [hleader] using hInit
      have htlt :=
        l18LastThresholdLt hn3 hpsi
      have hte :
          l18LastThreshold n psi <=
            PPL.cyclicOffset ring root e := by
        rw [heoff]
        omega
      exact
        Iff.intro
          (fun _ => hte)
          (fun _ => hlast)
    · have hkpos : 0 < k := by
        omega
      have hroff :
          PPL.cyclicOffset ring root r =
            n - k := by
        rw [hrsite]
        exact
          l18LastCyclicOffsetShiftLeftPos
            ring root k hkpos (by omega)
      have hrnot : Ne r root := by
        intro hrroot
        have hoff0 :
            PPL.cyclicOffset ring root r = 0 := by
          rw [hrroot, l18LastCyclicOffsetSelf]
        rw [hroff] at hoff0
        omega
      have hleader :
          (C r).leader = false := by
        cases hl : (C r).leader with
        | false =>
            rfl
        | true =>
            have hre : r = root :=
              (hUnique r).mp hl
            exact False.elim (hrnot hre)
      have hInit2 :
          (D e).last =
            if
                Or
                  ((C r).dist.val = 0)
                  ((C r).dist.val = psi) then
              false
            else
              (C r).last := by
        simpa [hleader, htmp] using hInit
      have hs :
          n - k =
            (n - (k + 1)) + 1 := by
        omega
      have ha :
          (n - (k + 1)) + 1 < n := by
        omega
      have hprefixCond :
          n - k <=
            PPL.cyclicOffset ring root r := by
        rw [hroff]
        exact Nat.le_refl _
      have hprefixR0 :=
        hPrefix r hprefixCond
      have hprefixR :
          Iff
            ((C r).last = true)
            (l18LastThreshold n psi <=
              n - k) := by
        simpa only [hroff] using hprefixR0
      by_cases hborder :
          Or
            ((C r).dist.val = 0)
            ((C r).dist.val = psi)
      · have hborderOff :
            Or
              ((n - k) % (2 * psi) = 0)
              ((n - k) % (2 * psi) = psi) := by
          have hdr := hDist r
          rw [hdr, hroff] at hborder
          exact hborder
        have hborderSucc :
            Or
              (((n - (k + 1)) + 1) %
                  (2 * psi) = 0)
              (((n - (k + 1)) + 1) %
                  (2 * psi) = psi) := by
          rw [← hs]
          exact hborderOff
        have hbelow :
            Not
              (l18LastThreshold n psi <=
                n - (k + 1)) :=
          l18LastBorderForcesBelowThreshold
            hn3 hpsi ha hborderSucc
        have hlastFalse :
            (D e).last = false := by
          rw [hInit2, if_pos hborder]
        rw [heoff]
        constructor
        · intro htrue
          rw [hlastFalse] at htrue
          contradiction
        · intro hte
          exact False.elim (hbelow hte)
      · have hnotOff :
            Not
              (Or
                ((n - k) % (2 * psi) = 0)
                ((n - k) % (2 * psi) = psi)) := by
          intro hb
          apply hborder
          have hdr := hDist r
          rw [hdr, hroff]
          exact hb
        have hnotSucc :
            Not
              (Or
                (((n - (k + 1)) + 1) %
                    (2 * psi) = 0)
                (((n - (k + 1)) + 1) %
                    (2 * psi) = psi)) := by
          rw [← hs]
          exact hnotOff
        have hrec :=
          l18LastNonborderThresholdStep
            hn3 hpsi ha hnotSucc
        have hcopy :
            (D e).last = (C r).last := by
          rw [hInit2, if_neg hborder]
        rw [heoff]
        constructor
        · intro htrue
          have hrtrue :
              (C r).last = true := by
            rw [hcopy] at htrue
            exact htrue
          have hnext :
              l18LastThreshold n psi <=
                (n - (k + 1)) + 1 := by
            rw [← hs]
            exact hprefixR.mp hrtrue
          exact hrec.mp hnext
        · intro hcur
          have hnext :
              l18LastThreshold n psi <=
                (n - (k + 1)) + 1 :=
            hrec.mpr hcur
          have hrtrue :
              (C r).last = true := by
            apply hprefixR.mpr
            rw [hs]
            exact hnext
          rw [hcopy, hrtrue]

  have hLastFrame :
      forall i : Fin n,
        Ne i e ->
          (D i).last = (C i).last := by
    intro i hie
    by_cases hir : i = r
    · subst i
      rw [hright]
      exact hp.2.2.1
    · have hf :
          D i = C i := by
        dsimp only [D, r]
        exact
          l18LastUntouchedFrame
            ring C e i hie hir
      exact
        congrArg
          (fun s : PPL.State psi kappa => s.last) hf

  exact
    And.intro hCanonicalD
      (And.intro hSelected hLastFrame)

/-! -------------------------------------------------------------------------
    Prefix invariant and sweep induction
------------------------------------------------------------------------- -/

def l18LastPrefixInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (C : Config n psi kappa) : Prop :=
  And (PPL.CPB ring C)
    (And (L18UniqueLeaderAt C root)
      (And (L18CanonicalDistanceAt ring root C)
        (forall i : Fin n,
          n - k <=
              PPL.cyclicOffset ring root i ->
            Iff
              ((C i).last = true)
              (l18LastThreshold n psi <=
                PPL.cyclicOffset ring root i))))

theorem l18LastPrefixInvariantRun
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : PPL.CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (hDist : L18CanonicalDistanceAt ring root C) :
    forall k : Nat,
      k <= n ->
      l18LastPrefixInvariant
        ring root k
        (runPPrime ring C
          (PPL.seqL ring root k)) := by
  intro k
  induction k with
  | zero =>
      intro _hk
      have hrun :
          runPPrime ring C
              (PPL.seqL ring root 0) =
            C := by
        rfl
      rw [hrun]
      unfold l18LastPrefixInvariant
      refine
        And.intro hCPB
          (And.intro hUnique
            (And.intro hDist ?_))
      intro i hi
      have hofflt :=
        l18LastCyclicOffsetLt ring root i
      have hf : False := by
        omega
      exact False.elim hf
  | succ k ih =>
      intro hk
      have hklt : k < n := by
        omega
      have hkprev : k <= n := by
        omega
      have hprev := ih hkprev
      let D :=
        runPPrime ring C
          (PPL.seqL ring root k)
      let e :=
        PPL.shiftLeft ring root (k + 1)
      let E := pprimeStep ring D e
      have hprev' :
          l18LastPrefixInvariant
            ring root k D := by
        dsimp only [D]
        exact hprev
      have hstate :=
        PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
          hn3 hpsi ring root D e
          hprev'.1 hprev'.2.1
      have hwrite :=
        l18LastSingleLetterWrite
          hn3 hpsi hklt
          ring root D
          hprev'.2.1
          hprev'.2.2.1
          hprev'.2.2.2
      dsimp only at hwrite
      have hEInv :
          l18LastPrefixInvariant
            ring root (k + 1) E := by
        unfold l18LastPrefixInvariant
        refine
          And.intro hstate.1
            (And.intro hstate.2
              (And.intro hwrite.1 ?_))
        intro i hi
        by_cases hie : i = e
        · subst i
          exact hwrite.2.1
        · have heoff :
              PPL.cyclicOffset ring root e =
                n - (k + 1) := by
            dsimp only [e]
            exact
              l18LastCyclicOffsetShiftLeftPos
                ring root (k + 1)
                (by omega) (by omega)
          have hneoff :
              Ne
                (PPL.cyclicOffset ring root i)
                (n - (k + 1)) := by
            intro hoff
            apply hie
            apply l18LastCyclicOffsetInjective
              ring root
            calc
              PPL.cyclicOffset ring root i =
                  n - (k + 1) := hoff
              _ =
                  PPL.cyclicOffset ring root e :=
                heoff.symm
          have hold :
              n - k <=
                PPL.cyclicOffset ring root i := by
            omega
          have hOld :=
            hprev'.2.2.2 i hold
          have hframe :=
            hwrite.2.2 i hie
          rw [hframe]
          exact hOld
      have hword :=
        l18LastSeqLSucc ring root k
      have hrun :
          runPPrime ring C
              (PPL.seqL ring root (k + 1)) =
            E := by
        rw [hword, runPPrime_append]
        simp [D, E, e, runPPrime]
      rw [hrun]
      exact hEInv

/-! -------------------------------------------------------------------------
    Headline Lemma 18 last-sweep phase
------------------------------------------------------------------------- -/

theorem l18LastSweepPhase_proved :
    L18LastSweepPhase := by
  unfold L18LastSweepPhase
  intro n psi kappa
  intro hn3 hpsi
  intro ring root C
  intro hCPB hUnique hDist
  have hfinal :=
    l18LastPrefixInvariantRun
      hn3 hpsi ring root C
      hCPB hUnique hDist
      n (Nat.le_refl n)
  change
    PPL.CDLAt ring root
      (runPPrime ring C
        (PPL.seqL ring root n))
  unfold PPL.CDLAt
  refine
    And.intro hfinal.1
      (And.intro hfinal.2.1 ?_)
  intro i
  dsimp only
  have hlast :=
    hfinal.2.2.2 i (by omega)
  exact
    And.intro
      (hfinal.2.2.1 i)
      (by
        simpa [l18LastThreshold] using hlast)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18LastUntouchedFrame
#print axioms PPL.Convergence.L18.l18LastSingleLetterWrite
#print axioms PPL.Convergence.L18.l18LastPrefixInvariantRun
#print axioms PPL.Convergence.L18.l18LastSweepPhase_proved

