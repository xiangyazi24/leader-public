import Leader.PPL.SPLEntry.CPBUniqueStepRow
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/-! ## Literal P_PL-prime distance row -/

private theorem l18DistanceDetermineMode_static
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    And
      (d.1.dist = l.dist)
      (And
        (d.2.dist = r.dist)
        (And
          (d.1.leader = l.leader)
          (d.2.leader = r.leader))) := by
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
          (And.intro rfl rfl))

private theorem l18DistanceMoveToken_dist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields hpsi kind l r
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l r with hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId,
          PPL.birthFields]

private theorem l18DistancePPrimeMoveToken_dist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : PPL.State psi kappa) :
    let q := pprimeMoveToken hpsi kind l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only [pprimeMoveToken]
  have h :=
    l18DistanceMoveToken_dist
      hpsi kind l {r with mode := false}
  dsimp only at h
  exact And.intro h.1 h.2

private theorem l18DistanceEliminate_dist
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    And (q.1.dist = l.dist)
      (q.2.dist = r.dist) := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    And.intro
      (congrArg
        (fun z : PPL.Elim.OtherFields psi kappa =>
          z.dist) hl)
      (congrArg
        (fun z : PPL.Elim.OtherFields psi kappa =>
          z.dist) hr)

/--
Public-name mirror of Algorithm 2 lines 4, 8, 9 plus the two forced-Construct
Algorithm 3 calls.  It is definitionally equal to pprimeCreateLeader.
-/
private def l18DistanceCreateMirror
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let d := PPL.determineMode l r
  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(d.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩
  let r0 : PPL.State psi kappa :=
    { d.2 with dist := tmp }
  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { d.1 with last := true }
    else if Or (r0.dist.val = 0)
        (r0.dist.val = psi) then
      { d.1 with last := false }
    else
      { d.1 with last := r0.last }
  let b := pprimeMoveToken hpsi .black l0 r0
  pprimeMoveToken hpsi .white b.1 b.2

private theorem l18DistanceCreateMirror_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    l18DistanceCreateMirror hpsi l r =
      pprimeCreateLeader hpsi l r := by
  unfold l18DistanceCreateMirror pprimeCreateLeader
  rfl

private theorem l18DistanceCreate_dist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let q := pprimeCreateLeader hpsi l r
    And
      (q.1.dist = l.dist)
      (q.2.dist.val =
        if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi)) := by
  let d := PPL.determineMode l r
  have hd0 :=
    l18DistanceDetermineMode_static l r
  have hd :
      And
        (d.1.dist = l.dist)
        (And
          (d.2.dist = r.dist)
          (And
            (d.1.leader = l.leader)
            (d.2.leader = r.leader))) := by
    simpa [d] using hd0

  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(d.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩

  have htmp :
      tmp.val =
        if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi) := by
    dsimp [tmp]
    rw [hd.2.2.2, hd.1]
    split <;> rfl

  let r0 : PPL.State psi kappa :=
    { d.2 with dist := tmp }

  have hr0 :
      r0.dist.val =
        if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi) := by
    dsimp only [r0]
    exact htmp

  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { d.1 with last := true }
    else if Or (r0.dist.val = 0)
        (r0.dist.val = psi) then
      { d.1 with last := false }
    else
      { d.1 with last := r0.last }

  have hl0 : l0.dist = l.dist := by
    dsimp only [l0]
    split
    · exact hd.1
    · split
      · exact hd.1
      · exact hd.1

  let b := pprimeMoveToken hpsi .black l0 r0
  have hb0 :=
    l18DistancePPrimeMoveToken_dist
      hpsi .black l0 r0
  have hb :
      And (b.1.dist = l0.dist)
        (b.2.dist = r0.dist) := by
    simpa [b] using hb0

  let w := pprimeMoveToken hpsi .white b.1 b.2
  have hw0 :=
    l18DistancePPrimeMoveToken_dist
      hpsi .white b.1 b.2
  have hw :
      And (w.1.dist = b.1.dist)
        (w.2.dist = b.2.dist) := by
    simpa [w] using hw0

  have hmirror :
      l18DistanceCreateMirror hpsi l r = w := by
    rfl

  have hresult :
      And
        ((l18DistanceCreateMirror hpsi l r).1.dist =
          l.dist)
        ((l18DistanceCreateMirror hpsi l r).2.dist.val =
          if r.leader = true then
            0
          else
            (l.dist.val + 1) % (2 * psi)) := by
    rw [hmirror]
    refine And.intro ?_ ?_
    · exact hw.1.trans (hb.1.trans hl0)
    · calc
        w.2.dist.val = b.2.dist.val :=
          congrArg Fin.val hw.2
        _ = r0.dist.val :=
          congrArg Fin.val hb.2
        _ =
            if r.leader = true then
              0
            else
              (l.dist.val + 1) % (2 * psi) :=
          hr0

  rw [l18DistanceCreateMirror_eq hpsi l r] at hresult
  exact hresult

private theorem l18DistancePPrimePair_dist
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let q := pprimePpl hpsi l r
    And
      (q.1.dist = l.dist)
      (q.2.dist.val =
        if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi)) := by
  let c := pprimeCreateLeader hpsi l r
  have hc0 :=
    l18DistanceCreate_dist hpsi l r
  have hc :
      And
        (c.1.dist = l.dist)
        (c.2.dist.val =
          if r.leader = true then
            0
          else
            (l.dist.val + 1) % (2 * psi)) := by
    simpa [c] using hc0

  let q := PPL.eliminateLeaders c.1 c.2
  have he0 :=
    l18DistanceEliminate_dist c.1 c.2
  have he :
      And (q.1.dist = c.1.dist)
        (q.2.dist = c.2.dist) := by
    simpa [q] using he0

  have hdef :
      pprimePpl hpsi l r = q := by
    rfl
  rw [hdef]
  refine And.intro ?_ ?_
  · exact he.1.trans hc.1
  · calc
      q.2.dist.val = c.2.dist.val :=
        congrArg Fin.val he.2
      _ =
          if r.leader = true then
            0
          else
            (l.dist.val + 1) % (2 * psi) :=
        hc.2

/--
The named single-letter write used by the sweep induction.
A follower responder receives source.dist+1 modulo 2*psi, while the source
distance is framed.
-/
private theorem l18DistanceStep_write
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hresponder :
      (C (ring.rightNeighbor e)).leader = false) :
    And
      ((pprimeStep ring C e e).dist =
        (C e).dist)
      ((pprimeStep ring C e
          (ring.rightNeighbor e)).dist.val =
        ((C e).dist.val + 1) % (2 * psi)) := by
  have hp :=
    l18DistancePPrimePair_dist
      hpsi (C e) (C (ring.rightNeighbor e))
  have hne :
      Ne (ring.rightNeighbor e) e :=
    PPL.Convergence.L18Bridge.l18RightNeighbor_ne_self
      hn3 ring e
  constructor
  · simpa [
      pprimeStep,
      PopulationProtocol.step,
      pprimeProtocol,
      pprimeTransition,
      hpsi
    ] using hp.1
  · have hr :
        (pprimePpl hpsi
          (C e) (C (ring.rightNeighbor e))).2.dist.val =
          ((C e).dist.val + 1) % (2 * psi) := by
      simpa [hresponder] using hp.2
    simpa [
      pprimeStep,
      PopulationProtocol.step,
      pprimeProtocol,
      pprimeTransition,
      hpsi,
      hne
    ] using hr

/-- A site outside the scheduled pair keeps its distance literally. -/
private theorem l18DistanceStep_frame
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : Ne i e)
    (hir : Ne i (ring.rightNeighbor e)) :
    (pprimeStep ring C e i).dist =
      (C i).dist := by
  simp [
    pprimeStep,
    PopulationProtocol.step,
    hie,
    hir
  ]

/-! ## Ring geometry for the rotated sweep -/

private theorem l18DistanceShiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    PPL.shiftRight ring root 0 = root := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt root.isLt]

private theorem l18DistanceShiftRight_add
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

private theorem l18DistanceRightNeighbor_shiftRight
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
  rw [l18DistanceShiftRight_add]

private theorem l18DistanceCyclicOffset_shiftRight
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

private theorem l18DistanceShiftRight_cyclicOffset
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    PPL.shiftRight ring root
        (PPL.cyclicOffset ring root i) = i := by
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

private theorem l18DistanceShiftRight_ne_of_ne
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (a b : Nat)
    (ha : a < n)
    (hb : b < n)
    (hab : Ne a b) :
    Ne
      (PPL.shiftRight ring root a)
      (PPL.shiftRight ring root b) := by
  intro h
  have ho :=
    congrArg
      (fun i : Fin n =>
        PPL.cyclicOffset ring root i) h
  rw [
    l18DistanceCyclicOffset_shiftRight
      ring root a ha,
    l18DistanceCyclicOffset_shiftRight
      ring root b hb
  ] at ho
  exact hab ho

private theorem l18DistanceShiftRight_ne_root
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hd : d < n)
    (hpos : 0 < d) :
    Ne (PPL.shiftRight ring root d) root := by
  intro h
  have hz :
      PPL.shiftRight ring root d =
        PPL.shiftRight ring root 0 := by
    rw [l18DistanceShiftRight_zero]
    exact h
  exact
    (l18DistanceShiftRight_ne_of_ne
      ring root d 0 hd ring.hn (by omega)) hz

private theorem l18DistanceModSucc
    (k m : Nat)
    (hm : 1 < m) :
    ((k % m) + 1) % m =
      (k + 1) % m := by
  calc
    ((k % m) + 1) % m =
        ((k % m) + (1 % m)) % m := by
      rw [Nat.mod_eq_of_lt hm]
    _ = (k + 1) % m :=
      (Nat.add_mod k 1 m).symm

private theorem l18DistanceSeqR_succ
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat) :
    PPL.seqR ring root (k + 1) =
      PPL.seqR ring root k ++
        [PPL.shiftRight ring root k] := by
  unfold PPL.seqR
  rw [List.ofFn_succ_last]
  rfl

private theorem l18DistanceRun_seqR_succ
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (k : Nat) :
    runPPrime ring C
        (PPL.seqR ring root (k + 1)) =
      pprimeStep ring
        (runPPrime ring C
          (PPL.seqR ring root k))
        (PPL.shiftRight ring root k) := by
  rw [l18DistanceSeqR_succ, runPPrime_append]
  rfl

/-! ## Prefix invariant and sweep induction -/

private def L18DistancePrefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (k : Nat) : Prop :=
  And (CPB ring C)
    (And
      (L18UniqueLeaderAt C root)
      (forall d : Nat,
        d <= k ->
        d < n ->
        (C (PPL.shiftRight ring root d)).dist.val =
          d % (2 * psi)))

private theorem l18DistancePrefix_step
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (k : Nat)
    (hk : k + 1 < n)
    (hprefix :
      L18DistancePrefix ring root C k) :
    L18DistancePrefix ring root
      (pprimeStep ring C
        (PPL.shiftRight ring root k))
      (k + 1) := by
  have hstruct :=
    PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
      hn3 hpsi ring root C
      (PPL.shiftRight ring root k)
      hprefix.1 hprefix.2.1

  have hrn :=
    l18DistanceRightNeighbor_shiftRight
      ring root k

  have hnotRoot :
      Ne
        (PPL.shiftRight ring root (k + 1))
        root :=
    l18DistanceShiftRight_ne_root
      ring root (k + 1) hk (by omega)

  have hresp :
      (C
        (PPL.shiftRight ring root (k + 1))).leader =
        false := by
    cases hb :
        (C
          (PPL.shiftRight ring root (k + 1))).leader with
    | false =>
        rfl
    | true =>
        have heq :
            PPL.shiftRight ring root (k + 1) =
              root :=
          (hprefix.2.1
            (PPL.shiftRight ring root (k + 1))).1 hb
        exact False.elim (hnotRoot heq)

  have hrespRN :
      (C
        (ring.rightNeighbor
          (PPL.shiftRight ring root k))).leader =
        false := by
    rw [hrn]
    exact hresp

  have hwrite :=
    l18DistanceStep_write
      hn3 hpsi ring C
      (PPL.shiftRight ring root k)
      hrespRN

  refine
    And.intro hstruct.1
      (And.intro hstruct.2 ?_)
  intro d hdle hdlt

  by_cases hnew : d = k + 1
  · subst d
    have hkdist :=
      hprefix.2.2 k
        (Nat.le_refl k) (by omega)
    calc
      (pprimeStep ring C
        (PPL.shiftRight ring root k)
        (PPL.shiftRight ring root (k + 1))).dist.val =
          (pprimeStep ring C
            (PPL.shiftRight ring root k)
            (ring.rightNeighbor
              (PPL.shiftRight ring root k))).dist.val := by
        rw [hrn]
      _ =
          ((C
              (PPL.shiftRight ring root k)).dist.val + 1) %
            (2 * psi) :=
        hwrite.2
      _ =
          ((k % (2 * psi)) + 1) %
            (2 * psi) := by
        rw [hkdist]
      _ =
          (k + 1) % (2 * psi) :=
        l18DistanceModSucc
          k (2 * psi) (by omega)

  · have hdleK : d <= k := by
      omega
    by_cases hdk : d = k
    · subst d
      have hkdist :=
        hprefix.2.2 k
          (Nat.le_refl k) (by omega)
      calc
        (pprimeStep ring C
          (PPL.shiftRight ring root k)
          (PPL.shiftRight ring root k)).dist.val =
            (C
              (PPL.shiftRight ring root k)).dist.val :=
          congrArg Fin.val hwrite.1
        _ = k % (2 * psi) :=
          hkdist
    · have hde :
          Ne
            (PPL.shiftRight ring root d)
            (PPL.shiftRight ring root k) :=
        l18DistanceShiftRight_ne_of_ne
          ring root d k hdlt (by omega) hdk
      have hdr0 :
          Ne
            (PPL.shiftRight ring root d)
            (PPL.shiftRight ring root (k + 1)) :=
        l18DistanceShiftRight_ne_of_ne
          ring root d (k + 1)
          hdlt hk (by omega)
      have hdr :
          Ne
            (PPL.shiftRight ring root d)
            (ring.rightNeighbor
              (PPL.shiftRight ring root k)) := by
        rw [hrn]
        exact hdr0
      have hframe :=
        l18DistanceStep_frame
          ring C
          (PPL.shiftRight ring root k)
          (PPL.shiftRight ring root d)
          hde hdr
      calc
        (pprimeStep ring C
          (PPL.shiftRight ring root k)
          (PPL.shiftRight ring root d)).dist.val =
            (C
              (PPL.shiftRight ring root d)).dist.val :=
          congrArg Fin.val hframe
        _ = d % (2 * psi) :=
          hprefix.2.2 d hdleK hdlt

private theorem l18DistancePrefix_run
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (hroot : (C root).dist.val = 0) :
    forall k : Nat,
      k < n ->
      L18DistancePrefix ring root
        (runPPrime ring C
          (PPL.seqR ring root k))
        k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      have hbase :
          L18DistancePrefix ring root C 0 := by
        refine
          And.intro hCPB
            (And.intro hUnique ?_)
        intro d hdle hdlt
        have hd : d = 0 := by
          omega
        subst d
        rw [l18DistanceShiftRight_zero]
        simpa using hroot
      simpa [PPL.seqR, runPPrime] using hbase

  | succ k ih =>
      intro hk
      have hprev :=
        ih (by omega)
      rw [l18DistanceRun_seqR_succ]
      exact
        l18DistancePrefix_step
          hn3 hpsi ring root
          (runPPrime ring C
            (PPL.seqR ring root k))
          k hk hprev

theorem l18DistanceSweepPhase_proved :
    L18DistanceSweepPhase := by
  unfold L18DistanceSweepPhase
  intro n psi kappa
  intro hn3 hpsi ring root C
  intro hCPB hUnique hroot
  dsimp only

  have hprefix :
      L18DistancePrefix ring root
        (runPPrime ring C
          (l18DistanceWord ring root))
        (n - 1) := by
    unfold l18DistanceWord
    exact
      l18DistancePrefix_run
        hn3 hpsi ring root C
        hCPB hUnique hroot
        (n - 1) (by omega)

  refine
    And.intro hprefix.1
      (And.intro hprefix.2.1 ?_)
  unfold L18CanonicalDistanceAt
  intro i

  have hofflt :
      PPL.cyclicOffset ring root i < n :=
    Nat.mod_lt _ ring.hn

  have hoffle :
      PPL.cyclicOffset ring root i <= n - 1 := by
    omega

  have hd :=
    hprefix.2.2
      (PPL.cyclicOffset ring root i)
      hoffle hofflt

  have hsite :=
    l18DistanceShiftRight_cyclicOffset
      ring root i
  rw [hsite] at hd
  exact hd

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18DistanceSweepPhase_proved
