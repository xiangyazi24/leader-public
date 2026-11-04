import Leader.PPL.SPLEntry.RootResetPhase
import Leader.PPL.SPLEntry.CPBUniqueStepRow
import Leader.PPL.TransitionFacts
import Init.Omega


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-!
Gapped Root / Distance / Last phases for Lemma 18.


refuted the old global suffix-forcing row because it admitted
unreachable malformed intermediate states.  The replacement here is local and
monotone.


* Root carries the one fact root.dist = 0.
* Distance carries a clockwise fixed prefix.
* Last carries a counterclockwise fixed suffix, under globally canonical
  distances.


Every arbitrary inserted P_PL-prime letter preserves the already-fixed
region.  A matched phase letter extends that region by one site.  Therefore
the three phase postconditions hold for every schedule in which the frozen
phase word occurs as an ordered subsequence.  The endpoint theorem is stronger
than the requested first-hit alternative, so the proofs below always return
the postcondition branch.
-/


/-! -------------------------------------------------------------------------
    Public gapped phase interfaces
------------------------------------------------------------------------- -/


/-- The earlier boundary-oriented occurrence form.  The stronger gapped phase
theorems below use raw List.Sublist, but this definition is kept as the
phase-composition interface for later Risky / Build work. -/
def L18PhaseOccurrence
    {n : Nat}
    (word schedule : DetSchedule n) : Prop :=
  (word = [] ∧ schedule = []) ∨
    ∃ (w s : DetSchedule n) (e : Fin n),
      word = w ++ [e] ∧
        schedule = s ++ [e] ∧
        w.Sublist s


def L18GappedRootResetPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CPB ring C →
    L18UniqueLeaderAt C root →
    (l18RootResetWord ring root).Sublist schedule →
    l18HitsSPL ring root C schedule = true ∨
      (let D := runPPrime ring C schedule
       CPB ring D ∧
         L18UniqueLeaderAt D root ∧
         (D root).dist.val = 0)


def L18GappedDistanceSweepPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CPB ring C →
    L18UniqueLeaderAt C root →
    (C root).dist.val = 0 →
    (l18DistanceWord ring root).Sublist schedule →
    l18HitsSPL ring root C schedule = true ∨
      (let D := runPPrime ring C schedule
       CPB ring D ∧
         L18UniqueLeaderAt D root ∧
         L18CanonicalDistanceAt ring root D)


def L18GappedLastSweepPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CPB ring C →
    L18UniqueLeaderAt C root →
    L18CanonicalDistanceAt ring root C →
    (l18LastWord ring root).Sublist schedule →
    l18HitsSPL ring root C schedule = true ∨
      CDLAt ring root (runPPrime ring C schedule)


/-! -------------------------------------------------------------------------
    Ring geometry
------------------------------------------------------------------------- -/


theorem l18Gapped_cyclicOffset_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    cyclicOffset ring root i < n := by
  unfold cyclicOffset
  exact Nat.mod_lt _ ring.hn


@[simp] theorem l18Gapped_cyclicOffset_root
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    cyclicOffset ring root root = 0 := by
  unfold cyclicOffset
  have hsum :
      root.val + n - root.val = n := by
    omega
  rw [hsum, Nat.mod_self]


@[simp] theorem l18Gapped_shiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    shiftRight ring root 0 = root := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt root.isLt]


@[simp] theorem l18Gapped_shiftLeft_zero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    shiftLeft ring root 0 = root := by
  apply Fin.ext
  change
    (root.val + n - (0 % n)) % n =
      root.val
  rw [Nat.zero_mod, Nat.sub_zero,
    Nat.add_mod_right,
    Nat.mod_eq_of_lt root.isLt]


theorem l18Gapped_shiftRight_add
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) (a b : Nat) :
    shiftRight ring (shiftRight ring i a) b =
      shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


theorem l18Gapped_rightNeighbor_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) (k : Nat) :
    ring.rightNeighbor (shiftRight ring root k) =
      shiftRight ring root (k + 1) := by
  calc
    ring.rightNeighbor (shiftRight ring root k) =
        shiftRight ring (shiftRight ring root k) 1 := rfl
    _ = shiftRight ring root (k + 1) :=
      l18Gapped_shiftRight_add ring root k 1


theorem l18Gapped_cyclicOffset_eq_of_le
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n)
    (h : root.val ≤ i.val) :
    cyclicOffset ring root i =
      i.val - root.val := by
  unfold cyclicOffset
  have hs :
      i.val + n - root.val =
        n + (i.val - root.val) := by
    omega
  rw [hs, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega : i.val - root.val < n)]


theorem l18Gapped_cyclicOffset_eq_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n)
    (h : i.val < root.val) :
    cyclicOffset ring root i =
      i.val + n - root.val := by
  unfold cyclicOffset
  rw [Nat.mod_eq_of_lt (by omega :
    i.val + n - root.val < n)]


theorem l18Gapped_site_eq_shiftRight_offset
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    i =
      shiftRight ring root
        (cyclicOffset ring root i) := by
  by_cases hle : root.val ≤ i.val
  · have hoff :=
      l18Gapped_cyclicOffset_eq_of_le
        ring root i hle
    apply Fin.ext
    change
      i.val =
        (root.val +
          cyclicOffset ring root i) % n
    rw [hoff]
    have hs :
        root.val + (i.val - root.val) =
          i.val := by
      omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]
  · have hlt : i.val < root.val := by
      omega
    have hoff :=
      l18Gapped_cyclicOffset_eq_of_lt
        ring root i hlt
    apply Fin.ext
    change
      i.val =
        (root.val +
          cyclicOffset ring root i) % n
    rw [hoff]
    have hs :
        root.val + (i.val + n - root.val) =
          i.val + n := by
      omega
    rw [hs]
    simp [Nat.add_mod,
      Nat.mod_eq_of_lt i.isLt]


theorem l18Gapped_shiftRight_cyclicOffset
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    shiftRight ring root
        (cyclicOffset ring root i) =
      i :=
  (l18Gapped_site_eq_shiftRight_offset
    ring root i).symm


theorem l18Gapped_cyclicOffset_injective
    {n : Nat}
    (ring : DirectedRing n)
    (root i j : Fin n)
    (h :
      cyclicOffset ring root i =
        cyclicOffset ring root j) :
    i = j := by
  have hs :=
    congrArg
      (fun d : Nat => shiftRight ring root d) h
  simpa [
    l18Gapped_shiftRight_cyclicOffset
  ] using hs


theorem l18Gapped_cyclicOffset_shiftRight_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) (d : Nat)
    (hd : d < n) :
    cyclicOffset ring root
        (shiftRight ring root d) =
      d := by
  unfold cyclicOffset
  change
    (((root.val + d) % n + n - root.val) % n) =
      d
  by_cases hs : root.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        root.val + d + n - root.val =
          n + d := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt hd]
  · have hge : n ≤ root.val + d := by
      omega
    have hlt :
        root.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        root.val + d - n + n - root.val =
          d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]

theorem l18Gapped_rightNeighbor_offset_of_ne_root
    {n : Nat}
    (ring : DirectedRing n)
    (root e : Fin n)
    (hne : ring.rightNeighbor e ≠ root) :
    cyclicOffset ring root
        (ring.rightNeighbor e) =
      cyclicOffset ring root e + 1 := by
  let x := cyclicOffset ring root e
  have hxlt : x < n := by
    dsimp only [x]
    exact l18Gapped_cyclicOffset_lt ring root e
  have heq :
      e = shiftRight ring root x := by
    simpa [x] using
      l18Gapped_site_eq_shiftRight_offset
        ring root e
  have hr :
      ring.rightNeighbor e =
        shiftRight ring root (x + 1) := by
    calc
      ring.rightNeighbor e =
          shiftRight ring e 1 := rfl
      _ =
          shiftRight ring
            (shiftRight ring root x) 1 := by
              rw [heq]
      _ =
          shiftRight ring root (x + 1) :=
        l18Gapped_shiftRight_add
          ring root x 1
  by_cases hx1 : x + 1 < n
  · rw [hr]
    simpa [x] using
      l18Gapped_cyclicOffset_shiftRight_of_lt
        ring root (x + 1) hx1
  · have hxn : x + 1 = n := by
      omega
    have hroot :
        ring.rightNeighbor e = root := by
      rw [hr, hxn]
      apply Fin.ext
      simp [shiftRight, Nat.add_mod,
        Nat.mod_eq_of_lt root.isLt]
    exact False.elim (hne hroot)


theorem l18Gapped_predecessor_offset_of_right_root
    {n : Nat}
    (ring : DirectedRing n)
    (root e : Fin n)
    (hroot :
      ring.rightNeighbor e = root) :
    cyclicOffset ring root e = n - 1 := by
  let x := cyclicOffset ring root e
  have hxlt : x < n := by
    dsimp only [x]
    exact l18Gapped_cyclicOffset_lt ring root e
  have heq :
      e = shiftRight ring root x := by
    simpa [x] using
      l18Gapped_site_eq_shiftRight_offset
        ring root e
  have hr :
      ring.rightNeighbor e =
        shiftRight ring root (x + 1) := by
    calc
      ring.rightNeighbor e =
          shiftRight ring e 1 := rfl
      _ =
          shiftRight ring
            (shiftRight ring root x) 1 := by
              rw [heq]
      _ =
          shiftRight ring root (x + 1) :=
        l18Gapped_shiftRight_add
          ring root x 1
  by_cases hx1 : x + 1 < n
  · have hoff :
        cyclicOffset ring root
            (ring.rightNeighbor e) =
          x + 1 := by
      rw [hr]
      exact
        l18Gapped_cyclicOffset_shiftRight_of_lt
          ring root (x + 1) hx1
    rw [hroot, l18Gapped_cyclicOffset_root] at hoff
    omega
  · omega


theorem l18Gapped_shiftLeftValOfLE
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hdpos : 0 < d)
    (hdlt : d < n)
    (hdr : d ≤ root.val) :
    (shiftLeft ring root d).val =
      root.val - d := by
  unfold shiftLeft
  change
    (root.val + n - (d % n)) % n =
      root.val - d
  rw [Nat.mod_eq_of_lt hdlt]
  have heq :
      root.val + n - d =
        (root.val - d) + n := by
    omega
  rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero]
  simpa [Nat.mod_mod] using
    (Nat.mod_eq_of_lt (by omega : root.val - d < n))


theorem l18Gapped_shiftLeftValOfGT
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hdpos : 0 < d)
    (hdlt : d < n)
    (hrd : root.val < d) :
    (shiftLeft ring root d).val =
      n - (d - root.val) := by
  unfold shiftLeft
  change
    (root.val + n - (d % n)) % n =
      n - (d - root.val)
  rw [Nat.mod_eq_of_lt hdlt]
  have heq :
      root.val + n - d =
        n - (d - root.val) := by
    omega
  rw [heq]
  exact Nat.mod_eq_of_lt (by omega)


theorem l18Gapped_cyclicOffset_shiftLeft_pos
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hdpos : 0 < d)
    (hdle : d ≤ n) :
    cyclicOffset ring root
        (shiftLeft ring root d) =
      n - d := by
  by_cases hdn : d = n
  · subst d
    have hs :
        shiftLeft ring root n = root := by
      apply Fin.ext
      change
        (root.val + n - (n % n)) % n =
          root.val
      rw [Nat.mod_self, Nat.sub_zero,
        Nat.add_mod_right,
        Nat.mod_eq_of_lt root.isLt]
    rw [hs, l18Gapped_cyclicOffset_root]
    omega
  · have hdlt : d < n := by
      omega
    by_cases hdr : d ≤ root.val
    · unfold cyclicOffset
      change
        ((shiftLeft ring root d).val +
            n - root.val) % n =
          n - d
      rw [l18Gapped_shiftLeftValOfLE
        ring root d hdpos hdlt hdr]
      have heq :
          root.val - d + n - root.val =
            n - d := by
        omega
      rw [heq]
      exact Nat.mod_eq_of_lt (by omega)
    · have hrd : root.val < d := by
        omega
      unfold cyclicOffset
      change
        ((shiftLeft ring root d).val +
            n - root.val) % n =
          n - d
      rw [l18Gapped_shiftLeftValOfGT
        ring root d hdpos hdlt hrd]
      have heq :
          n - (d - root.val) + n - root.val =
            (n - d) + n := by
        omega
      rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero]
      simpa [Nat.mod_mod] using
        (Nat.mod_eq_of_lt (by omega : n - d < n))

theorem l18Gapped_rightNeighbor_shiftLeftSucc
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (hk : k < n) :
    ring.rightNeighbor
        (shiftLeft ring root (k + 1)) =
      shiftLeft ring root k := by
  by_cases hk0 : k = 0
  · subst k
    rw [l18Gapped_shiftLeft_zero]
    by_cases hroot :
        ring.rightNeighbor
            (shiftLeft ring root 1) =
          root
    · exact hroot
    · have hoff :=
        l18Gapped_rightNeighbor_offset_of_ne_root
          ring root
          (shiftLeft ring root 1) hroot
      have heoff :=
        l18Gapped_cyclicOffset_shiftLeft_pos
          ring root 1 (by omega) (by omega)
      have hlt :=
        l18Gapped_cyclicOffset_lt
          ring root
          (ring.rightNeighbor
            (shiftLeft ring root 1))
      rw [hoff, heoff] at hlt
      omega
  · have hkpos : 0 < k := by
      omega
    have heoff :
        cyclicOffset ring root
            (shiftLeft ring root (k + 1)) =
          n - (k + 1) :=
      l18Gapped_cyclicOffset_shiftLeft_pos
        ring root (k + 1)
        (by omega) (by omega)
    have hboff :
        cyclicOffset ring root
            (shiftLeft ring root k) =
          n - k :=
      l18Gapped_cyclicOffset_shiftLeft_pos
        ring root k hkpos (by omega)
    have hne :
        ring.rightNeighbor
            (shiftLeft ring root (k + 1)) ≠
          root := by
      intro hroot
      have hp :=
        l18Gapped_predecessor_offset_of_right_root
          ring root
          (shiftLeft ring root (k + 1))
          hroot
      rw [heoff] at hp
      omega
    apply
      l18Gapped_cyclicOffset_injective
        ring root
    calc
      cyclicOffset ring root
          (ring.rightNeighbor
            (shiftLeft ring root (k + 1))) =
          cyclicOffset ring root
              (shiftLeft ring root (k + 1)) + 1 :=
        l18Gapped_rightNeighbor_offset_of_ne_root
          ring root
          (shiftLeft ring root (k + 1)) hne
      _ = (n - (k + 1)) + 1 := by
        rw [heoff]
      _ = n - k := by
        omega
      _ =
          cyclicOffset ring root
            (shiftLeft ring root k) := hboff.symm

/-! -------------------------------------------------------------------------
    Pair-level dist/last projection of one P_PL-prime interaction
------------------------------------------------------------------------- -/


theorem l18Gapped_determineMode_fields
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.leader = l.leader ∧
      d.2.leader = r.leader ∧
      d.1.dist = l.dist ∧
      d.2.dist = r.dist ∧
      d.1.last = l.last ∧
      d.2.last = r.last := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem l18Gapped_moveToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
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


theorem l18Gapped_pprimeMoveToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := pprimeMoveToken hpsi kind l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
  unfold pprimeMoveToken
  dsimp only
  have h :=
    l18Gapped_moveToken_dist_last
      hpsi kind l { r with mode := false }
  dsimp only at h
  simpa using h


theorem l18Gapped_eliminate_dist_last
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let q := PPL.eliminateLeaders l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
  dsimp only
  have hl :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  have hr :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    ⟨congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.dist) hl,
      congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.last) hl,
      congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.dist) hr,
      congrArg
        (fun z : PPL.Elim.OtherFields psi kappa => z.last) hr⟩


/-- Public line-4 / line-9 projection for the P_PL-prime Algorithm-2/3
prefix.  This is the common single-letter write lemma used by both gapped
sweeps. -/
theorem l18Gapped_pprimeCreate_fields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    let q := pprimeCreateLeader hpsi l r
    q.1.dist = l.dist ∧
      q.2.dist.val =
        (if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi)) ∧
      q.2.last = r.last ∧
      q.1.last =
        (if r.leader = true then
          true
        else if
            ((l.dist.val + 1) % (2 * psi) = 0) ∨
              ((l.dist.val + 1) % (2 * psi) = psi) then
          false
        else
          r.last) := by
  let d := PPL.determineMode l r
  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(d.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩
  let r0 : State psi kappa :=
    { d.2 with dist := tmp }
  let l0 : State psi kappa :=
    if r0.leader = true then
      { d.1 with last := true }
    else if
        (r0.dist.val = 0) ∨
          (r0.dist.val = psi) then
      { d.1 with last := false }
    else
      { d.1 with last := r0.last }
  let b :=
    pprimeMoveToken hpsi .black l0 r0
  let w :=
    pprimeMoveToken hpsi .white b.1 b.2


  have hd := l18Gapped_determineMode_fields l r
  dsimp only at hd
  rcases hd with
    ⟨hdLL, hdRL, hdLD, hdRD, hdLLast, hdRLast⟩


  have htmp :
      tmp.val =
        if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi) := by
    dsimp only [tmp]
    rw [hdRL, hdLD]
    split <;> rfl


  have hr0Leader :
      r0.leader = r.leader := by
    dsimp only [r0]
    simpa only [d] using hdRL
  have hr0Last :
      r0.last = r.last := by
    dsimp only [r0]
    simpa only [d] using hdRLast
  have hr0DistVal :
      r0.dist.val =
        if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi) := by
    calc
      r0.dist.val = tmp.val := rfl
      _ = _ := htmp


  have hl0Dist :
      l0.dist = l.dist := by
    dsimp only [l0]
    split
    · simpa only [d] using hdLD
    · split
      · simpa only [d] using hdLD
      · simpa only [d] using hdLD
  have hl0Last :
      l0.last =
        (if r.leader = true then
          true
        else if
            ((l.dist.val + 1) % (2 * psi) = 0) ∨
              ((l.dist.val + 1) % (2 * psi) = psi) then
          false
        else
          r.last) := by
    dsimp only [l0]
    by_cases hrl : r0.leader = true
    · rw [if_pos hrl]
      have hr : r.leader = true := by
        calc
          r.leader = r0.leader := hr0Leader.symm
          _ = true := hrl
      rw [if_pos hr]
    · rw [if_neg hrl]
      have hr : ¬ r.leader = true := by
        intro hrt
        apply hrl
        calc
          r0.leader = r.leader := hr0Leader
          _ = true := hrt
      rw [if_neg hr]
      have hdist :
          r0.dist.val =
            (l.dist.val + 1) % (2 * psi) := by
        have hv := hr0DistVal
        rw [if_neg hr] at hv
        exact hv
      rw [hdist, hr0Last]
      split <;> rfl


  have hb :=
    l18Gapped_pprimeMoveToken_dist_last
      hpsi .black l0 r0
  have hw :=
    l18Gapped_pprimeMoveToken_dist_last
      hpsi .white b.1 b.2
  dsimp only at hb hw


  have hdef :
      pprimeCreateLeader hpsi l r = w := by
    rfl
  rw [hdef]


  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hw.1.trans (hb.1.trans hl0Dist)
  · have hdist :
        w.2.dist = r0.dist :=
      hw.2.2.1.trans hb.2.2.1
    calc
      w.2.dist.val = r0.dist.val :=
        congrArg Fin.val hdist
      _ = _ := hr0DistVal
  · exact
      hw.2.2.2.trans
        (hb.2.2.2.trans hr0Last)
  · exact
      hw.2.1.trans
        (hb.2.1.trans hl0Last)


theorem l18Gapped_pprimePpl_fields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    let q := pprimePpl hpsi l r
    q.1.dist = l.dist ∧
      q.2.dist.val =
        (if r.leader = true then
          0
        else
          (l.dist.val + 1) % (2 * psi)) ∧
      q.2.last = r.last ∧
      q.1.last =
        (if r.leader = true then
          true
        else if
            ((l.dist.val + 1) % (2 * psi) = 0) ∨
              ((l.dist.val + 1) % (2 * psi) = psi) then
          false
        else
          r.last) := by
  let c := pprimeCreateLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc :=
    l18Gapped_pprimeCreate_fields hpsi l r
  have he :=
    l18Gapped_eliminate_dist_last c.1 c.2
  dsimp only at hc he
  have hdef :
      pprimePpl hpsi l r = q := by
    rfl
  rw [hdef]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact he.1.trans hc.1
  · have hdist :
        q.2.dist = c.2.dist :=
      he.2.2.1
    calc
      q.2.dist.val = c.2.dist.val :=
        congrArg Fin.val hdist
      _ = _ := hc.2.1
  · exact he.2.2.2.trans hc.2.2.1
  · exact he.2.1.trans hc.2.2.2


/-- Configuration-level selected-pair projection. -/
theorem l18Gapped_step_pair_fields
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    let j := ring.rightNeighbor e
    (pprimeStep ring C e e).dist = (C e).dist ∧
      (pprimeStep ring C e j).dist.val =
        (if (C j).leader = true then
          0
        else
          ((C e).dist.val + 1) % (2 * psi)) ∧
      (pprimeStep ring C e j).last = (C j).last ∧
      (pprimeStep ring C e e).last =
        (if (C j).leader = true then
          true
        else if
            (((C e).dist.val + 1) % (2 * psi) = 0) ∨
              (((C e).dist.val + 1) % (2 * psi) = psi) then
          false
        else
          (C j).last) := by
  let j := ring.rightNeighbor e
  have hne : j ≠ e := by
    dsimp only [j]
    exact
      PPL.Convergence.L18Bridge.l18RightNeighbor_ne_self
        hn3 ring e
  have hlocal :=
    l18Gapped_pprimePpl_fields
      hpsi (C e) (C j)
  dsimp only at hlocal
  simpa [j, pprimeStep, pprimeProtocol,
    pprimeTransition, PopulationProtocol.step,
    hpsi, hne] using hlocal


/-- Named untouched-site frame used by both prefix inductions. -/
theorem l18Gapped_step_frame
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    pprimeStep ring C e i = C i := by
  simp [pprimeStep, pprimeProtocol,
    PopulationProtocol.step, hie, hir]


/-! -------------------------------------------------------------------------
    CPB / unique-root iteration
------------------------------------------------------------------------- -/


theorem l18Gapped_cpb_unique_run
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    CPB ring (runPPrime ring C schedule) ∧
      L18UniqueLeaderAt
        (runPPrime ring C schedule) root := by
  induction schedule generalizing C with
  | nil =>
      exact ⟨hCPB, hUnique⟩
  | cons e rest ih =>
      have hstep :=
        PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
          hn3 hpsi ring root C e hCPB hUnique
      exact
        ih (C := pprimeStep ring C e)
          hstep.1 hstep.2


/-! -------------------------------------------------------------------------
    Root phase: once zero, root.dist is closed under arbitrary letters
------------------------------------------------------------------------- -/


def L18RootDistanceAt
    {n psi kappa : Nat}
    (root : Fin n)
    (C : Config n psi kappa) : Prop :=
  (C root).dist.val = 0


theorem l18Gapped_rootDistance_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hUnique : L18UniqueLeaderAt C root)
    (hzero : L18RootDistanceAt root C) :
    L18RootDistanceAt root
      (pprimeStep ring C e) := by
  unfold L18RootDistanceAt at hzero ⊢
  let j := ring.rightNeighbor e
  have hp :=
    l18Gapped_step_pair_fields
      hn3 hpsi ring C e
  dsimp only [j] at hp
  by_cases hre : root = e
  · subst e
    exact
      congrArg Fin.val hp.1 |>.trans hzero
  · by_cases hrj : root = ring.rightNeighbor e
    · have hlead :
          (C (ring.rightNeighbor e)).leader = true := by
        exact
          (hUnique (ring.rightNeighbor e)).mpr hrj.symm
      have hd0 :
          (pprimeStep ring C e
              (ring.rightNeighbor e)).dist.val =
            0 := by
        have hd := hp.2.1
        rw [hlead] at hd
        exact hd
      calc
        (pprimeStep ring C e root).dist.val =
            (pprimeStep ring C e
              (ring.rightNeighbor e)).dist.val := by
          rw [hrj]
        _ = 0 := hd0
    · have hf :=
        l18Gapped_step_frame
          ring C e root hre hrj
      exact
        (congrArg
          (fun q : State psi kappa =>
            q.dist.val) hf).trans hzero

theorem l18Gapped_rootDistance_run
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (hzero : L18RootDistanceAt root C) :
    let D := runPPrime ring C schedule
    CPB ring D ∧
      L18UniqueLeaderAt D root ∧
      L18RootDistanceAt root D := by
  induction schedule generalizing C with
  | nil =>
      exact ⟨hCPB, hUnique, hzero⟩
  | cons e rest ih =>
      have hs :=
        PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
          hn3 hpsi ring root C e hCPB hUnique
      have hz :=
        l18Gapped_rootDistance_step
          hn3 hpsi ring root C e hUnique hzero
      exact
        ih (C := pprimeStep ring C e)
          hs.1 hs.2 hz


theorem l18Gapped_rootReset_of_sublist
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (hsub :
      [shiftLeft ring root 1].Sublist schedule) :
    let D := runPPrime ring C schedule
    CPB ring D ∧
      L18UniqueLeaderAt D root ∧
      L18RootDistanceAt root D := by
  induction schedule generalizing C with
  | nil =>
      have hlen :
          ([shiftLeft ring root 1] : DetSchedule n).length ≤ 0 := by
        simpa using hsub.length_le
      simp at hlen
  | cons fired rest ih =>
      let requested := shiftLeft ring root 1
      by_cases hfire : fired = requested
      · subst fired
        have hroot :
            (C root).leader = true :=
          (hUnique root).mpr rfl
        have hz :
            L18RootDistanceAt root
              (pprimeStep ring C requested) := by
          unfold L18RootDistanceAt
          exact
            l18RootReset_selected_dist_zero
              hn3 hpsi ring root C hroot
        have hs :=
          PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
            hn3 hpsi ring root C requested hCPB hUnique
        have htail :=
          l18Gapped_rootDistance_run
            hn3 hpsi ring root
            (pprimeStep ring C requested)
            rest hs.1 hs.2 hz
        simpa [runPPrime] using htail
      · have htailSub :
            [requested].Sublist rest := by
          rcases
              List.sublist_cons_iff.mp hsub with
            hskip | ⟨tail, heq, _ht⟩
          · simpa [requested] using hskip
          · have hhead :
                requested = fired := by
              exact
                (List.cons.inj
                  (by simpa [requested] using heq)).1
            exact False.elim (hfire hhead.symm)
        have hs :=
          PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
            hn3 hpsi ring root C fired hCPB hUnique
        have htail :=
          ih (C := pprimeStep ring C fired)
            hs.1 hs.2
            (by simpa [requested] using htailSub)
        simpa [runPPrime] using htail


theorem l18GappedRootResetPhase_proved :
    L18GappedRootResetPhase := by
  unfold L18GappedRootResetPhase
  intro n psi kappa hn3 hpsi
  intro ring root C schedule
  intro hCPB hUnique hsub
  right
  have hsub' :
      [shiftLeft ring root 1].Sublist schedule := by
    simpa [l18RootResetWord] using hsub
  exact
    l18Gapped_rootReset_of_sublist
      hn3 hpsi ring root C schedule
      hCPB hUnique hsub'


/-! -------------------------------------------------------------------------
    Distance phase: clockwise canonical prefix
------------------------------------------------------------------------- -/


def L18DistancePrefixAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n,
    cyclicOffset ring root i ≤ k →
      (C i).dist.val =
        cyclicOffset ring root i % (2 * psi)


/-- Arbitrary-letter distance-prefix frame.  Truth audit: TRUE under exactly
the stated unique-root + fixed-prefix hypotheses.  The only possible write is
to the responder.  If the responder is root, P_PL-prime forces zero; otherwise
its predecessor lies one position earlier and is already fixed. -/
def L18DistancePrefixStepRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (C : Config n psi kappa)
    (e : Fin n),
    L18UniqueLeaderAt C root →
    L18DistancePrefixAt ring root k C →
    L18DistancePrefixAt ring root k
      (pprimeStep ring C e)


theorem l18DistancePrefixStepRow_proved :
    L18DistancePrefixStepRow := by
  unfold L18DistancePrefixStepRow
  intro n psi kappa hn3 hpsi
  intro ring root k C e
  intro hUnique hPrefix
  let j := ring.rightNeighbor e
  have hp :=
    l18Gapped_step_pair_fields
      hn3 hpsi ring C e
  dsimp only [j] at hp
  intro i hi


  by_cases hie : i = e
  · subst i
    have hp0 := hPrefix e hi
    exact
      congrArg Fin.val hp.1 |>.trans hp0


  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      by_cases hjroot :
          ring.rightNeighbor e = root
      · have hlead :
            (C (ring.rightNeighbor e)).leader = true :=
          (hUnique (ring.rightNeighbor e)).mpr hjroot
        have hd0 :
            (pprimeStep ring C e
                (ring.rightNeighbor e)).dist.val =
              0 := by
          have hd := hp.2.1
          rw [hlead] at hd
          exact hd
        calc
          (pprimeStep ring C e
              (ring.rightNeighbor e)).dist.val =
              0 := hd0
          _ =
              cyclicOffset ring root
                  (ring.rightNeighbor e) %
                (2 * psi) := by
            rw [hjroot, l18Gapped_cyclicOffset_root]
            simp
      · have hlead :
            (C (ring.rightNeighbor e)).leader = false := by
          cases h :
              (C (ring.rightNeighbor e)).leader with
          | false => rfl
          | true =>
              exact False.elim
                (hjroot
                  ((hUnique
                    (ring.rightNeighbor e)).mp h))
        have hoff :
            cyclicOffset ring root
                (ring.rightNeighbor e) =
              cyclicOffset ring root e + 1 :=
          l18Gapped_rightNeighbor_offset_of_ne_root
            ring root e hjroot
        have hePrefix :
            cyclicOffset ring root e ≤ k := by
          rw [hoff] at hi
          omega
        have heDist := hPrefix e hePrefix
        have hd :
            (pprimeStep ring C e
                (ring.rightNeighbor e)).dist.val =
              ((C e).dist.val + 1) %
                (2 * psi) := by
          have hd0 := hp.2.1
          rw [hlead] at hd0
          exact hd0
        calc
          (pprimeStep ring C e
              (ring.rightNeighbor e)).dist.val =
              ((C e).dist.val + 1) %
                (2 * psi) := hd
          _ =
              (cyclicOffset ring root e + 1) %
                (2 * psi) := by
            rw [heDist, Nat.mod_add_mod]
          _ =
              cyclicOffset ring root
                  (ring.rightNeighbor e) %
                (2 * psi) := by
            rw [hoff]


    · have hf :=
        l18Gapped_step_frame
          ring C e i hie hij
      rw [hf]
      exact hPrefix i hi


theorem l18Gapped_distancePrefix_zero
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hzero : (C root).dist.val = 0) :
    L18DistancePrefixAt ring root 0 C := by
  intro i hi
  have hoff :
      cyclicOffset ring root i = 0 := by
    omega
  have hir : i = root := by
    apply l18Gapped_cyclicOffset_injective
      ring root
    rw [hoff, l18Gapped_cyclicOffset_root]
  subst i
  simpa using hzero


theorem l18Gapped_distance_selected_extends
    {n psi kappa k : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hk : k < n - 1)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hUnique : L18UniqueLeaderAt C root)
    (hPrefix :
      L18DistancePrefixAt ring root k C) :
    L18DistancePrefixAt ring root (k + 1)
      (pprimeStep ring C
        (shiftRight ring root k)) := by
  let e := shiftRight ring root k
  let j := ring.rightNeighbor e


  have hkN : k < n := by
    omega
  have hk1N : k + 1 < n := by
    omega
  have heoff :
      cyclicOffset ring root e = k := by
    dsimp only [e]
    exact
      l18Gapped_cyclicOffset_shiftRight_of_lt
        ring root k hkN
  have hjsite :
      j = shiftRight ring root (k + 1) := by
    dsimp only [j, e]
    exact l18Gapped_rightNeighbor_shiftRight
      ring root k
  have hjoff :
      cyclicOffset ring root j = k + 1 := by
    rw [hjsite]
    exact
      l18Gapped_cyclicOffset_shiftRight_of_lt
        ring root (k + 1) hk1N
  have hjroot : j ≠ root := by
    intro h
    have hz :
        cyclicOffset ring root j = 0 := by
      rw [h, l18Gapped_cyclicOffset_root]
    rw [hjoff] at hz
    omega
  have hjLeader :
      (C j).leader = false := by
    cases h : (C j).leader with
    | false => rfl
    | true =>
        exact False.elim
          (hjroot ((hUnique j).mp h))


  have hp :=
    l18Gapped_step_pair_fields
      hn3 hpsi ring C e
  dsimp only [j] at hp


  have hpres :=
    l18DistancePrefixStepRow_proved
      hn3 hpsi ring root k C e
      hUnique hPrefix


  intro i hi
  by_cases hold :
      cyclicOffset ring root i ≤ k
  · exact hpres i hold
  · have hoff :
        cyclicOffset ring root i = k + 1 := by
      omega
    have hij : i = j := by
      apply l18Gapped_cyclicOffset_injective
        ring root
      rw [hoff, hjoff]
    subst i
    have heLe :
        cyclicOffset ring root e ≤ k := by
      rw [heoff]
      exact Nat.le_refl k
    have heDist :
        (C e).dist.val = k % (2 * psi) := by
      have h := hPrefix e heLe
      rw [heoff] at h
      exact h
    have hd :
        (pprimeStep ring C e
            (ring.rightNeighbor e)).dist.val =
          ((C e).dist.val + 1) %
            (2 * psi) := by
      have hd0 := hp.2.1
      rw [hjLeader] at hd0
      exact hd0
    calc
      (pprimeStep ring C e j).dist.val =
          ((C e).dist.val + 1) %
            (2 * psi) := by
        simpa only [j] using hd
      _ = (k + 1) % (2 * psi) := by
        rw [heDist, Nat.mod_add_mod]
      _ =
          cyclicOffset ring root j %
            (2 * psi) := by
        rw [hjoff]


def l18GappedRightRange
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    Nat → Nat → DetSchedule n
  | _, 0 => []
  | k, m + 1 =>
      shiftRight ring root k ::
        l18GappedRightRange ring root (k + 1) m


theorem l18GappedRightRange_eq_ofFn
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ k m : Nat,
      l18GappedRightRange ring root k m =
        List.ofFn
          (fun x : Fin m =>
            shiftRight ring root (k + x.val)) := by
  intro k m
  induction m generalizing k with
  | zero =>
      rfl
  | succ m ih =>
      simp [l18GappedRightRange,
        List.ofFn_succ, ih,
        Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]


theorem l18GappedRightRange_zero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (m : Nat) :
    l18GappedRightRange ring root 0 m =
      PPL.seqR ring root m := by
  rw [l18GappedRightRange_eq_ofFn]
  simp [PPL.seqR]


theorem l18Gapped_distanceRange_run
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (k m : Nat)
      (C : Config n psi kappa)
      (schedule : DetSchedule n),
      k + m ≤ n - 1 →
      CPB ring C →
      L18UniqueLeaderAt C root →
      L18DistancePrefixAt ring root k C →
      (l18GappedRightRange ring root k m).Sublist
        schedule →
      let D := runPPrime ring C schedule
      CPB ring D ∧
        L18UniqueLeaderAt D root ∧
        L18DistancePrefixAt ring root (k + m) D := by
  intro k m C schedule
  intro hbound hCPB hUnique hPrefix hsub
  induction schedule generalizing C k m with
  | nil =>
      cases m with
      | zero =>
          change
            CPB ring C ∧
              L18UniqueLeaderAt C root ∧
              L18DistancePrefixAt ring root k C
          exact ⟨hCPB, hUnique, hPrefix⟩
      | succ m =>
          have hlen :=
            hsub.length_le
          simp [l18GappedRightRange] at hlen


  | cons fired rest ih =>
      cases m with
      | zero =>
          have hs :=
            PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
              hn3 hpsi ring root C fired
              hCPB hUnique
          have hp :=
            l18DistancePrefixStepRow_proved
              hn3 hpsi ring root k C fired
              hUnique hPrefix
          have htail :=
            ih (C := pprimeStep ring C fired)
              (k := k) (m := 0)
              (by omega)
              hs.1 hs.2 hp
              (List.nil_sublist rest)
          simpa [runPPrime] using htail


      | succ m =>
          let requested := shiftRight ring root k
          let tail :=
            l18GappedRightRange ring root (k + 1) m
          have hword :
              l18GappedRightRange ring root k (m + 1) =
                requested :: tail := by
            rfl
          rw [hword] at hsub


          by_cases hfire : fired = requested
          · subst fired
            have htailSub :
                tail.Sublist rest := by
              rcases
                  List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact
                  (List.sublist_cons_self requested tail).trans
                    hskip
              · cases heq
                exact ht


            have hs :=
              PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
                hn3 hpsi ring root C requested
                hCPB hUnique
            have hp :=
              l18Gapped_distance_selected_extends
                hn3 hpsi
                (by omega : k < n - 1)
                ring root C hUnique hPrefix
            have htail :=
              ih
                (C := pprimeStep ring C requested)
                (k := k + 1) (m := m)
                (by omega)
                hs.1 hs.2 hp
                (by simpa [tail] using htailSub)
            have hidx :
                k + 1 + m = k + (m + 1) := by
              omega
            rw [hidx] at htail
            simpa [runPPrime] using htail


          · have htailSub :
                (requested :: tail).Sublist rest := by
              rcases
                  List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, _ht⟩
              · exact hskip
              · have hhead :
                    requested = fired :=
                  (List.cons.inj heq).1
                exact False.elim (hfire hhead.symm)


            have hs :=
              PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
                hn3 hpsi ring root C fired
                hCPB hUnique
            have hp :=
              l18DistancePrefixStepRow_proved
                hn3 hpsi ring root k C fired
                hUnique hPrefix
            have htail :=
              ih
                (C := pprimeStep ring C fired)
                (k := k) (m := m + 1)
                hbound
                hs.1 hs.2 hp
                (by
                  rw [hword]
                  exact htailSub)
            simpa [runPPrime] using htail


theorem l18Gapped_canonicalDistance_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hUnique : L18UniqueLeaderAt C root)
    (hDist : L18CanonicalDistanceAt ring root C) :
    L18CanonicalDistanceAt ring root
      (pprimeStep ring C e) := by
  have hpref :
      L18DistancePrefixAt ring root (n - 1) C := by
    intro i _hi
    exact hDist i
  have hstep :=
    l18DistancePrefixStepRow_proved
      hn3 hpsi ring root (n - 1)
      C e hUnique hpref
  intro i
  exact
    hstep i (by
      have hi :=
        l18Gapped_cyclicOffset_lt ring root i
      omega)


theorem l18GappedDistanceSweepPhase_proved :
    L18GappedDistanceSweepPhase := by
  unfold L18GappedDistanceSweepPhase
  intro n psi kappa hn3 hpsi
  intro ring root C schedule
  intro hCPB hUnique hzero hsub
  right


  have hp0 :
      L18DistancePrefixAt ring root 0 C :=
    l18Gapped_distancePrefix_zero
      ring root C hzero
  have hsub' :
      (l18GappedRightRange
        ring root 0 (n - 1)).Sublist schedule := by
    rw [l18GappedRightRange_zero]
    simpa [l18DistanceWord] using hsub


  have hrun :=
    l18Gapped_distanceRange_run
      (n := n) (psi := psi) (kappa := kappa)
      hn3 hpsi ring root
      0 (n - 1) C schedule
      (by omega)
      hCPB hUnique hp0 hsub'
  dsimp only at hrun


  refine ⟨hrun.1, hrun.2.1, ?_⟩
  intro i
  exact
    hrun.2.2 i (by
      have hi :=
        l18Gapped_cyclicOffset_lt ring root i
      omega)


/-! -------------------------------------------------------------------------
    Last phase arithmetic
------------------------------------------------------------------------- -/


def l18GappedLastThreshold
    (n psi : Nat) : Nat :=
  psi * (segmentCount n psi - 1)


theorem l18Gapped_segmentCount_pos
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) :
    0 < segmentCount n psi := by
  unfold segmentCount
  have hle :
      1 ≤ (n + psi - 1) / psi := by
    apply (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).2
    simp only [Nat.one_mul]
    omega
  omega


theorem l18Gapped_lastThreshold_lt
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) :
    l18GappedLastThreshold n psi < n := by
  let z := segmentCount n psi
  have hzpos : 0 < z := by
    dsimp only [z]
    exact l18Gapped_segmentCount_pos hn3 hpsi
  have hmul :
      z * psi ≤ n + psi - 1 := by
    dsimp only [z]
    unfold segmentCount
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
      (z - 1) * psi ≤ n - 1 := by
    omega
  unfold l18GappedLastThreshold
  dsimp only [z] at hsmall
  have hsmall' :
      psi * (segmentCount n psi - 1) ≤
        n - 1 := by
    simpa only [Nat.mul_comm] using hsmall
  omega


theorem l18Gapped_lastThreshold_upper
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) :
    n ≤ l18GappedLastThreshold n psi + psi := by
  let z := segmentCount n psi
  have hzpos : 0 < z := by
    dsimp only [z]
    exact l18Gapped_segmentCount_pos hn3 hpsi
  have hrem :
      (n + psi - 1) % psi < psi :=
    Nat.mod_lt _ (by omega)
  have hdec :=
    Nat.mod_add_div (n + psi - 1) psi
  have hceil :
      n ≤ psi * ((n + psi - 1) / psi) := by
    omega
  have hzsplit :
      z = (z - 1) + 1 := by
    omega
  unfold l18GappedLastThreshold
  dsimp only [z] at hzsplit
  calc
    n ≤
        psi * segmentCount n psi := by
      simpa only [segmentCount] using hceil
    _ =
        psi * (segmentCount n psi - 1) +
          psi := by
      rw [hzsplit, Nat.mul_add]
      simp


theorem l18Gapped_psiMultiple_border
    (psi t : Nat)
    (hpsi : 0 < psi) :
    ((psi * t) % (2 * psi) = 0) ∨
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
    left
    rw [ht, heq]
    simp
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
    right
    rw [ht, heq, Nat.add_mod]
    have hsmall :
        psi % (2 * psi) = psi :=
      Nat.mod_eq_of_lt (by omega)
    rw [hsmall, Nat.mul_mod_right, Nat.add_zero]
    exact hsmall


theorem l18Gapped_border_mod_psi_zero
    (psi b : Nat)
    (hpsi : 0 < psi)
    (hborder :
      (b % (2 * psi) = 0) ∨
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


theorem l18Gapped_border_eq_threshold
    {n psi b : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hborder :
      (b % (2 * psi) = 0) ∨
        (b % (2 * psi) = psi))
    (hge : l18GappedLastThreshold n psi ≤ b)
    (hlt : b < n) :
    b = l18GappedLastThreshold n psi := by
  let t := segmentCount n psi - 1
  let q := b / psi
  have hbUpper :
      b < l18GappedLastThreshold n psi + psi :=
    Nat.lt_of_lt_of_le hlt
      (l18Gapped_lastThreshold_upper hn3 hpsi)
  have hmod :
      b % psi = 0 :=
    l18Gapped_border_mod_psi_zero
      psi b (by omega) hborder
  have hdec := Nat.mod_add_div b psi
  rw [hmod, Nat.zero_add] at hdec
  have hbq :
      b = psi * q := by
    dsimp only [q]
    exact hdec.symm
  have hleMul :
      psi * t ≤ psi * q := by
    simpa only [l18GappedLastThreshold, t, hbq] using hge
  have htq :
      t ≤ q :=
    Nat.le_of_mul_le_mul_left hleMul (by omega)
  have hltMul :
      psi * q < psi * (t + 1) := by
    calc
      psi * q = b := hbq.symm
      _ < l18GappedLastThreshold n psi + psi := hbUpper
      _ = psi * (t + 1) := by
        dsimp only [t]
        rw [Nat.mul_add]
        simp [l18GappedLastThreshold]
  have hqt :
      q < t + 1 :=
    (Nat.mul_lt_mul_left
      (by omega : 0 < psi)).mp hltMul
  have hqeq : q = t := by
    omega
  rw [hbq, hqeq]
  rfl


theorem l18Gapped_border_forces_below_threshold
    {n psi a : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ha : a + 1 < n)
    (hborder :
      (((a + 1) % (2 * psi) = 0) ∨
        ((a + 1) % (2 * psi) = psi))) :
    ¬ l18GappedLastThreshold n psi ≤ a := by
  intro hta
  have heq :=
    l18Gapped_border_eq_threshold
      hn3 hpsi hborder
      (by omega) ha
  omega


theorem l18Gapped_nonborder_threshold_step
    {n psi a : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ha : a + 1 < n)
    (hnot :
      ¬ (((a + 1) % (2 * psi) = 0) ∨
        ((a + 1) % (2 * psi) = psi))) :
    (l18GappedLastThreshold n psi ≤ a + 1) ↔
      (l18GappedLastThreshold n psi ≤ a) := by
  constructor
  · intro hnext
    by_cases hcur :
        l18GappedLastThreshold n psi ≤ a
    · exact hcur
    · have heq :
          l18GappedLastThreshold n psi = a + 1 := by
        omega
      have hborder :
          ((l18GappedLastThreshold n psi) %
              (2 * psi) = 0) ∨
            ((l18GappedLastThreshold n psi) %
              (2 * psi) = psi) := by
        unfold l18GappedLastThreshold
        exact
          l18Gapped_psiMultiple_border
            psi
            (segmentCount n psi - 1)
            (by omega)
      rw [heq] at hborder
      exact False.elim (hnot hborder)
  · intro hcur
    omega


/-! -------------------------------------------------------------------------
    Last phase: counterclockwise fixed suffix
------------------------------------------------------------------------- -/


def L18CanonicalLastAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n,
    (C i).last = true ↔
      l18GappedLastThreshold n psi ≤
        cyclicOffset ring root i


def L18LastPrefixAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n,
    n - k ≤ cyclicOffset ring root i →
      ((C i).last = true ↔
        l18GappedLastThreshold n psi ≤
          cyclicOffset ring root i)


theorem l18Gapped_responder_dist_idempotent
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hUnique : L18UniqueLeaderAt C root)
    (hDist : L18CanonicalDistanceAt ring root C) :
    (pprimeStep ring C e
      (ring.rightNeighbor e)).dist =
      (C (ring.rightNeighbor e)).dist := by
  let j := ring.rightNeighbor e
  have hp :=
    l18Gapped_step_pair_fields
      hn3 hpsi ring C e
  dsimp only [j] at hp
  apply Fin.ext
  by_cases hjroot :
      ring.rightNeighbor e = root
  · have hlead :
        (C (ring.rightNeighbor e)).leader = true :=
      (hUnique (ring.rightNeighbor e)).mpr hjroot
    have hd := hp.2.1
    rw [hlead] at hd
    calc
      (pprimeStep ring C e
          (ring.rightNeighbor e)).dist.val =
          0 := hd
      _ =
          (C (ring.rightNeighbor e)).dist.val := by
        rw [hDist (ring.rightNeighbor e), hjroot,
          l18Gapped_cyclicOffset_root]
        simp
  · have hlead :
        (C (ring.rightNeighbor e)).leader = false := by
      cases h :
          (C (ring.rightNeighbor e)).leader with
      | false => rfl
      | true =>
          exact False.elim
            (hjroot
              ((hUnique
                (ring.rightNeighbor e)).mp h))
    have hoff :=
      l18Gapped_rightNeighbor_offset_of_ne_root
        ring root e hjroot
    have hd :
        (pprimeStep ring C e
            (ring.rightNeighbor e)).dist.val =
          ((C e).dist.val + 1) %
            (2 * psi) := by
      have hd0 := hp.2.1
      rw [hlead] at hd0
      exact hd0
    calc
      (pprimeStep ring C e
          (ring.rightNeighbor e)).dist.val =
          ((C e).dist.val + 1) %
            (2 * psi) := hd
      _ =
          (cyclicOffset ring root e + 1) %
            (2 * psi) := by
        rw [hDist e, Nat.mod_add_mod]
      _ =
          cyclicOffset ring root
              (ring.rightNeighbor e) %
            (2 * psi) := by
        rw [hoff]
      _ =
          (C (ring.rightNeighbor e)).dist.val := by
        rw [hDist (ring.rightNeighbor e)]


/-- Line-9 canonical write.  The responder must already have its canonical
last value unless it is the root; this is precisely the monotone dependency
used by the counterclockwise suffix. -/
theorem l18Gapped_line9_writes_canonical
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hUnique : L18UniqueLeaderAt C root)
    (hDist : L18CanonicalDistanceAt ring root C)
    (hResp :
      ring.rightNeighbor e = root ∨
        ((C (ring.rightNeighbor e)).last = true ↔
          l18GappedLastThreshold n psi ≤
            cyclicOffset ring root
              (ring.rightNeighbor e))) :
    (pprimeStep ring C e e).last = true ↔
      l18GappedLastThreshold n psi ≤
        cyclicOffset ring root e := by
  let j := ring.rightNeighbor e
  have hp :=
    l18Gapped_step_pair_fields
      hn3 hpsi ring C e
  dsimp only [j] at hp
  have hinit := hp.2.2.2


  by_cases hjroot :
      ring.rightNeighbor e = root
  · have hlead :
        (C (ring.rightNeighbor e)).leader = true :=
      (hUnique (ring.rightNeighbor e)).mpr hjroot
    have hpost :
        (pprimeStep ring C e e).last = true := by
      rw [hinit, hlead]
      rfl
    have heoff :
        cyclicOffset ring root e = n - 1 :=
      l18Gapped_predecessor_offset_of_right_root
        ring root e hjroot
    have hthr :=
      l18Gapped_lastThreshold_lt hn3 hpsi
    constructor
    · intro _h
      rw [heoff]
      omega
    · intro _h
      exact hpost


  · have hlead :
        (C (ring.rightNeighbor e)).leader = false := by
      cases h :
          (C (ring.rightNeighbor e)).leader with
      | false => rfl
      | true =>
          exact False.elim
            (hjroot
              ((hUnique
                (ring.rightNeighbor e)).mp h))
    have hoff :
        cyclicOffset ring root
            (ring.rightNeighbor e) =
          cyclicOffset ring root e + 1 :=
      l18Gapped_rightNeighbor_offset_of_ne_root
        ring root e hjroot
    have hofflt :
        cyclicOffset ring root e + 1 < n := by
      have hjlt :=
        l18Gapped_cyclicOffset_lt
          ring root (ring.rightNeighbor e)
      rw [hoff] at hjlt
      exact hjlt


    have htmpOff :
        ((C e).dist.val + 1) % (2 * psi) =
          (cyclicOffset ring root e + 1) %
            (2 * psi) := by
      rw [hDist e, Nat.mod_add_mod]
    have htmp :
        ((C e).dist.val + 1) % (2 * psi) =
          (C (ring.rightNeighbor e)).dist.val := by
      calc
        ((C e).dist.val + 1) % (2 * psi) =
            (cyclicOffset ring root e + 1) %
              (2 * psi) := htmpOff
        _ =
            cyclicOffset ring root
                (ring.rightNeighbor e) %
              (2 * psi) := by
          rw [hoff]
        _ =
            (C (ring.rightNeighbor e)).dist.val := by
          rw [hDist (ring.rightNeighbor e)]


    have hrespLast :
        (C (ring.rightNeighbor e)).last = true ↔
          l18GappedLastThreshold n psi ≤
            cyclicOffset ring root
              (ring.rightNeighbor e) := by
      rcases hResp with hbad | hgood
      · exact False.elim (hjroot hbad)
      · exact hgood


    by_cases hborder :
        (C (ring.rightNeighbor e)).dist.val = 0 ∨
          (C (ring.rightNeighbor e)).dist.val = psi
    · have hborderOff :
          ((cyclicOffset ring root e + 1) %
              (2 * psi) = 0) ∨
            ((cyclicOffset ring root e + 1) %
              (2 * psi) = psi) := by
        rcases hborder with h0 | hp0
        · left
          calc
            (cyclicOffset ring root e + 1) %
                (2 * psi) =
                (C (ring.rightNeighbor e)).dist.val := by
              rw [← hoff, ← hDist (ring.rightNeighbor e)]
            _ = 0 := h0
        · right
          calc
            (cyclicOffset ring root e + 1) %
                (2 * psi) =
                (C (ring.rightNeighbor e)).dist.val := by
              rw [← hoff, ← hDist (ring.rightNeighbor e)]
            _ = psi := hp0
      have hbelow :=
        l18Gapped_border_forces_below_threshold
          hn3 hpsi hofflt hborderOff
      have hpost :
          (pprimeStep ring C e e).last = false := by
        rw [hinit, hlead]
        rw [htmp]
        rw [if_pos hborder]
        simp
      constructor
      · intro htrue
        rw [hpost] at htrue
        contradiction
      · intro hge
        exact False.elim (hbelow hge)


    · have hnotOff :
          ¬ (((cyclicOffset ring root e + 1) %
                (2 * psi) = 0) ∨
              ((cyclicOffset ring root e + 1) %
                (2 * psi) = psi)) := by
        intro hb
        apply hborder
        have hb' := hb
        rw [← htmpOff, htmp] at hb'
        exact hb'
      have hrec :=
        l18Gapped_nonborder_threshold_step
          hn3 hpsi hofflt hnotOff
      have hpost :
          (pprimeStep ring C e e).last =
            (C (ring.rightNeighbor e)).last := by
        rw [hinit, hlead]
        rw [htmp]
        rw [if_neg hborder]
        simp
      rw [hpost]
      constructor
      · intro hjtrue
        have hnext := hrespLast.mp hjtrue
        rw [hoff] at hnext
        exact hrec.mp hnext
      · intro hcur
        have hnext := hrec.mpr hcur
        apply hrespLast.mpr
        rw [hoff]
        exact hnext


theorem l18Gapped_last_frame_of_ne_initiator
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e) :
    (pprimeStep ring C e i).last =
      (C i).last := by
  by_cases hir : i = ring.rightNeighbor e
  · subst i
    have hp :=
      l18Gapped_step_pair_fields
        hn3 hpsi ring C e
    exact hp.2.2.1
  · have hf :=
      l18Gapped_step_frame
        ring C e i hie hir
    exact
      congrArg
        (fun q : State psi kappa => q.last) hf


/-- Arbitrary-letter last-suffix frame.  Truth audit: TRUE only because the
row explicitly assumes global canonical distance; omitting that premise
recreates the unreachable-state defect. -/
def L18LastPrefixStepRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (k : Nat)
    (C : Config n psi kappa)
    (e : Fin n),
    L18UniqueLeaderAt C root →
    L18CanonicalDistanceAt ring root C →
    L18LastPrefixAt ring root k C →
    L18LastPrefixAt ring root k
      (pprimeStep ring C e)


theorem l18LastPrefixStepRow_proved :
    L18LastPrefixStepRow := by
  unfold L18LastPrefixStepRow
  intro n psi kappa hn3 hpsi
  intro ring root k C e
  intro hUnique hDist hPrefix
  intro i hi
  by_cases hie : i = e
  · subst i
    have hResp :
        ring.rightNeighbor e = root ∨
          ((C (ring.rightNeighbor e)).last = true ↔
            l18GappedLastThreshold n psi ≤
              cyclicOffset ring root
                (ring.rightNeighbor e)) := by
      by_cases hjroot :
          ring.rightNeighbor e = root
      · exact Or.inl hjroot
      · right
        have hoff :=
          l18Gapped_rightNeighbor_offset_of_ne_root
            ring root e hjroot
        apply hPrefix
        rw [hoff]
        omega
    exact
      l18Gapped_line9_writes_canonical
        hn3 hpsi ring root C e
        hUnique hDist hResp


  · have hframe :=
      l18Gapped_last_frame_of_ne_initiator
        hn3 hpsi ring C e i hie
    rw [hframe]
    exact hPrefix i hi


theorem l18Gapped_lastPrefix_zero
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa) :
    L18LastPrefixAt ring root 0 C := by
  intro i hi
  have hlt :=
    l18Gapped_cyclicOffset_lt ring root i
  omega


theorem l18Gapped_last_selected_extends
    {n psi kappa k : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hk : k < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hUnique : L18UniqueLeaderAt C root)
    (hDist : L18CanonicalDistanceAt ring root C)
    (hPrefix :
      L18LastPrefixAt ring root k C) :
    L18LastPrefixAt ring root (k + 1)
      (pprimeStep ring C
        (shiftLeft ring root (k + 1))) := by
  let e := shiftLeft ring root (k + 1)
  let j := ring.rightNeighbor e


  have heoff :
      cyclicOffset ring root e =
        n - (k + 1) := by
    dsimp only [e]
    exact
      l18Gapped_cyclicOffset_shiftLeft_pos
        ring root (k + 1)
        (by omega) (by omega)
  have hjsite :
      j = shiftLeft ring root k := by
    dsimp only [j, e]
    exact
      l18Gapped_rightNeighbor_shiftLeftSucc
        ring root k hk


  have hpres :=
    l18LastPrefixStepRow_proved
      hn3 hpsi ring root k C e
      hUnique hDist hPrefix


  have hResp :
      j = root ∨
        ((C j).last = true ↔
          l18GappedLastThreshold n psi ≤
            cyclicOffset ring root j) := by
    by_cases hk0 : k = 0
    · subst k
      left
      rw [hjsite]
      exact l18Gapped_shiftLeft_zero ring root
    · right
      have hkpos : 0 < k := by
        omega
      have hjoff :
          cyclicOffset ring root j = n - k := by
        rw [hjsite]
        exact
          l18Gapped_cyclicOffset_shiftLeft_pos
            ring root k hkpos (by omega)
      apply hPrefix j
      rw [hjoff]
      exact Nat.le_refl (n - k)


  have hnew :=
    l18Gapped_line9_writes_canonical
      hn3 hpsi ring root C e
      hUnique hDist
      (by
        rcases hResp with h | h
        · exact Or.inl h
        · exact Or.inr h)


  intro i hi
  by_cases hold :
      n - k ≤ cyclicOffset ring root i
  · exact hpres i hold
  · have hoff :
        cyclicOffset ring root i =
          n - (k + 1) := by
      omega
    have hie : i = e := by
      apply l18Gapped_cyclicOffset_injective
        ring root
      rw [hoff, heoff]
    subst i
    exact hnew


def l18GappedLeftRange
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    Nat → Nat → DetSchedule n
  | _, 0 => []
  | k, m + 1 =>
      shiftLeft ring root (k + 1) ::
        l18GappedLeftRange ring root (k + 1) m


theorem l18GappedLeftRange_eq_ofFn
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ k m : Nat,
      l18GappedLeftRange ring root k m =
        List.ofFn
          (fun x : Fin m =>
            shiftLeft ring root
              (k + x.val + 1)) := by
  intro k m
  induction m generalizing k with
  | zero =>
      rfl
  | succ m ih =>
      simp [l18GappedLeftRange,
        List.ofFn_succ, ih,
        Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]


theorem l18GappedLeftRange_zero
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (m : Nat) :
    l18GappedLeftRange ring root 0 m =
      PPL.seqL ring root m := by
  rw [l18GappedLeftRange_eq_ofFn]
  simp [PPL.seqL, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]


theorem l18Gapped_lastRange_run
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (k m : Nat)
      (C : Config n psi kappa)
      (schedule : DetSchedule n),
      k + m ≤ n →
      CPB ring C →
      L18UniqueLeaderAt C root →
      L18CanonicalDistanceAt ring root C →
      L18LastPrefixAt ring root k C →
      (l18GappedLeftRange ring root k m).Sublist
        schedule →
      let D := runPPrime ring C schedule
      CPB ring D ∧
        L18UniqueLeaderAt D root ∧
        L18CanonicalDistanceAt ring root D ∧
        L18LastPrefixAt ring root (k + m) D := by
  intro k m C schedule
  intro hbound hCPB hUnique hDist hPrefix hsub
  induction schedule generalizing C k m with
  | nil =>
      cases m with
      | zero =>
          change
            CPB ring C ∧
              L18UniqueLeaderAt C root ∧
              L18CanonicalDistanceAt ring root C ∧
              L18LastPrefixAt ring root k C
          exact
            ⟨hCPB, hUnique, hDist, hPrefix⟩
      | succ m =>
          have hlen := hsub.length_le
          simp [l18GappedLeftRange] at hlen


  | cons fired rest ih =>
      cases m with
      | zero =>
          have hs :=
            PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
              hn3 hpsi ring root C fired
              hCPB hUnique
          have hd :=
            l18Gapped_canonicalDistance_step
              hn3 hpsi ring root C fired
              hUnique hDist
          have hp :=
            l18LastPrefixStepRow_proved
              hn3 hpsi ring root k C fired
              hUnique hDist hPrefix
          have htail :=
            ih (C := pprimeStep ring C fired)
              (k := k) (m := 0)
              (by omega)
              hs.1 hs.2 hd hp
              (List.nil_sublist rest)
          simpa [runPPrime] using htail


      | succ m =>
          let requested :=
            shiftLeft ring root (k + 1)
          let tail :=
            l18GappedLeftRange ring root (k + 1) m
          have hword :
              l18GappedLeftRange ring root k (m + 1) =
                requested :: tail := by
            rfl
          rw [hword] at hsub


          by_cases hfire : fired = requested
          · subst fired
            have htailSub :
                tail.Sublist rest := by
              rcases
                  List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact
                  (List.sublist_cons_self requested tail).trans
                    hskip
              · cases heq
                exact ht


            have hs :=
              PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
                hn3 hpsi ring root C requested
                hCPB hUnique
            have hd :=
              l18Gapped_canonicalDistance_step
                hn3 hpsi ring root C requested
                hUnique hDist
            have hp :=
              l18Gapped_last_selected_extends
                hn3 hpsi
                (by omega : k < n)
                ring root C
                hUnique hDist hPrefix
            have htail :=
              ih
                (C := pprimeStep ring C requested)
                (k := k + 1) (m := m)
                (by omega)
                hs.1 hs.2 hd hp
                (by simpa [tail] using htailSub)
            have hidx :
                k + 1 + m = k + (m + 1) := by
              omega
            rw [hidx] at htail
            simpa [runPPrime] using htail


          · have htailSub :
                (requested :: tail).Sublist rest := by
              rcases
                  List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, _ht⟩
              · exact hskip
              · have hhead :
                    requested = fired :=
                  (List.cons.inj heq).1
                exact False.elim (hfire hhead.symm)


            have hs :=
              PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
                hn3 hpsi ring root C fired
                hCPB hUnique
            have hd :=
              l18Gapped_canonicalDistance_step
                hn3 hpsi ring root C fired
                hUnique hDist
            have hp :=
              l18LastPrefixStepRow_proved
                hn3 hpsi ring root k C fired
                hUnique hDist hPrefix
            have htail :=
              ih
                (C := pprimeStep ring C fired)
                (k := k) (m := m + 1)
                hbound
                hs.1 hs.2 hd hp
                (by
                  rw [hword]
                  exact htailSub)
            simpa [runPPrime] using htail


theorem l18GappedLastSweepPhase_proved :
    L18GappedLastSweepPhase := by
  unfold L18GappedLastSweepPhase
  intro n psi kappa hn3 hpsi
  intro ring root C schedule
  intro hCPB hUnique hDist hsub
  right


  have hp0 :
      L18LastPrefixAt ring root 0 C :=
    l18Gapped_lastPrefix_zero ring root C
  have hsub' :
      (l18GappedLeftRange ring root 0 n).Sublist
        schedule := by
    rw [l18GappedLeftRange_zero]
    simpa [l18LastWord] using hsub


  have hrun :=
    l18Gapped_lastRange_run
      (n := n) (psi := psi) (kappa := kappa)
      hn3 hpsi ring root
      0 n C schedule
      (by omega)
      hCPB hUnique hDist hp0 hsub'
  dsimp only at hrun


  unfold CDLAt
  refine ⟨hrun.1, hrun.2.1, ?_⟩
  intro i
  refine ⟨hrun.2.2.1 i, ?_⟩
  have hlast :=
    hrun.2.2.2 i (by omega)
  simpa [l18GappedLastThreshold] using hlast


end PPL.Convergence.L18


#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_lt
#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_root
#print axioms PPL.Convergence.L18.l18Gapped_shiftRight_zero
#print axioms PPL.Convergence.L18.l18Gapped_shiftLeft_zero
#print axioms PPL.Convergence.L18.l18Gapped_shiftRight_add
#print axioms PPL.Convergence.L18.l18Gapped_rightNeighbor_shiftRight
#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_eq_of_le
#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_eq_of_lt
#print axioms PPL.Convergence.L18.l18Gapped_site_eq_shiftRight_offset
#print axioms PPL.Convergence.L18.l18Gapped_shiftRight_cyclicOffset
#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_injective
#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_shiftRight_of_lt
#print axioms PPL.Convergence.L18.l18Gapped_rightNeighbor_offset_of_ne_root
#print axioms PPL.Convergence.L18.l18Gapped_predecessor_offset_of_right_root
#print axioms PPL.Convergence.L18.l18Gapped_shiftLeftValOfLE
#print axioms PPL.Convergence.L18.l18Gapped_shiftLeftValOfGT
#print axioms PPL.Convergence.L18.l18Gapped_cyclicOffset_shiftLeft_pos
#print axioms PPL.Convergence.L18.l18Gapped_rightNeighbor_shiftLeftSucc
#print axioms PPL.Convergence.L18.l18Gapped_determineMode_fields
#print axioms PPL.Convergence.L18.l18Gapped_moveToken_dist_last
#print axioms PPL.Convergence.L18.l18Gapped_pprimeMoveToken_dist_last
#print axioms PPL.Convergence.L18.l18Gapped_eliminate_dist_last
#print axioms PPL.Convergence.L18.l18Gapped_pprimeCreate_fields
#print axioms PPL.Convergence.L18.l18Gapped_pprimePpl_fields
#print axioms PPL.Convergence.L18.l18Gapped_step_pair_fields
#print axioms PPL.Convergence.L18.l18Gapped_step_frame
#print axioms PPL.Convergence.L18.l18Gapped_cpb_unique_run
#print axioms PPL.Convergence.L18.l18Gapped_rootDistance_step
#print axioms PPL.Convergence.L18.l18Gapped_rootDistance_run
#print axioms PPL.Convergence.L18.l18Gapped_rootReset_of_sublist
#print axioms PPL.Convergence.L18.l18GappedRootResetPhase_proved
#print axioms PPL.Convergence.L18.l18DistancePrefixStepRow_proved
#print axioms PPL.Convergence.L18.l18Gapped_distancePrefix_zero
#print axioms PPL.Convergence.L18.l18Gapped_distance_selected_extends
#print axioms PPL.Convergence.L18.l18GappedRightRange_eq_ofFn
#print axioms PPL.Convergence.L18.l18GappedRightRange_zero
#print axioms PPL.Convergence.L18.l18Gapped_distanceRange_run
#print axioms PPL.Convergence.L18.l18Gapped_canonicalDistance_step
#print axioms PPL.Convergence.L18.l18GappedDistanceSweepPhase_proved
#print axioms PPL.Convergence.L18.l18Gapped_segmentCount_pos
#print axioms PPL.Convergence.L18.l18Gapped_lastThreshold_lt
#print axioms PPL.Convergence.L18.l18Gapped_lastThreshold_upper
#print axioms PPL.Convergence.L18.l18Gapped_psiMultiple_border
#print axioms PPL.Convergence.L18.l18Gapped_border_mod_psi_zero
#print axioms PPL.Convergence.L18.l18Gapped_border_eq_threshold
#print axioms PPL.Convergence.L18.l18Gapped_border_forces_below_threshold
#print axioms PPL.Convergence.L18.l18Gapped_nonborder_threshold_step
#print axioms PPL.Convergence.L18.l18Gapped_responder_dist_idempotent
#print axioms PPL.Convergence.L18.l18Gapped_line9_writes_canonical
#print axioms PPL.Convergence.L18.l18Gapped_last_frame_of_ne_initiator
#print axioms PPL.Convergence.L18.l18LastPrefixStepRow_proved
#print axioms PPL.Convergence.L18.l18Gapped_lastPrefix_zero
#print axioms PPL.Convergence.L18.l18Gapped_last_selected_extends
#print axioms PPL.Convergence.L18.l18GappedLeftRange_eq_ofFn
#print axioms PPL.Convergence.L18.l18GappedLeftRange_zero
#print axioms PPL.Convergence.L18.l18Gapped_lastRange_run
#print axioms PPL.Convergence.L18.l18GappedLastSweepPhase_proved

