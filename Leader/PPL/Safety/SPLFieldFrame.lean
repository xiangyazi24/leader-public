import Leader.PPL.Safety.SPLMoveTokenIdRow
import Leader.PPL.Safety.SPLCreateLeaderStep
import Leader.PPL.Safety.PeacefulProps
import Leader.PPL.SPLEntry.CPBUniqueStepRow
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false



private theorem splField_shiftRight_add
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

@[simp] private theorem splField_shiftRight_n
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    shiftRight ring i n = i := by
  apply Fin.ext
  simp [shiftRight, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]

private theorem splField_cyclicOffset_shiftRight_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) :
    cyclicOffset ring i (shiftRight ring i d) = d := by
  unfold cyclicOffset
  change ((i.val + d) % n + n - i.val) % n = d
  have hi : i.val < n := i.isLt
  have hn : 0 < n := ring.hn
  have hmod :
      (i.val + d) % n =
        if i.val + d < n then
          i.val + d
        else
          i.val + d - n := by
    by_cases h : i.val + d < n
    · rw [if_pos h, Nat.mod_eq_of_lt h]
    · rw [if_neg h]
      have hlt2 : i.val + d < 2 * n := by
        omega
      have hge : n <= i.val + d := by
        omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt
          (by omega : i.val + d - n < n)]
  rw [hmod]
  split
  · have h1 : i.val + d + n - i.val = d + n := by
      omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · have h1 : i.val + d - n + n - i.val = d := by
      omega
    rw [h1, Nat.mod_eq_of_lt hd]

private theorem splField_cyclicOffset_eq_of_le
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n)
    (h : root.val <= i.val) :
    cyclicOffset ring root i =
      i.val - root.val := by
  unfold cyclicOffset
  have hs :
      i.val + n - root.val =
        n + (i.val - root.val) := by
    omega
  rw [hs, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega : i.val - root.val < n)]

private theorem splField_cyclicOffset_eq_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n)
    (h : i.val < root.val) :
    cyclicOffset ring root i =
      i.val + n - root.val := by
  unfold cyclicOffset
  rw [Nat.mod_eq_of_lt (by omega :
    i.val + n - root.val < n)]

@[simp] private theorem splField_cyclicOffset_root
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    cyclicOffset ring root root = 0 := by
  unfold cyclicOffset
  have hs :
      root.val + n - root.val = n := by
    omega
  rw [hs, Nat.mod_self]

private theorem splField_site_eq_shiftRight_offset
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    i =
      shiftRight ring root
        (cyclicOffset ring root i) := by
  by_cases hle : root.val <= i.val
  · have hoff :=
      splField_cyclicOffset_eq_of_le
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
      splField_cyclicOffset_eq_of_lt
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

private theorem splField_rightNeighbor_offset_of_ne_root
    {n : Nat}
    (ring : DirectedRing n)
    (root e : Fin n)
    (hne : Not (ring.rightNeighbor e = root)) :
    cyclicOffset ring root
        (ring.rightNeighbor e) =
      cyclicOffset ring root e + 1 := by
  let x := cyclicOffset ring root e
  have hxlt : x < n := by
    dsimp [x, cyclicOffset]
    exact Nat.mod_lt _ ring.hn
  have heq :
      e = shiftRight ring root x := by
    simpa [x] using
      splField_site_eq_shiftRight_offset
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
        splField_shiftRight_add
          ring root x 1
  by_cases hx1 : x + 1 < n
  · rw [hr]
    simpa [x] using
      splField_cyclicOffset_shiftRight_of_lt
        ring root (x + 1) hx1
  · have hxn : x + 1 = n := by
      omega
    have hroot :
        ring.rightNeighbor e = root := by
      rw [hr, hxn, splField_shiftRight_n]
    exact False.elim (hne hroot)

private theorem splField_predecessor_offset_of_right_root
    {n : Nat}
    (ring : DirectedRing n)
    (root e : Fin n)
    (hroot :
      ring.rightNeighbor e = root) :
    cyclicOffset ring root e = n - 1 := by
  let x := cyclicOffset ring root e
  have hxlt : x < n := by
    dsimp [x, cyclicOffset]
    exact Nat.mod_lt _ ring.hn
  have heq :
      e = shiftRight ring root x := by
    simpa [x] using
      splField_site_eq_shiftRight_offset
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
        splField_shiftRight_add
          ring root x 1
  by_cases hx1 : x + 1 < n
  · have hoff :
        cyclicOffset ring root
            (ring.rightNeighbor e) =
          x + 1 := by
      rw [hr]
      exact
        splField_cyclicOffset_shiftRight_of_lt
          ring root (x + 1) hx1
    rw [hroot, splField_cyclicOffset_root] at hoff
    omega
  · omega

private theorem splField_rightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    Not (ring.rightNeighbor e = e) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega



private theorem splField_lastStart_bounds
    {n psi : Nat}
    (hn : 0 < n)
    (hpsi : 0 < psi) :
    let zeta := segmentCount n psi
    let start := psi * (zeta - 1)
    (And (start < n) (n <= start + psi)) := by
  show
    (And
      (psi * ((n + psi - 1) / psi - 1) < n)
      (n <= psi * ((n + psi - 1) / psi - 1) + psi))
  have hdiv := Nat.mod_add_div (n + psi - 1) psi
  have hrem : (n + psi - 1) % psi < psi :=
    Nat.mod_lt _ hpsi
  have hzpos : 0 < (n + psi - 1) / psi :=
    Nat.div_pos (by omega : psi <= n + psi - 1) hpsi
  have hmul :
      psi * ((n + psi - 1) / psi) =
        psi * ((n + psi - 1) / psi - 1) + psi := by
    have hq :
        (n + psi - 1) / psi =
          ((n + psi - 1) / psi - 1) + 1 := by
      omega
    conv => lhs; rw [hq]
    rw [Nat.mul_add, Nat.mul_one]
  constructor <;> omega


private theorem splField_determineMode_frame
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    (And (d.1.leader = l.leader)
      (And (d.2.leader = r.leader)
        (And (d.1.dist = l.dist)
          (And (d.2.dist = r.dist)
            (And (d.1.last = l.last)
              (And (d.2.last = r.last)
                (And (d.1.id = l.id)
                  (d.2.id = r.id)))))))) := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact
      ⟨rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl⟩


private def splField_line4Tmp
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    Fin (2 * psi) :=
  let d := PPL.determineMode l r
  if d.2.leader = true then
    ⟨0, by omega⟩
  else
    ⟨(d.1.dist.val + 1) % (2 * psi),
      Nat.mod_lt _ (by omega)⟩

private theorem splField_line4Tmp_bridge
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    splField_line4Tmp hpsi l r =
      (PPL.createLeaderThroughLine6
        hpsi l r).tmp := by
  rfl


theorem splAlgorithm2DistWriteIdempotent
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    let p :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C (ring.rightNeighbor e))
    (And
      (¬ PPL.createLeaderLine6Guard
        hpsi (C e) (C (ring.rightNeighbor e)))
      (And
        (p.1.leader = (C e).leader)
        (And
          (p.2.leader = (C (ring.rightNeighbor e)).leader)
          (And
            (p.1.dist = (C e).dist)
            (And
              (p.2.dist = (C (ring.rightNeighbor e)).dist)
              (And
                (p.1.id = (C e).id)
                (p.2.id = (C (ring.rightNeighbor e)).id))))))) := by
  let j := ring.rightNeighbor e
  let l := C e
  let r := C j
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  change
    (And
      (¬ PPL.createLeaderLine6Guard hpsi l r)
      (And
        (p.1.leader = l.leader)
        (And
          (p.2.leader = r.leader)
          (And
            (p.1.dist = l.dist)
            (And
              (p.2.dist = r.dist)
              (And
                (p.1.id = l.id)
                (p.2.id = r.id)))))))

  have hdet :=
    splField_determineMode_frame l r
  dsimp only at hdet
  rcases hdet with
    ⟨hdLLeader, hdRLeader,
      hdLDist, hdRDist,
      hdLLast, hdRLast,
      hdLId, hdRId⟩

  have hgeomE := hC.1.2.2 e
  have hgeomJ := hC.1.2.2 j
  dsimp only at hgeomE hgeomJ
  have huniq := hC.1.2.1

  have htmp :
      splField_line4Tmp hpsi l r =
        r.dist := by
    by_cases hjroot : j = root
    · have hrLeader :
          r.leader = true := by
        exact (huniq j).2 hjroot
      have hrDistVal :
          r.dist.val = 0 := by
        calc
          r.dist.val =
              cyclicOffset ring root j %
                (2 * psi) := hgeomJ.1
          _ = 0 := by
            rw [hjroot,
              splField_cyclicOffset_root]
            simp
      apply Fin.ext
      simp [splField_line4Tmp,
        hdRLeader, hrLeader,
        hrDistVal]
    · have hrLeader :
          r.leader = false := by
        cases hr : r.leader with
        | false =>
            rfl
        | true =>
            exact False.elim
              (hjroot ((huniq j).1 hr))
      have hoff :
          cyclicOffset ring root j =
            cyclicOffset ring root e + 1 := by
        simpa [j] using
          splField_rightNeighbor_offset_of_ne_root
            ring root e
            (by simpa [j] using hjroot)
      apply Fin.ext
      unfold splField_line4Tmp
      dsimp only
      rw [hdRLeader, hrLeader]
      simp only [Bool.false_eq_true, if_false]
      show ((PPL.determineMode l r).1.dist.val + 1) % (2 * psi) =
        r.dist.val
      rw [hdLDist, hgeomE.1,
        hgeomJ.1, hoff]
      rw [Nat.mod_add_mod]

  have hguard :
      ¬ PPL.createLeaderLine6Guard
          hpsi l r := by
    intro hfire
    unfold PPL.createLeaderLine6Guard at hfire
    dsimp only at hfire
    apply hfire.2
    change
      (PPL.createLeaderThroughLine6
          hpsi l r).tmp =
        (PPL.determineMode l r).2.dist
    calc
      (PPL.createLeaderThroughLine6
          hpsi l r).tmp =
          splField_line4Tmp hpsi l r :=
        (splField_line4Tmp_bridge
          hpsi l r).symm
      _ = r.dist := htmp
      _ =
          (PPL.determineMode l r).2.dist :=
        hdRDist.symm

  let s :=
    PPL.createLeaderThroughLine6
      hpsi l r
  have hsL :
      s.left =
        (PPL.determineMode l r).1 := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    try split
    all_goals first
      | rfl
      | (rename_i hfire; exact False.elim (hguard hfire))
  have hsR :
      s.right =
        (PPL.determineMode l r).2 := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    try split
    all_goals first
      | rfl
      | (rename_i hfire; exact False.elim (hguard hfire))
  have hsTmp :
      s.tmp = r.dist := by
    calc
      s.tmp =
          (PPL.createLeaderThroughLine6
            hpsi l r).tmp := rfl
      _ =
          splField_line4Tmp hpsi l r :=
        (splField_line4Tmp_bridge
          hpsi l r).symm
      _ = r.dist := htmp

  have hsLLeader :
      s.left.leader = l.leader := by
    rw [hsL, hdLLeader]
  have hsRLeader :
      s.right.leader = r.leader := by
    rw [hsR, hdRLeader]
  have hsLDist :
      s.left.dist = l.dist := by
    rw [hsL, hdLDist]
  have hsRDist :
      s.right.dist = r.dist := by
    rw [hsR, hdRDist]
  have hsLId :
      s.left.id = l.id := by
    rw [hsL, hdLId]
  have hsRId :
      s.right.id = r.id := by
    rw [hsR, hdRId]

  let r1 : PPL.State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  let l1 : PPL.State psi kappa :=
    if r1.leader = true then
      { s.left with last := true }
    else if
        (Or (r1.dist.val = 0) (r1.dist.val = psi)) then
      { s.left with last := false }
    else
      { s.left with last := r1.last }

  have hr1Leader :
      r1.leader = r.leader := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hsRLeader]
    · simp [r1, hm, hsRLeader]
  have hr1Dist :
      r1.dist = r.dist := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hsTmp]
    · simp [r1, hm, hsRDist]
  have hr1Id :
      r1.id = r.id := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hsRId]
    · simp [r1, hm, hsRId]

  have hl1Leader :
      l1.leader = l.leader := by
    dsimp [l1]
    repeat' split <;>
      simp [hsLLeader]
  have hl1Dist :
      l1.dist = l.dist := by
    dsimp [l1]
    repeat' split <;>
      simp [hsLDist]
  have hl1Id :
      l1.id = l.id := by
    dsimp [l1]
    repeat' split <;>
      simp [hsLId]

  have hpdef :
      p = (l1, r1) := by
    rfl

  refine ⟨hguard, ?_⟩
  rw [hpdef]
  exact
    ⟨hl1Leader, hr1Leader,
      hl1Dist, hr1Dist,
      hl1Id, hr1Id⟩



private theorem splField_canonicalLine9Value
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    let j := ring.rightNeighbor e
    (if (C j).leader = true then
        true
      else if
          (Or ((C j).dist.val = 0) ((C j).dist.val = psi)) then
        false
      else
        (C j).last) =
      (C e).last := by
  let j := ring.rightNeighbor e
  let x := cyclicOffset ring root e
  let y := cyclicOffset ring root j
  let zeta := segmentCount n psi
  let start := psi * (zeta - 1)

  change
    (if (C j).leader = true then
        true
      else if
          (Or ((C j).dist.val = 0) ((C j).dist.val = psi)) then
        false
      else
        (C j).last) =
      (C e).last

  have hgeomE := hC.1.2.2 e
  have hgeomJ := hC.1.2.2 j
  dsimp only at hgeomE hgeomJ
  have huniq := hC.1.2.1
  have hbounds :=
    splField_lastStart_bounds
      ring.hn (by omega : 0 < psi)
  dsimp only at hbounds

  by_cases hjroot : j = root
  · have hrLeader :
        (C j).leader = true :=
      (huniq j).2 hjroot
    have hx :
        x = n - 1 := by
      simpa [x, j] using
        splField_predecessor_offset_of_right_root
          ring root e
          (by simpa [j] using hjroot)
    have hstart :
        start <= x := by
      have hslt :
          start < n := by
        simpa [start, zeta] using hbounds.1
      omega
    have hlastE :
        (C e).last = true := by
      apply hgeomE.2.mpr
      simpa [x, start, zeta] using hstart
    simp [hrLeader, hlastE]

  · have hrLeader :
        (C j).leader = false := by
      cases hr : (C j).leader with
      | false =>
          rfl
      | true =>
          exact False.elim
            (hjroot ((huniq j).1 hr))

    have hyx :
        y = x + 1 := by
      simpa [x, y, j] using
        splField_rightNeighbor_offset_of_ne_root
          ring root e
          (by simpa [j] using hjroot)
    have hylt : y < n := by
      dsimp [y, cyclicOffset]
      exact Nat.mod_lt _ ring.hn

    by_cases hborder :
        (Or ((C j).dist.val = 0) ((C j).dist.val = psi))
    · have hyBorder :
          (Or (y % (2 * psi) = 0) (y % (2 * psi) = psi)) := by
        rcases hborder with h0 | hp
        · left
          calc
            y % (2 * psi) =
                (C j).dist.val := by
              simpa [y] using hgeomJ.1.symm
            _ = 0 := h0
        · right
          calc
            y % (2 * psi) =
                (C j).dist.val := by
              simpa [y] using hgeomJ.1.symm
            _ = psi := hp

      have hbase :
          psi ∣ 2 * psi := by
        refine ⟨2, ?_⟩
        omega
      have hyModPsi :
          y % psi = 0 := by
        calc
          y % psi =
              (y % (2 * psi)) % psi :=
            (Nat.mod_mod_of_dvd
              y hbase).symm
          _ = 0 := by
            rcases hyBorder with h0 | hp
            · rw [h0]
              simp
            · rw [hp]
              simp
      have hyDvd :
          psi ∣ y :=
        Nat.dvd_of_mod_eq_zero hyModPsi

      have hxBefore :
          x < start := by
        by_cases hsx : x < start
        · exact hsx
        · have hstartY :
              start < y := by
            omega
          rcases hyDvd with ⟨k, hyk⟩
          have hmulLt :
              psi * (zeta - 1) <
                psi * k := by
            calc
              psi * (zeta - 1) =
                  start := rfl
              _ < y := hstartY
              _ = psi * k := hyk
          have hkgt :
              zeta - 1 < k :=
            (Nat.mul_lt_mul_left
              (by omega : 0 < psi)).mp
              hmulLt
          have hstep :
              start + psi <= y := by
            calc
              start + psi =
                  psi * ((zeta - 1) + 1) := by
                dsimp [start]
                rw [Nat.mul_add, Nat.mul_one]
              _ <= psi * k :=
                Nat.mul_le_mul_left psi
                  (by omega)
              _ = y := hyk.symm
          have hnle :
              n <= y :=
            Nat.le_trans
              (by simpa [start, zeta]
                using hbounds.2)
              hstep
          omega

      have hlastE :
          (C e).last = false := by
        cases he : (C e).last with
        | false =>
            rfl
        | true =>
            have hs :=
              hgeomE.2.mp he
            have hs' :
                start <= x := by
              simpa [x, start, zeta] using hs
            omega

      simp [hrLeader, hborder, hlastE]

    · have hsame :
          (start <= x) ↔ (start <= y) := by
        constructor
        · intro hs
          omega
        · intro hsy
          by_cases hsx : start <= x
          · exact hsx
          · have hystart :
                y = start := by
              omega
            have hmulmod :
                (psi * (zeta - 1)) %
                    (2 * psi) =
                  psi * ((zeta - 1) % 2) := by
              simpa [Nat.mul_comm 2 psi] using
                Nat.mul_mod_mul_left
                  psi (zeta - 1) 2
            have hyBorder :
                (Or (y % (2 * psi) = 0) (y % (2 * psi) = psi)) := by
              rw [hystart]
              dsimp [start]
              rcases
                  Nat.mod_two_eq_zero_or_one
                    (zeta - 1)
                with hz | ho
              · left
                rw [hmulmod, hz]
                simp
              · right
                rw [hmulmod, ho]
                simp
            have hborder' :
                (Or ((C j).dist.val = 0) ((C j).dist.val = psi)) := by
              rcases hyBorder with h0 | hp
              · left
                calc
                  (C j).dist.val =
                      y % (2 * psi) := by
                    simpa [y] using hgeomJ.1
                  _ = 0 := h0
              · right
                calc
                  (C j).dist.val =
                      y % (2 * psi) := by
                    simpa [y] using hgeomJ.1
                  _ = psi := hp
            exact False.elim (hborder hborder')

      have hlastEq :
          (C j).last = (C e).last := by
        cases he : (C e).last with
        | false =>
            have hxnot :
                ¬ start <= x := by
              intro hs
              have ht :=
                hgeomE.2.mpr
                  (by simpa [x, start, zeta]
                    using hs)
              rw [he] at ht
              contradiction
            have hynot :
                ¬ start <= y := by
              intro hs
              exact hxnot (hsame.mpr hs)
            cases hj : (C j).last with
            | false =>
                rfl
            | true =>
                have hs :=
                  hgeomJ.2.mp hj
                exact False.elim
                  (hynot
                    (by simpa [y, start, zeta]
                      using hs))
        | true =>
            have hsx0 :=
              hgeomE.2.mp he
            have hsx :
                start <= x := by
              simpa [x, start, zeta]
                using hsx0
            have hsy :
                start <= y :=
              hsame.mp hsx
            have hjtrue :
                (C j).last = true :=
              hgeomJ.2.mpr
                (by simpa [y, start, zeta]
                  using hsy)
            simpa [he] using hjtrue

      simpa [hrLeader, hborder]
        using hlastEq


theorem splAlgorithm2LastWriteIdempotent
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    let p :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C (ring.rightNeighbor e))
    (And
      (p.1.last = (C e).last)
      (p.2.last = (C (ring.rightNeighbor e)).last)) := by
  let j := ring.rightNeighbor e
  let l := C e
  let r := C j
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  change
    (And (p.1.last = l.last) (p.2.last = r.last))

  have hrow1 :=
    splAlgorithm2DistWriteIdempotent
      hn3 hpsi ring root C e hC
  have hguard :
      ¬ PPL.createLeaderLine6Guard
          hpsi l r := by
    simpa [l, r, j] using hrow1.1

  have hdet :=
    splField_determineMode_frame l r
  dsimp only at hdet
  rcases hdet with
    ⟨hdLLeader, hdRLeader,
      hdLDist, hdRDist,
      hdLLast, hdRLast,
      hdLId, hdRId⟩

  let s :=
    PPL.createLeaderThroughLine6
      hpsi l r
  have hsL :
      s.left =
        (PPL.determineMode l r).1 := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    try split
    all_goals first
      | rfl
      | (rename_i hfire; exact False.elim (hguard hfire))
  have hsR :
      s.right =
        (PPL.determineMode l r).2 := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    try split
    all_goals first
      | rfl
      | (rename_i hfire; exact False.elim (hguard hfire))

  have htmp :
      s.tmp = r.dist := by
    have hrow :=
      splAlgorithm2DistWriteIdempotent
        hn3 hpsi ring root C e hC
    let p0 :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi l r
    have hpRdist :
        p0.2.dist = r.dist := by
      simpa [p0, l, r, j]
        using hrow.2.2.2.2.1
    have hbridge :=
      splField_line4Tmp_bridge
        hpsi l r
    have htmp0 :
        splField_line4Tmp hpsi l r =
          r.dist := by
      by_cases hjroot : j = root
      · have hgeomJ := hC.1.2.2 j
        dsimp only at hgeomJ
        have huniq := hC.1.2.1
        have hrLeader :
            r.leader = true :=
          (huniq j).2 hjroot
        have hrDistVal :
            r.dist.val = 0 := by
          calc
            r.dist.val =
                cyclicOffset ring root j %
                  (2 * psi) := hgeomJ.1
            _ = 0 := by
              rw [hjroot,
                splField_cyclicOffset_root]
              simp
        apply Fin.ext
        simp [splField_line4Tmp,
          hdRLeader, hrLeader,
          hrDistVal]
      · have hgeomE := hC.1.2.2 e
        have hgeomJ := hC.1.2.2 j
        dsimp only at hgeomE hgeomJ
        have huniq := hC.1.2.1
        have hrLeader :
            r.leader = false := by
          cases hr : r.leader with
          | false =>
              rfl
          | true =>
              exact False.elim
                (hjroot ((huniq j).1 hr))
        have hoff :
            cyclicOffset ring root j =
              cyclicOffset ring root e + 1 := by
          simpa [j] using
            splField_rightNeighbor_offset_of_ne_root
              ring root e
              (by simpa [j] using hjroot)
        apply Fin.ext
        unfold splField_line4Tmp
        dsimp only
        rw [hdRLeader, hrLeader]
        simp only [Bool.false_eq_true, if_false]
        show ((PPL.determineMode l r).1.dist.val + 1) % (2 * psi) =
          r.dist.val
        rw [hdLDist, hgeomE.1,
          hgeomJ.1, hoff]
        rw [Nat.mod_add_mod]
    calc
      s.tmp =
          (PPL.createLeaderThroughLine6
            hpsi l r).tmp := rfl
      _ =
          splField_line4Tmp hpsi l r :=
        hbridge.symm
      _ = r.dist := htmp0

  let r1 : PPL.State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  let l1 : PPL.State psi kappa :=
    if r1.leader = true then
      { s.left with last := true }
    else if
        (Or (r1.dist.val = 0) (r1.dist.val = psi)) then
      { s.left with last := false }
    else
      { s.left with last := r1.last }

  have hsRLeader :
      s.right.leader = r.leader := by
    rw [hsR, hdRLeader]
  have hsRDist :
      s.right.dist = r.dist := by
    rw [hsR, hdRDist]
  have hsRLast :
      s.right.last = r.last := by
    rw [hsR, hdRLast]

  have hr1Leader :
      r1.leader = r.leader := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hsRLeader]
    · simp [r1, hm, hsRLeader]
  have hr1Dist :
      r1.dist = r.dist := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, htmp]
    · simp [r1, hm, hsRDist]
  have hr1Last :
      r1.last = r.last := by
    by_cases hm : s.right.mode = false
    · simp [r1, hm, hsRLast]
    · simp [r1, hm, hsRLast]

  have hformula :
      (if r1.leader = true then
          true
        else if
            (Or (r1.dist.val = 0) (r1.dist.val = psi)) then
          false
        else
          r1.last) =
        l.last := by
    have hcanon :=
      splField_canonicalLine9Value
        hn3 hpsi ring root C e hC
    simpa [l, r, j,
      hr1Leader, hr1Dist, hr1Last]
      using hcanon

  have hl1Last :
      l1.last = l.last := by
    rw [← hformula]
    by_cases h1 : r1.leader = true <;>
      by_cases h2 :
        (Or (r1.dist.val = 0) (r1.dist.val = psi)) <;>
      simp [l1, h1, h2]

  have hpdef :
      p = (l1, r1) := by
    rfl
  rw [hpdef]
  exact ⟨hl1Last, hr1Last⟩




theorem splAlgorithm5NoNewLeaderFrame
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    (And
      (l.leader = false -> q.1.leader = false)
      (And
        (r.leader = false -> q.2.leader = false)
        (And
          (q.1.dist = l.dist)
          (And
            (q.2.dist = r.dist)
            (And
              (q.1.last = l.last)
              (And
                (q.2.last = r.last)
                (And
                  (q.1.id = l.id)
                  (q.2.id = r.id)))))))) := by
  let q := PPL.eliminateLeaders l r
  change
    (And
      (l.leader = false -> q.1.leader = false)
      (And
        (r.leader = false -> q.2.leader = false)
        (And
          (q.1.dist = l.dist)
          (And
            (q.2.dist = r.dist)
            (And
              (q.1.last = l.last)
              (And
                (q.2.last = r.last)
                (And
                  (q.1.id = l.id)
                  (q.2.id = r.id))))))))

  have hviewL :=
    PPL.Elim.view4_eliminateLeaders_left
      l r
  have hviewR :=
    PPL.Elim.view4_eliminateLeaders_right
      l r
  have hotherL :=
    PPL.Elim.otherView_eliminateLeaders_left
      l r
  have hotherR :=
    PPL.Elim.otherView_eliminateLeaders_right
      l r

  have hleadL :
      q.1.leader = l.leader := by
    calc
      q.1.leader =
          (PPL.Elim.rowE
            (PPL.Elim.view4 l)
            (PPL.Elim.view4 r)).1.leader := by
        have h :=
          congrArg
            (fun z : PPL.Elim.Cell4 =>
              z.leader)
            hviewL
        simpa [q, PPL.Elim.view4] using h
      _ =
          (PPL.Elim.view4 l).leader :=
        PPL.Elim.rowE_left_leader
          (PPL.Elim.view4 l)
          (PPL.Elim.view4 r)
      _ = l.leader := rfl

  have hdistL :
      q.1.dist = l.dist := by
    have h :=
      congrArg
        (fun z : PPL.Elim.OtherFields
            psi kappa => z.dist)
        hotherL
    simpa [q, PPL.Elim.otherView] using h
  have hdistR :
      q.2.dist = r.dist := by
    have h :=
      congrArg
        (fun z : PPL.Elim.OtherFields
            psi kappa => z.dist)
        hotherR
    simpa [q, PPL.Elim.otherView] using h
  have hlastL :
      q.1.last = l.last := by
    have h :=
      congrArg
        (fun z : PPL.Elim.OtherFields
            psi kappa => z.last)
        hotherL
    simpa [q, PPL.Elim.otherView] using h
  have hlastR :
      q.2.last = r.last := by
    have h :=
      congrArg
        (fun z : PPL.Elim.OtherFields
            psi kappa => z.last)
        hotherR
    simpa [q, PPL.Elim.otherView] using h
  have hidL :
      q.1.id = l.id := by
    have h :=
      congrArg
        (fun z : PPL.Elim.OtherFields
            psi kappa => z.id)
        hotherL
    simpa [q, PPL.Elim.otherView] using h
  have hidR :
      q.2.id = r.id := by
    have h :=
      congrArg
        (fun z : PPL.Elim.OtherFields
            psi kappa => z.id)
        hotherR
    simpa [q, PPL.Elim.otherView] using h

  refine
    ⟨?_, ?_,
      hdistL, hdistR,
      hlastL, hlastR,
      hidL, hidR⟩
  · intro hl
    rw [hleadL, hl]
  · intro hr
    have hrow :
        (PPL.Elim.rowE
          (PPL.Elim.view4 l)
          (PPL.Elim.view4 r)).2.leader =
            false :=
      PPL.Elim.rowE_right_leader_false_of_false
        (PPL.Elim.view4 l)
        (PPL.Elim.view4 r)
        (by simpa [PPL.Elim.view4] using hr)
    have hproj :
        q.2.leader =
          (PPL.Elim.rowE
            (PPL.Elim.view4 l)
            (PPL.Elim.view4 r)).2.leader := by
      have h :=
        congrArg
          (fun z : PPL.Elim.Cell4 =>
            z.leader)
          hviewR
      simpa [q, PPL.Elim.view4] using h
    exact hproj.trans hrow




private theorem splField_moveToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    (And
      (q.1.dist = l.dist)
      (And
        (q.2.dist = r.dist)
        (And
          (q.1.last = l.last)
          (q.2.last = r.last)))) := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  rcases
      PPL.moveToken_responder_fields
        hpsi kind l r
    with hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken,
          PPL.eraseKindTokenId,
          PPL.birthFields]




theorem splAlgorithm23FieldFrameResidual_of_idRow
    (hAlg3 : SPLAlgorithm3IdempotentIdRow) :
    SPLAlgorithm23FieldFrameResidual := by
  unfold SPLAlgorithm23FieldFrameResidual
  intro n psi kappa
  intro hn3 hpsi ring root C e hC

  let j := ring.rightNeighbor e
  let l := C e
  let r := C j
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  let b :=
    PPL.moveToken hpsi .black p.1 p.2
  let w :=
    PPL.moveToken hpsi .white b.1 b.2
  let q :=
    PPL.eliminateLeaders w.1 w.2

  have hrow1 :=
    splAlgorithm2DistWriteIdempotent
      hn3 hpsi ring root C e hC
  change
    (And
      (¬ PPL.createLeaderLine6Guard hpsi l r)
      (And
        (p.1.leader = l.leader)
        (And
          (p.2.leader = r.leader)
          (And
            (p.1.dist = l.dist)
            (And
              (p.2.dist = r.dist)
              (And
                (p.1.id = l.id)
                (p.2.id = r.id)))))))
    at hrow1
  rcases hrow1 with
    ⟨hguard,
      hpLLeader, hpRLeader,
      hpLDist, hpRDist,
      hpLId, hpRId⟩

  have hrow2 :=
    splAlgorithm2LastWriteIdempotent
      hn3 hpsi ring root C e hC
  change
    (And (p.1.last = l.last) (p.2.last = r.last))
    at hrow2
  rcases hrow2 with
    ⟨hpLLast, hpRLast⟩

  have hrow4 :=
    hAlg3
      hn3 hpsi ring root C e hC
  change
    (And
      (p.1.leader = false -> w.1.leader = false)
      (And
        (p.2.leader = false -> w.2.leader = false)
        (And
          (w.1.id = p.1.id)
          (w.2.id = p.2.id))))
    at hrow4
  rcases hrow4 with
    ⟨hwLNoBirth, hwRNoBirth,
      hwLId, hwRId⟩

  have hbFrame :=
    splField_moveToken_dist_last
      hpsi PPL.TokenKind.black
      p.1 p.2
  have hwFrame :=
    splField_moveToken_dist_last
      hpsi PPL.TokenKind.white
      b.1 b.2
  dsimp only at hbFrame hwFrame
  rcases hbFrame with
    ⟨hbLDist, hbRDist,
      hbLLast, hbRLast⟩
  rcases hwFrame with
    ⟨hwLDist0, hwRDist0,
      hwLLast0, hwRLast0⟩

  have hwLDist :
      w.1.dist = l.dist :=
    hwLDist0.trans
      (hbLDist.trans hpLDist)
  have hwRDist :
      w.2.dist = r.dist :=
    hwRDist0.trans
      (hbRDist.trans hpRDist)
  have hwLLast :
      w.1.last = l.last :=
    hwLLast0.trans
      (hbLLast.trans hpLLast)
  have hwRLast :
      w.2.last = r.last :=
    hwRLast0.trans
      (hbRLast.trans hpRLast)
  have hwLId0 :
      w.1.id = l.id :=
    hwLId.trans hpLId
  have hwRId0 :
      w.2.id = r.id :=
    hwRId.trans hpRId

  have hrow3 :=
    splAlgorithm5NoNewLeaderFrame
      w.1 w.2
  change
    (And
      (w.1.leader = false -> q.1.leader = false)
      (And
        (w.2.leader = false -> q.2.leader = false)
        (And
          (q.1.dist = w.1.dist)
          (And
            (q.2.dist = w.2.dist)
            (And
              (q.1.last = w.1.last)
              (And
                (q.2.last = w.2.last)
                (And
                  (q.1.id = w.1.id)
                  (q.2.id = w.2.id))))))))
    at hrow3
  rcases hrow3 with
    ⟨hqLNoBirth, hqRNoBirth,
      hqLDist0, hqRDist0,
      hqLLast0, hqRLast0,
      hqLId0, hqRId0⟩

  have hpairLNoBirth :
      l.leader = false ->
        q.1.leader = false := by
    intro hl
    apply hqLNoBirth
    apply hwLNoBirth
    rw [hpLLeader]
    exact hl

  have hpairRNoBirth :
      r.leader = false ->
        q.2.leader = false := by
    intro hr
    apply hqRNoBirth
    apply hwRNoBirth
    rw [hpRLeader]
    exact hr

  have hpairLDist :
      q.1.dist = l.dist :=
    hqLDist0.trans hwLDist
  have hpairRDist :
      q.2.dist = r.dist :=
    hqRDist0.trans hwRDist
  have hpairLLast :
      q.1.last = l.last :=
    hqLLast0.trans hwLLast
  have hpairRLast :
      q.2.last = r.last :=
    hqRLast0.trans hwRLast
  have hpairLId :
      q.1.id = l.id :=
    hqLId0.trans hwLId0
  have hpairRId :
      q.2.id = r.id :=
    hqRId0.trans hwRId0

  have hcreate :
      PPL.createLeader hpsi l r = w := by
    rfl
  have hppl :
      PPL.ppl hpsi l r = q := by
    change
      PPL.eliminateLeaders
          (PPL.createLeader hpsi l r).1
          (PPL.createLeader hpsi l r).2 =
        q
    rw [hcreate]
    try rfl
  have htrans :
      PPL.transition psi kappa l r = q := by
    calc
      PPL.transition psi kappa l r =
          PPL.ppl hpsi l r :=
        PPL.transition_eq_ppl hpsi l r
      _ = q := hppl

  let C' : Config n psi kappa :=
    nextConfig ring C e
  have hne : Not (j = e) := by
    simpa [j] using
      splField_rightNeighbor_ne_self
        hn3 ring e

  have hstepL :
      C' e = q.1 := by
    dsimp [C', nextConfig]
    simp [PopulationProtocol.step,
      PPL.protocol, l, r, j, htrans]

  have hstepR :
      C' j = q.2 := by
    dsimp [C', nextConfig]
    simp [PopulationProtocol.step,
      PPL.protocol, l, r, j,
      hne, htrans]

  have hstepOther :
      forall i : Fin n,
        Not (i = e) ->
        Not (i = j) ->
        C' i = C i := by
    intro i hie hij
    dsimp [C', nextConfig]
    simp [PopulationProtocol.step,
      PPL.protocol, hie, hij, j]
    try rfl

  have hleader :
      forall i : Fin n,
        (C i).leader = false ->
          (C' i).leader = false := by
    intro i hi
    by_cases hie : i = e
    · subst i
      rw [hstepL]
      exact hpairLNoBirth hi
    · by_cases hij : i = j
      · subst i
        rw [hstepR]
        exact hpairRNoBirth hi
      · rw [hstepOther i hie hij]
        exact hi

  have hdist :
      forall i : Fin n,
        (C' i).dist = (C i).dist := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hstepL]
      exact hpairLDist
    · by_cases hij : i = j
      · subst i
        rw [hstepR]
        exact hpairRDist
      · exact
          congrArg
            (fun z : PPL.State psi kappa =>
              z.dist)
            (hstepOther i hie hij)

  have hlast :
      forall i : Fin n,
        (C' i).last = (C i).last := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hstepL]
      exact hpairLLast
    · by_cases hij : i = j
      · subst i
        rw [hstepR]
        exact hpairRLast
      · exact
          congrArg
            (fun z : PPL.State psi kappa =>
              z.last)
            (hstepOther i hie hij)

  have hid :
      forall i : Fin n,
        (C' i).id = (C i).id := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hstepL]
      exact hpairLId
    · by_cases hij : i = j
      · subst i
        rw [hstepR]
        exact hpairRId
      · exact
          congrArg
            (fun z : PPL.State psi kappa =>
              z.id)
            (hstepOther i hie hij)

  dsimp only
  exact
    ⟨hleader,
      hdist,
      hlast,
      hid⟩


theorem splAlgorithm23FieldFrameResidual_proved :
    SPLAlgorithm23FieldFrameResidual :=
  splAlgorithm23FieldFrameResidual_of_idRow
    splAlgorithm3IdempotentIdRow_proved

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splAlgorithm2DistWriteIdempotent
#print axioms PPL.Safety.SPL.splAlgorithm2LastWriteIdempotent
#print axioms PPL.Safety.SPL.splAlgorithm5NoNewLeaderFrame
#print axioms PPL.Safety.SPL.splAlgorithm3IdempotentIdRow_proved
#print axioms PPL.Safety.SPL.splAlgorithm23FieldFrameResidual_of_idRow
#print axioms PPL.Safety.SPL.splAlgorithm23FieldFrameResidual_proved
