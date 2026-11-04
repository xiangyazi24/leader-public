import Leader.PPL.ReachCPB.MismatchHistFreshBranchRowGeom
import Leader.PPL.ReachCPB.MismatchHistFreshCoherent
import Leader.Core.ModArith
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
Part 1 proves the distance fact requested in the question.

Part 2 records the exact DistReady replacement of
Lemma16PostEpochFreshNewCompletionStepGeomCoherent and refutes it on an
n = 4, psi = 2 state-local witness.

The defect is independent of the border gap.  The witness has the
literal cyclic distance pattern 0,1,2,3, hence both adjacent borders from
b = 2 are exactly two edges away.

The remaining arbitrary-G hole is completion-ID history.  G.completed may
already contain a metadata record with the same LineageId as the live owner
but different metadata.  This makes Lemma16NoPriorCompletionId false, so the
live payload/prefix clause of Lemma16PostEpochFreshStateInvariant imposes no
condition on that owner.  Yet the terminal row asks only that the newly logged
terminal metadata itself is not a member of G.completed.
-/

/-! -------------------------------------------------------------------------
    1. Distance-cycle geometry
------------------------------------------------------------------------- -/

@[simp] private theorem q20039_shiftRight_zero
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]

private theorem q20039_shiftRight_add
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (a d : Nat) :
    PPL.shiftRight ring
        (PPL.shiftRight ring i a) d =
      PPL.shiftRight ring i (a + d) := by
  apply Fin.ext
  change
    (((i.val + a) % n + d) % n) =
      (i.val + (a + d)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

@[simp] private theorem q20039_shiftRight_n
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i n = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]

private theorem q20039_shiftRight_one
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i 1 = ring.rightNeighbor i := by
  rfl

private theorem q20039_shiftRight_succ
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) :
    PPL.shiftRight ring i (d + 1) =
      ring.rightNeighbor (PPL.shiftRight ring i d) := by
  calc
    PPL.shiftRight ring i (d + 1) =
        PPL.shiftRight ring
          (PPL.shiftRight ring i d) 1 :=
      (q20039_shiftRight_add ring i d 1).symm
    _ = ring.rightNeighbor
          (PPL.shiftRight ring i d) :=
      q20039_shiftRight_one ring
        (PPL.shiftRight ring i d)

private theorem q20039_shiftLeft_eq_shiftRight_sub
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) :
    PPL.shiftLeft ring i d =
      PPL.shiftRight ring i (n - d) := by
  apply Fin.ext
  simp only [PPL.shiftLeft, PPL.shiftRight]
  rw [Nat.mod_eq_of_lt hd]
  have hs :
      i.val + n - d =
        i.val + (n - d) := by
    omega
  rw [hs]

private theorem q20039_scanDistance_eq_some_first
    {n : Nat}
    (site : Nat → Fin n)
    (hit : Fin n → Bool)
    (fuel lo target : Nat)
    (hlo : lo ≤ target)
    (hin : target < lo + fuel)
    (hbefore :
      ∀ d : Nat,
        lo ≤ d →
        d < target →
        hit (site d) = false)
    (hhit : hit (site target) = true) :
    PPL.scanDistance site hit fuel lo =
      some target := by
  induction fuel generalizing lo with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases heq : lo = target
      · subst lo
        change
          (if hit (site target) = true then
              some target
            else
              PPL.scanDistance
                site hit fuel (target + 1)) =
            some target
        simp [hhit]
      · have hlt : lo < target := by
          omega
        have hfalse :=
          hbefore lo (Nat.le_refl lo) hlt
        change
          (if hit (site lo) = true then
              some lo
            else
              PPL.scanDistance
                site hit fuel (lo + 1)) =
            some target
        simp only
          [hfalse, Bool.false_eq_true, if_false]
        apply ih (lo := lo + 1)
        · omega
        · omega
        · intro d hd hdt
          exact hbefore d (by omega) hdt

private theorem q20039_isBorderBool_true_iff
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (i : Fin n) :
    PPL.isBorderBool C i = true ↔
      PPL.IsBorder C i := by
  simp [PPL.isBorderBool, PPL.IsBorder]

private theorem q20039_isBorderBool_false_of_not
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (i : Fin n)
    (h : ¬ PPL.IsBorder C i) :
    PPL.isBorderBool C i = false := by
  cases hB : PPL.isBorderBool C i with
  | false =>
      rfl
  | true =>
      exfalso
      exact
        h
          ((q20039_isBorderBool_true_iff
            C i).mp hB)

private theorem q20039_mod_twoPsi_border_iff_dvd
    (psi k : Nat)
    (hpsi : 0 < psi) :
    k % (2 * psi) = 0 ∨
      k % (2 * psi) = psi ↔
        psi ∣ k := by
  have hbase :
      psi ∣ 2 * psi :=
    Nat.dvd_mul_left psi 2
  constructor
  · intro h
    have hrem :
        (k % (2 * psi)) % psi = 0 := by
      rcases h with h0 | hp
      · rw [h0]
        simp
      · rw [hp]
        simp
    have hkmod : k % psi = 0 := by
      calc
        k % psi =
            (k % (2 * psi)) % psi :=
          (Nat.mod_mod_of_dvd k hbase).symm
        _ = 0 := hrem
    exact Nat.dvd_of_mod_eq_zero hkmod
  · intro hk
    have hrem :
        (k % (2 * psi)) % psi = 0 := by
      calc
        (k % (2 * psi)) % psi =
            k % psi :=
          Nat.mod_mod_of_dvd k hbase
        _ = 0 :=
          Nat.mod_eq_zero_of_dvd hk
    have hrlt :
        k % (2 * psi) < 2 * psi :=
      Nat.mod_lt _ (by omega)
    by_cases hlt :
        k % (2 * psi) < psi
    · left
      rw [Nat.mod_eq_of_lt hlt] at hrem
      exact hrem
    · right
      have hge :
          psi ≤ k % (2 * psi) := by
        omega
      have hsub :
          k % (2 * psi) - psi < psi := by
        omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt hsub] at hrem
      omega

private theorem q20039_not_dvd_of_pos_lt
    (psi d : Nat)
    (hd0 : 0 < d)
    (hdlt : d < psi) :
    ¬ psi ∣ d := by
  intro hd
  have hle := Nat.le_of_dvd hd0 hd
  omega

private theorem q20039_not_dvd_mul_add_small
    (psi j d : Nat)
    (hd0 : 0 < d)
    (hdlt : d < psi) :
    ¬ psi ∣ j * psi + d := by
  have hj :
      psi ∣ j * psi :=
    Nat.dvd_mul_left psi j
  intro hsum
  have hd : psi ∣ d :=
    (Nat.dvd_add_iff_right hj).mpr hsum
  exact
    q20039_not_dvd_of_pos_lt
      psi d hd0 hdlt hd

private theorem q20039_dvd_mul_add_sub_iff
    {n psi : Nat}
    (hnpsi : psi ∣ n)
    (j d : Nat)
    (hdn : d ≤ n) :
    psi ∣ j * psi + (n - d) ↔
      psi ∣ d := by
  have hj :
      psi ∣ j * psi :=
    Nat.dvd_mul_left psi j
  have hsum :
      psi ∣ j * psi + n :=
    Nat.dvd_add hj hnpsi
  have heq :
      j * psi + (n - d) =
        (j * psi + n) - d := by
    omega
  rw [heq]
  exact
    Nat.dvd_sub_iff_right
      (by omega) hsum

private theorem q20039_dist_shiftRight
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hdist :
      ∀ i : Fin n,
        (C (ring.rightNeighbor i)).dist.val =
          ((C i).dist.val + 1) %
            (2 * psi))
    (k : Fin n) :
    ∀ d : Nat,
      (C (PPL.shiftRight ring k d)).dist.val =
        ((C k).dist.val + d) %
          (2 * psi) := by
  intro d
  induction d with
  | zero =>
      rw [q20039_shiftRight_zero]
      simpa using
        (Nat.mod_eq_of_lt
          (C k).dist.isLt).symm
  | succ d ih =>
      rw [q20039_shiftRight_succ]
      calc
        (C
            (ring.rightNeighbor
              (PPL.shiftRight ring k d))).dist.val =
            ((C
                (PPL.shiftRight
                  ring k d)).dist.val + 1) %
              (2 * psi) :=
          hdist
            (PPL.shiftRight ring k d)
        _ =
            ((((C k).dist.val + d) %
                (2 * psi)) + 1) %
              (2 * psi) := by
          rw [ih]
        _ =
            ((C k).dist.val + d + 1) %
              (2 * psi) := by
          rw [Nat.mod_add_mod]
        _ =
            ((C k).dist.val + (d + 1)) %
              (2 * psi) := by
          congr 1

private theorem q20039_twoPsi_dvd_n
    {n psi kappa : Nat}
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hdist :
      ∀ i : Fin n,
        (C (ring.rightNeighbor i)).dist.val =
          ((C i).dist.val + 1) %
            (2 * psi))
    (k : Fin n) :
    2 * psi ∣ n := by
  have hcycle :=
    q20039_dist_shiftRight
      ring C hdist k n
  rw [q20039_shiftRight_n] at hcycle
  exact
    dvd_of_lt_mod_add_eq
      (C k).dist.val n (2 * psi)
      (by omega)
      (C k).dist.isLt
      hcycle

private theorem q20039_border_geometry
    {n psi kappa : Nat}
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (hdist :
      ∀ d : Nat,
        (C
          (PPL.shiftRight
            ring start d)).dist.val =
          ((C start).dist.val + d) %
            (2 * psi))
    (hb : PPL.IsBorder C start) :
    ∀ d : Nat,
      PPL.IsBorder C
          (PPL.shiftRight
            ring start d) ↔
        psi ∣ d := by
  unfold PPL.IsBorder at hb
  intro d
  unfold PPL.IsBorder
  rw [hdist d]
  rcases hb with h0 | hp
  · rw [h0]
    simpa using
      q20039_mod_twoPsi_border_iff_dvd
        psi d hpsi
  · rw [hp]
    have hmod :=
      q20039_mod_twoPsi_border_iff_dvd
        psi (psi + d) hpsi
    rw [hmod]
    have hself : psi ∣ psi :=
      Nat.dvd_refl psi
    exact
      (Nat.dvd_add_iff_right hself).symm

private theorem q20039_nextBorderDistance_eq_psi
    {n psi kappa : Nat}
    (hpsi : 0 < psi)
    (hpsin : psi < n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (hgeom :
      ∀ d : Nat,
        PPL.IsBorder C
            (PPL.shiftRight
              ring start d) ↔
          psi ∣ d)
    (j : Nat) :
    PPL.nextBorderDistance ring C
        (PPL.shiftRight
          ring start (j * psi)) =
      psi := by
  let b :=
    PPL.shiftRight
      ring start (j * psi)
  have hscan :
      PPL.scanDistance
          (fun d =>
            PPL.shiftRight ring b d)
          (PPL.isBorderBool C)
          n 1 =
        some psi := by
    apply q20039_scanDistance_eq_some_first
    · omega
    · omega
    · intro d hd1 hdpsi
      have hnot :
          ¬ psi ∣ j * psi + d :=
        q20039_not_dvd_mul_add_small
          psi j d (by omega) hdpsi
      have hsite :
          PPL.shiftRight ring b d =
            PPL.shiftRight ring start
              (j * psi + d) := by
        dsimp [b]
        exact
          q20039_shiftRight_add
            ring start (j * psi) d
      have hnb :
          ¬ PPL.IsBorder C
              (PPL.shiftRight ring b d) := by
        intro hb
        rw [hsite] at hb
        exact
          hnot
            ((hgeom
              (j * psi + d)).mp hb)
      exact
        q20039_isBorderBool_false_of_not
          C _ hnb
    · have hsite :
          PPL.shiftRight ring b psi =
            PPL.shiftRight ring start
              (j * psi + psi) := by
        dsimp [b]
        exact
          q20039_shiftRight_add
            ring start (j * psi) psi
      apply
        (q20039_isBorderBool_true_iff
          C _).mpr
      rw [hsite]
      apply
        (hgeom
          (j * psi + psi)).mpr
      have hj :
          psi ∣ j * psi :=
        Nat.dvd_mul_left psi j
      exact
        (Nat.dvd_add_iff_right hj).mp
          (Nat.dvd_refl psi)
  unfold PPL.nextBorderDistance
  rw [hscan]

private theorem q20039_prevBorderDistance_eq_psi
    {n psi kappa : Nat}
    (hpsi : 0 < psi)
    (hpsin : psi < n)
    (hnpsi : psi ∣ n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (hgeom :
      ∀ d : Nat,
        PPL.IsBorder C
            (PPL.shiftRight
              ring start d) ↔
          psi ∣ d)
    (j : Nat) :
    PPL.prevBorderDistance ring C
        (PPL.shiftRight
          ring start (j * psi)) =
      psi := by
  let b :=
    PPL.shiftRight
      ring start (j * psi)
  have hscan :
      PPL.scanDistance
          (fun d =>
            PPL.shiftLeft ring b d)
          (PPL.isBorderBool C)
          n 1 =
        some psi := by
    apply q20039_scanDistance_eq_some_first
    · omega
    · omega
    · intro d hd1 hdpsi
      have hdN : d < n := by
        omega
      have hsite :
          PPL.shiftLeft ring b d =
            PPL.shiftRight ring start
              (j * psi + (n - d)) := by
        calc
          PPL.shiftLeft ring b d =
              PPL.shiftRight ring b
                (n - d) :=
            q20039_shiftLeft_eq_shiftRight_sub
              ring b d hdN
          _ =
              PPL.shiftRight ring start
                (j * psi + (n - d)) := by
            dsimp [b]
            exact
              q20039_shiftRight_add
                ring start
                (j * psi) (n - d)
      have hnotD :
          ¬ psi ∣ d :=
        q20039_not_dvd_of_pos_lt
          psi d (by omega) hdpsi
      have hiff :=
        q20039_dvd_mul_add_sub_iff
          hnpsi j d (by omega : d ≤ n)
      have hnot :
          ¬ psi ∣
              j * psi + (n - d) := by
        intro h
        exact hnotD (hiff.mp h)
      have hnb :
          ¬ PPL.IsBorder C
              (PPL.shiftLeft ring b d) := by
        intro hb
        rw [hsite] at hb
        exact
          hnot
            ((hgeom
              (j * psi +
                (n - d))).mp hb)
      exact
        q20039_isBorderBool_false_of_not
          C _ hnb
    · have hsite :
          PPL.shiftLeft ring b psi =
            PPL.shiftRight ring start
              (j * psi + (n - psi)) := by
        calc
          PPL.shiftLeft ring b psi =
              PPL.shiftRight ring b
                (n - psi) :=
            q20039_shiftLeft_eq_shiftRight_sub
              ring b psi hpsin
          _ =
              PPL.shiftRight ring start
                (j * psi +
                  (n - psi)) := by
            dsimp [b]
            exact
              q20039_shiftRight_add
                ring start
                (j * psi) (n - psi)
      apply
        (q20039_isBorderBool_true_iff
          C _).mpr
      rw [hsite]
      apply
        (hgeom
          (j * psi +
            (n - psi))).mpr
      exact
        (q20039_dvd_mul_add_sub_iff
          hnpsi j psi
          (by omega : psi ≤ n)).mpr
            (Nat.dvd_refl psi)
  unfold PPL.prevBorderDistance
  rw [hscan]

/--
Under the capped global successor-distance equation, every 0/psi border has
both adjacent borders exactly psi edges away.

The same global cycle also forces 2*psi | n, so the recursive scanner has
enough fuel to encounter the adjacent border before wrapping.
-/
theorem lemma16DistReady_nextBorderDistance_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b : Fin n)
    (hready : DistReadyCapped ring C)
    (hb : PPL.IsBorder C b) :
    PPL.nextBorderDistance ring C b = psi ∧
      PPL.prevBorderDistance ring C b = psi := by
  have hdist := hready.2
  have hdiv :
      2 * psi ∣ n :=
    q20039_twoPsi_dvd_n
      (by omega)
      ring C hdist b
  have htwo :
      2 * psi ≤ n :=
    Nat.le_of_dvd ring.hn hdiv
  have hpsin : psi < n := by
    omega
  have hnpsi : psi ∣ n :=
    Nat.dvd_trans
      (Nat.dvd_mul_left psi 2)
      hdiv
  have hformula :=
    q20039_dist_shiftRight
      ring C hdist b
  have hgeom :=
    q20039_border_geometry
      (by omega)
      ring C b hformula hb
  constructor
  · have hnxt :=
      q20039_nextBorderDistance_eq_psi
        (by omega) hpsin
        ring C b hgeom 0
    simpa using hnxt
  · have hprv :=
      q20039_prevBorderDistance_eq_psi
        (by omega) hpsin hnpsi
        ring C b hgeom 0
    simpa using hprv

/-! -------------------------------------------------------------------------
    2. Exact DistReady replacement
------------------------------------------------------------------------- -/

/--
Exactly Lemma16PostEpochFreshNewCompletionStepGeomCoherent, with the physical
readiness premise strengthened from DetectReadyCapped to DistReadyCapped.
-/
def Lemma16PostEpochFreshNewCompletionStepGeomDist : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16GhostLineageCoherent G →
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi →
    DistReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G →
    let G' :=
      PPL.ghostStep hpsi ring step G e
    PPL.CPB ring G'.phys ∨
      ∀ m : PPL.LineageMeta n,
        m ∈ G'.completed →
        PPL.FreshCompletion
          (psi := psi) kind k m →
        m ∉ G.completed →
        (∀ (i : Fin n)
          (z : PPL.GhostToken n psi)
          (t : Nat),
          PPL.ghostTokenAt kind G i =
            some z →
          z.lmeta.id = .born kind t →
          z.lmeta.birthSite = k →
          epoch ≤ z.lmeta.birthStep) →
        Lemma16BadBorderWitness
          ring G.phys b k kind →
        False

/-! -------------------------------------------------------------------------
    3. Executable distance audit
------------------------------------------------------------------------- -/

private def q20039Q19985Ring :
    DirectedRing 6 :=
  ⟨by decide⟩

private def q20039Q19985DistVal
    (i : Fin 6) : Nat :=
  if i.val = 0 then 0
  else if i.val = 1 then 1
  else if i.val = 2 then 2
  else if i.val = 3 then 3
  else if i.val = 4 then 1
  else 0

/-- Bool mirror of the sole extra DistReady equation on the distance
row.  It is false (already at the physical edge 3 -> 4). -/
private def q20039Q19985DistanceEquationBool : Bool :=
  decide
    (∀ i : Fin 6,
      q20039Q19985DistVal
          (q20039Q19985Ring.rightNeighbor i) =
        (q20039Q19985DistVal i + 1) % 4)

private theorem q20039Q19985DistanceEquationBool_false :
    q20039Q19985DistanceEquationBool = false := by
  decide

/-! -------------------------------------------------------------------------
    4. n = 4, psi = 2 DistReady counterexample
------------------------------------------------------------------------- -/

private theorem q20039Hpsi : 2 ≤ 2 := by
  omega

private theorem q20039Hn3 : 3 ≤ 4 := by
  omega

private def q20039Ring :
    DirectedRing 4 :=
  ⟨by decide⟩

private def q20039E0 : Fin 4 :=
  ⟨0, by decide⟩
private def q20039E1 : Fin 4 :=
  ⟨1, by decide⟩
private def q20039E2 : Fin 4 :=
  ⟨2, by decide⟩
private def q20039E3 : Fin 4 :=
  ⟨3, by decide⟩

private def q20039Token :
    PPL.TokenData 2 :=
  ((PPL.offsetOneCode
      2 q20039Hpsi,
      (0 : Fin 2)),
    (0 : Fin 2))

private def q20039State
    (i : Fin 4) :
    PPL.State 2 1 :=
  {
    leader := false
    id :=
      if i = q20039E1 ∨
          i = q20039E2 then
        true
      else
        false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB :=
      if i = q20039E2 then
        some q20039Token
      else
        none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }

private def q20039C :
    Config 4 2 1 :=
  q20039State

private def q20039Z :
    PPL.GhostToken 4 2 :=
  {
    value := q20039Token
    lmeta :=
      {
        id := .born .black 0
        birthSite := q20039E0
        birthStep := 0
        moves := 4
      }
  }

/--
An already-completed metadata record with the same lineage ID but a different
birthSite.  This is enough to make Lemma16NoPriorCompletionId false while
remaining different from the exact terminal metadata q20039M.
-/
private def q20039Old :
    PPL.LineageMeta 4 :=
  {
    id := .born .black 0
    birthSite := q20039E1
    birthStep := 0
    moves := 0
  }

private def q20039M :
    PPL.LineageMeta 4 :=
  {
    id := .born .black 0
    birthSite := q20039E0
    birthStep := 0
    moves := 5
  }

private def q20039G :
    PPL.GhostConfig 4 2 1 :=
  {
    phys := q20039C
    black :=
      fun i =>
        if i = q20039E2 then
          some q20039Z
        else
          none
    white := fun _ => none
    completed := [q20039Old]
  }

private theorem q20039_owner_shape
    {i : Fin 4}
    {z : PPL.GhostToken 4 2}
    (h :
      PPL.ghostTokenAt .black
        q20039G i = some z) :
    i = q20039E2 ∧
      z = q20039Z := by
  by_cases hi : i = q20039E2
  · subst i
    have hz : q20039Z = z := by
      simpa
        [q20039G,
          PPL.ghostTokenAt]
        using h
    exact ⟨rfl, hz.symm⟩
  · have hf : False := by
      simpa
        [q20039G,
          PPL.ghostTokenAt, hi]
        using h
    exact False.elim hf

/-- Coherence is now genuine: the live black slot, LineageId color/timestamp,
and birthStep all agree. -/
private theorem q20039_coherent :
    Lemma16GhostLineageCoherent
      q20039G := by
  unfold Lemma16GhostLineageCoherent
  intro slotKind bornKind i z t
  intro howner hid
  cases slotKind with
  | black =>
      rcases
          q20039_owner_shape howner with
        ⟨hi, hz⟩
      subst i
      subst z
      cases bornKind with
      | black =>
          change
            PPL.LineageId.born
                .black 0 =
              PPL.LineageId.born
                .black t
            at hid
          cases hid
          exact ⟨rfl, rfl⟩
      | white =>
          change
            PPL.LineageId.born
                .black 0 =
              PPL.LineageId.born
                .white t
            at hid
          cases hid
  | white =>
      have hf : False := by
        simpa
          [q20039G,
            PPL.ghostTokenAt]
          using howner
      exact False.elim hf

private theorem q20039_geometry :
    Lemma16PostEpochFreshBorderGeometry
      q20039Ring
      q20039E2 q20039E0 2 := by
  unfold
    Lemma16PostEpochFreshBorderGeometry
  decide

private theorem q20039_ready :
    DetectReadyCapped
      q20039Ring q20039G.phys := by
  unfold DetectReadyCapped DetectReady
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact
      @of_decide_eq_true _
        (instDecidableAllLivePeaceful _ _)
        rfl
  all_goals decide

/-- Executable Bool mirror of the global successor-distance equation. -/
private def q20039DistanceEquationBool : Bool :=
  decide
    (∀ i : Fin 4,
      (q20039G.phys
          (q20039Ring.rightNeighbor i)).dist.val =
        ((q20039G.phys i).dist.val + 1) %
          4)

private theorem q20039DistanceEquationBool_true :
    q20039DistanceEquationBool = true := by
  decide

private theorem q20039_distanceEquation :
    ∀ i : Fin 4,
      (q20039G.phys
          (q20039Ring.rightNeighbor i)).dist.val =
        ((q20039G.phys i).dist.val + 1) %
          (2 * 2) := by
  have h :
      ∀ i : Fin 4,
        (q20039G.phys
            (q20039Ring.rightNeighbor i)).dist.val =
          ((q20039G.phys i).dist.val + 1) %
            4 := by
    apply of_decide_eq_true
    exact
      q20039DistanceEquationBool_true
  simpa using h

private theorem q20039_distReady :
    DistReadyCapped
      q20039Ring q20039G.phys := by
  unfold DistReadyCapped
  exact
    ⟨q20039_ready,
      q20039_distanceEquation⟩

private theorem q20039_border :
    PPL.IsBorder q20039G.phys
      q20039E2 := by
  unfold PPL.IsBorder
  decide

/-- This invokes the public theorem from part 1 on the actual counterexample,
so both scanners are certified to return exactly psi = 2. -/
private theorem q20039_borderDistances :
    PPL.nextBorderDistance
        q20039Ring q20039G.phys
        q20039E2 = 2 ∧
      PPL.prevBorderDistance
        q20039Ring q20039G.phys
        q20039E2 = 2 :=
  lemma16DistReady_nextBorderDistance_eq
    q20039Hpsi
    q20039Ring q20039G.phys
    q20039E2
    q20039_distReady
    q20039_border

/-- The bad segment equation holds on this finite witness. -/
private theorem q20039_bad :
    Lemma16BadBorderWitness
      q20039Ring q20039G.phys
      q20039E2 q20039E0 .black := by
  unfold Lemma16BadBorderWitness PPL.IsBorder PPL.Cd
  dsimp only
  decide

/--
The frozen-ID half is literal.  The live half is vacuous for the unique live
owner because q20039Old, already in completed, has the same LineageId.
-/
private theorem q20039_stateInvariant :
    Lemma16PostEpochFreshStateInvariant
      q20039Ring q20039C 0
      q20039E2 q20039E0
      .black q20039G := by
  unfold
    Lemma16PostEpochFreshStateInvariant
  refine ⟨(fun _ => rfl), ?_⟩
  unfold
    Lemma16PostEpochFreshLiveInvariant
  intro i z t howner
  intro _hid _hsite _hepoch hprior
  rcases q20039_owner_shape howner with
    ⟨hi, hz⟩
  subst i
  subst z
  unfold
    Lemma16NoPriorCompletionId
    at hprior
  have hold :
      q20039Old ∈ q20039G.completed := by
    simp [q20039G]
  have hne :=
    hprior q20039Old hold
  have heq :
      q20039Old.id =
        q20039Z.lmeta.id := by
    rfl
  exact False.elim (hne heq)

private theorem q20039_history :
    ∀ (i : Fin 4)
      (z : PPL.GhostToken 4 2)
      (t : Nat),
      PPL.ghostTokenAt .black
          q20039G i =
        some z →
      z.lmeta.id = .born .black t →
      z.lmeta.birthSite = q20039E0 →
      0 ≤ z.lmeta.birthStep := by
  intro _i z _t _howner _hid _hsite
  exact Nat.zero_le z.lmeta.birthStep

private theorem q20039_fresh :
    PPL.FreshCompletion
      (psi := 2) .black
      q20039E0 q20039M := by
  unfold
    PPL.FreshCompletion PPL.FreshAt
  refine ⟨?_, ?_⟩
  · exact ⟨0, rfl, rfl⟩
  · decide

private theorem q20039_not_old :
    q20039M ∉ q20039G.completed := by
  change q20039M ∉ [q20039Old]
  decide

private theorem q20039_post_completed :
    (PPL.ghostStep
      q20039Hpsi q20039Ring
      2 q20039G q20039E2).completed =
        [q20039Old, q20039M] := by
  decide

private theorem q20039_new_member :
    q20039M ∈
      (PPL.ghostStep
        q20039Hpsi q20039Ring
        2 q20039G q20039E2).completed := by
  rw [q20039_post_completed]
  simp

/-- Executable mirror of the physical non-success branch. -/
private def q20039PostLeaderlessBool : Bool :=
  decide
    (∀ i : Fin 4,
      ((PPL.ghostStep
        q20039Hpsi q20039Ring
        2 q20039G q20039E2).phys i).leader =
          false)

private theorem q20039PostLeaderlessBool_true :
    q20039PostLeaderlessBool = true := by
  decide

private theorem q20039_post_leaderless :
    ∀ i : Fin 4,
      ((PPL.ghostStep
        q20039Hpsi q20039Ring
        2 q20039G q20039E2).phys i).leader =
          false := by
  apply of_decide_eq_true
  exact q20039PostLeaderlessBool_true

private theorem q20039_post_not_cpb :
    ¬ PPL.CPB q20039Ring
        (PPL.ghostStep
          q20039Hpsi q20039Ring
          2 q20039G q20039E2).phys := by
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨i, hi⟩
  dsimp only at hi
  rw [q20039_post_leaderless i] at hi
  contradiction

/--
Counterexample to the requested DistReady terminal row.

The spacing problem is absent:
  dist = 0,1,2,3 cyclically,
  nextBorderDistance b = 2,
  prevBorderDistance b = 2.

The failure is instead the missing once-only/same-LineageId completion-history
condition described above.
-/
theorem
    lemma16PostEpochFreshNewCompletionStepGeomDist_refuted :
    ¬ Lemma16PostEpochFreshNewCompletionStepGeomDist := by
  intro hrow
  unfold
    Lemma16PostEpochFreshNewCompletionStepGeomDist
    at hrow
  have hs :=
    hrow
      (n := 4) (psi := 2) (kappa := 1)
      q20039Hpsi q20039Hn3
      q20039Ring
      q20039C
      0
      q20039E2 q20039E0
      .black
      2
      q20039G
      q20039E2
      q20039_coherent
      q20039_geometry
      q20039_distReady
      q20039_stateInvariant
  dsimp only at hs
  rcases hs with hcpb | hterminal
  · exact q20039_post_not_cpb hcpb
  · exact
      hterminal
        q20039M
        q20039_new_member
        q20039_fresh
        q20039_not_old
        q20039_history
        q20039_bad

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16DistReady_nextBorderDistance_eq
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeomDist_refuted
