import Leader.PPL.Convergence.BulletLineageSweepSteps


namespace PPL.Convergence.BulletLineage


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL.Convergence.BulletSweep
open PPL.Safety.PeacefulProps


private def BadLive4Reach
    {n : Nat}
    (ring : DirectedRing n)
    (D : Fin n -> Cell4)
    (i : Fin n) : Prop :=
  (D i).bullet = (2 : Fin 3) ∧
    Not (Peaceful4 ring D i)


private def CellCleared (q : Cell4) : Prop :=
  q.leader = false ∧ q.signalB = false


/--
Reachable ghosts remember a literal cleared clockwise arc.


For a still-bad owner o, every positive site already crossed by the lineage
is a follower with signalB=false.  the earlier forged counter-ghost violates
exactly this relation: its owner has origin=0 and swept=2, but the d=2 site
still has signalB=true.
-/
def BadSweepClearedArcInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa) : Prop :=
  forall (i : Fin n) (o : BulletOwner n),
    g.owner i = some o ->
    BadLive ring g.physical i ->
      And
        (i = PPL.shiftRight ring o.tag.origin o.swept)
        (forall d : Nat,
          1 <= d ->
          d <= o.swept ->
          d <= n ->
            let q := PPL.shiftRight ring o.tag.origin d
            CellCleared (project4 g.physical q))


private theorem q19751_rightNeighbor_ne_self
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      have he := e.isLt
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem q19751_shiftRight_zero
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]


private theorem q19751_shiftRight_n
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i n = i := by
  apply Fin.ext
  change (i.val + n) % n = i.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]


private theorem q19751_shiftRight_add
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring i a) b =
      PPL.shiftRight ring i (a + b) := by
  apply Fin.ext
  change (((i.val + a) % n + b) % n) =
    (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem q19751_shiftRight_succ
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) :
    PPL.shiftRight ring i (d + 1) =
      ring.rightNeighbor (PPL.shiftRight ring i d) := by
  calc
    PPL.shiftRight ring i (d + 1) =
        PPL.shiftRight ring (PPL.shiftRight ring i d) 1 :=
      (q19751_shiftRight_add ring i d 1).symm
    _ = ring.rightNeighbor (PPL.shiftRight ring i d) := rfl


private theorem q19751_shiftLeft_one
    {n : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftLeft ring i 1 = ring.leftNeighbor i := by
  apply Fin.ext
  simp only [PPL.shiftLeft, DirectedRing.leftNeighbor]
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]


private theorem q19751_leftNeighbor_rightNeighbor
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem q19751_cyclicOffset_shiftRight_of_lt
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring i (PPL.shiftRight ring i d) = d := by
  unfold PPL.cyclicOffset PPL.shiftRight
  change (((i.val + d) % n + n - i.val) % n) = d
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq : i.val + d + n - i.val = n + d := by
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have heq : i.val + d - n + n - i.val = d := by
      omega
    rw [heq, Nat.mod_eq_of_lt hd]


private theorem q19751_shiftRight_cyclicOffset
    {n : Nat} (ring : DirectedRing n)
    (a b : Fin n) :
    PPL.shiftRight ring a (PPL.cyclicOffset ring a b) = b := by
  apply Fin.ext
  change
    (a.val + ((b.val + n - a.val) % n)) % n = b.val
  by_cases hab : a.val <= b.val
  · have heq :
        b.val + n - a.val = n + (b.val - a.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : b.val - a.val < n)]
    have hsum : a.val + (b.val - a.val) = b.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt b.isLt]
  · have hlt : b.val + n - a.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        a.val + (b.val + n - a.val) = b.val + n := by
      omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]


private theorem q19751_shiftLeft_shiftRight_sub
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d k : Nat)
    (hk : k <= d) (hd : d < n) :
    PPL.shiftLeft ring (PPL.shiftRight ring i d) k =
      PPL.shiftRight ring i (d - k) := by
  apply Fin.ext
  unfold PPL.shiftLeft PPL.shiftRight
  change
    (((i.val + d) % n + n - k % n) % n) =
      (i.val + (d - k)) % n
  have hklt : k < n := Nat.lt_of_le_of_lt hk hd
  rw [Nat.mod_eq_of_lt hklt]
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - k =
          n + (i.val + (d - k)) := by
      omega
    rw [heq, Nat.add_mod_left]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - k =
          i.val + (d - k) := by
      omega
    rw [heq]


private theorem q19751_shiftLeft_shiftRight_cancel
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) :
    PPL.shiftLeft ring (PPL.shiftRight ring i d) d = i := by
  rw [q19751_shiftLeft_shiftRight_sub ring i d d
      (Nat.le_refl _) hd,
    Nat.sub_self,
    q19751_shiftRight_zero]


private theorem q19751_shiftRight_injective_lt
    {n : Nat} (ring : DirectedRing n)
    (origin : Fin n) (a b : Nat)
    (ha : a < n) (hb : b < n)
    (h :
      PPL.shiftRight ring origin a =
        PPL.shiftRight ring origin b) :
    a = b := by
  have hc :=
    congrArg
      (fun q : Fin n => PPL.cyclicOffset ring origin q)
      h
  rw [q19751_cyclicOffset_shiftRight_of_lt ring origin a ha,
    q19751_cyclicOffset_shiftRight_of_lt ring origin b hb] at hc
  exact hc


private theorem q19751_fin3_cases
    (b : Fin 3) :
    b = (0 : Fin 3) ∨
      b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega


private theorem q19751_rowE_right_born4
    (l : Cell4) :
    (PPL.Elim.rowE l born4).2 = born4 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases q19751_fin3_cases lb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  simp [PPL.Elim.rowE, born4]


private theorem q19751_rowE_cleared_right
    (l r : Cell4)
    (hr : CellCleared r) :
    CellCleared (PPL.Elim.rowE l r).2 := by
  unfold CellCleared at hr ⊢
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases q19751_fin3_cases lb with rfl | rfl | rfl <;>
  rcases q19751_fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem q19751_rowE_cleared_pair
    (l r : Cell4)
    (hl : CellCleared l)
    (hr : CellCleared r) :
    And
      (CellCleared (PPL.Elim.rowE l r).1)
      (CellCleared (PPL.Elim.rowE l r).2) := by
  unfold CellCleared at hl hr ⊢
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases q19751_fin3_cases lb with rfl | rfl | rfl <;>
  rcases q19751_fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem q19751_rowE_moved_live_right
    (l r : Cell4)
    (hr : r.bullet ≠ (2 : Fin 3))
    (hout :
      (PPL.Elim.rowE l r).2.bullet = (2 : Fin 3)) :
    CellCleared (PPL.Elim.rowE l r).2 := by
  unfold CellCleared
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases q19751_fin3_cases lb with rfl | rfl | rfl <;>
  rcases q19751_fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem q19751_rowE_moved_live_pair
    (l r : Cell4)
    (hl : CellCleared l)
    (hr : r.bullet ≠ (2 : Fin 3))
    (hout :
      (PPL.Elim.rowE l r).2.bullet = (2 : Fin 3)) :
    And
      (CellCleared (PPL.Elim.rowE l r).1)
      (CellCleared (PPL.Elim.rowE l r).2) := by
  unfold CellCleared at hl ⊢
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases q19751_fin3_cases lb with rfl | rfl | rfl <;>
  rcases q19751_fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem q19751_badLive_iff_four
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n) :
    BadLive ring C i <->
      BadLive4Reach ring (project4 C) i := by
  rfl


private theorem q19751_project_step_case
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) :
    FourFieldStepCase ring
      (project4 g.physical)
      (project4 (ghostStep hpsi ring g e).physical)
      e := by
  have he := ghostStep_erase hpsi ring g e
  change
    (ghostStep hpsi ring g e).physical =
      PPL.Convergence.BulletSweep.step ring g.physical e at he
  rw [he]
  have hc :=
    PPL.Safety.PeacefulProps.step_fourField_cases
      hn3 hpsi ring g.physical e
  dsimp only at hc
  simpa [PPL.Convergence.BulletSweep.step] using hc


private theorem q19751_shiftLeft_zero
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftLeft ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]


private theorem q19751_dLLBy_self
    {n : Nat} (ring : DirectedRing n)
    (leader : Fin n -> Bool) (i : Fin n)
    (hi : leader i = true) :
    PPL.dLLBy ring leader i = some 0 := by
  unfold PPL.dLLBy
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ m =>
      have hz : PPL.shiftLeft ring i 0 = i :=
        q19751_shiftLeft_zero ring i
      simp [PPL.scanDistance, hz, hi]


private theorem q19751_peaceful4_self_safe
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n -> Cell4) (i : Fin n)
    (hs : (D i).signalB = false)
    (hl : (D i).leader = true)
    (hh : (D i).shield = true) :
    Peaceful4 ring D i := by
  unfold Peaceful4 PPL.PeacefulCore
  rw [q19751_dLLBy_self
    ring (fun j => (D j).leader) i hl]
  constructor
  · simpa [q19751_shiftLeft_zero] using hh
  · intro j
    have hj : j.val = 0 := by
      omega
    have hp : PPL.shiftLeft ring i j.val = i := by
      rw [hj]
      exact q19751_shiftLeft_zero ring i
    rw [hp]
    exact hs


private theorem q19751_scan_none_all_false
    {n : Nat}
    (site : Nat -> Fin n)
    (hit : Fin n -> Bool)
    (hfalse : forall i : Fin n, hit i = false) :
    forall fuel start,
      PPL.scanDistance site hit fuel start = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      rfl
  | succ fuel ih =>
      intro start
      simp [PPL.scanDistance, hfalse, ih]


private theorem q19751_peaceful4_all_clear
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n -> Cell4) (i : Fin n)
    (hleader : forall q : Fin n, (D q).leader = false)
    (hsignal : forall q : Fin n, (D q).signalB = false) :
    Peaceful4 ring D i := by
  unfold Peaceful4 PPL.PeacefulCore
  have hd :
      PPL.dLLBy ring (fun q => (D q).leader) i = none := by
    unfold PPL.dLLBy
    exact
      q19751_scan_none_all_false
        (fun d => PPL.shiftLeft ring i d)
        (fun q => (D q).leader)
        hleader n 0
  rw [hd]
  exact hsignal


private theorem q19751_scan_some_first
    {n : Nat}
    (site : Nat -> Fin n)
    (hit : Fin n -> Bool) :
    forall fuel start target,
      start <= target ->
      target < start + fuel ->
      hit (site target) = true ->
      (forall q, start <= q -> q < target ->
        hit (site q) = false) ->
      PPL.scanDistance site hit fuel start = some target := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target hst hlt hhit hbefore
      omega
  | succ fuel ih =>
      intro start target hst hlt hhit hbefore
      by_cases heq : start = target
      · subst target
        simp [PPL.scanDistance, hhit]
      · have hslt : start < target := by
          omega
        have hzero :
            hit (site start) = false :=
          hbefore start (Nat.le_refl _) hslt
        have hrec :=
          ih (start + 1) target
            (by omega) (by omega) hhit
            (fun q hq0 hq1 =>
              hbefore q (by omega) hq1)
        simpa [PPL.scanDistance, hzero] using hrec


private theorem q19751_peaceful4_first_left_leader
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n -> Cell4)
    (i : Fin n) (d : Nat)
    (hd : d < n)
    (hleader :
      (D (PPL.shiftLeft ring i d)).leader = true)
    (hshield :
      (D (PPL.shiftLeft ring i d)).shield = true)
    (hbefore :
      forall q : Nat, q < d ->
        (D (PPL.shiftLeft ring i q)).leader = false)
    (hsignal :
      forall q : Nat, q <= d ->
        (D (PPL.shiftLeft ring i q)).signalB = false) :
    Peaceful4 ring D i := by
  unfold Peaceful4 PPL.PeacefulCore
  have hscan :
      PPL.dLLBy ring (fun q => (D q).leader) i =
        some d := by
    unfold PPL.dLLBy
    exact
      q19751_scan_some_first
        (fun q => PPL.shiftLeft ring i q)
        (fun q => (D q).leader)
        n 0 d
        (Nat.zero_le _)
        (by omega)
        hleader
        (fun q hq0 hqd =>
          hbefore q hqd)
  rw [hscan]
  constructor
  · exact hshield
  · intro j
    exact hsignal j.val (by omega)


/--
A CreateLeader birth strictly inside the already-cleared arc makes the
tracked live bullet peaceful in that same physical step.
-/
private theorem q19751_birth_inside_arc_peaceful
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (D D' : Fin n -> Cell4)
    (e origin : Fin n)
    (s d : Nat)
    (hslt : s < n)
    (hd1 : 1 <= d)
    (hds : d <= s)
    (htrail :
      forall x : Nat, 1 <= x -> x <= s ->
        CellCleared (D (PPL.shiftRight ring origin x)))
    (hother :
      forall k : Fin n,
        k ≠ e ->
        k ≠ ring.rightNeighbor e ->
        D' k = D k)
    (hrborn :
      D' (ring.rightNeighbor e) = born4)
    (hrpos :
      ring.rightNeighbor e =
        PPL.shiftRight ring origin d) :
    Peaceful4 ring D'
      (PPL.shiftRight ring origin s) := by
  have hdlt : d < n := by
    omega
  have hepos :
      e = PPL.shiftRight ring origin (d - 1) := by
    calc
      e = ring.leftNeighbor (ring.rightNeighbor e) :=
        (q19751_leftNeighbor_rightNeighbor ring e).symm
      _ = ring.leftNeighbor
            (PPL.shiftRight ring origin d) := by
          rw [hrpos]
      _ = PPL.shiftLeft ring
            (PPL.shiftRight ring origin d) 1 :=
          (q19751_shiftLeft_one (by omega) ring _).symm
      _ = PPL.shiftRight ring origin (d - 1) :=
          q19751_shiftLeft_shiftRight_sub
            ring origin d 1 (by omega) hdlt
  have habove :
      forall x : Nat, d < x -> x <= s ->
        CellCleared
          (D' (PPL.shiftRight ring origin x)) := by
    intro x hdx hxs
    have hxlt : x < n := by
      omega
    have hpre :=
      htrail x (by omega) hxs
    let q := PPL.shiftRight ring origin x
    have hqr : q ≠ ring.rightNeighbor e := by
      intro h
      have heq :
          PPL.shiftRight ring origin x =
            PPL.shiftRight ring origin d := by
        calc
          PPL.shiftRight ring origin x = q := rfl
          _ = ring.rightNeighbor e := h
          _ = PPL.shiftRight ring origin d := hrpos
      have hxd :=
        q19751_shiftRight_injective_lt
          ring origin x d hxlt hdlt heq
      omega
    have hqe : q ≠ e := by
      intro h
      have heq :
          PPL.shiftRight ring origin x =
            PPL.shiftRight ring origin (d - 1) := by
        calc
          PPL.shiftRight ring origin x = q := rfl
          _ = e := h
          _ = PPL.shiftRight ring origin (d - 1) := hepos
      have hdm1 : d - 1 < n := by
        omega
      have hxd :=
        q19751_shiftRight_injective_lt
          ring origin x (d - 1) hxlt hdm1 heq
      omega
    have hs := hother q hqe hqr
    rw [hs]
    exact hpre
  have hbirthLeader :
      (D' (PPL.shiftRight ring origin d)).leader = true := by
    rw [← hrpos, hrborn]
    rfl
  have hbirthShield :
      (D' (PPL.shiftRight ring origin d)).shield = true := by
    rw [← hrpos, hrborn]
    rfl
  have hbirthSignal :
      (D' (PPL.shiftRight ring origin d)).signalB = false := by
    rw [← hrpos, hrborn]
    rfl
  let cur := PPL.shiftRight ring origin s
  let gap := s - d
  have hgaplt : gap < n := by
    dsimp [gap]
    omega
  have htarget :
      PPL.shiftLeft ring cur gap =
        PPL.shiftRight ring origin d := by
    dsimp [cur, gap]
    calc
      PPL.shiftLeft ring
          (PPL.shiftRight ring origin s) (s - d) =
          PPL.shiftRight ring origin (s - (s - d)) :=
        q19751_shiftLeft_shiftRight_sub
          ring origin s (s - d) (by omega) hslt
      _ = PPL.shiftRight ring origin d := by
        congr 1
        omega
  have hbefore :
      forall q : Nat, q < gap ->
        (D' (PPL.shiftLeft ring cur q)).leader = false := by
    intro q hq
    have hqle : q <= s := by
      dsimp [gap] at hq
      omega
    have hgeom :
        PPL.shiftLeft ring cur q =
          PPL.shiftRight ring origin (s - q) := by
      dsimp [cur]
      exact
        q19751_shiftLeft_shiftRight_sub
          ring origin s q hqle hslt
    rw [hgeom]
    have hx : d < s - q := by
      dsimp [gap] at hq
      omega
    exact (habove (s - q) hx (by omega)).1
  have hsignals :
      forall q : Nat, q <= gap ->
        (D' (PPL.shiftLeft ring cur q)).signalB = false := by
    intro q hq
    have hqle : q <= s := by
      dsimp [gap] at hq
      omega
    have hgeom :
        PPL.shiftLeft ring cur q =
          PPL.shiftRight ring origin (s - q) := by
      dsimp [cur]
      exact
        q19751_shiftLeft_shiftRight_sub
          ring origin s q hqle hslt
    rw [hgeom]
    by_cases heq : q = gap
    · dsimp [gap] at heq
      have hsqd : s - q = d := by
        omega
      rw [hsqd]
      exact hbirthSignal
    · have hx : d < s - q := by
        dsimp [gap] at hq heq
        omega
      exact (habove (s - q) hx (by omega)).2
  apply
    q19751_peaceful4_first_left_leader
      ring D' cur gap hgaplt
  · rw [htarget]
    exact hbirthLeader
  · rw [htarget]
    exact hbirthShield
  · exact hbefore
  · exact hsignals


theorem badSweepClearedArcInvariant_initial
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    BadSweepClearedArcInvariant ring (initialGhost C) := by
  intro i o howner hbad
  change BadLive ring C i at hbad
  let oi : BulletOwner n :=
    {
      tag := { origin := i, serial := 0 }
      swept := 0
    }
  have hsome : some oi = some o := by
    simpa [initialGhost, hbad.1, oi] using howner
  have ho : oi = o := Option.some.inj hsome
  subst o
  constructor
  · exact (q19751_shiftRight_zero ring i).symm
  · intro d hd1 hd0 hdn
    dsimp only [oi] at hd0
    omega


private theorem q19751_bad_swept_lt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (hinv : BadSweepClearedArcInvariant ring g)
    (i : Fin n) (o : BulletOwner n)
    (howner : g.owner i = some o)
    (hbad : BadLive ring g.physical i) :
    o.swept < n := by
  have hi := hinv i o howner hbad
  by_cases hs : o.swept < n
  · exact hs
  · have hnle : n <= o.swept := by
      omega
    have hall :
        forall q : Fin n,
          CellCleared (project4 g.physical q) := by
      intro q
      let d := PPL.cyclicOffset ring o.tag.origin q
      have hdlt : d < n := by
        dsimp [d]
        unfold PPL.cyclicOffset
        exact Nat.mod_lt _ ring.hn
      have hshift :
          PPL.shiftRight ring o.tag.origin d = q := by
        simpa [d] using
          q19751_shiftRight_cyclicOffset
            ring o.tag.origin q
      by_cases hd0 : d = 0
      · have hqorigin : q = o.tag.origin := by
          have hz := hshift
          rw [hd0, q19751_shiftRight_zero] at hz
          exact hz.symm
        have hc :=
          hi.2 n (by omega) hnle (Nat.le_refl n)
        rw [q19751_shiftRight_n] at hc
        simpa [hqorigin] using hc
      · have hdpos : 1 <= d := by
          omega
        have hds : d <= o.swept := by
          omega
        have hc := hi.2 d hdpos hds (by omega)
        rw [hshift] at hc
        exact hc
    have hpeace :=
      q19751_peaceful4_all_clear
        ring (project4 g.physical) i
        (fun q => (hall q).1)
        (fun q => (hall q).2)
    have hb4 :=
      (q19751_badLive_iff_four ring g.physical i).1 hbad
    exact False.elim (hb4.2 hpeace)


private theorem q19751_post_bad_owner_cases
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e i : Fin n)
    (o' : BulletOwner n)
    (hsound : LineageSound ring g)
    (howner :
      (ghostStep hpsi ring g e).owner i = some o')
    (hbad :
      BadLive ring (ghostStep hpsi ring g e).physical i) :
    exists j : Fin n, exists o : BulletOwner n,
      g.owner j = some o ∧
      BadLive ring g.physical j ∧
      o'.tag = o.tag ∧
      Or
        (i = j ∧
 o' = o)
        (j = e ∧
          i = ring.rightNeighbor e ∧
          o' = advanceOwner o ∧
          (g.physical (ring.rightNeighbor e)).bullet ≠
            (2 : Fin 3)) := by
  have hstep :=
    noNewBadOneStep_proved hn3 hpsi ring g e hsound
  have hanc := hstep.2 i o' howner hbad
  rcases hanc with
    ⟨j, o, hjo, hjbad, htag⟩
  refine ⟨j, o, hjo, hjbad, htag, ?_⟩
  have hne :=
    q19751_rightNeighbor_ne_self hn3 ring e
  by_cases hie : i = e
  · subst i
    have hs := ghostStep_owner_source hpsi ring g e
    rw [hs] at howner
    cases howner
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hr :=
        ghostStep_owner_responder hpsi ring g e hne
      rw [hr, if_pos hbad.1] at howner
      by_cases hrlive :
          (g.physical (ring.rightNeighbor e)).bullet =
            (2 : Fin 3)
      · rw [if_pos hrlive] at howner
        have hloc :=
          hsound.1
            (ring.rightNeighbor e) j o' o
            howner hjo htag
        subst j
        have hoo : o' = o := by
          exact
            Option.some.inj
              (howner.symm.trans hjo)
        subst o
        exact Or.inl ⟨rfl, rfl⟩
      · rw [if_neg hrlive] at howner
        by_cases helive :
            (g.physical e).bullet = (2 : Fin 3)
        · rw [if_pos helive] at howner
          cases heo : g.owner e with
          | none =>
              simp [bumpOwner, heo] at howner
          | some oe =>
              have hadv :
                  advanceOwner oe = o' := by
                have hs :
                    some (advanceOwner oe) = some o' := by
                  simpa [bumpOwner, heo] using howner
                exact Option.some.inj hs
              have htagEO : oe.tag = o.tag := by
                calc
                  oe.tag = (advanceOwner oe).tag := rfl
                  _ = o'.tag :=
                    congrArg BulletOwner.tag hadv
                  _ = o.tag := htag
              have hloc :=
                hsound.1 e j oe o heo hjo htagEO
              subst j
              have hoe : oe = o := by
                exact
                  Option.some.inj
                    (heo.symm.trans hjo)
              subst oe
              exact
                Or.inr
                  ⟨rfl, rfl, hadv.symm, hrlive⟩
        · rw [if_neg helive] at howner
          have hfresh :
              freshOwner g e = o' :=
            Option.some.inj howner
          have hfreshSerial :
              g.nextBirth = o'.tag.serial := by
            calc
              g.nextBirth =
                  (freshOwner g e).tag.serial := rfl
              _ = o'.tag.serial :=
                congrArg
                  (fun z : BulletOwner n => z.tag.serial)
                  hfresh
          have htagSerial :
              o'.tag.serial = o.tag.serial :=
            congrArg BulletTag.serial htag
          have hbound := hsound.2.1 j o hjo
          omega
    · have hother :=
        ghostStep_owner_other
          hpsi ring g e i hie hir
      rw [hother] at howner
      have hloc :=
        hsound.1 i j o' o howner hjo htag
      subst j
      have hoo : o' = o :=
        Option.some.inj (howner.symm.trans hjo)
      subst o
      exact Or.inl ⟨rfl, rfl⟩


private theorem q19751_moved_bad_succ_lt
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (o : BulletOwner n)
    (hinv : BadSweepClearedArcInvariant ring g)
    (howner : g.owner e = some o)
    (hbad : BadLive ring g.physical e)
    (hdest :
      (g.physical (ring.rightNeighbor e)).bullet ≠
        (2 : Fin 3))
    (hbadPost :
      BadLive ring
        (ghostStep hpsi ring g e).physical
        (ring.rightNeighbor e)) :
    o.swept + 1 < n := by
  have hpre := hinv e o howner hbad
  have hslt :=
    q19751_bad_swept_lt ring g hinv e o howner hbad
  by_cases hnext : o.swept + 1 < n
  · exact hnext
  · have hsn : o.swept + 1 = n := by
      omega
    have hspos : 1 <= o.swept := by
      omega
    have hsrc :=
      hpre.2 o.swept hspos (Nat.le_refl _) (by omega)
    have hcase :=
      q19751_project_step_case hn3 hpsi ring g e
    have hbad4 :=
      (q19751_badLive_iff_four
        ring
        (ghostStep hpsi ring g e).physical
        (ring.rightNeighbor e)).1 hbadPost
    have hdest4 :
        (project4 g.physical
          (ring.rightNeighbor e)).bullet ≠
            (2 : Fin 3) := by
      exact hdest
    have hrOrigin :
        ring.rightNeighbor e = o.tag.origin := by
      calc
        ring.rightNeighbor e =
            ring.rightNeighbor
              (PPL.shiftRight ring o.tag.origin o.swept) := by
          rw [hpre.1]
        _ = PPL.shiftRight ring o.tag.origin (o.swept + 1) :=
          (q19751_shiftRight_succ
            ring o.tag.origin o.swept).symm
        _ = PPL.shiftRight ring o.tag.origin n := by
          rw [hsn]
        _ = o.tag.origin :=
          q19751_shiftRight_n ring o.tag.origin
    unfold FourFieldStepCase at hcase
    dsimp only at hcase
    rcases hcase.2 with hrow | hbirth
    · have hrowLive :
          (PPL.Elim.rowE
            (project4 g.physical e)
            (project4 g.physical
              (ring.rightNeighbor e))).2.bullet =
              (2 : Fin 3) := by
        rw [← hrow.2]
        exact hbad4.1
      have hfields :=
        q19751_rowE_moved_live_pair
          (project4 g.physical e)
          (project4 g.physical (ring.rightNeighbor e))
          (by
            have hs := hsrc
            rw [← hpre.1] at hs
            exact hs)
          hdest4 hrowLive
      have hleft :
          CellCleared
            (project4
              (ghostStep hpsi ring g e).physical e) := by
        rw [hrow.1]
        exact hfields.1
      have hright :
          CellCleared
            (project4
              (ghostStep hpsi ring g e).physical
              (ring.rightNeighbor e)) := by
        rw [hrow.2]
        exact hfields.2
      have hall :
          forall q : Fin n,
            CellCleared
              (project4
                (ghostStep hpsi ring g e).physical q) := by
        intro q
        by_cases hqe : q = e
        · subst q
          exact hleft
        · by_cases hqr : q = ring.rightNeighbor e
          · subst q
            exact hright
          · let rel :=
              PPL.cyclicOffset ring o.tag.origin q
            have hrelLt : rel < n := by
              dsimp [rel]
              unfold PPL.cyclicOffset
              exact Nat.mod_lt _ ring.hn
            have hshift :
                PPL.shiftRight ring o.tag.origin rel = q := by
              simpa [rel] using
                q19751_shiftRight_cyclicOffset
                  ring o.tag.origin q
            have hrel0 : rel ≠ 0 := by
              intro hz
              have hs := hshift
              rw [hz, q19751_shiftRight_zero] at hs
              have hqR : q = ring.rightNeighbor e := by
                calc
                  q = o.tag.origin := hs.symm
                  _ = ring.rightNeighbor e := hrOrigin.symm
              exact hqr hqR
            have hrelPos : 1 <= rel := by
              omega
            have hrelSwept : rel <= o.swept := by
              omega
            have hqpre :=
              hpre.2 rel hrelPos hrelSwept (by omega)
            rw [hshift] at hqpre
            have hs := hcase.1 q hqe hqr
            rw [hs]
            exact hqpre
      have hp :=
        q19751_peaceful4_all_clear
          ring
          (project4 (ghostStep hpsi ring g e).physical)
          (ring.rightNeighbor e)
          (fun q => (hall q).1)
          (fun q => (hall q).2)
      exact False.elim (hbad4.2 hp)
    · have hrborn :
          project4
              (ghostStep hpsi ring g e).physical
              (ring.rightNeighbor e) =
            born4 := by
        exact
          hbirth.2.trans
            (q19751_rowE_right_born4
              (project4 g.physical e))
      have hp :=
        q19751_peaceful4_self_safe
          ring
          (project4 (ghostStep hpsi ring g e).physical)
          (ring.rightNeighbor e)
          (by rw [hrborn]; rfl)
          (by rw [hrborn]; rfl)
          (by rw [hrborn]; rfl)
      exact False.elim (hbad4.2 hp)


/--
The cleared-arc relation is preserved by every literal ghostStep as long as
the pre-ghost is LineageSound.  No scheduling restriction is used.
-/
theorem badSweepClearedArcInvariant_step
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hsound : LineageSound ring g)
    (hinv : BadSweepClearedArcInvariant ring g) :
    BadSweepClearedArcInvariant ring
      (ghostStep hpsi ring g e) := by
  intro i o' howner' hbad'
  obtain
    ⟨j, o, howner, hbad, htag, hclass⟩ :=
      q19751_post_bad_owner_cases
        hn3 hpsi ring g e i o' hsound howner' hbad'
  have hpre := hinv j o howner hbad
  have hslt :=
    q19751_bad_swept_lt ring g hinv j o howner hbad
  have hcase :=
    q19751_project_step_case hn3 hpsi ring g e
  rcases hclass with hsame | hmove
  · rcases hsame with ⟨hij, hoo⟩
    subst i
    subst o'
    have hbad4 :=
      (q19751_badLive_iff_four
        ring (ghostStep hpsi ring g e).physical j).1 hbad'
    refine And.intro hpre.1 ?_
    intro d hd1 hdle hdn
    dsimp only
    let q := PPL.shiftRight ring o.tag.origin d
    change
      CellCleared
        (project4 (ghostStep hpsi ring g e).physical q)
    have hpreClear :=
      hpre.2 d hd1 hdle hdn
    change
      CellCleared (project4 g.physical q)
        at hpreClear
    by_cases hqe : q = e
    · have hdne : d ≠ o.swept := by
        intro hds
        have hqj : q = j := by
          dsimp [q]
          rw [hds]
          exact hpre.1.symm
        have hje : j = e :=
          hqj.symm.trans hqe
        have hc := howner'
        rw [hje] at hc
        have hs := ghostStep_owner_source hpsi ring g e
        rw [hs] at hc
        cases hc
      have hdlt : d < o.swept := by
        omega
      have hepos :
          e = PPL.shiftRight ring o.tag.origin d := by
        simpa [q] using hqe.symm
      have hrpos :
          ring.rightNeighbor e =
            PPL.shiftRight ring o.tag.origin (d + 1) := by
        calc
          ring.rightNeighbor e =
              ring.rightNeighbor
                (PPL.shiftRight ring o.tag.origin d) := by
            rw [hepos]
          _ = PPL.shiftRight ring o.tag.origin (d + 1) :=
            (q19751_shiftRight_succ
              ring o.tag.origin d).symm
      have hright :=
        hpre.2 (d + 1)
          (by omega) (by omega) (by omega)
      rw [← hrpos] at hright
      have hc := hcase
      unfold FourFieldStepCase at hc
      dsimp only at hc
      rcases hc.2 with hrow | hbirth
      · have hp :=
          q19751_rowE_cleared_pair
            (project4 g.physical e)
            (project4 g.physical (ring.rightNeighbor e))
            (by
              have hs := hpreClear
              rw [hqe] at hs
              exact hs)
            hright
        rw [hqe, hrow.1]
        exact hp.1
      · have hrborn :
            project4
                (ghostStep hpsi ring g e).physical
                (ring.rightNeighbor e) =
              born4 := by
          exact
            hbirth.2.trans
              (q19751_rowE_right_born4
                (project4 g.physical e))
        have hp :=
          q19751_birth_inside_arc_peaceful
            hn3 ring
            (project4 g.physical)
            (project4 (ghostStep hpsi ring g e).physical)
            e o.tag.origin o.swept (d + 1)
            hslt (by omega) (by omega)
            (fun x hx hxs =>
              hpre.2 x hx hxs (by omega))
            hc.1 hrborn hrpos
        have hpj :
            Peaceful4 ring
              (project4 (ghostStep hpsi ring g e).physical)
              j := by
          rw [hpre.1]
          exact hp
        exact False.elim (hbad4.2 hpj)
    · by_cases hqr : q = ring.rightNeighbor e
      · have hrpre := hpreClear
        rw [hqr] at hrpre
        have hrpos :
            ring.rightNeighbor e =
              PPL.shiftRight ring o.tag.origin d := by
          simpa [q] using hqr.symm
        have hc := hcase
        unfold FourFieldStepCase at hc
        dsimp only at hc
        rcases hc.2 with hrow | hbirth
        · rw [hqr, hrow.2]
          exact
            q19751_rowE_cleared_right
              (project4 g.physical e)
              (project4 g.physical (ring.rightNeighbor e))
              hrpre
        · have hrborn :
              project4
                  (ghostStep hpsi ring g e).physical
                  (ring.rightNeighbor e) =
                born4 := by
            exact
              hbirth.2.trans
                (q19751_rowE_right_born4
                  (project4 g.physical e))
          have hp :=
            q19751_birth_inside_arc_peaceful
              hn3 ring
              (project4 g.physical)
              (project4 (ghostStep hpsi ring g e).physical)
              e o.tag.origin o.swept d
              hslt hd1 hdle
              (fun x hx hxs =>
                hpre.2 x hx hxs (by omega))
              hc.1 hrborn hrpos
          have hpj :
              Peaceful4 ring
                (project4 (ghostStep hpsi ring g e).physical)
                j := by
            rw [hpre.1]
            exact hp
          exact False.elim (hbad4.2 hpj)
      · have hc := hcase
        unfold FourFieldStepCase at hc
        dsimp only at hc
        have hs := hc.1 q hqe hqr
        rw [hs]
        exact hpreClear
  · rcases hmove with
      ⟨hje, hir, hadv, hdest⟩
    subst j
    subst i
    subst o'
    have hnext :=
      q19751_moved_bad_succ_lt
        hn3 hpsi ring g e o
        hinv howner hbad hdest hbad'
    have hbad4 :=
      (q19751_badLive_iff_four
        ring
        (ghostStep hpsi ring g e).physical
        (ring.rightNeighbor e)).1 hbad'
    have hcoordPost :
        ring.rightNeighbor e =
          PPL.shiftRight ring o.tag.origin (o.swept + 1) := by
      calc
        ring.rightNeighbor e =
            ring.rightNeighbor
              (PPL.shiftRight ring o.tag.origin o.swept) := by
          rw [hpre.1]
        _ = PPL.shiftRight ring o.tag.origin (o.swept + 1) :=
          (q19751_shiftRight_succ
            ring o.tag.origin o.swept).symm
    refine And.intro ?_ ?_
    · simpa [advanceOwner] using hcoordPost
    · intro d hd1 hdle hdn
      dsimp only [advanceOwner] at hdle ⊢
      let q := PPL.shiftRight ring o.tag.origin d
      change
        CellCleared
          (project4 (ghostStep hpsi ring g e).physical q)
      have hcase0 := hcase
      unfold FourFieldStepCase at hcase0
      dsimp only at hcase0
      by_cases hnew : d = o.swept + 1
      · have hqr : q = ring.rightNeighbor e := by
          dsimp [q]
          rw [hnew]
          exact hcoordPost.symm
        rcases hcase0.2 with hrow | hbirth
        · have hrowLive :
              (PPL.Elim.rowE
                (project4 g.physical e)
                (project4 g.physical
                  (ring.rightNeighbor e))).2.bullet =
                  (2 : Fin 3) := by
            rw [← hrow.2]
            exact hbad4.1
          have hdest4 :
              (project4 g.physical
                (ring.rightNeighbor e)).bullet ≠
                  (2 : Fin 3) := by
            exact hdest
          have hp :=
            q19751_rowE_moved_live_right
              (project4 g.physical e)
              (project4 g.physical (ring.rightNeighbor e))
              hdest4 hrowLive
          rw [hqr, hrow.2]
          exact hp
        · have hrborn :
              project4
                  (ghostStep hpsi ring g e).physical
                  (ring.rightNeighbor e) =
                born4 := by
            exact
              hbirth.2.trans
                (q19751_rowE_right_born4
                  (project4 g.physical e))
          have hp :=
            q19751_peaceful4_self_safe
              ring
              (project4 (ghostStep hpsi ring g e).physical)
              (ring.rightNeighbor e)
              (by rw [hrborn]; rfl)
              (by rw [hrborn]; rfl)
              (by rw [hrborn]; rfl)
          exact False.elim (hbad4.2 hp)
      · have hdold : d <= o.swept := by
          omega
        have hpreClear :=
          hpre.2 d hd1 hdold hdn
        change
          CellCleared (project4 g.physical q)
            at hpreClear
        have hqr : q ≠ ring.rightNeighbor e := by
          intro h
          have heq :
              PPL.shiftRight ring o.tag.origin d =
                PPL.shiftRight ring o.tag.origin (o.swept + 1) := by
            calc
              PPL.shiftRight ring o.tag.origin d = q := rfl
              _ = ring.rightNeighbor e := h
              _ =
                  PPL.shiftRight ring o.tag.origin (o.swept + 1) :=
                hcoordPost
          have hdeq :=
            q19751_shiftRight_injective_lt
              ring o.tag.origin d (o.swept + 1)
              (by omega) hnext heq
          exact hnew hdeq
        by_cases hqe : q = e
        · rcases hcase0.2 with hrow | hbirth
          · have hrowLive :
                (PPL.Elim.rowE
                  (project4 g.physical e)
                  (project4 g.physical
                    (ring.rightNeighbor e))).2.bullet =
                    (2 : Fin 3) := by
              rw [← hrow.2]
              exact hbad4.1
            have hdest4 :
                (project4 g.physical
                  (ring.rightNeighbor e)).bullet ≠
                    (2 : Fin 3) := by
              exact hdest
            have hp :=
              q19751_rowE_moved_live_pair
                (project4 g.physical e)
                (project4 g.physical (ring.rightNeighbor e))
                (by
                  have hs := hpreClear
                  rw [hqe] at hs
                  exact hs)
                hdest4 hrowLive
            rw [hqe, hrow.1]
            exact hp.1
          · have hrborn :
                project4
                    (ghostStep hpsi ring g e).physical
                    (ring.rightNeighbor e) =
                  born4 := by
              exact
                hbirth.2.trans
                  (q19751_rowE_right_born4
                    (project4 g.physical e))
            have hp :=
              q19751_peaceful4_self_safe
                ring
                (project4 (ghostStep hpsi ring g e).physical)
                (ring.rightNeighbor e)
                (by rw [hrborn]; rfl)
                (by rw [hrborn]; rfl)
                (by rw [hrborn]; rfl)
            exact False.elim (hbad4.2 hp)
        · have hs := hcase0.1 q hqe hqr
          rw [hs]
          exact hpreClear


private theorem q19751_initial_owner_serial_bound
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    OwnerSerialBound (initialGhost C) := by
  intro i o howner
  by_cases hlive : (C i).bullet = (2 : Fin 3)
  · let oi : BulletOwner n :=
      { tag := { origin := i, serial := 0 }, swept := 0 }
    have hsome : some oi = some o := by
      simpa [initialGhost, hlive, oi] using howner
    have ho : oi = o := Option.some.inj hsome
    subst o
    simp [initialGhost, oi]
  · simp [initialGhost, hlive] at howner


private theorem q19751_initial_bad_owner_coverage
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    BadOwnerCoverage ring (initialGhost C) := by
  intro i hbad
  refine
    ⟨
      ({ tag := { origin := i, serial := 0 }, swept := 0 } :
        BulletOwner n),
      ?_⟩
  have hb : (C i).bullet = (2 : Fin 3) := hbad.1
  simp [initialGhost, hb]


private theorem q19751_initial_lineage_sound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    LineageSound ring (initialGhost C) := by
  exact
    And.intro
      (initialGhost_noCloning C)
      (And.intro
        (q19751_initial_owner_serial_bound C)
        (q19751_initial_bad_owner_coverage ring C))


private theorem q19751_invariant_run_from
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g)
    (hinv : BadSweepClearedArcInvariant ring g) :
    BadSweepClearedArcInvariant ring
      (ghostRun hpsi ring g schedule) := by
  induction schedule generalizing g with
  | nil =>
      exact hinv
  | cons e rest ih =>
      have hs1 :
          LineageSound ring (ghostStep hpsi ring g e) :=
        (noNewBadOneStep_proved
          hn3 hpsi ring g e hsound).1
      have hi1 :=
        badSweepClearedArcInvariant_step
          hn3 hpsi ring g e hsound hinv
      simpa [ghostRun] using
        (ih (g := ghostStep hpsi ring g e) hs1 hi1)


theorem badSweepClearedArcInvariant_reachable
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (hreach :
      exists C : Config n psi kappa,
        exists schedule : DetSchedule n,
          g = ghostRun hpsi ring (initialGhost C) schedule) :
    BadSweepClearedArcInvariant ring g := by
  rcases hreach with ⟨C, schedule, hg⟩
  subst g
  exact
    q19751_invariant_run_from
      hn3 hpsi ring
      (initialGhost C) schedule
      (q19751_initial_lineage_sound ring C)
      (badSweepClearedArcInvariant_initial ring C)


private theorem q19751_sweepPendingSuffix_step
    {n : Nat}
    (ring : DirectedRing n)
    (pending : DetSchedule n)
    (e : Fin n)
    (hsuffix : SweepPendingSuffix ring pending) :
    SweepPendingSuffix ring (sweepPendingStep pending e) := by
  unfold SweepPendingSuffix at hsuffix ⊢
  rcases hsuffix with ⟨pre, hword⟩
  cases pending with
  | nil =>
      refine ⟨pre, ?_⟩
      simpa [sweepPendingStep] using hword
  | cons requested rest =>
      by_cases he : e = requested
      · subst e
        have hstep :
            sweepPendingStep (requested :: rest) requested =
              rest := by
          simp [sweepPendingStep]
        rw [hstep]
        refine ⟨pre ++ [requested], ?_⟩
        calc
          PPL.Convergence.BulletSweep.lemma15SweepWord ring =
              pre ++ requested :: rest := hword
          _ = (pre ++ [requested]) ++ rest := by
            simp [List.append_assoc]
      · have hstep :
            sweepPendingStep (requested :: rest) e =
              requested :: rest := by
          simp [sweepPendingStep, he]
        rw [hstep]
        exact ⟨pre, hword⟩


private theorem q19751_sweepWord_get_val
    {n : Nat}
    (ring : DirectedRing n)
    (m : Nat)
    (hm :
      m <
        (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length) :
    ((PPL.Convergence.BulletSweep.lemma15SweepWord ring).get
      ⟨m, hm⟩).val = m % n := by
  have hm2 := hm
  rw [PPL.Convergence.BulletSweep.lemma15SweepWord_length ring]
    at hm2
  unfold PPL.Convergence.BulletSweep.lemma15SweepWord
  simp only [List.get_eq_getElem, List.getElem_append]
  by_cases hleft :
      m < (PPL.seqR ring
        (PPL.Convergence.BulletSweep.zeroSite ring) n).length
  · rw [dif_pos hleft]
    have hmn : m < n := by
      simpa [PPL.seqR] using hleft
    simp only [PPL.seqR, List.getElem_ofFn]
    simp only [PPL.shiftRight,
      PPL.Convergence.BulletSweep.zeroSite,
      Nat.zero_add]
  · rw [dif_neg hleft]
    have hnot : Not (m < n) := by
      simpa [PPL.seqR] using hleft
    have hge : n <= m := by
      omega
    have hsub : m - n < n := by
      omega
    simp only [PPL.seqR, List.length_ofFn, List.getElem_ofFn]
    simp only [PPL.shiftRight,
      PPL.Convergence.BulletSweep.zeroSite,
      Nat.zero_add]
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]


private theorem q19751_pending_head_of_tight_credit
    {n : Nat}
    (ring : DirectedRing n)
    (origin i : Fin n)
    (swept : Nat)
    (requested : Fin n)
    (rest : DetSchedule n)
    (hsuffix :
      SweepPendingSuffix ring (requested :: rest))
    (hsite :
      i = PPL.shiftRight ring origin swept)
    (htight :
      (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
          (requested :: rest).length =
        origin.val + swept) :
    requested = i := by
  rcases hsuffix with ⟨pre, hword⟩
  have hidx :
      pre.length <
        (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length := by
    rw [hword]
    simp
  have hget :
      (PPL.Convergence.BulletSweep.lemma15SweepWord ring).get
          ⟨pre.length, hidx⟩ =
        requested := by
    simp only [List.get_eq_getElem]
    simp only [hword, List.getElem_append]
    simp
  have hval :=
    q19751_sweepWord_get_val ring pre.length hidx
  rw [hget] at hval
  have htight' := htight
  rw [hword] at htight'
  simp only [List.length_append, List.length_cons] at htight'
  have hpre :
      pre.length = origin.val + swept := by
    omega
  apply Fin.ext
  calc
    requested.val = pre.length % n := hval
    _ = (origin.val + swept) % n := by
      rw [hpre]
    _ = (PPL.shiftRight ring origin swept).val := rfl
    _ = i.val := by
      exact (congrArg Fin.val hsite).symm


private theorem q19751_matched_cons_succ
    {n : Nat}
    (ring : DirectedRing n)
    (requested : Fin n)
    (rest : DetSchedule n)
    (hsuffix :
      SweepPendingSuffix ring (requested :: rest)) :
    (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
        rest.length =
      ((PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
          (requested :: rest).length) + 1 := by
  rcases hsuffix with ⟨pre, hword⟩
  rw [hword]
  simp only [List.length_append, List.length_cons]
  omega


private theorem q19751_matched_step_le_succ
    {n : Nat}
    (ring : DirectedRing n)
    (pending : DetSchedule n)
    (e : Fin n)
    (hsuffix : SweepPendingSuffix ring pending) :
    (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
        (sweepPendingStep pending e).length <=
      ((PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
          pending.length) + 1 := by
  cases pending with
  | nil =>
      simp [sweepPendingStep]
  | cons requested rest =>
      by_cases he : e = requested
      · subst e
        have hs :=
          q19751_matched_cons_succ
            ring requested rest hsuffix
        have hstep :
            sweepPendingStep (requested :: rest) requested =
              rest := by
          simp [sweepPendingStep]
        rw [hstep, hs]
        exact Nat.le_refl _
      · have hstep :
            sweepPendingStep (requested :: rest) e =
              requested :: rest := by
          simp [sweepPendingStep, he]
        rw [hstep]
        omega


private theorem q19751_credit_same
    {n : Nat}
    (ring : DirectedRing n)
    (origin i : Fin n)
    (swept : Nat)
    (pending : DetSchedule n)
    (e : Fin n)
    (hsuffix : SweepPendingSuffix ring pending)
    (hsite :
      i = PPL.shiftRight ring origin swept)
    (hcredit :
      (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
          pending.length <=
        origin.val + swept)
    (hne : e ≠ i) :
    (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
        (sweepPendingStep pending e).length <=
      origin.val + swept := by
  cases pending with
  | nil =>
      simpa [sweepPendingStep] using hcredit
  | cons requested rest =>
      by_cases he : e = requested
      · have hs :=
          q19751_matched_cons_succ
            ring requested rest hsuffix
        by_cases htight :
            (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
                (requested :: rest).length =
              origin.val + swept
        · have hhead :=
            q19751_pending_head_of_tight_credit
              ring origin i swept requested rest
              hsuffix hsite htight
          have hei : e = i := he.trans hhead
          exact False.elim (hne hei)
        · have hlt :
              (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
                  (requested :: rest).length <
                origin.val + swept := by
            omega
          have hstep :
              sweepPendingStep (requested :: rest) e =
                rest := by
            simp [sweepPendingStep, he]
          rw [hstep, hs]
          omega
      · have hstep :
            sweepPendingStep (requested :: rest) e =
              requested :: rest := by
          simp [sweepPendingStep, he]
        rw [hstep]
        exact hcredit


private theorem q19751_credit_move
    {n : Nat}
    (ring : DirectedRing n)
    (origin : Fin n)
    (swept : Nat)
    (pending : DetSchedule n)
    (e : Fin n)
    (hsuffix : SweepPendingSuffix ring pending)
    (hcredit :
      (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
          pending.length <=
        origin.val + swept) :
    (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
        (sweepPendingStep pending e).length <=
      origin.val + (swept + 1) := by
  have hs :=
    q19751_matched_step_le_succ
      ring pending e hsuffix
  omega


theorem badSweepProgressOneStepReachable_proved :
    BadSweepProgressOneStepReachable := by
  classical
  unfold BadSweepProgressOneStepReachable
  intro n psi kappa hn3 hpsi ring g e origin tag pending
    hreach hsound hstate
  have hinv :=
    badSweepClearedArcInvariant_reachable
      hn3 hpsi ring g hreach
  rcases hstate.2 with
    ⟨i, o, howner, htag, hbad,
      hsite, hswept, hcredit⟩
  have hpreInv := hinv i o howner hbad
  have hshiftEq :
      PPL.shiftRight ring origin o.swept =
        PPL.shiftRight ring o.tag.origin o.swept :=
    hsite.symm.trans hpreInv.1
  have hcancel :=
    congrArg
      (fun q : Fin n =>
        PPL.shiftLeft ring q o.swept)
      hshiftEq
  rw [q19751_shiftLeft_shiftRight_cancel
        ring origin o.swept hswept,
      q19751_shiftLeft_shiftRight_cancel
        ring o.tag.origin o.swept hswept] at hcancel
  have horiginTag :
      origin = tag.origin := by
    calc
      origin = o.tag.origin := hcancel
      _ = tag.origin :=
        congrArg BulletTag.origin htag
  let g' := ghostStep hpsi ring g e
  let pending' := sweepPendingStep pending e
  have hinv' :
      BadSweepClearedArcInvariant ring g' := by
    dsimp [g']
    exact
      badSweepClearedArcInvariant_step
        hn3 hpsi ring g e hsound hinv
  by_cases hret : LineageRetired ring g' tag
  · exact Or.inl hret
  · unfold LineageRetired at hret
    obtain ⟨ip, hnn⟩ :=
      Classical.not_forall.mp hret
    have htagged :
        TaggedBad ring g' tag ip :=
      Classical.not_not.mp hnn
    rcases htagged with
      ⟨op, hop, hoptag, hpbad⟩
    have hpinv := hinv' ip op hop hpbad
    have hpostSite :
        ip = PPL.shiftRight ring origin op.swept := by
      calc
        ip =
            PPL.shiftRight ring op.tag.origin op.swept :=
          hpinv.1
        _ =
            PPL.shiftRight ring tag.origin op.swept := by
          rw [hoptag]
        _ =
            PPL.shiftRight ring origin op.swept := by
          rw [← horiginTag]
    have hpostCap :
        op.swept < n :=
      q19751_bad_swept_lt
        ring g' hinv' ip op hop hpbad
    have hsuffix' :
        SweepPendingSuffix ring pending' := by
      dsimp [pending']
      exact
        q19751_sweepPendingSuffix_step
          ring pending e hstate.1
    have hclass0 :=
      q19751_post_bad_owner_cases
        hn3 hpsi ring g e ip op
        hsound
        (by simpa [g'] using hop)
        (by simpa [g'] using hpbad)
    rcases hclass0 with
      ⟨j, o0, hjowner, hjbad, hptag0, hclass⟩
    have hsameTag : o0.tag = o.tag := by
      calc
        o0.tag = op.tag := hptag0.symm
        _ = tag := hoptag
        _ = o.tag := htag.symm
    have hji :=
      hsound.1 j i o0 o
        hjowner howner hsameTag
    subst j
    have ho0 : o0 = o := by
      exact
        Option.some.inj
          (hjowner.symm.trans howner)
    subst o0
    have hcreditPost :
        (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
            pending'.length <=
          origin.val + op.swept := by
      rcases hclass with hsame | hmove
      · rcases hsame with ⟨hip, hopEq⟩
        have hene : e ≠ i := by
          intro hei
          have hc := hop
          have hipe : ip = e := hip.trans hei.symm
          rw [hipe] at hc
          have hs := ghostStep_owner_source hpsi ring g e
          change (ghostStep hpsi ring g e).owner e = some op at hc
          rw [hs] at hc
          cases hc
        have hc :=
          q19751_credit_same
            ring origin i o.swept pending e
            hstate.1 hsite hcredit hene
        dsimp [pending']
        calc
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
                (sweepPendingStep pending e).length <=
              origin.val + o.swept := hc
          _ = origin.val + op.swept := by
            rw [hopEq]
      · rcases hmove with
          ⟨hie, hip, hopEq, hdest⟩
        have hc :=
          q19751_credit_move
            ring origin o.swept pending e
            hstate.1 hcredit
        dsimp [pending']
        calc
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring).length -
                (sweepPendingStep pending e).length <=
              origin.val + (o.swept + 1) := hc
          _ = origin.val + op.swept := by
            rw [hopEq]
            rfl
    exact
      Or.inr
        ⟨hsuffix', ip, op, hop, hoptag, hpbad,
          hpostSite, hpostCap, hcreditPost⟩


theorem lemma15SublistSweep_proved :
    PPL.Convergence.BulletSweep.Lemma15SublistSweep := by
  exact
    lemma15SublistSweep_of_reachable
      noNewBadOneStep_proved
      badSweepProgressOneStepReachable_proved


end PPL.Convergence.BulletLineage


#print axioms PPL.Convergence.BulletLineage.badSweepClearedArcInvariant_initial
#print axioms PPL.Convergence.BulletLineage.badSweepClearedArcInvariant_step
#print axioms PPL.Convergence.BulletLineage.badSweepClearedArcInvariant_reachable
#print axioms PPL.Convergence.BulletLineage.badSweepProgressOneStepReachable_proved
#print axioms PPL.Convergence.BulletLineage.lemma15SublistSweep_proved


