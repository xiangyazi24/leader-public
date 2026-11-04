import Leader.PPL.Safety.PeacefulProps




namespace PPL.Safety.PeacefulProps




set_option autoImplicit false
set_option Elab.async false




private def leftOffset
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  PPL.shiftLeft ring i d




private def peaceScan
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n) :
    Nat → Nat → Prop
  | 0, _ => True
  | fuel + 1, d =>
      let x := leftOffset ring base d
      (D x).signalB = false ∧
        if (D x).leader = true then
          (D x).shield = true
        else
          peaceScan ring D base fuel (d + 1)




private def ScanHeadSafe (u : Cell4) : Prop :=
  u.signalB = false ∧
    (u.leader = true → u.shield = true)




private structure ScanFrame
    (before after : Cell4) : Prop where
  signalB : after.signalB = false
  leader : after.leader = before.leader
  shield : before.leader = true → after.shield = true




private theorem fin3_cases_scan (b : Fin 3) :
    b = (0 : Fin 3) ∨
      b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · omega




private theorem rightNeighbor_ne_self_scan
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega




private theorem leftNeighbor_rightNeighbor_scan
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by
      omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega




private theorem rightNeighbor_leftNeighbor_scan
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by
      omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by
      omega
    rw [heq]
    have hmod :
        (n + (i.val - 1)) % n = i.val - 1 := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    rw [hmod]
    have hs : i.val - 1 + 1 = i.val := by
      omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]




private theorem leftOffset_val_of_le
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) (hle : d ≤ i.val) :
    (leftOffset ring i d).val = i.val - d := by
  simp only [leftOffset, PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt hd]
  have heq : i.val + n - d = n + (i.val - d) := by
    omega
  rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega : i.val - d < n)]




private theorem leftOffset_val_of_lt
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) (hlt : i.val < d) :
    (leftOffset ring i d).val = n - (d - i.val) := by
  simp only [leftOffset, PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt hd]
  have heq : i.val + n - d = n - (d - i.val) := by
    omega
  rw [heq,
    Nat.mod_eq_of_lt
      (by omega : n - (d - i.val) < n)]




private theorem leftOffset_zero
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    leftOffset ring i 0 = i := by
  apply Fin.ext
  rw [leftOffset_val_of_le ring i 0 ring.hn (Nat.zero_le _)]
  simp




private theorem leftNeighbor_val_of_pos
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (hi : 0 < i.val) :
    (ring.leftNeighbor i).val = i.val - 1 := by
  simp only [DirectedRing.leftNeighbor]
  have heq : i.val + n - 1 = n + (i.val - 1) := by
    omega
  rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]




private theorem leftNeighbor_val_of_zero
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (hi : i.val = 0) :
    (ring.leftNeighbor i).val = n - 1 := by
  simp only [DirectedRing.leftNeighbor, hi, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]




private theorem leftOffset_succ
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d + 1 < n) :
    ring.leftNeighbor (leftOffset ring i d) =
      leftOffset ring i (d + 1) := by
  apply Fin.ext
  by_cases hlt : d < i.val
  · have hcur :
        (leftOffset ring i d).val = i.val - d :=
      leftOffset_val_of_le ring i d (by omega) (by omega)
    have hcurPos :
        0 < (leftOffset ring i d).val := by
      rw [hcur]
      omega
    rw [leftNeighbor_val_of_pos ring _ hcurPos,
      leftOffset_val_of_le ring i d (by omega) (by omega),
      leftOffset_val_of_le ring i (d + 1) hd (by omega)]
    omega
  · by_cases heq : d = i.val
    · have hcur :
          (leftOffset ring i d).val = 0 := by
        rw [leftOffset_val_of_le ring i d (by omega) (by omega)]
        omega
      rw [leftNeighbor_val_of_zero ring _ hcur,
        leftOffset_val_of_lt ring i (d + 1) hd (by omega)]
      omega
    · have hgt : i.val < d := by
        omega
      have hcur :
          (leftOffset ring i d).val =
            n - (d - i.val) :=
        leftOffset_val_of_lt ring i d (by omega) hgt
      have hcurPos :
          0 < (leftOffset ring i d).val := by
        rw [hcur]
        omega
      rw [leftNeighbor_val_of_pos ring _ hcurPos,
        leftOffset_val_of_lt ring i d (by omega) hgt,
        leftOffset_val_of_lt ring i (d + 1) hd (by omega)]
      omega




private theorem leftOffset_mod
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) :
    leftOffset ring i d =
      leftOffset ring i (d % n) := by
  apply Fin.ext
  simp [leftOffset, PPL.shiftLeft, Nat.mod_mod]


private theorem leftOffset_last
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n) :
    leftOffset ring i (n - 1) =
      ring.rightNeighbor i := by
  apply Fin.ext
  simp only [leftOffset, PPL.shiftLeft,
    DirectedRing.rightNeighbor]
  rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  have heq :
      i.val + n - (n - 1) = i.val + 1 := by
    omega
  rw [heq]




private theorem leftOffset_succ_all
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n) (d : Nat) :
    ring.leftNeighbor (leftOffset ring i d) =
      leftOffset ring i (d + 1) := by
  let r := d % n
  have hr : r < n := by
    dsimp [r]
    exact Nat.mod_lt _ ring.hn
  have hdEq :
      leftOffset ring i d =
        leftOffset ring i r := by
    simpa [r] using leftOffset_mod ring i d
  have hmod :
      (d + 1) % n = (r + 1) % n := by
    calc
      (d + 1) % n =
          (d % n + 1 % n) % n :=
        Nat.add_mod _ _ _
      _ = (r + 1) % n := by
        have h1 : 1 % n = 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [h1]
  by_cases hs : r + 1 < n
  · have hmod' :
        (d + 1) % n = r + 1 := by
      rw [hmod, Nat.mod_eq_of_lt hs]
    have hdNext :
        leftOffset ring i (d + 1) =
          leftOffset ring i (r + 1) := by
      calc
        leftOffset ring i (d + 1) =
            leftOffset ring i ((d + 1) % n) :=
          leftOffset_mod ring i (d + 1)
        _ = leftOffset ring i (r + 1) := by
          rw [hmod']
    rw [hdEq, hdNext]
    exact leftOffset_succ ring i r hs
  · have heq : r + 1 = n := by
      omega
    have hmod0 : (d + 1) % n = 0 := by
      rw [hmod, heq, Nat.mod_self]
    have hdNext :
        leftOffset ring i (d + 1) = i := by
      calc
        leftOffset ring i (d + 1) =
            leftOffset ring i ((d + 1) % n) :=
          leftOffset_mod ring i (d + 1)
        _ = leftOffset ring i 0 := by
          rw [hmod0]
        _ = i := leftOffset_zero ring i
    have hrEq : r = n - 1 := by
      omega
    calc
      ring.leftNeighbor (leftOffset ring i d) =
          ring.leftNeighbor (leftOffset ring i r) := by
        rw [hdEq]
      _ =
          ring.leftNeighbor
            (leftOffset ring i (n - 1)) := by
        rw [hrEq]
      _ = ring.leftNeighbor (ring.rightNeighbor i) := by
        rw [leftOffset_last ring hn2 i]
      _ = i := leftNeighbor_rightNeighbor_scan ring i
      _ = leftOffset ring i (d + 1) := hdNext.symm






private theorem leftOffset_ne_rightNeighbor_of_lt
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (i : Fin n)
    (d : Nat) (hd : d < n - 1) :
    leftOffset ring i d ≠ ring.rightNeighbor i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hwrap : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hwrap] at hv
    by_cases hle : d ≤ i.val
    · rw [leftOffset_val_of_le ring i d (by omega) hle] at hv
      omega
    · rw [leftOffset_val_of_lt ring i d
        (by omega) (by omega)] at hv
      omega
  · have hi : i.val + 1 = n := by
      omega
    rw [hi, Nat.mod_self] at hv
    rw [leftOffset_val_of_le ring i d
        (by omega) (by omega)] at hv
    omega




private theorem leftOffset_surjective
    {n : Nat} (ring : DirectedRing n)
    (base k : Fin n) :
    ∃ d : Nat, d < n ∧
      leftOffset ring base d = k := by
  by_cases hle : k.val ≤ base.val
  · let d := base.val - k.val
    have hd : d < n := by
      dsimp [d]
      omega
    refine ⟨d, hd, ?_⟩
    apply Fin.ext
    rw [leftOffset_val_of_le ring base d hd]
    · dsimp [d]
      omega
    · dsimp [d]
      omega
  · let d := base.val + n - k.val
    have hd : d < n := by
      dsimp [d]
      omega
    have hlt : base.val < d := by
      dsimp [d]
      omega
    refine ⟨d, hd, ?_⟩
    apply Fin.ext
    rw [leftOffset_val_of_lt ring base d hd hlt]
    dsimp [d]
    omega




private theorem leftOffset_rightNeighbor_succ
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (e : Fin n) :
    ∀ q : Nat, q + 1 < n →
      leftOffset ring (ring.rightNeighbor e) (q + 1) =
        leftOffset ring e q := by
  intro q
  induction q with
  | zero =>
      intro hq
      rw [← leftOffset_succ ring
        (ring.rightNeighbor e) 0 hq,
        leftOffset_zero,
        leftNeighbor_rightNeighbor_scan,
        leftOffset_zero]
  | succ q ih =>
      intro hq
      rw [← leftOffset_succ ring
          (ring.rightNeighbor e) (q + 1) hq,
        ← leftOffset_succ ring e q (by omega),
        ih (by omega)]




private theorem scanDistance_some_info
    {n : Nat}
    (site : Nat → Fin n)
    (hit : Fin n → Bool) :
    ∀ fuel start d,
      PPL.scanDistance site hit fuel start = some d →
      start ≤ d ∧
        d < start + fuel ∧
        hit (site d) = true ∧
        ∀ q, start ≤ q → q < d →
          hit (site q) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d h
      cases hh : hit (site start) with
      | true =>
          simp [PPL.scanDistance, hh] at h
          subst d
          refine ⟨Nat.le_refl _, by omega, hh, ?_⟩
          intro q hq0 hq1
          omega
      | false =>
          have hrec :
              PPL.scanDistance site hit fuel (start + 1) =
                some d := by
            simpa [PPL.scanDistance, hh] using h
          have hi := ih (start + 1) d hrec
          refine ⟨by omega, by omega, hi.2.2.1, ?_⟩
          intro q hq0 hqd
          by_cases hqs : q = start
          · subst q
            exact hh
          · exact hi.2.2.2 q (by omega) hqd




private theorem scanDistance_none_info
    {n : Nat}
    (site : Nat → Fin n)
    (hit : Fin n → Bool) :
    ∀ fuel start,
      PPL.scanDistance site hit fuel start = none →
      ∀ q, start ≤ q → q < start + fuel →
        hit (site q) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start h q hq0 hq1
      omega
  | succ fuel ih =>
      intro start h
      cases hh : hit (site start) with
      | true =>
          simp [PPL.scanDistance, hh] at h
      | false =>
          have hrec :
              PPL.scanDistance site hit fuel (start + 1) =
                none := by
            simpa [PPL.scanDistance, hh] using h
          intro q hq0 hq1
          by_cases hqs : q = start
          · subst q
            exact hh
          · exact ih (start + 1) hrec q
              (by omega) (by omega)




private theorem peaceScan_head
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n)
    (fuel d : Nat)
    (h : peaceScan ring D base (fuel + 1) d) :
    ScanHeadSafe (D (leftOffset ring base d)) := by
  change
    (D (leftOffset ring base d)).signalB = false ∧
      (if (D (leftOffset ring base d)).leader = true then
        (D (leftOffset ring base d)).shield = true
      else
        peaceScan ring D base fuel (d + 1)) at h
  refine ⟨h.1, ?_⟩
  intro hl
  simpa [hl] using h.2




private theorem peaceScan_tail
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n)
    (fuel d : Nat)
    (h : peaceScan ring D base (fuel + 1) d)
    (hl :
      (D (leftOffset ring base d)).leader = false) :
    peaceScan ring D base fuel (d + 1) := by
  change
    (D (leftOffset ring base d)).signalB = false ∧
      (if (D (leftOffset ring base d)).leader = true then
        (D (leftOffset ring base d)).shield = true
      else
        peaceScan ring D base fuel (d + 1)) at h
  simpa [hl] using h.2




private theorem peaceScan_of_first
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n) :
    ∀ fuel start d,
      start ≤ d →
      d < start + fuel →
      (∀ q, start ≤ q → q < d →
        (D (leftOffset ring base q)).leader = false) →
      (∀ q, start ≤ q → q ≤ d →
        (D (leftOffset ring base q)).signalB = false) →
      (D (leftOffset ring base d)).leader = true →
      (D (leftOffset ring base d)).shield = true →
      peaceScan ring D base fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d hsd hdf hleaders hsignals hleader hshield
      omega
  | succ fuel ih =>
      intro start d hsd hdf hleaders hsignals hleader hshield
      by_cases hEq : start = d
      · subst d
        change
          (D (leftOffset ring base start)).signalB = false ∧
            (if (D (leftOffset ring base start)).leader = true then
              (D (leftOffset ring base start)).shield = true
            else
              peaceScan ring D base fuel (start + 1))
        refine ⟨hsignals start (Nat.le_refl _) (Nat.le_refl _), ?_⟩
        simpa [hleader] using hshield
      · have hlt : start < d := by
          omega
        have hcurLeader :
            (D (leftOffset ring base start)).leader = false :=
          hleaders start (Nat.le_refl _) hlt
        have htail :=
          ih (start + 1) d
            (by omega) (by omega)
            (fun q hq0 hqd =>
              hleaders q (by omega) hqd)
            (fun q hq0 hqd =>
              hsignals q (by omega) hqd)
            hleader hshield
        change
          (D (leftOffset ring base start)).signalB = false ∧
            (if (D (leftOffset ring base start)).leader = true then
              (D (leftOffset ring base start)).shield = true
            else
              peaceScan ring D base fuel (start + 1))
        refine ⟨hsignals start (Nat.le_refl _) (by omega), ?_⟩
        simpa [hcurLeader] using htail




private theorem peaceScan_of_none
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n) :
    ∀ fuel start,
      (∀ q, start ≤ q → q < start + fuel →
        (D (leftOffset ring base q)).leader = false) →
      (∀ q, start ≤ q → q < start + fuel →
        (D (leftOffset ring base q)).signalB = false) →
      peaceScan ring D base fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hleaders hsignals
      trivial
  | succ fuel ih =>
      intro start hleaders hsignals
      have hl :
          (D (leftOffset ring base start)).leader = false :=
        hleaders start (Nat.le_refl _) (by omega)
      have hs :
          (D (leftOffset ring base start)).signalB = false :=
        hsignals start (Nat.le_refl _) (by omega)
      have ht :=
        ih (start + 1)
          (fun q hq0 hq1 =>
            hleaders q (by omega) (by omega))
          (fun q hq0 hq1 =>
            hsignals q (by omega) (by omega))
      change
        (D (leftOffset ring base start)).signalB = false ∧
          (if (D (leftOffset ring base start)).leader = true then
            (D (leftOffset ring base start)).shield = true
          else
            peaceScan ring D base fuel (start + 1))
      refine ⟨hs, ?_⟩
      simpa [hl] using ht




private theorem peaceScan_head_at
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n) :
    ∀ fuel start d,
      start ≤ d →
      d < start + fuel →
      peaceScan ring D base fuel start →
      (∀ q, start ≤ q → q < d →
        (D (leftOffset ring base q)).leader = false) →
      ScanHeadSafe (D (leftOffset ring base d)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d hsd hdf hscan hfollowers
      omega
  | succ fuel ih =>
      intro start d hsd hdf hscan hfollowers
      by_cases hEq : start = d
      · subst d
        exact peaceScan_head ring D base fuel start hscan
      · have hlt : start < d := by
          omega
        have hl :
            (D (leftOffset ring base start)).leader = false :=
          hfollowers start (Nat.le_refl _) hlt
        have htail :=
          peaceScan_tail ring D base fuel start hscan hl
        exact
          ih (start + 1) d
            (by omega) (by omega) htail
            (fun q hq0 hqd =>
              hfollowers q (by omega) hqd)




private theorem peaceful4_iff_scan
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (i : Fin n) :
    Peaceful4 ring D i ↔
      peaceScan ring D i n 0 := by
  constructor
  · intro hpeace
    unfold Peaceful4 PPL.PeacefulCore at hpeace
    cases hd :
        PPL.dLLBy ring
          (fun j => (D j).leader) i with
    | none =>
        rw [hd] at hpeace
        have hd0 :
            PPL.scanDistance
              (fun d => leftOffset ring i d)
              (fun j => (D j).leader) n 0 = none := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hnone :=
          scanDistance_none_info
            (fun d => leftOffset ring i d)
            (fun j => (D j).leader)
            n 0 hd0
        apply peaceScan_of_none ring D i n 0
        · intro q hq0 hqn
          exact hnone q hq0 hqn
        · intro q hq0 hqn
          exact hpeace (leftOffset ring i q)
    | some d =>
        rw [hd] at hpeace
        have hd0 :
            PPL.scanDistance
              (fun q => leftOffset ring i q)
              (fun j => (D j).leader) n 0 =
                some d := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hi :=
          scanDistance_some_info
            (fun q => leftOffset ring i q)
            (fun j => (D j).leader)
            n 0 d hd0
        apply
          peaceScan_of_first ring D i n 0 d
            (by omega) (by omega)
        · intro q hq0 hqd
          exact hi.2.2.2 q hq0 hqd
        · intro q hq0 hqd
          exact hpeace.2 ⟨q, by omega⟩
        · exact hi.2.2.1
        · exact hpeace.1
  · intro hscan
    unfold Peaceful4 PPL.PeacefulCore
    cases hd :
        PPL.dLLBy ring
          (fun j => (D j).leader) i with
    | none =>
        change ∀ k : Fin n, (D k).signalB = false
        have hd0 :
            PPL.scanDistance
              (fun d => leftOffset ring i d)
              (fun j => (D j).leader) n 0 = none := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hnone :=
          scanDistance_none_info
            (fun d => leftOffset ring i d)
            (fun j => (D j).leader)
            n 0 hd0
        intro k
        obtain ⟨d, hdn, hdk⟩ :=
          leftOffset_surjective ring i k
        have hhead :=
          peaceScan_head_at ring D i n 0 d
            (Nat.zero_le _) (by omega) hscan
            (fun q hq0 hqd =>
              hnone q hq0 (by omega))
        rw [hdk] at hhead
        exact hhead.1
    | some d =>
        change
          (D (leftOffset ring i d)).shield = true ∧
            ∀ q : Fin (d + 1),
              (D (leftOffset ring i q.val)).signalB = false
        have hd0 :
            PPL.scanDistance
              (fun q => leftOffset ring i q)
              (fun j => (D j).leader) n 0 =
                some d := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hi :=
          scanDistance_some_info
            (fun q => leftOffset ring i q)
            (fun j => (D j).leader)
            n 0 d hd0
        constructor
        · have hhead :=
            peaceScan_head_at ring D i n 0 d
              (Nat.zero_le _) hi.2.1 hscan
              (fun q hq0 hqd =>
                hi.2.2.2 q hq0 hqd)
          exact hhead.2 hi.2.2.1
        · intro q
          have hhead :=
            peaceScan_head_at ring D i n 0 q.val
              (Nat.zero_le _) (by omega) hscan
              (fun t ht0 htq =>
                hi.2.2.2 t ht0 (by omega))
          exact hhead.1




private theorem rowE_left_bullet_zero_scan
    (l r : Cell4) :
    (PPL.Elim.rowE l r).1.bullet =
      (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp [PPL.Elim.rowE]




private theorem rowE_left_scanFrame_scan
    (l r : Cell4)
    (hl : ScanHeadSafe l)
    (hrLeader : r.leader = false)
    (hrSignal : r.signalB = false) :
    ScanFrame l (PPL.Elim.rowE l r).1 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  constructor <;>
    simp_all [ScanHeadSafe, PPL.Elim.rowE]




private theorem rowE_left_live_scanFrame_scan
    (l r : Cell4)
    (hlive : l.bullet = (2 : Fin 3))
    (hl : ScanHeadSafe l)
    (hrLeader : r.leader = false) :
    ScanFrame l (PPL.Elim.rowE l r).1 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  constructor <;>
    simp_all [ScanHeadSafe, PPL.Elim.rowE]




private theorem rowE_right_scanFrame_scan
    (l r : Cell4)
    (hr : ScanHeadSafe r) :
    ScanFrame r (PPL.Elim.rowE l r).2 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  constructor <;>
    simp_all [ScanHeadSafe, PPL.Elim.rowE]




private theorem rowE_right_new_live_cases_scan
    (l r : Cell4)
    (hold : r.bullet ≠ (2 : Fin 3))
    (hout :
      (PPL.Elim.rowE l r).2.bullet =
        (2 : Fin 3)) :
    r.leader = false ∧
      (PPL.Elim.rowE l r).2.signalB = false ∧
      (l.bullet = (2 : Fin 3) ∨
        (l.leader = true ∧ l.signalB = true)) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]




private theorem rowE_fired_source_safe_scan
    (l r : Cell4)
    (hlLeader : l.leader = true)
    (hlSignal : l.signalB = true)
    (hrLeader : r.leader = false) :
    (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).1.leader = true ∧
      (PPL.Elim.rowE l r).1.shield = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]




private theorem rowE_right_deleted_origin_scan
    (l r : Cell4)
    (hrLeader : r.leader = true)
    (hout :
      (PPL.Elim.rowE l r).2.leader = false) :
    l.bullet = (2 : Fin 3) ∨
      (l.leader = true ∧ l.signalB = true) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]




private theorem rowE_right_survives_live_safe_scan
    (l r : Cell4)
    (hlive : l.bullet = (2 : Fin 3))
    (hrLeader : r.leader = true)
    (hrSignal : r.signalB = false)
    (hrShield : r.shield = true) :
    (PPL.Elim.rowE l r).2.leader = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  rcases fin3_cases_scan rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]




private theorem rowE_born_right_safe_scan
    (l : Cell4) :
    let r := (PPL.Elim.rowE l born4).2
    r.leader = true ∧
      r.bullet = (2 : Fin 3) ∧
      r.shield = true ∧
      r.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases fin3_cases_scan lb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  simp [born4, PPL.Elim.rowE]




private abbrev rowStep
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n) :
    Fin n → Cell4 :=
  PopulationProtocol.step PPL.Elim.protocolE ring D e




private theorem rowStep_source
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n) :
    rowStep ring D e e =
      (PPL.Elim.rowE
        (D e) (D (ring.rightNeighbor e))).1 := by
  simp [rowStep, PopulationProtocol.step,
    PPL.Elim.protocolE]




private theorem rowStep_responder
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (hne : e ≠ ring.rightNeighbor e) :
    rowStep ring D e (ring.rightNeighbor e) =
      (PPL.Elim.rowE
        (D e) (D (ring.rightNeighbor e))).2 := by
  simp [rowStep, PopulationProtocol.step,
    PPL.Elim.protocolE, hne, Ne.symm hne]




private theorem rowStep_other
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e k : Fin n)
    (hke : k ≠ e)
    (hkr : k ≠ ring.rightNeighbor e) :
    rowStep ring D e k = D k := by
  simp [rowStep, PopulationProtocol.step,
    PPL.Elim.protocolE, hke, hkr]




private theorem rowStep_leader_eq_ne_responder
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e k : Fin n)
    (hk : k ≠ ring.rightNeighbor e) :
    (rowStep ring D e k).leader =
      (D k).leader := by
  by_cases hke : k = e
  · subst k
    rw [rowStep_source, PPL.Elim.rowE_left_leader]
  · rw [rowStep_other ring D e k hke hk]




private theorem rowStep_scanFrame_ne_source
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4)
    (e x : Fin n)
    (hx : x ≠ e)
    (h : ScanHeadSafe (D x)) :
    ScanFrame (D x) (rowStep ring D e x) := by
  let j := ring.rightNeighbor e
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  by_cases hxj : x = j
  · subst x
    rw [rowStep_responder ring D e hne]
    exact rowE_right_scanFrame_scan (D e) (D j) h
  · rw [rowStep_other ring D e x hx
      (by simpa [j] using hxj)]
    exact ⟨h.1, rfl, h.2⟩




private theorem rowStep_scanFrame_source_live
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (hlive : (D e).bullet = (2 : Fin 3))
    (h : ScanHeadSafe (D e))
    (hrLeader :
      (D (ring.rightNeighbor e)).leader = false) :
    ScanFrame (D e) (rowStep ring D e e) := by
  rw [rowStep_source]
  exact
    rowE_left_live_scanFrame_scan
      (D e) (D (ring.rightNeighbor e))
      hlive h hrLeader




private theorem rowStep_scanFrame_source
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (h : ScanHeadSafe (D e))
    (hrLeader :
      (D (ring.rightNeighbor e)).leader = false)
    (hrSignal :
      (D (ring.rightNeighbor e)).signalB = false) :
    ScanFrame (D e) (rowStep ring D e e) := by
  rw [rowStep_source]
  exact
    rowE_left_scanFrame_scan
      (D e) (D (ring.rightNeighbor e))
      h hrLeader hrSignal




private theorem peaceScan_preserve_with_right_any
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e base : Fin n) :
    ∀ fuel d,
      peaceScan ring D base fuel d →
      (D (ring.rightNeighbor
        (leftOffset ring base d))).leader = false →
      (D (ring.rightNeighbor
        (leftOffset ring base d))).signalB = false →
      peaceScan ring (rowStep ring D e) base fuel d := by
  intro fuel
  induction fuel with
  | zero =>
      intro d hscan hrL hrS
      trivial
  | succ fuel ih =>
      intro d hscan hrL hrS
      let x := leftOffset ring base d
      have hhead :=
        peaceScan_head ring D base fuel d hscan
      have hframe :
          ScanFrame (D x) (rowStep ring D e x) := by
        by_cases hxe : x = e
        · have hxd :
              leftOffset ring base d = e := by
            simpa [x] using hxe
          have hheadE : ScanHeadSafe (D e) := by
            simpa [hxd] using hhead
          have hrLE :
              (D (ring.rightNeighbor e)).leader = false := by
            simpa [hxd] using hrL
          have hrSE :
              (D (ring.rightNeighbor e)).signalB = false := by
            simpa [hxd] using hrS
          have hs :=
            rowStep_scanFrame_source
              ring D e hheadE hrLE hrSE
          simpa [x, hxd] using hs
        · exact
            rowStep_scanFrame_ne_source
              hn2 ring D e x hxe hhead
      change
        (rowStep ring D e x).signalB = false ∧
          (if (rowStep ring D e x).leader = true then
            (rowStep ring D e x).shield = true
          else
            peaceScan ring (rowStep ring D e)
              base fuel (d + 1))
      refine ⟨hframe.signalB, ?_⟩
      cases hl : (D x).leader with
      | true =>
          have hnew :
              (rowStep ring D e x).leader = true := by
            rw [hframe.leader, hl]
          simpa [hnew] using hframe.shield hl
      | false =>
          have hnew :
              (rowStep ring D e x).leader = false := by
            rw [hframe.leader, hl]
          have htail :=
            peaceScan_tail ring D base fuel d hscan hl
          cases fuel with
          | zero =>
              simpa [hnew, peaceScan] using htail
          | succ fuel =>
              have hoff :
                  ring.leftNeighbor x =
                    leftOffset ring base (d + 1) := by
                dsimp [x]
                exact
                  leftOffset_succ_all
                    ring hn2 base d
              have hrl :
                  ring.rightNeighbor
                      (leftOffset ring base (d + 1)) = x := by
                rw [← hoff,
                  rightNeighbor_leftNeighbor_scan]
              have hnextL :
                  (D (ring.rightNeighbor
                    (leftOffset ring base (d + 1)))).leader =
                    false := by
                rw [hrl]
                exact hl
              have hnextS :
                  (D (ring.rightNeighbor
                    (leftOffset ring base (d + 1)))).signalB =
                    false := by
                rw [hrl]
                exact hhead.1
              have htail' :=
                ih (d + 1) htail hnextL hnextS
              simpa [hnew] using htail'




private theorem peaceScan_preserve_with_right
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e base : Fin n) :
    ∀ fuel d,
      d + fuel ≤ n →
      peaceScan ring D base fuel d →
      (D (ring.rightNeighbor
        (leftOffset ring base d))).leader = false →
      (D (ring.rightNeighbor
        (leftOffset ring base d))).signalB = false →
      peaceScan ring (rowStep ring D e) base fuel d := by
  intro fuel d hbound hscan hrL hrS
  exact
    peaceScan_preserve_with_right_any
      hn2 ring D e base fuel d hscan hrL hrS




private theorem peaceScan_preserve_ne_current
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4)
    (e base : Fin n) :
    ∀ fuel d,
      d + fuel ≤ n →
      leftOffset ring base d ≠ e →
      peaceScan ring D base fuel d →
      peaceScan ring (rowStep ring D e) base fuel d := by
  intro fuel
  induction fuel with
  | zero =>
      intro d hbound hne hscan
      trivial
  | succ fuel ih =>
      intro d hbound hne hscan
      let x := leftOffset ring base d
      have hhead :=
        peaceScan_head ring D base fuel d hscan
      have hframe :=
        rowStep_scanFrame_ne_source
          hn2 ring D e x hne hhead
      change
        (rowStep ring D e x).signalB = false ∧
          (if (rowStep ring D e x).leader = true then
            (rowStep ring D e x).shield = true
          else
            peaceScan ring (rowStep ring D e)
              base fuel (d + 1))
      refine ⟨hframe.signalB, ?_⟩
      cases hl : (D x).leader with
      | true =>
          have hnew :
              (rowStep ring D e x).leader = true := by
            rw [hframe.leader, hl]
          simpa [hnew] using hframe.shield hl
      | false =>
          have hnew :
              (rowStep ring D e x).leader = false := by
            rw [hframe.leader, hl]
          have htail :=
            peaceScan_tail ring D base fuel d hscan hl
          cases fuel with
          | zero =>
              simpa [hnew, peaceScan] using htail
          | succ fuel =>
              have hoff :
                  ring.leftNeighbor x =
                    leftOffset ring base (d + 1) := by
                dsimp [x]
                exact leftOffset_succ ring base d (by omega)
              have hrl :
                  ring.rightNeighbor
                      (leftOffset ring base (d + 1)) = x := by
                rw [← hoff,
                  rightNeighbor_leftNeighbor_scan]
              have hnextL :
                  (D (ring.rightNeighbor
                    (leftOffset ring base (d + 1)))).leader =
                    false := by
                rw [hrl]
                exact hl
              have hnextS :
                  (D (ring.rightNeighbor
                    (leftOffset ring base (d + 1)))).signalB =
                    false := by
                rw [hrl]
                exact hhead.1
              have htail' :=
                peaceScan_preserve_with_right
                  hn2 ring D e base
                  (fuel + 1) (d + 1)
                  (by omega) htail hnextL hnextS
              simpa [hnew] using htail'




private theorem peaceScan_preserve_source_live
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (fuel : Nat) (hfuel : 0 < fuel)
    (hscan : peaceScan ring D e fuel 0)
    (hlive : (D e).bullet = (2 : Fin 3))
    (hrLeader :
      (D (ring.rightNeighbor e)).leader = false) :
    peaceScan ring (rowStep ring D e) e fuel 0 := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      have hhead :=
        peaceScan_head ring D e fuel 0 hscan
      have hframe :=
        rowStep_scanFrame_source_live
          ring D e hlive
          (by simpa [leftOffset_zero] using hhead)
          hrLeader
      have hx0 :
          leftOffset ring e 0 = e :=
        leftOffset_zero ring e
      change
        (rowStep ring D e
          (leftOffset ring e 0)).signalB = false ∧
          (if
            (rowStep ring D e
              (leftOffset ring e 0)).leader = true
          then
            (rowStep ring D e
              (leftOffset ring e 0)).shield = true
          else
            peaceScan ring (rowStep ring D e)
              e fuel 1)
      rw [hx0]
      refine ⟨hframe.signalB, ?_⟩
      cases hl : (D e).leader with
      | true =>
          have hnew :
              (rowStep ring D e e).leader = true := by
            rw [hframe.leader, hl]
          simpa [hnew] using hframe.shield hl
      | false =>
          have hnew :
              (rowStep ring D e e).leader = false := by
            rw [hframe.leader, hl]
          have htail :=
            peaceScan_tail ring D e fuel 0 hscan
              (by simpa [leftOffset_zero] using hl)
          cases fuel with
          | zero =>
              simpa [hnew, peaceScan] using htail
          | succ fuel =>
              have hoff :
                  ring.leftNeighbor e =
                    leftOffset ring e 1 := by
                simpa [leftOffset_zero] using
                  leftOffset_succ ring e 0 (by omega)
              have hrl :
                  ring.rightNeighbor
                      (leftOffset ring e 1) = e := by
                rw [← hoff,
                  rightNeighbor_leftNeighbor_scan]
              have hnextL :
                  (D (ring.rightNeighbor
                    (leftOffset ring e 1))).leader = false := by
                rw [hrl]
                exact hl
              have hnextS :
                  (D (ring.rightNeighbor
                    (leftOffset ring e 1))).signalB = false := by
                rw [hrl]
                simpa [leftOffset_zero] using hhead.1
              have htail' :=
                peaceScan_preserve_with_right_any
                  hn2 ring D e e
                  (fuel + 1) 1
                  htail hnextL hnextS
              simpa [hnew] using htail'




private theorem peaceScan_drop_one
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n) :
    ∀ fuel d,
      peaceScan ring D base (fuel + 1) d →
      peaceScan ring D base fuel d := by
  intro fuel
  induction fuel with
  | zero =>
      intro d h
      trivial
  | succ fuel ih =>
      intro d h
      have hhead :=
        peaceScan_head ring D base (fuel + 1) d h
      change
        (D (leftOffset ring base d)).signalB = false ∧
          (if (D (leftOffset ring base d)).leader = true then
            (D (leftOffset ring base d)).shield = true
          else
            peaceScan ring D base fuel (d + 1))
      refine ⟨hhead.1, ?_⟩
      cases hl :
          (D (leftOffset ring base d)).leader with
      | true =>
          simpa [hl] using hhead.2 hl
      | false =>
          have htail :=
            peaceScan_tail ring D base
              (fuel + 1) d h hl
          have htail' := ih (d + 1) htail
          simpa [hl] using htail'




private theorem peaceScan_safe_leader
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4) (base : Fin n)
    (fuel d : Nat) (hfuel : 0 < fuel)
    (hs :
      (D (leftOffset ring base d)).signalB = false)
    (hl :
      (D (leftOffset ring base d)).leader = true)
    (hh :
      (D (leftOffset ring base d)).shield = true) :
    peaceScan ring D base fuel d := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      change
        (D (leftOffset ring base d)).signalB = false ∧
          (if (D (leftOffset ring base d)).leader = true then
            (D (leftOffset ring base d)).shield = true
          else
            peaceScan ring D base fuel (d + 1))
      exact ⟨hs, by simpa [hl] using hh⟩




private theorem peaceScan_rebase_right
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n) :
    ∀ fuel q,
      q + fuel < n →
      (peaceScan ring D e fuel q ↔
        peaceScan ring D (ring.rightNeighbor e)
          fuel (q + 1)) := by
  intro fuel q
  induction fuel generalizing q with
  | zero =>
      intro hbound
      simp [peaceScan]
  | succ fuel ih =>
      intro hbound
      have hoff :=
        leftOffset_rightNeighbor_succ
          ring hn2 e q (by omega)
      simp only [peaceScan]
      rw [hoff]
      by_cases hl :
          (D (leftOffset ring e q)).leader = true
      · simp [hl]
      · have ht := ih (q + 1) (by omega)
        simp [hl, ht]




private theorem peaceScan_responder_of_tail
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (hjSignal :
      (D (ring.rightNeighbor e)).signalB = false)
    (hjLeader :
      (D (ring.rightNeighbor e)).leader = false)
    (htail :
      peaceScan ring D e (n - 1) 0) :
    peaceScan ring D (ring.rightNeighbor e) n 0 := by
  have hreb0 :=
    peaceScan_rebase_right
      hn2 ring D e (n - 1) 0
  have hreb :=
    (hreb0 (by omega)).1 htail
  rw [show peaceScan ring D (ring.rightNeighbor e) n 0 =
      peaceScan ring D (ring.rightNeighbor e) ((n - 1) + 1) 0 by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]]
  change
    (D (leftOffset ring
      (ring.rightNeighbor e) 0)).signalB = false ∧
      (if
        (D (leftOffset ring
          (ring.rightNeighbor e) 0)).leader = true
      then
        (D (leftOffset ring
          (ring.rightNeighbor e) 0)).shield = true
      else
        peaceScan ring D
          (ring.rightNeighbor e) (n - 1) 1)
  rw [leftOffset_zero]
  refine ⟨hjSignal, ?_⟩
  simpa [hjLeader] using hreb




private theorem peaceful4_of_safe_leader
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (i : Fin n)
    (hs : (D i).signalB = false)
    (hl : (D i).leader = true)
    (hh : (D i).shield = true) :
    Peaceful4 ring D i := by
  apply (peaceful4_iff_scan hn2 ring D i).2
  have hz : leftOffset ring i 0 = i :=
    leftOffset_zero ring i
  exact
    peaceScan_safe_leader
      ring D i n 0 ring.hn
      (by simpa [hz] using hs)
      (by simpa [hz] using hl)
      (by simpa [hz] using hh)




private theorem peaceScan_unique_right_safe
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (hscan : peaceScan ring D e n 0)
    (honly :
      ∀ k : Fin n, (D k).leader = true →
        k = ring.rightNeighbor e)
    (hrLeader :
      (D (ring.rightNeighbor e)).leader = true) :
    (D (ring.rightNeighbor e)).signalB = false ∧
      (D (ring.rightNeighbor e)).shield = true := by
  have hfollowers :
      ∀ q : Nat, q < n - 1 →
        (D (leftOffset ring e q)).leader = false := by
    intro q hq
    cases hl :
        (D (leftOffset ring e q)).leader with
    | false =>
        rfl
    | true =>
        have heq :=
          honly (leftOffset ring e q) hl
        exact False.elim
          ((leftOffset_ne_rightNeighbor_of_lt
            ring hn2 e q hq) heq)
  have hhead :=
    peaceScan_head_at ring D e n 0 (n - 1)
      (Nat.zero_le _) (by omega) hscan
      (fun q hq0 hq1 =>
        hfollowers q (by omega))
  rw [leftOffset_last ring hn2 e] at hhead
  exact ⟨hhead.1, hhead.2 hrLeader⟩




private theorem pure_leader_survival
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n)
    (hPB : PB4 ring D) :
    ∃ i : Fin n,
      (rowStep ring D e i).leader = true := by
  unfold PB4 PPL.CPBCore at hPB
  rcases hPB with ⟨hex, hpeace⟩
  let j := ring.rightNeighbor e
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  obtain ⟨root, hroot⟩ := hex
  by_cases hrj : root = j
  · subst root
    by_cases hother :
        ∃ k : Fin n, k ≠ j ∧ (D k).leader = true
    · obtain ⟨k, hkj, hk⟩ := hother
      refine ⟨k, ?_⟩
      have heq :=
        rowStep_leader_eq_ne_responder
          ring D e k hkj
      rw [heq]
      exact hk
    · have honly :
          ∀ k : Fin n, (D k).leader = true → k = j := by
        intro k hk
        by_cases hkj : k = j
        · exact hkj
        · exact False.elim (hother ⟨k, hkj, hk⟩)
      have hjSurvives :
          (rowStep ring D e j).leader = true := by
        cases hout :
            (rowStep ring D e j).leader with
        | true =>
            rfl
        | false =>
            have hrowOut :
                (PPL.Elim.rowE (D e) (D j)).2.leader =
                  false := by
              rw [rowStep_responder ring D e hne] at hout
              exact hout
            have horigin :=
              rowE_right_deleted_origin_scan
                (D e) (D j) hroot hrowOut
            rcases horigin with hlive | hfire
            · have hpeaceE := hpeace e hlive
              have hscan :=
                (peaceful4_iff_scan
                  hn2 ring D e).1 hpeaceE
              have hsafe :=
                peaceScan_unique_right_safe
                  hn2 ring D e hscan honly hroot
              have hsurvive :=
                rowE_right_survives_live_safe_scan
                  (D e) (D j) hlive
                  hroot hsafe.1 hsafe.2
              rw [hsurvive] at hrowOut
              contradiction
            · have heq := honly e hfire.1
              exact False.elim (hne heq)
      exact ⟨j, hjSurvives⟩
  · refine ⟨root, ?_⟩
    have heq :=
      rowStep_leader_eq_ne_responder
        ring D e root
        (by simpa [j] using hrj)
    rw [heq]
    exact hroot




private theorem pure_new_live_peaceful
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e i : Fin n)
    (hpost :
      (rowStep ring D e i).bullet = (2 : Fin 3))
    (hold : (D i).bullet ≠ (2 : Fin 3))
    (hnot :
      i ≠ ring.rightNeighbor e ∨
        (D e).bullet ≠ (2 : Fin 3)) :
    Peaceful4 ring (rowStep ring D e) i := by
  let j := ring.rightNeighbor e
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  by_cases hie : i = e
  · subst i
    have hz :
        (rowStep ring D e e).bullet =
          (0 : Fin 3) := by
      rw [rowStep_source]
      exact
        rowE_left_bullet_zero_scan
          (D e) (D (ring.rightNeighbor e))
    rw [hz] at hpost
    have hv := congrArg Fin.val hpost
    simp at hv
  · by_cases hij : i = j
    · subst i
      have hrowLive :
          (PPL.Elim.rowE (D e) (D j)).2.bullet =
            (2 : Fin 3) := by
        rw [rowStep_responder ring D e hne] at hpost
        exact hpost
      have hinfo :=
        rowE_right_new_live_cases_scan
          (D e) (D j) hold hrowLive
      rcases hinfo with
        ⟨hrFollower, hrSignal, horigin⟩
      have hsrcNot :
          (D e).bullet ≠ (2 : Fin 3) := by
        rcases hnot with hbad | hsrc
        · exact False.elim (hbad rfl)
        · exact hsrc
      rcases horigin with hsrc | hfire
      · exact False.elim (hsrcNot hsrc)
      · have hfields :=
          rowE_fired_source_safe_scan
            (D e) (D j)
            hfire.1 hfire.2 hrFollower
        have hsource := rowStep_source ring D e
        have hs :
            (rowStep ring D e e).signalB = false := by
          rw [hsource]
          exact hfields.1
        have hl :
            (rowStep ring D e e).leader = true := by
          rw [hsource]
          exact hfields.2.1
        have hh :
            (rowStep ring D e e).shield = true := by
          rw [hsource]
          exact hfields.2.2
        have htail :
            peaceScan ring (rowStep ring D e)
              e (n - 1) 0 := by
          have hz :
              leftOffset ring e 0 = e :=
            leftOffset_zero ring e
          exact
            peaceScan_safe_leader
              ring (rowStep ring D e) e
              (n - 1) 0 (by omega)
              (by simpa [hz] using hs)
              (by simpa [hz] using hl)
              (by simpa [hz] using hh)
        have hjStep :=
          rowStep_responder ring D e hne
        have hjSignal :
            (rowStep ring D e j).signalB = false := by
          rw [hjStep]
          exact hrSignal
        have hjLeader :
            (rowStep ring D e j).leader = false := by
          rw [hjStep]
          exact
            PPL.Elim.rowE_right_leader_false_of_false
              (D e) (D j) hrFollower
        apply
          (peaceful4_iff_scan
            hn2 ring (rowStep ring D e) j).2
        simpa [j] using
          peaceScan_responder_of_tail
            hn2 ring (rowStep ring D e)
            e hjSignal hjLeader htail
    · have hsame :=
        rowStep_other ring D e i hie
          (by simpa [j] using hij)
      rw [hsame] at hpost
      exact False.elim (hold hpost)




private theorem pure_keep_live_peaceful
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e i : Fin n)
    (hlive : (D i).bullet = (2 : Fin 3))
    (hpeace : Peaceful4 ring D i) :
    ((rowStep ring D e i).bullet = (2 : Fin 3) →
      Peaceful4 ring (rowStep ring D e) i) ∧
    (i = e →
      (rowStep ring D e
        (ring.rightNeighbor e)).bullet = (2 : Fin 3) →
      (D (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3) →
      Peaceful4 ring (rowStep ring D e)
        (ring.rightNeighbor e)) := by
  constructor
  · intro hpost
    by_cases hie : i = e
    · subst i
      have hz :
          (rowStep ring D e e).bullet =
            (0 : Fin 3) := by
        rw [rowStep_source]
        exact
          rowE_left_bullet_zero_scan
            (D e) (D (ring.rightNeighbor e))
      rw [hz] at hpost
      have hv := congrArg Fin.val hpost
      simp at hv
    · have hscan :=
        (peaceful4_iff_scan hn2 ring D i).1 hpeace
      have hzero :
          leftOffset ring i 0 = i :=
        leftOffset_zero ring i
      have hscan' :=
        peaceScan_preserve_ne_current
          hn2 ring D e i n 0
          (by omega)
          (by simpa [hzero] using hie)
          hscan
      exact
        (peaceful4_iff_scan
          hn2 ring (rowStep ring D e) i).2 hscan'
  · intro hie hpost hold
    subst i
    let j := ring.rightNeighbor e
    have hne : e ≠ j :=
      (rightNeighbor_ne_self_scan ring hn2 e).symm
    have hrowLive :
        (PPL.Elim.rowE (D e) (D j)).2.bullet =
          (2 : Fin 3) := by
      rw [rowStep_responder ring D e hne] at hpost
      simpa [j] using hpost
    have hinfo :=
      rowE_right_new_live_cases_scan
        (D e) (D j)
        (by simpa [j] using hold)
        hrowLive
    rcases hinfo with
      ⟨hrFollower, hrSignal, horigin⟩
    have hscan :=
      (peaceful4_iff_scan hn2 ring D e).1 hpeace
    have hnform : n = (n - 1) + 1 := by
      omega
    have hfull :
        peaceScan ring D e ((n - 1) + 1) 0 := by
      rw [← hnform]
      exact hscan
    have hshort :=
      peaceScan_drop_one ring D e (n - 1) 0 hfull
    have htail :=
      peaceScan_preserve_source_live
        hn2 ring D e (n - 1) (by omega)
        hshort hlive hrFollower
    have hjStep :=
      rowStep_responder ring D e hne
    have hjSignal :
        (rowStep ring D e j).signalB = false := by
      rw [hjStep]
      exact hrSignal
    have hjLeader :
        (rowStep ring D e j).leader = false := by
      rw [hjStep]
      exact
        PPL.Elim.rowE_right_leader_false_of_false
          (D e) (D j) hrFollower
    apply
      (peaceful4_iff_scan
        hn2 ring (rowStep ring D e) j).2
    simpa [j] using
      peaceScan_responder_of_tail
        hn2 ring (rowStep ring D e)
        e hjSignal hjLeader htail




private def bornOverwrite
    {n : Nat} (D : Fin n → Cell4)
    (j : Fin n) : Fin n → Cell4 :=
  fun k => if k = j then born4 else D k




private theorem peaceScan_bornOverwrite
    {n : Nat} (ring : DirectedRing n)
    (D : Fin n → Cell4)
    (j base : Fin n) :
    ∀ fuel d,
      peaceScan ring D base fuel d →
      peaceScan ring (bornOverwrite D j) base fuel d := by
  intro fuel
  induction fuel with
  | zero =>
      intro d h
      trivial
  | succ fuel ih =>
      intro d h
      let x := leftOffset ring base d
      by_cases hx : x = j
      · change
          (bornOverwrite D j x).signalB = false ∧
            (if (bornOverwrite D j x).leader = true then
              (bornOverwrite D j x).shield = true
            else
              peaceScan ring (bornOverwrite D j)
                base fuel (d + 1))
        simp [bornOverwrite, hx, born4]
      · have hhead :=
          peaceScan_head ring D base fuel d h
        change
          (bornOverwrite D j x).signalB = false ∧
            (if (bornOverwrite D j x).leader = true then
              (bornOverwrite D j x).shield = true
            else
              peaceScan ring (bornOverwrite D j)
                base fuel (d + 1))
        have hsame :
            bornOverwrite D j x = D x := by
          simp [bornOverwrite, hx]
        rw [hsame]
        refine ⟨hhead.1, ?_⟩
        cases hl : (D x).leader with
        | true =>
            simpa [hl] using hhead.2 hl
        | false =>
            have htail :=
              peaceScan_tail ring D base fuel d h hl
            have htail' := ih (d + 1) htail
            simpa [hl] using htail'




private theorem noBirth_eq_rowStep
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n)
    (hother :
      ∀ k : Fin n,
        k ≠ e →
        k ≠ ring.rightNeighbor e →
        D' k = D k)
    (he :
      D' e =
        (PPL.Elim.rowE
          (D e) (D (ring.rightNeighbor e))).1)
    (hj :
      D' (ring.rightNeighbor e) =
        (PPL.Elim.rowE
          (D e) (D (ring.rightNeighbor e))).2) :
    D' = rowStep ring D e := by
  funext k
  by_cases hke : k = e
  · subst k
    rw [he, rowStep_source]
  · by_cases hkj : k = ring.rightNeighbor e
    · subst k
      rw [hj,
        rowStep_responder ring D e
          ((rightNeighbor_ne_self_scan
            ring hn2 e).symm)]
    · rw [hother k hke hkj,
      rowStep_other ring D e k hke hkj]




private theorem birth_eq_rowStep
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n)
    (hother :
      ∀ k : Fin n,
        k ≠ e →
        k ≠ ring.rightNeighbor e →
        D' k = D k)
    (he :
      D' e =
        (PPL.Elim.rowE (D e) born4).1)
    (hj :
      D' (ring.rightNeighbor e) =
        (PPL.Elim.rowE (D e) born4).2) :
    D' =
      rowStep ring
        (bornOverwrite D (ring.rightNeighbor e)) e := by
  let j := ring.rightNeighbor e
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  funext k
  by_cases hke : k = e
  · subst k
    rw [he, rowStep_source]
    simp [bornOverwrite, j, hne, Ne.symm hne]
  · by_cases hkj : k = j
    · subst k
      rw [hj,
        rowStep_responder
          ring (bornOverwrite D j) e hne]
      simp [bornOverwrite, j, hne, Ne.symm hne]
    · rw [rowStep_other
        ring (bornOverwrite D j) e k hke
        (by simpa [j] using hkj)]
      rw [hother k hke (by simpa [j] using hkj)]
      simp [bornOverwrite, hkj]




private theorem birth_leader_survival
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e : Fin n) :
    ∃ i : Fin n,
      (rowStep ring
        (bornOverwrite D (ring.rightNeighbor e)) e i).leader =
          true := by
  let j := ring.rightNeighbor e
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  refine ⟨j, ?_⟩
  rw [rowStep_responder
    ring (bornOverwrite D j) e hne]
  have hs := rowE_born_right_safe_scan (D e)
  simpa [bornOverwrite, j, hne, Ne.symm hne]
    using hs.1




private theorem birth_new_live_peaceful
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e i : Fin n)
    (hpost :
      (rowStep ring
        (bornOverwrite D (ring.rightNeighbor e)) e i).bullet =
          (2 : Fin 3))
    (hold : (D i).bullet ≠ (2 : Fin 3)) :
    Peaceful4 ring
      (rowStep ring
        (bornOverwrite D (ring.rightNeighbor e)) e) i := by
  let j := ring.rightNeighbor e
  let B := bornOverwrite D j
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  by_cases hie : i = e
  · subst i
    have hz :
        (rowStep ring B e e).bullet =
          (0 : Fin 3) := by
      rw [rowStep_source]
      exact
        rowE_left_bullet_zero_scan
          (B e) (B j)
    rw [hz] at hpost
    have hv := congrArg Fin.val hpost
    simp at hv
  · by_cases hij : i = j
    · subst i
      have hs := rowE_born_right_safe_scan (D e)
      have hstep :=
        rowStep_responder ring B e hne
      have hLeader :
          (rowStep ring B e j).leader = true := by
        rw [hstep]
        simpa [B, bornOverwrite, j, hne, Ne.symm hne]
          using hs.1
      have hShield :
          (rowStep ring B e j).shield = true := by
        rw [hstep]
        simpa [B, bornOverwrite, j, hne, Ne.symm hne]
          using hs.2.2.1
      have hSignal :
          (rowStep ring B e j).signalB = false := by
        rw [hstep]
        simpa [B, bornOverwrite, j, hne, Ne.symm hne]
          using hs.2.2.2
      exact
        peaceful4_of_safe_leader
          hn2 ring (rowStep ring B e) j
          hSignal hLeader hShield
    · have hsame :=
        rowStep_other ring B e i hie
          (by simpa [j] using hij)
      have hBi : B i = D i := by
        simp [B, bornOverwrite, hij]
      rw [hsame, hBi] at hpost
      exact False.elim (hold hpost)




private theorem birth_keep_live_peaceful
    {n : Nat} (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (D : Fin n → Cell4) (e i : Fin n)
    (hlive : (D i).bullet = (2 : Fin 3))
    (hpeace : Peaceful4 ring D i) :
    ((rowStep ring
        (bornOverwrite D (ring.rightNeighbor e)) e i).bullet =
          (2 : Fin 3) →
      Peaceful4 ring
        (rowStep ring
          (bornOverwrite D (ring.rightNeighbor e)) e) i) ∧
    (i = e →
      (rowStep ring
        (bornOverwrite D (ring.rightNeighbor e)) e
        (ring.rightNeighbor e)).bullet =
          (2 : Fin 3) →
      (D (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3) →
      Peaceful4 ring
        (rowStep ring
          (bornOverwrite D (ring.rightNeighbor e)) e)
        (ring.rightNeighbor e)) := by
  let j := ring.rightNeighbor e
  let B := bornOverwrite D j
  have hne : e ≠ j :=
    (rightNeighbor_ne_self_scan ring hn2 e).symm
  constructor
  · intro hpost
    by_cases hie : i = e
    · subst i
      have hz :
          (rowStep ring B e e).bullet =
            (0 : Fin 3) := by
        rw [rowStep_source]
        exact
          rowE_left_bullet_zero_scan
            (B e) (B j)
      rw [hz] at hpost
      have hv := congrArg Fin.val hpost
      simp at hv
    · have hpeaceB : Peaceful4 ring B i := by
        by_cases hij : i = j
        · subst i
          exact
            peaceful4_of_safe_leader
              hn2 ring B j
              (by simp [B, bornOverwrite, born4])
              (by simp [B, bornOverwrite, born4])
              (by simp [B, bornOverwrite, born4])
        · have hscan :=
            (peaceful4_iff_scan
              hn2 ring D i).1 hpeace
          have hscanB :=
            peaceScan_bornOverwrite
              ring D j i n 0 hscan
          exact
            (peaceful4_iff_scan
              hn2 ring B i).2
              (by simpa [B] using hscanB)
      have hscanB :=
        (peaceful4_iff_scan
          hn2 ring B i).1 hpeaceB
      have hzero :
          leftOffset ring i 0 = i :=
        leftOffset_zero ring i
      have hscan' :=
        peaceScan_preserve_ne_current
          hn2 ring B e i n 0
          (by omega)
          (by simpa [hzero] using hie)
          hscanB
      exact
        (peaceful4_iff_scan
          hn2 ring (rowStep ring B e) i).2 hscan'
  · intro hie hpost hold
    subst i
    have hs := rowE_born_right_safe_scan (D e)
    have hstep :=
      rowStep_responder ring B e hne
    have hLeader :
        (rowStep ring B e j).leader = true := by
      rw [hstep]
      simpa [B, bornOverwrite, j, hne, Ne.symm hne]
        using hs.1
    have hShield :
        (rowStep ring B e j).shield = true := by
      rw [hstep]
      simpa [B, bornOverwrite, j, hne, Ne.symm hne]
        using hs.2.2.1
    have hSignal :
        (rowStep ring B e j).signalB = false := by
      rw [hstep]
      simpa [B, bornOverwrite, j, hne, Ne.symm hne]
        using hs.2.2.2
    simpa [j] using
      peaceful4_of_safe_leader
        hn2 ring (rowStep ring B e) j
        hSignal hLeader hShield




theorem peacefulScanLocality :
    PeacefulScanLocalityProp := by
  intro n hn3 ring D D' e hcase
  have hn2 : 2 ≤ n := by
    omega
  unfold FourFieldStepCase at hcase
  rcases hcase with ⟨hother, hpair⟩
  rcases hpair with hrow | hbirth
  · rcases hrow with ⟨he, hj⟩
    have hEq :=
      noBirth_eq_rowStep
        hn2 ring D D' e hother he hj
    subst D'
    refine ⟨?_, ?_, ?_⟩
    · exact pure_leader_survival hn2 ring D e
    · intro i hpost hold hnot
      exact
        pure_new_live_peaceful
          hn2 ring D e i hpost hold hnot
    · intro i hlive hpeace
      exact
        pure_keep_live_peaceful
          hn2 ring D e i hlive hpeace
  · rcases hbirth with ⟨he, hj⟩
    have hEq :=
      birth_eq_rowStep
        hn2 ring D D' e hother he hj
    subst D'
    refine ⟨?_, ?_, ?_⟩
    · intro hPB
      exact birth_leader_survival hn2 ring D e
    · intro i hpost hold hnot
      exact
        birth_new_live_peaceful
          hn2 ring D e i hpost hold
    · intro i hlive hpeace
      exact
        birth_keep_live_peaceful
          hn2 ring D e i hlive hpeace




theorem cpb_step_closed_proved
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : CPB ring C) :
    CPB ring
      (PopulationProtocol.step
        (PPL.protocol psi kappa) ring C e) := by
  exact
    cpb_step_closed_uncond
      peacefulScanLocality
      hn3 hpsi ring C e hC




end PPL.Safety.PeacefulProps




#print axioms PPL.Safety.PeacefulProps.peacefulScanLocality
#print axioms PPL.Safety.PeacefulProps.cpb_step_closed_proved






