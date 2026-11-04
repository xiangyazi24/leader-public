import Leader.L3.Base

/-!
# The BANK pair on a nonroot source, mode rows separated from token rows

`bankPair` (Base.lean) is one `Id.run do` block: it resets modes and leases, runs the root rows
(source PACK 0), the responder's grant/ARMED/wait rows, and the token rows. A lemma about one
field of the result that unfolds `bankPair` with abstract cells makes `simp` carry every row
through every case.

On a nonroot source (`x0.role ≠ 0`) the root rows never run, the source ends in RESET with lease 0,
and the responder's mode and lease depend only on its own mode, lease, grant and the PACK change
(`bankPairModeY`), while the bits and tokens of both ends depend only on roles, bits, tokens,
`b` and `theta` (`bankPairNR`, the token rows of `bankPair` verbatim without the mode and lease
writes). `bankPair_nonroot` states this once, at variables; consumers rewrite with it and unfold
only the part their statement reads.
-/

namespace L3

set_option autoImplicit false

/-- The bit and token rows of `bankPair` on a nonroot source: the text of `bankPair` without the
mode and lease writes, the root rows and the responder's grant/ARMED/wait rows (none of which
writes a bit or a token). Roles: the source keeps its role, the responder takes `postYRole`.
Consumer: `bankPair_nonroot`. -/
def bankPairNR (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool) : BankCell × BankCell :=
  Id.run do
    let mut x := x0
    let mut y := y0
    let changed := postYRole != y.role
    y := { y with role := postYRole }
    if changed then
      y := { y with bit := false, tok := .E }
    if !(1 ≤ x.role && x.role ≤ b) then
      x := { x with tok := .E }
    if !(1 ≤ y.role && y.role ≤ b) then
      y := { y with tok := .E }
    if changed then
      if 1 ≤ x.role && x.role < b && (x.tok == .IR || x.tok == .CR0 || x.tok == .CR1) then
        x := { x with tok := .E }
      return (x, y)
    if x.role == b && x.tok == .IR then x := { x with tok := .E }
    if y.role == b && y.tok == .IR then y := { y with tok := .E }
    if 1 ≤ x.role && x.role < b && y.role == x.role + 1 then
      if x.tok == .RR then
        return ({ x with tok := .E }, { y with bit := false, tok := .RR })
      if y.role == b && y.tok == .RR then
        return ({ x with bit := false, tok := .RL }, { y with tok := .E })
      if y.tok == .RL then
        return ({ x with bit := false, tok := .RL }, { y with tok := .E })
      if x.tok != .E && y.tok != .E then
        return ({ x with tok := .E }, { y with tok := .E })
      if y.role == b && (y.tok == .CR0 || y.tok == .CR1) then
        return ({ x with tok := (if y.tok == .CR1 then BTok.CL1 else BTok.CL0) }, { y with tok := .E })
      if y.tok == .AL || y.tok == .CL0 || y.tok == .CL1 then
        return ({ x with tok := y.tok }, { y with tok := .E })
      if x.tok == .IR then
        return ({ x with tok := .E },
                { y with bit := !y.bit, tok := (if y.bit then BTok.IR else BTok.AL) })
      if x.tok == .CR0 || x.tok == .CR1 then
        let eq := (x.tok == .CR1) && (y.bit == theta (y.role - 1))
        return ({ x with tok := .E }, { y with tok := (if eq then BTok.CR1 else BTok.CR0) })
    return (x, y)

/-- The responder's mode and lease after `bankPair` on a nonroot source: RESET with lease 0 unless
its PACK stays 0, and then the grant, ARMED and wait rows. Consumer: `bankPair_nonroot`. -/
def bankPairModeY (y0 : BankCell) (postYRole : Nat) : Mode × Nat :=
  if postYRole = y0.role ∧ postYRole = 0 then
    if y0.grant then (.RESET, 0)
    else if y0.mode = .ARMED then (.RESET, 0)
    else if isWaitMode y0.mode then
      (if 1 < y0.lease then (y0.mode, y0.lease - 1) else (.RESET, 0))
    else (y0.mode, y0.lease)
  else (.RESET, 0)

/-- A cell with its mode and lease forgotten. Consumer: `bankPair_nonroot_tokView`. -/
def bankTokView (c : BankCell) : BankCell := { c with mode := .RESET, lease := 0 }

/-- On a nonroot source, `bankPair` and `bankPairNR` agree up to modes and leases. The projections
are pushed into the branches (`apply_ite`), so every mode row collapses (`ite_self`). -/
theorem bankPair_nonroot_tokView (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool)
    (hx : x0.role ≠ 0) :
    Prod.map bankTokView bankTokView (bankPair x0 y0 postYRole b theta) =
      Prod.map bankTokView bankTokView (bankPairNR x0 y0 postYRole b theta) := by
  have hx' : (x0.role != 0) = true := by simp [hx]
  have hx'' : (x0.role == 0) = false := by simp [hx]
  simp [bankPair, bankPairNR, bankTokView, Prod.map, hx, hx', hx'',
    apply_ite (Prod.map bankTokView bankTokView), apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
    apply_ite BankCell.bit, apply_ite BankCell.role, apply_ite BankCell.grant, apply_ite BankCell.mode,
    apply_ite BankCell.lease, ite_self]

/-- On a nonroot source the source ends in RESET with lease 0. -/
theorem bankPair_nonroot_fst_mode (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool)
    (hx : x0.role ≠ 0) :
    (bankPair x0 y0 postYRole b theta).1.mode = .RESET ∧
      (bankPair x0 y0 postYRole b theta).1.lease = 0 := by
  have hx' : (x0.role != 0) = true := by simp [hx]
  have hx'' : (x0.role == 0) = false := by simp [hx]
  simp [bankPair, hx, hx', hx'', apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
    apply_ite BankCell.bit, apply_ite BankCell.role, apply_ite BankCell.grant, apply_ite BankCell.mode,
    apply_ite BankCell.lease, ite_self]

/-- On a nonroot source the responder's mode and lease are `bankPairModeY`. -/
theorem bankPair_nonroot_snd_mode (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool)
    (hx : x0.role ≠ 0) :
    (bankPair x0 y0 postYRole b theta).2.mode = (bankPairModeY y0 postYRole).1 ∧
      (bankPair x0 y0 postYRole b theta).2.lease = (bankPairModeY y0 postYRole).2 := by
  have hx' : (x0.role != 0) = true := by simp [hx]
  have hx'' : (x0.role == 0) = false := by simp [hx]
  simp [bankPair, bankPairModeY, hx, hx', hx'', apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
    apply_ite BankCell.bit, apply_ite BankCell.role, apply_ite BankCell.grant, apply_ite BankCell.mode,
    apply_ite BankCell.lease, ite_self] <;>
    by_cases h1 : postYRole = y0.role <;> by_cases h2 : postYRole = 0 <;> simp_all

/-- The responder's mode and lease are `bankPairModeY` for every source: the root rows write only
the responder's bit and token. -/
theorem bankPair_snd_mode (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool) :
    (bankPair x0 y0 postYRole b theta).2.mode = (bankPairModeY y0 postYRole).1 ∧
      (bankPair x0 y0 postYRole b theta).2.lease = (bankPairModeY y0 postYRole).2 := by
  by_cases hx : x0.role = 0
  · have hx' : (x0.role != 0) = false := by simp [hx]
    have hx'' : (x0.role == 0) = true := by simp [hx]
    simp [bankPair, bankPairModeY, hx, hx', hx'', apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
      apply_ite BankCell.tok, apply_ite BankCell.bit, apply_ite BankCell.role, apply_ite BankCell.grant,
      apply_ite BankCell.mode, apply_ite BankCell.lease, ite_self, -not_imp,
      Decidable.not_imp_iff_and_not] <;>
      by_cases h1 : postYRole = y0.role <;> by_cases h2 : postYRole = 0 <;>
      simp_all [-not_imp, Decidable.not_imp_iff_and_not]
  · exact bankPair_nonroot_snd_mode x0 y0 postYRole b theta hx

/-- A responder with nonzero post PACK ends in RESET with lease 0, for every source. -/
theorem bankPair_snd_reset (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool)
    (hy : postYRole ≠ 0) :
    (bankPair x0 y0 postYRole b theta).2.mode = .RESET ∧
      (bankPair x0 y0 postYRole b theta).2.lease = 0 := by
  have hy' : (postYRole != 0) = true := by simp [hy]
  have hy'' : (postYRole == 0) = false := by simp [hy]
  simp [bankPair, hy, hy', hy'', apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
    apply_ite BankCell.tok, apply_ite BankCell.bit, apply_ite BankCell.role, apply_ite BankCell.grant,
    apply_ite BankCell.mode, apply_ite BankCell.lease, ite_self]

/-- **`bankPair` on a nonroot source**: the source is RESET with lease 0, the responder's mode and
lease are `bankPairModeY`, and roles, bits, tokens and grants are those of `bankPairNR`. -/
theorem bankPair_nonroot (x0 y0 : BankCell) (postYRole b : Nat) (theta : Nat → Bool)
    (hx : x0.role ≠ 0) :
    bankPair x0 y0 postYRole b theta =
      ({ (bankPairNR x0 y0 postYRole b theta).1 with mode := .RESET, lease := 0 },
       { (bankPairNR x0 y0 postYRole b theta).2 with
          mode := (bankPairModeY y0 postYRole).1, lease := (bankPairModeY y0 postYRole).2 }) := by
  have hA := bankPair_nonroot_tokView x0 y0 postYRole b theta hx
  have hB := bankPair_nonroot_fst_mode x0 y0 postYRole b theta hx
  have hC := bankPair_nonroot_snd_mode x0 y0 postYRole b theta hx
  generalize bankPair x0 y0 postYRole b theta = P at hA hB hC ⊢
  generalize bankPairNR x0 y0 postYRole b theta = Q at hA ⊢
  rcases P with ⟨⟨r1, m1, b1, t1, l1, g1⟩, ⟨r2, m2, b2, t2, l2, g2⟩⟩
  rcases Q with ⟨⟨s1, n1, c1, u1, k1, h1⟩, ⟨s2, n2, c2, u2, k2, h2⟩⟩
  simp only [Prod.map, bankTokView, Prod.mk.injEq, BankCell.mk.injEq, true_and, and_true] at hA hB hC ⊢
  obtain ⟨⟨e1, e2, e3, e4⟩, ⟨e5, e6, e7, e8⟩⟩ := hA
  obtain ⟨hm1, hl1⟩ := hB
  obtain ⟨hm2, hl2⟩ := hC
  subst e1 e2 e3 e4 e5 e6 e7 e8 hm1 hl1 hm2 hl2
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end L3
