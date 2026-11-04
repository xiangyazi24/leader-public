import Leader.PPL.MainTheorem.Statement

/-!
# P_PL Theorem 1, general whp union for any target

The finite union bound behind the whp conjunct: if every failing word is bad
for one of the five phase events, and the five padded phase bounds hold with
coefficients 12, 8, 4, 1, 1, then `n` times the number of failing words is at
most `64 n^H`.  The global hitting test and the L18 event are parameters, so
the `psi < n` chain (`PPL.PsiBelowN.theorem1_whp_of_splice`, target `S_PL`)
and the `n ≤ psi` chain (`PPL.PsiAtLeastN.theorem1SafeWhp_of_splice`, the
safe target) are both special cases.

P_PL Theorem 1 cleanup, phase 2, step 6b.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- The whp union at one `(n, psi, ring, C0)` for any global test `reach`
and L18 event `bad18`: the splice and the five padded phase bounds
(coefficients 12, 8, 4, 1, 1) give at most `64 n^H / n` failing words. -/
theorem theorem1_whp_of_splice_at
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (reach bad18 : DetSchedule n → Bool)
    (hsplice :
      ∀ word : DetSchedule n,
        word ∈ allSchedules n (theorem1Horizon n psi) →
        !(reach word) = true →
        Or
          (theorem1Bad16B ring C0 word = true)
          (Or
            (theorem1Bad5iB ring C0 word = true)
            (Or
              (theorem1Bad5iiB ring C0 word = true)
              (Or
                (theorem1Bad17B ring C0 word = true)
                (bad18 word = true)))))
    (hb16 :
      n * (allSchedules n (theorem1Horizon n psi)).countP
          (theorem1Bad16B ring C0) ≤
        12 * n ^ theorem1Horizon n psi)
    (hb5i :
      n * (allSchedules n (theorem1Horizon n psi)).countP
          (theorem1Bad5iB ring C0) ≤
        8 * n ^ theorem1Horizon n psi)
    (hb5ii :
      n * (allSchedules n (theorem1Horizon n psi)).countP
          (theorem1Bad5iiB ring C0) ≤
        4 * n ^ theorem1Horizon n psi)
    (hb17 :
      n * (allSchedules n (theorem1Horizon n psi)).countP
          (theorem1Bad17B ring C0) ≤
        n ^ theorem1Horizon n psi)
    (hb18 :
      n * (allSchedules n (theorem1Horizon n psi)).countP bad18 ≤
        n ^ theorem1Horizon n psi) :
    n * (allSchedules n (theorem1Horizon n psi)).countP
        (fun word => !(reach word)) ≤
      64 * n ^ theorem1Horizon n psi := by
  have hfailure :
      (allSchedules n (theorem1Horizon n psi)).countP
          (fun word => !(reach word)) ≤
        (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad16B ring C0) +
          (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad5iB ring C0) +
          (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad5iiB ring C0) +
          (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad17B ring C0) +
          (allSchedules n (theorem1Horizon n psi)).countP bad18 :=
    theorem1_countP_five_union_le
      (allSchedules n (theorem1Horizon n psi))
      (fun word => !(reach word))
      (theorem1Bad16B ring C0)
      (theorem1Bad5iB ring C0)
      (theorem1Bad5iiB ring C0)
      (theorem1Bad17B ring C0)
      bad18
      (fun word hmem hbad => hsplice word hmem (by simpa using hbad))
  have hscaled := Nat.mul_le_mul_left n hfailure
  have hphase :=
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add hb16 hb5i) hb5ii)
        hb17)
      hb18
  calc
    n * (allSchedules n (theorem1Horizon n psi)).countP
          (fun word => !(reach word)) ≤
        n *
          ((allSchedules n (theorem1Horizon n psi)).countP
              (theorem1Bad16B ring C0) +
            (allSchedules n (theorem1Horizon n psi)).countP
              (theorem1Bad5iB ring C0) +
            (allSchedules n (theorem1Horizon n psi)).countP
              (theorem1Bad5iiB ring C0) +
            (allSchedules n (theorem1Horizon n psi)).countP
              (theorem1Bad17B ring C0) +
            (allSchedules n (theorem1Horizon n psi)).countP bad18) :=
      hscaled
    _ =
        n * (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad16B ring C0) +
          n * (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad5iB ring C0) +
          n * (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad5iiB ring C0) +
          n * (allSchedules n (theorem1Horizon n psi)).countP
            (theorem1Bad17B ring C0) +
          n * (allSchedules n (theorem1Horizon n psi)).countP bad18 := by
      simp only [Nat.mul_add]
    _ ≤
        12 * n ^ theorem1Horizon n psi +
          8 * n ^ theorem1Horizon n psi +
          4 * n ^ theorem1Horizon n psi +
          n ^ theorem1Horizon n psi +
          n ^ theorem1Horizon n psi :=
      hphase
    _ ≤ 64 * n ^ theorem1Horizon n psi :=
      theorem1_five_event_constants n (theorem1Horizon n psi)

end PPL.Theorem1General
