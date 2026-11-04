import Leader.L3.Primitive.TapMatrix
import Leader.L3.Primitive.ExactPeriod

namespace L3

set_option autoImplicit false

/-!
Generic soundness of the installed GF(2) tap certificates,
and coverage of all nonzero Boolean words by each primitive orbit.

The unrestricted rowsApply multiplication theorem in TapMatrix is PRIVATE;
the following local proof copies the same finite-fold argument instead of
silently importing it or demanding unproved well-formedness of a computed
Gauss-Jordan inverse.

No non-core imports.
-/

/-! Unrestricted matrix multiplication: private local helpers match
the source proofs in TapMatrix.lean. -/

private theorem fold_id :
    ∀ (t : Nat) (b : Bool),
      Fin.foldl t (fun x _ => x) b = b := by
  intro t
  induction t with
  | zero =>
      intro b
      rfl
  | succ t ih =>
      intro b
      simpa only [Fin.foldl_succ] using ih b

private theorem foldXorAdd :
    ∀ (t : Nat) (f g : Fin t → Bool) (a b : Bool),
      Fin.foldl t
        (fun z j => z ^^ (f j ^^ g j)) (a ^^ b) =
        ((Fin.foldl t (fun z j => z ^^ f j) a) ^^
         (Fin.foldl t (fun z j => z ^^ g j) b)) := by
  intro t
  induction t with
  | zero =>
      intro f g a b
      rfl
  | succ t ih =>
      intro f g a b
      simp only [Fin.foldl_succ]
      have hstart :
          ((a ^^ b) ^^ (f 0 ^^ g 0)) =
          ((a ^^ f 0) ^^ (b ^^ g 0)) := by
        cases a <;> cases b <;>
          cases f 0 <;> cases g 0 <;> decide
      rw [hstart]
      exact ih (fun j : Fin t => f j.succ)
        (fun j : Fin t => g j.succ)
        (a ^^ f 0) (b ^^ g 0)

private def dot (t : Nat) (row : Nat) (u : Fin t → Bool) : Bool :=
  Fin.foldl t (fun acc j => acc ^^ (row.testBit j.val && u j)) false

private theorem dot_zero (t : Nat) (u : Fin t → Bool) :
    dot t 0 u = false := by
  unfold dot
  simp only [Nat.zero_testBit, Bool.false_and, Bool.xor_false]
  exact fold_id t false

private theorem dot_xor (t : Nat) (a b : Nat)
    (u : Fin t → Bool) :
    dot t (Nat.xor a b) u = ((dot t a u) ^^ (dot t b u)) := by
  rw [show Nat.xor a b = a ^^^ b from rfl]
  unfold dot
  simp only [Nat.testBit_xor]
  simp only [Bool.and_xor_distrib_right]
  simpa only [Bool.false_xor] using
    (foldXorAdd t
      (fun j => a.testBit j.val && u j)
      (fun j => b.testBit j.val && u j)
      false false)

/-- Applying dot after a selected XOR of rows is the corresponding
selected XOR of dot values. This also handles unbounded source masks. -/
private theorem dotFoldXor (t : Nat) (xs : List Nat)
    (selected : Nat → Bool) (value : Nat → Nat)
    (u : Fin t → Bool) :
    ∀ z : Nat,
      dot t
        (xs.foldl
          (fun acc j => if selected j then Nat.xor acc (value j) else acc)
          z) u =
      xs.foldl
        (fun acc j => acc ^^ (selected j && dot t (value j) u))
        (dot t z u) := by
  induction xs with
  | nil =>
      intro z
      rfl
  | cons j xs ih =>
      intro z
      cases hj : selected j with
      | false =>
          simpa [List.foldl_cons, hj] using ih z
      | true =>
          have h := ih (Nat.xor z (value j))
          rw [dot_xor t z (value j) u] at h
          simpa [List.foldl_cons, hj] using h

private theorem rangePrimeFold {α : Type} (n : Nat) :
    ∀ (start : Nat) (f : α → Nat → α) (a : α),
      (List.range' start n).foldl f a =
        Fin.foldl n (fun z i => f z (start + i.val)) a := by
  induction n with
  | zero =>
      intro start f a
      rfl
  | succ n ih =>
      intro start f a
      rw [List.range'_succ, List.foldl_cons, Fin.foldl_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (start + 1) f (f a start))

private theorem rangeFoldFin {α : Type} (n : Nat)
    (f : α → Nat → α) (a : α) :
    (List.range n).foldl f a =
      Fin.foldl n (fun z i => f z i.val) a := by
  rw [List.range_eq_range']
  simpa only [Nat.zero_add] using rangePrimeFold n 0 f a

private theorem range_map_getD (t i : Nat) (f : Nat → Nat)
    (hi : i < t) :
    ((List.range t).map f).getD i 0 = f i := by
  have hm : i < ((List.range t).map f).length := by simpa using hi
  rw [← List.getElem_eq_getD
    (l := (List.range t).map f) (i := i) (h := hm) 0]
  simp

private theorem rowsApply_mul_any (t : Nat) (A B : List Nat)
    (u : Fin t → Bool) :
    rowsApply t (rowsMul t A B) u =
      rowsApply t A (rowsApply t B u) := by
  funext i
  change dot t ((rowsMul t A B).getD i.val 0) u =
    dot t (A.getD i.val 0) (rowsApply t B u)
  change dot t
      (((List.range t).map (fun r =>
        (List.range t).foldl
          (fun acc j =>
            if Nat.testBit (A.getD r 0) j
            then Nat.xor acc (B.getD j 0) else acc) 0)).getD i.val 0) u =
    dot t (A.getD i.val 0) (rowsApply t B u)
  rw [range_map_getD t i.val _ i.isLt]
  rw [dotFoldXor t (List.range t)
    (fun j => Nat.testBit (A.getD i.val 0) j)
    (fun j => B.getD j 0) u 0]
  rw [dot_zero]
  rw [rangeFoldFin]
  rfl

private theorem rowsApply_false_vector (t : Nat)
    (A : List Nat) :
    rowsApply t A (fun _ => false) = (fun _ => false) := by
  funext i
  change Fin.foldl t
    (fun acc j =>
      acc ^^ (Nat.testBit (A.getD i.val 0) j.val && false))
    false = false
  simpa only [Bool.and_false, Bool.xor_false] using
    (fold_id t false)

/-! The actual recurrence iterate convention is compatible with
PeriodLemma.iterate, even though their successor equations differ. -/

private theorem iterate_succ_right {α : Type}
    (f : α → α) (k : Nat) (x : α) :
    iterate f (k + 1) x = f (iterate f k x) := by
  calc
    iterate f (k + 1) x = iterate f (1 + k) x := by
      rw [Nat.add_comm]
    _ = iterate f 1 (iterate f k x) := iterate_add f 1 k x
    _ = f (iterate f k x) := rfl

private theorem recIter_eq_iterate (t : Nat)
    (taps : Nat → Bool) (k : Nat) (u : Fin t → Bool) :
    recIter t taps k u = iterate (recStep t taps) k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        recIter t taps (k + 1) u =
            recStep t taps (recIter t taps k u) := rfl
        _ = recStep t taps (iterate (recStep t taps) k u) := by
              rw [ih]
        _ = iterate (recStep t taps) (k + 1) u :=
              (iterate_succ_right (recStep t taps) k u).symm

private theorem andTrueSplit {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- Checked factorization, bounded prime tests, matrix period, and
verified left inverses imply the genuine exact primitive period. -/
theorem certificateCheck_sound (t : Nat)
    (h2 : 2 ≤ t) (h17 : t ≤ 17)
    (hc : certificateCheck t = true) :
    IsPrimitive t (fun j => (tapTable t).getD j false) := by
  let taps : Nat → Bool := fun j => (tapTable t).getD j false
  let A : List Nat := recRows t taps
  let M : Nat := 2 ^ t - 1
  let ps : List Nat := tapFactorList t
  change
      ((((ps.foldl (fun acc p => acc * p) 1 == M) &&
        ps.all smallPrimeTrial) &&
        (rowsPowFast t A M == rowsId t)) &&
        ps.all (fun p =>
          let C := rowsXor t
            (rowsPowFast t A (M / p)) (rowsId t)
          rowsMul t (rowsInverseCandidate t C) C == rowsId t)) =
        true at hc
  have hrest := andTrueSplit hc
  have hthree := andTrueSplit hrest.1
  have htwo := andTrueSplit hthree.1
  have hfactorB := htwo.1
  have hprimeB := htwo.2
  have hpowerB := hthree.2
  have hinverseB := hrest.2
  have hfactorEq :
      ps.foldl (fun acc p => acc * p) 1 = M := by
    simpa only [beq_iff_eq] using hfactorB
  have hproduct : prodList ps = M := by
    rw [← foldl_mul_one_eq]
    exact hfactorEq
  have hpower : rowsPowFast t A M = rowsId t := by
    simpa only [beq_iff_eq] using hpowerB
  have hleft :
      ∀ p ∈ ps,
        rowsMul t
          (rowsInverseCandidate t
            (rowsXor t (rowsPowFast t A (M / p)) (rowsId t)))
          (rowsXor t (rowsPowFast t A (M / p)) (rowsId t)) =
        rowsId t := by
    intro p hp
    have h := List.all_eq_true.mp hinverseB p hp
    change
      (rowsMul t
        (rowsInverseCandidate t
          (rowsXor t (rowsPowFast t A (M / p)) (rowsId t)))
        (rowsXor t (rowsPowFast t A (M / p)) (rowsId t)) ==
        rowsId t) = true at h
    simpa only [beq_iff_eq] using h
  have hpowLow : 2 ^ 2 ≤ 2 ^ t :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h2
  have hMpos : 0 < M := by
    have hcalc : 2 ^ 2 = 4 := by decide
    rw [hcalc] at hpowLow
    dsimp [M]
    omega
  have hpowUp : 2 ^ t ≤ 2 ^ 17 :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h17
  have hMle : M ≤ 131071 := by
    have hcalc : 2 ^ 17 = 131072 := by decide
    rw [hcalc] at hpowUp
    dsimp [M]
    omega
  have hprime : ∀ p ∈ ps, IsPrimeNat p := by
    intro p hp
    have htrial := List.all_eq_true.mp hprimeB p hp
    have hdvd : p ∣ M := by
      rw [← hproduct]
      exact dvd_prodList ps p hp
    have hle : p ≤ M := Nat.le_of_dvd hMpos hdvd
    exact smallPrimeTrial_sound p htrial
      (Nat.le_trans hle hMle)
  have hperiod : ∀ u : Fin t → Bool, recIter t taps M u = u := by
    intro u
    calc
      recIter t taps M u =
          rowsApply t (rowsPowFast t A M) u :=
            recIter_rowsPowFast t taps M u
      _ = rowsApply t (rowsId t) u := by rw [hpower]
      _ = u := rowsApply_id t u
  have hnotFix : ∀ (u : Fin t → Bool),
      (∃ i, u i = true) →
      ∀ p ∈ ps, recIter t taps (M / p) u ≠ u := by
    intro u hu p hp hfix
    let C : List Nat := rowsXor t
      (rowsPowFast t A (M / p)) (rowsId t)
    let B : List Nat := rowsInverseCandidate t C
    have hBC : rowsMul t B C = rowsId t := hleft p hp
    have hAp : rowsApply t (rowsPowFast t A (M / p)) u = u := by
      calc
        rowsApply t (rowsPowFast t A (M / p)) u =
            recIter t taps (M / p) u :=
              (recIter_rowsPowFast t taps (M / p) u).symm
        _ = u := hfix
    have hCu : rowsApply t C u = (fun _ => false) := by
      calc
        rowsApply t C u =
            (fun i =>
              ((rowsApply t (rowsPowFast t A (M / p)) u) i) ^^
              ((rowsApply t (rowsId t) u) i)) :=
                rowsApply_xor t (rowsPowFast t A (M / p))
                  (rowsId t) u
        _ = (fun i => (u i) ^^ (u i)) := by
              rw [hAp, rowsApply_id]
        _ = (fun _ => false) := by
              funext i
              cases u i <;> rfl
    have hzero : u = (fun _ => false) := by
      calc
        u = rowsApply t (rowsId t) u := (rowsApply_id t u).symm
        _ = rowsApply t (rowsMul t B C) u := by rw [hBC]
        _ = rowsApply t B (rowsApply t C u) :=
          rowsApply_mul_any t B C u
        _ = rowsApply t B (fun _ => false) := by rw [hCu]
        _ = (fun _ => false) := rowsApply_false_vector t B
    obtain ⟨i, hi⟩ := hu
    have hbad : false = true := by
      calc
        false = (fun _ : Fin t => false) i := rfl
        _ = u i := congrFun hzero.symm i
        _ = true := hi
    cases hbad
  intro u hu
  have hM : iterate (recStep t taps) M u = u := by
    rw [← recIter_eq_iterate t taps M u]
    exact hperiod u
  have htests :
      ∀ p ∈ ps, iterate (recStep t taps) (M / p) u ≠ u := by
    intro p hp hfix
    apply hnotFix u hu p hp
    calc
      recIter t taps (M / p) u =
          iterate (recStep t taps) (M / p) u :=
            recIter_eq_iterate t taps (M / p) u
      _ = u := hfix
  have hshort := period_exact_of_prime_tests
    (recStep t taps) u M ps hMpos hM hproduct hprime htests
  refine ⟨hperiod u, ?_⟩
  intro k hk hkM hfix
  apply hshort k hk hkM
  calc
    iterate (recStep t taps) k u = recIter t taps k u :=
      (recIter_eq_iterate t taps k u).symm
    _ = u := hfix

theorem tapTable_primitive (t : Nat)
    (h2 : 2 ≤ t) (h17 : t ≤ 17) :
    IsPrimitive t (fun j => (tapTable t).getD j false) := by
  have hcases :
      t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨
      t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨
      t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨
      t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 := by
    omega
  have hmem :
      t ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
        : List Nat) := by
    rcases hcases with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h <;> simp [h]
  have hc : certificateCheck t = true :=
    List.all_eq_true.mp certificateCheck_installed t hmem
  exact certificateCheck_sound t h2 h17 hc

/-! Generic nonzero-orbit coverage. -/

private theorem recIter_add (t : Nat) (taps : Nat → Bool)
    (a b : Nat) (u : Fin t → Bool) :
    recIter t taps (a + b) u =
      recIter t taps a (recIter t taps b u) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
      simp only [Nat.succ_add, recIter_succ, ih]

private theorem recStep_false_vector (t : Nat)
    (taps : Nat → Bool) :
    recStep t taps (fun _ => false) = (fun _ => false) := by
  funext i
  unfold recStep
  split
  · rfl
  · simpa only [Bool.and_false, Bool.xor_false] using
      (fold_id t false)

private theorem recIter_false_vector (t : Nat)
    (taps : Nat → Bool) (k : Nat) :
    recIter t taps k (fun _ => false) = (fun _ => false) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change recStep t taps
        (recIter t taps k (fun _ => false)) = (fun _ => false)
      rw [ih]
      exact recStep_false_vector t taps

private theorem recIter_nonzero (t : Nat)
    (taps : Nat → Bool) (M k : Nat)
    (u : Fin t → Bool)
    (hk : k ≤ M)
    (hM : recIter t taps M u = u)
    (hu : ∃ i, u i = true) :
    ∃ i, (recIter t taps k u) i = true := by
  classical
  by_cases h : ∃ i, (recIter t taps k u) i = true
  · exact h
  · have hzero :
        recIter t taps k u = (fun _ => false) := by
      funext i
      cases hb : recIter t taps k u i with
      | false => rfl
      | true => exact False.elim (h ⟨i, hb⟩)
    have hsum : M - k + k = M := Nat.sub_add_cancel hk
    have hUz : u = (fun _ => false) := by
      calc
        u = recIter t taps M u := hM.symm
        _ = recIter t taps (M - k + k) u := by rw [hsum]
        _ = recIter t taps (M - k)
              (recIter t taps k u) := recIter_add t taps _ _ u
        _ = recIter t taps (M - k) (fun _ => false) := by rw [hzero]
        _ = (fun _ => false) := recIter_false_vector t taps _
    obtain ⟨i, hi⟩ := hu
    have hbad : false = true := by
      calc
        false = (fun _ : Fin t => false) i := rfl
        _ = u i := congrFun hUz.symm i
        _ = true := hi
    cases hbad

private theorem vcode_pos_of_true (t : Nat)
    (u : Fin t → Bool) (hu : ∃ i, u i = true) :
    0 < vcode t u := by
  obtain ⟨i, hi⟩ := hu
  have hn : vcode t u ≠ 0 := by
    intro hz
    have hbad : false = true := by
      calc
        false = (vdecode t 0) i := by simp [vdecode]
        _ = (vdecode t (vcode t u)) i := by rw [hz]
        _ = u i := congrFun (vdecode_vcode t u) i
        _ = true := hi
    cases hbad
  omega

private def omitFin {n : Nat} (p z : Fin (n + 1))
    (hz : z ≠ p) : Fin n :=
  if hl : z.val < p.val then
    ⟨z.val, by omega⟩
  else
    ⟨z.val - 1, by
      have hn : z.val ≠ p.val := by
        intro he
        exact hz (Fin.ext he)
      omega⟩

private theorem omitFin_inj {n : Nat} (p z w : Fin (n + 1))
    (hz : z ≠ p) (hw : w ≠ p)
    (h : omitFin p z hz = omitFin p w hw) :
    z = w := by
  apply Fin.ext
  have hval := congrArg Fin.val h
  have hzn : z.val ≠ p.val := by
    intro he
    exact hz (Fin.ext he)
  have hwn : w.val ≠ p.val := by
    intro he
    exact hw (Fin.ext he)
  by_cases hzl : z.val < p.val <;>
    by_cases hwl : w.val < p.val <;>
    simp [omitFin, hzl, hwl] at hval <;>
    omega

private theorem fin_injective_surjective :
    ∀ n (f : Fin n → Fin n),
      Function.Injective f → Function.Surjective f := by
  intro n
  induction n with
  | zero =>
      intro f hf v
      exact v.elim0
  | succ n ih =>
      intro f hf v
      let last : Fin (n + 1) := ⟨n, by omega⟩
      let p : Fin (n + 1) := f last
      by_cases hv : v = p
      · exact ⟨last, hv.symm⟩
      · let inc : Fin n → Fin (n + 1) :=
          fun i => ⟨i.val, by omega⟩
        have hinc (i : Fin n) : inc i ≠ last := by
          intro he
          have heval := congrArg Fin.val he
          dsimp [inc, last] at heval
          omega
        have hnot (i : Fin n) : f (inc i) ≠ p := by
          intro he
          exact hinc i (hf he)
        let g : Fin n → Fin n :=
          fun i => omitFin p (f (inc i)) (hnot i)
        have hg : Function.Injective g := by
          intro i j hij
          have hi :
              omitFin p (f (inc i)) (hnot i) =
                omitFin p (f (inc j)) (hnot j) := by
            simpa [g] using hij
          have hsame :
              f (inc i) = f (inc j) :=
            omitFin_inj p _ _ (hnot i) (hnot j) hi
          have he : inc i = inc j := hf hsame
          apply Fin.ext
          have heval := congrArg Fin.val he
          simpa [inc] using heval
        obtain ⟨i, hi⟩ := ih g hg (omitFin p v hv)
        have heq :
            omitFin p (f (inc i)) (hnot i) =
              omitFin p v hv := by
          simpa [g] using hi
        exact ⟨inc i, omitFin_inj p _ _ (hnot i) hv heq⟩

theorem isPrimitive_orbit_covers {t : Nat} {taps : Nat → Bool}
    (hp : IsPrimitive t taps)
    (u v : Fin t → Bool)
    (hu : ∃ i, u i = true)
    (hv : ∃ i, v i = true) :
    ∃ k, k < 2 ^ t - 1 ∧ recIter t taps k u = v := by
  let M : Nat := 2 ^ t - 1
  have hper : recIter t taps M u = u := (hp u hu).1
  have hshort : ∀ k, 0 < k → k < M →
      recIter t taps k u ≠ u := (hp u hu).2
  have hiterM :
      iterate (recStep t taps) M u = u := by
    rw [← recIter_eq_iterate t taps M u]
    exact hper
  have hiterShort :
      ∀ k, 0 < k → k < M →
      iterate (recStep t taps) k u ≠ u := by
    intro k hk hkM heq
    exact hshort k hk hkM
      ((recIter_eq_iterate t taps k u).trans heq)
  have hdist : ∀ i j, i < j → j < M →
      recIter t taps i u ≠ recIter t taps j u := by
    intro i j hij hjM heq
    have h := iterates_distinct (recStep t taps) u M
      hiterM hiterShort i j hij hjM
    apply h
    calc
      iterate (recStep t taps) i u = recIter t taps i u :=
        (recIter_eq_iterate t taps i u).symm
      _ = recIter t taps j u := heq
      _ = iterate (recStep t taps) j u :=
        recIter_eq_iterate t taps j u
  have hNZ (k : Fin M) :
      ∃ i, (recIter t taps k.val u) i = true :=
    recIter_nonzero t taps M k.val u
      (Nat.le_of_lt k.isLt) hper hu
  have hcodeNZ (k : Fin M) :
      0 < vcode t (recIter t taps k.val u) :=
    vcode_pos_of_true t _ (hNZ k)
  have hcodeV : 0 < vcode t v := vcode_pos_of_true t v hv
  let code : Fin M → Fin M := fun k =>
    ⟨vcode t (recIter t taps k.val u) - 1, by
      have hLo := hcodeNZ k
      have hHi := vcode_lt t (recIter t taps k.val u)
      dsimp [M]
      omega⟩
  have hInj : Function.Injective code := by
    intro i j hij
    have heqSub :
        vcode t (recIter t taps i.val u) - 1 =
          vcode t (recIter t taps j.val u) - 1 := by
      exact congrArg Fin.val hij
    have hcodeEq :
        vcode t (recIter t taps i.val u) =
          vcode t (recIter t taps j.val u) := by
      have hLo := hcodeNZ i
      have hHi := hcodeNZ j
      omega
    have hvEq :
        recIter t taps i.val u = recIter t taps j.val u := by
      calc
        recIter t taps i.val u =
            vdecode t (vcode t (recIter t taps i.val u)) :=
              (vdecode_vcode t _).symm
        _ = vdecode t (vcode t (recIter t taps j.val u)) := by
              rw [hcodeEq]
        _ = recIter t taps j.val u := vdecode_vcode t _
    by_cases hlt : i.val < j.val
    · exact False.elim (hdist i.val j.val hlt j.isLt hvEq)
    · by_cases hgt : j.val < i.val
      · exact False.elim (hdist j.val i.val hgt i.isLt hvEq.symm)
      · exact Fin.ext (by omega)
  let target : Fin M := ⟨vcode t v - 1, by
    have hHi := vcode_lt t v
    dsimp [M]
    omega⟩
  obtain ⟨k, hk⟩ :=
    fin_injective_surjective M code hInj target
  have hcodeEq : vcode t (recIter t taps k.val u) = vcode t v := by
    have heqSub :
        vcode t (recIter t taps k.val u) - 1 =
          vcode t v - 1 := by
      exact congrArg Fin.val hk
    have hLo := hcodeNZ k
    omega
  refine ⟨k.val, k.isLt, ?_⟩
  calc
    recIter t taps k.val u =
        vdecode t (vcode t (recIter t taps k.val u)) :=
          (vdecode_vcode t _).symm
    _ = vdecode t (vcode t v) := by rw [hcodeEq]
    _ = v := vdecode_vcode t v

end L3
