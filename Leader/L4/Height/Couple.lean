import Leader.L4.Height.Window
import Init.Data.List.Perm

namespace L4.Height.Couple

open Classical

/-! ## State-dependent relabelling -/

/-- Relabel the raw letter at the current state before applying `next`. -/
def relabelNext {α : Type} {n : Nat}
    (next : α → Fin n → α) (σ : α → Fin n → Fin n) :
    α → Fin n → α :=
  fun x e => next x (σ x e)

/-- `List.ofFn` of an injective finite map has no repetitions. -/
private theorem ofFn_nodup_of_injective {α : Type} {n : Nat}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
        have h := hf hi
        cases h
      · exact ih (fun i => f i.succ)
          (fun i j h => Fin.succ_inj.mp (hf h))

/-- Reindexing a `Fin n` sum by a bijection does not change the sum. -/
theorem sum_ofFn_relabel {n : Nat}
    (σ τ : Fin n → Fin n)
    (hστ : ∀ e, σ (τ e) = e)
    (hτσ : ∀ e, τ (σ e) = e)
    (f : Fin n → Nat) :
    (List.ofFn (fun e => f (σ e))).sum =
      (List.ofFn f).sum := by
  have hσinj : Function.Injective σ := by
    intro i j hij
    have h := congrArg τ hij
    rw [hτσ i, hτσ j] at h
    exact h
  have hσnodup : (List.ofFn σ).Nodup :=
    ofFn_nodup_of_injective σ hσinj
  have hidnodup : (List.ofFn (fun e : Fin n => e)).Nodup :=
    ofFn_nodup_of_injective (fun e : Fin n => e) (fun _ _ h => h)
  have hperm :
      List.Perm (List.ofFn σ) (List.ofFn (fun e : Fin n => e)) := by
    apply (List.perm_ext_iff_of_nodup hσnodup hidnodup).2
    intro a
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨a, rfl⟩
    · rintro ⟨j, hj⟩
      subst a
      exact ⟨τ j, hστ j⟩
  have hsum := (hperm.map f).sum_nat
  simpa [Function.comp_def] using hsum

/-- State-dependent bijective relabelling preserves every endpoint
observable under the uniform word count. -/
theorem wordSum_relabel {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (σ τ : α → Fin n → Fin n)
    (hστ : ∀ x e, σ x (τ x e) = e)
    (hτσ : ∀ x e, τ x (σ x e) = e)
    (F : α → Nat) :
    ∀ (t : Nat) (x : α),
      wordSum
          (fun u => F (runWord (relabelNext next σ) x u)) t =
        wordSum (fun u => F (runWord next x u)) t := by
  intro t
  induction t with
  | zero =>
      intro x
      rfl
  | succ t ih =>
      intro x
      change
        (List.ofFn (fun e : Fin n =>
          wordSum
            (fun v => F (runWord (relabelNext next σ)
              (next x (σ x e)) v)) t)).sum =
        (List.ofFn (fun e : Fin n =>
          wordSum
            (fun v => F (runWord next (next x e) v)) t)).sum
      calc
        (List.ofFn (fun e : Fin n =>
          wordSum
            (fun v => F (runWord (relabelNext next σ)
              (next x (σ x e)) v)) t)).sum =
            (List.ofFn (fun e : Fin n =>
              wordSum
                (fun v => F (runWord next
                  (next x (σ x e)) v)) t)).sum := by
              apply sum_ofFn_eq
              intro e
              exact ih (next x (σ x e))
        _ = (List.ofFn (fun e : Fin n =>
              wordSum
                (fun v => F (runWord next (next x e) v)) t)).sum := by
              exact sum_ofFn_relabel (σ x) (τ x)
                (hστ x) (hτσ x)
                (fun e => wordSum
                  (fun v => F (runWord next (next x e) v)) t)

/-- State-dependent bijective relabelling also preserves every truncated
IID hitting cost. -/
theorem iidHitCost_relabel {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (σ τ : α → Fin n → Fin n)
    (hστ : ∀ x e, σ x (τ x e) = e)
    (hτσ : ∀ x e, τ x (σ x e) = e)
    (stop : α → Prop) :
    ∀ (t : Nat) (x : α),
      iidHitCost (relabelNext next σ) stop t x =
        iidHitCost next stop t x := by
  classical
  intro t
  induction t with
  | zero =>
      intro x
      rfl
  | succ t ih =>
      intro x
      by_cases hx : stop x
      · simp [iidHitCost, hx]
      · simp only [iidHitCost, hx, if_false]
        apply congrArg (fun z : Nat => n ^ (t + 1) + z)
        calc
          (List.ofFn (fun e : Fin n =>
            iidHitCost (relabelNext next σ) stop t
              (next x (σ x e)))).sum =
              (List.ofFn (fun e : Fin n =>
                iidHitCost next stop t
                  (next x (σ x e)))).sum := by
                apply sum_ofFn_eq
                intro e
                exact ih (next x (σ x e))
          _ = (List.ofFn (fun e : Fin n =>
                iidHitCost next stop t (next x e))).sum := by
                exact sum_ofFn_relabel (σ x) (τ x)
                  (hστ x) (hτσ x)
                  (fun e => iidHitCost next stop t (next x e))

/-! ## Adaptively revealed indexed bits -/

/-- A source whose letters are paired by an involution. A revealing
letter and its mate reveal the same index with opposite Boolean values.
No compatibility with `next` is assumed. -/
structure PairedSource (α ι : Type) (n : Nat) where
  next : α → Fin n → α
  bitOf : α → Fin n → Option (ι × Bool)
  flip : α → Fin n → Fin n
  half : Nat
  alphabet_even : n = 2 * half
  flip_invol : ∀ x e, flip x (flip x e) = e
  flip_reveal : ∀ x e k v,
    bitOf x e = some (k, v) →
      bitOf x (flip x e) = some (k, !v)

/-- The first value of index `k` revealed along a state-dependent run. -/
def firstReveal {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (k : ι) :
    α → List (Fin n) → Option Bool
  | _, [] => none
  | x, e :: u =>
      match S.bitOf x e with
      | none => firstReveal S k (S.next x e) u
      | some (j, v) =>
          if j = k then some v
          else firstReveal S k (S.next x e) u

/-- Delete the unique occurrence of an index from a pending list. -/
def eraseIndex {ι : Type} [DecidableEq ι] (k : ι) : List ι → List ι
  | [] => []
  | a :: ks => if a = k then ks else a :: eraseIndex k ks

private theorem mem_eraseIndex_iff {ι : Type} [DecidableEq ι]
    {k j : ι} {ks : List ι} (hnd : ks.Nodup) :
    j ∈ eraseIndex k ks ↔ j ∈ ks ∧ j ≠ k := by
  induction ks with
  | nil =>
      simp [eraseIndex]
  | cons a ks ih =>
      have hparts := List.nodup_cons.mp hnd
      by_cases hak : a = k
      · subst a
        simp only [eraseIndex]
        constructor
        · intro hj
          constructor
          · exact List.mem_cons_of_mem k hj
          · intro hjk
            subst j
            exact hparts.1 hj
        · rintro ⟨hj, hjk⟩
          rcases (List.mem_cons.mp hj) with hhead | htail
          · exact False.elim (hjk hhead)
          · exact htail
      · simp only [eraseIndex, if_neg hak]
        constructor
        · intro hj
          rcases (List.mem_cons.mp hj) with hhead | htail
          · subst j
            exact ⟨by simp, hak⟩
          · have hm := (ih hparts.2).mp htail
            exact ⟨List.mem_cons_of_mem a hm.1, hm.2⟩
        · rintro ⟨hj, hjk⟩
          rcases (List.mem_cons.mp hj) with hhead | htail
          · subst j
            exact (by simp)
          · exact List.mem_cons_of_mem a
              ((ih hparts.2).mpr ⟨htail, hjk⟩)

private theorem length_eraseIndex {ι : Type} [DecidableEq ι]
    {k : ι} {ks : List ι} (hk : k ∈ ks) :
    (eraseIndex k ks).length + 1 = ks.length := by
  induction ks with
  | nil =>
      simp at hk
  | cons a ks ih =>
      by_cases hak : a = k
      · subst a
        simp [eraseIndex]
      · have htail : k ∈ ks := by
          rcases (List.mem_cons.mp hk) with h | h
          · exact False.elim (hak h.symm)
          · exact h
        simp only [eraseIndex, if_neg hak, List.length_cons]
        have h := ih htail
        omega

private theorem nodup_eraseIndex {ι : Type} [DecidableEq ι]
    {k : ι} {ks : List ι} (hnd : ks.Nodup) :
    (eraseIndex k ks).Nodup := by
  induction ks with
  | nil =>
      simp [eraseIndex]
  | cons a ks ih =>
      have hparts := List.nodup_cons.mp hnd
      by_cases hak : a = k
      · subst a
        simpa [eraseIndex] using hparts.2
      · rw [eraseIndex, if_neg hak]
        apply List.nodup_cons.mpr
        constructor
        · intro ha
          have hm := (mem_eraseIndex_iff hparts.2).mp ha
          exact hparts.1 hm.1
        · exact ih hparts.2

private theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

private theorem bool_not_eq_of_ne (a b : Bool) (h : a ≠ b) :
    (!a) = b := by
  cases a <;> cases b <;> simp_all

/-- Pending indices after a letter, ignoring the revealed value. -/
def pendingIndices {ι : Type} [DecidableEq ι]
    (ks : List ι) : Option (ι × Bool) → List ι
  | none => ks
  | some (k, _) => if k ∈ ks then eraseIndex k ks else ks

/-- Recursive acceptance of prescribed first-reveal values. Once an index
is first revealed it is removed, so later revelations of the same index are
ignored. -/
def adaptiveAccept {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool) :
    α → List ι → List (Fin n) → Bool
  | _, ks, [] => decide (ks = [])
  | x, ks, e :: u =>
      match S.bitOf x e with
      | none => adaptiveAccept S want (S.next x e) ks u
      | some (k, v) =>
          if k ∈ ks then
            if v = want k then
              adaptiveAccept S want (S.next x e) (eraseIndex k ks) u
            else false
          else adaptiveAccept S want (S.next x e) ks u

/-- User-facing first-reveal prescription. -/
def FirstPrescribed {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool)
    (x : α) (ks : List ι) (u : List (Fin n)) : Prop :=
  ∀ k, k ∈ ks → firstReveal S k x u = some (want k)

/-- On a duplicate-free pending list, recursive acceptance is exactly the
conjunction of prescribed first-reveal values. -/
theorem adaptiveAccept_iff_firstPrescribed
    {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool) :
    ∀ (x : α) (ks : List ι) (u : List (Fin n)),
      ks.Nodup →
      (adaptiveAccept S want x ks u = true ↔
        FirstPrescribed S want x ks u) := by
  intro x ks u
  induction u generalizing x ks with
  | nil =>
      intro hnd
      cases ks with
      | nil =>
          simp [adaptiveAccept, FirstPrescribed]
      | cons k ks =>
          constructor
          · intro h
            simp [adaptiveAccept] at h
          · intro h
            have hk := h k (by simp)
            simp [firstReveal] at hk
  | cons e u ih =>
      intro hnd
      cases hbit : S.bitOf x e with
      | none =>
          simpa [adaptiveAccept, FirstPrescribed, firstReveal, hbit] using
            (ih (S.next x e) ks hnd)
      | some kv =>
          rcases kv with ⟨k, v⟩
          by_cases hk : k ∈ ks
          · by_cases hv : v = want k
            · have hnd' : (eraseIndex k ks).Nodup :=
                nodup_eraseIndex hnd
              have hpres :
                  FirstPrescribed S want x ks (e :: u) ↔
                    FirstPrescribed S want (S.next x e)
                      (eraseIndex k ks) u := by
                constructor
                · intro h j hj
                  have hm := (mem_eraseIndex_iff hnd).mp hj
                  have hj0 := h j hm.1
                  have hne : k ≠ j := by
                    intro hkj
                    exact hm.2 hkj.symm
                  simpa [firstReveal, hbit, hne] using hj0
                · intro h j hj
                  by_cases hjk : j = k
                  · subst j
                    simp [firstReveal, hbit, hv]
                  · have hmem : j ∈ eraseIndex k ks :=
                      (mem_eraseIndex_iff hnd).mpr ⟨hj, hjk⟩
                    have hj0 := h j hmem
                    have hne : k ≠ j := by
                      intro hkj
                      exact hjk hkj.symm
                    simpa [firstReveal, hbit, hne] using hj0
              simp only [adaptiveAccept, hbit, if_pos hk, if_pos hv]
              exact (ih (S.next x e) (eraseIndex k ks) hnd').trans
                hpres.symm
            · have hfalse :
                  ¬ FirstPrescribed S want x ks (e :: u) := by
                intro h
                have hk0 := h k hk
                have heq : v = want k := by
                  have hs : some v = some (want k) := by
                    simpa [firstReveal, hbit] using hk0
                  exact Option.some.inj hs
                exact hv heq
              simp [adaptiveAccept, hbit, hk, hv, hfalse]
          · have hpres :
                FirstPrescribed S want x ks (e :: u) ↔
                  FirstPrescribed S want (S.next x e) ks u := by
              constructor
              · intro h j hj
                have hne : k ≠ j := by
                  intro hkj
                  apply hk
                  simpa [hkj] using hj
                have hj0 := h j hj
                simpa [firstReveal, hbit, hne] using hj0
              · intro h j hj
                have hne : k ≠ j := by
                  intro hkj
                  apply hk
                  simpa [hkj] using hj
                have hj0 := h j hj
                simpa [firstReveal, hbit, hne] using hj0
            simp only [adaptiveAccept, hbit, if_neg hk]
            exact (ih (S.next x e) ks hnd).trans hpres.symm

/-- Count of words accepted by the pending-index machine. -/
def adaptiveMass {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool)
    (x : α) (ks : List ι) (t : Nat) : Nat :=
  wordSum
    (fun u => if adaptiveAccept S want x ks u then 1 else 0) t

private theorem flip_none {α ι : Type} {n : Nat}
    (S : PairedSource α ι n) (x : α) (e : Fin n)
    (h : S.bitOf x e = none) :
    S.bitOf x (S.flip x e) = none := by
  cases h' : S.bitOf x (S.flip x e) with
  | none => rfl
  | some kv =>
      rcases kv with ⟨k, v⟩
      have hh := S.flip_reveal x (S.flip x e) k v h'
      rw [S.flip_invol x e] at hh
      rw [h] at hh
      cases hh

/-- Averaging an inequality over a finite involution cancels the duplicated
pair count. -/
private theorem paired_sum_bound {n P N : Nat}
    (flip : Fin n → Fin n)
    (hinvol : ∀ e, flip (flip e) = e)
    (c : Fin n → Nat)
    (hpair : ∀ e, P * (c e + c (flip e)) ≤ 2 * N) :
    P * (List.ofFn c).sum ≤ n * N := by
  have hsum := sum_ofFn_le
    (fun e : Fin n => P * (c e + c (flip e)))
    (fun _ : Fin n => 2 * N) hpair
  have hflip :
      (List.ofFn (fun e : Fin n => c (flip e))).sum =
        (List.ofFn c).sum :=
    sum_ofFn_relabel flip flip hinvol hinvol c
  have hdouble :
      (P * (List.ofFn c).sum) * 2 ≤ (n * N) * 2 := by
    calc
      (P * (List.ofFn c).sum) * 2 =
          (List.ofFn (fun e : Fin n =>
            P * (c e + c (flip e)))).sum := by
              rw [sum_ofFn_mul_left, sum_ofFn_add, hflip,
                Nat.mul_add]
              omega
      _ ≤ (List.ofFn (fun _ : Fin n => 2 * N)).sum := hsum
      _ = (n * N) * 2 := by
            rw [sum_ofFn_const]
            ac_rfl
  exact Nat.le_of_mul_le_mul_right hdouble (by decide)

/-- The equality version of `paired_sum_bound`. -/
private theorem paired_sum_eq {n P N : Nat}
    (flip : Fin n → Fin n)
    (hinvol : ∀ e, flip (flip e) = e)
    (c : Fin n → Nat)
    (hpair : ∀ e, P * (c e + c (flip e)) = 2 * N) :
    P * (List.ofFn c).sum = n * N := by
  have hsum := sum_ofFn_eq
    (fun e : Fin n => P * (c e + c (flip e)))
    (fun _ : Fin n => 2 * N) hpair
  have hflip :
      (List.ofFn (fun e : Fin n => c (flip e))).sum =
        (List.ofFn c).sum :=
    sum_ofFn_relabel flip flip hinvol hinvol c
  have hdouble :
      (P * (List.ofFn c).sum) * 2 = (n * N) * 2 := by
    calc
      (P * (List.ofFn c).sum) * 2 =
          (List.ofFn (fun e : Fin n =>
            P * (c e + c (flip e)))).sum := by
              rw [sum_ofFn_mul_left, sum_ofFn_add, hflip,
                Nat.mul_add]
              omega
      _ = (List.ofFn (fun _ : Fin n => 2 * N)).sum := hsum
      _ = (n * N) * 2 := by
            rw [sum_ofFn_const]
            ac_rfl
  apply Nat.le_antisymm
  · exact Nat.le_of_mul_le_mul_right
      (Nat.le_of_eq hdouble) (by decide)
  · exact Nat.le_of_mul_le_mul_right
      (Nat.le_of_eq hdouble.symm) (by decide)

/-- Core adaptive upper bound, expressed through the recursive pending-index
machine. -/
private theorem adaptiveMass_bound
    {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool) :
    ∀ (t : Nat) (x : α) (ks : List ι),
      ks.Nodup →
      2 ^ ks.length * adaptiveMass S want x ks t ≤ n ^ t := by
  intro t
  induction t with
  | zero =>
      intro x ks hnd
      cases ks with
      | nil =>
          simp [adaptiveMass, adaptiveAccept, wordSum]
      | cons k ks =>
          simp [adaptiveMass, adaptiveAccept, wordSum]
  | succ t ih =>
      intro x ks hnd
      unfold adaptiveMass
      simp only [wordSum]
      let c : Fin n → Nat := fun e =>
        wordSum
          (fun u => if adaptiveAccept S want x ks (e :: u)
            then 1 else 0) t
      change 2 ^ ks.length * (List.ofFn c).sum ≤ n ^ (t + 1)
      have hpair : ∀ e : Fin n,
          2 ^ ks.length * (c e + c (S.flip x e)) ≤
            2 * n ^ t := by
        intro e
        cases hbit : S.bitOf x e with
        | none =>
            have hflip := flip_none S x e hbit
            have hc :
                c e = adaptiveMass S want (S.next x e) ks t := by
              simp [c, adaptiveMass, adaptiveAccept, hbit]
            have hcf :
                c (S.flip x e) =
                  adaptiveMass S want (S.next x (S.flip x e)) ks t := by
              simp [c, adaptiveMass, adaptiveAccept, hflip]
            have he := ih (S.next x e) ks hnd
            have hef := ih (S.next x (S.flip x e)) ks hnd
            rw [hc, hcf, Nat.mul_add]
            have hadd := Nat.add_le_add he hef
            omega
        | some kv =>
            rcases kv with ⟨k, v⟩
            have hflip := S.flip_reveal x e k v hbit
            by_cases hk : k ∈ ks
            · have hnd' : (eraseIndex k ks).Nodup :=
                nodup_eraseIndex hnd
              have hlen := length_eraseIndex hk
              by_cases hv : v = want k
              · have hnot : (!v) ≠ want k := by
                  intro h
                  apply bool_not_ne_self v
                  calc
                    (!v) = want k := h
                    _ = v := hv.symm
                have hc :
                    c e = adaptiveMass S want (S.next x e)
                      (eraseIndex k ks) t := by
                  simp [c, adaptiveMass, adaptiveAccept,
                    hbit, hk, hv]
                have hcf : c (S.flip x e) = 0 := by
                  simp [c, adaptiveAccept, hflip, hk, hnot,
                    wordSum_zero]
                have hs := ih (S.next x e) (eraseIndex k ks) hnd'
                rw [hc, hcf, Nat.add_zero, ← hlen, Nat.pow_succ]
                have htwice := Nat.mul_le_mul_left 2 hs
                simpa [Nat.mul_assoc, Nat.mul_comm,
                  Nat.mul_left_comm] using htwice
              · have hmatch : (!v) = want k :=
                  bool_not_eq_of_ne v (want k) hv
                have hc : c e = 0 := by
                  simp [c, adaptiveAccept, hbit, hk, hv,
                    wordSum_zero]
                have hcf :
                    c (S.flip x e) =
                      adaptiveMass S want (S.next x (S.flip x e))
                        (eraseIndex k ks) t := by
                  simp [c, adaptiveMass, adaptiveAccept,
                    hflip, hk, hmatch]
                have hs := ih (S.next x (S.flip x e))
                  (eraseIndex k ks) hnd'
                rw [hc, hcf, Nat.zero_add, ← hlen, Nat.pow_succ]
                have htwice := Nat.mul_le_mul_left 2 hs
                simpa [Nat.mul_assoc, Nat.mul_comm,
                  Nat.mul_left_comm] using htwice
            · have hc :
                  c e = adaptiveMass S want (S.next x e) ks t := by
                simp [c, adaptiveMass, adaptiveAccept, hbit, hk]
              have hcf :
                  c (S.flip x e) =
                    adaptiveMass S want
                      (S.next x (S.flip x e)) ks t := by
                simp [c, adaptiveMass, adaptiveAccept, hflip, hk]
              have he := ih (S.next x e) ks hnd
              have hef := ih (S.next x (S.flip x e)) ks hnd
              rw [hc, hcf, Nat.mul_add]
              have hadd := Nat.add_le_add he hef
              omega
      have havg := paired_sum_bound (S.flip x) (S.flip_invol x)
        c hpair
      simpa [Nat.pow_succ, Nat.mul_comm] using havg

/-- Every pending index is revealed on every word of the given length. -/
def FirstCoverage {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (x : α)
    (ks : List ι) (t : Nat) : Prop :=
  ∀ u, u.length = t → ∀ k, k ∈ ks →
    ∃ v, firstReveal S k x u = some v

/-- Coverage passes to the suffix after one arbitrary first letter. -/
private theorem coverage_tail
    {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n)
    (x : α) (ks : List ι) (t : Nat)
    (hnd : ks.Nodup)
    (hcover : FirstCoverage S x ks (t + 1))
    (e : Fin n) :
    FirstCoverage S (S.next x e)
      (pendingIndices ks (S.bitOf x e)) t := by
  intro u hu j hj
  cases hbit : S.bitOf x e with
  | none =>
      obtain ⟨b, hb⟩ := hcover (e :: u) (by simp [hu]) j (by
        simpa [pendingIndices, hbit] using hj)
      exact ⟨b, by simpa [firstReveal, hbit] using hb⟩
  | some kv =>
      rcases kv with ⟨k, v⟩
      by_cases hk : k ∈ ks
      · have hj' : j ∈ eraseIndex k ks := by
          simpa [pendingIndices, hbit, hk] using hj
        have hm := (mem_eraseIndex_iff hnd).mp hj'
        have hne : k ≠ j := by
          intro hkj
          exact hm.2 hkj.symm
        obtain ⟨b, hb⟩ := hcover (e :: u) (by simp [hu]) j hm.1
        exact ⟨b, by simpa [firstReveal, hbit, hne] using hb⟩
      · have hj' : j ∈ ks := by
          simpa [pendingIndices, hbit, hk] using hj
        have hne : k ≠ j := by
          intro hkj
          apply hk
          simpa [hkj] using hj'
        obtain ⟨b, hb⟩ := hcover (e :: u) (by simp [hu]) j hj'
        exact ⟨b, by simpa [firstReveal, hbit, hne] using hb⟩

/-- Exact adaptive mass when every pending index is revealed on every word. -/
private theorem adaptiveMass_eq
    {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool) :
    ∀ (t : Nat) (x : α) (ks : List ι),
      ks.Nodup → FirstCoverage S x ks t →
      2 ^ ks.length * adaptiveMass S want x ks t = n ^ t := by
  intro t
  induction t with
  | zero =>
      intro x ks hnd hcover
      cases ks with
      | nil =>
          simp [adaptiveMass, adaptiveAccept, wordSum]
      | cons k ks =>
          exfalso
          obtain ⟨b, hb⟩ := hcover [] rfl k (by simp)
          simp [firstReveal] at hb
  | succ t ih =>
      intro x ks hnd hcover
      unfold adaptiveMass
      simp only [wordSum]
      let c : Fin n → Nat := fun e =>
        wordSum
          (fun u => if adaptiveAccept S want x ks (e :: u)
            then 1 else 0) t
      change 2 ^ ks.length * (List.ofFn c).sum = n ^ (t + 1)
      have hpair : ∀ e : Fin n,
          2 ^ ks.length * (c e + c (S.flip x e)) =
            2 * n ^ t := by
        intro e
        have hcovE := coverage_tail S x ks t hnd hcover e
        have hcovF := coverage_tail S x ks t hnd hcover (S.flip x e)
        cases hbit : S.bitOf x e with
        | none =>
            have hflip := flip_none S x e hbit
            have hc :
                c e = adaptiveMass S want (S.next x e) ks t := by
              simp [c, adaptiveMass, adaptiveAccept, hbit]
            have hcf :
                c (S.flip x e) =
                  adaptiveMass S want (S.next x (S.flip x e)) ks t := by
              simp [c, adaptiveMass, adaptiveAccept, hflip]
            have hcovE' : FirstCoverage S (S.next x e) ks t := by
              simpa [pendingIndices, hbit] using hcovE
            have hcovF' :
                FirstCoverage S (S.next x (S.flip x e)) ks t := by
              simpa [pendingIndices, hflip] using hcovF
            have he := ih (S.next x e) ks hnd hcovE'
            have hef := ih (S.next x (S.flip x e)) ks hnd hcovF'
            rw [hc, hcf, Nat.mul_add, he, hef]
            omega
        | some kv =>
            rcases kv with ⟨k, v⟩
            have hflip := S.flip_reveal x e k v hbit
            by_cases hk : k ∈ ks
            · have hnd' : (eraseIndex k ks).Nodup :=
                nodup_eraseIndex hnd
              have hlen := length_eraseIndex hk
              have hcovE' :
                  FirstCoverage S (S.next x e) (eraseIndex k ks) t := by
                simpa [pendingIndices, hbit, hk] using hcovE
              have hcovF' :
                  FirstCoverage S (S.next x (S.flip x e))
                    (eraseIndex k ks) t := by
                simpa [pendingIndices, hflip, hk] using hcovF
              by_cases hv : v = want k
              · have hnot : (!v) ≠ want k := by
                  intro h
                  apply bool_not_ne_self v
                  calc
                    (!v) = want k := h
                    _ = v := hv.symm
                have hc :
                    c e = adaptiveMass S want (S.next x e)
                      (eraseIndex k ks) t := by
                  simp [c, adaptiveMass, adaptiveAccept,
                    hbit, hk, hv]
                have hcf : c (S.flip x e) = 0 := by
                  simp [c, adaptiveAccept, hflip, hk, hnot,
                    wordSum_zero]
                have hs := ih (S.next x e)
                  (eraseIndex k ks) hnd' hcovE'
                rw [hc, hcf, Nat.add_zero, ← hlen, Nat.pow_succ]
                calc
                  (2 ^ (eraseIndex k ks).length * 2) *
                      adaptiveMass S want (S.next x e)
                        (eraseIndex k ks) t =
                      2 * (2 ^ (eraseIndex k ks).length *
                        adaptiveMass S want (S.next x e)
                          (eraseIndex k ks) t) := by ac_rfl
                  _ = 2 * n ^ t := by rw [hs]
              · have hmatch : (!v) = want k :=
                  bool_not_eq_of_ne v (want k) hv
                have hc : c e = 0 := by
                  simp [c, adaptiveAccept, hbit, hk, hv,
                    wordSum_zero]
                have hcf :
                    c (S.flip x e) =
                      adaptiveMass S want (S.next x (S.flip x e))
                        (eraseIndex k ks) t := by
                  simp [c, adaptiveMass, adaptiveAccept,
                    hflip, hk, hmatch]
                have hs := ih (S.next x (S.flip x e))
                  (eraseIndex k ks) hnd' hcovF'
                rw [hc, hcf, Nat.zero_add, ← hlen, Nat.pow_succ]
                calc
                  (2 ^ (eraseIndex k ks).length * 2) *
                      adaptiveMass S want (S.next x (S.flip x e))
                        (eraseIndex k ks) t =
                      2 * (2 ^ (eraseIndex k ks).length *
                        adaptiveMass S want
                          (S.next x (S.flip x e))
                          (eraseIndex k ks) t) := by ac_rfl
                  _ = 2 * n ^ t := by rw [hs]
            · have hc :
                  c e = adaptiveMass S want (S.next x e) ks t := by
                simp [c, adaptiveMass, adaptiveAccept, hbit, hk]
              have hcf :
                  c (S.flip x e) =
                    adaptiveMass S want
                      (S.next x (S.flip x e)) ks t := by
                simp [c, adaptiveMass, adaptiveAccept, hflip, hk]
              have hcovE' : FirstCoverage S (S.next x e) ks t := by
                simpa [pendingIndices, hbit, hk] using hcovE
              have hcovF' :
                  FirstCoverage S (S.next x (S.flip x e)) ks t := by
                simpa [pendingIndices, hflip, hk] using hcovF
              have he := ih (S.next x e) ks hnd hcovE'
              have hef := ih (S.next x (S.flip x e)) ks hnd hcovF'
              rw [hc, hcf, Nat.mul_add, he, hef]
              omega
      have havg := paired_sum_eq (S.flip x) (S.flip_invol x)
        c hpair
      simpa [Nat.pow_succ, Nat.mul_comm] using havg

/-- Adaptive distinct indexed bits have at most the uniform prescribed mass. -/
theorem adaptive_prescribed
    {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool)
    (x : α) (ks : List ι) (hnd : ks.Nodup) (t : Nat) :
    2 ^ ks.length *
        wordSum
          (fun u => if FirstPrescribed S want x ks u then 1 else 0) t ≤
      n ^ t := by
  classical
  have hcore := adaptiveMass_bound S want t x ks hnd
  have heq :
      wordSum
          (fun u => if FirstPrescribed S want x ks u then 1 else 0) t =
        adaptiveMass S want x ks t := by
    unfold adaptiveMass
    apply wordSum_congr
    intro u
    have hiff := adaptiveAccept_iff_firstPrescribed S want x ks u hnd
    by_cases hp : FirstPrescribed S want x ks u
    · have ha := hiff.mpr hp
      simp [hp, ha]
    · have ha : adaptiveAccept S want x ks u ≠ true := by
        intro ha
        exact hp (hiff.mp ha)
      cases hb : adaptiveAccept S want x ks u <;> simp_all
  rw [heq]
  exact hcore

/-- If every selected index is revealed on every length-`t` word, the
adaptive prescribed mass is exactly uniform. -/
theorem adaptive_prescribed_eq
    {α ι : Type} {n : Nat} [DecidableEq ι]
    (S : PairedSource α ι n) (want : ι → Bool)
    (x : α) (ks : List ι) (hnd : ks.Nodup) (t : Nat)
    (hcover : FirstCoverage S x ks t) :
    2 ^ ks.length *
        wordSum
          (fun u => if FirstPrescribed S want x ks u then 1 else 0) t =
      n ^ t := by
  classical
  have hcore := adaptiveMass_eq S want t x ks hnd hcover
  have heq :
      wordSum
          (fun u => if FirstPrescribed S want x ks u then 1 else 0) t =
        adaptiveMass S want x ks t := by
    unfold adaptiveMass
    apply wordSum_congr
    intro u
    have hiff := adaptiveAccept_iff_firstPrescribed S want x ks u hnd
    by_cases hp : FirstPrescribed S want x ks u
    · have ha := hiff.mpr hp
      simp [hp, ha]
    · have ha : adaptiveAccept S want x ks u ≠ true := by
        intro ha
        exact hp (hiff.mp ha)
      cases hb : adaptiveAccept S want x ks u <;> simp_all
  rw [heq]
  exact hcore

/-! ## Quarter-weight transfer to a logical bad set -/

/-- Defaulted vector of first-reveal values. Under `FirstCoverage`, the
default branch is never used. -/
noncomputable def readVector {α : Type} {n K : Nat}
    (S : PairedSource α (Fin K) n) (x : α)
    (u : List (Fin n)) : Fin K → Bool :=
  fun k => (firstReveal S k x u).getD false

/-- The fiber corresponding to one logical Boolean vector. -/
def AssignmentFiber {α : Type} {n K : Nat}
    (S : PairedSource α (Fin K) n) (x : α)
    (a : Fin K → Bool) (u : List (Fin n)) : Prop :=
  FirstPrescribed S a x (List.finRange K) u

/-- Sum of indicators over a finite list of logical assignments. -/
noncomputable def eventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop) :
    List β → List (Fin n) → Nat
  | [], _ => 0
  | a :: as, u => (if P a u then 1 else 0) + eventSum P as u

private theorem wordSum_eventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop) (as : List β) (t : Nat) :
    wordSum (eventSum P as) t =
      (as.map (fun a =>
        wordSum (fun u => if P a u then 1 else 0) t)).sum := by
  classical
  induction as with
  | nil =>
      simp [eventSum, wordSum_zero]
  | cons a as ih =>
      simp only [eventSum, List.map_cons, List.sum_cons]
      rw [wordSum_add_fun, ih]

private theorem one_le_eventSum_of_mem {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop)
    {a : β} {as : List β} {u : List (Fin n)}
    (ha : a ∈ as) (hp : P a u) :
    1 ≤ eventSum P as u := by
  classical
  induction as with
  | nil =>
      simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hba | ha
      · subst b
        simp [eventSum, hp]
      · have htail := ih ha
        by_cases hb : P b u
        · simp [eventSum, hb]
        · simpa [eventSum, hb] using htail

private theorem wordSum_mono_on_length {n : Nat}
    (f g : List (Fin n) → Nat) :
    ∀ t, (∀ u, u.length = t → f u ≤ g u) →
      wordSum f t ≤ wordSum g t := by
  intro t
  induction t generalizing f g with
  | zero =>
      intro h
      exact h [] rfl
  | succ t ih =>
      intro h
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      apply ih
      intro u hu
      apply h
      simp [hu]

private theorem list_scaled_sum_le {β : Type}
    (p T : Nat) (f : β → Nat) :
    ∀ as : List β,
      (∀ a, a ∈ as → p * f a ≤ T) →
      p * (as.map f).sum ≤ as.length * T := by
  intro as
  induction as with
  | nil =>
      intro h
      simp
  | cons a as ih =>
      intro h
      have ha := h a (by simp)
      have htail : ∀ b, b ∈ as → p * f b ≤ T := by
        intro b hb
        exact h b (by simp [hb])
      have hi := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.succ_mul]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_le_add ha hi)

/-- A quarter-weight logical bad set pulls back to a quarter-weight raw
failure event. `bad` is a duplicate-free enumeration of the logical set
`F`; logical words are Boolean functions on `Fin K`. -/
theorem adaptive_quarter_transfer
    {α : Type} {n K : Nat}
    (S : PairedSource α (Fin K) n) (x : α) (t : Nat)
    (E : List (Fin n) → Prop)
    (F : (Fin K → Bool) → Prop)
    (bad : List (Fin K → Bool))
    (hbadDistinct : bad.Nodup)
    (hbad : ∀ a, a ∈ bad ↔ F a)
    (hquarter : 4 * bad.length ≤ 2 ^ K)
    (hcover : FirstCoverage S x (List.finRange K) t)
    (hlogical : ∀ u, u.length = t → E u →
      F (readVector S x u)) :
    4 * wordSum (fun u => if E u then 1 else 0) t ≤ n ^ t := by
  classical
  let P : (Fin K → Bool) → List (Fin n) → Prop :=
    fun a u => FirstPrescribed S a x (List.finRange K) u
  let eventMass : Nat :=
    wordSum (fun u => if E u then 1 else 0) t
  let fiberMass : (Fin K → Bool) → Nat := fun a =>
    wordSum (fun u => if P a u then 1 else 0) t
  have hpoint : ∀ u, u.length = t →
      (if E u then 1 else 0) ≤ eventSum P bad u := by
    intro u hu
    by_cases he : E u
    · have hF := hlogical u hu he
      have hmem : readVector S x u ∈ bad :=
        (hbad (readVector S x u)).2 hF
      have hpres : P (readVector S x u) u := by
        intro k hk
        obtain ⟨b, hb⟩ := hcover u hu k hk
        have hv : readVector S x u k = b := by
          simp [readVector, hb]
        rw [hv]
        exact hb
      have hone := one_le_eventSum_of_mem P hmem hpres
      simpa [he] using hone
    · simp [he]
  have hmass :
      eventMass ≤ (bad.map fiberMass).sum := by
    unfold eventMass fiberMass
    calc
      wordSum (fun u => if E u then 1 else 0) t ≤
          wordSum (eventSum P bad) t :=
            wordSum_mono_on_length _ _ t hpoint
      _ = (bad.map (fun a =>
            wordSum (fun u => if P a u then 1 else 0) t)).sum :=
              wordSum_eventSum P bad t
  have hfiber : ∀ a, a ∈ bad →
      2 ^ K * fiberMass a ≤ n ^ t := by
    intro a ha
    dsimp [fiberMass, P]
    simpa only [List.length_finRange] using
      (adaptive_prescribed S a x (List.finRange K)
        (List.nodup_finRange K) t)
  have hsum :
      2 ^ K * (bad.map fiberMass).sum ≤ bad.length * n ^ t :=
    list_scaled_sum_le (2 ^ K) (n ^ t) fiberMass bad hfiber
  have hpull :
      2 ^ K * eventMass ≤ bad.length * n ^ t :=
    Nat.le_trans (Nat.mul_le_mul_left (2 ^ K) hmass) hsum
  have hscaled :
      (4 * eventMass) * (2 ^ K) ≤
        (4 * bad.length) * n ^ t := by
    calc
      (4 * eventMass) * (2 ^ K) =
          4 * ((2 ^ K) * eventMass) := by ac_rfl
      _ ≤ 4 * (bad.length * n ^ t) :=
        Nat.mul_le_mul_left 4 hpull
      _ = (4 * bad.length) * n ^ t := by ac_rfl
  have hproduct :
      (4 * eventMass) * (2 ^ K) ≤ (n ^ t) * (2 ^ K) := by
    calc
      (4 * eventMass) * (2 ^ K) ≤
          (4 * bad.length) * n ^ t := hscaled
      _ ≤ (2 ^ K) * n ^ t :=
        Nat.mul_le_mul_right (n ^ t) hquarter
      _ = (n ^ t) * (2 ^ K) := Nat.mul_comm _ _
  have hpow : 0 < (2 : Nat) ^ K := Nat.pow_pos (by decide)
  have hfinal := Nat.le_of_mul_le_mul_right hproduct hpow
  simpa [eventMass] using hfinal

#print axioms sum_ofFn_relabel
#print axioms wordSum_relabel
#print axioms iidHitCost_relabel
#print axioms adaptiveAccept_iff_firstPrescribed
#print axioms adaptive_prescribed
#print axioms adaptive_prescribed_eq
#print axioms adaptive_quarter_transfer

end L4.Height.Couple
