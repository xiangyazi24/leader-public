import Leader.L4.Height.Couple

namespace L4.BStarRevealCompletion
open L4.Height L4.Height.Couple
open Classical

/-- An independent bit obtained by pairing letters of the same finite alphabet. -/
structure Auxiliary (n : Nat) where
  bit : Fin n → Bool
  flip : Fin n → Fin n
  invol : ∀ e, flip (flip e) = e
  opposite : ∀ e, bit (flip e) = !bit e

structure State (α ι : Type) where
  raw : α
  left : Nat
  keys : List ι

variable {α ι : Type} {n : Nat}

def start (x : α) (t : Nat) (ks : List ι) : State α ι := ⟨x,t,ks⟩

/-- Use real stages up to the fixed horizon, then freeze the raw state while
each pending slot in the schedule supplies its own bit. Repeated reveals do
not override a previous first reveal. -/
def completed (S : PairedSource α ι n) (A : Auxiliary n) :
    PairedSource (State α ι) ι n where
  next x e :=
    match x.left with
    | k+1 => ⟨S.next x.raw e,k,x.keys⟩
    | 0 => ⟨x.raw,0,x.keys.tail⟩
  bitOf x e :=
    match x.left with
    | _+1 => S.bitOf x.raw e
    | 0 => x.keys.head?.map (fun k => (k,A.bit e))
  flip x e :=
    match x.left with
    | _+1 => S.flip x.raw e
    | 0 => A.flip e
  half := S.half
  alphabet_even := S.alphabet_even
  flip_invol := by
    intro x e
    cases x with
    | mk raw left keys =>
      cases left
      · exact A.invol e
      · exact S.flip_invol raw e
  flip_reveal := by
    intro x e k v h
    cases x with
    | mk raw left keys =>
      cases left
      · cases keys with
        | nil => contradiction
        | cons j js =>
          change some (j,A.bit e) = some (k,v) at h
          cases h
          change some (k,A.bit (A.flip e)) = some (k,!A.bit e)
          rw [A.opposite]
      · exact S.flip_reveal raw e k v h

theorem raw_prefix (S : PairedSource α ι n) (A : Auxiliary n)
    (ks : List ι) (u : List (Fin n)) (x : α) :
    runWord (completed S A).next (start x u.length ks) u =
      start (runWord S.next x u) 0 ks := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (S.next x e)

theorem raw_frozen (S : PairedSource α ι n) (A : Auxiliary n)
    (ks : List ι) (v : List (Fin n)) (x : α) :
    (runWord (completed S A).next (start x 0 ks) v).raw = x := by
  induction v generalizing ks with
  | nil => rfl
  | cons e v ih => exact ih ks.tail

variable [DecidableEq ι]

theorem first_append (S : PairedSource α ι n) (k : ι)
    (x : α) (u v : List (Fin n)) :
    firstReveal S k x (u++v) =
      (firstReveal S k x u).or (firstReveal S k (runWord S.next x u) v) := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    cases h : S.bitOf x e with
    | none => simpa [firstReveal, h, runWord] using ih (S.next x e)
    | some a =>
      rcases a with ⟨j,b⟩
      by_cases E : j=k
      · simp [firstReveal,h,E]
      · simpa [firstReveal,h,E,runWord] using ih (S.next x e)

theorem first_prefix (S : PairedSource α ι n) (A : Auxiliary n) (k : ι)
    (ks : List ι) (u : List (Fin n)) (x : α) :
    firstReveal (completed S A) k (start x u.length ks) u = firstReveal S k x u := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    cases h : S.bitOf x e with
    | none =>
      change (match S.bitOf x e with
        | none => _
        | some (j,b) => if j=k then some b else _) = _
      simp [h, firstReveal]
      exact ih (S.next x e)
    | some a =>
      rcases a with ⟨j,b⟩
      by_cases E : j=k
      · simp [firstReveal,completed,start,h,E]
      · simp [firstReveal,completed,start,h,E]
        exact ih (S.next x e)

theorem first_complete_append (S : PairedSource α ι n) (A : Auxiliary n) (k : ι)
    (ks : List ι) (u v : List (Fin n)) (x : α) :
    firstReveal (completed S A) k (start x u.length ks) (u++v) =
      (firstReveal S k x u).or
        (firstReveal (completed S A) k (start (runWord S.next x u) 0 ks) v) := by
  rw [first_append, first_prefix, raw_prefix]

theorem first_retained (S : PairedSource α ι n) (A : Auxiliary n) (k : ι)
    (ks : List ι) (u v : List (Fin n)) (x : α) (b : Bool)
    (read : firstReveal S k x u = some b) :
    firstReveal (completed S A) k (start x u.length ks) (u++v) = some b := by
  rw [first_complete_append,read]
  rfl

theorem auxiliary_covers (S : PairedSource α ι n) (A : Auxiliary n) (k : ι)
    (ks : List ι) (v : List (Fin n)) (x : α) (hv : v.length=ks.length)
    (mem : k ∈ ks) :
    ∃ b, firstReveal (completed S A) k (start x 0 ks) v = some b := by
  induction ks generalizing v with
  | nil => simp at mem
  | cons j js ih =>
    cases v with
    | nil => simp at hv
    | cons e v =>
      by_cases H : j=k
      · exact ⟨A.bit e, by simp [firstReveal,completed,start,H]⟩
      · have memTail : k ∈ js := by
          rcases List.mem_cons.mp mem with E|E
          · exact False.elim (H E.symm)
          · exact E
        obtain ⟨b,hb⟩ := ih v (by simpa using hv) memTail
        exact ⟨b, by simpa [firstReveal,completed,start,H] using hb⟩

theorem covers (S : PairedSource α ι n) (A : Auxiliary n)
    (ks : List ι) (x : α) (t : Nat) :
    FirstCoverage (completed S A) (start x t ks) ks (t+ks.length) := by
  intro w hw k mem
  let u := w.take t
  let v := w.drop t
  have hu : u.length=t := by simp [u, hw]
  have hv : v.length=ks.length := by simp [v, hw]
  have split : u++v=w := List.take_append_drop t w
  rw [← split, ← hu, first_complete_append]
  cases h : firstReveal S k x u with
  | some b => exact ⟨b,rfl⟩
  | none => obtain ⟨b,hb⟩ := auxiliary_covers S A k ks v (runWord S.next x u) hv mem
            exact ⟨b,hb⟩

/-- Matching the physical first-read information imposes no constraint on
a slot not yet physically read. -/
def Compatible {K : Nat} (S : PairedSource α (Fin K) n) (x : α)
    (u : List (Fin n)) (a : Fin K → Bool) : Prop :=
  ∀ k b, firstReveal S k x u = some b → a k = b

theorem readVector_compatible {K : Nat}
    (S : PairedSource α (Fin K) n) (A : Auxiliary n)
    (ks : List (Fin K)) (u v : List (Fin n)) (x : α) :
    Compatible S x u (readVector (completed S A) (start x u.length ks) (u++v)) := by
  intro k b h
  simp only [readVector, first_retained S A k ks u v x b h, Option.getD_some]

/-- Adding arbitrarily many ignored letters to the right multiplies the
count by precisely the number of ignored words. -/
theorem wordSum_take_factor (f : List (Fin n) → Nat) (t K : Nat) :
    wordSum (fun w => f (w.take t)) (t+K) = n^K * wordSum f t := by
  induction t generalizing f with
  | zero => simpa [wordSum] using (wordSum_const (n:=n) (f []) K)
  | succ t ih =>
    rw [Nat.succ_add]
    change (List.ofFn (fun e : Fin n =>
      wordSum (fun w => f (e :: w.take t)) (t+K))).sum =
      n^K * (List.ofFn (fun e : Fin n => wordSum (fun w => f (e :: w)) t)).sum
    rw [← sum_ofFn_mul_left]
    apply sum_ofFn_eq
    intro e
    exact ih (fun w => f (e::w))

/-- A sufficient, explicitly deterministic comparison hypothesis for
transferring a quarter bound: *every* assignment compatible with the
physical first reads of a bad word is logically bad. The auxiliary stages
supply exactly one letter per key, not extra physical transitions. -/
theorem quarter_of_compatible {K : Nat}
    (S : PairedSource α (Fin K) n) (A : Auxiliary n)
    (x : α) (t : Nat) (hn : 0<n)
    (E : List (Fin n) → Prop) (F : (Fin K → Bool) → Prop)
    (bad : List (Fin K → Bool)) (distinct : bad.Nodup)
    (exactBad : ∀ a, a ∈ bad ↔ F a) (quarter : 4*bad.length≤2^K)
    (compare : ∀ u, u.length=t → E u → ∀ a, Compatible S x u a → F a) :
    4 * wordSum (fun u => if E u then 1 else 0) t ≤ n^t := by
  classical
  let ks := List.finRange K
  let Es := fun w : List (Fin n) => E (w.take t)
  have C : FirstCoverage (completed S A) (start x t ks) ks (t+K) := by
    simpa [ks] using covers S A ks x t
  have B : ∀ w, w.length=t+K → Es w →
      F (readVector (completed S A) (start x t ks) w) := by
    intro w hw he
    let u := w.take t
    let v := w.drop t
    have hu : u.length=t := by simp [u, hw]
    apply compare u hu he
    have H := readVector_compatible S A ks u v x
    rw [hu] at H
    change Compatible S x u (readVector (completed S A) (start x t ks) (w.take t ++ w.drop t)) at H
    rwa [List.take_append_drop] at H
  have L := adaptive_quarter_transfer (completed S A) (start x t ks)
    (t+K) Es F bad distinct exactBad quarter C B
  change 4 * wordSum (fun w => if E (w.take t) then 1 else 0) (t+K) ≤ n^(t+K) at L
  rw [wordSum_take_factor (fun u => if E u then 1 else 0), Nat.pow_add] at L
  have R : (4 * wordSum (fun u => if E u then 1 else 0) t) * n^K ≤ n^t * n^K := by
    simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using L
  exact Nat.le_of_mul_le_mul_right R (Nat.pow_pos hn)

end L4.BStarRevealCompletion
