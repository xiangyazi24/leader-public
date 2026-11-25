import Leader.L4.Height.HeightLemma
import Leader.L4.Height.Quarter
import Init.Data.List.OfFn
import Init.Data.List.Pairwise
import Init.Data.List.Perm
import Init.Data.List.Nat.Sum
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Div.Lemmas
import Init.Omega

/-!
# Bit-vector enumeration and the logical quarter bound

A vector in `Fin (Q * m) → Bool` is read in `Q` consecutive blocks of
`m` bits.  Each block is encoded as the corresponding letter of
`Fin (2 ^ m)`.  The explicit inverse proves that this is a bijection onto
scheduler words of length `Q`; consequently the vector failure count is
exactly the `wordSum` failure mass bounded by `logical_quarter`.
-/

namespace L4.Height

open Classical
open L4.Compiler.Native

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section

/-! ## Exact binary coding of Boolean vectors -/

/-- Little-endian numerical encoding of a Boolean vector. -/
private def logicalCode : (K : Nat) → (Fin K → Bool) → Nat
  | 0, _ => 0
  | K + 1, a =>
      2 * logicalCode K (fun i => a i.succ) + (a 0).toNat

/-- Decode the first `K` bits of a natural number. -/
private def logicalDecode (K x : Nat) : Fin K → Bool :=
  fun i => x.testBit i.val

private theorem double_add_bit_div (a : Nat) (b : Bool) :
    (2 * a + b.toNat) / 2 = a := by
  cases b <;> simp <;> omega

private theorem double_add_bit_testBit_zero (a : Nat) (b : Bool) :
    (2 * a + b.toNat).testBit 0 = b := by
  cases b <;> simp [Nat.testBit_zero, Nat.add_mod] <;> omega

private theorem logicalCode_lt :
    ∀ (K : Nat) (a : Fin K → Bool), logicalCode K a < 2 ^ K := by
  intro K
  induction K with
  | zero =>
      intro a
      simp [logicalCode]
  | succ K ih =>
      intro a
      have htail := ih (fun i : Fin K => a i.succ)
      change
        2 * logicalCode K (fun i : Fin K => a i.succ) +
            (a 0).toNat <
          2 ^ (K + 1)
      rw [Nat.pow_succ]
      cases a 0 <;> simp <;> omega

private theorem logicalDecode_logicalCode
    (K : Nat) (a : Fin K → Bool) :
    logicalDecode K (logicalCode K a) = a := by
  induction K with
  | zero =>
      funext i
      exact i.elim0
  | succ K ih =>
      funext i
      cases i using Fin.cases with
      | zero =>
          change
            (2 * logicalCode K (fun j : Fin K => a j.succ) +
              (a 0).toNat).testBit 0 = a 0
          exact double_add_bit_testBit_zero _ _
      | succ j =>
          change
            (2 * logicalCode K (fun k : Fin K => a k.succ) +
              (a 0).toNat).testBit (j.val + 1) = a j.succ
          rw [Nat.testBit_add_one, double_add_bit_div]
          exact congrFun (ih (fun k : Fin K => a k.succ)) j

private theorem logicalCode_logicalDecode
    (K x : Nat) (hx : x < 2 ^ K) :
    logicalCode K (logicalDecode K x) = x := by
  induction K generalizing x with
  | zero =>
      have hxzero : x = 0 := by
        have hxone : x < 1 := by simpa using hx
        omega
      subst x
      rfl
  | succ K ih =>
      have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by
        rw [Nat.pow_succ]
        omega
      have hhalf : x / 2 < 2 ^ K := by
        rw [hpow] at hx
        omega
      change
        2 * logicalCode K
              (fun j : Fin K => x.testBit j.succ.val) +
            (x.testBit 0).toNat =
          x
      have htail :
          (fun j : Fin K => x.testBit j.succ.val) =
            logicalDecode K (x / 2) := by
        funext j
        change x.testBit (j.val + 1) = (x / 2).testBit j.val
        exact Nat.testBit_add_one x j.val
      rw [htail, ih (x / 2) hhalf, Nat.toNat_testBit]
      simp only [Nat.pow_zero, Nat.div_one]
      omega

/-- Encode one Boolean vector as the corresponding scheduler letter. -/
def encodeBits {K : Nat} (a : Fin K → Bool) : Fin (2 ^ K) :=
  ⟨logicalCode K a, logicalCode_lt K a⟩

/-- Decoding an encoded Boolean vector returns the original vector. -/
@[simp] theorem bitsOf_encodeBits {K : Nat} (a : Fin K → Bool) :
    bitsOf (encodeBits a) = a := by
  change logicalDecode K (logicalCode K a) = a
  exact logicalDecode_logicalCode K a

/-- Encoding the bits of a scheduler letter returns the same letter. -/
@[simp] theorem encodeBits_bitsOf {K : Nat} (e : Fin (2 ^ K)) :
    encodeBits (bitsOf e) = e := by
  apply Fin.ext
  change logicalCode K (logicalDecode K e.val) = e.val
  exact logicalCode_logicalDecode K e.val e.isLt

private theorem bitsOf_injective (K : Nat) :
    Function.Injective (fun e : Fin (2 ^ K) => bitsOf e) := by
  intro e f hef
  calc
    e = encodeBits (bitsOf e) := (encodeBits_bitsOf e).symm
    _ = encodeBits (bitsOf f) := congrArg encodeBits hef
    _ = f := encodeBits_bitsOf f

/-- `List.ofFn` of an injective finite map has no repetitions. -/
private theorem ofFn_nodup_of_injective {α : Type} :
    (n : Nat) → (f : Fin n → α) →
      Function.Injective f → (List.ofFn f).Nodup
  | 0, _, _ => by simp [List.ofFn_zero]
  | n + 1, f, hf => by
      rw [List.ofFn_succ]
      apply (List.nodup_cons).2
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have hzero : (0 : Fin (n + 1)) = i.succ := hf hi.symm
        exact (Fin.succ_ne_zero i) hzero.symm
      · apply ofFn_nodup_of_injective n
          (fun i : Fin n => f i.succ)
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- The complete list of Boolean vectors of length `K`. -/
def allVectors (K : Nat) : List (Fin K → Bool) :=
  List.ofFn (fun e : Fin (2 ^ K) => bitsOf e)

/-- Every Boolean vector occurs at most once in `allVectors`. -/
theorem allVectors_nodup (K : Nat) : (allVectors K).Nodup := by
  unfold allVectors
  exact ofFn_nodup_of_injective (2 ^ K)
    (fun e : Fin (2 ^ K) => bitsOf e) (bitsOf_injective K)

/-- Every Boolean vector occurs in `allVectors`. -/
theorem mem_allVectors {K : Nat} (a : Fin K → Bool) :
    a ∈ allVectors K := by
  unfold allVectors
  apply List.mem_ofFn.mpr
  exact ⟨encodeBits a, bitsOf_encodeBits a⟩

/-- There are exactly `2^K` Boolean vectors of length `K`. -/
theorem allVectors_length (K : Nat) :
    (allVectors K).length = 2 ^ K := by
  simp [allVectors]

/-! ## Splitting a vector into logical rounds -/

/-- The flattened coordinate belonging to round `r` and site `i`. -/
private def blockIndex {Q m : Nat} (r : Fin Q) (i : Fin m) :
    Fin (Q * m) :=
  ⟨r.val * m + i.val, by
    calc
      r.val * m + i.val < r.val * m + m :=
        Nat.add_lt_add_left i.isLt _
      _ = (r.val + 1) * m := (Nat.succ_mul r.val m).symm
      _ ≤ Q * m :=
        Nat.mul_le_mul_right m (Nat.succ_le_of_lt r.isLt)⟩

/-- Split a flattened `Q*m`-bit vector into `Q` consecutive `m`-bit rounds. -/
def vecRounds (Q m : Nat) (a : Fin (Q * m) → Bool) :
    List (Fin m → Bool) :=
  List.ofFn (fun r : Fin Q => fun i => a (blockIndex r i))

/-- `vecRounds` contains exactly `Q` rounds. -/
theorem vecRounds_length (Q m : Nat) (a : Fin (Q * m) → Bool) :
    (vecRounds Q m a).length = Q := by
  simp [vecRounds]

/-- Encode every round as one letter of `Fin (2^m)`. -/
def vecWord (Q m : Nat) (a : Fin (Q * m) → Bool) :
    List (Fin (2 ^ m)) :=
  List.ofFn (fun r : Fin Q =>
    encodeBits (fun i => a (blockIndex r i)))

/-- The encoded scheduler word has length `Q`. -/
theorem vecWord_length (Q m : Nat) (a : Fin (Q * m) → Bool) :
    (vecWord Q m a).length = Q := by
  simp [vecWord]

/-- Decoding every encoded letter gives exactly `vecRounds`. -/
theorem vecWord_map_bitsOf (Q m : Nat)
    (a : Fin (Q * m) → Bool) :
    (vecWord Q m a).map bitsOf = vecRounds Q m a := by
  apply List.ext_getElem
  · simp [vecWord, vecRounds]
  · intro r hleft hright
    simp only [vecWord, vecRounds, List.getElem_map,
      List.getElem_ofFn]
    exact bitsOf_encodeBits _

/-- Executing the encoded word is the same as executing the split rounds. -/
theorem runWord_vecWord {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (Q : Nat)
    (a : Fin (Q * m) → Bool) :
    runWord (heightChain B hm) s (vecWord Q m a) =
      runRounds B hm (vecRounds Q m a) s := by
  rw [runWord_heightChain, vecWord_map_bitsOf]

/-! ## Explicit inverse and the vector/word bijection -/

/-- The unique all-zero letter, used only as an out-of-range `getD` default. -/
private def zeroLetter (m : Nat) : Fin (2 ^ m) :=
  encodeBits (fun _ : Fin m => false)

private theorem vecWord_getD {Q m : Nat}
    (a : Fin (Q * m) → Bool) (r : Fin Q) :
    (vecWord Q m a).getD r.val (zeroLetter m) =
      encodeBits (fun i => a (blockIndex r i)) := by
  have hr : r.val < (vecWord Q m a).length := by
    simpa only [vecWord_length] using r.isLt
  rw [← List.getElem_eq_getD
    (l := vecWord Q m a) (i := r.val) (h := hr) (zeroLetter m)]
  simp [vecWord]

/-- Flatten a word back into one `Q*m`-bit vector.  For malformed short words,
missing letters are read as zero; the round-trip theorem only needs words of
length `Q`. -/
def wordVec (Q m : Nat) (u : List (Fin (2 ^ m))) :
    Fin (Q * m) → Bool :=
  fun j =>
    if hpos : 0 < m then
      bitsOf (u.getD (j.val / m) (zeroLetter m))
        ⟨j.val % m, Nat.mod_lt _ hpos⟩
    else false

/-- Flattening the word produced by a vector returns that vector. -/
theorem wordVec_vecWord (Q m : Nat) (a : Fin (Q * m) → Bool) :
    wordVec Q m (vecWord Q m a) = a := by
  funext j
  by_cases hm : 0 < m
  · unfold wordVec
    rw [dif_pos hm]
    have hr : j.val / m < Q :=
      Nat.div_lt_of_lt_mul
        (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm Q m))
    let r : Fin Q := ⟨j.val / m, hr⟩
    let i : Fin m := ⟨j.val % m, Nat.mod_lt _ hm⟩
    change
      bitsOf ((vecWord Q m a).getD r.val (zeroLetter m)) i = a j
    rw [vecWord_getD]
    have hbit := congrFun
      (bitsOf_encodeBits (fun k : Fin m => a (blockIndex r k))) i
    rw [hbit]
    apply congrArg a
    apply Fin.ext
    change r.val * m + i.val = j.val
    dsimp [r, i]
    calc
      (j.val / m) * m + j.val % m =
          m * (j.val / m) + j.val % m := by
            rw [Nat.mul_comm (j.val / m) m]
      _ = j.val := Nat.div_add_mod j.val m
  · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have hfalse : False := by
      simpa using j.isLt
    exact hfalse.elim

private theorem wordVec_block {Q m : Nat} (hm : 0 < m)
    (u : List (Fin (2 ^ m))) (r : Fin Q) :
    (fun i : Fin m => wordVec Q m u (blockIndex r i)) =
      bitsOf (u.getD r.val (zeroLetter m)) := by
  funext i
  unfold wordVec
  rw [dif_pos hm]
  have hdiv : (r.val * m + i.val) / m = r.val := by
    rw [Nat.mul_comm r.val m, Nat.mul_add_div hm,
      Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hmod : (r.val * m + i.val) % m = i.val := by
    rw [Nat.mul_comm r.val m, Nat.mul_add_mod,
      Nat.mod_eq_of_lt i.isLt]
  change
    bitsOf (u.getD ((r.val * m + i.val) / m) (zeroLetter m))
        ⟨(r.val * m + i.val) % m, Nat.mod_lt _ hm⟩ =
      bitsOf (u.getD r.val (zeroLetter m)) i
  rw [hdiv]
  have hfin :
      (⟨(r.val * m + i.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = i :=
    Fin.ext hmod
  rw [hfin]

/-- Every word of length `Q` is recovered after flattening and re-encoding. -/
theorem vecWord_wordVec (Q m : Nat) (u : List (Fin (2 ^ m)))
    (hu : u.length = Q) :
    vecWord Q m (wordVec Q m u) = u := by
  by_cases hm : 0 < m
  · apply List.ext_getElem
    · simpa only [vecWord_length] using hu.symm
    · intro r hleft hright
      have hrQ : r < Q := by
        simpa only [vecWord_length] using hleft
      let rf : Fin Q := ⟨r, hrQ⟩
      calc
        (vecWord Q m (wordVec Q m u))[r] =
            (vecWord Q m (wordVec Q m u)).getD r (zeroLetter m) :=
          List.getElem_eq_getD
            (l := vecWord Q m (wordVec Q m u))
            (i := r) (h := hleft) (zeroLetter m)
        _ = encodeBits
              (fun i : Fin m => wordVec Q m u (blockIndex rf i)) := by
          simpa [rf] using
            (vecWord_getD (a := wordVec Q m u) rf)
        _ = encodeBits (bitsOf (u.getD r (zeroLetter m))) := by
          have hb := wordVec_block hm u rf
          have hb' :
              (fun i : Fin m => wordVec Q m u (blockIndex rf i)) =
                bitsOf (u.getD r (zeroLetter m)) := by
            simpa [rf] using hb
          exact congrArg encodeBits hb'
        _ = u.getD r (zeroLetter m) :=
          encodeBits_bitsOf (u.getD r (zeroLetter m))
        _ = u[r] :=
          (List.getElem_eq_getD
            (l := u) (i := r) (h := hright) (zeroLetter m)).symm
  · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    apply List.ext_getElem
    · simpa only [vecWord_length] using hu.symm
    · intro r hleft hright
      apply Fin.ext
      have hl := (vecWord Q 0 (wordVec Q 0 u))[r].isLt
      have hr := u[r].isLt
      simp only [Nat.pow_zero] at hl hr
      omega

/-- `vecWord` is injective. -/
theorem vecWord_injective (Q m : Nat) :
    Function.Injective (vecWord Q m) := by
  intro a b hab
  calc
    a = wordVec Q m (vecWord Q m a) :=
      (wordVec_vecWord Q m a).symm
    _ = wordVec Q m (vecWord Q m b) := congrArg (wordVec Q m) hab
    _ = b := wordVec_vecWord Q m b

/-- `vecWord` is a bijection from flattened vectors onto words of length `Q`:
every such word has exactly one preimage. -/
theorem vec_word_bij (Q m : Nat) :
    ∀ u : List (Fin (2 ^ m)), u.length = Q →
      ∃ a : Fin (Q * m) → Bool,
        vecWord Q m a = u ∧
          ∀ b : Fin (Q * m) → Bool,
            vecWord Q m b = u → b = a := by
  intro u hu
  refine ⟨wordVec Q m u, vecWord_wordVec Q m u hu, ?_⟩
  intro a ha
  apply vecWord_injective Q m
  calc
    vecWord Q m a = u := ha
    _ = vecWord Q m (wordVec Q m u) :=
      (vecWord_wordVec Q m u hu).symm

/-! ## Exact finite counting -/

private theorem map_nodup_of_injective {α β : Type}
    (f : α → β) (hf : Function.Injective f) :
    ∀ xs : List α, xs.Nodup → (xs.map f).Nodup := by
  intro xs hxs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hcons := List.nodup_cons.mp hxs
      simp only [List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        have hyx : y = x := hf hfy
        subst y
        exact hcons.1 hy
      · exact ih hcons.2

/-- Core-only `flatMap` nodup criterion, specialized later to word blocks. -/
private theorem nodup_flatMap_of_nodup
    {α β : Type} (xs : List α) (f : α → List β)
    (hxs : xs.Nodup)
    (hfn : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisjoint : ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
      ∀ a, a ∈ f x → ∀ b, b ∈ f y → a ≠ b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨hfn x (by simp), ?_, ?_⟩
      · apply ih hxs.2
        · intro y hy
          exact hfn y (by simp [hy])
        · intro y hy z hz hyz
          exact hdisjoint y (by simp [hy]) z (by simp [hz]) hyz
      · intro a ha b hb
        rw [List.mem_flatMap] at hb
        obtain ⟨y, hy, hby⟩ := hb
        apply hdisjoint x (by simp) y (by simp [hy])
        · intro hxy
          exact hxs.1 (hxy ▸ hy)
        · exact ha
        · exact hby

/-- Canonical duplicate-free enumeration of all words of length `q`. -/
private def allWords (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | q + 1 =>
      (List.ofFn (fun e : Fin n => e)).flatMap
        (fun e => (allWords n q).map (fun u => e :: u))

private theorem mem_allWords_iff {n : Nat} :
    ∀ (q : Nat) (u : List (Fin n)),
      u ∈ allWords n q ↔ u.length = q := by
  intro q
  induction q with
  | zero =>
      intro u
      simp [allWords]
  | succ q ih =>
      intro u
      constructor
      · intro hu
        rw [allWords] at hu
        obtain ⟨e, he, hem⟩ := List.mem_flatMap.mp hu
        obtain ⟨v, hv, hev⟩ := List.mem_map.mp hem
        rw [← hev]
        simp only [List.length_cons]
        exact congrArg Nat.succ ((ih v).1 hv)
      · intro hu
        cases u with
        | nil =>
            simp at hu
        | cons e v =>
            have hvlen : v.length = q := by
              simp only [List.length_cons] at hu
              omega
            rw [allWords]
            apply List.mem_flatMap.mpr
            refine ⟨e, List.mem_ofFn.mpr ⟨e, rfl⟩, ?_⟩
            apply List.mem_map.mpr
            exact ⟨v, (ih v).2 hvlen, rfl⟩

private theorem allWords_nodup (n : Nat) :
    ∀ q : Nat, (allWords n q).Nodup := by
  intro q
  induction q with
  | zero =>
      simp [allWords]
  | succ q ih =>
      rw [allWords]
      apply nodup_flatMap_of_nodup
        (List.ofFn (fun e : Fin n => e))
        (fun e => (allWords n q).map (fun u => e :: u))
      · exact ofFn_nodup_of_injective n
          (fun e : Fin n => e) (fun _ _ h => h)
      · intro e he
        exact map_nodup_of_injective
          (fun u : List (Fin n) => e :: u)
          (by
            intro u v huv
            exact (List.cons.inj huv).2)
          (allWords n q) ih
      · intro e he e' he' hne w hw w' hw' hww'
        obtain ⟨u, hu, hwu⟩ := List.mem_map.mp hw
        obtain ⟨v, hv, hwv⟩ := List.mem_map.mp hw'
        have hlist : e :: u = e' :: v :=
          hwu.trans (hww'.trans hwv.symm)
        have hhead : e = e' := (List.cons.inj hlist).1
        exact hne hhead

private theorem sum_flatMap_map {α β : Type}
    (xs : List α) (ys : α → List β) (f : β → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]

private theorem wordSum_eq_allWords_sum {n : Nat} :
    ∀ (q : Nat) (f : List (Fin n) → Nat),
      wordSum f q = ((allWords n q).map f).sum := by
  intro q
  induction q with
  | zero =>
      intro f
      simp [wordSum, allWords]
  | succ q ih =>
      intro f
      calc
        wordSum f (q + 1) =
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) q)).sum := rfl
        _ = (List.ofFn (fun e : Fin n =>
              (((allWords n q).map (fun v => e :: v)).map f).sum)).sum := by
              apply sum_ofFn_eq
              intro e
              simpa [List.map_map, Function.comp_def] using
                ih (fun v => f (e :: v))
        _ = (((List.ofFn (fun e : Fin n => e)).flatMap
              (fun e => (allWords n q).map (fun v => e :: v))).map f).sum := by
              symm
              rw [sum_flatMap_map]
              simp only [List.map_ofFn, Function.comp_def]
        _ = ((allWords n (q + 1)).map f).sum := rfl

/-- The words obtained by encoding all flattened vectors. -/
private def vectorWords (Q m : Nat) : List (List (Fin (2 ^ m))) :=
  (allVectors (Q * m)).map (vecWord Q m)

private theorem vectorWords_nodup (Q m : Nat) :
    (vectorWords Q m).Nodup := by
  unfold vectorWords
  exact map_nodup_of_injective (vecWord Q m)
    (vecWord_injective Q m) (allVectors (Q * m))
    (allVectors_nodup (Q * m))

private theorem mem_vectorWords_iff (Q m : Nat)
    (u : List (Fin (2 ^ m))) :
    u ∈ vectorWords Q m ↔ u.length = Q := by
  constructor
  · intro hu
    unfold vectorWords at hu
    obtain ⟨a, ha, hau⟩ := List.mem_map.mp hu
    rw [← hau]
    exact vecWord_length Q m a
  · intro hu
    obtain ⟨a, ha, _huniq⟩ := vec_word_bij Q m u hu
    unfold vectorWords
    apply List.mem_map.mpr
    exact ⟨a, mem_allVectors a, ha⟩

private theorem vectorWords_perm_allWords (Q m : Nat) :
    (vectorWords Q m).Perm (allWords (2 ^ m) Q) := by
  apply (List.perm_ext_iff_of_nodup
    (vectorWords_nodup Q m) (allWords_nodup (2 ^ m) Q)).2
  intro u
  exact (mem_vectorWords_iff Q m u).trans
    (mem_allWords_iff (n := 2 ^ m) Q u).symm

private theorem vector_sum_eq_wordSum (Q m : Nat)
    (f : List (Fin (2 ^ m)) → Nat) :
    ((allVectors (Q * m)).map (fun a => f (vecWord Q m a))).sum =
      wordSum f Q := by
  have hp := (vectorWords_perm_allWords Q m).map f
  have hs := List.Perm.sum_nat hp
  calc
    ((allVectors (Q * m)).map (fun a => f (vecWord Q m a))).sum =
        ((vectorWords Q m).map f).sum := by
          simp [vectorWords, List.map_map, Function.comp_def]
    _ = ((allWords (2 ^ m) Q).map f).sum := hs
    _ = wordSum f Q :=
      (wordSum_eq_allWords_sum (n := 2 ^ m) Q f).symm

private theorem filter_length_eq_indicator_sum {α : Type}
    (P : α → Prop) [DecidablePred P] :
    ∀ xs : List α,
      (xs.filter P).length =
        (xs.map (fun x => if P x then 1 else 0)).sum := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : P x
      · simp [hx, ih, Nat.add_comm]
      · simp [hx, ih]

private theorem badVectorCount_eq_wordSum {m : Nat}
    (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot) (Q : Nat) :
    ((allVectors (Q * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds Q m a) s) ≠ 1)).length =
      wordSum
        (fun u => if anchorCount hm
          (runWord (heightChain B hm) s u) = 1 then 0 else 1) Q := by
  calc
    ((allVectors (Q * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds Q m a) s) ≠ 1)).length =
        ((allVectors (Q * m)).map
          (fun a => if anchorCount hm
            (runRounds B hm (vecRounds Q m a) s) ≠ 1
            then 1 else 0)).sum :=
      filter_length_eq_indicator_sum
        (fun a => anchorCount hm
          (runRounds B hm (vecRounds Q m a) s) ≠ 1)
        (allVectors (Q * m))
    _ = ((allVectors (Q * m)).map
          (fun a => if anchorCount hm
            (runWord (heightChain B hm) s (vecWord Q m a)) = 1
            then 0 else 1)).sum := by
      apply list_sum_congr
      intro a ha
      rw [runWord_vecWord (m := m) B hm s Q a]
      by_cases hone :
          anchorCount hm
            (runRounds B hm (vecRounds Q m a) s) = 1
      · simp [hone]
      · simp [hone]
    _ = wordSum
          (fun u => if anchorCount hm
            (runWord (heightChain B hm) s u) = 1 then 0 else 1) Q :=
      vector_sum_eq_wordSum Q m
        (fun u => if anchorCount hm
          (runWord (heightChain B hm) s u) = 1 then 0 else 1)

/-- At `Q = 2^19*m`, at most one quarter of the flattened bit vectors fail
to produce exactly one anchor. -/
theorem logical_quarter_vectors {m B : Nat}
    (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s) :
    4 * ((allVectors ((2 ^ 19 * m) * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds (2 ^ 19 * m) m a) s) ≠ 1)).length ≤
      2 ^ ((2 ^ 19 * m) * m) := by
  let Q : Nat := 2 ^ 19 * m
  change
    4 * ((allVectors (Q * m)).filter
      (fun a => anchorCount hm
        (runRounds B hm (vecRounds Q m a) s) ≠ 1)).length ≤
      2 ^ (Q * m)
  have hcount := badVectorCount_eq_wordSum B hm s Q
  have hquarter := logical_quarter hm hmb s hs
    (anchor_contraction B hm hmb s hs)
  have hpow : (2 ^ m) ^ Q = 2 ^ (Q * m) := by
    calc
      (2 ^ m) ^ Q = 2 ^ (m * Q) := (Nat.pow_mul 2 m Q).symm
      _ = 2 ^ (Q * m) := by rw [Nat.mul_comm m Q]
  calc
    4 * ((allVectors (Q * m)).filter
        (fun a => anchorCount hm
          (runRounds B hm (vecRounds Q m a) s) ≠ 1)).length =
        4 * wordSum
          (fun u => if anchorCount hm
            (runWord (heightChain B hm) s u) = 1 then 0 else 1) Q :=
      congrArg (fun z : Nat => 4 * z) hcount
    _ ≤ (2 ^ m) ^ Q := by
      simpa only [Q] using hquarter
    _ = 2 ^ (Q * m) := hpow

end

end L4.Height

