import Leader.L4.Count
import Leader.L4.RootedProduct

/-! The total 48-bit bounded physical branch. -/
namespace L4.BoundedPublicCodec

def boundedN : Nat := 2^32
def boundedP : Nat := boundedN + 1
abbrev BoundedCode := Fin (2^48)
abbrev BoundedRaw (n : Nat) := Fin n → BoundedCode

private theorem rank_positive : 0 < stateCount boundedP 12 := by decide
private theorem rank_fits : stateCount boundedP 12 < 2^48 := by decide

/-- Pad the public mixed-radix rank to the bounded physical alphabet. -/
def boundedEncode (x : Site boundedP 12) : BoundedCode :=
  let code := (stateCoding boundedP 12).encode x
  ⟨code.val, Nat.lt_trans code.isLt rank_fits⟩

/-- Every spare rank decodes as the rank-zero public site. -/
def boundedDecode (x : BoundedCode) : Site boundedP 12 :=
  let coding := stateCoding boundedP 12
  if h : x.val < stateCount boundedP 12 then coding.decode ⟨x.val, h⟩
  else coding.decode ⟨0, rank_positive⟩

theorem boundedDecode_encode (x : Site boundedP 12) : boundedDecode (boundedEncode x) = x := by
  let coding := stateCoding boundedP 12
  let rank := coding.encode x
  change (if h : rank.val < stateCount boundedP 12 then
    coding.decode ⟨rank.val, h⟩ else coding.decode ⟨0, rank_positive⟩) = x
  rw [dif_pos rank.isLt]
  exact coding.left_inv x

theorem boundedDecode_spare (x : BoundedCode) (h : stateCount boundedP 12 ≤ x.val) :
    boundedDecode x = (stateCoding boundedP 12).decode ⟨0, rank_positive⟩ := by
  unfold boundedDecode
  rw [dif_neg (Nat.not_lt_of_ge h)]

def boundedPair (u v : BoundedCode) : BoundedCode × BoundedCode :=
  let y := pairStep (boundedDecode u) (boundedDecode v)
  (boundedEncode y.1, boundedEncode y.2)

def boundedNext {n : Nat} (x : BoundedRaw n) (e : Fin n) : BoundedRaw n :=
  let j := rightNeighbor e
  let pair := boundedPair (x e) (x j)
  fun i => if i = e then pair.1 else if i = j then pair.2 else x i

def boundedProject {n : Nat} (x : BoundedRaw n) : Config boundedP 12 n :=
  fun i => boundedDecode (x i)

def boundedLeader {n : Nat} (x : BoundedRaw n) (i : Fin n) : Bool :=
  (boundedProject x i).leader

def BoundedElected {n : Nat} (x : BoundedRaw n) : Prop :=
  RootedProduct.ProductSafe boundedNext boundedLeader x

/-- The ordinary pair acts on the decoded sites of each literal raw edge.
Untouched spare codes are retained by the raw step. -/
theorem bounded_projects {n : Nat} (x : BoundedRaw n) (e : Fin n) :
    boundedProject (boundedNext x e) = step (boundedProject x) e := by
  funext i
  by_cases he : i = e
  · simp [boundedProject, boundedNext, boundedPair, step, he, boundedDecode_encode]
  · by_cases hj : i = rightNeighbor e
    · have hne : rightNeighbor e ≠ e := hj ▸ he
      subst i
      simp only [boundedProject, boundedNext, boundedPair, step,
        if_neg hne, if_true, boundedDecode_encode]
    · simp [boundedProject, boundedNext, step, he, hj]


theorem bounded_rank_size : stateCount boundedP 12 = 51408 * (2^32 + 1) := by decide

/-- Literal regression: the highest raw code is spare and decodes to rank zero. -/
theorem top_code_spare :
    boundedDecode (⟨2^48-1, by decide⟩ : BoundedCode) =
      (stateCoding boundedP 12).decode ⟨0, rank_positive⟩ :=
  boundedDecode_spare _ (by decide)

/-- Non-endpoints preserve their raw code even when it is a spare. -/
theorem boundedNext_off_edge {n : Nat} (x : BoundedRaw n) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ rightNeighbor e) :
    boundedNext x e i = x i := by
  simp [boundedNext, hi, hj]

/-- Literal integration regression: the mark 0→1 does not normalize the
highest spare code at the untouched site 2 on a four-site ring. -/
theorem top_code_off_edge :
    let top : BoundedCode := ⟨2^48-1, by decide⟩
    boundedNext (n := 4) (fun _ => top) 0 2 = top :=
  boundedNext_off_edge _ _ _ (by decide) (by decide)

#print axioms top_code_off_edge
#print axioms boundedDecode_encode
#print axioms boundedDecode_spare
#print axioms bounded_projects
#print axioms bounded_rank_size
#print axioms top_code_spare
#print axioms boundedNext_off_edge

end L4.BoundedPublicCodec
