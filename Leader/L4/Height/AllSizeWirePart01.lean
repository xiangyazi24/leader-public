import Leader.L4.Height.AllSizeWirePart00
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section PublicationService

variable {S : Type} {n : Nat}

/-- A word publishes at `i` when the edge initiated by `i` makes a
publication at `i` on the raw state reached by its preceding letters. -/
def publishes (next : (Fin n → S) → Fin n → (Fin n → S))
    (publication : (Fin n → S) → Fin n → Fin n → Prop)
    (x : Fin n → S) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∃ pre post : List (Fin n),
    w = pre ++ i :: post ∧ publication (runWord next x pre) i i

/-- The two steering intervals have total length `2 * (2^20 * n * W)`.
The count is over the original raw-edge alphabet from each custody cut. -/
noncomputable def StrictPublicationBlock (D : AllSizeData S n) (hn : 0 < n)
    (publication : (Fin n → S) → Fin n → Fin n → Prop)
    (header : ∀ j, Fin (D.m j) → Fin n) : Prop :=
  ∀ j i z,
    let W := D.width j
    let T := 2^20 * n * W
    2^(5*(2^32 : Nat)+1) *
        wordSum (fun w => if publishes (D.next hn) publication
          (D.raw j z) (header j i) w then 1 else 0) (2*T) ≥ n^(2*T)

/-- Executing the same raw letters on a chart projects to the pair rule. -/
theorem publication_run_projects (D : AllSizeData S n) (hn : 0 < n)
    (rawStep : ∀ j z e, D.raw j ((D.clock j).next z e) = D.next hn (D.raw j z) e)
    (j : D.Chart) (z : D.State j) (w : List (Fin n)) :
    D.raw j (Thru.runWord (D.clock j).next z w) =
      runWord (D.next hn) (D.raw j z) w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    change D.raw j (Thru.runWord (D.clock j).next ((D.clock j).next z e) w) =
      runWord (D.next hn) (D.next hn (D.raw j z) e) w
    rw [ih, rawStep]

theorem publication_run_snoc {X : Type}
    (next : X → Fin n → X) (x : X) (w : List (Fin n)) (e : Fin n) :
    Thru.runWord next x (w ++ [e]) = next (Thru.runWord next x w) e := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => exact ih (next x a)

/-- A chart's last-publication field detects a genuine raw event on each
step, including a publication that leaves the native record unchanged. -/
theorem served_next_iff_publication {X : Type} {m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain X n m B M hm) (z : X) (e : Fin n) (i : Fin m) :
    C.served i (C.next z e) ↔ ∃ b, C.act z e = some (i,b) := by
  unfold Recover.Chain.ClockChain.served
  rw [C.last_next]
  cases ha : C.act z e with
  | none => simp
  | some p =>
    rcases p with ⟨j,b⟩
    change some j = some i ↔ ∃ c, some (j,b) = some (i,c)
    constructor
    · intro h
      cases Option.some.inj h
      exact ⟨b, rfl⟩
    · rintro ⟨c, hc⟩
      exact congrArg (fun p : Fin m × Bool => some p.1) (Option.some.inj hc)

/-- Split a positive publication prefix at the exact letter ending it.
An event registered before the cut is excluded by the positive prefix. -/
theorem publication_prefix_iff (D : AllSizeData S n) (hn : 0 < n)
    (publication : (Fin n → S) → Fin n → Fin n → Prop)
    (header : ∀ j, Fin (D.m j) → Fin n)
    (rawStep : ∀ j z e, D.raw j ((D.clock j).next z e) = D.next hn (D.raw j z) e)
    (actMatches : ∀ j z (e : Fin n) i,
      (∃ b, (D.clock j).act z e = some (i,b)) ↔
        e = header j i ∧ publication (D.raw j z) e e)
    (j : D.Chart) (i : Fin (D.m j)) (z : D.State j) (w : List (Fin n)) :
    RawService.hasPublication (D.clock j).next ((D.clock j).served i) z w ↔
      publishes (D.next hn) publication (D.raw j z) (header j i) w := by
  constructor
  · rintro ⟨k, hk, hw, hs⟩
    obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    have hq : q < w.length := by omega
    let y := Thru.runWord (D.clock j).next z (w.take q)
    have hy : (D.clock j).served i ((D.clock j).next y w[q]) := by
      rw [List.take_succ_eq_append_getElem hq, publication_run_snoc] at hs
      exact hs
    obtain ⟨he, hp⟩ := (actMatches j y w[q] i).1
      ((served_next_iff_publication (D.clock j) y w[q] i).1 hy)
    refine ⟨w.take q, w.drop (q+1), ?_, ?_⟩
    · calc
        w = w.take (q+1) ++ w.drop (q+1) := (List.take_append_drop _ _).symm
        _ = w.take q ++ header j i :: w.drop (q+1) := by
          rw [List.take_succ_eq_append_getElem hq, he, List.append_assoc,
            List.cons_append, List.nil_append]
    · rw [← publication_run_projects D hn rawStep, ← he]
      exact hp
  · rintro ⟨pre, post, rfl, hp⟩
    have hlen : pre.length + 1 ≤ (pre ++ header j i :: post).length := by
      simp only [List.length_append, List.length_cons]
      omega
    refine ⟨pre.length+1, by omega, hlen, ?_⟩
    have ht : (pre ++ header j i :: post).take (pre.length+1) = pre ++ [header j i] := by
      simp [List.take_append, List.take_of_length_le (Nat.le_succ pre.length)]
    rw [ht, publication_run_snoc, served_next_iff_publication, actMatches]
    exact ⟨rfl, by rwa [publication_run_projects D hn rawStep]⟩

/-- Transport the strict physical block count to the chart without changing
the scheduler alphabet or treating its publication list as an IID word. -/
theorem service_of_strict_publication_block (D : AllSizeData S n) (hn : 0 < n)
    (publication : (Fin n → S) → Fin n → Fin n → Prop)
    (header : ∀ j, Fin (D.m j) → Fin n)
    (rawStep : ∀ j z e, D.raw j ((D.clock j).next z e) = D.next hn (D.raw j z) e)
    (actMatches : ∀ j z (e : Fin n) i,
      (∃ b, (D.clock j).act z e = some (i,b)) ↔
        e = header j i ∧ publication (D.raw j z) e e)
    (hStrict : StrictPublicationBlock D hn publication header) :
    ∀ j i z, n^(D.block j) ≤ 2^(5*(2^32 : Nat)+1) *
      RawService.publicationMass (D.clock j).next ((D.clock j).served i) z (D.block j) := by
  classical
  intro j i z
  rw [RawService.publicationMass_eq_prefix, ← repair_wordSum_eq_thru]
  have heq :
      (fun w => if RawService.hasPublication (D.clock j).next ((D.clock j).served i) z w
        then 1 else 0) =
      (fun w => if publishes (D.next hn) publication (D.raw j z) (header j i) w
        then 1 else 0) := by
    funext w
    have h := publication_prefix_iff D hn publication header rawStep actMatches j i z w
    by_cases hp : publishes (D.next hn) publication (D.raw j z) (header j i) w
    · simp only [if_pos hp, if_pos (h.mpr hp)]
    · simp only [if_neg hp, if_neg (fun hs => hp (h.mp hs))]
  rw [heq]
  have hblock : D.block j = 2 * (2^20 * n * D.width j) := by
    change 2^21 * n * D.width j = _
    rw [Nat.pow_succ 2 20]
    ac_rfl
  rw [hblock]
  exact hStrict j i z

/-- The maximum actual owner width fits the service scale. -/
theorem parameters_of_packing (D : AllSizeData S n) (hn : 0 < n) (bL : Nat)
    (hClock : Recover.StageTwo.ClockParams (modulus D.r))
    (hDiameter : ∀ j, D.m j / 2 < modulus D.r / 2)
    (hWidthPos : ∀ j, 0 < D.width j) (hWidthBound : ∀ j, D.width j ≤ 1024 * D.r)
    (hPacked : ∀ j, D.m j * D.r ≤ n) :
    ∀ j : D.Chart, Recover.StageTwo.ClockParams (modulus D.r) ∧
      D.m j / 2 < modulus D.r / 2 ∧ 0 < D.block j ∧
      4 * (2^(5*bL+1) * D.block j) ≤ D.scale bL ∧ D.m j * D.r ≤ n := by
  intro j
  refine ⟨hClock, hDiameter j, Nat.mul_pos (Nat.mul_pos (by decide) hn) (hWidthPos j),
    ?_, hPacked j⟩
  calc
    4 * (2^(5*bL+1) * D.block j) =
        (4 * 2^(5*bL+1) * 2^21) * n * D.width j := by
      unfold AllSizeData.block
      ac_rfl
    _ ≤ (4 * 2^(5*bL+1) * 2^21) * n * (1024 * D.r) :=
      Nat.mul_le_mul_left _ (hWidthBound j)
    _ = D.scale bL := by
      unfold AllSizeData.scale
      change (2^2 * 2^(5*bL+1) * 2^21) * n * (2^10 * D.r) =
        2^(5*bL+34) * n * D.r
      have hpow : 2^2 * 2^(5*bL+1) * 2^21 * 2^10 = 2^(5*bL+34) := by
        rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
        congr 1 <;> omega
      calc
        _ = (2^2 * 2^(5*bL+1) * 2^21 * 2^10) * n * D.r := by ac_rfl
        _ = _ := by rw [hpow]

/-- The double-ceiling-log advice provides enough modulus for every
chart packed at the deployed radius. -/
theorem packed_modulus_parameters (D : AllSizeData S n) (hfour : 4 ≤ n)
    (hRadius : D.r = 2 ^ ceilingLogTwo (ceilingLogTwo n) - 1)
    (hPacked : ∀ j, D.m j * D.r ≤ n) :
    Recover.StageTwo.ClockParams (modulus D.r) ∧
      ∀ j, D.m j < modulus D.r / 2 := by
  let q := ceilingLogTwo n
  let s := ceilingLogTwo q
  have hnq : n ≤ 2 ^ q := (ceilingLogTwo_spec n (by omega)).2
  have hq : 2 ≤ q := by
    by_cases h : 2 ≤ q
    · exact h
    · have hpow : 2 ^ q ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
      have hsmall : n ≤ 2 := Nat.le_trans hnq hpow
      omega
  have hqs : q ≤ 2 ^ s := (ceilingLogTwo_spec q hq).2
  change D.r = 2 ^ s - 1 at hRadius
  have hr : 1 ≤ D.r := by omega
  have hqr : q ≤ D.r + 1 := by omega
  have hnm : 4 * n ≤ modulus D.r := by
    calc
      4 * n ≤ 4 * 2 ^ q := Nat.mul_le_mul_left 4 hnq
      _ = 2 ^ (q + 2) := by
        rw [Nat.pow_add]
        exact Nat.mul_comm (2 ^ 2) (2 ^ q)
      _ ≤ 2 ^ (4 * D.r) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = modulus D.r := by rw [Nat.pow_mul, modulus]
  have heven : modulus D.r = 16 ^ (D.r - 1) * 16 := by
    unfold modulus
    have he : D.r - 1 + 1 = D.r := by omega
    calc
      16 ^ D.r = 16 ^ (D.r - 1 + 1) := congrArg (fun k : Nat => 16 ^ k) he.symm
      _ = 16 ^ (D.r - 1) * 16 := Nat.pow_succ 16 (D.r - 1)
  have hClock : Recover.StageTwo.ClockParams (modulus D.r) := by
    unfold Recover.StageTwo.ClockParams
    omega
  refine ⟨hClock, ?_⟩
  intro j
  have hm : D.m j ≤ n := by
    have hmul := Nat.mul_le_mul_left (D.m j) hr
    rw [Nat.mul_one] at hmul
    exact Nat.le_trans hmul (hPacked j)
  omega

/-- The half-diameter inequality can hold even when the header count
exceeds the available half-period residues. -/
theorem half_diameter_counterexample :
    (200 : Nat) / 2 < 256 / 2 ∧ ¬ (200 : Nat) < 256 / 2 := by
  decide

end PublicationService

end L4.Height.AllSizeWire
