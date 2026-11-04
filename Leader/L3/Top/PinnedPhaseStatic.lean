import Leader.L3.Top.PinnedPhaseCertificate
import Leader.L3.Top.PinnedPhaseFillCost

/-!
# Q7 (P.12 preparation, lemma 2): the static data of an aligned window

At an aligned labelled state the `r` registers hold the `r` consecutive samples
`sam 0 .. sam (r-1)` (the tail at the border, site `s + j` at register `j`), carried by the exports
with indices `k0 + (r - 1 - j)` of the accepted queue.  This module extracts the static data of the
strict-terminal certificate from the labelled window invariant.

Consumer: `Leader/L3/Top/PinnedPhaseSweepCost.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The frame log carries sampled atoms made strictly before their exports.

Consumer: `export_atom_lt`. -/
def AtomLt {n : Nat} (Z : TopFixedTraceState n) : Prop :=
  ∀ f ∈ Z.1.2.frames, ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
    (digitReceiptLane .comparison f.receipt).exported = some x →
    ∀ id, x.operand = some (.sampled id) → id.time < x.time

/-- One letter keeps the frame-log property of a reached state.

Consumer: `export_atom_lt`. -/
theorem atomLt_next {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n) (hreach : topClockReached ring C Z) (ih : AtomLt Z) :
    AtomLt (topFixedTraceNext ring C Z e) := by
  intro f hf x hx id hid
  obtain ⟨F, hF1, hF2⟩ : ∃ F : DigitFrame (compileAdvice (ceilLogTwo n)) n,
      (topFixedTraceNext ring C Z e).1.2.frames = F :: Z.1.2.frames ∧
      (digitReceiptLane .comparison F.receipt).exported = (traceReplay ring Z e).exported :=
    ⟨_, rfl, rfl⟩
  rw [hF1] at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [hF2] at hx
    obtain ⟨_, _, hxt, hxo, _⟩ := replay_exported_fields (c := compileAdvice (ceilLogTwo n))
      .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e) _ _ _ _ x hx
    have hlin := lin_reached ring C hn Z hreach
    have := hlin.tOut e id (by
      unfold cmpOut
      rw [hxo] at hid
      exact hid)
    rw [hxt]
    omega
  · exact ih f hf x hx id hid

/-- **An export carries a sampled atom made strictly before the export.**

Consumer: `static_of_aligned`. -/
theorem export_atom_lt {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (C : HeadlineConfiguration n)
    (w : List (Fin n)) : AtomLt (topFixedTraceRun ring C w) := by
  have key : ∀ (v : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      AtomLt Z → AtomLt (v.foldl (topFixedTraceNext ring C) Z) := by
    intro v
    induction v with
    | nil => intro Z _ h; exact h
    | cons e v ih =>
        intro Z hr h
        exact ih _ (topClockReachedNext ring C Z e hr) (atomLt_next ring hn C Z e hr h)
  unfold topFixedTraceRun
  exact key w _ rfl (fun f hf => absurd hf (by simp [digitAuditInitial]))

/-- **The export and sample of a flagged register.**  Register `j` of a window whose registers
`[h, r)` are all flagged holds the operand of the export of index `k0 + (r - 1 - j)`.

Consumer: `static_of_aligned`. -/
theorem labelled_export {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat) (k0 : Nat)
    (hlist : ordLab (paFlagSettled s Y τ) (paLabSettled s Y) (topClockSpan n) =
      (paQ s Y τ).drop k0)
    (h : Nat) (hflag : ∀ j, h ≤ j → j < topClockSpan n → paFlagSettled s Y τ j = true)
    (j : Nat) (hj1 : h ≤ j) (hj2 : j < topClockSpan n) :
    ∃ (hi : k0 + (topClockSpan n - 1 - j) < (topClockConcreteExportsAfter s Y τ).length),
      (Y.1.2.current (winSite s j)).comparison.input =
        (topClockConcreteExportsAfter s Y τ)[k0 + (topClockSpan n - 1 - j)].operand ∧
      puTok (Y.1.1 (winSite s j)).qIn =
        InTok.P (topClockConcreteExportsAfter s Y τ)[k0 + (topClockSpan n - 1 - j)].value
          (topClockConcreteExportsAfter s Y τ)[k0 + (topClockSpan n - 1 - j)].tail := by
  have hget := ordLab_get_all (paFlagSettled s Y τ) (paLabSettled s Y) h (topClockSpan n) hflag j
    hj1 hj2
  rw [hlist, List.getElem?_drop] at hget
  unfold paQ at hget
  rw [List.getElem?_map] at hget
  rcases hE : (topClockConcreteExportsAfter s Y τ)[k0 + (topClockSpan n - 1 - j)]? with _ | ex
  · rw [hE] at hget; simp at hget
  · rw [hE] at hget
    simp only [Option.map_some] at hget
    have hlab := Option.some.inj hget
    obtain ⟨hi, hex⟩ := List.getElem?_eq_some_iff.1 hE
    refine ⟨hi, ?_, ?_⟩
    · have := congrArg Prod.fst hlab
      simp only [paLabSettled] at this
      rw [hex, ← this]
    · have := congrArg Prod.snd hlab
      simp only [paLabSettled] at this
      rw [hex]
      exact this.symm

/-- A function from a family of existence statements.

Consumer: `static_of_aligned`. -/
theorem exists_fun_two {α β : Type} (P : Nat → α → β → Prop) (m : Nat) (hm : 0 < m)
    (h : ∀ j, j < m → ∃ a b, P j a b) :
    ∃ (f : Nat → α) (g : Nat → β), ∀ j, j < m → P j (f j) (g j) := by
  obtain ⟨a0, b0, _⟩ := h 0 hm
  refine ⟨fun j => if hj : j < m then Classical.choose (h j hj) else a0,
    fun j => if hj : j < m then Classical.choose (Classical.choose_spec (h j hj)) else b0, ?_⟩
  intro j hj
  simp only [hj, dif_pos]
  exact Classical.choose_spec (Classical.choose_spec (h j hj))

/-- The static data of register `j`: its sample, its export and its checker data.

Consumer: `static_of_aligned`. -/
def StaticAt {n : Nat} (s : Fin n) (Yl : TopFixedTraceState n) (τ k0 j : Nat)
    (sm : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (ex : DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (DigitRecordedSample Yl.1.2 sm ∧ sm.id.lane = .comparison ∧ sm.id.site = certSite s j ∧
    0 < sm.id.time ∧ sm.tail = decide (j = 0)) ∧
  (DigitRecordedExport Yl.1.2 ex ∧ ex.lane = .comparison ∧
    ex.source = certSite s (topClockSpan n - 1) ∧ ex.destination = certSite s (topClockSpan n) ∧
    ex.operand = some (.sampled sm.id) ∧ ex.value = sm.value ∧ ex.tail = sm.tail ∧
    sm.id.time < ex.time ∧ ex.time ≤ Yl.1.2.clock) ∧
  (topClockConcreteExportsAfter s Yl τ)[k0 + (topClockSpan n - 1 - j)]? = some ex ∧
  ((Yl.1.1 (winSite s j)).qIn = .S sm.value sm.tail ∧ (Yl.1.1 (winSite s j)).qCarry = .OFF ∧
    (Yl.1.2.current (winSite s j)).comparison.input = some (.sampled sm.id))

/-- **The static data of an aligned labelled window.**

Consumer: `sweep_init`. -/
theorem static_of_aligned {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 Yl : TopFixedTraceState n)
    (hP : PuPinAt ring C s Y0 Yl) (hA : AlignShape (topClockSpan n) (cellOf s Yl)) :
    ∃ (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
      (exs : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n),
      SweepStatic s Yl sam exs ∧
      (∀ j, 1 ≤ j → j < topClockSpan n → (sam j).tail = false) ∧
      (∀ j, j < topClockSpan n → RegData s sam Yl j) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨hcut, hfrom, hold, hl, ha⟩ := hP
  have hreach : topClockReached ring C Yl := markedFrom_reached ring C Y0 Yl hfrom
  obtain ⟨hreach0, hgen, anchor, hanchor, htime, hfuture⟩ := hcut
  have hpure : topClockConcretePureStream s Yl anchor := by
    obtain ⟨w, hw⟩ := hfrom
    rw [hw]; exact hfuture w
  rw [← htime] at hl ha
  obtain ⟨hfree, hI, k0, hk0, hlist⟩ := hl
  have hnonE : ∀ j, j < topClockSpan n → puNonE (cellOf s Yl j).i = true := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; rw [hA.2.1]; rfl
    · rw [hA.2.2 j hj (by omega)]; rfl
  have hflag : ∀ j, 0 ≤ j → j < topClockSpan n → paFlagSettled s Yl anchor.time j = true :=
    fun j _ hj => ha j hj (hnonE j hj)
  -- the alignment of the oldest serial
  have hsamp := fun j hj1 hj2 => labelled_sample s Yl anchor hpure k0 hlist 0 hflag j hj1 hj2
  have hexp := fun j hj1 hj2 => labelled_export s Yl anchor.time k0 hlist 0 hflag j hj1 hj2
  have hmod0 : k0 % topClockSpan n = 0 := by
    obtain ⟨sT, _, _, _, htailT, _, htokT⟩ := hsamp 0 (Nat.le_refl _) (by omega)
    obtain ⟨vT, hqT⟩ := (qIn_of_cell s Yl 0).1 (by rw [hA.2.1])
    have hsT : sT.tail = true := by
      rw [hqT] at htokT
      simp only [puTok] at htokT
      exact (InTok.P.inj htokT).2.symm
    rw [hsT] at htailT
    have hm : (k0 + (topClockSpan n - 1 - 0)) % topClockSpan n = topClockSpan n - 1 := by
      by_cases hc : (k0 + (topClockSpan n - 1 - 0)) % topClockSpan n = topClockSpan n - 1
      · exact hc
      · rw [if_neg hc] at htailT; exact absurd htailT (by decide)
    have := mod_shift k0 (topClockSpan n - 1) (topClockSpan n) (by omega) (by omega)
      (by simpa using hm)
    omega
  have hmodj : ∀ j, j < topClockSpan n →
      (k0 + (topClockSpan n - 1 - j)) % topClockSpan n = topClockSpan n - 1 - j := by
    intro j hj
    rw [← Nat.mod_add_mod, hmod0, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  -- the per-register data
  have hall' : ∀ j, j < topClockSpan n → ∃ (sm : DigitSample (compileAdvice (ceilLogTwo n)) n)
      (ex : DigitExport (compileAdvice (ceilLogTwo n)) n), StaticAt s Yl anchor.time k0 j sm ex := by
    intro j hj
    obtain ⟨sm, hrec, hlane, hsite, htail, hatom, htok⟩ := hsamp j (by omega) hj
    obtain ⟨hi, hatom', htok'⟩ := hexp j (by omega) hj
    obtain ⟨ex, hex⟩ : ∃ ex, ex = (topClockConcreteExportsAfter s Yl anchor.time)[k0 + (topClockSpan n - 1 - j)] := ⟨_, rfl⟩
    rw [← hex] at hatom' htok'
    have hexmem : ex ∈ topClockConcreteExportsAfter s Yl anchor.time := by rw [hex]; exact List.getElem_mem hi
    obtain ⟨hrecE, hlE, hTE, hsE, hdE⟩ := (exportList_mem ring C s Yl hreach anchor.time ex).1 hexmem
    have hinv := framesInv_run ring C Yl.2
    have hinv' : FramesInv ring Yl.1.2 := by
      have := hreach
      unfold topClockReached at this
      rw [this]; exact hinv
    obtain ⟨fE, hfE, hfEt, hfEe, hfEr⟩ := hrecE
    obtain ⟨fS, hfS, hfSt, _, _, _⟩ := id hrec
    have hexT : ex.time ≤ Yl.1.2.clock := by
      have := (hinv'.1 fE hfE).2
      omega
    have hsT : 0 < sm.id.time := by
      have := (hinv'.1 fS hfS).1
      omega
    have hatomEq : ex.operand = some (.sampled sm.id) := by
      rw [← hatom, ← hatom']
    have hvt := htok.symm.trans htok'
    have hvv : sm.value = ex.value := (InTok.P.inj hvt).1
    have htt : sm.tail = ex.tail := (InTok.P.inj hvt).2
    have hsimtime : sm.id.time < ex.time := by
      have hrun : Yl = topFixedTraceRun ring C Yl.2 := hreach
      have hAL := export_atom_lt ring hn2 C Yl.2
      rw [← hrun] at hAL
      have hfEr' := hfEr
      rw [hlE] at hfEr'
      exact hAL fE hfE ex hfEr' sm.id hatomEq
    have hmodv := hmodj j hj
    refine ⟨sm, ex, ⟨hrec, hlane, ?_, hsT, ?_⟩, ⟨⟨fE, hfE, hfEt, hfEe, hfEr⟩, hlE, hsE, hdE, hatomEq,
      hvv.symm, htt.symm, hsimtime, hexT⟩, ?_, ?_⟩
    · rw [hsite, hmodv]
      congr 1
      omega
    · rw [htail, hmodv]
      by_cases hj0 : j = 0
      · subst hj0; simp
      · have : ¬ (topClockSpan n - 1 - j = topClockSpan n - 1) := by omega
        simp [this, hj0]
    · rw [List.getElem?_eq_getElem hi, hex]
    · have hq : ∃ v, (Yl.1.1 (winSite s j)).qIn = .S v (decide (j = 0)) := by
        by_cases hj0 : j = 0
        · subst hj0
          obtain ⟨v, hv⟩ := (qIn_of_cell s Yl 0).1 (by rw [hA.2.1])
          exact ⟨v, by simpa using hv⟩
        · obtain ⟨v, hv⟩ := (qIn_of_cell s Yl j).2.1 (by rw [hA.2.2 j hj (by omega)])
          exact ⟨v, by simpa [hj0] using hv⟩
      obtain ⟨v, hv⟩ := hq
      have htk : puTok (Yl.1.1 (winSite s j)).qIn = InTok.P sm.value sm.tail := htok
      rw [hv] at htk
      simp only [puTok] at htk
      have hvv' := InTok.P.inj htk
      refine ⟨?_, ?_, hatom⟩
      · rw [hv, hvv'.1, hvv'.2]
      · have hoff := siteCell_offMatch Yl (winSite s j)
        unfold OffMatch at hoff
        have hc : (siteCell Yl (winSite s j)).c = .off := by
          by_cases hj0 : j = 0
          · subst hj0
            have := hA.2.1
            unfold cellOf at this
            rw [this]
          · have := hA.2.2 j hj (by omega)
            unfold cellOf at this
            rw [this]
        exact hoff.1 hc
  obtain ⟨sam, exs, hspec⟩ := exists_fun_two (StaticAt s Yl anchor.time k0) (topClockSpan n)
    (by omega) hall'
  have hexps := exportList_pairwise ring C s Yl hreach anchor.time
  have hgetE : ∀ j, j < topClockSpan n → ∃ (hi : k0 + (topClockSpan n - 1 - j) <
      (topClockConcreteExportsAfter s Yl anchor.time).length),
      (topClockConcreteExportsAfter s Yl anchor.time)[k0 + (topClockSpan n - 1 - j)] = exs j := by
    intro j hj
    have := (hspec j hj).2.2.1
    exact List.getElem?_eq_some_iff.1 this
  refine ⟨sam, exs, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj
    exact (hspec j hj).1
  · intro j hj
    exact (hspec j hj).2.1
  · intro i j hi hj hij
    obtain ⟨hi', hei⟩ := hgetE i hi
    obtain ⟨hj', hej⟩ := hgetE j hj
    have := List.pairwise_iff_getElem.1 hexps (k0 + (topClockSpan n - 1 - j))
      (k0 + (topClockSpan n - 1 - i)) hj' hi' (by omega)
    rw [hei, hej] at this
    exact this
  · intro other hother hl hsrc hdst hle hge
    obtain ⟨ha', hea⟩ := hgetE (topClockSpan n - 1) (by omega)
    obtain ⟨hb', heb⟩ := hgetE 0 (by omega)
    have hmemA : exs (topClockSpan n - 1) ∈ topClockConcreteExportsAfter s Yl anchor.time := by
      rw [← hea]; exact List.getElem_mem ha'
    have hTA := ((exportList_mem ring C s Yl hreach anchor.time _).1 hmemA).2.2.1
    obtain ⟨m, hm, hm1, hm2, hmo⟩ := exportList_between ring C s Yl hreach anchor.time
      (k0 + (topClockSpan n - 1 - (topClockSpan n - 1))) (k0 + (topClockSpan n - 1 - 0)) ha' hb'
      other hother hl (by omega) hsrc hdst (by rw [hea]; exact hle) (by rw [heb]; exact hge)
    refine ⟨k0 + (topClockSpan n - 1) - m, by omega, ?_⟩
    have hj : k0 + (topClockSpan n - 1) - m < topClockSpan n := by omega
    have hq := (hspec _ hj).2.2.1
    have hidx : k0 + (topClockSpan n - 1 - (k0 + (topClockSpan n - 1) - m)) = m := by omega
    rw [hidx, List.getElem?_eq_getElem hm, hmo] at hq
    exact Option.some.inj hq
  · intro j hj0 hj
    have := (hspec j hj).1.2.2.2.2
    rw [this]
    simp; omega
  · intro j hj
    exact (hspec j hj).2.2.2

end MarkedCells
end L3

#print axioms L3.MarkedCells.static_of_aligned
#print axioms L3.MarkedCells.export_atom_lt
