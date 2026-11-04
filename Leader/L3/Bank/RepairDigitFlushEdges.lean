import Leader.L3.Bank.RepairDigit
import Leader.L3.LiveTopBlocks

/-!
# T17: leading-fragment boundary edges at the first delimiter

Companion to the T17 block at the end of `Leader/L3/Bank/RepairDigit.lean`. It is kept in its
own module because these exhaustive row case splits take about 25 minutes to elaborate.
Appended to `BankRepairDigit.lean`, they push that file's check past the verification queue
deadline.

The delimiter site (beta = true) carries its own input weight `DelimInW`. The site before it
is an ordinary segment site at distance `1`, with output weight `PreOutW R 1`. The site after
it is a segment site at distance `R - 1`. These are the edge inequalities, non-strict and
strict, for the two edges touching the delimiter, in both the writer and comparison lanes.
They extend the interior-edge inequalities in `BankRepairDigit.lean`
(`bankRepairDigitWriterSegSeg*`, `...PreOut*`, `bankRepairDigitComparison*`).
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-- Input weight at the first delimiter (segment length `R`). -/
def bankRepairDigitDelimInW {A : Nat} (R : Nat) : InTok A → Nat
  | .E => 0
  | .X => R
  | .P _ _ => 2 * R + 2
  | .S _ _ => 2 * R + 1

theorem bankRepairDigitTailWOne (R : Nat) : bankRepairDigitTailW R 1 = 4 * R + 7 := by
  show bankRepairDigitTailW R 0 + 0 + 2 * R + 5 = 4 * R + 7
  simp only [bankRepairDigitTailW]; omega

/-! Writer lane. -/

theorem bankRepairDigitWriterIntoDelim (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true) :
    bankRepairDigitPreOutW R 1 (liveTopPair c ox oy).x.wOut +
      bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitDelimInW R (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).y.wCarry.isW ≤
    bankRepairDigitPreOutW R 1 ox.wOut + bankRepairDigitSegInW R 1 ox.wIn +
      bankRepairDigitLiveW 1 ox.wCarry.isW + bankRepairDigitDelimInW R oy.wIn +
      bankRepairDigitLiveW R oy.wCarry.isW := by
  have h1 := bankRepairDigitTailWOne R
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases ho : ox.wOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, outT,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitPreOutW,
      h1, bankRepairDigitDelimInW] <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitWriterIntoDelimStrictIn (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 1 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW)
    (hy : bankRepairDigitDelimInW R oy.wIn + bankRepairDigitLiveW R oy.wCarry.isW = 0) :
    bankRepairDigitPreOutW R 1 (liveTopPair c ox oy).x.wOut +
      bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitDelimInW R (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).y.wCarry.isW + 1 ≤
    bankRepairDigitPreOutW R 1 ox.wOut + bankRepairDigitSegInW R 1 ox.wIn +
      bankRepairDigitLiveW 1 ox.wCarry.isW + bankRepairDigitDelimInW R oy.wIn +
      bankRepairDigitLiveW R oy.wCarry.isW := by
  have h1 := bankRepairDigitTailWOne R
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases ho : ox.wOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, outT,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitPreOutW,
      h1, bankRepairDigitDelimInW] at hx hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitWriterIntoDelimStrictOut (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 1 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitPreOutW R 1 ox.wOut)
    (hin : bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW = 0)
    (hy : bankRepairDigitDelimInW R oy.wIn + bankRepairDigitLiveW R oy.wCarry.isW = 0) :
    bankRepairDigitPreOutW R 1 (liveTopPair c ox oy).x.wOut +
      bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitDelimInW R (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).y.wCarry.isW + 1 ≤
    bankRepairDigitPreOutW R 1 ox.wOut + bankRepairDigitSegInW R 1 ox.wIn +
      bankRepairDigitLiveW 1 ox.wCarry.isW + bankRepairDigitDelimInW R oy.wIn +
      bankRepairDigitLiveW R oy.wCarry.isW := by
  have h1 := bankRepairDigitTailWOne R
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases ho : ox.wOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, outT,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitPreOutW,
      h1, bankRepairDigitDelimInW] at hx hin hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitWriterFromDelim (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 2 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = true) (hby : oy.beta = false) :
    bankRepairDigitDelimInW R (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitSegInW R (R - 1) (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW (R - 1) (liveTopPair c ox oy).y.wCarry.isW ≤
    bankRepairDigitDelimInW R ox.wIn + bankRepairDigitLiveW R ox.wCarry.isW +
      bankRepairDigitSegInW R (R - 1) oy.wIn + bankRepairDigitLiveW (R - 1) oy.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, WC,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitDelimInW] <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitWriterFromDelimStrict (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 2 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = true) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitDelimInW R ox.wIn + bankRepairDigitLiveW R ox.wCarry.isW)
    (hy : bankRepairDigitSegInW R (R - 1) oy.wIn +
      bankRepairDigitLiveW (R - 1) oy.wCarry.isW = 0) :
    bankRepairDigitDelimInW R (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitSegInW R (R - 1) (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW (R - 1) (liveTopPair c ox oy).y.wCarry.isW + 1 ≤
    bankRepairDigitDelimInW R ox.wIn + bankRepairDigitLiveW R ox.wCarry.isW +
      bankRepairDigitSegInW R (R - 1) oy.wIn + bankRepairDigitLiveW (R - 1) oy.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, WC,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitDelimInW] at hx hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitWriterOutOfSeg (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true) :
    bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.wCarry.isW ≤
    bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases ho : ox.wOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
      bankRepairDigitSegInW, bankRepairDigitLiveW] <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitWriterOutOfSegStrict (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW) :
    bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.wCarry.isW + 1 ≤
    bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW := by
  simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry,
    liveTopPair_y_wCarry, liveTopPair_x_wOut]
  rcases ho : ox.wOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.wIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.wCarry with _ | _ <;>
  rcases hi2 : oy.wIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.wCarry with _ | _ <;>
    simp [liveTopWC, liveTopWI, liveTopWO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
      bankRepairDigitSegInW, bankRepairDigitLiveW] at hx ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

/-! Comparison lane. -/

theorem bankRepairDigitComparisonIntoDelim (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true) :
    bankRepairDigitPreOutW R 1 (liveTopPair c ox oy).x.qOut +
      bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitDelimInW R (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).y.qCarry.isL ≤
    bankRepairDigitPreOutW R 1 ox.qOut + bankRepairDigitSegInW R 1 ox.qIn +
      bankRepairDigitLiveW 1 ox.qCarry.isL + bankRepairDigitDelimInW R oy.qIn +
      bankRepairDigitLiveW R oy.qCarry.isL := by
  have h1 := bankRepairDigitTailWOne R
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases ho : ox.qOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, outT,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitPreOutW,
      h1, bankRepairDigitDelimInW] <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitComparisonIntoDelimStrictIn (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 1 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL)
    (hy : bankRepairDigitDelimInW R oy.qIn + bankRepairDigitLiveW R oy.qCarry.isL = 0) :
    bankRepairDigitPreOutW R 1 (liveTopPair c ox oy).x.qOut +
      bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitDelimInW R (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).y.qCarry.isL + 1 ≤
    bankRepairDigitPreOutW R 1 ox.qOut + bankRepairDigitSegInW R 1 ox.qIn +
      bankRepairDigitLiveW 1 ox.qCarry.isL + bankRepairDigitDelimInW R oy.qIn +
      bankRepairDigitLiveW R oy.qCarry.isL := by
  have h1 := bankRepairDigitTailWOne R
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases ho : ox.qOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, outT,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitPreOutW,
      h1, bankRepairDigitDelimInW] at hx hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitComparisonIntoDelimStrictOut (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 1 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitPreOutW R 1 ox.qOut)
    (hin : bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL = 0)
    (hy : bankRepairDigitDelimInW R oy.qIn + bankRepairDigitLiveW R oy.qCarry.isL = 0) :
    bankRepairDigitPreOutW R 1 (liveTopPair c ox oy).x.qOut +
      bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitDelimInW R (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).y.qCarry.isL + 1 ≤
    bankRepairDigitPreOutW R 1 ox.qOut + bankRepairDigitSegInW R 1 ox.qIn +
      bankRepairDigitLiveW 1 ox.qCarry.isL + bankRepairDigitDelimInW R oy.qIn +
      bankRepairDigitLiveW R oy.qCarry.isL := by
  have h1 := bankRepairDigitTailWOne R
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases ho : ox.qOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, outT,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitPreOutW,
      h1, bankRepairDigitDelimInW] at hx hin hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitComparisonFromDelim (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 2 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = true) (hby : oy.beta = false) :
    bankRepairDigitDelimInW R (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitSegInW R (R - 1) (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW (R - 1) (liveTopPair c ox oy).y.qCarry.isL ≤
    bankRepairDigitDelimInW R ox.qIn + bankRepairDigitLiveW R ox.qCarry.isL +
      bankRepairDigitSegInW R (R - 1) oy.qIn + bankRepairDigitLiveW (R - 1) oy.qCarry.isL := by
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, QC,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitDelimInW] <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitComparisonFromDelimStrict (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hR : 2 ≤ R)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = true) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitDelimInW R ox.qIn + bankRepairDigitLiveW R ox.qCarry.isL)
    (hy : bankRepairDigitSegInW R (R - 1) oy.qIn +
      bankRepairDigitLiveW (R - 1) oy.qCarry.isL = 0) :
    bankRepairDigitDelimInW R (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW R (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitSegInW R (R - 1) (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW (R - 1) (liveTopPair c ox oy).y.qCarry.isL + 1 ≤
    bankRepairDigitDelimInW R ox.qIn + bankRepairDigitLiveW R ox.qCarry.isL +
      bankRepairDigitSegInW R (R - 1) oy.qIn + bankRepairDigitLiveW (R - 1) oy.qCarry.isL := by
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, QC,
      bankRepairDigitSegInW, bankRepairDigitLiveW, bankRepairDigitDelimInW] at hx hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitComparisonOutOfSeg (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true) :
    bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.qCarry.isL ≤
    bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL := by
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases ho : ox.qOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
      bankRepairDigitSegInW, bankRepairDigitLiveW] <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

theorem bankRepairDigitComparisonOutOfSegStrict (c : Compiled) (ox oy : Agent c) (R : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL) :
    bankRepairDigitSegInW R 1 (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW 1 (liveTopPair c ox oy).x.qCarry.isL + 1 ≤
    bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL := by
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qCarry,
    liveTopPair_y_qCarry, liveTopPair_x_qOut]
  rcases ho : ox.qOut with _ | _ | ⟨v, _ | _⟩ <;>
  rcases hi : ox.qIn with _ | _ | ⟨w, _ | _⟩ | ⟨w, _ | _⟩ <;>
  rcases hc : ox.qCarry with _ | ⟨_, _⟩ <;>
  rcases hi2 : oy.qIn with _ | _ | ⟨u, _ | _⟩ | ⟨u, _ | _⟩ <;>
  rcases hc2 : oy.qCarry with _ | ⟨_, _⟩ <;>
    simp [liveTopQC, liveTopQI, liveTopQO, hl, hly, hb, hby, ho, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
      bankRepairDigitSegInW, bankRepairDigitLiveW] at hx ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> (try omega)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitTailWOne
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterIntoDelim
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterIntoDelimStrictIn
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterIntoDelimStrictOut
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterFromDelim
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterFromDelimStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterOutOfSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterOutOfSegStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonIntoDelim
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonIntoDelimStrictIn
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonIntoDelimStrictOut
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonFromDelim
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonFromDelimStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonOutOfSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonOutOfSegStrict
