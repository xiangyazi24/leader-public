import Leader.L3.Width.DigitQuietStepPairs
import Leader.L3.Width.DigitQuietStepRegions

/-!
# The one-letter law of the quiet class

`quietStepLawProved : QuietStepLaw ring root first` for a ring of at least five sites: the class
(`WidthDigitQuiet`) is closed under every letter at a fixed clean word root with `QWord`, every digit
is kept, and a report clears an old dirty endpoint.

The pieces: `digits_kept` (digits), `quiet_rootFixed_step`, `quiet_layout_step`, `quiet_values_step`,
`quiet_base_step` (root, layout, values, base labels), `quiet_leading_step`, `quiet_firstSegment_step`,
`quiet_fragment_step` (regions), `pairs_step` (the pair scans: `pq_after_letter` with the window
lemmas `win_pipe`, `win_fin`, `win_del`, `win_term`), `quiet_report_clause`.

Consumer: `L3.DigitQuiet.qdigitOfQuiet` and the hypothesis `hlaw` of the writer chain
(`WidthDigitWriterCore`, `HeadlineCleanAssembly`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

/-- **The one-letter law of the quiet class** (rings of at least five sites).  Consumer:
`qdigitOfQuiet`, the writer chain. -/
theorem quietStepLawProved {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) :
    QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first := by
  intro S e hQ hF hW
  have hdig := digits_kept hn ring root first S hQ hF hW e
  have hR : 0 < digitSpan (compileAdvice (ceilLogTwo n)) := by
    have := digitSpan_ge_two hn
    omega
  refine ⟨?_, hdig, quiet_report_clause hR ring root first S hQ e⟩
  refine quiet_of_parts ?_ (pairs_step hn ring root first S hQ hF hW e)
  exact
    { rootFixed := quiet_rootFixed_step hn ring root first S hF e
      layout := quiet_layout_step ring root first S hQ hW e
      values := quiet_values_step ring root first S hQ hW e hdig
      base := quiet_base_step hn ring root first S hQ hW e
      leading := quiet_leading_step hn ring root first S hQ hF hW e
      firstSegment := quiet_firstSegment_step hn ring root first S hQ hF hW e
      fragment := quiet_fragment_step hn ring root first S hQ hF hW e }

end L3.DigitQuiet

#print axioms L3.DigitQuiet.quietStepLawProved
