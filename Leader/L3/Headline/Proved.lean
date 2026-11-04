import Leader.L3.Width.DigitQuietEntryValuesAtCut
import Leader.L3.Headline.CleanAssembly
import Leader.L3.Width.DigitQuietStepLaw

/-!
# `hcert` discharged in the headline

The premise `hcert` of `l3HeadlineOfCleanBranches` by `widthWriterCertificateOfBand`; the one-letter
law `hlaw` of the quiet class by `quietStepLawProved` (WidthDigitQuietStepLaw).  `l3HeadlineProved`
is the headline for every `n ≥ 5` with no premise beyond `hn`.

Consumer: the L3 board (H1).
-/

namespace L3.HeadlineCleanAssembly

/-- **The headline from the one-letter law of the quiet class.**  Consumer: the L3 board (H1). -/
theorem l3HeadlineOfQuietLaw {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first) :
    L3Headline ring :=
  l3HeadlineOfCleanBranches ring hn hlaw (L3.WriterCertificate.widthWriterCertificateOfBand ring hn)

/-- **The L3 headline for every ring size `n ≥ 5`.**  The one-letter law of the quiet class is
`quietStepLawProved`.  Consumer: the L3 board (H1). -/
theorem l3HeadlineProved {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) : L3Headline ring :=
  l3HeadlineOfQuietLaw ring hn
    (fun root first => L3.DigitQuiet.quietStepLawProved hn ring root first)

end L3.HeadlineCleanAssembly

#print axioms L3.HeadlineCleanAssembly.l3HeadlineOfQuietLaw
#print axioms L3.HeadlineCleanAssembly.l3HeadlineProved
