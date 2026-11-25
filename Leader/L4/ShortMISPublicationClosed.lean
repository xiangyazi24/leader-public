import Leader.L4.ShortMISPublicationOwner
import Leader.L4.ShortMISFencedWord

namespace L4.ShortMISPublicationClosed
set_option exponentiation.threshold 40575
open ShortH2Final
open PhysicalCustody ShortH2RawEntrance ShortMIS3Entrance ShortMISLift

/-- Actual original-mark MIS2 then MIS3 from a reached permanent H2.
No publication supplier hypothesis remains. -/
theorem permanent_h4_from_permanent_h2 {s n : Nat} (N : 189<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x
      ((K_H3+K_H4)*n^2) :=
  ShortMISPublicationOwner.mis23_from_h2_only_word N x H
    (ShortMISFencedWord.mis2_fenced_word_rows (by omega) x H)
    (ShortMISFencedWord.mis3_fenced_word_rows N)

/-- Actual physical H4 entrance from arbitrary bytes, including the
controller-accepted H2 stage. All three stage coefficients are fixed. -/
theorem permanent_h4_from_raw {s n : Nat} (N : 189<n) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x
      ((5+2*6^9)*n^2 + (10^8095+19+2*publicationScale)*n^2 +
        (K_H3+K_H4)*n^2) :=
  AllSizeComposition.additive_stage (rawNext s) (PermanentH2 (by omega)) (PermanentH4 N)
    _ _ x (permanent_h2_from_raw (by omega) x) (permanent_h4_from_permanent_h2 N)

#print axioms permanent_h4_from_permanent_h2
#print axioms permanent_h4_from_raw
end L4.ShortMISPublicationClosed
