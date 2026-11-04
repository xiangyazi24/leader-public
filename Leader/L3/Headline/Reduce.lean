import Leader.L3.Headline.Assembly
import Leader.L3.ClosureFull

/-!
# L3 headline reduced to its expected-time stages

`HeadlineAssembly.l3Headline_of_stages` proves `L3Headline ring` from seven named stage
premises.  Two of them, closure of the generated target and safety on it, are kernel
theorems of `ClosureFull` for `n ≥ 5` (the target is `Closure.targetSet`, eq:e-target).
What remains are the five expected-time stages of the proof of `thm:linear-lease`
(`appendices/renewal.tex`): purification, first grant, request/checker, first protected
birth, and the rooted renewal.
-/

namespace L3

set_option autoImplicit false

/-- `L3Headline` from the five expected-time stages alone. -/
theorem l3Headline_of_time_stages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hpurify : StageNativePurification ring)
    (hgrant : StageFirstGrant ring)
    (hrequest : StageRequestChecker ring)
    (hbirth : StageFirstProtectedBirth ring)
    (hrenew : StageRootedRenewal ring) :
    L3Headline ring :=
  l3Headline_of_stages ring hn hpurify hgrant hrequest hbirth hrenew
    (ClosureFull.targetSetClosed hn ring)
    (fun C hC => ClosureFull.targetSetIsSafe hn ring C hC)

end L3
