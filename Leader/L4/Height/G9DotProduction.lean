import Leader.L4.Height.G9Dot
import Leader.L4.PhysicalCustodyProduction
import Leader.L4.MonitorRawBridge

namespace L4.Height.G9Dot
open L4.AllSizeProtocol L4.PhysicalCustody L4.Compiler.Native
open L4.Height.G9Wire L4.Height.G9Wire.CustodySpec L4.Height.G9Wire.PublicSpec

theorem actual_custody : CustodyReached :=
  custody_contract L4.PhysicalCustodyProduction.K_custody
    (fun _ hs ha x=>
      (L4.MonitorRawBridge.height_iff_row _ _ _ _).mpr
        (L4.PhysicalCustodyProduction.custody_reached ha hs x))

theorem all_sizes_expected :
    ∃ g patrol : Nat, ∀ n (hn : 4 ≤ n),
      (deployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn g patrol :=
  deployed_of_custody actual_custody

#print axioms actual_custody
#print axioms all_sizes_expected
end L4.Height.G9Dot
