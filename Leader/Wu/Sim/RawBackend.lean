import Leader.Wu.Sim.RawServer
import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs
import Leader.Wu.Birth.LeaderlessEscapeConsumeControl

/-!
# Raw-carrier exploration backend: `protocolAll8` and `protocolAll10Consume`

Serves the catalogue variants `all8` (`ZZRepairAll8.ppllIntegratedRepairAll5`,
the transition of `ZZRepairAll8.protocolAll8`) and `all10consume`
(`ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume`, the transition of
`ZZRepairAll10Consume.protocolAll10Consume`).  `protocolAll9R7` needs its own
process (`Leader/Wu/Sim/RawBackendJamGuard.lean`) because its module declares names
that collide with `Leader/Wu/Birth/LeaderlessEscapeCleanBotRepairs.lean`.

Run it interpreted (`lake env lean --run`): the import closure contains closed
definitions that a native executable evaluates eagerly at start-up.
-/

set_option autoImplicit false

namespace PPLLSimRawBackend

open PPLLSimRawServer

def table : List RawVariant :=
  [ { entry := entry! "all8"
      transition := fun hψ κ => ZZRepairAll8.ppllIntegratedRepairAll5 hψ κ }
  , { entry := entry! "all10consume"
      transition := fun hψ κ => ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume hψ κ }
  ]

end PPLLSimRawBackend

def main : IO Unit := do
  PPLLSimRawServer.serve PPLLSimRawBackend.table (← IO.getStdin) (← IO.getStdout)
