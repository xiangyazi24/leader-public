import Leader.Wu.Sim.RawServer
import Leader.Wu.Birth.LeaderlessEscapeResultGuardPoison

/-!
# Raw-carrier exploration backend: `protocolAll9R7`

Serves the catalogue variant `all9r7`
(`ZZRepairAll8.ppllIntegratedRepairAll5R7` from
`Leader/Wu/Birth/LeaderlessEscapeResultGuardPoison.lean`, the transition of
`ZZRepairAll8.protocolAll9R7`).  It is a separate process because that module
declares its names in the namespace `ZZRepairAll8`, colliding with
`Leader/Wu/Birth/LeaderlessEscapeCleanBotRepairs.lean`.  Run it interpreted (`lake env lean --run`).
-/

set_option autoImplicit false

namespace PPLLSimRawBackendR7

open PPLLSimRawServer

def table : List RawVariant :=
  [ { entry := entry! "all9r7"
      transition := fun hψ κ => ZZRepairAll8.ppllIntegratedRepairAll5R7 hψ κ } ]

end PPLLSimRawBackendR7

def main : IO Unit := do
  PPLLSimRawServer.serve PPLLSimRawBackendR7.table (← IO.getStdin) (← IO.getStdout)
