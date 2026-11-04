import Lean.Data.Json

/-!
# Variant catalogue shared by the P_PLL exploration backends

The simulator can load several P_PLL transition functions.  They live on two
different local-state carriers, so they are served by two kinds of process:

* the native backend (`Leader/Wu/Sim/BoundedBackend.lean`) serves the variants whose
  carrier is the finite `BoundedAgentState ψ κ`;
* the interpreted raw backends (`Leader/Wu/Sim/RawBackend.lean` and
  `Leader/Wu/Sim/RawBackendJamGuard.lean`) serve the kernel-experiment variants whose
  carrier is the audit record `AgentState ψ`.  They are interpreted rather than
  compiled because their import closure contains closed definitions that a
  native executable evaluates eagerly at start-up.

Two raw processes are needed because `Leader/Wu/Birth/LeaderlessEscapeCleanBotRepairs.lean` and
`Leader/Wu/Birth/LeaderlessEscapeResultGuardPoison.lean` both declare their definitions in the namespace
`ZZRepairAll8` (for example `ZZRepairAll8.jamGuard`), so no single Lean
environment can import both.

This module holds only descriptive metadata; it has no transition code.
-/

set_option autoImplicit false

open Lean

namespace PPLLSimVariantCatalog

/-- Where a variant is executed. -/
inductive Server where
  | native
  | raw
  | rawR7
  deriving DecidableEq, Repr

/-- One catalogue row: the wire name of a variant together with the exact Lean
entry points that define its transition. -/
structure Entry where
  name : String
  providerId : String
  protocolId : String
  protocolEntrypoint : String
  transitionEntrypoint : String
  carrier : String
  stateCodec : String
  server : Server
  note : String

def serverName : Server → String
  | .native => "native: scripts/run_ppll_sim_backend.sh"
  | .raw => "interpreted: scripts/run_ppll_sim_raw_backend.sh raw"
  | .rawR7 => "interpreted: scripts/run_ppll_sim_raw_backend.sh r7"

def boundedCodec : String := "ppll-bounded-agent-state-32.v1"
def rawCodec : String := "ppll-raw-agent-state-32.v1"

def entries : List Entry :=
  [ { name := "bounded"
      providerId := "ppll.repaired.bounded.v1"
      protocolId := "PPLLRepair.boundedProtocol"
      protocolEntrypoint := "Leader/Wu/Protocol/BoundedProtocol.lean:PPLLRepair.boundedProtocol"
      transitionEntrypoint := "Leader/Wu/Protocol/Repairs.lean:PPLLRepair.ppllSaturatedNoCollision"
      carrier := "BoundedAgentState psi kappa"
      stateCodec := boundedCodec
      server := .native
      note := "default; used when params has no variant field" }
  , { name := "integrated"
      providerId := "ppll.integrated.bounded.v1"
      protocolId := "PPLLRepair.integratedBoundedProtocol"
      protocolEntrypoint :=
        "Leader/Wu/Protocol/BoundedProtocol.lean:PPLLRepair.integratedBoundedProtocol"
      transitionEntrypoint := "Leader/Wu/Protocol/Repairs.lean:PPLLRepair.ppllIntegratedRepair"
      carrier := "BoundedAgentState psi kappa"
      stateCodec := boundedCodec
      server := .native
      note := "CorrectedFormulation.physicalProtocol is an abbrev for this protocol" }
  , { name := "all8"
      providerId := "ppll.zz.all8.raw.v1"
      protocolId := "ZZRepairAll8.protocolAll8"
      protocolEntrypoint := "Leader/Wu/Birth/LeaderlessEscapeCleanBotRepairs.lean:ZZRepairAll8.protocolAll8"
      transitionEntrypoint :=
        "Leader/Wu/Birth/LeaderlessEscapeCleanBotRepairs.lean:ZZRepairAll8.ppllIntegratedRepairAll5"
      carrier := "AgentState psi"
      stateCodec := rawCodec
      server := .raw
      note := "protocolAll8 is the psi=2, kappa=2 instance of the transition entry point" }
  , { name := "all9r7"
      providerId := "ppll.zz.all9r7.raw.v1"
      protocolId := "ZZRepairAll8.protocolAll9R7"
      protocolEntrypoint :=
        "Leader/Wu/Birth/LeaderlessEscapeResultGuardPoison.lean:ZZRepairAll8.protocolAll9R7"
      transitionEntrypoint :=
        "Leader/Wu/Birth/LeaderlessEscapeResultGuardPoison.lean:ZZRepairAll8.ppllIntegratedRepairAll5R7"
      carrier := "AgentState psi"
      stateCodec := rawCodec
      server := .rawR7
      note := "protocolAll9R7 is the psi=2, kappa=2 instance; the module declares its names in namespace ZZRepairAll8" }
  , { name := "all10consume"
      providerId := "ppll.zz.all10consume.raw.v1"
      protocolId := "ZZRepairAll10Consume.protocolAll10Consume"
      protocolEntrypoint :=
        "Leader/Wu/Birth/LeaderlessEscapeConsumeControl.lean:ZZRepairAll10Consume.protocolAll10Consume"
      transitionEntrypoint :=
        "Leader/Wu/Birth/LeaderlessEscapeConsumeControl.lean:ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume"
      carrier := "AgentState psi"
      stateCodec := rawCodec
      server := .raw
      note := "protocolAll10Consume is the psi=2, kappa=2 instance of the transition entry point" }
  ]

def find? (name : String) : Option Entry :=
  entries.find? (·.name == name)

def entryJson (e : Entry) : Json :=
  Json.mkObj
    [ ("variant", e.name), ("provider_id", e.providerId)
    , ("protocol_id", e.protocolId)
    , ("protocol_entrypoint", e.protocolEntrypoint)
    , ("transition_entrypoint", e.transitionEntrypoint)
    , ("carrier", e.carrier), ("state_codec", e.stateCodec)
    , ("served_by", serverName e.server), ("note", e.note) ]

/-- The full catalogue, as listed by `describe` whenever a variant is named. -/
def catalogueJson : Json :=
  Json.arr (entries.toArray.map entryJson)

/-- Error text for a variant this process does not serve. -/
def wrongServer (name : String) : String :=
  match find? name with
  | some e => s!"variant {name} is not served by this process; it is {serverName e.server}"
  | none =>
      let names := ", ".intercalate (entries.map (·.name))
      s!"unknown variant: {name} (known: {names})"

end PPLLSimVariantCatalog
