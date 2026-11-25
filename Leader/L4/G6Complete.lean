import Leader.L4.TripleLongRestart
import Leader.L4.TripleOneEdge
import Leader.L4.RootedWindows

namespace L4.G6Complete

/-- Both literal physical boundary cases, for all moduli. -/
theorem boundary : TripleBoundary.MissingBoundary where
  oneEdge := TripleOneEdge.oneEdge
  long hn v z _ hSep hCert _ := TripleLongRestart.concrete_attempt hn v _ _ z hCert hSep

theorem restartTrial : RestartSerial.RootIndependentRestartTrial :=
  TripleBoundary.restartTrial_of_boundary boundary

theorem row175_rooted_of_short_window (h : RootedWindows.RootedShortWindowReward) :
    RootedAssembly.RootedStatement :=
  RootedWindows.row175_rooted_of_minimal_inputs boundary h

theorem row175_of_short_window (h : RootedWindows.RootedShortWindowReward) :
    row175Statement :=
  RootedWindows.row175Statement_of_minimal_rooted_inputs boundary h

#print axioms boundary
#print axioms restartTrial
#print axioms row175_rooted_of_short_window
#print axioms row175_of_short_window
end L4.G6Complete
